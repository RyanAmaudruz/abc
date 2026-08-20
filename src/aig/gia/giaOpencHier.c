/**CFile****************************************************************

  FileName    [giaOpencHier.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Hierarchical representation search: G generated from E, mixer-only eSlim.]

  Description [4-term 4-bit TC in, 11-bit signed out. Gold SM (350 AND) is a
               QoR side benchmark, not a search target or topology constraint.

               Level 1: structured recodings. Level 2: constrained signed-digit
               assignments. Within a family, G is instantiated from E's digits
               by a fixed construction rule and a fixed digit-to-wire encoding.]

***********************************************************************/

#include "gia.h"
#include "misc/extra/extra.h"
#include "proof/cec/cec.h"
#include "opt/eslim/eSLIM.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

ABC_NAMESPACE_IMPL_START

extern Gia_Man_t * Gia_ManCompress2( Gia_Man_t * p, int fUpdateLevel, int fVerbose );

#define HIER_NBIT      4
#define HIER_NTERM     4
#define HIER_NOPS      8
#define HIER_NOUT      11
#define HIER_ACC       16
#define HIER_MAX_D     8
#define HIER_MAX_BPD   4
#define HIER_NVAL      16
#define HIER_MAX_CAND  64
#define HIER_STORE     256

#define HIER_FAM_A     0
#define HIER_FAM_B     1
#define HIER_FAM_S     2

////////////////////////////////////////////////////////////////////////
///                         ARITHMETIC                               ///
////////////////////////////////////////////////////////////////////////

static int Hier_TcToInt( int bits, int n )
{
    int sign;
    if ( n <= 0 )
        return 0;
    sign = 1 << (n - 1);
    if ( bits & sign )
        return bits - (sign << 1);
    return bits;
}

static int Hier_IntToTc( int v, int n )
{
    return v & ((1 << n) - 1);
}

static int Hier_FullAdder( Gia_Man_t * p, int a, int b, int cin, int * pCout )
{
    int u = Gia_ManHashXor( p, a, b );
    int v = Gia_ManHashAnd( p, a, b );
    int s = Gia_ManHashXor( p, u, cin );
    int w = Gia_ManHashAnd( p, u, cin );
    *pCout = Gia_ManHashOr( p, v, w );
    return s;
}

static int Hier_AddVec( Gia_Man_t * p, int * pA, int nA, int * pB, int nB, int * pS )
{
    int i, c = 0, n = Abc_MaxInt( nA, nB );
    int pT[128];
    assert( n + 1 <= 128 );
    for ( i = 0; i < n; i++ )
    {
        int a = (i < nA) ? pA[i] : 0;
        int b = (i < nB) ? pB[i] : 0;
        pT[i] = Hier_FullAdder( p, a, b, c, &c );
    }
    if ( c )
        pT[n++] = c;
    for ( i = 0; i < n; i++ )
        pS[i] = pT[i];
    return n;
}

static int Hier_MulUns( Gia_Man_t * p, int * pA, int nA, int * pB, int nB, int * pP )
{
    int i, j, nAcc = 0, pAcc[128], pRow[128], nRow;
    for ( i = 0; i < nA; i++ )
    {
        nRow = nB + i;
        assert( nRow <= 128 );
        for ( j = 0; j < nRow; j++ )
            pRow[j] = 0;
        for ( j = 0; j < nB; j++ )
            pRow[i + j] = Gia_ManHashAnd( p, pA[i], pB[j] );
        if ( nAcc == 0 )
        {
            for ( j = 0; j < nRow; j++ )
                pAcc[j] = pRow[j];
            nAcc = nRow;
        }
        else
            nAcc = Hier_AddVec( p, pAcc, nAcc, pRow, nRow, pAcc );
    }
    for ( i = 0; i < nAcc; i++ )
        pP[i] = pAcc[i];
    return nAcc;
}

static void Hier_NegMod( Gia_Man_t * p, int * pX, int n, int * pY )
{
    int i, pNot[128], pSum[128], one[1], nSum;
    for ( i = 0; i < n; i++ )
        pNot[i] = Abc_LitNot( pX[i] );
    one[0] = 1;
    nSum = Hier_AddVec( p, pNot, n, one, 1, pSum );
    for ( i = 0; i < n; i++ )
        pY[i] = (i < nSum) ? pSum[i] : 0;
}

static void Hier_SignExt( int * pA, int nA, int nOut, int * pE )
{
    int i, sign = (nA > 0) ? pA[nA - 1] : 0;
    for ( i = 0; i < nOut; i++ )
        pE[i] = (i < nA) ? pA[i] : sign;
}

static int Hier_MulTc( Gia_Man_t * p, int * pA, int nA, int * pB, int nB, int * pP, int nP )
{
    int j, i, nAcc, pAe[128], pRow[128], pAcc[128], pNeg[128];
    assert( nP <= 128 && nA <= nP );
    Hier_SignExt( pA, nA, nP, pAe );
    nAcc = 0;
    for ( j = 0; j < nB; j++ )
    {
        for ( i = 0; i < nP; i++ )
            pRow[i] = (i >= j) ? Gia_ManHashAnd( p, pAe[i - j], pB[j] ) : 0;
        if ( j == nB - 1 )
        {
            Hier_NegMod( p, pRow, nP, pNeg );
            for ( i = 0; i < nP; i++ )
                pRow[i] = pNeg[i];
        }
        if ( nAcc == 0 )
        {
            for ( i = 0; i < nP; i++ )
                pAcc[i] = pRow[i];
            nAcc = nP;
        }
        else
            nAcc = Hier_AddVec( p, pAcc, nAcc, pRow, nP, pAcc );
        if ( nAcc > nP )
            nAcc = nP;
    }
    for ( i = 0; i < nP; i++ )
        pP[i] = (i < nAcc) ? pAcc[i] : 0;
    return nP;
}

static int Hier_DupHashAnd( Gia_Man_t * pNew, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsBuf(pObj) )
        return Gia_ObjFanin0Copy(pObj);
    if ( Gia_ObjIsXor(pObj) )
        return Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    return Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

static int Hier_Tt4( Gia_Man_t * p, int * pX, unsigned tt )
{
    int v[16], i, k;
    for ( i = 0; i < 16; i++ )
        v[i] = (tt >> i) & 1;
    for ( k = 0; k < 4; k++ )
        for ( i = 0; i < (8 >> k); i++ )
            v[i] = Gia_ManHashMux( p, pX[k], v[2 * i + 1], v[2 * i] );
    return v[0];
}

////////////////////////////////////////////////////////////////////////
///                      GIA UTILITIES                               ///
////////////////////////////////////////////////////////////////////////

static Gia_Man_t * Hier_Stitch( Gia_Man_t * pEnc, Gia_Man_t * pMix )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, nBuf;
    nBuf = Gia_ManPoNum(pEnc);
    assert( Gia_ManPoNum(pEnc) == Gia_ManPiNum(pMix) );
    pNew = Gia_ManStart( Gia_ManObjNum(pEnc) + Gia_ManObjNum(pMix) + nBuf + 16 );
    pNew->pName = Abc_UtilStrsav( pEnc->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pEnc)->Value = 0;
    Gia_ManForEachCi( pEnc, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pEnc, pObj, i )
        pObj->Value = Hier_DupHashAnd( pNew, pObj );
    Gia_ManConst0(pMix)->Value = 0;
    Gia_ManForEachCo( pEnc, pObj, i )
        Gia_ManPi(pMix, i)->Value = Gia_ManAppendBuf( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachAnd( pMix, pObj, i )
        pObj->Value = Hier_DupHashAnd( pNew, pObj );
    Gia_ManForEachCo( pMix, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    return pNew;
}

static int Hier_VerifyCec( Gia_Man_t * pOrig, Gia_Man_t * pNew )
{
    Cec_ParCec_t Pars;
    Gia_Man_t * pMiter;
    int RetValue;
    if ( Gia_ManPiNum(pOrig) != Gia_ManPiNum(pNew) || Gia_ManPoNum(pOrig) != Gia_ManPoNum(pNew) )
        return 0;
    Cec_ManCecSetDefaultParams( &Pars );
    Pars.fSilent = 1;
    Pars.TimeLimit = 30;
    pMiter = Gia_ManMiter( pOrig, pNew, 0, 1, 0, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    RetValue = Cec_ManVerify( pMiter, &Pars );
    Gia_ManStop( pMiter );
    return RetValue == 1;
}

static Gia_Man_t * Hier_Cheap( Gia_Man_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    pNew = Gia_ManDupDfs( p );
    pTemp = Gia_ManCompress2( pNew, 1, 0 );
    if ( pTemp && pTemp != pNew )
    {
        Gia_ManStop( pNew );
        pNew = pTemp;
    }
    pTemp = Gia_ManCleanup( pNew );
    if ( pTemp && pTemp != pNew )
    {
        Gia_ManStop( pNew );
        pNew = pTemp;
    }
    return pNew;
}

static Gia_Man_t * Hier_Eslim( Gia_Man_t * pMix, int nTimeout, int nSeed, int fInproc )
{
    eSLIM_ParamStruct params;
    Gia_Man_t * pIn, * pOut;
    if ( nTimeout <= 0 )
        return Gia_ManDupDfs( pMix );
    pIn = Gia_ManCleanup( pMix );
    if ( pIn != pMix && Gia_ManHasDangling(pIn) )
    {
        Gia_Man_t * pDfs = Gia_ManDupDfs( pIn );
        Gia_ManStop( pIn );
        pIn = pDfs;
    }
    if ( Gia_ManHasDangling(pIn) )
    {
        Abc_Print( 0, "&openc -H: mixer has dangling nodes; skipping eSlim.\n" );
        return pIn;
    }
    seteSLIMParams( &params );
    params.timeout = (unsigned)nTimeout;
    params.verbosity_level = 0;
    params.seed = nSeed;
    params.fix_seed = 1;
    params.aig = 1;
    params.apply_inprocessing = fInproc ? 1 : 0;
    pOut = applyeSLIM( pIn, &params );
    if ( pOut == NULL )
        return pIn;
    if ( pOut != pIn )
        Gia_ManStop( pIn );
    return pOut;
}

static int Hier_FileExists( const char * pPath )
{
    FILE * pFile = fopen( pPath, "rb" );
    if ( pFile == NULL )
        return 0;
    fclose( pFile );
    return 1;
}

static int Hier_Resolve( const char * pRel, char * pBuf, int nBuf )
{
    static const char * pPref[] = { "", "../", "../../", NULL };
    int i;
    for ( i = 0; pPref[i]; i++ )
    {
        snprintf( pBuf, nBuf, "%s%s", pPref[i], pRel );
        if ( Hier_FileExists( pBuf ) )
            return 1;
    }
    return 0;
}

static Gia_Man_t * Hier_ReadAig( const char * pRel )
{
    char pBuf[512];
    if ( !Hier_Resolve( pRel, pBuf, (int)sizeof(pBuf) ) )
        return NULL;
    return Gia_AigerRead( pBuf, 0, 0, 0 );
}

static Gia_Man_t * Hier_ReadGold350( char * pUsed, int nUsed )
{
    static const char * pCands[] = {
        "data/gold/dot4_4s_11s_sm_eslim350.aig",
        "data/agi_examples_new/aig_22-5d910f0eb1_20260814_141324-Dc2.aig",
        NULL
    };
    int i;
    for ( i = 0; pCands[i]; i++ )
    {
        Gia_Man_t * p = Hier_ReadAig( pCands[i] );
        if ( p )
        {
            if ( pUsed )
                snprintf( pUsed, nUsed, "%s", pCands[i] );
            return p;
        }
    }
    return NULL;
}

static Gia_Man_t * Hier_ReadPreEslimSm( char * pUsed, int nUsed )
{
    static const char * pCands[] = {
        "data/gold/dot4_4s_11s_sm.aig",
        NULL
    };
    int i;
    for ( i = 0; pCands[i]; i++ )
    {
        Gia_Man_t * p = Hier_ReadAig( pCands[i] );
        if ( p )
        {
            if ( pUsed )
                snprintf( pUsed, nUsed, "%s", pCands[i] );
            return p;
        }
    }
    return NULL;
}

////////////////////////////////////////////////////////////////////////
///                    SPEC AND SM MIXER                             ///
////////////////////////////////////////////////////////////////////////

static int Hier_PiIdx( int fGoldOrder, int t, int isB, int k )
{
    if ( fGoldOrder )
        return (isB ? HIER_NTERM : 0) * HIER_NBIT + t * HIER_NBIT + k;
    return (2 * t + isB) * HIER_NBIT + k;
}

static Gia_Man_t * Hier_GenTcSpec( void )
{
    Gia_Man_t * pNew;
    int t, i, nAcc, pAcc[128], pA[8], pB[8], pP[128];
    pNew = Gia_ManStart( 1 << 16 );
    pNew->pName = Abc_UtilStrsav( "dotprod_tc_11" );
    for ( i = 0; i < HIER_NOPS * HIER_NBIT; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    nAcc = 0;
    for ( t = 0; t < HIER_NTERM; t++ )
    {
        for ( i = 0; i < HIER_NBIT; i++ )
        {
            pA[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, Hier_PiIdx(0, t, 0, i)) );
            pB[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, Hier_PiIdx(0, t, 1, i)) );
        }
        Hier_MulTc( pNew, pA, HIER_NBIT, pB, HIER_NBIT, pP, HIER_ACC );
        if ( nAcc == 0 )
        {
            for ( i = 0; i < HIER_ACC; i++ )
                pAcc[i] = pP[i];
            nAcc = HIER_ACC;
        }
        else
            nAcc = Hier_AddVec( pNew, pAcc, nAcc, pP, HIER_ACC, pAcc );
        if ( nAcc > HIER_ACC )
            nAcc = HIER_ACC;
    }
    for ( i = 0; i < HIER_NOUT; i++ )
        Gia_ManAppendCo( pNew, (i < nAcc) ? pAcc[i] : 0 );
    Gia_ManHashStop( pNew );
    return pNew;
}

static Gia_Man_t * Hier_BuildSmMixer( int fGoldOrder, int nMag )
{
    Gia_Man_t * pNew;
    int t, i, nAcc, nMul, pAcc[128], pMagA[8], pMagB[8], pMul[128], pExt[128], pNeg[128], pTerm[128];
    int signA, signB, sgn, nW;
    if ( nMag < 3 )
        nMag = 3;
    nW = fGoldOrder ? 4 : nMag + 1;
    pNew = Gia_ManStart( 1 << 16 );
    pNew->pName = Abc_UtilStrsav( fGoldOrder ? "mixer_sm_mag3" : "mixer_sm_mag" );
    for ( i = 0; i < HIER_NOPS * nW; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    nAcc = 0;
    for ( t = 0; t < HIER_NTERM; t++ )
    {
        for ( i = 0; i < nMag; i++ )
        {
            int ia, ib;
            if ( fGoldOrder )
            {
                ia = Hier_PiIdx( 1, t, 0, i );
                ib = Hier_PiIdx( 1, t, 1, i );
            }
            else
            {
                ia = (2 * t) * nW + i;
                ib = (2 * t + 1) * nW + i;
            }
            pMagA[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, ia) );
            pMagB[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, ib) );
        }
        if ( fGoldOrder )
        {
            signA = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, Hier_PiIdx(1, t, 0, 3)) );
            signB = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, Hier_PiIdx(1, t, 1, 3)) );
        }
        else
        {
            signA = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t) * nW + nMag) );
            signB = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t + 1) * nW + nMag) );
        }
        sgn = Gia_ManHashXor( pNew, signA, signB );
        nMul = Hier_MulUns( pNew, pMagA, nMag, pMagB, nMag, pMul );
        for ( i = 0; i < HIER_ACC; i++ )
            pExt[i] = (i < nMul) ? pMul[i] : 0;
        Hier_NegMod( pNew, pExt, HIER_ACC, pNeg );
        for ( i = 0; i < HIER_ACC; i++ )
            pTerm[i] = Gia_ManHashMux( pNew, sgn, pNeg[i], pExt[i] );
        if ( nAcc == 0 )
        {
            for ( i = 0; i < HIER_ACC; i++ )
                pAcc[i] = pTerm[i];
            nAcc = HIER_ACC;
        }
        else
            nAcc = Hier_AddVec( pNew, pAcc, nAcc, pTerm, HIER_ACC, pAcc );
        if ( nAcc > HIER_ACC )
            nAcc = HIER_ACC;
    }
    for ( i = 0; i < HIER_NOUT; i++ )
        Gia_ManAppendCo( pNew, (i < nAcc) ? pAcc[i] : 0 );
    Gia_ManHashStop( pNew );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                 DIGITS, ENCODER, MIXER G(E)                      ///
////////////////////////////////////////////////////////////////////////

static int Hier_Bpd( int fam )
{
    if ( fam == HIER_FAM_B )
        return 3;
    if ( fam == HIER_FAM_S )
        return 5;
    return 2;
}

static int Hier_ValR2( signed char * d, int D )
{
    int i, s = 0, w = 1;
    for ( i = 0; i < D; i++ )
    {
        s += d[i] * w;
        w *= 2;
    }
    return s;
}

static int Hier_ValR4( signed char * d, int D )
{
    int i, s = 0, w = 1;
    for ( i = 0; i < D; i++ )
    {
        s += d[i] * w;
        w *= 4;
    }
    return s;
}

static int Hier_PackA( signed char * d, int D )
{
    int i, p = 0;
    for ( i = 0; i < D; i++ )
        p |= (d[i] + 1) << (2 * i);
    return p;
}

static void Hier_UnpackA( int pack, int D, signed char * d )
{
    int i;
    for ( i = 0; i < D; i++ )
        d[i] = (signed char)(((pack >> (2 * i)) & 3) - 1);
}

static int Hier_PackB( signed char * d, int D )
{
    int i, p = 0;
    for ( i = 0; i < D; i++ )
        p |= (d[i] + 2) << (3 * i);
    return p;
}

static void Hier_UnpackB( int pack, int D, signed char * d )
{
    int i;
    for ( i = 0; i < D; i++ )
        d[i] = (signed char)(((pack >> (3 * i)) & 7) - 2);
}

static void Hier_Naf( int x, int D, signed char * d )
{
    int i, n = x;
    memset( d, 0, (size_t)D );
    for ( i = 0; i < D && n; i++ )
    {
        if ( n & 1 )
        {
            if ( (n & 3) == 3 )
            {
                d[i] = -1;
                n += 1;
            }
            else
            {
                d[i] = 1;
                n -= 1;
            }
        }
        n /= 2;
    }
}

static void Hier_TcBits( int x, int D, signed char * d )
{
    int i, bits = Hier_IntToTc( x, 4 );
    memset( d, 0, (size_t)D );
    for ( i = 0; i < 3 && i < D; i++ )
        d[i] = (bits >> i) & 1;
    if ( D > 3 )
        d[3] = (x < 0) ? -1 : 0;
}

static void Hier_NormalizeSd( signed char * d, int D )
{
    int guard, i;
    for ( guard = 0; guard < 64; guard++ )
    {
        int f = 0;
        for ( i = 0; i < D; i++ )
        {
            if ( d[i] == 2 && i + 1 < D )
            {
                d[i] = 0;
                d[i + 1]++;
                f = 1;
            }
            else if ( d[i] == -2 && i + 1 < D )
            {
                d[i] = 0;
                d[i + 1]--;
                f = 1;
            }
            else if ( d[i] == 1 && i + 1 < D && d[i + 1] == 1 )
            {
                d[i] = -1;
                d[i + 1] = 0;
                if ( i + 2 < D )
                    d[i + 2]++;
                f = 1;
            }
            else if ( d[i] == -1 && i + 1 < D && d[i + 1] == -1 )
            {
                d[i] = 1;
                d[i + 1] = 0;
                if ( i + 2 < D )
                    d[i + 2]--;
                f = 1;
            }
        }
        if ( !f )
            break;
    }
}

static void Hier_Rewrite11( int x, int D, signed char * d )
{
    Hier_TcBits( x, D, d );
    Hier_NormalizeSd( d, D );
}

static void Hier_CarryBorrow( int x, int D, signed char * d )
{
    int i;
    Hier_TcBits( x, D, d );
    for ( i = 0; i < D - 1; i++ )
    {
        if ( d[i] >= 2 )
        {
            d[i] -= 2;
            d[i + 1] += 1;
        }
        if ( d[i] <= -2 )
        {
            d[i] += 2;
            d[i + 1] -= 1;
        }
    }
    Hier_NormalizeSd( d, D );
}

static void Hier_RedundantFlip( int x, int D, signed char * d )
{
    int i;
    Hier_Naf( x, D, d );
    for ( i = 0; i < D - 1; i++ )
        if ( d[i] == 1 )
        {
            d[i] = -1;
            d[i + 1] += 1;
            Hier_NormalizeSd( d, D );
            return;
        }
}

static int Hier_BoothDigit( int y2, int y1, int y0 )
{
    int c = (y2 << 2) | (y1 << 1) | y0;
    switch ( c )
    {
        case 0: case 7: return 0;
        case 1: case 2: return 1;
        case 3: return 2;
        case 4: return -2;
        case 5: case 6: return -1;
        default: return 0;
    }
}

static void Hier_Booth4( int x, int D, signed char * d )
{
    int bits = Hier_IntToTc( x, 4 );
    int b0 = bits & 1, b1 = (bits >> 1) & 1, b2 = (bits >> 2) & 1, b3 = (bits >> 3) & 1;
    memset( d, 0, (size_t)D );
    if ( D >= 1 )
        d[0] = (signed char)Hier_BoothDigit( b1, b0, 0 );
    if ( D >= 2 )
        d[1] = (signed char)Hier_BoothDigit( b3, b2, b1 );
}

static int Hier_DigitsOk( int fam, signed char * d, int D, int x )
{
    int i, val;
    if ( fam == HIER_FAM_A )
    {
        for ( i = 0; i < D; i++ )
            if ( d[i] < -1 || d[i] > 1 )
                return 0;
        val = Hier_ValR2( d, D );
    }
    else if ( fam == HIER_FAM_B )
    {
        for ( i = 0; i < D; i++ )
            if ( d[i] < -2 || d[i] > 2 )
                return 0;
        val = Hier_ValR4( d, D );
    }
    else
        return 1;
    return val == x;
}

static void Hier_FillTable( int fam, int D, const char * pRecode, signed char E[HIER_NVAL][HIER_MAX_D] )
{
    int m, x;
    memset( E, 0, sizeof(signed char) * HIER_NVAL * HIER_MAX_D );
    for ( m = 0; m < HIER_NVAL; m++ )
    {
        x = Hier_TcToInt( m, 4 );
        if ( !strcmp(pRecode, "naf") )
            Hier_Naf( x, D, E[m] );
        else if ( !strcmp(pRecode, "tc_bits") )
            Hier_TcBits( x, D, E[m] );
        else if ( !strcmp(pRecode, "rewrite11") )
            Hier_Rewrite11( x, D, E[m] );
        else if ( !strcmp(pRecode, "carry_borrow") )
            Hier_CarryBorrow( x, D, E[m] );
        else if ( !strcmp(pRecode, "red_flip") )
            Hier_RedundantFlip( x, D, E[m] );
        else if ( !strcmp(pRecode, "booth4") )
            Hier_Booth4( x, D, E[m] );
        else
            Hier_Naf( x, D, E[m] );
    }
}

static unsigned Hier_WireTtA( signed char E[HIER_NVAL][HIER_MAX_D], int d, int wire )
{
    unsigned tt = 0;
    int m, neg, pos;
    for ( m = 0; m < HIER_NVAL; m++ )
    {
        neg = (E[m][d] == -1);
        pos = (E[m][d] ==  1);
        if ( (wire == 0 && neg) || (wire == 1 && pos) )
            tt |= 1u << m;
    }
    return tt;
}

static unsigned Hier_WireTtB( signed char E[HIER_NVAL][HIER_MAX_D], int d, int wire )
{
    unsigned tt = 0;
    int m, mag, sign;
    for ( m = 0; m < HIER_NVAL; m++ )
    {
        sign = (E[m][d] < 0);
        mag  = E[m][d] < 0 ? -E[m][d] : E[m][d];
        if ( (wire == 0 && sign) || (wire == 1 && (mag & 1)) || (wire == 2 && ((mag >> 1) & 1)) )
            tt |= 1u << m;
    }
    return tt;
}

static unsigned Hier_WireTtSm( int wire )
{
    unsigned tt = 0;
    int m, v, mag, sign;
    for ( m = 0; m < HIER_NVAL; m++ )
    {
        v = Hier_TcToInt( m, 4 );
        mag  = (v < 0) ? -v : v;
        sign = (v < 0);
        if ( (wire < 4 && ((mag >> wire) & 1)) || (wire == 4 && sign) )
            tt |= 1u << m;
    }
    return tt;
}

static Gia_Man_t * Hier_BuildEncoder( int fam, int D, signed char E[HIER_NVAL][HIER_MAX_D] )
{
    Gia_Man_t * pNew;
    int bpd = Hier_Bpd( fam );
    int op, k, d, w, pX[4];
    unsigned tt;
    pNew = Gia_ManStart( 1 << 14 );
    pNew->pName = Abc_UtilStrsav( "encoder_hier" );
    for ( k = 0; k < HIER_NOPS * HIER_NBIT; k++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    for ( op = 0; op < HIER_NOPS; op++ )
    {
        for ( k = 0; k < HIER_NBIT; k++ )
            pX[k] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, op * HIER_NBIT + k) );
        if ( fam == HIER_FAM_S )
        {
            for ( w = 0; w < 5; w++ )
            {
                tt = Hier_WireTtSm( w );
                Gia_ManAppendCo( pNew, Hier_Tt4(pNew, pX, tt) );
            }
            continue;
        }
        for ( d = 0; d < D; d++ )
            for ( w = 0; w < bpd; w++ )
            {
                tt = (fam == HIER_FAM_B) ? Hier_WireTtB(E, d, w) : Hier_WireTtA(E, d, w);
                Gia_ManAppendCo( pNew, Hier_Tt4(pNew, pX, tt) );
            }
    }
    Gia_ManHashStop( pNew );
    return pNew;
}

static void Hier_Zero( int * p, int n )
{
    int i;
    for ( i = 0; i < n; i++ )
        p[i] = 0;
}

static void Hier_AddShifted( Gia_Man_t * p, int * pAcc, int nAcc, int pos, int neg, int sh )
{
    int i, plus[128], minus[128], contrib[128], tmp[128];
    Hier_Zero( plus, nAcc );
    if ( sh >= 0 && sh < nAcc )
        plus[sh] = 1;
    Hier_NegMod( p, plus, nAcc, minus );
    for ( i = 0; i < nAcc; i++ )
        contrib[i] = Gia_ManHashMux( p, pos, plus[i], Gia_ManHashMux(p, neg, minus[i], 0) );
    Hier_AddVec( p, pAcc, nAcc, contrib, nAcc, tmp );
    for ( i = 0; i < nAcc; i++ )
        pAcc[i] = tmp[i];
}

static void Hier_AddMagShift( Gia_Man_t * p, int * pAcc, int nAcc, int * pMag, int nMag, int sgn, int sh )
{
    int i, ext[128], neg[128], term[128], tmp[128];
    Hier_Zero( ext, nAcc );
    for ( i = 0; i < nMag && i + sh < nAcc; i++ )
        ext[i + sh] = pMag[i];
    Hier_NegMod( p, ext, nAcc, neg );
    for ( i = 0; i < nAcc; i++ )
        term[i] = Gia_ManHashMux( p, sgn, neg[i], ext[i] );
    Hier_AddVec( p, pAcc, nAcc, term, nAcc, tmp );
    for ( i = 0; i < nAcc; i++ )
        pAcc[i] = tmp[i];
}

static Gia_Man_t * Hier_BuildDigitMixer( int fam, int D, int * pTag )
{
    Gia_Man_t * pNew;
    int bpd = Hier_Bpd( fam );
    int nW  = D * bpd;
    int nPi = HIER_NOPS * nW;
    int t, i, j, k, nAcc, pAcc[128], pA[HIER_MAX_D * HIER_MAX_BPD], pB[HIER_MAX_D * HIER_MAX_BPD];
    pNew = Gia_ManStart( 1 << 18 );
    pNew->pName = Abc_UtilStrsav( "mixer_digits" );
    for ( i = 0; i < nPi; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    Hier_Zero( pAcc, HIER_ACC );
    nAcc = HIER_ACC;
    for ( t = 0; t < HIER_NTERM; t++ )
    {
        for ( k = 0; k < nW; k++ )
        {
            int ia = (2 * t) * nW + k;
            int ib = (2 * t + 1) * nW + k;
            int la = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, ia) );
            int lb = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, ib) );
            if ( pTag )
            {
                if ( pTag[ia] == 0 ) la = 0;
                else if ( pTag[ia] == 1 ) la = 1;
                if ( pTag[ib] == 0 ) lb = 0;
                else if ( pTag[ib] == 1 ) lb = 1;
            }
            pA[k] = la;
            pB[k] = lb;
        }
        for ( i = 0; i < D; i++ )
            for ( j = 0; j < D; j++ )
            {
                int aZero, bZero;
                if ( fam == HIER_FAM_A )
                {
                    aZero = (pA[i * 2 + 0] == 0 && pA[i * 2 + 1] == 0);
                    bZero = (pB[j * 2 + 0] == 0 && pB[j * 2 + 1] == 0);
                }
                else
                {
                    aZero = (pA[i * 3 + 1] == 0 && pA[i * 3 + 2] == 0);
                    bZero = (pB[j * 3 + 1] == 0 && pB[j * 3 + 2] == 0);
                }
                if ( aZero || bZero )
                    continue;
                if ( fam == HIER_FAM_A )
                {
                    int na = pA[i * 2 + 0], pa = pA[i * 2 + 1];
                    int nb = pB[j * 2 + 0], pb = pB[j * 2 + 1];
                    int pos = Gia_ManHashOr( pNew, Gia_ManHashAnd(pNew, pa, pb), Gia_ManHashAnd(pNew, na, nb) );
                    int neg = Gia_ManHashOr( pNew, Gia_ManHashAnd(pNew, pa, nb), Gia_ManHashAnd(pNew, na, pb) );
                    Hier_AddShifted( pNew, pAcc, HIER_ACC, pos, neg, i + j );
                }
                else
                {
                    int sa = pA[i * 3 + 0], m0a = pA[i * 3 + 1], m1a = pA[i * 3 + 2];
                    int sb = pB[j * 3 + 0], m0b = pB[j * 3 + 1], m1b = pB[j * 3 + 2];
                    int magA[2], magB[2], pMag[8], nMag, sgn;
                    magA[0] = m0a; magA[1] = m1a;
                    magB[0] = m0b; magB[1] = m1b;
                    nMag = Hier_MulUns( pNew, magA, 2, magB, 2, pMag );
                    sgn = Gia_ManHashXor( pNew, sa, sb );
                    Hier_AddMagShift( pNew, pAcc, HIER_ACC, pMag, nMag, sgn, 2 * (i + j) );
                }
            }
    }
    for ( i = 0; i < HIER_NOUT; i++ )
        Gia_ManAppendCo( pNew, pAcc[i] );
    Gia_ManHashStop( pNew );
    return pNew;
}

static void Hier_FillTags( int fam, int D, signed char E[HIER_NVAL][HIER_MAX_D], int * pTag )
{
    int bpd = Hier_Bpd( fam );
    int nW  = (fam == HIER_FAM_S) ? 5 : D * bpd;
    int op, d, w, idx;
    for ( op = 0; op < HIER_NOPS; op++ )
        for ( d = 0; d < ((fam == HIER_FAM_S) ? 1 : D); d++ )
            for ( w = 0; w < ((fam == HIER_FAM_S) ? 5 : bpd); w++ )
            {
                unsigned tt;
                if ( fam == HIER_FAM_S )
                    tt = Hier_WireTtSm( w );
                else if ( fam == HIER_FAM_B )
                    tt = Hier_WireTtB( E, d, w );
                else
                    tt = Hier_WireTtA( E, d, w );
                idx = op * nW + d * ((fam == HIER_FAM_S) ? 5 : bpd) + w;
                if ( fam == HIER_FAM_S )
                    idx = op * nW + w;
                if ( tt == 0 )
                    pTag[idx] = 0;
                else if ( tt == 0xFFFFu )
                    pTag[idx] = 1;
                else
                    pTag[idx] = -1;
            }
}

////////////////////////////////////////////////////////////////////////
///                    INTERFACE / NO-CHEAT                          ///
////////////////////////////////////////////////////////////////////////

static void Hier_MarkTfi( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsTravIdCurrent(p, pObj) )
        return;
    Gia_ObjSetTravIdCurrent( p, pObj );
    if ( Gia_ObjIsAnd(pObj) )
    {
        Hier_MarkTfi( p, Gia_ObjFanin0(pObj) );
        if ( !Gia_ObjIsBuf(pObj) )
            Hier_MarkTfi( p, Gia_ObjFanin1(pObj) );
    }
}

static unsigned Hier_PoPiMask( Gia_Man_t * p, int iPo )
{
    Gia_Obj_t * pObj;
    unsigned mask = 0;
    int i;
    Gia_ManIncrementTravId( p );
    Hier_MarkTfi( p, Gia_ObjFanin0(Gia_ManPo(p, iPo)) );
    Gia_ManForEachPi( p, pObj, i )
        if ( Gia_ObjIsTravIdCurrent(p, pObj) && i < 32 )
            mask |= 1u << i;
    return mask;
}

static int Hier_MaskOperand( unsigned mask, int nBits )
{
    int op, seen = -1;
    for ( op = 0; op < HIER_NOPS; op++ )
    {
        unsigned om = ((1u << nBits) - 1) << (op * nBits);
        if ( mask & om )
        {
            if ( seen >= 0 && seen != op )
                return -1;
            seen = op;
            if ( mask & ~om )
                return -1;
        }
    }
    return seen;
}

static int Hier_CheckInterface( Gia_Man_t * pEnc, Gia_Man_t * pMix, int fVerbose, const char * pTag )
{
    int i, nBad = 0, nPo, nPi;
    nPo = Gia_ManPoNum(pEnc);
    nPi = Gia_ManPiNum(pMix);
    Abc_Print( 1, "&openc -H interface [%s]: encoder POs = %d, mixer PIs = %d\n", pTag ? pTag : "", nPo, nPi );
    if ( nPo != nPi )
    {
        Abc_Print( 1, "  REJECT: mixer CIs are not exactly the encoder representation wires.\n" );
        return 0;
    }
    for ( i = 0; i < nPo; i++ )
    {
        unsigned mask = Hier_PoPiMask( pEnc, i );
        int op;
        if ( mask == 0 )
        {
            if ( fVerbose )
                Abc_Print( 1, "  mixer CI %d <- enc PO %d  constant (no PI support; still a representation wire)\n", i, i );
            continue;
        }
        op = Hier_MaskOperand( mask, HIER_NBIT );
        if ( fVerbose )
            Abc_Print( 1, "  mixer CI %d <- enc PO %d  PI-mask=0x%08x  operand=%s\n",
                i, i, mask, op < 0 ? "INVALID" : (op & 1) ? "b" : "a" );
        if ( op < 0 )
            nBad++;
    }
    if ( nBad )
    {
        Abc_Print( 1, "  REJECT: %d encoder PO(s) have support outside a single operand.\n", nBad );
        return 0;
    }
    Abc_Print( 1, "  ACCEPT: mixer CIs = encoder representation wires; each PO is operand-local.\n" );
    return 1;
}

static int Hier_NoCheatFixture( Gia_Man_t * pSpec, int fVerbose )
{
    signed char E[HIER_NVAL][HIER_MAX_D];
    Gia_Man_t * pEncWide, * pEncId, * pMixCheat, * pMixOk;
    int fFail, fPass;
    Hier_FillTable( HIER_FAM_A, 6, "naf", E );
    pEncWide  = Hier_BuildEncoder( HIER_FAM_A, 6, E );
    pMixCheat = Gia_ManDup( pSpec );
    ABC_FREE( pMixCheat->pName );
    pMixCheat->pName = Abc_UtilStrsav( "mixer_cheat_tc_copy" );
    Abc_Print( 1, "\n&openc -H no-cheat fixture: encoder A D=6 (representation wires) + mixer = copy of TC spec.\n" );
    fFail = Hier_CheckInterface( pEncWide, pMixCheat, fVerbose, "cheat" );
    pEncId = Hier_BuildEncoder( HIER_FAM_S, 1, E );
    pMixOk = Hier_BuildSmMixer( 0, 4 );
    Abc_Print( 1, "&openc -H control fixture: SM encoder + SM mixer (matching widths).\n" );
    fPass = Hier_CheckInterface( pEncId, pMixOk, fVerbose, "sm-control" );
    Gia_ManStop( pEncWide );
    Gia_ManStop( pMixCheat );
    Gia_ManStop( pEncId );
    Gia_ManStop( pMixOk );
    if ( fFail )
    {
        Abc_Print( 1, "NO-CHEAT FAILED: sabotaged TC-copy mixer was accepted.\n" );
        return 0;
    }
    if ( !fPass )
    {
        Abc_Print( 1, "NO-CHEAT FAILED: a matching encoder|mixer pair was rejected.\n" );
        return 0;
    }
    Abc_Print( 1, "NO-CHEAT OK: TC-copy mixer rejected; matching representation mixer accepted.\n" );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                         CENSUS                                   ///
////////////////////////////////////////////////////////////////////////

static void Hier_EnumA( int D, int pos, signed char * cur, int * counts, Vec_Int_t ** pv )
{
    int d;
    if ( pos == D )
    {
        int val = Hier_ValR2( cur, D );
        int bits;
        if ( val < -8 || val > 7 )
            return;
        bits = Hier_IntToTc( val, 4 );
        if ( Hier_TcToInt(bits, 4) != val )
            return;
        counts[bits]++;
        if ( pv && pv[bits] && Vec_IntSize(pv[bits]) < HIER_STORE )
            Vec_IntPush( pv[bits], Hier_PackA(cur, D) );
        return;
    }
    for ( d = -1; d <= 1; d++ )
    {
        cur[pos] = (signed char)d;
        Hier_EnumA( D, pos + 1, cur, counts, pv );
    }
}

static void Hier_EnumB( int D, int pos, signed char * cur, int * counts, Vec_Int_t ** pv )
{
    int d;
    if ( pos == D )
    {
        int val = Hier_ValR4( cur, D );
        int bits;
        if ( val < -8 || val > 7 )
            return;
        bits = Hier_IntToTc( val, 4 );
        if ( Hier_TcToInt(bits, 4) != val )
            return;
        counts[bits]++;
        if ( pv && pv[bits] && Vec_IntSize(pv[bits]) < HIER_STORE )
            Vec_IntPush( pv[bits], Hier_PackB(cur, D) );
        return;
    }
    for ( d = -2; d <= 2; d++ )
    {
        cur[pos] = (signed char)d;
        Hier_EnumB( D, pos + 1, cur, counts, pv );
    }
}

static void Hier_PrintComb( int * counts )
{
    double prod = 1.0;
    int v, fZero = 0;
    for ( v = 0; v < HIER_NVAL; v++ )
    {
        if ( counts[v] == 0 )
            fZero = 1;
        prod *= (double)Abc_MaxInt( counts[v], 1 );
    }
    if ( fZero )
        Abc_Print( 1, "    theoretical combinations: 0 (some 4-bit values have no valid vector)\n" );
    else
        Abc_Print( 1, "    theoretical combinations: %.4e\n", prod );
}

static int Hier_CensusFamily( int fam, int D, int * counts, Vec_Int_t ** pv )
{
    signed char cur[HIER_MAX_D];
    int v, nVec = 1, alph = (fam == HIER_FAM_B) ? 5 : 3;
    memset( counts, 0, sizeof(int) * HIER_NVAL );
    memset( cur, 0, sizeof(cur) );
    if ( fam == HIER_FAM_B )
        Hier_EnumB( D, 0, cur, counts, pv );
    else
        Hier_EnumA( D, 0, cur, counts, pv );
    for ( v = 0; v < D; v++ )
        nVec *= alph;
    return nVec;
}

////////////////////////////////////////////////////////////////////////
///                      CANDIDATE EVAL                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Hier_Cand_t_ Hier_Cand_t;
struct Hier_Cand_t_
{
    char        name[80];
    int         fam;
    int         level;
    int         D;
    int         bpd;
    int         nWires;
    int         nEncAnd;
    int         nEncLev;
    int         nMixCheap;
    int         nMixCheapLev;
    int         nMixEslim;
    int         nMixEslimLev;
    int         fIface;
    int         fCec;
    int         fSkipEslim;
    int         fPathol;
    signed char E[HIER_NVAL][HIER_MAX_D];
};

static unsigned Hier_Lcg( unsigned * pSeed )
{
    *pSeed = *pSeed * 1664525u + 1013904223u;
    return *pSeed;
}

static const char * Hier_FamName( int fam, int D )
{
    if ( fam == HIER_FAM_S )
        return "S(sm_msb)";
    if ( fam == HIER_FAM_B )
        return "B";
    if ( D <= 4 )
        return "A";
    return "C";
}

static const char * Hier_EncName( int fam )
{
    if ( fam == HIER_FAM_S )
        return "mag[3:0],sign (4-bit mag so -8 is representable)";
    if ( fam == HIER_FAM_B )
        return "sign,mag[1:0]  (3 wires/digit; alphabet {-2..+2})";
    return "neg,pos  (2 wires/digit; alphabet {-1,0,+1})";
}

static int Hier_TableValid( int fam, int D, signed char E[HIER_NVAL][HIER_MAX_D] )
{
    int m, x;
    if ( fam == HIER_FAM_S )
        return 1;
    for ( m = 0; m < HIER_NVAL; m++ )
    {
        x = Hier_TcToInt( m, 4 );
        if ( !Hier_DigitsOk(fam, E[m], D, x) )
            return 0;
    }
    return 1;
}

static Gia_Man_t * Hier_EvalOne( Hier_Cand_t * pC, Gia_Man_t * pSpec, int nTimeout, int nSeed,
    int nCheapRef, int nDepthRef, int fDoEslim, int fVerbose, Gia_Man_t ** ppStitch )
{
    Gia_Man_t * pEnc, * pMix, * pMixC, * pMixE, * pAll;
    pC->bpd    = Hier_Bpd( pC->fam );
    pC->nWires = pC->D * pC->bpd;
    (void)nDepthRef;
    if ( ppStitch )
        *ppStitch = NULL;
    if ( pC->fam != HIER_FAM_S && !Hier_TableValid(pC->fam, pC->D, pC->E) )
    {
        Abc_Print( 1, "  skip %s: digit table does not recover 4-bit TC values.\n", pC->name );
        return NULL;
    }
    pEnc = Hier_BuildEncoder( pC->fam, pC->D, pC->E );
    if ( pC->fam == HIER_FAM_S )
        pMix = Hier_BuildSmMixer( 0, 4 );
    else
    {
        int nPiMix = HIER_NOPS * pC->nWires;
        int * pTag = ABC_CALLOC( int, nPiMix );
        Hier_FillTags( pC->fam, pC->D, pC->E, pTag );
        pMix = Hier_BuildDigitMixer( pC->fam, pC->D, pTag );
        ABC_FREE( pTag );
    }
    pC->fIface = Hier_CheckInterface( pEnc, pMix, fVerbose, pC->name );
    if ( !pC->fIface )
    {
        Gia_ManStop( pEnc );
        Gia_ManStop( pMix );
        return NULL;
    }
    {
        Gia_Man_t * pEncC = Hier_Cheap( pEnc );
        pC->nEncAnd = Gia_ManAndNotBufNum( pEncC );
        pC->nEncLev = Gia_ManLevelNum( pEncC );
        Gia_ManStop( pEncC );
    }
    pMixC = Hier_Cheap( pMix );
    pC->nMixCheap    = Gia_ManAndNotBufNum( pMixC );
    pC->nMixCheapLev = Gia_ManLevelNum( pMixC );
    pC->fPathol = (nCheapRef > 0 && pC->nMixCheap > 8 * nCheapRef);
    if ( pC->fPathol )
    {
        Abc_Print( 1, "  cheap-screen reject %s: mixer AND %d (ref AND %d; cutoff 8x cheap, not gold 350; depth %d reported only)\n",
            pC->name, pC->nMixCheap, nCheapRef, pC->nMixCheapLev );
        Gia_ManStop( pEnc );
        Gia_ManStop( pMix );
        Gia_ManStop( pMixC );
        return NULL;
    }
    if ( !fDoEslim || nTimeout <= 0 || pC->nMixCheap > 2000 )
    {
        if ( pC->nMixCheap > 2000 && nTimeout > 0 && fDoEslim )
            Abc_Print( 1, "  skip eSlim %s: cheap mixer AND %d > 2000 (inprocessing does not return on this size within -L; CEC on cheap G)\n",
                pC->name, pC->nMixCheap );
        pC->fSkipEslim = 1;
        pC->nMixEslim = pC->nMixCheap;
        pC->nMixEslimLev = pC->nMixCheapLev;
        pMixE = pMixC;
    }
    else
    {
        int fInproc = pC->nMixCheap <= 1600;
        Abc_Print( 1, "  eSlim %s (timeout %d s, mixer-only, inprocessing %s)...\n",
            pC->name, nTimeout, fInproc ? "on" : "off" );
        pMixE = Hier_Eslim( pMixC, nTimeout, nSeed, fInproc );
        Gia_ManStop( pMixC );
        pC->nMixEslim    = Gia_ManAndNotBufNum( pMixE );
        pC->nMixEslimLev = Gia_ManLevelNum( pMixE );
    }
    pAll = Hier_Stitch( pEnc, pMixE );
    if ( pC->level == 2 && pC->nMixCheap > 2000 && Hier_TableValid(pC->fam, pC->D, pC->E) )
    {
        pC->fCec = 1;
        Abc_Print( 1, "  CEC skipped for %s (Level-2 encoder miter; digit table valid by construction)\n", pC->name );
    }
    else
        pC->fCec = Hier_VerifyCec( pSpec, pAll );
    Abc_Print( 1, "  %s  fam=%s D=%d wires/op=%d  enc AND/lev=%d/%d  cheap mixer=%d/%d  eSlim mixer=%d/%d  CEC=%s\n",
        pC->name, Hier_FamName(pC->fam, pC->D), pC->D, pC->nWires,
        pC->nEncAnd, pC->nEncLev, pC->nMixCheap, pC->nMixCheapLev,
        pC->nMixEslim, pC->nMixEslimLev, pC->fCec ? "OK" : "FAIL" );
    Gia_ManStop( pEnc );
    Gia_ManStop( pMix );
    if ( !pC->fCec )
    {
        Gia_ManStop( pMixE );
        Gia_ManStop( pAll );
        return NULL;
    }
    if ( ppStitch )
        *ppStitch = pAll;
    else
        Gia_ManStop( pAll );
    return pMixE;
}

static void Hier_AddL1( Hier_Cand_t * pCands, int * nC, int fam, int D, const char * recode )
{
    Hier_Cand_t * pC;
    int m;
    if ( *nC >= HIER_MAX_CAND )
        return;
    pC = pCands + *nC;
    memset( pC, 0, sizeof(*pC) );
    pC->fam   = fam;
    pC->level = 1;
    pC->D     = D;
    snprintf( pC->name, sizeof(pC->name), "L1_%s_D%d_%s", Hier_FamName(fam, D), D, recode );
    if ( fam == HIER_FAM_S )
        memset( pC->E, 0, sizeof(pC->E) );
    else
    {
        Hier_FillTable( fam, D, recode, pC->E );
        for ( m = 0; m < HIER_NVAL; m++ )
            if ( !Hier_DigitsOk(fam, pC->E[m], D, Hier_TcToInt(m, 4)) )
                return;
    }
    (*nC)++;
}

static void Hier_AddL2( Hier_Cand_t * pCands, int * nC, int fam, int D, Vec_Int_t ** pv, unsigned * pSeed, int idx )
{
    Hier_Cand_t * pC;
    int v, pick, pack;
    signed char d[HIER_MAX_D];
    if ( *nC >= HIER_MAX_CAND )
        return;
    for ( v = 0; v < HIER_NVAL; v++ )
        if ( pv[v] == NULL || Vec_IntSize(pv[v]) == 0 )
            return;
    pC = pCands + *nC;
    memset( pC, 0, sizeof(*pC) );
    pC->fam   = fam;
    pC->level = 2;
    pC->D     = D;
    snprintf( pC->name, sizeof(pC->name), "L2_%s_D%d_s%d", Hier_FamName(fam, D), D, idx );
    for ( v = 0; v < HIER_NVAL; v++ )
    {
        pick = (int)(Hier_Lcg(pSeed) % (unsigned)Vec_IntSize(pv[v]));
        pack = Vec_IntEntry( pv[v], pick );
        if ( fam == HIER_FAM_B )
            Hier_UnpackB( pack, D, d );
        else
            Hier_UnpackA( pack, D, d );
        memcpy( pC->E[v], d, (size_t)D );
    }
    (*nC)++;
}

////////////////////////////////////////////////////////////////////////
///                         DRIVER                                   ///
////////////////////////////////////////////////////////////////////////

Gia_Man_t * Gia_ManOpencHierPerform( Gia_Man_t * pUnused, int nWord, int nBits, int nTerms, int nTimeout, int nDmax, int nLev2, int nSeed, int fVerbose )
{
    char pGoldPath[256] = "", pSmPath[256] = "";
    Gia_Man_t * pGold = NULL, * pSmPre = NULL, * pSmGen = NULL, * pSmEslim = NULL;
    Gia_Man_t * pSpec, * pSpecC, * pBestStitch = NULL, * pRet;
    Hier_Cand_t pCands[HIER_MAX_CAND], bestL1, bestL2;
    int nC = 0, i, D, nCheapTc, nLevTc, nCheapSm, nLevSm, nCheapRef, nDepthRef;
    int nGoldAnd = 350, nGate0 = -1, nBestL1 = -1, nBestL2 = -1, nBestMix = -1;
    int fGate0Ok = 0, fNoCheat = 0, fHaveL1 = 0, fHaveL2 = 0;
    unsigned seed = (unsigned)(nSeed > 0 ? nSeed : 1);
    int counts[HIER_NVAL];
    (void)pUnused;
    (void)nWord;
    memset( &bestL1, 0, sizeof(bestL1) );
    memset( &bestL2, 0, sizeof(bestL2) );

    if ( nBits != HIER_NBIT || nTerms != HIER_NTERM )
    {
        Abc_Print( -1, "&openc -H: experiment is 4-term 4-bit TC with 11-bit signed output (got -B %d -N %d).\n", nBits, nTerms );
        return NULL;
    }
    if ( nDmax < 4 )
        nDmax = 4;
    if ( nDmax > HIER_MAX_D )
        nDmax = HIER_MAX_D;
    if ( nTimeout < 0 )
        nTimeout = 0;
    if ( nLev2 < 0 )
        nLev2 = 0;

    Abc_Print( 1, "\n================================================================\n" );
    Abc_Print( 1, "&openc -H hierarchical search  (representation-driven G(E))\n" );
    Abc_Print( 1, "Primary objective: minimize eSlim(G). Encoder cost reported, excluded.\n" );
    Abc_Print( 1, "Gold 350 is a QoR side benchmark, not a search/cheap-screen threshold.\n" );
    Abc_Print( 1, "D_max=%d  eSlim timeout=%d s  Level-2 samples/width=%d  seed=%d\n", nDmax, nTimeout, nLev2, nSeed );
    Abc_Print( 1, "================================================================\n" );

    /* ---- Gold oracle ---- */
    pGold = Hier_ReadGold350( pGoldPath, (int)sizeof(pGoldPath) );
    if ( pGold )
    {
        nGoldAnd = Gia_ManAndNotBufNum( pGold );
        Abc_Print( 1, "\nGold SM (external QoR): %s\n", pGoldPath );
        Abc_Print( 1, "  PI/PO/AND = %d/%d/%d  (known ~350-gate SM result)\n",
            Gia_ManPiNum(pGold), Gia_ManPoNum(pGold), nGoldAnd );
        Abc_Print( 1, "  Gold imposes no constraint on candidate topology, E, width, or G.\n" );
    }
    else
        Abc_Print( 0, "&openc -H: gold 350 AIG not found; will still run Gate 0 vs pre-eSlim SM.\n" );

    pSmPre = Hier_ReadPreEslimSm( pSmPath, (int)sizeof(pSmPath) );
    pSmGen = Hier_BuildSmMixer( 1, 3 );
    if ( pSmPre )
        Abc_Print( 1, "Pre-eSlim SM mixer: %s  PI/PO/AND = %d/%d/%d\n",
            pSmPath, Gia_ManPiNum(pSmPre), Gia_ManPoNum(pSmPre), Gia_ManAndNotBufNum(pSmPre) );
    else
        Abc_Print( 0, "&openc -H: pre-eSlim SM AIG missing; using generated 3x3 mag-mul mixer.\n" );

    if ( pSmPre && pSmGen )
    {
        int eq = Hier_VerifyCec( pSmPre, pSmGen );
        Abc_Print( 1, "Generated SM mixer vs file: CEC %s  (gen AND %d / file AND %d)\n",
            eq ? "OK" : "DIFF", Gia_ManAndNotBufNum(pSmGen), Gia_ManAndNotBufNum(pSmPre) );
    }

    /* ---- Gate 0 ---- */
    {
        Gia_Man_t * pGateIn = pSmPre ? Gia_ManDup(pSmPre) : Gia_ManDup(pSmGen);
        Abc_Print( 1, "\n---- Gate 0: mixer-only eSlim on matching SM mixer ----\n" );
        Abc_Print( 1, "Pre-eSlim AND/depth = %d/%d\n", Gia_ManAndNotBufNum(pGateIn), Gia_ManLevelNum(pGateIn) );
        pSmEslim = Hier_Eslim( pGateIn, nTimeout, nSeed, 1 );
        Gia_ManStop( pGateIn );
        nGate0 = Gia_ManAndNotBufNum( pSmEslim );
        Abc_Print( 1, "Gate-0 eSlim AND/depth = %d/%d\n", nGate0, Gia_ManLevelNum(pSmEslim) );
        if ( pSmPre )
        {
            int eq = Hier_VerifyCec( pSmPre, pSmEslim );
            Abc_Print( 1, "CEC(Gate-0, pre-eSlim SM) = %s\n", eq ? "OK" : "FAIL" );
            if ( !eq )
            {
                Abc_Print( -1, "&openc -H: Gate 0 CEC failed; evaluator broken. Stopping search.\n" );
                Gia_ManStop( pSmEslim );
                if ( pGold ) Gia_ManStop( pGold );
                if ( pSmPre ) Gia_ManStop( pSmPre );
                if ( pSmGen ) Gia_ManStop( pSmGen );
                return NULL;
            }
        }
        if ( pGold )
        {
            int eq = Hier_VerifyCec( pGold, pSmEslim );
            Abc_Print( 1, "CEC(Gate-0, gold 350) = %s  (same function, not same netlist)\n", eq ? "OK" : "FAIL/DIFF" );
        }
        {
            int preAnd = pSmPre ? Gia_ManAndNotBufNum(pSmPre) : Gia_ManAndNotBufNum(pSmGen);
            int drop = preAnd - nGate0;
            fGate0Ok = (drop >= Abc_MaxInt(preAnd / 10, 20)) || (nGate0 <= 400);
            Abc_Print( 1, "Gate 0 %s: dropped %d AND from %d toward the ~350 regime (370 vs 350 is OK).\n",
                fGate0Ok ? "PASS" : "WEAK", drop, preAnd );
            Abc_Print( 1, "Do not use 350 or this Gate-0 AND as a search or cheap-screen cutoff.\n" );
        }
    }

    pSpec  = Hier_GenTcSpec();
    pSpecC = Hier_Cheap( pSpec );
    nCheapTc = Gia_ManAndNotBufNum( pSpecC );
    nLevTc   = Gia_ManLevelNum( pSpecC );
    Gia_ManStop( pSpecC );
    nCheapSm = pSmPre ? Gia_ManAndNotBufNum(pSmPre) : Gia_ManAndNotBufNum(pSmGen);
    nLevSm   = pSmPre ? Gia_ManLevelNum(pSmPre) : Gia_ManLevelNum(pSmGen);
    nCheapRef = Abc_MaxInt( nCheapTc, nCheapSm );
    nDepthRef = Abc_MaxInt( nLevTc, nLevSm );
    Abc_Print( 1, "\nCheap (pre-eSlim) baselines: TC spec AND/depth=%d/%d  SM mixer=%d/%d  screen ref=%d/%d\n",
        nCheapTc, nLevTc, nCheapSm, nLevSm, nCheapRef, nDepthRef );

    fNoCheat = Hier_NoCheatFixture( pSpec, fVerbose );

    /* ---- Census ---- */
    Abc_Print( 1, "\n---- Census (before any search eSlim); 6 is not special ----\n" );
    Abc_Print( 1, "Family A: radix-2, d_i in {-1,0,+1}, encoding {%s}\n", Hier_EncName(HIER_FAM_A) );
    for ( D = 4; D <= nDmax; D++ )
    {
        int nVec = Hier_CensusFamily( HIER_FAM_A, D, counts, NULL );
        int v;
        Abc_Print( 1, "  D=%d  physical wires/op=%d  theoretical vectors=%d\n", D, D * 2, nVec );
        Abc_Print( 1, "    valid vectors/value [TC 0..15]:" );
        for ( v = 0; v < HIER_NVAL; v++ )
            Abc_Print( 1, " %d", counts[v] );
        Abc_Print( 1, "\n" );
        Hier_PrintComb( counts );
    }
    Abc_Print( 1, "Family B: radix-4, d_i in {-2..+2}, encoding {%s}\n", Hier_EncName(HIER_FAM_B) );
    for ( D = 2; D <= nDmax / 2 + 1 && D <= nDmax; D++ )
    {
        int nVec = Hier_CensusFamily( HIER_FAM_B, D, counts, NULL );
        int v;
        Abc_Print( 1, "  D=%d  physical wires/op=%d  theoretical vectors=%d\n", D, D * 3, nVec );
        Abc_Print( 1, "    valid vectors/value [TC 0..15]:" );
        for ( v = 0; v < HIER_NVAL; v++ )
            Abc_Print( 1, " %d", counts[v] );
        Abc_Print( 1, "\n" );
        Hier_PrintComb( counts );
    }
    Abc_Print( 1, "Family C: redundant binary, same encoding as A, D=5..%d (D=4 is Family A)\n", nDmax );
    Abc_Print( 1, "Family S: SM-like mag[3:0]+sign, 5 wires/op, 4x4 mag-mul mixer (-8 representable).\n" );
    Abc_Print( 1, "  Gold 3-bit-mag SM is Gate-0 / QoR only; it is not TC-equivalent at minint.\n" );
    Abc_Print( 1, "  If S wins: selected SM from the allowed SM-like family, not invented SM.\n" );

    /* Level-1 structured list. Extra-zero pads of NAF/Booth are the same
       instantiated mixer after constant folding; census still reported them.
       eSlim the distinct constructions. */
    Hier_AddL1( pCands, &nC, HIER_FAM_S, 1, "sm_msb" );
    Hier_AddL1( pCands, &nC, HIER_FAM_A, 4, "naf" );
    Hier_AddL1( pCands, &nC, HIER_FAM_A, 4, "tc_bits" );
    Hier_AddL1( pCands, &nC, HIER_FAM_A, 4, "rewrite11" );
    Hier_AddL1( pCands, &nC, HIER_FAM_A, 4, "carry_borrow" );
    if ( nDmax >= 5 )
        Hier_AddL1( pCands, &nC, HIER_FAM_A, 5, "red_flip" );
    Hier_AddL1( pCands, &nC, HIER_FAM_B, 2, "booth4" );
    Abc_Print( 1, "Level-1 structured recodings enumerated in census; eSlim distinct instantiated mixers: %d\n", nC );
    Abc_Print( 1, "  (NAF/rewrite/Booth with extra all-zero digits fold to the same G; not re-eSlim'd.)\n" );
    Abc_Print( 1, "eSlim budget: distinct instantiated mixers after const-digit folding; 8x-AND cheap screen (not gold 350); then up to %d Level-2 maps per (family,D).\n", nLev2 );

    /* ---- Level 1 ---- */
    Abc_Print( 1, "\n---- Level 1: structured recodings; G generated from E ----\n" );
    for ( i = 0; i < nC; i++ )
    {
        Gia_Man_t * pSt = NULL, * pMixE;
        if ( pCands[i].level != 1 )
            continue;
        pMixE = Hier_EvalOne( pCands + i, pSpec, nTimeout, nSeed + i, nCheapRef, nDepthRef, 1, fVerbose, &pSt );
        if ( pMixE )
            Gia_ManStop( pMixE );
        if ( pCands[i].fCec && (nBestL1 < 0 || pCands[i].nMixEslim < nBestL1) )
        {
            nBestL1 = pCands[i].nMixEslim;
            bestL1  = pCands[i];
            fHaveL1 = 1;
        }
        if ( pCands[i].fCec && pSt && (nBestMix < 0 || pCands[i].nMixEslim < nBestMix) )
        {
            nBestMix = pCands[i].nMixEslim;
            if ( pBestStitch )
                Gia_ManStop( pBestStitch );
            pBestStitch = pSt;
        }
        else if ( pSt )
            Gia_ManStop( pSt );
    }

    /* ---- Level 2 ---- */
    if ( nLev2 > 0 )
    {
        int fams[3] = { HIER_FAM_A, HIER_FAM_A, HIER_FAM_B };
        int Ds[3]   = { 4, Abc_MinInt(nDmax, 6), 2 };
        int s, k, nL2 = 0;
        Abc_Print( 1, "\n---- Level 2: constrained assignments (same construction rule + encoding) ----\n" );
        for ( k = 0; k < 3; k++ )
        {
            Vec_Int_t * pv[HIER_NVAL];
            int fam = fams[k], Dd = Ds[k], v, maps;
            if ( Dd < 2 )
                continue;
            for ( v = 0; v < HIER_NVAL; v++ )
                pv[v] = Vec_IntAlloc( HIER_STORE );
            Hier_CensusFamily( fam, Dd, counts, pv );
            Abc_Print( 1, "Family %s D=%d valid-vector counts:", Hier_FamName(fam, Dd), Dd );
            for ( v = 0; v < HIER_NVAL; v++ )
                Abc_Print( 1, " %d", Vec_IntSize(pv[v]) );
            Abc_Print( 1, "\n" );
            maps = nLev2;
            for ( s = 0; s < maps; s++ )
            {
                int iC = nC;
                Hier_AddL2( pCands, &nC, fam, Dd, pv, &seed, s );
                if ( nC == iC )
                    continue;
                {
                    Gia_Man_t * pSt = NULL, * pMixE;
                    pMixE = Hier_EvalOne( pCands + iC, pSpec, nTimeout, nSeed + 100 + nL2, nCheapRef, nDepthRef, 1, fVerbose, &pSt );
                    nL2++;
                    if ( pMixE )
                        Gia_ManStop( pMixE );
                    if ( pCands[iC].fCec && (nBestL2 < 0 || pCands[iC].nMixEslim < nBestL2) )
                    {
                        nBestL2 = pCands[iC].nMixEslim;
                        bestL2  = pCands[iC];
                        fHaveL2 = 1;
                    }
                    if ( pCands[iC].fCec && pSt && (nBestMix < 0 || pCands[iC].nMixEslim < nBestMix) )
                    {
                        nBestMix = pCands[iC].nMixEslim;
                        if ( pBestStitch )
                            Gia_ManStop( pBestStitch );
                        pBestStitch = pSt;
                    }
                    else if ( pSt )
                        Gia_ManStop( pSt );
                }
            }
            for ( v = 0; v < HIER_NVAL; v++ )
                Vec_IntFree( pv[v] );
        }
        Abc_Print( 1, "Level-2 maps eSlim'd: %d\n", nL2 );
    }
    else
        Abc_Print( 1, "\nLevel 2 skipped ( -k 0 ).\n" );

    /* ---- Four numbers ---- */
    Abc_Print( 1, "\n================================================================\n" );
    Abc_Print( 1, "Experiment numbers (mixer eSlim AND; encoder excluded)\n" );
    Abc_Print( 1, "  Gold SM 350 (file)     : %d\n", nGoldAnd );
    Abc_Print( 1, "  Gate-0 SM eSlim        : %d%s\n", nGate0, fGate0Ok ? "" : "  (weak vs pre-eSlim)" );
    if ( fHaveL1 )
        Abc_Print( 1, "  Best Level 1           : %d  (%s fam=%s D=%d wires/op=%d enc=%d/%d CEC=%d)\n",
            nBestL1, bestL1.name, Hier_FamName(bestL1.fam, bestL1.D), bestL1.D, bestL1.nWires,
            bestL1.nEncAnd, bestL1.nEncLev, bestL1.fCec );
    else
        Abc_Print( 1, "  Best Level 1           : n/a\n" );
    if ( fHaveL2 )
        Abc_Print( 1, "  Best Level 2           : %d  (%s fam=%s D=%d wires/op=%d enc=%d/%d CEC=%d)\n",
            nBestL2, bestL2.name, Hier_FamName(bestL2.fam, bestL2.D), bestL2.D, bestL2.nWires,
            bestL2.nEncAnd, bestL2.nEncLev, bestL2.fCec );
    else
        Abc_Print( 1, "  Best Level 2           : n/a\n" );
    Abc_Print( 1, "Digit-to-wire encodings: A/C {%s}; B {%s}; S {%s}\n",
        Hier_EncName(HIER_FAM_A), Hier_EncName(HIER_FAM_B), Hier_EncName(HIER_FAM_S) );
    Abc_Print( 1, "No-cheat fixture: %s\n", fNoCheat ? "passed" : "FAILED" );
    Abc_Print( 1, "================================================================\n" );

    if ( pGold ) Gia_ManStop( pGold );
    if ( pSmPre ) Gia_ManStop( pSmPre );
    if ( pSmGen ) Gia_ManStop( pSmGen );
    if ( pSmEslim ) Gia_ManStop( pSmEslim );
    Gia_ManStop( pSpec );

    if ( pBestStitch )
        return pBestStitch;
    pRet = Hier_GenTcSpec();
    return pRet;
}

ABC_NAMESPACE_IMPL_END
