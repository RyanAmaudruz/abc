/**CFile****************************************************************

  FileName    [giaOpenc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Operand-local encoder discovery with a free encoder / cost mixer.]

  Description [Two distinct modes share the encoder/mixer split:

               1. Forced-bound-set Ashenhurst-Curtis (default). Bound
                  sets may be consecutive PI groups or arithmetic-role
                  partitions. Column equivalence merges operand
                  assignments that induce the same residual. Encoder
                  nodes are free; the mixer is G of the class codes.

               2. Bijective representation search (&openc -e perm).
                  Operand values stay distinguishable; the optimization
                  variable is the assignment of binary codes to those
                  values. Encoder cost is reported but excluded from
                  the objective.

                  Default mixer: Shannon of the encoded truth table
                  (existence proof that the code assignment matters).

                  -A mixer: inverse-E + structural F, then the same
                  &dc2+&syn2 flow for every encoding. An SM-friendly
                  multiplier is a labeled reference, not a search seed.

                  -T mixer: joint search over a small arithmetic template
                  library (TC array, unsigned, radix-4 Booth, SM mag-mul,
                  SM+Booth). Each template already accumulates per-term
                  products (MAC / signed dot product). Encoding E is
                  recovered from F via the multiplicative identity on
                  one term with the others at 0; known encodings are
                  not seeds. Shared E is copied to every operand; a
                  first-pair-only diagnostic tests whether that E must
                  be reused.]

  Author      [Cursor Grok]

  Date        [Ver. 1.0. Started - August 18, 2026.]

***********************************************************************/

#include "gia.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/cnf/cnf.h"
#include "sat/bsat/satSolver.h"
#include "proof/cec/cec.h"
#include <string.h>
#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#include "misc/st/st.h"
#undef b0
#undef b1
#endif

ABC_NAMESPACE_IMPL_START

extern Gia_Man_t * Gia_ManCompress2( Gia_Man_t * p, int fUpdateLevel, int fVerbose );

#define OPENC_MAX_PI     256
#define OPENC_MAX_BOUND  12
#define OPENC_MAX_OPS    128
#define OPENC_MAX_ENC    16
#define OPENC_TT_PI      16
#define OPENC_TT_MIX     16
#define OPENC_SAT_CONFS  ((ABC_INT64_T)1000000)
#define OPENC_PERM_BOUND 8
#define OPENC_PERM_SEARCH_PI 8
#define OPENC_PERM_TOPK  32
#define OPENC_TPL_TC       0
#define OPENC_TPL_UNS      1
#define OPENC_TPL_BOOTH    2
#define OPENC_TPL_BOOTHUNS 3
#define OPENC_TPL_SM       4
#define OPENC_TPL_SMBOOTH  5

typedef struct Openc_Op_t_ Openc_Op_t;
struct Openc_Op_t_
{
    int     lo;
    int     hi;
    int     nBound;
    int     pPis[OPENC_MAX_BOUND];
    char    pLabel[48];
    int     nClasses;
    int     nEnc;
    int     fIdentity;
    int *   pClass;
    int *   pRep;
    word ** pEncTt;
};

typedef struct Openc_Man_t_ Openc_Man_t;
struct Openc_Man_t_
{
    Gia_Man_t *   pGia;
    int           nVars;
    int           nOuts;
    int           nWords;
    int           nOps;
    int           nMixVars;
    int           fOneHot;
    int           nMaxEnc;
    int           fVerbose;
    int           fStruct;
    int           fSimSat;
    int           nSimWords;
    int           nSatCalls;
    int           nSatEq;
    int           nSatNeq;
    int           nSatUndef;
    int           fMixNeedSyn2;
    int           fClusterOnly;
    char *        pMixMethod;
    char          pPartName[32];
    word **       pOuts;
    Openc_Op_t    pOps[OPENC_MAX_OPS];
};

typedef struct Openc_Sat_t_ Openc_Sat_t;
struct Openc_Sat_t_
{
    Gia_Man_t *   pMit;
    sat_solver *  pSat;
    Cnf_Dat_t *   pCnf;
    int           iCiVarBeg;
    int           nBound;
    int           nCalls;
    int           nEq;
    int           nNeq;
    int           nUndef;
};

static inline int Openc_Log2Ceil( int n )
{
    int r = 0, v = 1;
    if ( n <= 1 )
        return 0;
    while ( v < n )
    {
        v <<= 1;
        r++;
    }
    return r;
}

static inline int Openc_PopcountInt( int x, int n )
{
    int i, c = 0;
    for ( i = 0; i < n; i++ )
        c += (x >> i) & 1;
    return c;
}

static int Openc_DupHashAnd( Gia_Man_t * pNew, Gia_Obj_t * pObj )
{
    if ( Gia_ObjIsBuf(pObj) )
        return Gia_ObjFanin0Copy(pObj);
    if ( Gia_ObjIsXor(pObj) )
        return Gia_ManHashXor( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    return Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

static int Openc_OpBoundIndex( Openc_Op_t * pOp, int iPi )
{
    int k;
    for ( k = 0; k < pOp->nBound; k++ )
        if ( pOp->pPis[k] == iPi )
            return k;
    return -1;
}

static int Openc_OpIsConsec( Openc_Op_t * pOp )
{
    int k;
    if ( pOp->nBound < 1 )
        return 0;
    for ( k = 1; k < pOp->nBound; k++ )
        if ( pOp->pPis[k] != pOp->pPis[0] + k )
            return 0;
    return 1;
}

static void Openc_FmtBound( Openc_Op_t * pOp, char * pBuf, int nBuf )
{
    int k, n;
    if ( pOp->pLabel[0] )
        n = snprintf( pBuf, nBuf, "%s ", pOp->pLabel );
    else
        n = 0;
    if ( n < 0 )
        n = 0;
    if ( n >= nBuf )
        return;
    if ( Openc_OpIsConsec(pOp) )
        snprintf( pBuf + n, nBuf - n, "PIs[%d:%d]", pOp->pPis[0], pOp->pPis[pOp->nBound - 1] );
    else
    {
        n += snprintf( pBuf + n, nBuf - n, "PIs{" );
        for ( k = 0; k < pOp->nBound && n < nBuf - 8; k++ )
            n += snprintf( pBuf + n, nBuf - n, "%s%d", k ? "," : "", pOp->pPis[k] );
        snprintf( pBuf + n, nBuf - n, "}" );
    }
}


////////////////////////////////////////////////////////////////////////
///                     TRUTH-TABLE HELPERS                          ///
////////////////////////////////////////////////////////////////////////

static word ** Openc_AllocTts( int nFuncs, int nWords )
{
    word ** p;
    int i;
    p = ABC_ALLOC( word *, nFuncs );
    for ( i = 0; i < nFuncs; i++ )
        p[i] = ABC_CALLOC( word, nWords );
    return p;
}

static void Openc_FreeTts( word ** p, int nFuncs )
{
    int i;
    if ( p == NULL )
        return;
    for ( i = 0; i < nFuncs; i++ )
        ABC_FREE( p[i] );
    ABC_FREE( p );
}

static int Openc_ExtractTruths( Gia_Man_t * p, word ** pOuts, int nOuts, int nWords )
{
    Gia_Obj_t * pObj;
    word * pTruth;
    int i;
    Gia_ManForEachPo( p, pObj, i )
    {
        if ( i >= nOuts )
            break;
        pTruth = Gia_ObjComputeTruthTable( p, pObj );
        if ( pTruth == NULL )
            return 0;
        Abc_TtCopy( pOuts[i], pTruth, nWords, 0 );
    }
    if ( p->vTtMemory )
        Gia_ObjComputeTruthTableStop( p );
    return 1;
}

static int Openc_TtToLitRec( Gia_Man_t * pGia, word * pTt, int nVars, int * pFanins )
{
    int nMints, nHalf, nWordsC, i, f0, f1, all0, all1;
    word * pC0, * pC1;
    nMints = 1 << nVars;
    all0 = all1 = 1;
    for ( i = 0; i < nMints; i++ )
    {
        if ( Abc_TtGetBit(pTt, i) )
            all0 = 0;
        else
            all1 = 0;
    }
    if ( all0 )
        return 0;
    if ( all1 )
        return 1;
    if ( nVars == 1 )
        return Abc_LitNotCond( pFanins[0], !Abc_TtGetBit(pTt, 1) );
    nHalf   = nMints >> 1;
    nWordsC = Abc_Truth6WordNum( nVars - 1 );
    pC0 = ABC_CALLOC( word, nWordsC );
    pC1 = ABC_CALLOC( word, nWordsC );
    for ( i = 0; i < nHalf; i++ )
    {
        if ( Abc_TtGetBit(pTt, i) )
            Abc_TtSetBit( pC0, i );
        if ( Abc_TtGetBit(pTt, i + nHalf) )
            Abc_TtSetBit( pC1, i );
    }
    f0 = Openc_TtToLitRec( pGia, pC0, nVars - 1, pFanins );
    f1 = Openc_TtToLitRec( pGia, pC1, nVars - 1, pFanins );
    ABC_FREE( pC0 );
    ABC_FREE( pC1 );
    if ( f0 == f1 )
        return f0;
    return Gia_ManHashMux( pGia, pFanins[nVars - 1], f1, f0 );
}

static int Openc_TtToLit( Gia_Man_t * pGia, word * pTruth, int nVars, Vec_Int_t * vCover, Vec_Int_t * vLeaves )
{
    (void)vCover;
    if ( nVars <= 0 )
        return Abc_TtGetBit( pTruth, 0 ) ? 1 : 0;
    assert( Vec_IntSize(vLeaves) >= nVars );
    return Openc_TtToLitRec( pGia, pTruth, nVars, Vec_IntArray(vLeaves) );
}

static Gia_Man_t * Openc_BuildFromTruths( int nVars, int nOuts, word ** pOuts, char * pName )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vCover, * vLeaves;
    int i, lit;
    pNew = Gia_ManStart( 1000 );
    pNew->pName = Abc_UtilStrsav( pName );
    for ( i = 0; i < nVars; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    vCover  = Vec_IntAlloc( 1 << 12 );
    vLeaves = Vec_IntAlloc( nVars );
    for ( i = 0; i < nVars; i++ )
        Vec_IntPush( vLeaves, Gia_Obj2Lit(pNew, Gia_ManPi(pNew, i)) );
    for ( i = 0; i < nOuts; i++ )
    {
        lit = Openc_TtToLit( pNew, pOuts[i], nVars, vCover, vLeaves );
        Gia_ManAppendCo( pNew, lit );
    }
    Gia_ManHashStop( pNew );
    Vec_IntFree( vCover );
    Vec_IntFree( vLeaves );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                     DEMO GENERATORS                              ///
////////////////////////////////////////////////////////////////////////

static int Openc_FullAdder( Gia_Man_t * p, int a, int b, int cin, int * pCout )
{
    int u = Gia_ManHashXor( p, a, b );
    int v = Gia_ManHashAnd( p, a, b );
    int s = Gia_ManHashXor( p, u, cin );
    int w = Gia_ManHashAnd( p, u, cin );
    *pCout = Gia_ManHashOr( p, v, w );
    return s;
}

static int Openc_AddVec( Gia_Man_t * p, int * pA, int nA, int * pB, int nB, int * pS )
{
    int i, c = 0, n = Abc_MaxInt( nA, nB );
    int pT[128];
    assert( n + 1 <= 128 );
    for ( i = 0; i < n; i++ )
    {
        int a = (i < nA) ? pA[i] : 0;
        int b = (i < nB) ? pB[i] : 0;
        pT[i] = Openc_FullAdder( p, a, b, c, &c );
    }
    if ( c )
        pT[n++] = c;
    for ( i = 0; i < n; i++ )
        pS[i] = pT[i];
    return n;
}

static int Openc_AddBit( Gia_Man_t * p, int * pSum, int nSum, int bit )
{
    int pOne[1];
    pOne[0] = bit;
    if ( nSum == 0 )
    {
        pSum[0] = bit;
        return 1;
    }
    return Openc_AddVec( p, pSum, nSum, pOne, 1, pSum );
}

static int Openc_Mul( Gia_Man_t * p, int * pA, int nA, int * pB, int nB, int * pP )
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
            nAcc = Openc_AddVec( p, pAcc, nAcc, pRow, nRow, pAcc );
    }
    for ( i = 0; i < nAcc; i++ )
        pP[i] = pAcc[i];
    return nAcc;
}

static void Openc_ZeroPadLits( int * pA, int nA, int nOut, int * pE )
{
    int i;
    assert( nOut <= 128 );
    for ( i = 0; i < nOut; i++ )
        pE[i] = (i < nA) ? pA[i] : 0;
}

static void Openc_ShlZ( int * pDst, int nDst, int * pSrc, int nSrc, int sh )
{
    int i;
    for ( i = 0; i < nDst; i++ )
        pDst[i] = (i >= sh && (i - sh) < nSrc) ? pSrc[i - sh] : 0;
}

static Gia_Man_t * Openc_GenMajxor( int nBits )
{
    word ** pOuts;
    Gia_Man_t * pNew;
    int nVars, nWords, nMints, m, a, b, ma, mb;
    if ( nBits < 1 || nBits > 6 )
    {
        Abc_Print( -1, "&openc: majxor operand width must be in 1..6.\n" );
        return NULL;
    }
    nVars  = 2 * nBits;
    nWords = Abc_Truth6WordNum( nVars );
    nMints = 1 << nVars;
    pOuts  = Openc_AllocTts( 1, nWords );
    for ( m = 0; m < nMints; m++ )
    {
        a  = m & ((1 << nBits) - 1);
        b  = (m >> nBits) & ((1 << nBits) - 1);
        ma = Openc_PopcountInt( a, nBits ) > nBits / 2;
        mb = Openc_PopcountInt( b, nBits ) > nBits / 2;
        if ( ma ^ mb )
            Abc_TtSetBit( pOuts[0], m );
    }
    pNew = Openc_BuildFromTruths( nVars, 1, pOuts, "majxor" );
    Openc_FreeTts( pOuts, 1 );
    return pNew;
}

static Gia_Man_t * Openc_GenPopaddTt( int nBits )
{
    word ** pOuts;
    Gia_Man_t * pNew;
    int nVars, nOuts, nWords, nMints, m, a, b, sum, o;
    nVars  = 2 * nBits;
    nOuts  = Openc_Log2Ceil( 2 * nBits + 1 );
    if ( nOuts < 1 )
        nOuts = 1;
    nWords = Abc_Truth6WordNum( nVars );
    nMints = 1 << nVars;
    pOuts  = Openc_AllocTts( nOuts, nWords );
    for ( m = 0; m < nMints; m++ )
    {
        a   = m & ((1 << nBits) - 1);
        b   = (m >> nBits) & ((1 << nBits) - 1);
        sum = Openc_PopcountInt( a, nBits ) + Openc_PopcountInt( b, nBits );
        for ( o = 0; o < nOuts; o++ )
            if ( (sum >> o) & 1 )
                Abc_TtSetBit( pOuts[o], m );
    }
    pNew = Openc_BuildFromTruths( nVars, nOuts, pOuts, "popadd" );
    Openc_FreeTts( pOuts, nOuts );
    return pNew;
}

static Gia_Man_t * Openc_GenPopaddAig( int nBits, int nTerms )
{
    Gia_Man_t * pNew;
    int nPi, i, nSum, nOuts, pSum[128];
    nPi = nBits * nTerms;
    if ( nPi < 1 || nPi > OPENC_MAX_PI )
    {
        Abc_Print( -1, "&openc: popadd would have %d PIs (limit %d).\n", nPi, OPENC_MAX_PI );
        return NULL;
    }
    pNew = Gia_ManStart( nPi * 16 + 64 );
    pNew->pName = Abc_UtilStrsav( "popadd" );
    for ( i = 0; i < nPi; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    nSum = 0;
    for ( i = 0; i < nPi; i++ )
        nSum = Openc_AddBit( pNew, pSum, nSum, Gia_Obj2Lit(pNew, Gia_ManPi(pNew, i)) );
    nOuts = Openc_Log2Ceil( nPi + 1 );
    if ( nOuts < 1 )
        nOuts = 1;
    for ( i = 0; i < nOuts; i++ )
        Gia_ManAppendCo( pNew, (i < nSum) ? pSum[i] : 0 );
    Gia_ManHashStop( pNew );
    return pNew;
}

static Gia_Man_t * Openc_GenPopadd( int nBits, int nTerms )
{
    if ( nBits < 1 || nBits > OPENC_MAX_BOUND )
    {
        Abc_Print( -1, "&openc: popadd operand width must be in 1..%d.\n", OPENC_MAX_BOUND );
        return NULL;
    }
    if ( nTerms < 1 )
        nTerms = 2;
    if ( nTerms == 2 && nBits <= 6 )
        return Openc_GenPopaddTt( nBits );
    return Openc_GenPopaddAig( nBits, nTerms );
}

static Gia_Man_t * Openc_GenDotprod( int nBits, int nTerms )
{
    Gia_Man_t * pNew;
    int nPi, t, i, nAcc, nProd, pAcc[128], pProd[128], pA[32], pB[32];
    if ( nBits < 1 || nBits > 8 )
    {
        Abc_Print( -1, "&openc: dotprod operand width must be in 1..8.\n" );
        return NULL;
    }
    if ( nTerms < 1 )
        nTerms = 2;
    nPi = 2 * nBits * nTerms;
    if ( nPi < 1 || nPi > OPENC_MAX_PI )
    {
        Abc_Print( -1, "&openc: dotprod would have %d PIs (limit %d).\n", nPi, OPENC_MAX_PI );
        return NULL;
    }
    pNew = Gia_ManStart( nPi * nBits * 8 + 256 );
    pNew->pName = Abc_UtilStrsav( "dotprod" );
    for ( i = 0; i < nPi; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    nAcc = 0;
    for ( t = 0; t < nTerms; t++ )
    {
        for ( i = 0; i < nBits; i++ )
        {
            pA[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t) * nBits + i) );
            pB[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t + 1) * nBits + i) );
        }
        nProd = Openc_Mul( pNew, pA, nBits, pB, nBits, pProd );
        if ( nAcc == 0 )
        {
            for ( i = 0; i < nProd; i++ )
                pAcc[i] = pProd[i];
            nAcc = nProd;
        }
        else
            nAcc = Openc_AddVec( pNew, pAcc, nAcc, pProd, nProd, pAcc );
    }
    for ( i = 0; i < nAcc; i++ )
        Gia_ManAppendCo( pNew, pAcc[i] );
    Gia_ManHashStop( pNew );
    return pNew;
}

static int Openc_SignExtLits( int * pA, int nA, int nOut, int * pE )
{
    int i, sign;
    assert( nA >= 1 && nOut >= nA && nOut <= 128 );
    sign = pA[nA - 1];
    for ( i = 0; i < nOut; i++ )
        pE[i] = (i < nA) ? pA[i] : sign;
    return nOut;
}

static int Openc_TcRangeWidth( int lo, int hi )
{
    int w;
    for ( w = 2; w <= 32; w++ )
    {
        int minv = -(1 << (w - 1));
        int maxv =  (1 << (w - 1)) - 1;
        if ( lo >= minv && hi <= maxv )
            return w;
    }
    return 32;
}

static Gia_Man_t * Openc_GenDotprodTc( int nBits, int nTerms )
{
    Gia_Man_t * pNew;
    int nPi, t, i, nAcc, nProd, nExt, nOuts, pmin, pmax, vmin, vmax;
    int pAcc[128], pProd[128], pA[32], pB[32], pAe[128], pBe[128], pPe[128];
    if ( nBits < 1 || nBits > 8 )
    {
        Abc_Print( -1, "&openc: mul_tc/dotprod_tc operand width must be in 1..8.\n" );
        return NULL;
    }
    if ( nTerms < 1 )
        nTerms = 2;
    nPi = 2 * nBits * nTerms;
    if ( nPi < 1 || nPi > OPENC_MAX_PI )
    {
        Abc_Print( -1, "&openc: dotprod_tc would have %d PIs (limit %d).\n", nPi, OPENC_MAX_PI );
        return NULL;
    }
    vmin = -(1 << (nBits - 1));
    vmax = (1 << (nBits - 1)) - 1;
    pmin = vmin * vmax;
    pmax = vmin * vmin;
    if ( vmax * vmax > pmax )
        pmax = vmax * vmax;
    nOuts = Openc_TcRangeWidth( nTerms * pmin, nTerms * pmax );
    nExt  = nOuts;
    pNew = Gia_ManStart( nPi * nBits * 16 + 256 );
    pNew->pName = Abc_UtilStrsav( nTerms == 1 ? "mul_tc" : "dotprod_tc" );
    for ( i = 0; i < nPi; i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    nAcc = 0;
    for ( t = 0; t < nTerms; t++ )
    {
        for ( i = 0; i < nBits; i++ )
        {
            pA[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t) * nBits + i) );
            pB[i] = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, (2 * t + 1) * nBits + i) );
        }
        Openc_SignExtLits( pA, nBits, nExt, pAe );
        Openc_SignExtLits( pB, nBits, nExt, pBe );
        nProd = Openc_Mul( pNew, pAe, nExt, pBe, nExt, pProd );
        for ( i = 0; i < nOuts; i++ )
            pPe[i] = (i < nProd) ? pProd[i] : 0;
        if ( nAcc == 0 )
        {
            for ( i = 0; i < nOuts; i++ )
                pAcc[i] = pPe[i];
            nAcc = nOuts;
        }
        else
            nAcc = Openc_AddVec( pNew, pAcc, nAcc, pPe, nOuts, pAcc );
    }
    for ( i = 0; i < nOuts; i++ )
        Gia_ManAppendCo( pNew, (i < nAcc) ? pAcc[i] : 0 );
    Gia_ManHashStop( pNew );
    return pNew;
}

Gia_Man_t * Gia_ManOpencGen( char * pType, int nBits, int nTerms )
{
    if ( pType == NULL )
        return NULL;
    if ( nTerms < 1 )
        nTerms = 2;
    if ( !strcmp(pType, "majxor") )
        return Openc_GenMajxor( nBits );
    if ( !strcmp(pType, "popadd") )
        return Openc_GenPopadd( nBits, nTerms );
    if ( !strcmp(pType, "dotprod") )
        return Openc_GenDotprod( nBits, nTerms );
    if ( !strcmp(pType, "mul_tc") )
        return Openc_GenDotprodTc( nBits, 1 );
    if ( !strcmp(pType, "dotprod_tc") )
        return Openc_GenDotprodTc( nBits, nTerms );
    Abc_Print( -1, "&openc: unknown generator \"%s\" (use majxor, popadd, dotprod, mul_tc, or dotprod_tc).\n", pType );
    return NULL;
}


////////////////////////////////////////////////////////////////////////
///                     BOUND-SET PARTITIONS                         ///
////////////////////////////////////////////////////////////////////////

static int Openc_PushOp( Openc_Man_t * p, int * pPis, int n, char * pLabel )
{
    Openc_Op_t * pOp;
    int k;
    if ( n < 1 )
        return 1;
    if ( p->nOps >= OPENC_MAX_OPS )
    {
        Abc_Print( -1, "&openc: too many bound sets (limit %d).\n", OPENC_MAX_OPS );
        return 0;
    }
    if ( n > OPENC_MAX_BOUND )
    {
        Abc_Print( -1, "&openc: bound set wider than %d bits.\n", OPENC_MAX_BOUND );
        return 0;
    }
    pOp = p->pOps + p->nOps;
    memset( pOp, 0, sizeof(Openc_Op_t) );
    pOp->nBound = n;
    pOp->lo = pPis[0];
    pOp->hi = pPis[n - 1] + 1;
    for ( k = 0; k < n; k++ )
        pOp->pPis[k] = pPis[k];
    if ( pLabel )
        strncpy( pOp->pLabel, pLabel, sizeof(pOp->pLabel) - 1 );
    p->nOps++;
    return 1;
}

static int Openc_CheckCover( Openc_Man_t * p )
{
    int used[OPENC_MAX_PI];
    int i, k, v;
    memset( used, 0, sizeof(used) );
    for ( i = 0; i < p->nOps; i++ )
        for ( k = 0; k < p->pOps[i].nBound; k++ )
        {
            v = p->pOps[i].pPis[k];
            if ( v < 0 || v >= p->nVars || used[v] )
            {
                Abc_Print( -1, "&openc: bound sets are not a partition of the PIs (PI %d).\n", v );
                return 0;
            }
            used[v] = 1;
        }
    for ( v = 0; v < p->nVars; v++ )
        if ( !used[v] )
        {
            Abc_Print( -1, "&openc: PI %d is not in any bound set.\n", v );
            return 0;
        }
    return 1;
}

static int Openc_FillConsec( Openc_Man_t * p, int nWord )
{
    int i, k, n, buf[OPENC_MAX_BOUND];
    char label[48];
    if ( nWord < 1 || nWord > p->nVars )
    {
        Abc_Print( -1, "&openc: operand width -W must be in 1..nPIs.\n" );
        return 0;
    }
    for ( i = 0; i < p->nVars; )
    {
        n = Abc_MinInt( nWord, p->nVars - i );
        for ( k = 0; k < n; k++ )
            buf[k] = i + k;
        sprintf( label, "op%d", p->nOps );
        if ( !Openc_PushOp( p, buf, n, label ) )
            return 0;
        i += n;
    }
    return 1;
}

static int Openc_MacA( int nBits, int t, int k ) { return (2 * t) * nBits + k; }
static int Openc_MacB( int nBits, int t, int k ) { return (2 * t + 1) * nBits + k; }

static int Openc_FillWeightDot( Openc_Man_t * p, int nBits, int nTerms )
{
    int k, t, buf[OPENC_MAX_BOUND];
    char label[48];
    if ( nTerms > OPENC_MAX_BOUND )
    {
        Abc_Print( -1, "&openc: -P weight bound width is N=%d (limit %d).\n", nTerms, OPENC_MAX_BOUND );
        return 0;
    }
    for ( k = 0; k < nBits; k++ )
    {
        for ( t = 0; t < nTerms; t++ )
            buf[t] = Openc_MacA( nBits, t, k );
        sprintf( label, "a[*][%d]", k );
        if ( !Openc_PushOp( p, buf, nTerms, label ) )
            return 0;
    }
    for ( k = 0; k < nBits; k++ )
    {
        for ( t = 0; t < nTerms; t++ )
            buf[t] = Openc_MacB( nBits, t, k );
        sprintf( label, "b[*][%d]", k );
        if ( !Openc_PushOp( p, buf, nTerms, label ) )
            return 0;
    }
    return 1;
}

static int Openc_FillWeightPop( Openc_Man_t * p, int nBits, int nTerms )
{
    int k, t, buf[OPENC_MAX_BOUND];
    char label[48];
    if ( nTerms > OPENC_MAX_BOUND )
    {
        Abc_Print( -1, "&openc: -P weight bound width is N=%d (limit %d).\n", nTerms, OPENC_MAX_BOUND );
        return 0;
    }
    for ( k = 0; k < nBits; k++ )
    {
        for ( t = 0; t < nTerms; t++ )
            buf[t] = t * nBits + k;
        sprintf( label, "x[*][%d]", k );
        if ( !Openc_PushOp( p, buf, nTerms, label ) )
            return 0;
    }
    return 1;
}

static int Openc_FillPair( Openc_Man_t * p, int nBits, int nTerms )
{
    int t, k, buf[2];
    char label[48];
    for ( t = 0; t < nTerms; t++ )
        for ( k = 0; k < nBits; k++ )
        {
            buf[0] = Openc_MacA( nBits, t, k );
            buf[1] = Openc_MacB( nBits, t, k );
            sprintf( label, "a%db%d[%d]", t, t, k );
            if ( !Openc_PushOp( p, buf, 2, label ) )
                return 0;
        }
    return 1;
}

static int Openc_FillSlice2( Openc_Man_t * p, int nBits, int nTerms, int fDot )
{
    int t, isB, k, n, i, nFactors, buf[OPENC_MAX_BOUND];
    char label[48];
    nFactors = fDot ? 2 * nTerms : nTerms;
    for ( t = 0; t < nFactors; t++ )
        for ( k = 0; k < nBits; )
        {
            n = Abc_MinInt( 2, nBits - k );
            for ( i = 0; i < n; i++ )
                buf[i] = t * nBits + k + i;
            isB = fDot ? (t & 1) : 0;
            if ( fDot )
                sprintf( label, "%c%d[%d:%d]", isB ? 'b' : 'a', t / 2, k + n - 1, k );
            else
                sprintf( label, "x%d[%d:%d]", t, k + n - 1, k );
            if ( !Openc_PushOp( p, buf, n, label ) )
                return 0;
            k += n;
        }
    return 1;
}

static int Openc_FillCross( Openc_Man_t * p, int nBits, int nTerms )
{
    int t, k, h, n, buf[OPENC_MAX_BOUND];
    char label[48];
    h = nBits / 2;
    if ( h < 1 || 2 * h != nBits )
    {
        Abc_Print( -1, "&openc: -P cross needs even operand width B.\n" );
        return 0;
    }
    n = 2 * h;
    if ( n > OPENC_MAX_BOUND )
    {
        Abc_Print( -1, "&openc: -P cross bound width is %d (limit %d).\n", n, OPENC_MAX_BOUND );
        return 0;
    }
    for ( t = 0; t < nTerms; t++ )
    {
        for ( k = 0; k < h; k++ )
        {
            buf[k]     = Openc_MacA( nBits, t, k );
            buf[h + k] = Openc_MacB( nBits, t, k );
        }
        sprintf( label, "t%d lo(a,b)", t );
        if ( !Openc_PushOp( p, buf, n, label ) )
            return 0;
        for ( k = 0; k < h; k++ )
        {
            buf[k]     = Openc_MacA( nBits, t, h + k );
            buf[h + k] = Openc_MacB( nBits, t, h + k );
        }
        sprintf( label, "t%d hi(a,b)", t );
        if ( !Openc_PushOp( p, buf, n, label ) )
            return 0;
    }
    return 1;
}

static int Openc_GuessDot( int nVars, int nBits, int nTerms )
{
    return nBits > 0 && nTerms > 0 && 2 * nBits * nTerms == nVars;
}

static int Openc_GuessPop( int nVars, int nBits, int nTerms )
{
    return nBits > 0 && nTerms > 0 && nBits * nTerms == nVars;
}

static int Openc_FillPartition( Openc_Man_t * p, char * pPart, int nWord, int nBits, int nTerms )
{
    int fDot, fPop;
    if ( pPart == NULL || pPart[0] == 0 || !strcmp(pPart, "consec") || !strcmp(pPart, "hier") )
    {
        if ( pPart && !strcmp(pPart, "hier") )
            strcpy( p->pPartName, "hier/slice2" );
        else
            strcpy( p->pPartName, "consec" );
        if ( pPart && !strcmp(pPart, "hier") )
        {
            fDot = Openc_GuessDot( p->nVars, nBits, nTerms );
            fPop = Openc_GuessPop( p->nVars, nBits, nTerms );
            if ( !fDot && !fPop )
            {
                Abc_Print( -1, "&openc: -P hier needs -B/-N matching a dotprod (2*B*N PIs) or popadd (B*N PIs).\n" );
                return 0;
            }
            return Openc_FillSlice2( p, nBits, nTerms, fDot ) && Openc_CheckCover( p );
        }
        return Openc_FillConsec( p, nWord ) && Openc_CheckCover( p );
    }
    fDot = Openc_GuessDot( p->nVars, nBits, nTerms );
    fPop = Openc_GuessPop( p->nVars, nBits, nTerms );
    strncpy( p->pPartName, pPart, sizeof(p->pPartName) - 1 );
    if ( !strcmp(pPart, "weight") )
    {
        if ( fDot )
            return Openc_FillWeightDot( p, nBits, nTerms ) && Openc_CheckCover( p );
        if ( fPop )
            return Openc_FillWeightPop( p, nBits, nTerms ) && Openc_CheckCover( p );
        Abc_Print( -1, "&openc: -P weight needs -B/-N matching a dotprod (2*B*N PIs) or popadd (B*N PIs); got i=%d B=%d N=%d.\n",
            p->nVars, nBits, nTerms );
        return 0;
    }
    if ( !strcmp(pPart, "pair") )
    {
        if ( !fDot )
        {
            Abc_Print( -1, "&openc: -P pair is (a_t[k], b_t[k]) and needs a dot-product layout (2*B*N PIs).\n" );
            return 0;
        }
        return Openc_FillPair( p, nBits, nTerms ) && Openc_CheckCover( p );
    }
    if ( !strcmp(pPart, "slice2") )
    {
        if ( !fDot && !fPop )
        {
            Abc_Print( -1, "&openc: -P slice2 needs -B/-N matching the PI layout.\n" );
            return 0;
        }
        return Openc_FillSlice2( p, nBits, nTerms, fDot ) && Openc_CheckCover( p );
    }
    if ( !strcmp(pPart, "cross") )
    {
        if ( !fDot )
        {
            Abc_Print( -1, "&openc: -P cross groups lo/hi halves of (a_t, b_t) and needs a dot-product layout.\n" );
            return 0;
        }
        return Openc_FillCross( p, nBits, nTerms ) && Openc_CheckCover( p );
    }
    Abc_Print( -1, "&openc: unknown partition \"%s\" (use consec, weight, pair, slice2, cross, hier).\n", pPart );
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                     COLUMN ENCODING                              ///
////////////////////////////////////////////////////////////////////////

static int Openc_FullMinterm( int b, int f, Openc_Op_t * pOp, int nVars )
{
    int m = 0, v, fi = 0, bk;
    for ( v = 0; v < nVars; v++ )
    {
        bk = Openc_OpBoundIndex( pOp, v );
        if ( bk >= 0 )
        {
            if ( (b >> bk) & 1 )
                m |= (1 << v);
        }
        else
        {
            if ( (f >> fi) & 1 )
                m |= (1 << v);
            fi++;
        }
    }
    return m;
}

static int Openc_ColumnsEqual( word * pA, word * pB, int nWords )
{
    int i;
    for ( i = 0; i < nWords; i++ )
        if ( pA[i] != pB[i] )
            return 0;
    return 1;
}

static void Openc_OpFree( Openc_Op_t * pOp )
{
    int i;
    ABC_FREE( pOp->pClass );
    ABC_FREE( pOp->pRep );
    if ( pOp->pEncTt )
    {
        for ( i = 0; i < pOp->nEnc; i++ )
            ABC_FREE( pOp->pEncTt[i] );
        ABC_FREE( pOp->pEncTt );
    }
}

static int Openc_AssignEncoderBits( Openc_Man_t * p, Openc_Op_t * pOp )
{
    int nMintsB, k, b, nEncBin;
    nMintsB = 1 << pOp->nBound;
    nEncBin = Openc_Log2Ceil( pOp->nClasses );
    pOp->fIdentity = 0;
    if ( p->fOneHot )
    {
        if ( pOp->nClasses <= p->nMaxEnc && pOp->nClasses > 0 )
            pOp->nEnc = pOp->nClasses;
        else if ( nEncBin <= p->nMaxEnc )
        {
            pOp->nEnc = nEncBin;
            if ( p->fVerbose )
            {
                char buf[96];
                Openc_FmtBound( pOp, buf, sizeof(buf) );
                Abc_Print( 1, "  operand %s one-hot too wide (%d); using binary.\n",
                    buf, pOp->nClasses );
            }
        }
        else
            pOp->fIdentity = 1;
    }
    else
    {
        if ( nEncBin <= p->nMaxEnc && pOp->nClasses < nMintsB )
            pOp->nEnc = nEncBin;
        else
            pOp->fIdentity = 1;
    }
    if ( pOp->fIdentity )
    {
        pOp->nEnc = pOp->nBound;
        pOp->pEncTt = ABC_ALLOC( word *, pOp->nEnc );
        for ( k = 0; k < pOp->nEnc; k++ )
        {
            pOp->pEncTt[k] = ABC_CALLOC( word, Abc_Truth6WordNum(pOp->nBound) );
            for ( b = 0; b < nMintsB; b++ )
                if ( (b >> k) & 1 )
                    Abc_TtSetBit( pOp->pEncTt[k], b );
        }
        return 1;
    }
    if ( pOp->nEnc == 0 )
        return 1;
    pOp->pEncTt = ABC_ALLOC( word *, pOp->nEnc );
    for ( k = 0; k < pOp->nEnc; k++ )
    {
        pOp->pEncTt[k] = ABC_CALLOC( word, Abc_Truth6WordNum(pOp->nBound) );
        for ( b = 0; b < nMintsB; b++ )
        {
            int code, bit;
            if ( p->fOneHot && pOp->nEnc == pOp->nClasses )
                bit = (pOp->pClass[b] == k);
            else
            {
                code = pOp->pClass[b];
                bit  = (code >> k) & 1;
            }
            if ( bit )
                Abc_TtSetBit( pOp->pEncTt[k], b );
        }
    }
    return 1;
}

static int Openc_ClusterColumnsTt( Openc_Man_t * p, Openc_Op_t * pOp )
{
    int nMintsB, nMintsF, nFree, nColWords, nColBits;
    int b, f, o, c;
    word * pCols;
    nFree     = p->nVars - pOp->nBound;
    nMintsB   = 1 << pOp->nBound;
    nMintsF   = 1 << nFree;
    nColBits  = p->nOuts * nMintsF;
    nColWords = (nColBits + 63) >> 6;
    if ( nColWords < 1 )
        nColWords = 1;
    pCols = ABC_CALLOC( word, (size_t)nMintsB * nColWords );
    for ( b = 0; b < nMintsB; b++ )
    {
        word * pCol = pCols + (size_t)b * nColWords;
        for ( f = 0; f < nMintsF; f++ )
        {
            int m = Openc_FullMinterm( b, f, pOp, p->nVars );
            for ( o = 0; o < p->nOuts; o++ )
                if ( Abc_TtGetBit(p->pOuts[o], m) )
                    Abc_TtSetBit( pCol, o * nMintsF + f );
        }
    }
    pOp->pClass = ABC_ALLOC( int, nMintsB );
    pOp->pRep   = ABC_ALLOC( int, nMintsB );
    pOp->nClasses = 0;
    for ( b = 0; b < nMintsB; b++ )
    {
        word * pCol = pCols + (size_t)b * nColWords;
        for ( c = 0; c < pOp->nClasses; c++ )
            if ( Openc_ColumnsEqual(pCol, pCols + (size_t)pOp->pRep[c] * nColWords, nColWords) )
            {
                pOp->pClass[b] = c;
                break;
            }
        if ( c == pOp->nClasses )
        {
            pOp->pClass[b] = pOp->nClasses;
            pOp->pRep[pOp->nClasses] = b;
            pOp->nClasses++;
        }
    }
    ABC_FREE( pCols );
    return 1;
}

static word Openc_HashWords( word * p, int n )
{
    word h = ABC_CONST(0xCBF29CE484222325);
    int i;
    for ( i = 0; i < n; i++ )
    {
        h ^= p[i];
        h *= ABC_CONST(0x00000100000001B3);
    }
    return h;
}

static void Openc_ClusterByHash( Openc_Op_t * pOp, word * pHash, int nMints )
{
    int b, c;
    pOp->pClass = ABC_ALLOC( int, nMints );
    pOp->pRep   = ABC_ALLOC( int, nMints );
    pOp->nClasses = 0;
    for ( b = 0; b < nMints; b++ )
    {
        for ( c = 0; c < pOp->nClasses; c++ )
            if ( pHash[b] == pHash[pOp->pRep[c]] )
            {
                pOp->pClass[b] = c;
                break;
            }
        if ( c == pOp->nClasses )
        {
            pOp->pClass[b] = pOp->nClasses;
            pOp->pRep[pOp->nClasses] = b;
            pOp->nClasses++;
        }
    }
}

static int Openc_SimClassNeedsSat( Openc_Op_t * pOp )
{
    int nMints = 1 << pOp->nBound;
    int * pCnt, b, need = 0;
    pCnt = ABC_CALLOC( int, pOp->nClasses );
    for ( b = 0; b < nMints; b++ )
        if ( ++pCnt[pOp->pClass[b]] > 1 )
            need = 1;
    ABC_FREE( pCnt );
    return need;
}

static Gia_Man_t * Openc_BuildColumnMiter( Gia_Man_t * p, Openc_Op_t * pOp )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, iFree, nBound, nPi, nPo, xorAcc;
    int * pPoA;
    nBound = pOp->nBound;
    nPi    = Gia_ManPiNum( p );
    nPo    = Gia_ManPoNum( p );
    pNew = Gia_ManStart( 2 * Gia_ManObjNum(p) + 64 );
    pNew->pName = Abc_UtilStrsav( "openc_colmit" );
    for ( i = 0; i < 2 * nBound + (nPi - nBound); i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    iFree = 0;
    Gia_ManForEachCi( p, pObj, i )
    {
        int bk = Openc_OpBoundIndex( pOp, i );
        if ( bk >= 0 )
            pObj->Value = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, bk) );
        else
        {
            pObj->Value = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, 2 * nBound + iFree) );
            iFree++;
        }
    }
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Openc_DupHashAnd( pNew, pObj );
    pPoA = ABC_ALLOC( int, nPo );
    Gia_ManForEachCo( p, pObj, i )
        pPoA[i] = Gia_ObjFanin0Copy( pObj );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    iFree = 0;
    Gia_ManForEachCi( p, pObj, i )
    {
        int bk = Openc_OpBoundIndex( pOp, i );
        if ( bk >= 0 )
            pObj->Value = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, nBound + bk) );
        else
        {
            pObj->Value = Gia_Obj2Lit( pNew, Gia_ManPi(pNew, 2 * nBound + iFree) );
            iFree++;
        }
    }
    Gia_ManForEachAnd( p, pObj, i )
        pObj->Value = Openc_DupHashAnd( pNew, pObj );
    xorAcc = 0;
    Gia_ManForEachCo( p, pObj, i )
        xorAcc = Gia_ManHashOr( pNew, xorAcc, Gia_ManHashXor(pNew, pPoA[i], Gia_ObjFanin0Copy(pObj)) );
    Gia_ManAppendCo( pNew, xorAcc );
    ABC_FREE( pPoA );
    Gia_ManHashStop( pNew );
    return pNew;
}

static void Openc_SatStop( Openc_Sat_t * p )
{
    if ( p->pSat )
        sat_solver_delete( p->pSat );
    Cnf_DataFree( p->pCnf );
    if ( p->pMit )
        Gia_ManStop( p->pMit );
    memset( p, 0, sizeof(Openc_Sat_t) );
}

static int Openc_SatStart( Openc_Sat_t * p, Gia_Man_t * pGia, Openc_Op_t * pOp )
{
    int nCi;
    memset( p, 0, sizeof(Openc_Sat_t) );
    p->nBound = pOp->nBound;
    p->pMit = Openc_BuildColumnMiter( pGia, pOp );
    if ( p->pMit == NULL )
        return 0;
    p->pCnf = (Cnf_Dat_t *)Mf_ManGenerateCnf( p->pMit, 8, 0, 1, 0, 0 );
    p->pMit->pData = NULL;
    if ( p->pCnf == NULL )
    {
        Openc_SatStop( p );
        return 0;
    }
    nCi = Gia_ManCiNum( p->pMit );
    p->iCiVarBeg = p->pCnf->nVars - nCi;
    if ( p->iCiVarBeg < 1 )
    {
        Openc_SatStop( p );
        return 0;
    }
    p->pSat = (sat_solver *)Cnf_DataWriteIntoSolver( p->pCnf, 1, 0 );
    if ( p->pSat == NULL )
    {
        Openc_SatStop( p );
        return 0;
    }
    return 1;
}

static int Openc_SatEqual( Openc_Sat_t * p, int b1, int b2 )
{
    Vec_Int_t * vLits;
    int k, status;
    if ( b1 == b2 )
        return 1;
    p->nCalls++;
    vLits = Vec_IntAlloc( 2 * p->nBound );
    for ( k = 0; k < p->nBound; k++ )
    {
        Vec_IntPush( vLits, Abc_Var2Lit( p->iCiVarBeg + k, !((b1 >> k) & 1) ) );
        Vec_IntPush( vLits, Abc_Var2Lit( p->iCiVarBeg + p->nBound + k, !((b2 >> k) & 1) ) );
    }
    status = sat_solver_solve( p->pSat, Vec_IntArray(vLits), Vec_IntLimit(vLits), OPENC_SAT_CONFS, 0, 0, 0 );
    Vec_IntFree( vLits );
    if ( status == l_False )
    {
        p->nEq++;
        return 1;
    }
    if ( status == l_True )
    {
        p->nNeq++;
        return 0;
    }
    p->nUndef++;
    return 0;
}

static void Openc_RefineClassesSat( Openc_Op_t * pOp, Openc_Sat_t * pSat )
{
    int nMints = 1 << pOp->nBound;
    int * pNewClass, * pNewRep, * pDone, * pMem, * pLocal;
    int b, m, r, nMem, nNew, nLocal;
    pNewClass = ABC_ALLOC( int, nMints );
    pNewRep   = ABC_ALLOC( int, nMints );
    pDone     = ABC_CALLOC( int, nMints );
    pMem      = ABC_ALLOC( int, nMints );
    pLocal    = ABC_ALLOC( int, nMints );
    nNew = 0;
    for ( b = 0; b < nMints; b++ )
    {
        if ( pDone[b] )
            continue;
        nMem = 0;
        for ( m = 0; m < nMints; m++ )
            if ( pOp->pClass[m] == pOp->pClass[b] )
                pMem[nMem++] = m;
        pNewClass[pMem[0]] = nNew;
        pNewRep[nNew] = pMem[0];
        pLocal[0] = nNew;
        nLocal = 1;
        nNew++;
        pDone[pMem[0]] = 1;
        for ( m = 1; m < nMem; m++ )
        {
            int found = 0;
            for ( r = 0; r < nLocal; r++ )
            {
                if ( Openc_SatEqual(pSat, pMem[m], pNewRep[pLocal[r]]) )
                {
                    pNewClass[pMem[m]] = pLocal[r];
                    found = 1;
                    break;
                }
            }
            if ( !found )
            {
                pNewClass[pMem[m]] = nNew;
                pNewRep[nNew] = pMem[m];
                pLocal[nLocal++] = nNew;
                nNew++;
            }
            pDone[pMem[m]] = 1;
        }
    }
    memcpy( pOp->pClass, pNewClass, sizeof(int) * nMints );
    memcpy( pOp->pRep, pNewRep, sizeof(int) * nNew );
    pOp->nClasses = nNew;
    ABC_FREE( pNewClass );
    ABC_FREE( pNewRep );
    ABC_FREE( pDone );
    ABC_FREE( pMem );
    ABC_FREE( pLocal );
}

static int Openc_ClusterColumnsSimSat( Openc_Man_t * p, Openc_Op_t * pOp )
{
    Gia_Man_t * pGia = p->pGia;
    int nMints, nCi, nSim, b, k, w;
    word * pHash;
    Vec_Wrd_t * vBase, * vPat, * vOut;
    Openc_Sat_t sat;
    nMints = 1 << pOp->nBound;
    nCi    = Gia_ManCiNum( pGia );
    nSim   = p->nSimWords;
    if ( nSim < 1 )
        nSim = 8;
    vBase = Vec_WrdStartRandom( nCi * nSim );
    pHash = ABC_ALLOC( word, nMints );
    for ( b = 0; b < nMints; b++ )
    {
        vPat = Vec_WrdDup( vBase );
        for ( k = 0; k < pOp->nBound; k++ )
        {
            word val = ((b >> k) & 1) ? ~(word)0 : 0;
            for ( w = 0; w < nSim; w++ )
                Vec_WrdWriteEntry( vPat, pOp->pPis[k] * nSim + w, val );
        }
        vOut = Gia_ManSimPatSimOut( pGia, vPat, 1 );
        pHash[b] = Openc_HashWords( Vec_WrdArray(vOut), Vec_WrdSize(vOut) );
        Vec_WrdFree( vOut );
        Vec_WrdFree( vPat );
    }
    Vec_WrdFree( vBase );
    Openc_ClusterByHash( pOp, pHash, nMints );
    ABC_FREE( pHash );
    if ( !Openc_SimClassNeedsSat(pOp) )
        return 1;
    memset( &sat, 0, sizeof(Openc_Sat_t) );
    if ( !Openc_SatStart(&sat, pGia, pOp) )
    {
        char buf[96];
        Openc_FmtBound( pOp, buf, sizeof(buf) );
        Abc_Print( 0, "&openc: SAT column miter failed for %s; trusting simulation classes.\n", buf );
        return 1;
    }
    Openc_RefineClassesSat( pOp, &sat );
    p->nSatCalls += sat.nCalls;
    p->nSatEq    += sat.nEq;
    p->nSatNeq   += sat.nNeq;
    p->nSatUndef += sat.nUndef;
    if ( p->fVerbose )
    {
        char buf[96];
        Openc_FmtBound( pOp, buf, sizeof(buf) );
        Abc_Print( 1, "  operand %s SAT: calls = %d  eq = %d  neq = %d  undef = %d\n",
            buf, sat.nCalls, sat.nEq, sat.nNeq, sat.nUndef );
    }
    Openc_SatStop( &sat );
    return 1;
}

static int Openc_EncodeOperand( Openc_Man_t * p, Openc_Op_t * pOp )
{
    if ( p->fSimSat )
    {
        if ( !Openc_ClusterColumnsSimSat(p, pOp) )
            return 0;
    }
    else
    {
        if ( !Openc_ClusterColumnsTt(p, pOp) )
            return 0;
    }
    return Openc_AssignEncoderBits( p, pOp );
}


////////////////////////////////////////////////////////////////////////
///                     NETWORK BUILDING                             ///
////////////////////////////////////////////////////////////////////////

static int Openc_VerifyCec( Gia_Man_t * pOrig, Gia_Man_t * pNew );

static Gia_Man_t * Openc_BuildEncoder( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pEnc;
    Vec_Int_t * vCover, * vLeaves;
    int i, k, lit;
    pEnc = Gia_ManStart( Gia_ManObjNum(pOrig) + 256 );
    pEnc->pName = Abc_UtilStrsav( pOrig->pName );
    for ( i = 0; i < p->nVars; i++ )
        Gia_ManAppendCi( pEnc );
    Gia_ManHashStart( pEnc );
    vCover = Vec_IntAlloc( 1 << 12 );
    for ( i = 0; i < p->nOps; i++ )
    {
        Openc_Op_t * pOp = p->pOps + i;
        vLeaves = Vec_IntAlloc( pOp->nBound );
        for ( k = 0; k < pOp->nBound; k++ )
            Vec_IntPush( vLeaves, Gia_Obj2Lit(pEnc, Gia_ManPi(pEnc, pOp->pPis[k])) );
        for ( k = 0; k < pOp->nEnc; k++ )
        {
            lit = Openc_TtToLit( pEnc, pOp->pEncTt[k], pOp->nBound, vCover, vLeaves );
            Gia_ManAppendCo( pEnc, lit );
        }
        Vec_IntFree( vLeaves );
    }
    Gia_ManHashStop( pEnc );
    Vec_IntFree( vCover );
    return pEnc;
}

static int Openc_AllIdentity( Openc_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nOps; i++ )
        if ( !p->pOps[i].fIdentity )
            return 0;
    return p->nOps > 0;
}

static int Openc_CodeToRep( Openc_Man_t * p, Openc_Op_t * pOp, int code )
{
    int c;
    if ( pOp->fIdentity )
        return code;
    if ( pOp->nEnc <= 0 )
        return pOp->pRep[0];
    if ( p->fOneHot && pOp->nEnc == pOp->nClasses )
    {
        if ( code <= 0 || (code & (code - 1)) )
            return -1;
        c = 0;
        while ( (code & 1) == 0 )
        {
            code >>= 1;
            c++;
        }
        return pOp->pRep[c];
    }
    if ( code < 0 || code >= pOp->nClasses )
        return -1;
    return pOp->pRep[code];
}

static int Openc_CodesToPiBits( Openc_Man_t * p, int mx, int * pPiBits )
{
    int i, k, shift = 0;
    for ( i = 0; i < p->nVars; i++ )
        pPiBits[i] = 0;
    for ( i = 0; i < p->nOps; i++ )
    {
        Openc_Op_t * pOp = p->pOps + i;
        int code, rep, mask;
        if ( pOp->nEnc <= 0 )
            rep = pOp->pRep[0];
        else
        {
            mask = (1 << pOp->nEnc) - 1;
            code = (mx >> shift) & mask;
            shift += pOp->nEnc;
            rep = Openc_CodeToRep( p, pOp, code );
            if ( rep < 0 )
                return 0;
        }
        for ( k = 0; k < pOp->nBound; k++ )
            pPiBits[pOp->pPis[k]] = (rep >> k) & 1;
    }
    return 1;
}

static int Openc_RepBitLit( Gia_Man_t * pMix, Openc_Man_t * p, Openc_Op_t * pOp, int bit, int * pCode )
{
    word * pTt;
    int c, nWords, lit;
    if ( pOp->fIdentity )
        return pCode[bit];
    if ( pOp->nEnc <= 0 )
        return (pOp->pRep[0] >> bit) & 1;
    nWords = Abc_Truth6WordNum( pOp->nEnc );
    pTt = ABC_CALLOC( word, nWords );
    for ( c = 0; c < pOp->nClasses; c++ )
    {
        if ( !((pOp->pRep[c] >> bit) & 1) )
            continue;
        if ( p->fOneHot && pOp->nEnc == pOp->nClasses )
            Abc_TtSetBit( pTt, 1 << c );
        else
            Abc_TtSetBit( pTt, c );
    }
    lit = Openc_TtToLitRec( pMix, pTt, pOp->nEnc, pCode );
    ABC_FREE( pTt );
    return lit;
}

static Gia_Man_t * Openc_BuildSpecFromF( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pSpec;
    Gia_Obj_t * pObj;
    int i, k, shift, * pPiLits, * pCode;
    pSpec = Gia_ManStart( Gia_ManObjNum(pOrig) + 1024 );
    pSpec->pName = Abc_UtilStrsav( "g_spec" );
    for ( i = 0; i < p->nMixVars; i++ )
        Gia_ManAppendCi( pSpec );
    if ( p->nMixVars == 0 )
        Gia_ManAppendCi( pSpec );
    Gia_ManHashStart( pSpec );
    pPiLits = ABC_ALLOC( int, p->nVars );
    shift = 0;
    for ( i = 0; i < p->nOps; i++ )
    {
        Openc_Op_t * pOp = p->pOps + i;
        pCode = ABC_ALLOC( int, Abc_MaxInt(pOp->nEnc, 1) );
        for ( k = 0; k < pOp->nEnc; k++ )
            pCode[k] = Gia_Obj2Lit( pSpec, Gia_ManPi(pSpec, shift + k) );
        for ( k = 0; k < pOp->nBound; k++ )
            pPiLits[pOp->pPis[k]] = Openc_RepBitLit( pSpec, p, pOp, k, pCode );
        ABC_FREE( pCode );
        shift += pOp->nEnc;
    }
    Gia_ManFillValue( pOrig );
    Gia_ManConst0(pOrig)->Value = 0;
    Gia_ManForEachCi( pOrig, pObj, i )
        pObj->Value = pPiLits[i];
    Gia_ManForEachAnd( pOrig, pObj, i )
        pObj->Value = Openc_DupHashAnd( pSpec, pObj );
    Gia_ManForEachCo( pOrig, pObj, i )
        Gia_ManAppendCo( pSpec, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pSpec );
    ABC_FREE( pPiLits );
    return pSpec;
}

static Gia_Man_t * Openc_GiaFromTts( int nVars, int nOuts, word ** pOuts, char * pName )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vCover, * vLeaves;
    int i, lit;
    pNew = Gia_ManStart( 256 );
    pNew->pName = Abc_UtilStrsav( pName );
    for ( i = 0; i < Abc_MaxInt(nVars, 1); i++ )
        Gia_ManAppendCi( pNew );
    Gia_ManHashStart( pNew );
    vCover  = Vec_IntAlloc( 1 << 12 );
    vLeaves = Vec_IntAlloc( Abc_MaxInt(nVars, 1) );
    for ( i = 0; i < Abc_MaxInt(nVars, 1); i++ )
        Vec_IntPush( vLeaves, Gia_Obj2Lit(pNew, Gia_ManPi(pNew, i)) );
    for ( i = 0; i < nOuts; i++ )
    {
        lit = Openc_TtToLit( pNew, pOuts[i], nVars, vCover, vLeaves );
        Gia_ManAppendCo( pNew, lit );
    }
    Gia_ManHashStop( pNew );
    Vec_IntFree( vCover );
    Vec_IntFree( vLeaves );
    return pNew;
}

static Gia_Man_t * Openc_SynthGTt( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pMix;
    Vec_Wrd_t * vSimsPi, * vSimsCo;
    int * pPiBits;
    word ** pG;
    int nMints, nWordsG, nCi, mx, i, o;
    nCi     = Gia_ManCiNum( pOrig );
    nMints  = (p->nMixVars > 0) ? (1 << p->nMixVars) : 1;
    nWordsG = Abc_Truth6WordNum( Abc_MaxInt(p->nMixVars, 1) );
    pPiBits = ABC_ALLOC( int, p->nVars );
    vSimsPi = Vec_WrdStart( nCi * nWordsG );
    for ( mx = 0; mx < nMints; mx++ )
    {
        if ( !Openc_CodesToPiBits(p, mx, pPiBits) )
            continue;
        for ( i = 0; i < nCi; i++ )
            if ( pPiBits[i] )
                Abc_TtSetBit( Vec_WrdEntryP(vSimsPi, i * nWordsG), mx );
    }
    ABC_FREE( pPiBits );
    vSimsCo = Gia_ManSimPatSimOut( pOrig, vSimsPi, 1 );
    Vec_WrdFree( vSimsPi );
    pG = ABC_ALLOC( word *, p->nOuts );
    for ( o = 0; o < p->nOuts; o++ )
        pG[o] = Vec_WrdEntryP( vSimsCo, o * nWordsG );
    pMix = Openc_GiaFromTts( p->nMixVars, p->nOuts, pG, "mixer" );
    ABC_FREE( pG );
    Vec_WrdFree( vSimsCo );
    p->pMixMethod = "direct G (truth table)";
    return pMix;
}

#ifdef ABC_USE_CUDD
static int Openc_BddToLit( DdManager * dd, DdNode * bFunc, Gia_Man_t * pNew, st__table * t )
{
    DdNode * bReg = Cudd_Regular( bFunc );
    int fComp = (int)(bReg != bFunc);
    char * pVal;
    int iLitR, iLitT, iLitE, iVar;
    if ( Cudd_IsConstant(bReg) )
        return fComp ? 0 : 1;
    if ( st__lookup( t, (char *)bReg, &pVal ) )
        return Abc_LitNotCond( Abc_Ptr2Int(pVal) - 1, fComp );
    iVar  = Cudd_NodeReadIndex( bReg );
    iLitT = Openc_BddToLit( dd, Cudd_T(bReg), pNew, t );
    iLitE = Openc_BddToLit( dd, Cudd_E(bReg), pNew, t );
    iLitR = Gia_ManHashMux( pNew, Gia_Obj2Lit(pNew, Gia_ManPi(pNew, iVar)), iLitT, iLitE );
    st__insert( t, (char *)bReg, (char *)Abc_Int2Ptr(iLitR + 1) );
    return Abc_LitNotCond( iLitR, fComp );
}

static Gia_Man_t * Openc_SynthGBdd( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pSpec, * pMix;
    DdManager * dd;
    Vec_Ptr_t * vFuncs;
    Gia_Obj_t * pObj;
    DdNode * bFunc0, * bFunc1, * bFunc;
    st__table * t;
    int i, Id, nCi;
    pSpec = Openc_BuildSpecFromF( p, pOrig );
    nCi = Gia_ManCiNum( pSpec );
    dd = Cudd_Init( nCi, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Gia_ManCreateRefs( pSpec );
    vFuncs = Vec_PtrStart( Gia_ManObjNum(pSpec) );
    if ( Gia_ObjRefNumId(pSpec, 0) > 0 )
    {
        Vec_PtrWriteEntry( vFuncs, 0, Cudd_ReadLogicZero(dd) );
        Cudd_Ref( Cudd_ReadLogicZero(dd) );
    }
    Gia_ManForEachCiId( pSpec, Id, i )
        if ( Gia_ObjRefNumId(pSpec, Id) > 0 )
        {
            Vec_PtrWriteEntry( vFuncs, Id, Cudd_bddIthVar(dd, i) );
            Cudd_Ref( Cudd_bddIthVar(dd, i) );
        }
    Gia_ManForEachAnd( pSpec, pObj, i )
    {
        bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Gia_ObjFaninId0(pObj, i)), Gia_ObjFaninC0(pObj) );
        bFunc1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Gia_ObjFaninId1(pObj, i)), Gia_ObjFaninC1(pObj) );
        if ( Gia_ObjIsBuf(pObj) )
            bFunc = bFunc0;
        else if ( Gia_ObjIsXor(pObj) )
            bFunc = Cudd_bddXor( dd, bFunc0, bFunc1 );
        else
            bFunc = Cudd_bddAnd( dd, bFunc0, bFunc1 );
        if ( bFunc == NULL )
        {
            Vec_PtrFree( vFuncs );
            Extra_StopManager( dd );
            Gia_ManStop( pSpec );
            return NULL;
        }
        Cudd_Ref( bFunc );
        Vec_PtrWriteEntry( vFuncs, i, bFunc );
    }
    pMix = Gia_ManStart( Gia_ManObjNum(pSpec) );
    pMix->pName = Abc_UtilStrsav( "mixer" );
    for ( i = 0; i < nCi; i++ )
        Gia_ManAppendCi( pMix );
    Gia_ManHashStart( pMix );
    t = st__init_table( st__ptrcmp, st__ptrhash );
    Gia_ManForEachCo( pSpec, pObj, i )
    {
        Id = Gia_ObjId( pSpec, pObj );
        bFunc = Cudd_NotCond( (DdNode *)Vec_PtrEntry(vFuncs, Gia_ObjFaninId0(pObj, Id)), Gia_ObjFaninC0(pObj) );
        Gia_ManAppendCo( pMix, Openc_BddToLit(dd, bFunc, pMix, t) );
    }
    Gia_ManHashStop( pMix );
    st__free_table( t );
    Gia_ManForEachAnd( pSpec, pObj, i )
        if ( Vec_PtrEntry(vFuncs, i) )
            Cudd_RecursiveDeref( dd, (DdNode *)Vec_PtrEntry(vFuncs, i) );
    Gia_ManForEachCiId( pSpec, Id, i )
        if ( Vec_PtrEntry(vFuncs, Id) )
            Cudd_RecursiveDeref( dd, (DdNode *)Vec_PtrEntry(vFuncs, Id) );
    if ( Vec_PtrEntry(vFuncs, 0) )
        Cudd_RecursiveDeref( dd, (DdNode *)Vec_PtrEntry(vFuncs, 0) );
    Vec_PtrFree( vFuncs );
    Extra_StopManager( dd );
    Gia_ManStop( pSpec );
    p->pMixMethod = "direct G (BDD collapse)";
    p->fMixNeedSyn2 = 1;
    return pMix;
}
#else
static Gia_Man_t * Openc_SynthGBdd( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    (void)p;
    (void)pOrig;
    return NULL;
}
#endif

static Gia_Man_t * Openc_SynthGClassSum( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pMix, * pSpec;
    int i, k, shift, nAcc, nNum, fOk;
    int pAcc[128], pNum[32];
    if ( p->fOneHot )
        return NULL;
    for ( i = 0; i < p->nOps; i++ )
        if ( p->pOps[i].nEnc < 1 || p->pOps[i].nEnc > 8 )
            return NULL;
    pMix = Gia_ManStart( 256 + p->nMixVars * 32 );
    pMix->pName = Abc_UtilStrsav( "mixer" );
    for ( i = 0; i < p->nMixVars; i++ )
        Gia_ManAppendCi( pMix );
    Gia_ManHashStart( pMix );
    nAcc  = 0;
    shift = 0;
    for ( i = 0; i < p->nOps; i++ )
    {
        nNum = p->pOps[i].nEnc;
        for ( k = 0; k < nNum; k++ )
            pNum[k] = Gia_Obj2Lit( pMix, Gia_ManPi(pMix, shift + k) );
        shift += nNum;
        if ( p->pOps[i].nClasses < (1 << nNum) )
        {
            int c, used = 0;
            for ( c = 0; c < p->pOps[i].nClasses; c++ )
            {
                int eq = 1, b;
                for ( b = 0; b < nNum; b++ )
                    eq = Gia_ManHashAnd( pMix, eq, Abc_LitNotCond(pNum[b], !((c >> b) & 1)) );
                used = Gia_ManHashOr( pMix, used, eq );
            }
            for ( k = 0; k < nNum; k++ )
                pNum[k] = Gia_ManHashAnd( pMix, pNum[k], used );
        }
        if ( nAcc == 0 )
        {
            for ( k = 0; k < nNum; k++ )
                pAcc[k] = pNum[k];
            nAcc = nNum;
        }
        else
            nAcc = Openc_AddVec( pMix, pAcc, nAcc, pNum, nNum, pAcc );
    }
    for ( i = 0; i < p->nOuts; i++ )
        Gia_ManAppendCo( pMix, (i < nAcc) ? pAcc[i] : 0 );
    Gia_ManHashStop( pMix );
    pSpec = Openc_BuildSpecFromF( p, pOrig );
    fOk = Openc_VerifyCec( pSpec, pMix );
    Gia_ManStop( pSpec );
    if ( !fOk )
    {
        Gia_ManStop( pMix );
        return NULL;
    }
    p->pMixMethod = "direct G (class-code adder, CEC-checked)";
    return pMix;
}

static Gia_Man_t * Openc_BuildMixerG( Openc_Man_t * p, Gia_Man_t * pOrig )
{
    Gia_Man_t * pMix;
    if ( Openc_AllIdentity(p) )
    {
        pMix = Gia_ManDup( pOrig );
        ABC_FREE( pMix->pName );
        pMix->pName = Abc_UtilStrsav( "mixer" );
        p->pMixMethod = "direct G (identity, G = F)";
        return pMix;
    }
    if ( p->nMixVars <= OPENC_TT_MIX )
        return Openc_SynthGTt( p, pOrig );
    pMix = Openc_SynthGClassSum( p, pOrig );
    if ( pMix )
        return pMix;
    pMix = Openc_SynthGBdd( p, pOrig );
    if ( pMix )
        return pMix;
    Abc_Print( 0, "&openc: could not collapse G; using encoder-PI spec as mixer.\n" );
    pMix = Openc_BuildSpecFromF( p, pOrig );
    ABC_FREE( pMix->pName );
    pMix->pName = Abc_UtilStrsav( "mixer" );
    p->pMixMethod = "direct G (spec fallback)";
    return pMix;
}

static Gia_Man_t * Openc_Stitch( Gia_Man_t * pEnc, Gia_Man_t * pMix )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i, nBuf;
    nBuf = Gia_ManPoNum(pEnc);
    assert( Gia_ManPoNum(pEnc) == Gia_ManPiNum(pMix) || (Gia_ManPoNum(pEnc) == 0 && Gia_ManPiNum(pMix) <= 1) );
    pNew = Gia_ManStart( Gia_ManObjNum(pEnc) + Gia_ManObjNum(pMix) + nBuf + 16 );
    pNew->pName = Abc_UtilStrsav( pEnc->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pEnc)->Value = 0;
    Gia_ManForEachCi( pEnc, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pEnc, pObj, i )
        pObj->Value = Openc_DupHashAnd( pNew, pObj );
    Gia_ManConst0(pMix)->Value = 0;
    if ( Gia_ManPoNum(pEnc) == 0 )
    {
        Gia_ManForEachCi( pMix, pObj, i )
            pObj->Value = 0;
    }
    else
    {
        Gia_ManForEachCo( pEnc, pObj, i )
            Gia_ManPi(pMix, i)->Value = Gia_ManAppendBuf( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManForEachAnd( pMix, pObj, i )
        pObj->Value = Openc_DupHashAnd( pNew, pObj );
    Gia_ManForEachCo( pMix, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    return pNew;
}

static int Openc_VerifyTt( Gia_Man_t * pOrig, Gia_Man_t * pNew, int nWords )
{
    word ** pA, ** pB;
    int i, nOuts, status = 1;
    nOuts = Gia_ManPoNum(pOrig);
    if ( nOuts != Gia_ManPoNum(pNew) || Gia_ManPiNum(pOrig) != Gia_ManPiNum(pNew) )
        return 0;
    pA = Openc_AllocTts( nOuts, nWords );
    pB = Openc_AllocTts( nOuts, nWords );
    if ( !Openc_ExtractTruths(pOrig, pA, nOuts, nWords) ||
         !Openc_ExtractTruths(pNew,  pB, nOuts, nWords) )
        status = 0;
    else
    {
        for ( i = 0; i < nOuts; i++ )
            if ( !Abc_TtEqual(pA[i], pB[i], nWords) )
                status = 0;
    }
    Openc_FreeTts( pA, nOuts );
    Openc_FreeTts( pB, nOuts );
    return status;
}

static int Openc_VerifyCec( Gia_Man_t * pOrig, Gia_Man_t * pNew )
{
    Cec_ParCec_t Pars;
    Gia_Man_t * pMiter;
    int RetValue;
    if ( Gia_ManPiNum(pOrig) != Gia_ManPiNum(pNew) || Gia_ManPoNum(pOrig) != Gia_ManPoNum(pNew) )
        return 0;
    Cec_ManCecSetDefaultParams( &Pars );
    Pars.fSilent = 1;
    pMiter = Gia_ManMiter( pOrig, pNew, 0, 1, 0, 0, 0 );
    if ( pMiter == NULL )
        return 0;
    RetValue = Cec_ManVerify( pMiter, &Pars );
    Gia_ManStop( pMiter );
    return RetValue == 1;
}


////////////////////////////////////////////////////////////////////////
///           BIJECTIVE REPRESENTATION SEARCH (-e perm)              ///
////////////////////////////////////////////////////////////////////////

typedef struct Openc_PermCost_t_ Openc_PermCost_t;
struct Openc_PermCost_t_
{
    int nEncAnds;
    int nEncLev;
    int nMixAndsRaw;
    int nMixLevRaw;
    int nMixAnds;
    int nMixLev;
    int nAllAnds;
    int nAllLev;
    int fOk;
};

typedef struct Openc_PermCand_t_ Openc_PermCand_t;
struct Openc_PermCand_t_
{
    int * pPerms;
    int   nMixAndsRaw;
    int   nMixAnds;
    int   nMixLev;
    int   nEncAnds;
    int   nEncLev;
    int   fOk;
    int   fUsed;
};

static unsigned Openc_LcgNext( unsigned * pSeed )
{
    *pSeed = *pSeed * 1664525u + 1013904223u;
    return *pSeed;
}

static int Openc_TcToInt( int bits, int n )
{
    int sign;
    if ( n <= 0 )
        return 0;
    sign = 1 << (n - 1);
    if ( bits & sign )
        return bits - (sign << 1);
    return bits;
}

static int Openc_TcToSm( int tc, int n )
{
    int v, signbit, mag;
    if ( n <= 0 )
        return 0;
    v       = Openc_TcToInt( tc, n );
    signbit = 1 << (n - 1);
    mag     = (v < 0) ? -v : v;
    return (v < 0 ? signbit : 0) | (mag & (signbit - 1));
}

static int Openc_NextPerm( int * a, int n )
{
    int i, j, k, t;
    for ( i = n - 2; i >= 0 && a[i] >= a[i + 1]; i-- );
    if ( i < 0 )
        return 0;
    for ( j = n - 1; a[j] <= a[i]; j-- );
    t = a[i]; a[i] = a[j]; a[j] = t;
    for ( k = i + 1, j = n - 1; k < j; k++, j-- )
    {
        t = a[k]; a[k] = a[j]; a[j] = t;
    }
    return 1;
}

static void Openc_PermIdent( int * p, int nM )
{
    int i;
    for ( i = 0; i < nM; i++ )
        p[i] = i;
}

static void Openc_PermSm( int * p, int n )
{
    int i, nM = 1 << n;
    for ( i = 0; i < nM; i++ )
        p[i] = Openc_TcToSm( i, n );
}

static void Openc_PermCopy( int * pDst, int * pSrc, int n )
{
    int i;
    for ( i = 0; i < n; i++ )
        pDst[i] = pSrc[i];
}

static int Openc_PermEq( int * a, int * b, int n )
{
    int i;
    for ( i = 0; i < n; i++ )
        if ( a[i] != b[i] )
            return 0;
    return 1;
}

static int Openc_PermHamming( int * a, int * b, int n )
{
    int i, c = 0;
    for ( i = 0; i < n; i++ )
        if ( a[i] != b[i] )
            c++;
    return c;
}

static int Openc_PermIsBij( int * p, int nM )
{
    int * pSeen, i;
    if ( nM <= 0 )
        return 0;
    pSeen = ABC_CALLOC( int, nM );
    for ( i = 0; i < nM; i++ )
    {
        if ( p[i] < 0 || p[i] >= nM || pSeen[p[i]] )
        {
            ABC_FREE( pSeen );
            return 0;
        }
        pSeen[p[i]] = 1;
    }
    ABC_FREE( pSeen );
    return 1;
}

static void Openc_PermShuffle( int * p, int nM, unsigned * pSeed )
{
    int i, j, t;
    Openc_PermIdent( p, nM );
    for ( i = nM - 1; i > 0; i-- )
    {
        j = (int)(Openc_LcgNext(pSeed) % (unsigned)(i + 1));
        t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static int Openc_ApplyBitRewrite( int x, int * pPi, int n, int mask )
{
    int y = 0, k;
    for ( k = 0; k < n; k++ )
        if ( (x >> k) & 1 )
            y |= 1 << pPi[k];
    return y ^ mask;
}

static int Openc_PermBitRewriteEq( int * pA, int * pB, int n )
{
    int pi[OPENC_PERM_BOUND], nM, mask, i, ok;
    if ( n < 1 || n > OPENC_PERM_BOUND )
        return 0;
    nM = 1 << n;
    Openc_PermIdent( pi, n );
    do
    {
        for ( mask = 0; mask < nM; mask++ )
        {
            ok = 1;
            for ( i = 0; i < nM; i++ )
                if ( Openc_ApplyBitRewrite(pA[i], pi, n, mask) != pB[i] )
                {
                    ok = 0;
                    break;
                }
            if ( ok )
                return 1;
        }
    } while ( Openc_NextPerm(pi, n) );
    return 0;
}

static void Openc_PrintPermLine( char * pName, int * pPerm, int nM, int nBound )
{
    int i, nShow;
    nShow = Abc_MinInt( nM, 16 );
    Abc_Print( 1, "  %-18s", pName );
    for ( i = 0; i < nShow; i++ )
        Abc_Print( 1, "%s%d", i ? "," : " [", pPerm[i] );
    Abc_Print( 1, "]%s\n", nM > nShow ? " ..." : "" );
    (void)nBound;
}

static int Openc_FactCapped( int n, int cap )
{
    int f = 1, i;
    for ( i = 2; i <= n; i++ )
    {
        if ( f > cap / i )
            return cap + 1;
        f *= i;
    }
    return f;
}

static int Openc_PowCapped( int a, int e, int cap )
{
    int i, r = 1;
    for ( i = 0; i < e; i++ )
    {
        if ( a > 0 && r > cap / a )
            return cap + 1;
        r *= a;
    }
    return r;
}

static int Openc_Gf2Map( int * pRows, int bias, int x, int n )
{
    int y = bias, i, j, par;
    for ( i = 0; i < n; i++ )
    {
        par = 0;
        for ( j = 0; j < n; j++ )
            if ( ((pRows[i] >> j) & 1) && ((x >> j) & 1) )
                par ^= 1;
        if ( par )
            y ^= 1 << i;
    }
    return y;
}

static int Openc_Gf2Invertible( int * pRows, int n )
{
    int m[OPENC_PERM_BOUND], i, k, t, piv;
    for ( i = 0; i < n; i++ )
        m[i] = pRows[i];
    for ( k = 0; k < n; k++ )
    {
        piv = -1;
        for ( i = k; i < n; i++ )
            if ( (m[i] >> k) & 1 )
            {
                piv = i;
                break;
            }
        if ( piv < 0 )
            return 0;
        t = m[k]; m[k] = m[piv]; m[piv] = t;
        for ( i = 0; i < n; i++ )
            if ( i != k && ((m[i] >> k) & 1) )
                m[i] ^= m[k];
    }
    return 1;
}

static int Openc_OpsUniform( Openc_Man_t * p, int * pBound )
{
    int i;
    if ( p->nOps < 1 )
        return 0;
    *pBound = p->pOps[0].nBound;
    if ( *pBound < 1 || *pBound > OPENC_PERM_BOUND )
        return 0;
    for ( i = 1; i < p->nOps; i++ )
        if ( p->pOps[i].nBound != *pBound )
            return 0;
    return 1;
}

static void Openc_PermFillShared( int * pAll, int nOps, int * pOne, int nM )
{
    int i;
    for ( i = 0; i < nOps; i++ )
        Openc_PermCopy( pAll + i * nM, pOne, nM );
}

static void Openc_PermFillFirstPair( int * pAll, int nOps, int * pOne, int nM )
{
    int i;
    Openc_PermIdent( pAll, nM );
    for ( i = 1; i < nOps; i++ )
        Openc_PermIdent( pAll + i * nM, nM );
    if ( nOps >= 1 )
        Openc_PermCopy( pAll, pOne, nM );
    if ( nOps >= 2 )
        Openc_PermCopy( pAll + nM, pOne, nM );
}

static void Openc_InstallPerms( Openc_Man_t * p, int * pAll )
{
    int i, b, k, nMints;
    p->nMixVars = 0;
    for ( i = 0; i < p->nOps; i++ )
    {
        Openc_Op_t * pOp = p->pOps + i;
        int * pPerm = pAll + i * (1 << pOp->nBound);
        nMints = 1 << pOp->nBound;
        Openc_OpFree( pOp );
        pOp->pClass = ABC_ALLOC( int, nMints );
        pOp->pRep   = ABC_ALLOC( int, nMints );
        pOp->nClasses = nMints;
        pOp->nEnc = pOp->nBound;
        pOp->fIdentity = 1;
        for ( b = 0; b < nMints; b++ )
        {
            pOp->pClass[b] = pPerm[b];
            pOp->pRep[pPerm[b]] = b;
            if ( pPerm[b] != b )
                pOp->fIdentity = 0;
        }
        pOp->pEncTt = ABC_ALLOC( word *, pOp->nEnc );
        for ( k = 0; k < pOp->nEnc; k++ )
        {
            pOp->pEncTt[k] = ABC_CALLOC( word, Abc_Truth6WordNum(pOp->nBound) );
            for ( b = 0; b < nMints; b++ )
                if ( (pOp->pClass[b] >> k) & 1 )
                    Abc_TtSetBit( pOp->pEncTt[k], b );
        }
        p->nMixVars += pOp->nEnc;
    }
}

static int Openc_AllConsecEqual( Openc_Man_t * p )
{
    int i;
    for ( i = 0; i < p->nOps; i++ )
        if ( !Openc_OpIsConsec(p->pOps + i) || p->pOps[i].nEnc != p->pOps[i].nBound )
            return 0;
    return p->nOps > 0;
}

static void Openc_CopyPadZ( int * pDst, int nDst, int * pSrc, int nSrc )
{
    int i;
    for ( i = 0; i < nDst; i++ )
        pDst[i] = (i < nSrc) ? pSrc[i] : 0;
}

static void Openc_SmMagLitsAt( Gia_Man_t * p, int * pSm, int n, int iSign, int * pMag )
{
    int k, t = 0, eq0 = 1;
    assert( iSign >= 0 && iSign < n );
    for ( k = 0; k < n; k++ )
    {
        if ( k == iSign )
            continue;
        pMag[t++] = pSm[k];
        eq0 = Gia_ManHashAnd( p, eq0, Abc_LitNot(pSm[k]) );
    }
    if ( n >= 1 )
        pMag[n - 1] = Gia_ManHashAnd( p, pSm[iSign], eq0 );
}

static void Openc_SmMagLits( Gia_Man_t * p, int * pSm, int n, int * pMag )
{
    Openc_SmMagLitsAt( p, pSm, n, n - 1, pMag );
}

static int Openc_TcNegMod( Gia_Man_t * p, int * pX, int n, int * pY )
{
    int i, pNot[128], pSum[128], one[1], nSum;
    assert( n <= 128 );
    for ( i = 0; i < n; i++ )
        pNot[i] = Abc_LitNot( pX[i] );
    one[0] = 1;
    nSum = Openc_AddVec( p, pNot, n, one, 1, pSum );
    Openc_CopyPadZ( pY, n, pSum, nSum );
    return n;
}

/* Modified radix-4 Booth: digits {-2,-1,0,1,2} from overlapping triples. */
static void Openc_BoothPP( Gia_Man_t * p, int y2, int y1, int y0, int * pX, int nX, int * pPP, int nPP )
{
    int i, allEq, isTwo, neg;
    int one[128], two[128], neg1[128], neg2[128];
    assert( nPP <= 128 && nX <= nPP );
    Openc_CopyPadZ( one, nPP, pX, nX );
    two[0] = 0;
    for ( i = 0; i < nPP - 1; i++ )
        two[i + 1] = one[i];
    Openc_TcNegMod( p, one, nPP, neg1 );
    Openc_TcNegMod( p, two, nPP, neg2 );
    allEq = Gia_ManHashAnd( p, Abc_LitNot(Gia_ManHashXor(p, y2, y1)), Abc_LitNot(Gia_ManHashXor(p, y1, y0)) );
    isTwo = Gia_ManHashAnd( p, Abc_LitNot(Gia_ManHashXor(p, y1, y0)), Gia_ManHashXor(p, y2, y1) );
    neg   = y2;
    for ( i = 0; i < nPP; i++ )
    {
        int mag = Gia_ManHashMux( p, isTwo, two[i], one[i] );
        int ng  = Gia_ManHashMux( p, isTwo, neg2[i], neg1[i] );
        int d   = Gia_ManHashMux( p, neg, ng, mag );
        pPP[i]  = Gia_ManHashMux( p, allEq, 0, d );
    }
}

static int Openc_BoothMul( Gia_Man_t * p, int * pX, int nX, int * pY, int nY, int * pP, int nP, int fSigned )
{
    int nYext, g, nAcc = 0, i;
    int yext[32], pXw[128], pPP[128], pSh[128], pAcc[128], pAdd[128];
    int y2, y1, y0;
    assert( nY <= 32 && nP <= 128 );
    if ( fSigned )
    {
        nYext = nY + (nY & 1);
        Openc_SignExtLits( pY, nY, nYext, yext );
    }
    else
    {
        /* extra 0 MSB so the last digit includes the unsigned high bit */
        nYext = nY + 1;
        nYext = nYext + (nYext & 1);
        if ( nYext > 32 )
            nYext = 32;
        Openc_ZeroPadLits( pY, nY, nYext, yext );
    }
    if ( fSigned )
        Openc_SignExtLits( pX, nX, nP, pXw );
    else
        Openc_ZeroPadLits( pX, nX, nP, pXw );
    for ( g = 0; g < nYext; g += 2 )
    {
        y0 = (g == 0) ? 0 : yext[g - 1];
        y1 = yext[g];
        y2 = (g + 1 < nYext) ? yext[g + 1] : (fSigned ? yext[nYext - 1] : 0);
        Openc_BoothPP( p, y2, y1, y0, pXw, nP, pPP, nP );
        Openc_ShlZ( pSh, nP, pPP, nP, g );
        if ( nAcc == 0 )
        {
            for ( i = 0; i < nP; i++ )
                pAcc[i] = pSh[i];
            nAcc = nP;
        }
        else
        {
            nAcc = Openc_AddVec( p, pAcc, nAcc, pSh, nP, pAdd );
            Openc_CopyPadZ( pAcc, nP, pAdd, nAcc );
            nAcc = nP;
        }
    }
    for ( i = 0; i < nP; i++ )
        pP[i] = (i < nAcc) ? pAcc[i] : 0;
    return nP;
}

static void Openc_TplName( char * buf, int kind, int iSign )
{
    if ( kind == OPENC_TPL_TC )
        sprintf( buf, "tpl tc_array" );
    else if ( kind == OPENC_TPL_UNS )
        sprintf( buf, "tpl unsigned" );
    else if ( kind == OPENC_TPL_BOOTH )
        sprintf( buf, "tpl booth4" );
    else if ( kind == OPENC_TPL_BOOTHUNS )
        sprintf( buf, "tpl booth4_uns" );
    else if ( kind == OPENC_TPL_SM )
        sprintf( buf, "tpl sm_mag s=%d", iSign );
    else if ( kind == OPENC_TPL_SMBOOTH )
        sprintf( buf, "tpl sm_booth s=%d", iSign );
    else
        sprintf( buf, "tpl ?" );
}

/* Mixer G of codes. Template kind chooses the arithmetic; encoding E is recovered separately. */
static Gia_Man_t * Openc_BuildTplMixer( Openc_Man_t * p, int kind, int iSign )
{
    Gia_Man_t * pMix;
    int i, t, k, shift, nTerms, nAcc, nProd, nW, sign, nOuts, fSm;
    int pA[32], pB[32], pAe[128], pBe[128];
    int pMagA[32], pMagB[32];
    int pProd[128], pPe[128], pNeg[128], pTerm[128], pAcc[128], pAdd[128];
    if ( p->nOps < 2 || (p->nOps & 1) )
        return NULL;
    nW = p->pOps[0].nBound;
    if ( nW < 1 || nW > 32 || p->nOuts < 1 || p->nOuts > 128 )
        return NULL;
    fSm = (kind == OPENC_TPL_SM || kind == OPENC_TPL_SMBOOTH);
    if ( fSm && (iSign < 0 || iSign >= nW) )
        return NULL;
    for ( i = 0; i < p->nOps; i++ )
        if ( p->pOps[i].nEnc != p->pOps[i].nBound || p->pOps[i].nBound != nW )
            return NULL;
    nTerms = p->nOps / 2;
    nOuts  = p->nOuts;
    pMix = Gia_ManStart( 256 + p->nMixVars * 64 + nOuts * 64 );
    pMix->pName = Abc_UtilStrsav( "mixer" );
    for ( i = 0; i < Abc_MaxInt(p->nMixVars, 1); i++ )
        Gia_ManAppendCi( pMix );
    Gia_ManHashStart( pMix );
    nAcc  = 0;
    shift = 0;
    for ( t = 0; t < nTerms; t++ )
    {
        for ( k = 0; k < nW; k++ )
        {
            pA[k] = Gia_Obj2Lit( pMix, Gia_ManPi(pMix, shift + k) );
            pB[k] = Gia_Obj2Lit( pMix, Gia_ManPi(pMix, shift + nW + k) );
        }
        shift += 2 * nW;
        if ( kind == OPENC_TPL_TC )
        {
            Openc_SignExtLits( pA, nW, nOuts, pAe );
            Openc_SignExtLits( pB, nW, nOuts, pBe );
            nProd = Openc_Mul( pMix, pAe, nOuts, pBe, nOuts, pProd );
            Openc_CopyPadZ( pTerm, nOuts, pProd, nProd );
        }
        else if ( kind == OPENC_TPL_UNS )
        {
            nProd = Openc_Mul( pMix, pA, nW, pB, nW, pProd );
            Openc_CopyPadZ( pTerm, nOuts, pProd, nProd );
        }
        else if ( kind == OPENC_TPL_BOOTH )
            Openc_BoothMul( pMix, pA, nW, pB, nW, pTerm, nOuts, 1 );
        else if ( kind == OPENC_TPL_BOOTHUNS )
            Openc_BoothMul( pMix, pA, nW, pB, nW, pTerm, nOuts, 0 );
        else if ( fSm )
        {
            Openc_SmMagLitsAt( pMix, pA, nW, iSign, pMagA );
            Openc_SmMagLitsAt( pMix, pB, nW, iSign, pMagB );
            if ( kind == OPENC_TPL_SMBOOTH )
            {
                Openc_BoothMul( pMix, pMagA, nW, pMagB, nW, pProd, nOuts, 0 );
                nProd = nOuts;
            }
            else
                nProd = Openc_Mul( pMix, pMagA, nW, pMagB, nW, pProd );
            Openc_CopyPadZ( pPe, nOuts, pProd, nProd );
            sign = Gia_ManHashXor( pMix, pA[iSign], pB[iSign] );
            Openc_TcNegMod( pMix, pPe, nOuts, pNeg );
            for ( k = 0; k < nOuts; k++ )
                pTerm[k] = Gia_ManHashMux( pMix, sign, pNeg[k], pPe[k] );
        }
        else
        {
            Gia_ManHashStop( pMix );
            Gia_ManStop( pMix );
            return NULL;
        }
        if ( nAcc == 0 )
        {
            for ( k = 0; k < nOuts; k++ )
                pAcc[k] = pTerm[k];
            nAcc = nOuts;
        }
        else
        {
            nAcc = Openc_AddVec( pMix, pAcc, nAcc, pTerm, nOuts, pAdd );
            Openc_CopyPadZ( pAcc, nOuts, pAdd, nAcc );
            nAcc = nOuts;
        }
    }
    for ( i = 0; i < nOuts; i++ )
        Gia_ManAppendCo( pMix, (i < nAcc) ? pAcc[i] : 0 );
    Gia_ManHashStop( pMix );
    return pMix;
}

/* Arithmetic SM-family mixer: mixer PIs are codes. Bit iSign is the sign;
   remaining bits in index order are the magnitude. Mag-mul + sign-xor + TC convert. */
static Gia_Man_t * Openc_BuildSmMixerAt( Openc_Man_t * p, int iSign )
{
    return Openc_BuildTplMixer( p, OPENC_TPL_SM, iSign );
}

/* Hand SM-friendly mixer: mixer PIs are sign-magnitude codes (sign = MSB).
   Magnitude multiply + product-sign XOR + TC negate/mux. Not a search seed. */
static Gia_Man_t * Openc_BuildSmFriendlyMixer( Openc_Man_t * p )
{
    if ( p->nOps < 1 )
        return NULL;
    return Openc_BuildSmMixerAt( p, p->pOps[0].nBound - 1 );
}

static int Openc_TtMintEq( word ** pA, int mA, word ** pB, int mB, int nOuts )
{
    int o;
    for ( o = 0; o < nOuts; o++ )
        if ( Abc_TtGetBit(pA[o], mA) != Abc_TtGetBit(pB[o], mB) )
            return 0;
    return 1;
}

/* Recover bijection E: semantic TC minterm -> mixer code, such that G(E(x),E(y))=F(x,y).
   Uses F(1,y)=y: try each candidate for E(1), invert G(E(1), ·). SM is not an input. */
static int Openc_ArithSolveEnc( word ** pF, word ** pG, int nOuts, int nBound, int * pE )
{
    int nM = 1 << nBound, c1, y, c, x, nHit, cHit, ok, * pUsed;
    if ( nBound < 1 || nBound > OPENC_PERM_BOUND )
        return 0;
    pUsed = ABC_CALLOC( int, nM );
    for ( c1 = 0; c1 < nM; c1++ )
    {
        memset( pUsed, 0, sizeof(int) * nM );
        ok = 1;
        for ( y = 0; y < nM; y++ )
        {
            int mF = 1 | (y << nBound);
            nHit = 0;
            cHit = -1;
            for ( c = 0; c < nM; c++ )
            {
                int mG = c1 | (c << nBound);
                if ( !Openc_TtMintEq(pF, mF, pG, mG, nOuts) )
                    continue;
                nHit++;
                cHit = c;
            }
            if ( nHit != 1 || pUsed[cHit] )
            {
                ok = 0;
                break;
            }
            pUsed[cHit] = 1;
            pE[y] = cHit;
        }
        if ( !ok )
            continue;
        for ( x = 0; x < nM && ok; x++ )
            for ( y = 0; y < nM; y++ )
            {
                int mF = x | (y << nBound);
                int mG = pE[x] | (pE[y] << nBound);
                if ( !Openc_TtMintEq(pF, mF, pG, mG, nOuts) )
                {
                    ok = 0;
                    break;
                }
            }
        if ( ok && Openc_PermIsBij(pE, nM) )
        {
            ABC_FREE( pUsed );
            return 1;
        }
    }
    ABC_FREE( pUsed );
    return 0;
}

static void Openc_PutOpVal( int * pPi, int nBound, int iOp, int val )
{
    int k;
    for ( k = 0; k < nBound; k++ )
        pPi[iOp * nBound + k] = (val >> k) & 1;
}

static void Openc_FillDotPi( int * pPi, int nBound, int nOps, int iTerm, int va, int vb, int vRest )
{
    int o;
    for ( o = 0; o < nOps; o++ )
        Openc_PutOpVal( pPi, nBound, o, vRest );
    Openc_PutOpVal( pPi, nBound, 2 * iTerm,     va );
    Openc_PutOpVal( pPi, nBound, 2 * iTerm + 1, vb );
}

static void Openc_EvalMint( Gia_Man_t * p, int * pPi, int * pOut )
{
    Gia_Obj_t * pObj;
    int i;
    Gia_ManConst0(p)->fMark0 = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->fMark0 = pPi[i] & 1;
    Gia_ManForEachAnd( p, pObj, i )
        pObj->fMark0 = (Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj))
                     & (Gia_ObjFanin1(pObj)->fMark0 ^ Gia_ObjFaninC1(pObj));
    Gia_ManForEachCo( p, pObj, i )
        pOut[i] = Gia_ObjFanin0(pObj)->fMark0 ^ Gia_ObjFaninC0(pObj);
}

static int Openc_VecBitEq( int * pA, int * pB, int n )
{
    int i;
    for ( i = 0; i < n; i++ )
        if ( (pA[i] & 1) != (pB[i] & 1) )
            return 0;
    return 1;
}

static int Openc_ArithCheckTerm( Gia_Man_t * pF, Gia_Man_t * pG, int nBound, int nOps, int iTerm, int * pE )
{
    int nM = 1 << nBound, x, y, nPo = Gia_ManPoNum(pF);
    int pPiF[OPENC_MAX_PI], pPiG[OPENC_MAX_PI], oF[128], oG[128];
    int c0 = pE[0];
    if ( nPo > 128 || nOps * nBound > OPENC_MAX_PI )
        return 0;
    for ( x = 0; x < nM; x++ )
        for ( y = 0; y < nM; y++ )
        {
            Openc_FillDotPi( pPiF, nBound, nOps, iTerm, x, y, 0 );
            Openc_FillDotPi( pPiG, nBound, nOps, iTerm, pE[x], pE[y], c0 );
            Openc_EvalMint( pF, pPiF, oF );
            Openc_EvalMint( pG, pPiG, oG );
            if ( !Openc_VecBitEq(oF, oG, nPo) )
                return 0;
        }
    return 1;
}

static int Openc_ArithCheckAllTerms( Gia_Man_t * pF, Gia_Man_t * pG, int nBound, int nOps, int * pE )
{
    int t, nTerms = nOps / 2;
    for ( t = 0; t < nTerms; t++ )
        if ( !Openc_ArithCheckTerm(pF, pG, nBound, nOps, t, pE) )
            return 0;
    return 1;
}

/* Recover shared E from an N-term dot product: F(1,y,0,...,0)=y, extra terms at TC 0.
   Mixer codes for extra operands are E(0). Known encodings are not seeds. */
static int Openc_ArithSolveEncDot( Gia_Man_t * pF, Gia_Man_t * pG, int nBound, int nOps, int iTerm, int * pE )
{
    int nM, nPo, c0, c1, y, c, nHit, cHit, ok, pass, * pUsed;
    int pPiF[OPENC_MAX_PI], pPiG[OPENC_MAX_PI], oF[128], oG[128];
    int pC0Try[256];
    int nC0, iC0;
    if ( nBound < 1 || nBound > OPENC_PERM_BOUND || nOps < 2 || (nOps & 1) )
        return 0;
    if ( iTerm < 0 || 2 * iTerm + 1 >= nOps )
        return 0;
    if ( Gia_ManPiNum(pF) != nOps * nBound || Gia_ManPiNum(pG) != nOps * nBound )
        return 0;
    nPo = Gia_ManPoNum(pF);
    if ( nPo < 1 || nPo > 128 || Gia_ManPoNum(pG) != nPo )
        return 0;
    nM = 1 << nBound;
    if ( nM > 256 )
        return 0;
    /* Prefer mixer-code 0 for semantic 0 (annihilator of F), then the rest. */
    pC0Try[0] = 0;
    nC0 = 1;
    for ( c0 = 1; c0 < nM; c0++ )
        pC0Try[nC0++] = c0;
    pUsed = ABC_CALLOC( int, nM );
    for ( iC0 = 0; iC0 < nC0; iC0++ )
    {
        c0 = pC0Try[iC0];
        for ( c1 = 0; c1 < nM; c1++ )
        {
            memset( pUsed, 0, sizeof(int) * nM );
            ok = 1;
            for ( y = 0; y < nM; y++ )
            {
                Openc_FillDotPi( pPiF, nBound, nOps, iTerm, 1, y, 0 );
                Openc_EvalMint( pF, pPiF, oF );
                nHit = 0;
                cHit = -1;
                for ( c = 0; c < nM; c++ )
                {
                    Openc_FillDotPi( pPiG, nBound, nOps, iTerm, c1, c, c0 );
                    Openc_EvalMint( pG, pPiG, oG );
                    if ( !Openc_VecBitEq(oF, oG, nPo) )
                        continue;
                    nHit++;
                    cHit = c;
                }
                if ( nHit != 1 || pUsed[cHit] )
                {
                    ok = 0;
                    break;
                }
                pUsed[cHit] = 1;
                pE[y] = cHit;
            }
            if ( !ok || pE[0] != c0 || pE[1] != c1 )
                continue;
            if ( !Openc_PermIsBij(pE, nM) )
                continue;
            pass = Openc_ArithCheckTerm( pF, pG, nBound, nOps, iTerm, pE );
            if ( pass )
            {
                ABC_FREE( pUsed );
                Gia_ManCleanMark0( pF );
                Gia_ManCleanMark0( pG );
                return 1;
            }
        }
    }
    ABC_FREE( pUsed );
    Gia_ManCleanMark0( pF );
    Gia_ManCleanMark0( pG );
    return 0;
}

static Gia_Man_t * Openc_PermOptimize( Gia_Man_t * pMix, int nOpt, int fDelay )
{
    Gia_Man_t * pTemp;
    if ( pMix == NULL )
        return NULL;
    if ( nOpt >= 1 )
    {
        pTemp = Gia_ManCompress2( pMix, 1, 0 );
        if ( pTemp && pTemp != pMix )
        {
            Gia_ManStop( pMix );
            pMix = pTemp;
        }
    }
    if ( nOpt >= 2 )
    {
        Gia_Man_t * pKeep = Gia_ManDup( pMix );
        pTemp = Gia_ManAigSyn2( pMix, 0, 1, 0, 100, 0, 0, 0 );
        if ( pTemp && pTemp != pMix )
        {
            Gia_ManStop( pMix );
            pMix = pTemp;
        }
        if ( pMix && Gia_ManHasMapping(pMix) )
            Vec_IntFreeP( &pMix->vMapping );
        if ( pMix && Gia_ManHasMapping2(pMix) )
            Vec_WecFreeP( &pMix->vMapping2 );
        if ( pKeep && Gia_ManAndNotBufNum(pMix) > Gia_ManAndNotBufNum(pKeep) )
        {
            Gia_ManStop( pMix );
            pMix = pKeep;
        }
        else if ( pKeep )
            Gia_ManStop( pKeep );
    }
    if ( fDelay )
    {
        pTemp = Gia_ManBalance( pMix, 0, 0, 0 );
        if ( pTemp && pTemp != pMix )
        {
            Gia_ManStop( pMix );
            pMix = pTemp;
        }
    }
    return pMix;
}

static void Openc_FillGFromF( Openc_Man_t * p, word ** pG )
{
    int mx, o, nMints, nWordsG, * pPiBits, v, mF;
    nMints  = (p->nMixVars > 0) ? (1 << p->nMixVars) : 1;
    nWordsG = Abc_Truth6WordNum( Abc_MaxInt(p->nMixVars, 1) );
    for ( o = 0; o < p->nOuts; o++ )
        Abc_TtClear( pG[o], nWordsG );
    if ( Openc_AllConsecEqual(p) )
    {
        int i, B = p->pOps[0].nBound, mask = (1 << B) - 1;
        for ( mx = 0; mx < nMints; mx++ )
        {
            mF = 0;
            for ( i = 0; i < p->nOps; i++ )
            {
                int code = (mx >> (i * B)) & mask;
                mF |= p->pOps[i].pRep[code] << (i * B);
            }
            for ( o = 0; o < p->nOuts; o++ )
                if ( Abc_TtGetBit(p->pOuts[o], mF) )
                    Abc_TtSetBit( pG[o], mx );
        }
        return;
    }
    pPiBits = ABC_ALLOC( int, p->nVars );
    for ( mx = 0; mx < nMints; mx++ )
    {
        if ( !Openc_CodesToPiBits(p, mx, pPiBits) )
            continue;
        mF = 0;
        for ( v = 0; v < p->nVars; v++ )
            if ( pPiBits[v] )
                mF |= 1 << v;
        for ( o = 0; o < p->nOuts; o++ )
            if ( Abc_TtGetBit(p->pOuts[o], mF) )
                Abc_TtSetBit( pG[o], mx );
    }
    ABC_FREE( pPiBits );
}

static Gia_Man_t * Openc_PermMakeMixer( Openc_Man_t * p, word ** pG, int nOpt, int fDelay )
{
    Gia_Man_t * pMix;
    if ( p->fStruct )
    {
        pMix = Openc_BuildSpecFromF( p, p->pGia );
        ABC_FREE( pMix->pName );
        pMix->pName = Abc_UtilStrsav( "mixer" );
    }
    else
    {
        Openc_FillGFromF( p, pG );
        pMix = Openc_GiaFromTts( p->nMixVars, p->nOuts, pG, "mixer" );
    }
    return Openc_PermOptimize( pMix, nOpt, fDelay );
}

static int Openc_PermMixCost( Openc_Man_t * p, word ** pG, int nOpt, int * pLev )
{
    Gia_Man_t * pMix;
    int nAnds;
    pMix = Openc_PermMakeMixer( p, pG, nOpt, 0 );
    nAnds = Gia_ManAndNotBufNum( pMix );
    if ( pLev )
        *pLev = Gia_ManLevelNum( pMix );
    Gia_ManStop( pMix );
    return nAnds;
}

static int Openc_PermVerifyAll( Openc_Man_t * p, Gia_Man_t * pOrig, Gia_Man_t * pAll )
{
    if ( pOrig == NULL || pAll == NULL )
        return 0;
    if ( p->nVars <= OPENC_TT_PI && p->pOuts )
        return Openc_VerifyTt( pOrig, pAll, Abc_Truth6WordNum(p->nVars) );
    return Openc_VerifyCec( pOrig, pAll );
}

static Gia_Man_t * Openc_PermBuildVerified( Openc_Man_t * p, Gia_Man_t * pOrig, word ** pG, int nOpt, int fDelayOpt, Openc_PermCost_t * pCost )
{
    Gia_Man_t * pEnc, * pMix, * pAll, * pRaw;
    pEnc = Openc_BuildEncoder( p, pOrig );
    pCost->nMixAndsRaw = 0;
    pCost->nMixLevRaw  = 0;
    pRaw = Openc_PermMakeMixer( p, pG, 0, 0 );
    pCost->nMixAndsRaw = Gia_ManAndNotBufNum( pRaw );
    pCost->nMixLevRaw  = Gia_ManLevelNum( pRaw );
    Gia_ManStop( pRaw );
    pMix = Openc_PermMakeMixer( p, pG, nOpt, fDelayOpt );
    pAll = Openc_Stitch( pEnc, pMix );
    pCost->fOk      = Openc_PermVerifyAll( p, pOrig, pAll );
    pCost->nEncAnds = Gia_ManAndNotBufNum( pEnc );
    pCost->nEncLev  = Gia_ManLevelNum( pEnc );
    pCost->nMixAnds = Gia_ManAndNotBufNum( pMix );
    pCost->nMixLev  = Gia_ManLevelNum( pMix );
    pCost->nAllAnds = Gia_ManAndNotBufNum( pAll );
    pCost->nAllLev  = Gia_ManLevelNum( pAll );
    Gia_ManStop( pEnc );
    Gia_ManStop( pMix );
    return pAll;
}

static Gia_Man_t * Openc_PermBuildTpl( Openc_Man_t * p, Gia_Man_t * pOrig, int kind, int iSign, int nOpt, int fDelayOpt, Openc_PermCost_t * pCost )
{
    Gia_Man_t * pEnc, * pMix, * pAll;
    memset( pCost, 0, sizeof(*pCost) );
    pMix = Openc_BuildTplMixer( p, kind, iSign );
    if ( pMix == NULL )
        return NULL;
    pEnc = Openc_BuildEncoder( p, pOrig );
    pCost->nMixAndsRaw = Gia_ManAndNotBufNum( pMix );
    pCost->nMixLevRaw  = Gia_ManLevelNum( pMix );
    pMix = Openc_PermOptimize( pMix, nOpt, fDelayOpt );
    pAll = Openc_Stitch( pEnc, pMix );
    pCost->fOk      = Openc_PermVerifyAll( p, pOrig, pAll );
    pCost->nEncAnds = Gia_ManAndNotBufNum( pEnc );
    pCost->nEncLev  = Gia_ManLevelNum( pEnc );
    pCost->nMixAnds = Gia_ManAndNotBufNum( pMix );
    pCost->nMixLev  = Gia_ManLevelNum( pMix );
    pCost->nAllAnds = Gia_ManAndNotBufNum( pAll );
    pCost->nAllLev  = Gia_ManLevelNum( pAll );
    Gia_ManStop( pEnc );
    Gia_ManStop( pMix );
    return pAll;
}

static Gia_Man_t * Openc_PermBuildArith( Openc_Man_t * p, Gia_Man_t * pOrig, int iSign, int nOpt, int fDelayOpt, Openc_PermCost_t * pCost )
{
    return Openc_PermBuildTpl( p, pOrig, OPENC_TPL_SM, iSign, nOpt, fDelayOpt, pCost );
}

static Gia_Man_t * Openc_PermBuildSmFriendly( Openc_Man_t * p, Gia_Man_t * pOrig, int nOpt, int fDelayOpt, Openc_PermCost_t * pCost )
{
    if ( p->nOps < 1 )
        return NULL;
    return Openc_PermBuildArith( p, pOrig, p->pOps[0].nBound - 1, nOpt, fDelayOpt, pCost );
}

static void Openc_PrintGateReport( const char * pTag, int nEncWidth, int nEncAnd, int nEncLev,
    int nMixWidth, int nMixAnd, int nMixLev, int nMixRawAnd, int nAllAnd, int fSumOk );

static void Openc_PermPrintCost( char * pName, Openc_PermCost_t * pCost, int * pPerm, int nM, int nBound, int nOps, int fShared )
{
    int fSumOk = (pCost->nAllAnds == pCost->nEncAnds + pCost->nMixAnds);
    Openc_PrintGateReport( pName, nBound * nOps, pCost->nEncAnds, pCost->nEncLev,
        nBound * nOps, pCost->nMixAnds, pCost->nMixLev, pCost->nMixAndsRaw,
        pCost->nAllAnds, fSumOk );
    Abc_Print( 1, "    verify: %s  [enc FREE / mix COST]\n", pCost->fOk ? "equivalent" : "FAILED" );
    if ( pPerm )
        Openc_PrintPermLine( "encoding", pPerm, nM, nBound );
    (void)nOps;
    (void)fShared;
}

static void Openc_PermExplainVsSm( int * pPerm, int nBound, int nOps, int fShared )
{
    int nM = 1 << nBound, * pSm, ham, eqBits;
    pSm = ABC_ALLOC( int, nM );
    Openc_PermSm( pSm, nBound );
    ham    = Openc_PermHamming( pPerm, pSm, nM );
    eqBits = Openc_PermBitRewriteEq( pPerm, pSm, nBound );
    (void)nOps;
    if ( nBound <= 2 && Openc_PermEq(pSm, pPerm, nM) )
        Abc_Print( 1, "  vs SM:            identical (2-bit sign-magnitude coincides with two's complement)\n" );
    else
        Abc_Print( 1, "  vs SM:            Hamming = %d / %d   bit-perm+xor equivalent = %s   shared = %s\n",
            ham, nM, eqBits ? "yes" : "no", fShared ? "yes" : "independent" );
    if ( eqBits && ham )
        Abc_Print( 1, "  vs SM:            same encoding up to mixer-PI bit permutation and/or complement\n" );
    ABC_FREE( pSm );
    (void)nOps;
}

static int Openc_PermTakeTop( Openc_PermCand_t * pTop, int nTop, int * pAll, int nInts, int nRaw, int nDc2 )
{
    int i, worst = -1;
    for ( i = 0; i < nTop; i++ )
        if ( !pTop[i].fUsed )
        {
            worst = i;
            break;
        }
    if ( worst < 0 )
    {
        worst = 0;
        for ( i = 1; i < nTop; i++ )
            if ( pTop[i].nMixAndsRaw > pTop[worst].nMixAndsRaw )
                worst = i;
        if ( nRaw >= pTop[worst].nMixAndsRaw )
            return 0;
    }
    if ( pTop[worst].pPerms == NULL )
        pTop[worst].pPerms = ABC_ALLOC( int, nInts );
    Openc_PermCopy( pTop[worst].pPerms, pAll, nInts );
    pTop[worst].nMixAndsRaw = nRaw;
    pTop[worst].nMixAnds = nDc2;
    pTop[worst].fUsed = 1;
    return 1;
}

static int Openc_PermInnerCost( Openc_Man_t * p, int * pAll, word ** pG, int fInnerDc2, int * pLev )
{
    Openc_InstallPerms( p, pAll );
    return Openc_PermMixCost( p, pG, fInnerDc2, pLev );
}

static void Openc_NoteRaw( int c, int * pMin, int * pMax )
{
    if ( c < *pMin ) *pMin = c;
    if ( c > *pMax ) *pMax = c;
}

static void Openc_PermReportOutcome( int nTc, int nSm, int nSmF, int nBest, int * pBest, int nBound, int fShared, int fStruct, int fArith, char * pTplName )
{
    int nM = 1 << nBound, * pSm, eqBits, ham;
    pSm = ABC_ALLOC( int, nM );
    Openc_PermSm( pSm, nBound );
    ham    = Openc_PermHamming( pBest, pSm, nM );
    eqBits = Openc_PermBitRewriteEq( pBest, pSm, nBound );
    Abc_Print( 1, "\noutcome:\n" );
    if ( fArith )
    {
        Abc_Print( 1, "  mixer objective is jointly (template G, encoding E); encoder AND-count is free.\n" );
        Abc_Print( 1, "  encodings are recovered from F; SM is not a search seed.\n" );
        if ( pTplName && pTplName[0] )
            Abc_Print( 1, "  selected (E,G):   %s  mixer and = %d\n", pTplName, nBest );
        if ( eqBits || ham == 0 )
            Abc_Print( 1, "  encoding:         SM-like (bit-perm+xor equivalent = yes) recovered from F, not seeded.\n" );
        else
            Abc_Print( 1, "  encoding:         not SM-like (Hamming vs SM = %d / %d); typically identity for TC/Booth templates.\n", ham, nM );
        if ( nSmF >= 0 && nBest < nSmF )
            Abc_Print( 1, "  note:             selected template beat the labeled SM-friendly mixer (%d vs %d).\n", nBest, nSmF );
        else if ( nSmF >= 0 && nBest == nSmF )
            Abc_Print( 1, "  note:             selected template matched the labeled SM-friendly mixer AND-count (%d).\n", nSmF );
        if ( nSm > nTc && nSmF >= 0 && nSmF < nTc )
            Abc_Print( 1, "  SM decode+F+syn mixer and = %d: generic &syn2 did not recover the arithmetic structure.\n", nSm );
        Abc_Print( 1, "  costs: TC = %d   SM decode+F = %d   SM-friendly = %d   selected = %d   shared = %s\n",
            nTc, nSm, nSmF, nBest, fShared ? "yes" : "no" );
        ABC_FREE( pSm );
        return;
    }
    if ( fStruct )
    {
        Abc_Print( 1, "  mixer objective is structural (inverse-E + F, then &dc2+&syn2), not Shannon-of-TT.\n" );
        if ( nSmF >= 0 )
        {
            if ( nSmF < nTc )
                Abc_Print( 1, "  SM-friendly: hand arithmetic mixer beat TC under the same synthesis flow (%d vs %d).\n", nSmF, nTc );
            else if ( nSmF == nTc )
                Abc_Print( 1, "  SM-friendly: hand arithmetic mixer matched TC after synthesis (%d).\n", nSmF );
            else
                Abc_Print( 1, "  SM-friendly: hand arithmetic mixer did not beat TC after synthesis (%d vs %d).\n", nSmF, nTc );
            if ( nSm > nTc && nSmF < nTc )
                Abc_Print( 1, "  SM decode+F+syn mixer and = %d: generic synthesis did not recover the SM-friendly structure.\n", nSm );
            else if ( nSm < nTc )
                Abc_Print( 1, "  SM decode+F+syn also beat TC (mixer and = %d).\n", nSm );
            else
                Abc_Print( 1, "  SM decode+F+syn mixer and = %d (not cheaper than TC).\n", nSm );
        }
        if ( nBest < nTc && (eqBits || ham == 0) )
            Abc_Print( 1, "  A — search found an SM-like bijection cheaper than TC under structural synthesis.\n" );
        else if ( nBest < nTc )
            Abc_Print( 1, "  B — search found a cheaper encoding that is not SM (Hamming vs SM = %d).\n", ham );
        else if ( nSm < nTc && nBest > nSm )
            Abc_Print( 1, "  C — SM decode+F is cheaper than TC, but search did not recover it.\n" );
        else
            Abc_Print( 1, "  C — search did not beat TC under this structural mixer cost.\n" );
        if ( nSmF >= 0 )
            Abc_Print( 1, "  costs: TC = %d   SM decode+F = %d   SM-friendly = %d   best search = %d   shared = %s\n",
                nTc, nSm, nSmF, nBest, fShared ? "yes" : "no" );
        else
            Abc_Print( 1, "  costs: TC = %d   SM decode+F = %d   SM-friendly = n/a   best search = %d   shared = %s\n",
                nTc, nSm, nBest, fShared ? "yes" : "no" );
    }
    else if ( nBest < nTc && (eqBits || ham == 0) )
        Abc_Print( 1, "  A — discovered a sign-magnitude-like bijection with a cheaper mixer than two's complement.\n" );
    else if ( nBest < nTc )
        Abc_Print( 1, "  B — discovered a cheaper mixer encoding that is not sign-magnitude (Hamming vs SM = %d).\n", ham );
    else if ( nBest == nTc && nBest < nSm )
        Abc_Print( 1, "  B/C — mixer cost did not beat two's complement; sign-magnitude is not cheaper under this synthesizer.\n" );
    else if ( nSm < nTc && nBest > nSm )
        Abc_Print( 1, "  C — sign-magnitude is cheaper than TC, but search did not recover it (landscape / budget).\n" );
    else if ( nSm >= nTc )
        Abc_Print( 1, "  C — sign-magnitude is not cheaper than TC for a TC-output mixer under Shannon/&dc2; search %s TC.\n",
            nBest < nTc ? "still beat" : "did not beat" );
    else
        Abc_Print( 1, "  C — no mixer improvement over two's complement; SM mixer and = %d, TC mixer and = %d.\n", nSm, nTc );
    if ( !fStruct )
        Abc_Print( 1, "  costs: TC mixer and = %d   SM mixer and = %d   best mixer and = %d   shared = %s\n",
            nTc, nSm, nBest, fShared ? "yes" : "no" );
    ABC_FREE( pSm );
}

static void Openc_ManStop( Openc_Man_t * p );

Gia_Man_t * Gia_ManOpencPermPerform( Gia_Man_t * p, int nWord, int fAreaOpt, int fDelayOpt, int fVerbose, char * pPart, int nMacBits, int nMacTerms, int fShared, int nIters, int nRandom, int nSeed, int fAffine, int fStruct, int fArith )
{
    Openc_Man_t man, * pMan = &man;
    Gia_Man_t * pBestAll = NULL, * pTemp;
    word ** pG = NULL;
    Openc_PermCost_t costTc, costSm, costBest, costRnd, costSmF, costArith, costArithBest;
    Openc_PermCand_t pTop[OPENC_PERM_TOPK];
    int * pAll, * pOne, * pBest, * pSm, * pWork, * pAffBest = NULL, * pArithEnc = NULL;
    int nPis, nPos, nBound = 0, nM, nInts, nWordsG = 0;
    int i, nEvals = 0, nInnerOpt, nVerOpt, nBestRaw, nBestDc2, nAffBest = -1, nRndBest = -1, nRndSum = 0, nRndN = 0;
    int fExhaust = 0, fIndExhaust = 0, kTop, fOkBest = 0, nSmF = -1, nArithAnds = -1, iSignBest = -1, iTplBest = -1;
    int nRawMin = 1 << 30, nRawMax = 0;
    Gia_Man_t * pArithAll = NULL;
    char pTplBest[48];
    unsigned rng;
    abctime clk = Abc_Clock();
    memset( pMan, 0, sizeof(Openc_Man_t) );
    memset( &costTc, 0, sizeof(costTc) );
    memset( &costSm, 0, sizeof(costSm) );
    memset( &costBest, 0, sizeof(costBest) );
    memset( &costRnd, 0, sizeof(costRnd) );
    memset( &costSmF, 0, sizeof(costSmF) );
    memset( &costArith, 0, sizeof(costArith) );
    memset( &costArithBest, 0, sizeof(costArithBest) );
    memset( pTop, 0, sizeof(pTop) );
    pTplBest[0] = 0;
    nPis = Gia_ManPiNum( p );
    nPos = Gia_ManPoNum( p );
    if ( Gia_ManRegNum(p) )
    {
        Abc_Print( -1, "&openc: sequential networks are not supported.\n" );
        return NULL;
    }
    if ( nPis < 1 || nPos < 1 )
    {
        Abc_Print( -1, "&openc -e perm: needs a combinational AIG with at least one PI and PO (got i/o = %d/%d).\n", nPis, nPos );
        return NULL;
    }
    if ( fArith )
        fStruct = 1;
    if ( !fStruct && nPis > OPENC_TT_PI )
    {
        Abc_Print( -1, "&openc -e perm: TT mixer needs 1..%d PIs (got i/o = %d/%d). Use -A for a structural mixer.\n",
            OPENC_TT_PI, nPis, nPos );
        return NULL;
    }
    if ( fStruct && nPis > OPENC_MAX_PI )
    {
        Abc_Print( -1, "&openc -e perm -A: structural mixer supports at most %d PIs (got %d).\n", OPENC_MAX_PI, nPis );
        return NULL;
    }
    if ( nMacBits < 1 )
        nMacBits = nWord;
    if ( nMacTerms < 1 )
        nMacTerms = 1;
    if ( nWord < 1 )
        nWord = nMacBits > 0 ? nMacBits : 1;
    if ( nRandom < 0 )
        nRandom = 0;
    if ( nSeed == 0 )
        nSeed = 1;
    rng = (unsigned)nSeed;
    nVerOpt   = fStruct ? 2 : (fAreaOpt ? 1 : 0);
    nInnerOpt = fStruct ? 1 : 0;
    pMan->pGia     = p;
    pMan->nVars    = nPis;
    pMan->nOuts    = nPos;
    pMan->nWords   = (nPis <= OPENC_TT_PI) ? Abc_Truth6WordNum( nPis ) : 0;
    pMan->fVerbose = fVerbose;
    pMan->fStruct  = fStruct;
    pMan->fSimSat  = 0;
    if ( !fStruct || (fArith && nPis <= OPENC_TT_PI) )
    {
        pMan->pOuts = Openc_AllocTts( nPos, pMan->nWords );
        if ( !Openc_ExtractTruths(p, pMan->pOuts, nPos, pMan->nWords) )
        {
            Abc_Print( -1, "&openc -e perm: failed to extract specification truth tables.\n" );
            Openc_ManStop( pMan );
            return NULL;
        }
    }
    if ( !Openc_FillPartition( pMan, pPart, nWord, nMacBits, nMacTerms ) )
    {
        Openc_ManStop( pMan );
        return NULL;
    }
    if ( !Openc_OpsUniform(pMan, &nBound) )
    {
        Abc_Print( -1, "&openc -e perm: all bound sets must have the same width in 1..%d.\n", OPENC_PERM_BOUND );
        Openc_ManStop( pMan );
        return NULL;
    }
    nM    = 1 << nBound;
    nInts = pMan->nOps * nM;
    pAll  = ABC_ALLOC( int, nInts );
    pOne  = ABC_ALLOC( int, nM );
    pBest = ABC_ALLOC( int, nInts );
    pSm   = ABC_ALLOC( int, nM );
    pWork = ABC_ALLOC( int, nInts );
    if ( !fStruct )
    {
        nWordsG = Abc_Truth6WordNum( Abc_MaxInt(nPis, 1) );
        pG = Openc_AllocTts( nPos, nWordsG );
    }

    Abc_Print( 1, "\n" );
    Abc_Print( 1, "Bijective operand encoding search (encoder FREE / mixer COST)\n" );
    Abc_Print( 1, "-------------------------------------------------------------\n" );
    Abc_Print( 1, "spec:      i/o = %d/%d  groups = %d  width = %d  minterms/op = %d  (no class merging)\n",
        nPis, nPos, pMan->nOps, nBound, nM );
    Abc_Print( 1, "partition: %s\n", pMan->pPartName[0] ? pMan->pPartName : "consec" );
    if ( fStruct )
    {
        Abc_Print( 1, "model:     %s permutation; mixer = inverse-E + structural F (decoder is a spec, not the cost)\n",
            fShared ? "shared" : "independent" );
        Abc_Print( 1, "objective: mixer AND-count after &dc2+&syn2 (inner search uses &dc2 only)\n" );
        Abc_Print( 1, "note:      SM-friendly mul is a labeled arithmetic template, not a search seed\n" );
        if ( fArith )
            Abc_Print( 1, "note:      -T jointly selects mixer template G and recovers encoding E from F; encodings are not seeds\n" );
    }
    else
    {
        Abc_Print( 1, "model:     %s permutation; mixer synthesized from encoded truth table (not decoder+F)\n",
            fShared ? "shared" : "independent" );
        Abc_Print( 1, "objective: mixer AND-count after%s Shannon construction\n", fAreaOpt ? " &dc2 of" : "" );
    }
    if ( nPis > OPENC_PERM_SEARCH_PI )
        Abc_Print( 1, "note:      %d mixer PIs: iterative search is skipped; references only.\n", nPis );

    /* --- references: TC (identity) and sign-magnitude (not used as a search seed) --- */
    Openc_PermIdent( pOne, nM );
    Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
    Openc_InstallPerms( pMan, pAll );
    pTemp = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costTc );
    Gia_ManStop( pTemp );
    nEvals++;
    Openc_PermPrintCost( "TC (identity)", &costTc, pOne, nM, nBound, pMan->nOps, 1 );
    if ( !costTc.fOk )
        Abc_Print( -1, "&openc -e perm: identity encoding failed CEC/TT verification.\n" );

    Openc_PermSm( pSm, nBound );
    Openc_PermFillShared( pAll, pMan->nOps, pSm, nM );
    Openc_InstallPerms( pMan, pAll );
    pTemp = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costSm );
    Gia_ManStop( pTemp );
    nEvals++;
    Openc_PermPrintCost( "SM decode+F", &costSm, pSm, nM, nBound, pMan->nOps, 1 );
    Openc_PermExplainVsSm( pSm, nBound, pMan->nOps, 1 );
    if ( !costSm.fOk )
        Abc_Print( -1, "&openc -e perm: sign-magnitude encoding failed verification.\n" );
    Openc_NoteRaw( costTc.nMixAndsRaw, &nRawMin, &nRawMax );
    Openc_NoteRaw( costSm.nMixAndsRaw, &nRawMin, &nRawMax );

    /* bitwise complement is the 3-bit exhaustive winner; evaluate as a reference, not a search seed */
    {
        Openc_PermCost_t costNot;
        for ( i = 0; i < nM; i++ )
            pOne[i] = i ^ (nM - 1);
        Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
        Openc_InstallPerms( pMan, pAll );
        pTemp = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costNot );
        Gia_ManStop( pTemp );
        nEvals++;
        Openc_PermPrintCost( "bit-complement", &costNot, pOne, nM, nBound, pMan->nOps, 1 );
        Openc_NoteRaw( costNot.nMixAndsRaw, &nRawMin, &nRawMax );
    }

    if ( fStruct )
    {
        Openc_PermSm( pSm, nBound );
        Openc_PermFillShared( pAll, pMan->nOps, pSm, nM );
        Openc_InstallPerms( pMan, pAll );
        pTemp = Openc_PermBuildSmFriendly( pMan, p, nVerOpt, fDelayOpt, &costSmF );
        nEvals++;
        if ( pTemp == NULL )
            Abc_Print( 1, "  SM-friendly mul:   skipped (need an even number of equal-width operands)\n" );
        else
        {
            Openc_PermPrintCost( "SM-friendly mul", &costSmF, pSm, nM, nBound, pMan->nOps, 1 );
            Abc_Print( 1, "  SM-friendly:       hand mag-mul + sign-xor + TC convert; not used as a search seed\n" );
            if ( !costSmF.fOk )
                Abc_Print( -1, "&openc -e perm: SM-friendly mixer failed verification; discarded as a reference.\n" );
            else
                nSmF = costSmF.nMixAnds;
            Gia_ManStop( pTemp );
        }
    }

    if ( fArith )
    {
        int s, j, t, nMixPi, nJob, nTerms, pKind[64], pSign[64], * pDisc, * pEterm = NULL, * pSmLikeEnc = NULL;
        int fReuseBest = -1, fIndEqBest = -1, fPartialCec = -1, iSmKind = -1, iSmSign = -1, nIndSame = 0;
        Abc_Print( 1, "\njoint arithmetic-template + encoding search (encodings are not seeds)\n" );
        Abc_Print( 1, "  library: tc_array, unsigned, booth4, booth4_uns, sm_mag[s], sm_booth[s]\n" );
        Abc_Print( 1, "           each template accumulates per-term products (MAC / signed dot product)\n" );
        Abc_Print( 1, "  recover: shared E from F(1,y,0,...,0)=y; extra terms at TC 0; synthesize mixer G only\n" );
        Abc_Print( 1, "  score:   mixer AND-count after &dc2+&syn2; encoder AND/lev reported and excluded\n" );
        nTerms = pMan->nOps / 2;
        Abc_Print( 1, "  spec:    %d-term  %d-bit  operands = %d  mixer PIs = %d\n",
            nTerms, nBound, pMan->nOps, nPis );
        if ( pMan->nOps < 2 || (pMan->nOps & 1) )
            Abc_Print( 1, "  skipped: need an even number of equal-width operands (got %d groups)\n", pMan->nOps );
        else if ( !Openc_AllConsecEqual(pMan) || pMan->pOps[0].pPis[0] != 0 )
            Abc_Print( 1, "  skipped: need consecutive operands starting at PI 0\n" );
        else
        {
            nMixPi = pMan->nOps * nBound;
            nJob = 0;
            pKind[nJob] = OPENC_TPL_TC;       pSign[nJob] = -1; nJob++;
            pKind[nJob] = OPENC_TPL_UNS;      pSign[nJob] = -1; nJob++;
            pKind[nJob] = OPENC_TPL_BOOTH;    pSign[nJob] = -1; nJob++;
            pKind[nJob] = OPENC_TPL_BOOTHUNS; pSign[nJob] = -1; nJob++;
            for ( s = 0; s < nBound; s++ )
            {
                pKind[nJob] = OPENC_TPL_SM; pSign[nJob] = s; nJob++;
            }
            for ( s = 0; s < nBound; s++ )
            {
                pKind[nJob] = OPENC_TPL_SMBOOTH; pSign[nJob] = s; nJob++;
            }
            Openc_PermIdent( pOne, nM );
            Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
            Openc_InstallPerms( pMan, pAll );
            pDisc = ABC_ALLOC( int, nM );
            for ( j = 0; j < nJob; j++ )
            {
                Gia_Man_t * pGmix;
                int fSolved, fReuse;
                char buf[48];
                Openc_TplName( buf, pKind[j], pSign[j] );
                pGmix = Openc_BuildTplMixer( pMan, pKind[j], pSign[j] );
                if ( pGmix == NULL || Gia_ManPiNum(pGmix) != nMixPi )
                {
                    if ( pGmix )
                        Gia_ManStop( pGmix );
                    Abc_Print( 1, "  %-22s skipped (could not build mixer)\n", buf );
                    continue;
                }
                fSolved = Openc_ArithSolveEncDot( p, pGmix, nBound, pMan->nOps, 0, pDisc );
                nEvals++;
                if ( !fSolved )
                {
                    Abc_Print( 1, "  %-22s no bijection E satisfies G(E(x),E(y),E(0),...)=F(x,y,0,...)\n", buf );
                    Gia_ManStop( pGmix );
                    continue;
                }
                fReuse = Openc_ArithCheckAllTerms( p, pGmix, nBound, pMan->nOps, pDisc );
                Gia_ManStop( pGmix );
                Gia_ManCleanMark0( p );
                Openc_PermFillShared( pAll, pMan->nOps, pDisc, nM );
                Openc_InstallPerms( pMan, pAll );
                pTemp = Openc_PermBuildTpl( pMan, p, pKind[j], pSign[j], nVerOpt, fDelayOpt, &costArith );
                nEvals++;
                if ( pTemp == NULL )
                    continue;
                Openc_PermPrintCost( buf, &costArith, pDisc, nM, nBound, pMan->nOps, 1 );
                Openc_PermExplainVsSm( pDisc, nBound, pMan->nOps, 1 );
                Abc_Print( 1, "  reusable E:        term-0 encoding %s on all %d terms (identity-slice check)\n",
                    fReuse ? "works" : "FAILS", nTerms );
                if ( !costArith.fOk )
                {
                    Abc_Print( -1, "&openc -e perm -T: recovered encoding failed CEC; discarded.\n" );
                    Gia_ManStop( pTemp );
                    continue;
                }
                if ( (pKind[j] == OPENC_TPL_SM || pKind[j] == OPENC_TPL_SMBOOTH) &&
                     Openc_PermBitRewriteEq(pDisc, pSm, nBound) && pSmLikeEnc == NULL )
                {
                    pSmLikeEnc = ABC_ALLOC( int, nM );
                    Openc_PermCopy( pSmLikeEnc, pDisc, nM );
                    iSmKind = pKind[j];
                    iSmSign = pSign[j];
                }
                if ( nArithAnds < 0 || costArith.nMixAnds < nArithAnds )
                {
                    nArithAnds = costArith.nMixAnds;
                    iSignBest = pSign[j];
                    iTplBest = pKind[j];
                    costArithBest = costArith;
                    fReuseBest = fReuse;
                    strcpy( pTplBest, buf );
                    if ( pArithEnc == NULL )
                        pArithEnc = ABC_ALLOC( int, nInts );
                    Openc_PermCopy( pArithEnc, pAll, nInts );
                    if ( pArithAll )
                        Gia_ManStop( pArithAll );
                    pArithAll = pTemp;
                }
                else
                    Gia_ManStop( pTemp );
            }
            ABC_FREE( pDisc );
            if ( nArithAnds >= 0 )
            {
                Abc_Print( 1, "  selected:            %s   mixer and = %d   (encoder FREE; kind = %d sign-bit = %d)\n",
                    pTplBest, nArithAnds, iTplBest, iSignBest );
                Abc_Print( 1, "\nshared vs independent E (selected template; encodings are not seeds)\n" );
                Abc_Print( 1, "  shared:              one E copied to all %d operands; mixer and = %d; CEC = equivalent\n",
                    pMan->nOps, nArithAnds );
                if ( nTerms >= 2 )
                {
                    Openc_PermCost_t costPart;
                    int fSelIdent;
                    Openc_PermIdent( pOne, nM );
                    fSelIdent = Openc_PermEq( pArithEnc, pOne, nM );
                    Openc_PermFillFirstPair( pAll, pMan->nOps, pArithEnc, nM );
                    Openc_InstallPerms( pMan, pAll );
                    pTemp = Openc_PermBuildTpl( pMan, p, iTplBest, iSignBest, 0, 0, &costPart );
                    nEvals++;
                    fPartialCec = (pTemp && costPart.fOk);
                    Abc_Print( 1, "  first-pair only:     selected E on (a0,b0), identity elsewhere; CEC = %s%s\n",
                        fPartialCec ? "equivalent" : "FAILED",
                        fSelIdent ? " (selected E is identity)" : "" );
                    if ( !fPartialCec )
                        Abc_Print( 1, "  first-pair only:     encoding must be reused on every operand\n" );
                    if ( pTemp )
                        Gia_ManStop( pTemp );
                    if ( fSelIdent && pSmLikeEnc && iSmKind >= 0 )
                    {
                        Openc_PermFillFirstPair( pAll, pMan->nOps, pSmLikeEnc, nM );
                        Openc_InstallPerms( pMan, pAll );
                        pTemp = Openc_PermBuildTpl( pMan, p, iSmKind, iSmSign, 0, 0, &costPart );
                        nEvals++;
                        Abc_Print( 1, "  first-pair SM-like:  recovered SM-equivalent E on (a0,b0) only; CEC = %s\n",
                            (pTemp && costPart.fOk) ? "equivalent" : "FAILED" );
                        if ( !(pTemp && costPart.fOk) )
                            Abc_Print( 1, "  first-pair SM-like:  a non-identity E must be reused on every operand\n" );
                        if ( pTemp )
                            Gia_ManStop( pTemp );
                    }
                }
                pEterm = ABC_ALLOC( int, nTerms * nM );
                {
                    Gia_Man_t * pGmix;
                    int nSame = 0;
                    Openc_PermIdent( pOne, nM );
                    Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
                    Openc_InstallPerms( pMan, pAll );
                    pGmix = Openc_BuildTplMixer( pMan, iTplBest, iSignBest );
                    fIndEqBest = 1;
                    for ( t = 0; t < nTerms && pGmix; t++ )
                    {
                        if ( !Openc_ArithSolveEncDot(p, pGmix, nBound, pMan->nOps, t, pEterm + t * nM) )
                        {
                            fIndEqBest = 0;
                            Abc_Print( 1, "  independent:         term %d: no bijection E\n", t );
                            continue;
                        }
                        if ( Openc_PermEq(pEterm + t * nM, pArithEnc, nM) )
                            nSame++;
                        else
                            fIndEqBest = 0;
                    }
                    if ( pGmix )
                        Gia_ManStop( pGmix );
                    Gia_ManCleanMark0( p );
                    Abc_Print( 1, "  independent:         per-term recovered E equals shared E for %d / %d terms\n",
                        nSame, nTerms );
                    nIndSame = nSame;
                    if ( fIndEqBest )
                        Abc_Print( 1, "  independent:         all terms recover the same E; mixer and is unchanged (%d)\n",
                            nArithAnds );
                    else if ( nTerms >= 2 )
                    {
                        Openc_PermCost_t costInd;
                        for ( t = 0; t < nTerms; t++ )
                        {
                            Openc_PermCopy( pAll + (2 * t) * nM, pEterm + t * nM, nM );
                            Openc_PermCopy( pAll + (2 * t + 1) * nM, pEterm + t * nM, nM );
                        }
                        Openc_InstallPerms( pMan, pAll );
                        pTemp = Openc_PermBuildTpl( pMan, p, iTplBest, iSignBest, nVerOpt, fDelayOpt, &costInd );
                        nEvals++;
                        if ( pTemp )
                        {
                            Openc_PermPrintCost( "independent E", &costInd, NULL, nM, nBound, pMan->nOps, 0 );
                            Abc_Print( 1, "  independent:         mixer and = %d (template G is the same circuit; encoder FREE)\n",
                                costInd.nMixAnds );
                            Gia_ManStop( pTemp );
                        }
                    }
                }
                ABC_FREE( pEterm );
                ABC_FREE( pSmLikeEnc );
                Abc_Print( 1, "\nMAC summary:\n" );
                Abc_Print( 1, "  terms/width/ops = %d / %d / %d\n", nTerms, nBound, pMan->nOps );
                Abc_Print( 1, "  template        = %s\n", pTplBest );
                Openc_PrintPermLine( "recovered E", pArithEnc, nM, nBound );
                Abc_Print( 1, "  encoder         and = %d  lev = %d   [FREE]\n",
                    costArithBest.nEncAnds, costArithBest.nEncLev );
                Abc_Print( 1, "  mixer           and = %d  lev = %d   raw = %d   [COST]  CEC = %s\n",
                    costArithBest.nMixAnds, costArithBest.nMixLev, costArithBest.nMixAndsRaw,
                    costArithBest.fOk ? "equivalent" : "FAILED" );
                Abc_Print( 1, "  TC baseline     and = %d  lev = %d   (identity E, same &dc2+&syn2 flow)\n",
                    costTc.nMixAnds, costTc.nMixLev );
                Abc_Print( 1, "  reusable        term-0 E on all terms = %s; independent match = %d/%d\n",
                    fReuseBest ? "yes" : "no", nIndSame, nTerms );
                (void)fPartialCec;
            }
            else
                Abc_Print( 1, "  selected:            no (E,G) pair in the template library matches F\n" );
        }
    }

    if ( fArith )
        Abc_Print( 1, "search:    permutation search skipped; ABC selects among arithmetic mixer templates\n" );
    else
    {
    Openc_PermCopy( pBest, pAll, nInts );
    /* identity as initial best for search (do not seed from SM) */
    Openc_PermIdent( pOne, nM );
    Openc_PermFillShared( pBest, pMan->nOps, pOne, nM );
    Openc_PermIdent( pOne, nM );
    Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
    {
        int nIdentInner = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, NULL );
        nEvals++;
        nBestRaw = nIdentInner;
        nBestDc2 = nIdentInner;
        Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pAll, nInts, nIdentInner, costTc.nMixAnds );
    }
    costBest = costTc;
    fOkBest  = costTc.fOk;

    nInnerOpt = fStruct ? 1 : 0;
    if ( nPis > OPENC_PERM_SEARCH_PI )
        nRandom = 0, nIters = 0, fAffine = 0;
    if ( fStruct && nM > 4 && fShared && nPis <= OPENC_PERM_SEARCH_PI && Openc_FactCapped(nM, 50000) <= 50000 )
        Abc_Print( 1, "search:    skipping %d! exhaustive under structural mixer; hill-climb / SA instead\n", nM );

    /* --- random samples --- */
    for ( i = 0; i < nRandom; i++ )
    {
        int cRaw, cUse, lev = 0;
        if ( fShared )
        {
            Openc_PermShuffle( pOne, nM, &rng );
            Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
        }
        else
        {
            int o;
            for ( o = 0; o < pMan->nOps; o++ )
                Openc_PermShuffle( pAll + o * nM, nM, &rng );
        }
        cRaw = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, &lev );
        nEvals++;
        Openc_NoteRaw( cRaw, &nRawMin, &nRawMax );
        cUse = cRaw;
        nRndSum += cRaw;
        nRndN++;
        if ( nRndBest < 0 || cRaw < nRndBest )
        {
            nRndBest = cRaw;
            Openc_PermCopy( pWork, pAll, nInts );
        }
        Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pAll, nInts, cRaw, cRaw );
        if ( cUse < nBestDc2 )
        {
            nBestDc2 = cUse;
            nBestRaw = cRaw;
            Openc_PermCopy( pBest, pAll, nInts );
        }
        if ( fVerbose && (i < 4 || i == nRandom - 1) )
            Abc_Print( 1, "  random[%d]:        mixer and = %d  lev = %d\n", i, cRaw, lev );
    }
    if ( nRndN )
        Abc_Print( 1, "  random (%d):       best and = %d  mean and = %.1f\n",
            nRndN, nRndBest, (double)nRndSum / nRndN );

    /* --- affine / linear (Model 2); SM is nonlinear for width >= 3 --- */
    if ( fAffine || (nBound <= 3 && !(fShared && nPis <= OPENC_PERM_SEARCH_PI && Openc_FactCapped(nM, 50000) <= 50000)) )
    {
        int nMat = 1 << (nBound * nBound), mat, bias, rows[OPENC_PERM_BOUND], x, nAff = 0;
        if ( nBound <= OPENC_PERM_BOUND && nMat <= (1 << 16) )
        {
            Abc_Print( 1, "affine:    enumerating GL(%d,2) x translations (not seeded from SM)\n", nBound );
            for ( mat = 0; mat < nMat; mat++ )
            {
                for ( i = 0; i < nBound; i++ )
                    rows[i] = (mat >> (i * nBound)) & (nM - 1);
                if ( !Openc_Gf2Invertible(rows, nBound) )
                    continue;
                for ( bias = 0; bias < nM; bias++ )
                {
                    int cRaw;
                    for ( x = 0; x < nM; x++ )
                        pOne[x] = Openc_Gf2Map( rows, bias, x, nBound );
                    if ( !Openc_PermIsBij(pOne, nM) )
                        continue;
                    Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
                    cRaw = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, NULL );
                    nEvals++;
                    nAff++;
                    Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pAll, nInts, cRaw, cRaw );
                    if ( nAffBest < 0 || cRaw < nAffBest )
                    {
                        nAffBest = cRaw;
                        if ( pAffBest == NULL )
                            pAffBest = ABC_ALLOC( int, nInts );
                        Openc_PermCopy( pAffBest, pAll, nInts );
                    }
                    if ( cRaw < nBestDc2 )
                    {
                        nBestDc2 = cRaw;
                        nBestRaw = cRaw;
                        Openc_PermCopy( pBest, pAll, nInts );
                    }
                }
            }
            Abc_Print( 1, "  affine maps:      %d invertible   best mixer and = %d\n", nAff, nAffBest );
            if ( pAffBest )
            {
                Openc_PermExplainVsSm( pAffBest, nBound, pMan->nOps, 1 );
                Openc_PrintPermLine( "best affine", pAffBest, nM, nBound );
            }
        }
    }

    /* --- exhaustive shared S_{2^w} --- */
    if ( fShared && nPis <= OPENC_PERM_SEARCH_PI && Openc_FactCapped(nM, 50000) <= 50000 && !(fStruct && nM > 4) )
    {
        int cRaw;
        fExhaust = 1;
        Openc_PermIdent( pOne, nM );
        Abc_Print( 1, "search:    exhaustive shared %d! encodings\n", nM );
        do
        {
            Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
            cRaw = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, NULL );
            nEvals++;
            Openc_NoteRaw( cRaw, &nRawMin, &nRawMax );
            Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pAll, nInts, cRaw, cRaw );
            if ( cRaw < nBestRaw )
            {
                nBestDc2 = cRaw;
                nBestRaw = cRaw;
                Openc_PermCopy( pBest, pAll, nInts );
            }
            if ( fVerbose && (nEvals % 5000) == 0 )
                Abc_Print( 1, "  ... %d evals, best mixer and = %d\n", nEvals, nBestRaw );
        } while ( Openc_NextPerm(pOne, nM) );
    }
    else if ( !fShared && nBound == 2 && nPis <= OPENC_PERM_SEARCH_PI &&
              Openc_PowCapped(Openc_FactCapped(nM, 1000), pMan->nOps, 100000) <= 100000 )
    {
        /* independent exhaustive for 2-bit operands */
        int * pIdx, o, done, cRaw;
        fIndExhaust = 1;
        pIdx = ABC_ALLOC( int, pMan->nOps * nM );
        for ( o = 0; o < pMan->nOps; o++ )
            Openc_PermIdent( pIdx + o * nM, nM );
        Abc_Print( 1, "search:    exhaustive independent encodings (%d operands, %d! each)\n", pMan->nOps, nM );
        done = 0;
        while ( !done )
        {
            Openc_PermCopy( pAll, pIdx, nInts );
            cRaw = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, NULL );
            nEvals++;
            Openc_NoteRaw( cRaw, &nRawMin, &nRawMax );
            Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pAll, nInts, cRaw, cRaw );
            if ( cRaw < nBestDc2 )
            {
                nBestDc2 = cRaw;
                nBestRaw = cRaw;
                Openc_PermCopy( pBest, pAll, nInts );
            }
            done = 1;
            for ( o = pMan->nOps - 1; o >= 0; o-- )
            {
                if ( Openc_NextPerm(pIdx + o * nM, nM) )
                {
                    done = 0;
                    break;
                }
                Openc_PermIdent( pIdx + o * nM, nM );
            }
        }
        ABC_FREE( pIdx );
    }
    else if ( nPis <= OPENC_PERM_SEARCH_PI )
    {
        int it, a, b, t, cRaw, cCur, nNoImp = 0, op, T, delta;
        if ( nIters <= 0 )
            nIters = fStruct ? ((nM <= 8) ? 200 : 400) : ((nM <= 8) ? 2000 : 4000);
        /* hill-climb from identity (not from SM) */
        Openc_PermIdent( pOne, nM );
        Openc_PermFillShared( pAll, pMan->nOps, pOne, nM );
        Openc_PermCopy( pWork, pAll, nInts );
        cCur = Openc_PermInnerCost( pMan, pWork, pG, nInnerOpt, NULL );
        nEvals++;
        Abc_Print( 1, "search:    hill-climb + simulated annealing (%d iters), neighborhood = transpositions\n", nIters );
        for ( it = 0; it < 64; it++ )
        {
            int bestI = -1, bestJ = -1, bestOp = 0, bestC = cCur;
            int nTryOps = fShared ? 1 : pMan->nOps;
            for ( op = 0; op < nTryOps; op++ )
            {
                int * pP = pWork + op * nM;
                for ( a = 0; a < nM; a++ )
                    for ( b = a + 1; b < nM; b++ )
                    {
                        t = pP[a]; pP[a] = pP[b]; pP[b] = t;
                        if ( fShared )
                            Openc_PermFillShared( pAll, pMan->nOps, pP, nM );
                        else
                            Openc_PermCopy( pAll, pWork, nInts );
                        cRaw = Openc_PermInnerCost( pMan, pAll, pG, nInnerOpt, NULL );
                        nEvals++;
                        if ( cRaw < bestC )
                        {
                            bestC = cRaw; bestI = a; bestJ = b; bestOp = op;
                        }
                        t = pP[a]; pP[a] = pP[b]; pP[b] = t;
                    }
            }
            if ( bestI < 0 )
                break;
            {
                int * pP = pWork + bestOp * nM;
                t = pP[bestI]; pP[bestI] = pP[bestJ]; pP[bestJ] = t;
            }
            if ( fShared )
                Openc_PermFillShared( pWork, pMan->nOps, pWork, nM );
            cCur = bestC;
            Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pWork, nInts, cCur, cCur );
            if ( cCur < nBestDc2 )
            {
                nBestDc2 = cCur;
                nBestRaw = cCur;
                Openc_PermCopy( pBest, pWork, nInts );
            }
        }
        /* SA from identity and from best-so-far */
        for ( kTop = 0; kTop < 2; kTop++ )
        {
            if ( kTop == 0 )
            {
                Openc_PermIdent( pOne, nM );
                Openc_PermFillShared( pWork, pMan->nOps, pOne, nM );
            }
            else
                Openc_PermCopy( pWork, pBest, nInts );
            cCur = Openc_PermInnerCost( pMan, pWork, pG, nInnerOpt, NULL );
            nEvals++;
            T = Abc_MaxInt( 8, nBestDc2 / 4 + 1 );
            nNoImp = 0;
            for ( it = 0; it < nIters; it++ )
            {
                op = fShared ? 0 : (int)(Openc_LcgNext(&rng) % (unsigned)pMan->nOps);
                a = (int)(Openc_LcgNext(&rng) % (unsigned)nM);
                b = (int)(Openc_LcgNext(&rng) % (unsigned)nM);
                if ( a == b )
                    b = (a + 1) % nM;
                t = pWork[op * nM + a];
                pWork[op * nM + a] = pWork[op * nM + b];
                pWork[op * nM + b] = t;
                if ( fShared )
                    Openc_PermFillShared( pWork, pMan->nOps, pWork, nM );
                cRaw = Openc_PermInnerCost( pMan, pWork, pG, nInnerOpt, NULL );
                nEvals++;
                delta = cRaw - cCur;
                if ( delta <= 0 || (int)(Openc_LcgNext(&rng) % (unsigned)(delta + T + 1)) < T )
                {
                    cCur = cRaw;
                    Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pWork, nInts, cRaw, cRaw );
                    if ( cRaw < nBestDc2 )
                    {
                        nBestDc2 = cRaw;
                        nBestRaw = cRaw;
                        Openc_PermCopy( pBest, pWork, nInts );
                        nNoImp = 0;
                    }
                    else
                        nNoImp++;
                }
                else
                {
                    t = pWork[op * nM + a];
                    pWork[op * nM + a] = pWork[op * nM + b];
                    pWork[op * nM + b] = t;
                    if ( fShared )
                        Openc_PermFillShared( pWork, pMan->nOps, pWork, nM );
                    nNoImp++;
                }
                if ( (it & 63) == 63 && T > 1 )
                    T--;
                if ( nNoImp > 400 && it < nIters - 100 )
                {
                    Openc_PermShuffle( pOne, nM, &rng );
                    Openc_PermFillShared( pWork, pMan->nOps, pOne, nM );
                    cCur = Openc_PermInnerCost( pMan, pWork, pG, nInnerOpt, NULL );
                    nEvals++;
                    nNoImp = 0;
                }
            }
        }
    }

    /* --- re-rank top-k with &dc2 and verify accepted candidates --- */
    Abc_Print( 1, "\naccepted candidates (CEC/TT on each):\n" );
    Openc_PermTakeTop( pTop, OPENC_PERM_TOPK, pBest, nInts, nBestRaw, nBestRaw );
    nBestDc2 = costTc.nMixAnds;
    costBest = costTc;
    fOkBest  = costTc.fOk;
    for ( i = 0; i < OPENC_PERM_TOPK; i++ )
    {
        char buf[32];
        if ( !pTop[i].fUsed || pTop[i].pPerms == NULL )
            continue;
        Openc_InstallPerms( pMan, pTop[i].pPerms );
        pTemp = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costRnd );
        sprintf( buf, "topk[%d]", i );
        Openc_PermPrintCost( buf, &costRnd, fShared ? pTop[i].pPerms : NULL, nM, nBound, pMan->nOps, fShared );
        nEvals++;
        if ( costRnd.fOk && costRnd.nMixAnds < nBestDc2 )
        {
            nBestDc2 = costRnd.nMixAnds;
            nBestRaw = costRnd.nMixAndsRaw;
            Openc_PermCopy( pBest, pTop[i].pPerms, nInts );
            costBest = costRnd;
            fOkBest = costRnd.fOk;
            if ( pBestAll )
                Gia_ManStop( pBestAll );
            pBestAll = pTemp;
        }
        else
            Gia_ManStop( pTemp );
        if ( !costRnd.fOk )
            Abc_Print( -1, "&openc -e perm: candidate %s failed verification; discarded.\n", buf );
    }
    /* always verify the search-best; keep it only if it beats TC after &dc2 */
    Openc_InstallPerms( pMan, pBest );
    pTemp = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costRnd );
    nEvals++;
    if ( !costRnd.fOk )
    {
        Abc_Print( -1, "&openc -e perm: search-best encoding failed verification; discarded.\n" );
        Gia_ManStop( pTemp );
    }
    else if ( costRnd.nMixAnds < nBestDc2 )
    {
        if ( pBestAll )
            Gia_ManStop( pBestAll );
        pBestAll = pTemp;
        nBestDc2 = costRnd.nMixAnds;
        nBestRaw = costRnd.nMixAndsRaw;
        costBest = costRnd;
        fOkBest = 1;
    }
    else
        Gia_ManStop( pTemp );
    } /* !fArith permutation search */
    if ( pBestAll == NULL )
    {
        Openc_PermIdent( pOne, nM );
        Openc_PermFillShared( pBest, pMan->nOps, pOne, nM );
        Openc_InstallPerms( pMan, pBest );
        pBestAll = Openc_PermBuildVerified( pMan, p, pG, nVerOpt, fDelayOpt, &costBest );
        nEvals++;
        fOkBest = costBest.fOk;
        nBestDc2 = costBest.nMixAnds;
        if ( !fOkBest )
        {
            Abc_Print( -1, "&openc -e perm: identity fallback failed verification; leaving the original AIG.\n" );
            Gia_ManStop( pBestAll );
            pBestAll = NULL;
        }
    }

    if ( pArithAll && nArithAnds >= 0 && (pBestAll == NULL || nArithAnds < costBest.nMixAnds) )
    {
        if ( pBestAll )
            Gia_ManStop( pBestAll );
        pBestAll = pArithAll;
        pArithAll = NULL;
        costBest = costArithBest;
        fOkBest = costArithBest.fOk;
        nBestDc2 = costArithBest.nMixAnds;
        if ( pArithEnc )
            Openc_PermCopy( pBest, pArithEnc, nInts );
        Abc_Print( 1, "note:      using recovered %s (mixer and = %d)\n",
            pTplBest[0] ? pTplBest : "arithmetic template", nArithAnds );
    }

    Abc_Print( 1, "\nbest discovered:\n" );
    Openc_PermPrintCost( "best", &costBest, fShared ? pBest : NULL, nM, nBound, pMan->nOps, fShared );
    Openc_PermExplainVsSm( pBest, nBound, pMan->nOps, fShared );
    if ( !fShared )
    {
        for ( i = 0; i < pMan->nOps; i++ )
        {
            char buf[32];
            sprintf( buf, "op%d", i );
            Openc_PrintPermLine( buf, pBest + i * nM, nM, nBound );
        }
    }
    Openc_PermReportOutcome( (fStruct || fAreaOpt) ? costTc.nMixAnds : costTc.nMixAndsRaw,
        (fStruct || fAreaOpt) ? costSm.nMixAnds : costSm.nMixAndsRaw,
        nSmF,
        (fStruct || fAreaOpt) ? costBest.nMixAnds : costBest.nMixAndsRaw,
        pBest, nBound, fShared, fStruct, fArith, pTplBest );
    Abc_Print( 1, "evals:     %d   exhaustive = %s   affine = %s   mixer AND range = %d .. %d\n",
        nEvals, (fExhaust || fIndExhaust) ? "yes" : "no", (nAffBest >= 0) ? "yes" : "no",
        nRawMin > nRawMax ? 0 : nRawMin, nRawMax );
    Abc_Print( 1, "note:      encoder AND/lev is reported and excluded from the objective.\n" );
    if ( fStruct )
        Abc_Print( 1, "scale:     structural mixer supports <= %d PIs; search skipped above %d PIs.\n",
            OPENC_MAX_PI, OPENC_PERM_SEARCH_PI );
    else
        Abc_Print( 1, "scale:     TT mixer construction supports <= %d PIs; 4-bit 20-operand MAC does not fit.\n", OPENC_TT_PI );
    Abc_PrintTime( 1, "runtime", Abc_Clock() - clk );
    Abc_Print( 1, "\n" );

    for ( i = 0; i < OPENC_PERM_TOPK; i++ )
        ABC_FREE( pTop[i].pPerms );
    ABC_FREE( pAll );
    ABC_FREE( pOne );
    ABC_FREE( pBest );
    ABC_FREE( pSm );
    ABC_FREE( pWork );
    ABC_FREE( pAffBest );
    ABC_FREE( pArithEnc );
    if ( pArithAll )
        Gia_ManStop( pArithAll );
    Openc_FreeTts( pG, nPos );
    Openc_ManStop( pMan );
    if ( pBestAll == NULL || !fOkBest )
        return NULL;
    return pBestAll;
}


////////////////////////////////////////////////////////////////////////
///                     DRIVER                                       ///
////////////////////////////////////////////////////////////////////////

static void Openc_ManStop( Openc_Man_t * p )
{
    int i;
    Openc_FreeTts( p->pOuts, p->nOuts );
    for ( i = 0; i < p->nOps; i++ )
        Openc_OpFree( p->pOps + i );
}

static void Openc_PrintClassSummary( Openc_Man_t * p )
{
    int i, nId = 0, nDer = 0, nMint, nCls;
    char buf[96];
    Abc_Print( 1, "partition: %s  groups = %d\n", p->pPartName[0] ? p->pPartName : "consec", p->nOps );
    for ( i = 0; i < p->nOps; i++ )
    {
        if ( p->pOps[i].fIdentity )
            nId++;
        else
            nDer++;
    }
    Abc_Print( 1, "encoding:  identity %d / derived %d\n", nId, nDer );
    if ( p->nOps <= 24 || p->fVerbose || nDer > 0 )
    {
        for ( i = 0; i < p->nOps; i++ )
        {
            if ( !p->fVerbose && nDer > 0 && p->pOps[i].fIdentity && p->nOps > 24 )
                continue;
            Openc_FmtBound( p->pOps + i, buf, sizeof(buf) );
            nMint = 1 << p->pOps[i].nBound;
            nCls  = p->pOps[i].nClasses;
            Abc_Print( 1, "  %s  %d minterms -> %d classes -> %d enc bits  %s\n",
                buf, nMint, nCls, p->pOps[i].nEnc,
                p->pOps[i].fIdentity ? "(identity)" : "(derived)" );
        }
    }
    else
        Abc_Print( 1, "  (all groups identity; pass -v to list them)\n" );
}

static void Openc_PrintGateReport( const char * pTag, int nEncWidth, int nEncAnd, int nEncLev,
    int nMixWidth, int nMixAnd, int nMixLev, int nMixRawAnd, int nAllAnd, int fSumOk )
{
    Abc_Print( 1, "  gate counts [%s]:\n", pTag ? pTag : "candidate" );
    Abc_Print( 1, "    encoder:\n" );
    Abc_Print( 1, "        physical width: %d\n", nEncWidth );
    Abc_Print( 1, "        ANDs: %d\n", nEncAnd );
    Abc_Print( 1, "        depth: %d\n", nEncLev );
    Abc_Print( 1, "    mixer:\n" );
    Abc_Print( 1, "        input width: %d\n", nMixWidth );
    Abc_Print( 1, "        ANDs: %d\n", nMixAnd );
    Abc_Print( 1, "        depth: %d\n", nMixLev );
    if ( nMixRawAnd != nMixAnd )
        Abc_Print( 1, "        raw ANDs: %d\n", nMixRawAnd );
    Abc_Print( 1, "    combined:\n" );
    Abc_Print( 1, "        ANDs: %d  (enc %d + mix %d%s)\n",
        nAllAnd, nEncAnd, nMixAnd, fSumOk ? "; stitched sum OK" : "; stitched sum MISMATCH" );
}

static void Openc_PrintReport( Gia_Man_t * pOrig, Gia_Man_t * pEnc, Gia_Man_t * pMix, Gia_Man_t * pAll, Openc_Man_t * p, int fOk, abctime clk )
{
    int nEncAnds, nMixAnds, nAllAnds, nEncLev, nMixLev, nAllLev, nOrigAnds, nOrigLev, fSumOk;
    nOrigAnds = Gia_ManAndNotBufNum( pOrig );
    nOrigLev  = Gia_ManLevelNum( pOrig );
    Abc_Print( 1, "\n" );
    Abc_Print( 1, "Operand-local encoder discovery (free encoder / cost mixer)\n" );
    Abc_Print( 1, "-----------------------------------------------------------\n" );
    Abc_Print( 1, "method:    %s\n", p->fSimSat ? "simulation + SAT column equivalence" : "truth-table column enumeration" );
    Abc_Print( 1, "original:  and = %d  lev = %d  i/o = %d/%d\n",
        nOrigAnds, nOrigLev, Gia_ManPiNum(pOrig), Gia_ManPoNum(pOrig) );
    Openc_PrintClassSummary( p );
    if ( p->fSimSat )
        Abc_Print( 1, "sim/SAT:   words = %d  SAT calls = %d  eq = %d  neq = %d  undef = %d\n",
            p->nSimWords, p->nSatCalls, p->nSatEq, p->nSatNeq, p->nSatUndef );
    if ( pEnc == NULL || pMix == NULL || pAll == NULL )
    {
        Abc_Print( 1, "mode:      cluster-only (no mixer synthesis)\n" );
        Abc_PrintTime( 1, "runtime", clk );
        Abc_Print( 1, "\n" );
        return;
    }
    nEncAnds  = Gia_ManAndNotBufNum( pEnc );
    nEncLev   = Gia_ManLevelNum( pEnc );
    nMixAnds  = Gia_ManAndNotBufNum( pMix );
    nMixLev   = Gia_ManLevelNum( pMix );
    nAllAnds  = Gia_ManAndNotBufNum( pAll );
    nAllLev   = Gia_ManLevelNum( pAll );
    fSumOk    = (nAllAnds == nEncAnds + nMixAnds);
    Openc_PrintGateReport( p->pMixMethod ? p->pMixMethod : "acd", Gia_ManPoNum(pEnc),
        nEncAnds, nEncLev, Gia_ManPiNum(pMix), nMixAnds, nMixLev, nMixAnds, nAllAnds, fSumOk );
    Abc_Print( 1, "    objective: mixer-only and = %d  mixer-only lev = %d  [encoder excluded]\n", nMixAnds, nMixLev );
    Abc_Print( 1, "    verify:    %s\n", fOk ? "equivalent" : "FAILED" );
    Abc_PrintTime( 1, "runtime", clk );
    Abc_Print( 1, "\n" );
}

Gia_Man_t * Gia_ManOpencPerform( Gia_Man_t * p, int nWord, int nMaxEnc, int fOneHot, int fAreaOpt, int fDelayOpt, int fVerbose, int fForceTt, int nSimWords, char * pPart, int nMacBits, int nMacTerms, int fClusterOnly )
{
    Openc_Man_t man, * pMan = &man;
    Gia_Man_t * pEnc = NULL, * pMix = NULL, * pAll = NULL, * pTemp;
    int i, nPis, nPos, fOk;
    abctime clk = Abc_Clock();
    memset( pMan, 0, sizeof(Openc_Man_t) );
    nPis = Gia_ManPiNum( p );
    nPos = Gia_ManPoNum( p );
    if ( Gia_ManRegNum(p) )
    {
        Abc_Print( -1, "&openc: sequential networks are not supported.\n" );
        return NULL;
    }
    if ( nPis < 1 || nPis > OPENC_MAX_PI || nPos < 1 )
    {
        Abc_Print( -1, "&openc: need a combinational AIG with 1..%d PIs and at least one PO (got i/o = %d/%d).\n",
            OPENC_MAX_PI, nPis, nPos );
        return NULL;
    }
    if ( fForceTt && nPis > OPENC_TT_PI )
    {
        Abc_Print( -1, "&openc: truth-table mode supports at most %d PIs (got %d). Drop -t.\n",
            OPENC_TT_PI, nPis );
        return NULL;
    }
    if ( nMaxEnc < 1 || nMaxEnc > OPENC_MAX_ENC )
        nMaxEnc = OPENC_MAX_ENC;
    if ( nSimWords < 1 )
        nSimWords = 8;
    if ( nMacBits < 1 )
        nMacBits = nWord;
    if ( nMacTerms < 1 )
        nMacTerms = 1;
    pMan->pGia     = p;
    pMan->nVars    = nPis;
    pMan->nOuts    = nPos;
    pMan->nWords   = (nPis <= OPENC_TT_PI) ? Abc_Truth6WordNum(nPis) : 0;
    pMan->fOneHot  = fOneHot;
    pMan->nMaxEnc  = nMaxEnc;
    pMan->fVerbose = fVerbose;
    pMan->fSimSat  = !fForceTt;
    pMan->nSimWords = nSimWords;
    pMan->fClusterOnly = fClusterOnly;
    if ( !pMan->fSimSat )
    {
        pMan->pOuts = Openc_AllocTts( nPos, pMan->nWords );
        if ( !Openc_ExtractTruths(p, pMan->pOuts, nPos, pMan->nWords) )
        {
            Abc_Print( -1, "&openc: failed to extract truth tables.\n" );
            Openc_ManStop( pMan );
            return NULL;
        }
    }
    if ( !Openc_FillPartition( pMan, pPart, nWord, nMacBits, nMacTerms ) )
    {
        Openc_ManStop( pMan );
        return NULL;
    }
    pMan->nMixVars = 0;
    for ( i = 0; i < pMan->nOps; i++ )
    {
        char buf[96];
        if ( !Openc_EncodeOperand(pMan, pMan->pOps + i) )
        {
            Openc_ManStop( pMan );
            return NULL;
        }
        pMan->nMixVars += pMan->pOps[i].nEnc;
        if ( fVerbose )
        {
            Openc_FmtBound( pMan->pOps + i, buf, sizeof(buf) );
            Abc_Print( 1, "Operand %d: %s  %d minterms -> %d classes -> %d encoder bits%s\n",
                i, buf, 1 << pMan->pOps[i].nBound,
                pMan->pOps[i].nClasses, pMan->pOps[i].nEnc,
                pMan->pOps[i].fIdentity ? " (identity)" : "" );
        }
    }
    if ( fClusterOnly )
    {
        Openc_PrintReport( p, NULL, NULL, NULL, pMan, 1, Abc_Clock() - clk );
        Openc_ManStop( pMan );
        return Gia_ManDup( p );
    }
    pEnc = Openc_BuildEncoder( pMan, p );
    pMix = Openc_BuildMixerG( pMan, p );
    if ( fAreaOpt )
    {
        if ( pMan->fMixNeedSyn2 )
            pTemp = Gia_ManAigSyn2( pMix, 0, 1, 0, 100, 0, 0, 0 );
        else
            pTemp = Gia_ManCompress2( pMix, 1, 0 );
        if ( pTemp && pTemp != pMix )
        {
            Gia_ManStop( pMix );
            pMix = pTemp;
        }
    }
    if ( fDelayOpt )
    {
        pTemp = Gia_ManBalance( pMix, 0, 0, 0 );
        if ( pTemp && pTemp != pMix )
        {
            Gia_ManStop( pMix );
            pMix = pTemp;
        }
    }
    pAll = Openc_Stitch( pEnc, pMix );
    if ( nPis <= OPENC_TT_PI )
        fOk = Openc_VerifyTt( p, pAll, Abc_Truth6WordNum(nPis) );
    else
        fOk = Openc_VerifyCec( p, pAll );
    Openc_PrintReport( p, pEnc, pMix, pAll, pMan, fOk, Abc_Clock() - clk );
    Gia_ManStop( pEnc );
    Gia_ManStop( pMix );
    Openc_ManStop( pMan );
    if ( !fOk )
    {
        Abc_Print( -1, "&openc: combined circuit is not equivalent; leaving the original AIG.\n" );
        Gia_ManStop( pAll );
        return NULL;
    }
    return pAll;
}

void Gia_ManOpencPrintBaseline( Gia_Man_t * p, int fAreaOpt )
{
    Gia_Man_t * pDup, * pOpt;
    Abc_Print( 1, "baseline original:  and = %d  lev = %d\n",
        Gia_ManAndNotBufNum(p), Gia_ManLevelNum(p) );
    if ( !fAreaOpt )
        return;
    pDup = Gia_ManDup( p );
    pOpt = Gia_ManCompress2( pDup, 1, 0 );
    Gia_ManStop( pDup );
    Abc_Print( 1, "baseline &dc2:      and = %d  lev = %d\n",
        Gia_ManAndNotBufNum(pOpt), Gia_ManLevelNum(pOpt) );
    Gia_ManStop( pOpt );
}

/* Operand-support classification (transitive PI ancestry):
   encoder AND = support from exactly one operand partition;
   mixer AND   = support from two or more operands;
   other AND   = no PI in TFI (constants only). Buffers are excluded (same metric as Gia_ManAndNotBufNum). */
static int Openc_PiSupportOfCi( int iPi, int nOps, int * pLo, int * pHi )
{
    int k, mask = 0;
    for ( k = 0; k < nOps; k++ )
        if ( iPi >= pLo[k] && iPi < pHi[k] )
            mask |= 1 << k;
    return mask;
}

static int Openc_PiSupportPop( int s )
{
    int c = 0;
    while ( s )
    {
        c += s & 1;
        s >>= 1;
    }
    return c;
}

int Gia_ManOpencCountPiSupport( Gia_Man_t * p, int nOps, int * pLo, int * pHi,
    int * pEncAnd, int * pEncAndPerOp, int * pMixAnd, int * pOtherAnd )
{
    Gia_Obj_t * pObj;
    Vec_Int_t * vSup;
    int i, k, nPi, iObj, s, nEnc = 0, nMix = 0, nOther = 0;
    if ( pEncAnd )
        *pEncAnd = 0;
    if ( pMixAnd )
        *pMixAnd = 0;
    if ( pOtherAnd )
        *pOtherAnd = 0;
    if ( pEncAndPerOp && nOps > 0 )
        for ( k = 0; k < nOps; k++ )
            pEncAndPerOp[k] = 0;
    if ( p == NULL || nOps < 1 )
        return 0;
    nPi = Gia_ManPiNum( p );
    for ( k = 0; k < nOps; k++ )
        if ( pLo[k] < 0 || pHi[k] > nPi || pLo[k] >= pHi[k] )
            return 0;
    vSup = Vec_IntStart( Gia_ManObjNum(p) );
    Gia_ManForEachObj( p, pObj, iObj )
    {
        if ( Gia_ObjIsCi(pObj) )
            Vec_IntWriteEntry( vSup, iObj, Openc_PiSupportOfCi( Gia_ObjCioId(pObj), nOps, pLo, pHi ) );
        else if ( Gia_ObjIsAnd(pObj) )
        {
            s = Vec_IntEntry( vSup, Gia_ObjFaninId0p(p, pObj) );
            s |= Vec_IntEntry( vSup, Gia_ObjFaninId1p(p, pObj) );
            if ( Gia_ObjIsMux(p, pObj) )
                s |= Vec_IntEntry( vSup, Gia_ObjFaninId2p(p, pObj) );
            Vec_IntWriteEntry( vSup, iObj, s );
        }
        else if ( Gia_ObjIsBuf(pObj) )
            Vec_IntWriteEntry( vSup, iObj, Vec_IntEntry(vSup, Gia_ObjFaninId0p(p, pObj)) );
    }
    Gia_ManForEachAnd( p, pObj, i )
    {
        int nFans;
        if ( Gia_ObjIsBuf(pObj) )
            continue;
        s = Vec_IntEntry( vSup, Gia_ObjId(p, pObj) );
        nFans = Openc_PiSupportPop( s );
        if ( nFans >= 2 )
            nMix++;
        else if ( nFans == 1 )
        {
            nEnc++;
            if ( pEncAndPerOp && nOps > 0 )
            {
                for ( k = 0; k < nOps; k++ )
                    if ( s == (1 << k) )
                        pEncAndPerOp[k]++;
            }
        }
        else
            nOther++;
    }
    Vec_IntFree( vSup );
    if ( pEncAnd )
        *pEncAnd = nEnc;
    if ( pMixAnd )
        *pMixAnd = nMix;
    if ( pOtherAnd )
        *pOtherAnd = nOther;
    return 1;
}

int Gia_ManOpencCountPiSupport2( Gia_Man_t * p, int iSplit,
    int * pEncAnd, int * pEncA, int * pEncB, int * pMixAnd, int * pOtherAnd )
{
    int Lo[2], Hi[2], Per[2], nEnc, nMix, nOther;
    if ( iSplit < 1 || iSplit >= Gia_ManPiNum(p) )
        return 0;
    Lo[0] = 0;       Hi[0] = iSplit;
    Lo[1] = iSplit;  Hi[1] = Gia_ManPiNum(p);
    if ( !Gia_ManOpencCountPiSupport( p, 2, Lo, Hi, &nEnc, Per, &nMix, &nOther ) )
        return 0;
    if ( pEncAnd )   *pEncAnd   = nEnc;
    if ( pEncA )     *pEncA     = Per[0];
    if ( pEncB )     *pEncB     = Per[1];
    if ( pMixAnd )   *pMixAnd   = nMix;
    if ( pOtherAnd ) *pOtherAnd = nOther;
    return 1;
}

void Gia_ManOpencPrintPiSupportReport( Gia_Man_t * p, int iSplit )
{
    int nEnc, nEncA, nEncB, nMix, nOther, nAll, nSum;
    if ( !Gia_ManOpencCountPiSupport2( p, iSplit, &nEnc, &nEncA, &nEncB, &nMix, &nOther ) )
    {
        Abc_Print( -1, "&openc: PI-support report needs 1 <= split < nPI (got split=%d, nPI=%d).\n",
            iSplit, p ? Gia_ManPiNum(p) : 0 );
        return;
    }
    nAll = Gia_ManAndNotBufNum( p );
    nSum = nEnc + nMix + nOther;
    Abc_Print( 1, "\nPI-support encoder/mixer report (transitive operand ancestry)\n" );
    Abc_Print( 1, "--------------------------------------------------------------\n" );
    Abc_Print( 1, "definition:  encoder = AND nodes whose PI support lies in one operand;\n" );
    Abc_Print( 1, "             mixer   = AND nodes whose PI support spans 2+ operands;\n" );
    Abc_Print( 1, "             other   = AND nodes with no PI in TFI (constants only).\n" );
    Abc_Print( 1, "operand A:   PI[%d .. %d]   (%d PIs)\n", 0, iSplit - 1, iSplit );
    Abc_Print( 1, "operand B:   PI[%d .. %d]   (%d PIs)\n", iSplit, Gia_ManPiNum(p) - 1, Gia_ManPiNum(p) - iSplit );
    Abc_Print( 1, "  encoder:\n" );
    Abc_Print( 1, "      ANDs: %d  (A-only %d, B-only %d)\n", nEnc, nEncA, nEncB );
    Abc_Print( 1, "  mixer:\n" );
    Abc_Print( 1, "      ANDs: %d\n", nMix );
    if ( nOther )
        Abc_Print( 1, "  other (constant-only): ANDs: %d\n", nOther );
    Abc_Print( 1, "  combined:\n" );
    Abc_Print( 1, "      ANDs: %d  (enc %d + mix %d + other %d; total non-buf AND %d%s)\n",
        nEnc + nMix + nOther, nEnc, nMix, nOther, nAll,
        (nSum == nAll) ? "; OK" : "; MISMATCH" );
    Abc_Print( 1, "\n" );
}


ABC_NAMESPACE_IMPL_END
