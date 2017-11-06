
#include "def.h"
#include "macro.h"

#ifdef UNDEF
INT psh_partition__();
INT psh_ende()
{
    return OK;
}


INT psh_null__(b,c,f) OP b,c,f;
{
    return mxx_null__(b,c,f);
}
 
INT psh_integer_homsym_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    INT mhh_hashtable_hashtable_();
    CTO(INTEGER,"psh_integer_homsym_(1)",a);
    CTO(HOMSYM,"psh_integer_homsym_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_integer_homsym_(3)",c);
    SYMCHECK((S_I_I(a) < 0) , "psh_integer_homsym_:integer < 0");
 
    if (S_I_I(a) == 0) {
        erg += psh_null__(b,c,f);
        goto ende;
        }
    else if (S_S_N(b) == NULL) {
        erg += psh_integer_partition_(a,S_S_S(b),c,f);
        goto ende;
        }
    else  {
        erg += p_schursum(a,b,c,f,NULL,psh_integer_homsym_,
                                  mhh_hashtable_hashtable_);
        goto ende;
        }
ende:
    ENDR("psh_integer_homsym_");
}
 
 
INT psh_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;
    OP ff;
 
    CTO(INTEGER,"psh_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"psh_integer__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0) , "psh_integer__:integer < 0");
 
    if (S_I_I(a) == 0)
        erg += psh_null__(b,c,f);
    else if (S_O_K(b) == PARTITION)
        erg += psh_integer_partition_(a,b,c,f);
    else if (S_O_K(b) == HOMSYM)
        erg += psh_integer_homsym_(a,b,c,f);
    else
         NYI("psh_integer__");
 
    ENDR("psh_integer__");
}
 


INT psh_schur__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(SCHUR,"psh_schur__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"psh_schur__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_schur__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,psh_partition__);
    ENDR("psh_schur__");
}
 
INT psh_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"psh_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"psh_hashtable__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,psh_partition__);
    ENDR("psh_hashtable__");
}

INT psh_partition_partition_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    INT i,w;
    CTO(PARTITION,"psh_partition_partition_(1)",a);
    CTO(PARTITION,"psh_partition_partition_(2)",b);
    CTO(HASHTABLE,"psh_partition_partition_(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += psh_null__(b,c,f);
        goto ende;
        }
    /* theorem of conjugates */
    for (i=0,w=0;i<S_PA_LI(b);i++) w += S_PA_II(b,i);
    if (w % 2 == 0)
        {
        erg += pse_partition_partition_(a,b,c,f);
        }
    else
        {
        OP p = CALLOCOBJECT();
        conjugate_partition(a,p);
        erg += pse_partition_partition_(p,b,c,f);
        FREEALL(p);
        }
ende:
    ENDR("psh_partition_partition_");
}


INT psh_partition_homsym_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"psh_partition_homsym_(1)",a);
    CTO(HOMSYM,"psh_partition_homsym_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_partition_homsym_(3)",c);
 
    if (S_PA_LI(a) == 0) {
        erg += psh_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += psh_integer__(S_PA_I(a,0),b,c,f);
        }
    else if (S_S_N(b) == NULL) {
        erg += psh_partition_partition_(a,S_S_S(b),c,f);
        goto ende;
        }
    else {
        INT mhh_hashtable_hashtable_();
/*  loop over all partitions smaller then a */
/*  S_a[b1+b2] = \sum_d<a  S_a/d [b1] * S_d[b2] */
        erg += p_schursum(a,b,c,f,psh_schur__,
                                  psh_partition_homsym_,
                                  mhh_hashtable_hashtable_);
        goto ende;
        }
 
ende:
    ENDR("psh_partition_homsym_");
}

INT psh_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"psh_partition__(1)",a);
    CTTTO(HASHTABLE,HOMSYM,PARTITION,"psh_partition__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"psh_partition__(3)",c);
 
    if (S_PA_LI(a) == 0) {
        erg += psh_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += psh_integer__(S_PA_I(a,0),b,c,f);
        }
    else if (S_O_K(b) == PARTITION)
        {
        erg += psh_partition_partition_(a,b,c,f);
        }
    else if (S_O_K(b) == HOMSYM)
        {
        erg += psh_partition_homsym_(a,b,c,f);
        }
    else /* HASHTABLE */
        {
        erg += psh_partition_hashtable_(a,b,c,f);
        }
   
    ENDR("psh_partition__");
}
 
INT psh___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"psh___(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"psh___(2)",b);
    CTTO(HOMSYM,HASHTABLE,"psh___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += psh_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += psh_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == SCHUR)
        {
        erg += psh_schur__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += psh_hashtable__(a,b,c,f);
        }
 
    CTTO(HOMSYM,HASHTABLE,"psh___(3-ende)",c);
    ENDR("psh___");
}
#endif
 

INT tsp___faktor();
INT pph___();

INT plet_schur_homsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_homsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,HOMSYM,"plet_schur_homsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,HOMSYM,"plet_schur_homsym(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    else if (S_O_K(c) == HOMSYM)
         { t=1; t_HOMSYM_HASHTABLE(c); }
/*
    psh___(a,b,c,cons_eins);
*/
    {
    /* via pph with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tsp___faktor(a,f,cons_eins);
    erg += pph___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_HOMSYM(c,c);
    ENDR("plet_schur_homsym");
}


