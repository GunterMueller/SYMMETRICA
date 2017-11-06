#include "def.h"
#include "macro.h"

INT plet_schur_schur(a,b,c) OP a,b,c;
/* AK 061201 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
#ifdef PLETTRUE
  
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"plet_schur_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_schur_schur(3)",c);
 
    {
    INT t=0;
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    pss___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_SCHUR(c,c);
    }
#endif
    ENDR("plet_schur_schur");
}

INT pss_ende() { return OK; }

#ifdef PLETTRUE

INT m_merge_partition_partition();
INT pss_integer_integer_();
INT pss_integer_partition_();
INT pss_integer_hashtable_();
INT pss_partition_partition_();
INT pss_partition_schur_();
INT pss_schur__();
INT mss_hashtable_hashtable_();
INT pss_null_partition_();
INT mxx_null__();

INT pss___();

INT pss_null__(b,c,f) OP b,c,f;
{
    return mxx_null__(b,c,f);
}

INT p_schursum();
INT pss_integer_schur_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(INTEGER,"pss_integer_schur_(1)",a);
    CTO(SCHUR,"pss_integer_schur_(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_integer_schur_(3)",c);
    SYMCHECK((S_I_I(a) < 0) , "pss_integer_schur_:integer < 0");
 
    if (S_I_I(a) == 0) {
        erg += pss_null__(b,c,f);
        goto ende;
        }
    else if (S_S_N(b) == NULL) {
        erg += pss_integer_partition_(a,S_S_S(b),c,f);
        goto ende;
        }
    else  {
        erg += p_schursum(a,b,c,f,NULL,pss_integer_schur_,
                                  mss_hashtable_hashtable_);
        goto ende;
        }
ende:
    ENDR("pss_integer_schur_");
}


INT pss_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;
    CTO(INTEGER,"pss_integer__(1)",a);
    CTTTTO(HASHTABLE,PARTITION,SCHUR,INTEGER,"pss_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0) , "pss_integer__:integer < 0");

    if (S_I_I(a) == 0)
        {
        erg += pss_null__(b,c,f);
        }
    else if (S_O_K(b) == PARTITION)
        {
        erg += pss_integer_partition_(a,b,c,f);
        }
    else if (S_O_K(b) == INTEGER)
        {
        erg += pss_integer_integer_(a,b,c,f);
        }
    else if (S_O_K(b) == SCHUR)
        {
        erg += pss_integer_schur_(a,b,c,f);
        }
    else
        {
         NYI("pss_integer__");
        }
         
    ENDR("pss_integer__");
}

INT pss_partition_schur_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"pss_partition_schur_(1)",a);
    CTO(SCHUR,"pss_partition_schur_(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_partition_schur_(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += pss_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += pss_integer__(S_PA_I(a,0),b,c,f);
        }
    else if (S_S_N(b) == NULL) {
        erg += pss_partition_partition_(a,S_S_S(b),c,f);
        goto ende;
        }
    else {
/*  loop over all partitions smaller then a */
/*  S_a[b1+b2] = \sum_d<a  S_a/d [b1] * S_d[b2] */
        erg += p_schursum(a,b,c,f,pss___,
                                  pss_partition_schur_,
                                  mss_hashtable_hashtable_);
        goto ende;
        }

ende:
    ENDR("pss_partition_schur_");
}
INT pss_partition_hashtable_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"pss_partition_hashtable_(1)",a);
    CTO(HASHTABLE,"pss_partition_hashtable_(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_partition_hashtable_(3)",c);
 
    if (S_PA_LI(a) == 0) {
        erg += pss_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += pss_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else
        {
        NYI("pss_partition_hashtable_");
        }
ende: 
    ENDR("pss_partition_hashtable_");
}


INT pss_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"pss_partition__(1)",a);
    CTTTO(HASHTABLE,SCHUR,PARTITION,"pss_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += pss_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += pss_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        if (S_O_K(b) == PARTITION) {
            erg += pss_partition_partition_(a,b,c,f);
            }
        else if (S_O_K(b) == SCHUR)
            {
            erg += pss_partition_schur_(a,b,c,f);
            }
        else
            {
            erg += pss_partition_hashtable_(a,b,c,f);
            }
        }
    
    ENDR("pss_partition__");
}



INT pss_schur__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(SCHUR,"pss_schur__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pss_schur__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_schur__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pss_partition__);
    ENDR("pss_schur__");
}

INT pss_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pss_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pss_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pss_partition__);
    ENDR("pss_hashtable__");
}

INT pss_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pss_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"pss_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,pss_partition_partition_);
    ENDR("pss_hashtable_hashtable_");
}

INT pss_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"pss_null_partition(1)",b);
    CTTO(SCHUR,HASHTABLE,"pss_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("pss_null_partition");
}

extern INT cc_plet_pss_integer_partition();
INT pss_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"pss_integer_partition_(1)",a);
    CTO(PARTITION,"pss_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"pss_integer_partition_(3)",c);
    

    if (S_I_I(a) == 0) { erg += pss_null_partition_(b,c,f); goto ende; }
    if (S_I_I(a) < 0) { /* zero contributon */ goto ende; }

    erg += cc_plet_pss_integer_partition(a,b,c,f);
ende:
    ENDR("pss_integer_partition_");
}
INT pss_integer_integer_(a,b,c,f) OP a,b,c,f;
/* AK 030603 */
{
    INT erg = OK;

    CTO(INTEGER,"pss_integer_integer_(1)",a);
    CTO(INTEGER,"pss_integer_integer_(2)",b);
    CTTO(SCHUR,HASHTABLE,"pss_integer_integer_(3)",c);
    {
    OP d = CALLOCOBJECT();
    erg += m_i_pa(b,d);
    erg += pss_integer_partition_(a,d,c,f);
    FREEALL(d);
    }

ende:
    ENDR("pss_integer_integer_");
}

INT pss_partition_partition_(a,b,c,f) OP a,b,c,f;
/* AK 071201 */
{
    INT erg = OK;
    INT cc_plet_pss_partition_partition();
 
    CTO(PARTITION,"pss_partition_partition_(1)",a);
    CTO(PARTITION,"pss_partition_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"pss_partition_partition_(3)",c);
    if (S_PA_LI(a) == 0) {
        erg += pss_null_partition_(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += pss_integer_partition_(S_PA_I(a,0),b,c,f);
        }
    else{
        erg += cc_plet_pss_partition_partition(a,b,c,f);
        }
    CTTO(SCHUR,HASHTABLE,"pss_partition_partition_(3-ende)",c);
    ENDR("pss_partition_partition_");
}


INT pss_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"pss_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,SCHUR,"pss_integer_hashtable_(2)",b);
    CTTO(SCHUR,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,pss_integer_partition_);
    
    ENDR("pss_integer_hashtable_");
}


INT pss___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"pss___(1)",a);
    CTTTTO(HASHTABLE,PARTITION,SCHUR,INTEGER,"pss___(2)",b);
    CTTO(HASHTABLE,SCHUR,"pss___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += pss_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += pss_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == SCHUR)
        {
        erg += pss_schur__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += pss_hashtable__(a,b,c,f);
        }
 
    ENDR("pss___");
}




INT phs___();
INT tsh___faktor();
INT plet_schur_schur_via_phs(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"plet_schur_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_schur_schur(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    {
    /* via phs with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tsh___faktor(a,f,cons_eins);
    erg += phs___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_SCHUR(c,c);
    ENDR("plet_schur_schur");
}


#endif /* PLETTRUE */
