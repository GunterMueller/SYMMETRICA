/* 
   symmetric source code
   for the computation of the plethysm
   h_I[S_J]
*/

#include "def.h"
#include "macro.h"

INT plet_homsym_schur(a,b,c) OP a,b,c;
/* AK 051201 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"plet_homsym_schur(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"plet_homsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_homsym_schur(3)",c);
#ifdef PLETTRUE
    {
    INT t=0; /* is 1 if transfer HASHTABLE->SCHUR necessary */

    if (S_O_K(c) == EMPTY) 
        { t=1; init_hashtable(c); }

    phs___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_SCHUR(c,c);
    }
#endif
    ENDR("plet_homsym_schur");
}
INT phs_ende()
{
    INT erg = OK;
    return erg;
}

#ifdef PLETTRUE
INT phs_integer_partition_();
INT phs_integer_hashtable_();
INT phs___();

INT phs_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}

INT phs_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"phs_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,SCHUR,"phs_integer_hashtable_(2)",b);
    CTTO(SCHUR,HASHTABLE,"integer_hashtable_(3)",c);
    NYI("phs_integer_hashtable_");
    
    ENDR("phs_integer_hashtable_");
}

INT phs_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"phs_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"phs_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"phs_integer__(3)",c);

    SYMCHECK((S_I_I(a) < 0) , "phs_integer__:integer<0");

    if (S_I_I(a) == 0) {
        erg += phs_null__(b,c,f);
        }

    else if (S_O_K(b) == PARTITION)
        erg += phs_integer_partition_(a,b,c,f);
    else if (S_O_K(b) == SCHUR)
        {
        INT mss_hashtable_hashtable_();
        INT p_schursum();
        if (S_S_N(b) == NULL) 
            erg += phs_integer_partition_(a,S_S_S(b),c,f);
        else
            erg += p_schursum(a,b,c,f,NULL,phs_integer__,mss_hashtable_hashtable_);
        }
    else
        {
        erg += phs_integer_hashtable_(a,b,c,f);
        }

    
    ENDR("phs_integer__");
}

INT phs_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"phs_partition__(1)",a);
    CTTTO(HASHTABLE,SCHUR,PARTITION,"phs_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"phs_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += phs_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += phs_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else{
        INT p_splitpart();
        INT mss_hashtable_hashtable_();
        erg += p_splitpart(a,b,c,f,phs_partition__,
                                   mss_hashtable_hashtable_);
        goto ende;
        }
    
ende:
    CTTO(HASHTABLE,SCHUR,"phs_partition__(3)",c);
    ENDR("phs_partition__");
}



INT phs_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HOMSYM,"phs_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"phs_homsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"phs_homsym__(3)",c);

    M_FORALL_MONOMIALS_IN_A(a,b,c,f,phs_partition__);

    ENDR("phs_homsym__");
}

INT phs_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"phs_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"phs_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"phs_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,phs_partition__);

    CTTO(HASHTABLE,SCHUR,"phs_hashtable__(3-end)",c);
    ENDR("phs_hashtable__");
}

INT phs_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"phs_null_partition(1)",b);
    CTTO(SCHUR,HASHTABLE,"phs_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("phs_null_partition");
}

INT phs_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    INT cc_plet_phs_integer_partition();

    CTO(INTEGER,"phs_integer_partition_(1)",a);
    CTO(PARTITION,"phs_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"phs_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"phs_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += phs_null_partition_(b,c,f);
        goto ende;
        }

    erg += cc_plet_phs_integer_partition(a,b,c,f);   

ende:
    ENDR("phs_integer_partition_");
}



INT phs___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"phs___(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"phs___(2)",b);
    CTTO(HASHTABLE,SCHUR,"phs___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += phs_integer__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += phs_partition__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == HOMSYM)
        {
        erg += phs_homsym__(a,b,c,f);
        goto ende;
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += phs_hashtable__(a,b,c,f);
        goto ende;
        }
ende:
    CTTO(HASHTABLE,SCHUR,"phs___(3-end)",c);
 
    ENDR("phs___");
}


#endif /* PLETTRUE */
