/* pps.c */
/* plethysm p_I[S_J] in the basis of schur function */

#include "def.h"
#include "macro.h"



INT pps_ende()
{
    INT erg = OK;
    ENDR("pps_ende");
}

extern INT pps_integer_partition_();
extern INT pps_integer_hashtable_();
extern INT pps_integer_integer_();
extern INT pps___();
extern INT tsm___faktor();

INT pps_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}

INT pps_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;
    OP ff,p,z;
    INT i;
    INT mms_hashtable__(), tsm___faktor();

    CTO(INTEGER,"pps_integer__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"pps_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"pps_integer__:integer < 0");
    if (S_I_I(a) == 0) 
        {
        erg += pps_null__(b,c,f);
        goto ende;
        }

    ff = CALLOCOBJECT();
    erg += init_hashtable(ff);
    tsm___faktor(b,ff,f);
    FORALL(z,ff,{
        for (i=0;i<S_PA_LI(S_MO_S(z));i++)
            M_I_I(S_I_I(a)*S_PA_II(S_MO_S(z),i), S_PA_I(S_MO_S(z),i));
        });
    p = CALLOCOBJECT();
    first_partition(cons_null,p);
    mms_hashtable__(ff,p,c,cons_eins);
    
    FREEALL(p);
    FREEALL(ff);
ende:
    CTTO(HASHTABLE,SCHUR,"pps_integer__(3-end)",c);
    ENDR("pps_integer__");
}

INT pps_null_partition_();

INT pps_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"pps_partition__(1)",a);
    CTTTO(HASHTABLE,SCHUR,PARTITION,"pps_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += pps_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += pps_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        INT mss_hashtable_hashtable_();
        INT p_splitpart();
        erg += p_splitpart(a,b,c,f,pps_partition__,
                                   mss_hashtable_hashtable_);
        }
    CTTO(HASHTABLE,SCHUR,"pps_partition__(3-end)",c); 
    ENDR("pps_partition__");
}



INT pps_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [s_b]  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"pps_powsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pps_powsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps_powsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pps_partition__);
    ENDR("pps_powsym__");
}

INT pps_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [s_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pps_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pps_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pps_partition__);
    ENDR("pps_hashtable__");
}

INT pps_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [s_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pps_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"pps_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps_hashtable_hashtable_(3)",c);
    NYI("pps_hashtable_hashtable_");
    ENDR("pps_hashtable_hashtable_");
}

INT pps_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"pps_null_partition(1)",b);
    CTTO(SCHUR,HASHTABLE,"pps_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("pps_null_partition");
}

INT plet_powsym_schur(a,b,c) OP a,b,c;
/* AK 051201
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->POWSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"plet_powsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_powsym_schur(3)",c);

    if (S_O_K(c) == EMPTY) 
        { t=1; init_hashtable(c); }

    pps___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_SCHUR(c,c);
    ENDR("plet_powsym_schur");
}

INT pps___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"pps___(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"pps___(2)",b);
    CTTO(HASHTABLE,SCHUR,"pps___(3)",c);
    if (S_O_K(b) == INTEGER) /* AK 090703 */
        {
        OP d = CALLOCOBJECT();
        erg += m_i_pa(b,d);
        erg += pps___(a,d,c,f);
        FREEALL(d);
        }
    else if (S_O_K(a) == INTEGER)
        {
        erg += pps_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += pps_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += pps_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += pps_hashtable__(a,b,c,f);
        }
 
    ENDR("pps___");
}

INT plet_powsym_schur_via_ppm(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"plet_powsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_powsym_schur(3)",c);
 
/*
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    pse___(a,b,c,cons_eins);
*/
    {
    /* via ppm with change of basis */
    OP f = CALLOCOBJECT();
    OP d = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += init_hashtable(d);
    erg += tsm___faktor(b,f,cons_eins);
    erg += ppm___(a,f,d,cons_eins);
    FREEALL(f);
    erg += t_MONOMIAL_SCHUR(d,c,cons_eins);
    FREEALL(d);
    }
/*
    if (t==1) t_HASHTABLE_SCHUR(c,c);
*/
    ENDR("plet_powsym_schur");
}


