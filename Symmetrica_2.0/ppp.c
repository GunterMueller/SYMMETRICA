
#include "def.h"
#include "macro.h"

INT ppp_ende()
{
    return OK;
}

INT m_merge_partition_partition();
INT ppp_integer_partition_();
INT ppp_integer_hashtable_();
INT ppp___();
INT mpp_hashtable_hashtable_();
INT ppp_null_partition_();
INT p_splitpart();
INT mxx_null__();

INT ppp_null__(b,c,f) OP b,c,f;
{
    return mxx_null__(b,c,f);
}

INT ppp_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"ppp_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"ppp_integer__(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"ppp_integer__:integer < 0");
    if (S_I_I(a) == 0) 
        erg += ppp_null__(b,c,f);
    

    if (S_O_K(b) == PARTITION)
        erg += ppp_integer_partition_(a,b,c,f);
    else
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,ppp_integer_partition_);

    
    ENDR("ppp_integer__");
}


INT ppp_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"ppp_partition__(1)",a);
    CTTTO(HASHTABLE,POWSYM,PARTITION,"ppp_partition__(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += ppp_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += ppp_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        erg += p_splitpart(a,b,c,f,ppp_partition__,
                                   mpp_hashtable_hashtable_);
        }
    
    ENDR("ppp_partition__");
}



INT ppp_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"ppp_powsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"ppp_powsym__(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp_powsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppp_partition__);
    ENDR("ppp_powsym__");
}

INT ppp_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppp_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"ppp_hashtable__(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppp_partition__);
    ENDR("ppp_hashtable__");
}

INT ppp_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppp_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"ppp_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp_hashtable_hashtable_(3)",c);
    NYI("ppp_hashtable_hashtable_");
    ENDR("ppp_hashtable_hashtable_");
}

INT ppp_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"ppp_null_partition(1)",b);
    CTTO(POWSYM,HASHTABLE,"ppp_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("ppp_null_partition");
}

INT ppp_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    OP m;
    INT i;

    CTO(INTEGER,"ppp_integer_partition_(1)",a);
    CTO(PARTITION,"ppp_integer_partition_(2)",b);
    CTTO(POWSYM,HASHTABLE,"ppp_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"ppp_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += ppp_null__(b,c,f);
        goto ende;
        }

    
    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
    erg += m_il_v(S_PA_LI(b),S_PA_S(S_MO_S(m)));
    C_O_K(S_PA_S(S_MO_S(m)),INTEGERVECTOR);
    COPY(f, S_MO_K(m));
    for (i=0;i<S_PA_LI(b);i++)
        M_I_I(S_I_I(a)*S_PA_II(b,i),S_PA_I(S_MO_S(m),i));

    if (S_O_K(c) == POWSYM)
        INSERT_LIST(m,c,add_koeff,comp_monompowsym);
    else
        insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);

ende:
    ENDR("ppp_integer_partition_");
}

INT ppp_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"ppp_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,POWSYM,"ppp_integer_hashtable_(2)",b);
    CTTO(POWSYM,HASHTABLE,"integer_hashtable_(3)",c);

    NYI("ppp_integer_hashtable_");
    
    ENDR("ppp_integer_hashtable_");
}



INT plet_powsym_powsym(a,b,c) OP a,b,c;
/* AK 051201
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->POWSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_powsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"plet_powsym_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"plet_powsym_powsym(3)",c);

    if (S_O_K(c) == EMPTY) 
        if (S_O_K(a) == INTEGER) init_powsym(c);
        else { t=1; init_hashtable(c); }

    ppp___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_POWSYM(c,c);
    ENDR("plet_powsym_powsym");
}

INT ppp___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"ppp___(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"ppp___(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppp___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += ppp_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += ppp_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += ppp_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += ppp_hashtable__(a,b,c,f);
        }
 
    ENDR("ppp___");
}

