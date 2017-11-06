#include "def.h"
#include "macro.h"

INT ppm_ende()
{
    return OK;
}

INT ppm_integer_partition_();
INT ppm_integer_hashtable_();
INT ppm_integer_integer_();
INT ppm___();
INT ppm_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}

INT ppm_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"ppm_integer__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"ppm_integer__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"ppm_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"ppm_integer__:integer < 0");
    if (S_I_I(a) == 0) 
        {
        erg += ppm_null__(b,c,f);
        goto ende;
        }
    else if (S_O_K(b) == PARTITION)
        {
        erg += ppm_integer_partition_(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(b) == INTEGER)
        {
        erg += ppm_integer_integer_(a,b,c,f);
        goto ende;
        }
    else
        {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,ppm_integer_partition_);
        goto ende;
        }

ende:    
    CTTO(HASHTABLE,MONOMIAL,"ppm_integer__(e3)",c);
    ENDR("ppm_integer__");
}

INT ppm_null_partition_();

INT ppm_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"ppm_partition__(1)",a);
    CTTTO(HASHTABLE,MONOMIAL,PARTITION,"ppm_partition__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"ppm_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += ppm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += ppm_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else{
        INT mmm_hashtable_hashtable_();
        INT p_splitpart();
        erg += p_splitpart(a,b,c,f,ppm_partition__,
                                   mmm_hashtable_hashtable_);
        goto ende;
        }
    
ende:
    CTTO(HASHTABLE,MONOMIAL,"ppm_partition__(e3)",c);
    ENDR("ppm_partition__");
}



INT ppm_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"ppm_powsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"ppm_powsym__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"ppm_powsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppm_partition__);
    CTTO(HASHTABLE,MONOMIAL,"ppm_powsym__(e3)",c);
    ENDR("ppm_powsym__");
}

INT ppm_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppm_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"ppm_hashtable__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"ppm_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppm_partition__);
    CTTO(HASHTABLE,MONOMIAL,"ppm_hashtable__(e3)",c);
    ENDR("ppm_hashtable__");
}

INT ppm_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppm_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"ppm_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"ppm_hashtable_hashtable_(3)",c);
    NYI("ppm_hashtable_hashtable_");
    ENDR("ppm_hashtable_hashtable_");
}

INT ppm_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"ppm_null_partition(1)",b);
    CTTO(MONOMIAL,HASHTABLE,"ppm_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("ppm_null_partition");
}

INT ppm_integer_integer_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
 
    CTO(INTEGER,"ppm_integer_integer_(1)",a);
    CTO(INTEGER,"ppm_integer_integer_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"ppm_integer_integer_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"ppm_integer_integer_:integer(1)<0");
    SYMCHECK ((S_I_I(b) < 0),"ppm_integer_integer_:integer(2)<0");
 
    if (S_I_I(a) == 0) {
        erg += ppm_null__(b,c,f);
        goto ende;
        }
    else {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        COPY(f,S_MO_K(m));
        b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
        m_il_integervector(1,S_PA_S(S_MO_S(m)));
        M_I_I(S_I_I(b)*S_I_I(a), S_PA_I(S_MO_S(m),0));

        if (S_O_K(c) == HASHTABLE)
            insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        else
            insert_list(m,c,add_koeff,comp_monommonomial);

        goto ende;
        }


ende:
    CTTO(MONOMIAL,HASHTABLE,"ppm_integer_integer_(3-ende)",c);
    ENDR("ppm_integer_integer_");
}

INT ppm_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"ppm_integer_partition_(1)",a);
    CTO(PARTITION,"ppm_integer_partition_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"ppm_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"ppm_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += ppm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 0) {
        erg += ppm_null__(b,c,f);
        goto ende;
        }
    else {
        OP m;
        INT i;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        COPY(f,S_MO_K(m));
        b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
        m_il_integervector(S_PA_LI(b),S_PA_S(S_MO_S(m)));
        for (i=0;i<S_PA_LI(b);i++)
            M_I_I(S_PA_II(b,i)*S_I_I(a), S_PA_I(S_MO_S(m),i));

        if (S_O_K(c) == HASHTABLE)
            insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        else
            insert_list(m,c,add_koeff,comp_monommonomial);

        goto ende;
        }

    

ende:
    CTTO(MONOMIAL,HASHTABLE,"ppm_integer_partition_(3-ende)",c);
    ENDR("ppm_integer_partition_");
}

INT ppm_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"ppm_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"ppm_integer_hashtable_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,ppm_integer_partition_);
    
    ENDR("ppm_integer_hashtable_");
}



INT plet_powsym_monomial(a,b,c) OP a,b,c;
/* AK 051201
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->POWSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_monomial(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"plet_powsym_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_powsym_monomial(3)",c);

    if (S_O_K(c) == EMPTY) 
        if (S_O_K(a) == INTEGER) init_monomial(c);
        else { t=1; init_hashtable(c); }

    ppm___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("plet_powsym_monomial");
}

INT ppm___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"ppm___(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"ppm___(2)",b);
    CTTO(HASHTABLE,POWSYM,"ppm___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += ppm_integer__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += ppm_partition__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += ppm_powsym__(a,b,c,f);
        goto ende;
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += ppm_hashtable__(a,b,c,f);
        goto ende;
        }
 
ende:
    CTTO(HASHTABLE,POWSYM,"ppm___(e3)",c);
    ENDR("ppm___");
}

