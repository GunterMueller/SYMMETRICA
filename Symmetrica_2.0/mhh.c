

#include "def.h"
#include "macro.h"

static INT mhh_integer_partition_();
static INT mhh_integer_hashtable_();
static INT mhh_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(INTEGER,"mhh_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mhh_integer__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_integer__(3)",c);

    if (S_O_K(b) == PARTITION) {
        erg += mhh_integer_partition_(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mhh_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    ENDR("mhh_integer__");
}

INT mhh_partition_partition_(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    INT m_merge_partition_partition();
    CTO(PARTITION,"mhh_partition_partition_(1)",a);
    CTO(PARTITION,"mhh_partition_partition_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_partition_partition_(3-start)",c);

    erg += m_merge_partition_partition(a,b,c,f,comp_monomhomsym,eq_monomsymfunc);

    CTTO(HASHTABLE,HOMSYM,"mhh_partition_partition_(3-end)",c);
    ENDR("mhh_partition_partition_");
}

INT mhh_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhh_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mhh_partition__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_partition__(3)",c);

    if (S_O_K(b) == PARTITION)
        {
        erg += mhh_partition_partition_(a,b,c,f);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhh_partition_partition_);
        goto ende;
        }

ende:
    ENDR("mhh_partition__");
}

INT mhh_partition_hashtable_(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhh_partition_hashtable_(1)",a);
    CTO(HASHTABLE,"mhh_partition_hashtable_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_partition_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhh_partition_partition_);
    ENDR("mhh_partition_hashtable_");
}


INT mhh_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HOMSYM,"mhh_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mhh_homsym__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_homsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhh_partition__);    
    ENDR("mhh_homsym__");
}

INT mhh_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times b_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mhh_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mhh_hashtable__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhh_partition__); 
    ENDR("mhh_hashtable__");
}

INT mhh_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += h_a \times h_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mhh_hashtable_hashtable_(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mhh_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"mhh_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mhh_partition_partition_);
    ENDR("mhh_hashtable_hashtable_");
}

static INT mhh_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP m;
    INT i,k;

    CTO(INTEGER,"mhh_integer_partition_(1)",a);
    CTO(PARTITION,"mhh_integer_partition_(2)",b);
    CTTO(HOMSYM,HASHTABLE,"mhh_integer_partition_(3)",c);

    
    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
    erg += m_il_v(S_PA_LI(b)+1,S_PA_S(S_MO_S(m)));
    C_O_K(S_PA_S(S_MO_S(m)),INTEGERVECTOR);

    for (i=0,k=0; k<S_PA_LI(S_MO_S(m)); k++,i++)
        if (k == S_PA_LI(b))
            M_I_I(S_I_I(a), S_PA_I(S_MO_S(m),k) );
        else if (S_PA_II(b,i) < S_I_I(a))  
            M_I_I(S_PA_II(b,i), S_PA_I(S_MO_S(m),k) );
        else 
            {
            M_I_I(S_I_I(a), S_PA_I(S_MO_S(m),k) );
            break;
            }

    for (k++;k<S_PA_LI(S_MO_S(m)); k++,i++)
        M_I_I(S_PA_II(b,i), S_PA_I(S_MO_S(m),k) );

    COPY(f, S_MO_K(m));
    if (S_O_K(c) == HOMSYM)
        INSERT_LIST(m,c,add_koeff,comp_monomhomsym);
    else
        INSERT_HASHTABLE(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);

    ENDR("mhh_integer_partition_");
}

static INT mhh_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"mhh_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,HOMSYM,"mhh_integer_hashtable_(2)",b);
    CTTO(HOMSYM,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhh_integer_partition_);
    ENDR("mhh_integer_hashtable_");
}



INT mult_homsym_homsym(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->HOMSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"mult_homsym_homsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,HOMSYM,"mult_homsym_homsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,HOMSYM,"mult_homsym_homsym(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_homsym(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mhh_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY) { t=1; init_hashtable(c); } 
        erg += mhh_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == HOMSYM)
        {
        if (S_O_K(c) == EMPTY) { t=1; init_hashtable(c); } 
        erg += mhh_homsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY) { t=1; init_hashtable(c); }

        if (S_O_K(b) == HASHTABLE)
            erg += mhh_hashtable_hashtable_(a,b,c,cons_eins);
        else
            erg += mhh_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_HOMSYM(c,c);
    ENDR("mult_homsym_homsym");
}

