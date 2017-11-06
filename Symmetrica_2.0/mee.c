#include "def.h"
#include "macro.h"

INT mee_integer_partition_();
INT mee_integer_hashtable_();
INT m_merge_partition_partition();

INT mee_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;

    CTO(INTEGER,"mee_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mee_integer__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_integer__(3)",c);
    SYMCHECK( S_I_I(a) < 0 , "mee_integer__:integer<0");

    if (S_O_K(b) == PARTITION) {
        erg += mee_integer_partition_(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mee_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    ENDR("mee_integer__");
}

INT mee_partition_partition_(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"mee_partition_partition_(1)",a);
    CTO(PARTITION,"mee_partition_partition_(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_partition_partition_(3)",c);
    erg += m_merge_partition_partition(a,b,c,f,comp_monomelmsym,eq_monomsymfunc);
    ENDR("mee_partition_partition_");
}

INT mee_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mee_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mee_partition__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_partition__(3)",c);

    if (S_O_K(b) == PARTITION)
        {
        erg += mee_partition_partition_(a,b,c,f);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mee_partition_partition_);
        goto ende;
        }

ende:
    ENDR("mee_partition__");
}

INT mee_elmsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += e_a \times e_b  \times f */
{
    INT erg = OK;
    CTO(ELMSYM,"mee_elmsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mee_elmsym__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_elmsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mee_partition__);   
    ENDR("mee_elmsym__");
}

INT mee_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += e_a \times e_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mee_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mee_hashtable__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mee_partition__); 
    ENDR("mee_hashtable__");
}

INT mee_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += e_a \times e_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mee_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"mee_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mee_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mee_partition_partition_);
    ENDR("mee_hashtable_hashtable_");
}

INT mee_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP m;
    INT i,k;

    CTO(INTEGER,"mee_integer_partition_(1)",a);
    CTO(PARTITION,"mee_integer_partition_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"mee_integer_partition_(3)",c);
    SYMCHECK( S_I_I(a) < 0 , "mee_integer_partition_:integer<0");

    
    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    if (S_I_I(a) == 0) {
        COPY(b,S_MO_S(m));
        }
    else {
        erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
        erg += m_il_integervector(S_PA_LI(b)+1,S_PA_S(S_MO_S(m)));
    
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
        }

    COPY(f, S_MO_K(m));
    INSERT_ELMSYMMONOM_(m,c);

    ENDR("mee_integer_partition_");
}

INT mee_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"mee_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,ELMSYM,"mee_integer_hashtable_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"mee_integer_hashtable_(3)",c);
    CTO(ANYTYPE,"mee_integer_hashtable_(4)",f);
    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mee_integer_partition_);
    CTTO(ELMSYM,HASHTABLE,"mee_integer_hashtable_(e3)",c);
    ENDR("mee_integer_hashtable_");
}



INT mult_elmsym_elmsym(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->ELMSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"mult_elmsym_elmsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mult_elmsym_elmsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"mult_elmsym_elmsym(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_elmsym(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mee_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mee_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == ELMSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mee_elmsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mee_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_ELMSYM(c,c);
    ENDR("mult_elmsym_elmsym");
}

