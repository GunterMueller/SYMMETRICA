/* mhe: mult_homsym_elmsym 
        multiplication of two symmetric functions */
#include "def.h"
#include "macro.h"

static INT mhe_integer_partition_();
static INT mhe_integer_hashtable_();
static INT mhe_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(INTEGER,"mhe_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mhe_integer__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mhe_integer__(3)",c);

    if (S_O_K(b) == PARTITION) 
        erg += mhe_integer_partition_(a,b,c,f);
    else 
        erg += mhe_integer_hashtable_(a,b,c,f);
    ENDR("mhe_integer__");
}

static INT mhe_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhe_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mhe_partition__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mhe_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        if (S_O_K(b) == PARTITION) {
            OP d;
            d = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
            erg += copy_partition(b,S_MO_S(d));
            COPY(f,S_MO_K(d));
            if (S_O_K(c) == ELMSYM)
                INSERT_LIST(d,c,add_koeff,comp_monomelmsym);
            else
                INSERT_HASHTABLE(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }
        else /* elmsym or hashtable */
            {
            OP z;
            FORALL(z,b,{
                OP d;
                d = CALLOCOBJECT();
                erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
                erg += copy_partition(S_MO_S(z),S_MO_S(d));
                COPY(S_MO_K(z),S_MO_K(d));
                if (not EINSP(f))
                    {
                    MULT_APPLY(f,S_MO_K(d));
                    }
                if (S_O_K(c) == ELMSYM)
                    INSERT_LIST(d,c,add_koeff,comp_monomelmsym);
                else
                    INSERT_HASHTABLE(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
                });
            }
        goto endr_ende;
        }
    else { /* partition of length >= 1 */
        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();

        erg += init_hashtable(e);
        erg += mhe_integer__(S_PA_I(a,0),b,e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mhe_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
        if (S_O_K(c) == ELMSYM)
            INSERT_LIST(e,c,add_koeff,comp_monomelmsym);
        else
            INSERT_HASHTABLE(e,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        }


    ENDR("mhe_partition__");
}

static INT mhe_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times e_b  \times f */
{
    INT erg = OK;
    CTO(HOMSYM,"mhe_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mhe_homsym__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mhe_homsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhe_partition__);
    ENDR("mhe_homsym__");
}

static INT mhe_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times e_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mhe_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mhe_hashtable__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"mhe_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhe_partition__);
    ENDR("mhe_homsym__");
}

static INT mhe_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP e,z,m;
    INT i,j,k;
    OP find_the_integer();

    CTO(INTEGER,"mhs_integer_partition_(1)",a);
    CTO(PARTITION,"mhs_integer_partition_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"integer_partition_(3)",c);

    e = find_the_integer(a);
    
    FORALL(z,e,{
        m = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
        erg += m_il_v(S_PA_LI(b)+S_PA_LI(S_MO_S(z)),S_PA_S(S_MO_S(m)));
        C_O_K(S_PA_S(S_MO_S(m)),INTEGERVECTOR);
        for (i=0,j=0,k=0; k<S_PA_LI(S_MO_S(m)); k++)
            {
            if (j == S_PA_LI(b)) { M_I_I(S_PA_II(S_MO_S(z),i), S_PA_I(S_MO_S(m),k)); i++; }
            else if (i == S_PA_LI(S_MO_S(z))) { M_I_I(S_PA_II(b,j), S_PA_I(S_MO_S(m),k)); j++; }
            else if (S_PA_II(b,j) < S_PA_II(S_MO_S(z),i) )
                { M_I_I(S_PA_II(b,j), S_PA_I(S_MO_S(m),k)); j++; }
            else
                { M_I_I(S_PA_II(S_MO_S(z),i), S_PA_I(S_MO_S(m),k)); i++; }
            }
        COPY(S_MO_K(z), S_MO_K(m));
        if (not EINSP(f))
            {
            MULT_APPLY(f,S_MO_K(m));
            }
        if (S_O_K(c) == ELMSYM)
            INSERT_LIST(m,c,add_koeff,comp_monomelmsym);
        else
            INSERT_HASHTABLE(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        });

    ENDR("mhe_integer_partition_");
}

static INT mhe_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"mhs_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,ELMSYM,"mhs_integer_hashtable_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhe_integer_partition_);
   
    ENDR("mhe_integer_hashtable_");
}



INT mult_homsym_elmsym(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->ELMSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"mult_homsym_elmsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"mult_homsym_elmsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"mult_homsym_elmsym(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_elmsym(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mhe_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhe_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == HOMSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhe_homsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mhe_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_ELMSYM(c,c);

    CTTO(HASHTABLE,ELMSYM,"mult_homsym_elmsym(res)",c);
    ENDR("mult_homsym_elmsym");
}

