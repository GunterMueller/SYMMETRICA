#include "def.h"
#include "macro.h"

INT mhp_integer_partition_();
INT mhp_integer_hashtable_();
INT mhp_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    

    CTO(INTEGER,"mhp_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mhp_integer__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mhp_integer__(3)",c);
    CTO(ANYTYPE,"mhp_integer__(4)",f);

    if (S_O_K(b) == PARTITION) {
        erg += mhp_integer_partition_(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mhp_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    CTTO(HASHTABLE,POWSYM,"mhp_integer__(e3)",c);
    ENDR("mhp_integer__");
}

INT mhp_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhp_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mhp_partition__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mhp_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        if (S_O_K(b) == PARTITION) {
            OP d;
            d = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
            erg += copy_partition(b,S_MO_S(d));
            COPY(f,S_MO_K(d));
            INSERT_POWSYMMONOM_(d,c);
            }
        else /* powsym or hashtable */
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
                INSERT_POWSYMMONOM_(d,c);
                });
            }
        goto endr_ende;
        }
    else { /* partition of length >= 1 */
        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();

        erg += init_hashtable(e);
        erg += mhp_integer__(S_PA_I(a,0),b,e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mhp_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
        if (S_O_K(c) == POWSYM)
            INSERT_LIST(e,c,add_koeff,comp_monompowsym);
        else
            INSERT_HASHTABLE(e,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        }


    ENDR("mhp_partition__");
}

INT mhp_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times p_b  \times f */
{
    INT erg = OK;
    
    CTO(HOMSYM,"mhp_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mhp_homsym__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mhp_homsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhp_partition__);   
    ENDR("mhp_homsym__");
}

INT mhp_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times p_b  \times f */
{
    INT erg = OK;
    
    CTO(HASHTABLE,"mhp_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mhp_hashtable__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mhp_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhp_partition__); 
    ENDR("mhp_homsym__");
}

OP find_thp_integer();
INT mhp_co(a,b,c,f) OP a,b,c,f;
{
    INT m_merge_partition_partition();
    return m_merge_partition_partition(a,b,c,f,comp_monompowsym,eq_monomsymfunc);
}

INT mpp_partition_partition_();
INT mhp_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP e;

    CTO(INTEGER,"mhp_integer_partition_(1)",a);
    CTO(PARTITION,"mhp_integer_partition_(2)",b);
    CTTO(POWSYM,HASHTABLE,"mhp_integer_partition_(3)",c);
    SYMCHECK((S_I_I(a) <= 0),"mhp_integer_partition_:parameter <= 0");

    e = find_thp_integer(a);
    M_FORALL_MONOMIALS_IN_A(e,b,c,f,mpp_partition_partition_);
    ENDR("mhp_integer_partition_");
}


INT mhp_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP e;
 
    CTO(INTEGER,"mhp_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,POWSYM,"mhp_integer_hashtable_(2)",b);
    CTTO(POWSYM,HASHTABLE,"mhp_integer_hashtable_(3)",c);

    e = find_thp_integer(a);

    M_FORALL_MONOMIALS_IN_AB(e,b,c,f,mpp_partition_partition_);

    ENDR("mhp_integer_hashtable_");
}





INT mult_homsym_powsym(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->POWSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"mult_homsym_powsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mult_homsym_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"mult_homsym_powsym(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_powsym(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mhp_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhp_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == HOMSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhp_homsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mhp_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_POWSYM(c,c);
    ENDR("mult_homsym_powsym");
}

