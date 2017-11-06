#include "def.h"
#include "macro.h"

static OP mpp_pp_m = NULL;
INT mpp_ende()
{
    INT erg = OK;
    if (mpp_pp_m != NULL)
        {
        FREEALL(mpp_pp_m);
        mpp_pp_m=NULL;
        }
    ENDR("mpp_ende");
}

INT m_merge_partition_partition();
INT mpp_integer_partition_();
INT mpp_integer_hashtable_();
INT mpp_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(INTEGER,"mpp_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mpp_integer__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_integer__(3)",c);

    if (S_O_K(b) == PARTITION) {
        erg += mpp_integer_partition_(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mpp_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    ENDR("mpp_integer__");
}

INT mpp_partition_partition_(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"mpp_partition_partition_(1)",a);
    CTO(PARTITION,"mpp_partition_partition_(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_partition_partition_(3)",c);
    erg += m_merge_partition_partition(a,b,c,f,comp_monompowsym,eq_monomsymfunc);
    ENDR("mpp_partition_partition_");
}

INT m_merge_partition_partition(a,b,c,f,lf,hf) OP a,b,c; OP f;
     INT (*lf)();
     INT (*hf)();
/* multiplication of two partitions bei merging */
{
    INT erg = OK;
    INT i,j,k;
    static INT ms=0;
    OP ap,bp,mp;
    CTO(PARTITION,"m_merge_partition_partition(1)",a);
    CTO(PARTITION,"m_merge_partition_partition(2)",b);
    CTTTTO(HASHTABLE,POWSYM,HOMSYM,ELMSYM,"m_merge_partition_partition(3)",c);

 
    if (mpp_pp_m == NULL) {
        mpp_pp_m = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),mpp_pp_m);
        erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(mpp_pp_m));
        erg += m_il_nv(50,S_PA_S(S_MO_S(mpp_pp_m)));
        C_O_K(S_PA_S(S_MO_S(mpp_pp_m)), INTEGERVECTOR);
        ms = 50;
        }
    if (S_PA_LI(b)+S_PA_LI(a) > ms) {
        INT inkr;
        inkr=S_PA_LI(b)+S_PA_LI(a)-ms+10;
        M_I_I(ms,S_PA_L(S_MO_S(mpp_pp_m)));
        erg += inc_vector_co(S_PA_S(S_MO_S(mpp_pp_m)), inkr);
        ms = S_PA_LI(S_MO_S(mpp_pp_m));
        for (i=ms-1; inkr > 0; inkr--)
            M_I_I(0,S_PA_I(S_MO_S(mpp_pp_m),i));
        }

    C_I_I(S_PA_L(S_MO_S(mpp_pp_m)), S_PA_LI(b)+S_PA_LI(a) );


    for ( 
        ap = S_V_S(S_PA_S(a)),
        bp = S_V_S(S_PA_S(b)),
        mp = S_V_S(S_PA_S(S_MO_S(mpp_pp_m))),
        i=S_PA_LI(a),
        j=S_PA_LI(b),
        k=S_PA_LI(S_MO_S(mpp_pp_m));

        k>0; 

        k--,mp++
        )
        {

        if (j == 0)
            { 
            C_I_I(mp, S_I_I(ap) );
            i--; ap++; 
            }
        else if (i == 0)
            { 
            C_I_I(mp, S_I_I(bp) );
            j--; bp++; 
            }
        else if (S_I_I(bp) < S_I_I(ap) )
            { 
            C_I_I(mp, S_I_I(bp) );
            j--; bp++; 
            }
        else
            { 
            C_I_I(mp, S_I_I(ap) );
            i--; ap++; 
            }
        }


    CLEVER_COPY(f,S_MO_K(mpp_pp_m));
    if (S_O_K(c) == HASHTABLE)
        {
        HASH_INTEGERVECTOR(S_PA_S(S_MO_S(mpp_pp_m)),j);
        C_PA_HASH(S_MO_S(mpp_pp_m),j);
        erg += add_apply_hashtable(mpp_pp_m,c,add_koeff,hf,hash_monompartition);
        }
    else /* LIST */
        {
        OP mm;
        mm = CALLOCOBJECT();
        COPY(mpp_pp_m,mm);
        INSERT_LIST(mm,c,add_koeff,lf);
        }

    C_I_I(S_PA_L(S_MO_S(mpp_pp_m)), ms);
    ENDR("m_merge_partition_partition");
}

INT mpp_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mpp_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mpp_partition__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_partition__(3)",c);

    if (S_O_K(b) == PARTITION)
        {
        erg += mpp_partition_partition_(a,b,c,f);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mpp_partition_partition_);
        goto ende;
        }
ende:
    ENDR("mpp_partition__");
}

INT mpp_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"mpp_powsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mpp_powsym__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_powsym__(3)",c);
    if (S_O_K(b) == PARTITION)
        {
        M_FORALL_MONOMIALS_IN_A(a,b,c,f,mpp_partition_partition_);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mpp_partition_partition_);
        goto ende;
        }
ende:
    ENDR("mpp_powsym__");
}

INT mpp_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mpp_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mpp_hashtable__(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_hashtable__(3)",c);
    if (S_O_K(b) == PARTITION)
        {
        M_FORALL_MONOMIALS_IN_A(a,b,c,f,mpp_partition_partition_);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mpp_partition_partition_);
        goto ende;
        }
ende:
    ENDR("mpp_hashtable__");
}

INT mpp_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a \times p_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mpp_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"mpp_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mpp_partition_partition_);
    ENDR("mpp_hashtable_hashtable_");
}


INT mpp_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP m;
    INT i,k;

    CTO(INTEGER,"mpp_integer_partition_(1)",a);
    CTO(PARTITION,"mpp_integer_partition_(2)",b);
    CTTO(POWSYM,HASHTABLE,"mpp_integer_partition_(3)",c);

    
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
    if (S_O_K(c) == POWSYM)
        INSERT_LIST(m,c,add_koeff,comp_monompowsym);
    else
        INSERT_HASHTABLE(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);

    ENDR("mpp_integer_partition_");
}

INT mpp_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"mpp_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,POWSYM,"mpp_integer_hashtable_(2)",b);
    CTTO(POWSYM,HASHTABLE,"integer_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mpp_integer_partition_);
    ENDR("mpp_integer_hashtable_");
}



INT mult_powsym_powsym(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->POWSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"mult_powsym_powsym(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mult_powsym_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"mult_powsym_powsym(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_powsym(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mpp_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mpp_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == POWSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mpp_powsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mpp_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_POWSYM(c,c);
    ENDR("mult_powsym_powsym");
}

INT mpp___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"mpp___(1)",a);
    CTTTO(HASHTABLE,PARTITION,POWSYM,"mpp___(2)",b);
    CTTO(HASHTABLE,POWSYM,"mpp___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
         erg += mpp_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += mpp_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
         erg += mpp_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
         erg += mpp_hashtable__(a,b,c,f);
        }
 
    ENDR("mpp___");
}

