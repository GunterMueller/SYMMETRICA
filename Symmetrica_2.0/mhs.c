/* SYMMETRICA file mhs.c */
/* multiplication of homsym with schur */
/* result will be schur */
#include "def.h"
#include "macro.h"

INT mhs_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(INTEGER,"mhs_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mhs_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mhs_integer__(3)",c);

    if (S_O_K(b) == PARTITION) {
        erg += mhs_integer_partition_(a,b,c,f);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhs_integer_partition_);
        goto ende;
        }
ende:
    ENDR("mhs_integer__");
}

INT mhs_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhs_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mhs_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mhs_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        if (S_O_K(b) == PARTITION) {
            OP d;
            d = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
            erg += copy_partition(b,S_MO_S(d));
            COPY(f,S_MO_K(d));
            if (S_O_K(c) == SCHUR)
                INSERT_LIST(d,c,add_koeff,comp_monomschur);
            else
                INSERT_HASHTABLE(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }
        else /* schur or hashtable */
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
                if (S_O_K(c) == SCHUR)
                    INSERT_LIST(d,c,add_koeff,comp_monomschur);
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
        erg += mhs_integer__(S_PA_I(a,0),b,e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mhs_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
        if (S_O_K(c) == SCHUR)
            INSERT_LIST(e,c,add_koeff,comp_monomschur);
        else
            INSERT_HASHTABLE(e,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        }


    ENDR("mhs_partition__");
}

INT mhs_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HOMSYM,"mhs_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mhs_homsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mhs_homsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhs_partition__);
    ENDR("mhs_homsym__");
}

INT mhs_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mhs_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mhs_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mhs_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhs_partition__);
    ENDR("mhs_hashtable__");
}


INT mult_homsym_schur(a,b,c) OP a,b,c;
/* AK 111001
   with pieri rule
*/
/* is the result=c empty the result will be a SCHUR object
   is the result a HASHTABLE or SCHUR object will be the result inserted
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->SCHUR necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"mult_homsym_schur(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_homsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"mult_homsym_schur(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_schur(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mhs_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhs_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == HOMSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mhs_homsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mhs_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_SCHUR(c,c);
    ENDR("mult_homsym_schur");
}



static INT mhs_first_pieri(a,b,c) OP a,b,c;
{
    m_il_nv(S_V_LI(b),c);
    m_i_i(S_I_I(a),S_V_I(c,0));
    C_O_K(c,INTEGERVECTOR);
    return OK;
}

static INT mhs_next_pieri_limit_apply(limit,v) OP limit,v;
{
    INT i,w=0,g=0;
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"mhs_next_pieri_limit_apply(1)",limit);
    CTTO(INTEGERVECTOR,VECTOR,"mhs_next_pieri_limit_apply(2)",v);

    for (i=S_V_LI(v)-1; i>=0;i--) 
        {
        if (S_V_II(v,i) > 0) 
        if (w > 0) break;
        else 
            g+=S_V_II(v,i);
        if (S_V_II(limit,i) > 0) 
            w+=S_V_II(limit,i)-S_V_II(v,i);

        M_I_I(0,S_V_I(v,i));
        }
    /* an der stelle i kann nach rechts geschoben werden */
    if (i== -1) return FALSE;

    g++;
    M_I_I(S_V_II(v,i)-1, S_V_I(v,i));
    for (i++; ;i++)
        {
        if (S_V_II(limit,i) >= g)
            {
            M_I_I(g,S_V_I(v,i));
            return TRUE;
            }
        else {
            M_I_I(S_V_II(limit,i),S_V_I(v,i));
            g = g - S_V_II(limit,i);
            }
        }
    /* we should never end up here */
    ENDR("mhs_next_pieri_limit_apply");
}

INT mhs_integer_partition_(a,b,c,f) OP a,b,c,f;
/* c += h_a \times s_b \times f*/
/* c is already initialised */
{
    INT erg = OK;
    /* pieri rule */
    OP limit;
    OP v;
    INT i,j;
    OP ps,s,pa;

    CTO(INTEGER,"mhs_integer_partition_(1)",a);
    CTO(PARTITION,"mhs_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"mhs_integer_partition_(3)",c);

/*printf("mhs_integer_partition_:a=");println(a);
printf("mhs_integer_partition_:b=");println(b);
printf("mhs_integer_partition_:c=");println(c);
printf("mhs_integer_partition_:f=");println(f);*/


    if (S_PA_LI(b) == 0) {
        OP s;
        s = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),s);
        COPY(f,S_MO_K(s));
        m_i_pa(a,S_MO_S(s));
        
        if (S_O_K(c) == SCHUR)
            insert_list(s,c,add_koeff,comp_monomschur);
        else
            insert_scalar_hashtable(s,c,add_koeff,eq_monomsymfunc,hash_monompartition);

        goto ende;
        }

    limit = CALLOCOBJECT();
    v = CALLOCOBJECT();
    m_il_v(S_PA_LI(b)+1,limit);
    C_O_K(limit,INTEGERVECTOR);
    M_I_I(S_I_I(a),S_V_I(limit,0));
    for (j=1,i=S_PA_LI(b)-1;i>0;i--,j++)
        M_I_I(S_PA_II(b,i)-S_PA_II(b,i-1),S_V_I(limit,j));
    M_I_I(S_PA_II(b,0),S_V_I(limit,j));




    ps = CALLOCOBJECT();
    pa = CALLOCOBJECT();
    s = CALLOCOBJECT();

    erg += b_ks_pa(VECTOR,ps,pa);
    erg += m_il_nv(S_V_LI(limit),ps);
    C_O_K(ps,INTEGERVECTOR);
    erg += b_sk_mo(pa,CALLOCOBJECT(),s);
    COPY(f,S_MO_K(s));

    mhs_first_pieri(a,limit,v); 
    do {

        
        if (S_V_II(v,S_V_LI(v)-1) > 0) 
            {
            M_I_I(S_V_LI(v),S_V_L(ps));
            M_I_I(S_V_II(v,S_V_LI(v)-1), S_V_I(ps,0));
            }
        else 
            M_I_I(S_V_LI(v)-1,S_V_L(ps));
 
        for (i=S_PA_LI(b)-1,j=0;i>=0;i--,j++)
            M_I_I(S_PA_II(b,i)+S_V_II(v,j), S_V_I(ps,S_V_LI(ps)-1-j));

            

        if (S_O_K(c) == SCHUR)
            {
            OP ss = CALLOCOBJECT();
            copy_monom(s,ss);
            insert_list(ss,c,add_koeff,comp_monomschur);
            }
        else
            {
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(s)),j);
            C_PA_HASH(S_MO_S(s),j);
            erg += add_apply_hashtable(s,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }

    } while (mhs_next_pieri_limit_apply(limit,v) == TRUE);

    FREEALL(s);
    FREEALL(limit);
    FREEALL(v);
ende:
    ENDR("mhs_integer_partition_");
}

