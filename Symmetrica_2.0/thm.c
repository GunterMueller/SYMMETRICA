#include "def.h"
#include "macro.h"

INT t_HOMSYM_MONOMIAL(a,b) OP a,b;
/* AK 260901 */
/* faster using newmultiplication
   h_n \times m_I = \sum c_n,I,J m_J
*/
{
    INT erg = OK;
    OP m;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"t_HOMSYM_MONOMIAL",a);
    TCE2(a,b,t_HOMSYM_MONOMIAL,MONOMIAL);
 
    m=CALLOCOBJECT();
    erg += first_partition(cons_null,m);
    erg += mult_homsym_monomial(a,m,b);
    FREEALL(m);
    ENDR("t_HOMSYM_MONOMIAL");
}

static OP thm_sp = NULL;

INT thm_ende() 
{
    INT erg = OK;
    if (thm_sp!= NULL) {
        FREEALL(thm_sp);
        thm_sp=NULL;
        }
    ENDR("thm_ende");
}


static INT thm2_co(a,b,c,f) OP a,b,c,f;
{
    OP m;
    INT erg = OK;
    m = CALLOCOBJECT();
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    COPY(a,S_MO_S(m));
    COPY(f,S_MO_K(m));
    if (S_O_K(c) == HASHTABLE)
        insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
    else
        insert_list(m,c,add_koeff,comp_monommonomial);
    ENDR("thm2_co");
}

OP find_thm_integer(a) OP a;
{
    INT erg = OK;
    CTO(INTEGER,"find_thm_integer(1)",a);
    SYMCHECK( (S_I_I(a) < 0) ,"find_thm_integer:parameter <0");
    if (thm_sp==NULL){ thm_sp=CALLOCOBJECT();m_il_v(100,thm_sp);}
    if (S_I_I(a)>S_V_LI(thm_sp)) { erg += inc_vector_co(S_I_I(a)-S_V_LI(thm_sp)+30);}
    if (EMPTYP(S_V_I(thm_sp,S_I_I(a))))
        {
        OP c;
        c = CALLOCOBJECT();
        first_partition(a,c);
        init_hashtable(S_V_I(thm_sp,S_I_I(a)));
        do {
            OP m;
            m= CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
            M_I_I(1,S_MO_K(m));
            COPY(c,S_MO_S(m));
            insert_scalar_hashtable(m,S_V_I(thm_sp,S_I_I(a)),NULL,eq_monomsymfunc,hash_monompartition);
        } while (next_apply(c));

        FREEALL(c);
        }
    
    return S_V_I(thm_sp,S_I_I(a));

    ENDO("find_thm_integer");
}

INT thm_integer__faktor(a,b,f) OP a,b,f;
{
    OP c;
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"thm_integer__faktor(2)",b);
    CTO(INTEGER,"thm_integer__faktor(1)",a);
    SYMCHECK( (S_I_I(a) < 0) ,"thm_integer__faktor:parameter <0");

    if (thm_sp==NULL){ thm_sp=CALLOCOBJECT();m_il_v(100,thm_sp);}
    if (S_I_I(a)>S_V_LI(thm_sp)) { erg += inc_vector_co(S_I_I(a)-S_V_LI(thm_sp)+30);}

    if (EMPTYP(S_V_I(thm_sp,S_I_I(a)))) 
        {
        c = CALLOCOBJECT();
        first_partition(a,c);
        init_hashtable(S_V_I(thm_sp,S_I_I(a)));
        do {
            OP m;
            m= CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
            M_I_I(1,S_MO_K(m));
            COPY(c,S_MO_S(m));
            insert_scalar_hashtable(m,S_V_I(thm_sp,S_I_I(a)),NULL,eq_monomsymfunc,hash_monompartition);
        } while (next_apply(c));
        FREEALL(c);
        }

    erg += m_forall_monomials_in_a(S_V_I(thm_sp,S_I_I(a)),cons_eins,b,f,thm2_co);

    ENDR("thm_integer__factor");
}

INT thm_partition__faktor(a,b,f) OP a,b,f;
{
    OP c;
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"thm_partition__faktor(2)",b);
    CTO(PARTITION,"thm_partition__faktor(1)",a);
 
 
    c = CALLOCOBJECT();
    erg += first_partition(cons_null,c);
    erg += mhm_partition__(a,c,b,f);
    FREEALL(c);
 
    ENDR("thm_partition__factor");
}

