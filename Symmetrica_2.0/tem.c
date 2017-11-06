
#include "def.h"
#include "macro.h"


static OP tem_sp = NULL;

INT tem_ende() 
{
    INT erg = OK;
    if (tem_sp!= NULL) {
        FREEALL(tem_sp);
        tem_sp=NULL;
        }
    ENDR("tem_ende");
}


static INT tsp2_co(a,b,c,f) OP a,b,c,f;
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
    ENDR("tsp2_co");
}

OP find_tem_integer(a) OP a;
{
    INT erg = OK;
    CTO(INTEGER,"find_tem_integer(1)",a);
    SYMCHECK( (S_I_I(a) < 0) ,"find_tem_integer:parameter <0");
    if (tem_sp==NULL){ tem_sp=CALLOCOBJECT();m_il_v(100,tem_sp);}
    if (S_I_I(a)>S_V_LI(tem_sp)) { erg += inc_vector_co(S_I_I(a)-S_V_LI(tem_sp)+30);}
    if (EMPTYP(S_V_I(tem_sp,S_I_I(a))))
        {
        OP c;
        c = CALLOCOBJECT();
        first_partition(cons_null,c);
        init_hashtable(S_V_I(tem_sp,S_I_I(a)));
        mem_integer__(a,c,S_V_I(tem_sp,S_I_I(a)),cons_eins);
        FREEALL(c);
        }
    
    return S_V_I(tem_sp,S_I_I(a));

    ENDO("find_tem_integer");
}

INT tem_integer__faktor(a,b,f) OP a,b,f;
{
    OP c;
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"tem_integer__faktor(2)",b);
    CTO(INTEGER,"tem_integer__faktor(1)",a);
    SYMCHECK( (S_I_I(a) < 0) ,"tem_integer__faktor:parameter <0");

    if (tem_sp==NULL){ tem_sp=CALLOCOBJECT();m_il_v(100,tem_sp);}
    if (S_I_I(a)>S_V_LI(tem_sp)) { erg += inc_vector_co(S_I_I(a)-S_V_LI(tem_sp)+30);}

    if (EMPTYP(S_V_I(tem_sp,S_I_I(a)))) 
        {
        c = CALLOCOBJECT();
        first_partition(cons_null,c);
        init_hashtable(S_V_I(tem_sp,S_I_I(a)));
        mem_integer__(a,c,S_V_I(tem_sp,S_I_I(a)),cons_eins);
        FREEALL(c);
        }
    M_FORALL_MONOMIALS_IN_A(S_V_I(tem_sp,S_I_I(a)),cons_eins,b,f,tsp2_co);

    ENDR("tem_integer__factor");
}

INT tem_partition__faktor(a,b,f) OP a,b,f;
{
    OP c;
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"tem_partition__faktor(2)",b);
    CTO(PARTITION,"tem_partition__faktor(1)",a);
 
 
    c = CALLOCOBJECT();
    erg += first_partition(cons_null,c);
    erg += mem_partition__(a,c,b,f);
    FREEALL(c);
 
    ENDR("tem_partition__factor");
}

