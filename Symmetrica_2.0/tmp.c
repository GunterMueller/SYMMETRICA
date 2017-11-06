#include "def.h"
#include "macro.h"
INT tmp_monomial__faktor();
INT monomial_recursion();
INT tmp_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP c;
    CTO(INTEGER,"tmp_integer__faktor(1)",a);
    CTTO(POWSYM,HASHTABLE,"tmp_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0),"tmp_integer__faktor: first parameter < 0");

    c  = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),c);
    erg += first_partition(a,S_MO_S(c));
    COPY(f,S_MO_K(c));

    if (S_O_K(b) == POWSYM)
        INSERT_LIST(c,b,add_koeff,comp_monompowsym);
    else
        INSERT_HASHTABLE(c,b,add_koeff,eq_monomsymfunc,hash_monompartition);

    ENDR("tmp_integer__faktor");
}

INT tmp_int__faktor(a,b,f) OP b,f; INT a;
{
    INT erg = OK;
    OP c,d;
    CTTO(POWSYM,HASHTABLE,"tmp_int__faktor(2)",b);
    SYMCHECK((a < 0),"tmp_int__faktor: first parameter < 0");
 
    c  = CALLOCOBJECT();
    d  = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),c);
    M_I_I(a,d);
    erg += first_partition(d,S_MO_S(c));
    COPY(f,S_MO_K(c));
 
    if (S_O_K(b) == POWSYM)
        INSERT_LIST(c,b,add_koeff,comp_monompowsym);
    else
        INSERT_HASHTABLE(c,b,add_koeff,eq_monomsymfunc,hash_monompartition);
    FREEALL(d);
 
    ENDR("tmp_int__faktor");
}


INT mpp_hashtable_hashtable_();
INT tmp_partition__faktor(a,b,f) OP a,b,f;
{
    static INT level=0;
    INT erg = OK;
    CTO(PARTITION,"tmp_partition__faktor(1)",a);
    CTTO(POWSYM,HASHTABLE,"tmp_partition__faktor(2)",b);

    level++;
    if (S_PA_LI(a) == 0)
        erg += tmp_integer__faktor(cons_null,b,f);
    else if (S_PA_LI(a) == 1)
        erg += tmp_integer__faktor(S_PA_I(a,0),b,f);
    else if (S_PA_LI(a) == 2)
        {
        /* 
           if a != b : m_a,b = p_a,b - p_(a+b)
           if a == b : m_a,a = 1/2 p_a,a - 1/2 p_(a+a)
        */
        OP m,ff;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        copy_partition(a,S_MO_S(m));
        COPY(f,S_MO_K(m));
        if (S_PA_II(a,0)==S_PA_II(a,1))
            div_apply(S_MO_K(m),cons_zwei);
        if (S_O_K(b) == POWSYM)
            INSERT_LIST(m,b,add_koeff,comp_monompowsym);
        else
            insert_scalar_hashtable(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);

        ff = CALLOCOBJECT();
        ADDINVERS(f,ff);
        if (S_PA_II(a,0)==S_PA_II(a,1))
            div_apply(ff,cons_zwei);
        erg += tmp_int__faktor(S_PA_II(a,0)+S_PA_II(a,1),b,ff);
        FREEALL(ff);
        goto eee;
        }
    else
        {
            erg += monomial_recursion(a,b,f,
                           tmp_partition__faktor,
                           tmp_monomial__faktor,mpp_hashtable_hashtable_);
        goto eee;
        }

eee:    
    ENDR("tmp_partition__faktor");
}

INT splitpart(a,p1,p2) OP a,p1,p2;
/* a is a partition of length >= 2 */
/* b and c becomes half of it */
{
    OP v1,v2;
    INT erg = OK;
    INT i,j;
    CTO(PARTITION,"splitpart(1)",a);

    v1 = CALLOCOBJECT();
    v2 = CALLOCOBJECT();
    erg += m_il_v(S_PA_LI(a)/2 ,v1);
    erg += m_il_v(S_PA_LI(a)-S_V_LI(v1) ,v2);
    for (i=0;i<S_V_LI(v1);i++) M_I_I(S_PA_II(a,i),S_V_I(v1,i));
    for (j=0;i<S_PA_LI(a);i++,j++) M_I_I(S_PA_II(a,i),S_V_I(v2,j));
    erg += b_ks_pa(VECTOR,v1,p1);
    erg += b_ks_pa(VECTOR,v2,p2);
    ENDR("splitpart");
}
INT mmm_partition_partition_();
INT monomial_recursion(a,b,f,partf,monf,multf) OP a,b,f; INT (*partf)(); INT (*monf)();
     INT (*multf)();
/* implementiert die rekursion fuer monomial symmetric functions */
/* m_a1,a2,...,an,an+1,...a2n =
   m_a1,...,an * m_an+1,..,a2n - terms of length <2n 
*/
/* a ist partition
   b wirds result
   f ist faktor 
   partf ist eine funktion fuer partitionen
   monf ist eine funktion fuer monomials */
{
    INT erg = OK;
    OP p1,p2,m1,m2,h2,h3,c;
    OP coeff;

    CTO(PARTITION,"monomial_recursion(1)",a);

    p1 = CALLOCOBJECT(); p2 = CALLOCOBJECT();
    erg += splitpart(a,p1,p2);
    /* p1 und p2 sind die halben partitionen */
 
    m1 = CALLOCOBJECT(); init_hashtable(m1);
    erg += mmm_partition_partition_(p1,p2,m1,cons_eins);
 
    m2 = CALLOCOBJECT();
    erg += b_sk_mo(NULL,NULL,m2);
    C_MO_S(m2,a);
 
    c = find_hashtable(m2,m1,eq_monomsymfunc,hash_monompartition);
    SYMCHECK( (c == NULL) ,"tmp_partition__faktor:wrong leading monomial");
    coeff = CALLOCOBJECT();
    INVERS(S_MO_K(c),coeff); /* leitkoeff */
    MULT_APPLY(coeff,m1);
    FREESELF(c); 
    DEC_INTEGER(S_V_I(m1,S_V_LI(m1)));
 
    /* es gilt jetzt m_a = (m_p1 * m_p2 )*coeff - m1 */
 
 
 
    c = CALLOCOBJECT();
    ADDINVERS(f,c);
    erg += (*monf)(m1,b,c);

    C_MO_S(m2,c);
    C_MO_K(m2,m1);
    FREEALL(m2);
 
    h2 = CALLOCOBJECT();init_hashtable(h2);
    erg += (*partf)(p1,h2,coeff);
    FREEALL(p1);
    FREEALL(coeff);
 
    h3 = CALLOCOBJECT();init_hashtable(h3);
    erg += (*partf)(p2,h3,f);
    FREEALL(p2);
 
    erg += (*multf)(h3,h2,b,cons_eins);
 
    FREEALL(h2);
    FREEALL(h3);
    ENDR("monomial_recursion");
}

INT monomial_recursion2();
INT tmp_monomial__faktor(a,b,f) OP a,b,f;
{
    INT tep_integer__faktor();
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"tmp_monomial__faktor(1)",a);
    CTTO(POWSYM,HASHTABLE,"tmp_monomial__faktor(2)",b);

    monomial_recursion2(a,b,f,
             tmp_partition__faktor,tmp_integer__faktor,
             tep_integer__faktor,
             mult_powsym_powsym);
    ENDR("tmp_monomial__faktor");
}

INT tmp___faktor(a,b,f) OP a,b,f;
/* 061201 */
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,MONOMIAL,PARTITION,"tmp___faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tmp___faktor(2)",b);

    if (S_O_K(a) == INTEGER) {
        erg += tmp_integer__faktor(a,b,f);
        goto eee;
        }
 
    if (S_O_K(a) == PARTITION)
        {
        erg += tmp_partition__faktor(a,b,f);
        goto eee;
        }
    else /* MONOMIAL HASHTABLE */
        {
        erg += tmp_monomial__faktor(a,b,f);
        goto eee;
        }
eee:
    ENDR("tmp___faktor");
}

INT t_MONOMIAL_POWSYM(a,b) OP a,b;
/* AK 170901 */
{
    INT erg = OK;
    INT t = 0;
    
    CTTTTO(HASHTABLE,INTEGER,MONOMIAL,PARTITION,"t_MONOMIAL_POWSYM(1)",a);
    TCE2(a,b,t_MONOMIAL_POWSYM,POWSYM);

    if (S_O_K(b) == EMPTY)
        {
        init_hashtable(b);t=1;
        }
    CTTO(POWSYM,HASHTABLE,"t_MONOMIAL_POWSYM(2)",b);

    erg += tmp___faktor(a,b,cons_eins);

    if (t==1) t_HASHTABLE_POWSYM(b,b);
    ENDR("t_MONOMIAL_POWSYM");
}
