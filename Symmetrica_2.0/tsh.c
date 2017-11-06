#include "def.h"
#include "macro.h"

INT tsh_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP m;
    CTO(INTEGER,"tsh_integer__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0),"tsh_integer__faktor:parameter < 0");

    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    COPY(f,S_MO_K(m));
    erg += first_partition(a,S_MO_S(m));
    if (S_O_K(b) == HASHTABLE) 
        INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
    else
        INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
    ENDR("tsh_integer__faktor");
}

INT t_schur_jacobi_trudi(a,b,f,intf,multf)
/* implementiert die jacobi trudi determinante
   fuer basis wechsel schur -> ... */
    OP a,b,f;
    INT (*intf)(), (*multf)();
{
    OP ff;
    INT i,j;
    OP p,h2; OP h1;
    INT erg = OK;
    CTO(PARTITION,"t_schur_jacobi_trudi(1)",a);
    CTTTTTO(HASHTABLE,HOMSYM,MONOMIAL,ELMSYM,POWSYM,"t_schur_jacobi_trudi(2)",b);

    if (S_PA_LI(a) == 0) { (*intf)(cons_null,b,f); goto eee; }
    if (S_PA_LI(a) == 1) { (*intf)(S_PA_I(a,0),b,f); goto eee; }

    p = CALLOCOBJECT();
    b_ks_pa(VECTOR,CALLOCOBJECT(),p);
    m_il_integervector(S_PA_LI(a)-1,S_PA_S(p));
    h2 = CALLOCOBJECT();
    b_ks_pa(VECTOR,CALLOCOBJECT(),h2);
    m_il_integervector(1,S_PA_S(h2));
 
    NEW_HASHTABLE(h1);
    ff = CALLOCOBJECT();
    for (j=0,i=S_PA_LI(a)-1;i>= 0; i--,j++)
        {
        if (( S_PA_II(a,i) - j ) >= 0 ) {
            INT k;
            FREESELF(ff);
            for (k=0;k<S_PA_LI(a);k++)
                {
                if (k<i) M_I_I(S_PA_II(a,k), S_PA_I(p,k) );
                else if (k>i) M_I_I(S_PA_II(a,k)+1, S_PA_I(p,k-1));
                }
 
            if (( S_PA_II(a,i) - j ) == 0)
                {
                if (j%2 == 1) { ADDINVERS(f,ff); } else { COPY(f,ff); }
                erg += t_schur_jacobi_trudi(p,b,ff,intf,multf);
                }
            else {
                if (j%2 == 1) { ADDINVERS(f,ff); } else { COPY(f,ff); }
                erg += t_schur_jacobi_trudi(p,h1,ff,intf,multf);

                M_I_I(S_PA_II(a,i) - j,S_PA_I(h2,0));
                erg += (*multf)(h2,h1,b,cons_eins);   /* erster parameter homsym */

                CLEAR_HASHTABLE(h1);
                }
            }
        else break;
        }
    FREEALL(p);
    FREEALL(h2);
    FREEALL(h1);
    FREEALL(ff);

eee:
    ENDR("t_schur_jacobi_trudi");
}

INT t_schur_naegelsbach(a,b,f,intf,multf)
/* implementiert die naegelsbach determinante
   fuer basis wechsel schur -> ... */
    OP a,b,f;
    INT (*intf)(), (*multf)();
{
    OP z,ac;
    INT i,j;
    OP p,h2; OP h1;
    INT erg = OK;
    CTO(PARTITION,"t_schur_naegelsbach(1)",a);
    CTTTTTO(HASHTABLE,HOMSYM,MONOMIAL,ELMSYM,POWSYM,"t_schur_naegelsbach(2)",b);
 
    if (S_PA_LI(a) == 0) { (*intf)(cons_null,b,f); goto eee; }

    ac = CALLOCOBJECT();
    conjugate_partition(a,ac);
    a = ac;
    

    if (S_PA_LI(a) == 1) { (*intf)(S_PA_I(a,0),b,f); goto bbb; }
 
    p = CALLOCOBJECT();
    b_ks_pa(VECTOR,CALLOCOBJECT(),p);
    m_il_integervector(S_PA_LI(a)-1,S_PA_S(p));
    h2 = CALLOCOBJECT();
    b_ks_pa(VECTOR,CALLOCOBJECT(),h2);
    m_il_integervector(1,S_PA_S(h2));
 
    h1 = CALLOCOBJECT();init_hashtable(h1);
    for (j=0,i=S_PA_LI(a)-1;i>= 0; i--,j++)
        {
        if (( S_PA_II(a,i) - j ) >= 0 ) {
            INT k;
            OP ff;
            ff = CALLOCOBJECT();
            for (k=0;k<S_PA_LI(a);k++)
                {
                if (k<i) M_I_I(S_PA_II(a,k), S_PA_I(p,k) );
                else if (k>i) M_I_I(S_PA_II(a,k)+1, S_PA_I(p,k-1));
                }
 
            if (( S_PA_II(a,i) - j ) == 0)
                {
                if (j%2 == 1)  ADDINVERS(f,ff); else  COPY(f,ff); 
                erg += t_schur_jacobi_trudi(p,b,ff,intf,multf);
                }
            else {
                if (j%2 == 1)  ADDINVERS(f,ff); else  COPY(f,ff); 
                erg += t_schur_jacobi_trudi(p,h1,ff,intf,multf);
 
                M_I_I(S_PA_II(a,i) - j,S_PA_I(h2,0));
                erg += (*multf)(h2,h1,b,cons_eins);   /* erster parameter elmsym */
 
                FORALL(z,h1, { FREESELF(z); });
                M_I_I(0,S_V_I(h1,S_V_LI(h1)));
 
 
                }
            FREEALL(ff);
            }
        else break;
        }
    FREEALL(p);
    FREEALL(h2);
    FREEALL(h1);
bbb:
    FREEALL(a); /* die conjugierte partition */
 
eee:
    CTTTTTO(HASHTABLE,HOMSYM,MONOMIAL,ELMSYM,POWSYM,"t_schur_naegelsbach(2-ende)",b);
    ENDR("t_schur_naegelsbach");
}

INT mhh_partition__();
INT mhh_partition_hashtable_();

INT tsh_jt(a,m) OP a,m;
/* jacobi trudi matrix with integer entries */
/* -1 = zero contribution */
{
    INT erg = OK,i,j;
    CTTO(PARTITION,SKEWPARTITION,"jt(1)",a);
    CTO(EMPTY,"jt(2)",m);
    if (S_O_K(a) == PARTITION)
        {
        m_ilih_nm(S_PA_LI(a),S_PA_LI(a),m);
        for (j=0;j<S_M_LI(m);j++)
        for (i=0;i<S_M_HI(m);i++)
            if (S_PA_II(a,i)+i-j < 0) M_I_I(-1,S_M_IJ(m,i,j));
            else M_I_I(S_PA_II(a,i)+i-j, S_M_IJ(m,i,j));
        }
    else /* SKEW */
        {
        OP g,k;
        INT kl;
        g = S_SPA_G(a);
        k = S_SPA_K(a);
        m_ilih_nm(S_PA_LI(g),S_PA_LI(g),m);
        for (j=0;j<S_M_LI(m);j++)
        for (i=0;i<S_M_HI(m);i++)
            if (S_PA_II(g,i)+i-j < 0) M_I_I(-1,S_M_IJ(m,i,j));
            else M_I_I(S_PA_II(g,i)+i-j, S_M_IJ(m,i,j));
        println(m);
        /* now shift in the columns */
        for (j=S_M_LI(m)-1,kl=S_PA_LI(k)-1;kl>=0;kl--,j--)
        for (i=0;i<S_M_HI(m);i++)
             {
             if (S_M_IJI(m,i,j) == -1);
             else if ((S_M_IJI(m,i,j) - S_PA_II(k,kl)) < 0) M_I_I(-1,S_M_IJ(m,i,j));
             else M_I_I((S_M_IJI(m,i,j) - S_PA_II(k,kl)), S_M_IJ(m,i,j));
             }
        }
    ENDR("jt");
}

INT tsh_eval_jt(b,f,m) OP b,f,m;
{
    INT i,j;
    INT erg = OK;
    OP p,pv;
    CTTO(HASHTABLE,HOMSYM,"tsh_eval_jt(1)",b);
    p = CALLOCOBJECT();
    pv = CALLOCOBJECT();
    first_permutation(S_M_H(m),p);
    first_permutation(S_M_H(m),pv);
    do {
        OP c,v;
        INT z,k;
nn:
        for (i=0,z=0;i<S_P_LI(p);i++)
             if (S_M_IJI(m,i,S_P_II(p,i)-1) == -1) goto next;
             else if (S_M_IJI(m,i,S_P_II(p,i)-1) == 0) z++;
        /* valid contribution to result */
        c = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),c);
        signum_permutation(p,S_MO_K(c));
        v = CALLOCOBJECT();
        m_il_integervector(S_M_LI(m)-z,v);
        for (i=0,j=0;i<S_P_LI(p);i++)
            if (S_M_IJI(m,i,S_P_II(p,i)-1) > 0)
                {
                M_I_I(S_M_IJI(m,i,S_P_II(p,i)-1),S_V_I(v,j));
                j++;
                }
        qsort(S_V_S(v), S_V_LI(v), sizeof(struct object), comp_integer_integer);
        b_ks_pa(VECTOR,v,S_MO_S(c));
        MULT_APPLY(f,S_MO_K(c));
 
        INSERT_HOMSYMMONOM_(c,b);
        continue;
 
        next: /* we can increase the permutation */
        if (i==0) goto jj;
        i--;
        for (j=S_P_LI(p)-1;j>=i;j--) ADDINVERS_APPLY_INTEGER(S_P_I(pv,S_P_II(p,j)-1));
        /* now all used entries are marked */
        /* check where you can increase */
aa:        k = S_P_II(p,i);
        for (j=k; j<S_P_LI(p);j++)
             if (S_P_II(pv,j) < 0) {
                 /* it works */
                 M_I_I(- S_P_II(pv,j), S_P_I(p,i));
                 ADDINVERS_APPLY_INTEGER(S_P_I(pv,j));
                 i++;
                 for (k=0;k<S_P_LI(pv);k++)
                     if (S_P_II(pv,k) < 0) { M_I_I(- S_P_II(pv,k), S_P_I(p,i));
                                         ADDINVERS_APPLY_INTEGER(S_P_I(pv,k));
                                         i++;
                                       }
                 goto nn;
                 }
        i--;
        if (i==0) goto jj;
        ADDINVERS_APPLY_INTEGER(S_P_I(pv,S_P_II(p,i)-1));
        goto aa;
        ;
    } while(next_apply(p));
     
jj:
    FREEALL(p);
    FREEALL(pv);
    ENDR("tsh_eval_jt");
}

INT tsh_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tsh_partition__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        tsh_integer__faktor(cons_null,b,f);
        goto eee;
        }
    else if (S_PA_LI(a) == 1) {
        tsh_integer__faktor(S_PA_I(a,0),b,f);
        goto eee;
        }
    else {
        OP m;
        m = CALLOCOBJECT();
        tsh_jt(a,m);
        tsh_eval_jt(b,f,m);
        FREEALL(m);
        goto eee;
        }

eee:
    ENDR("tsh_partition__faktor");
}




#ifdef UNDEF
INT tsh_partition__faktor_pre310102(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tsh_partition__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        tsh_integer__faktor(cons_null,b,f);
        goto eee;
        }
    else if (S_PA_LI(a) == 1) {
        tsh_integer__faktor(S_PA_I(a,0),b,f);
        goto eee;
        }
    else 
        {
        OP m,p;
        INT i,j;
        m = CALLOCOBJECT();
        m_ilih_nm(S_PA_LI(a),S_PA_LI(a),m);
        for (j=0;j<S_M_LI(m);j++)
        for (i=0;i<S_M_HI(m);i++)
            if (S_PA_II(a,i)+i-j < 0) M_I_I(-1,S_M_IJ(m,i,j));
            else M_I_I(S_PA_II(a,i)+i-j, S_M_IJ(m,i,j));
     
    
        p = CALLOCOBJECT();
        first_permutation(S_PA_L(a),p);
        do {
            OP c,v;
            INT z=0;
            for (i=0;i<S_P_LI(p);i++)
                 if (S_M_IJI(m,i,S_P_II(p,i)-1) == -1) goto next;
                 else if (S_M_IJI(m,i,S_P_II(p,i)-1) == 0) z++;
            /* valid contribution to result */
            c = CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),c);
            signum_permutation(p,S_MO_K(c));
            MULT_APPLY(f,S_MO_K(c));
            v = CALLOCOBJECT();
            m_il_integervector(S_PA_LI(a)-z,v);
            for (i=0,j=0;i<S_P_LI(p);i++)
                if (S_M_IJI(m,i,S_P_II(p,i)-1) > 0)
                    {
                    M_I_I(S_M_IJI(m,i,S_P_II(p,i)-1),S_V_I(v,j));
                    j++;
                    }
            qsort(S_V_S(v), S_V_LI(v), sizeof(struct object), comp_integer_integer);
            b_ks_pa(VECTOR,v,S_MO_S(c));
    
            INSERT_HOMSYMMONOM_(c,b);
            next: ;
        } while(next_apply(p));
     
        FREEALL(m);
        FREEALL(p);
        goto eee;
        }
eee:
    ENDR("tsh_partition__faktor");
}

INT tsh_partition__faktor_pre240102(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tsh_partition__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_partition__faktor(2)",b);

    /* nach der ersten spalte entwickeln bei jacobi trudi det */
    if (S_PA_LI(a) == 0) { 
        tsh_integer__faktor(cons_null,b,f);
        goto eee;
        }
    if (S_PA_LI(a) == 1) {
        tsh_integer__faktor(S_PA_I(a,0),b,f);
        goto eee;
        }
    if (S_PA_LI(a) == 2) {
        OP m;
        /* s_a,b = h_a,b - h_a--,b++ */
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
        if (S_PA_II(a,0) > 1) {
            m_il_integervector(2,S_PA_S(S_MO_S(m)));
            M_I_I(S_PA_II(a,0)-1, S_PA_I(S_MO_S(m),0));
            M_I_I(S_PA_II(a,1)+1, S_PA_I(S_MO_S(m),1));
            }
        else {
            m_il_integervector(1,S_PA_S(S_MO_S(m)));
            M_I_I(S_PA_II(a,1)+1, S_PA_I(S_MO_S(m),0));
            }
        ADDINVERS(f,S_MO_K(m));
        if (S_O_K(b) == HOMSYM)
            INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
        else
            INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,
                                            hash_monompartition);

        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        copy_partition(a,S_MO_S(m));
        COPY(f,S_MO_K(m));
        if (S_O_K(b) == HOMSYM)
            INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
        else
            INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,
                                            hash_monompartition);
        goto eee;
        }

    if (S_PA_II(a,S_PA_LI(a)-1) == 1) /* elmsym */
        {
        INT teh_integer__faktor();
        erg += teh_integer__faktor(S_PA_L(a),b,f);
        goto eee;
        }
    t_schur_jacobi_trudi(a,b,f,tsh_integer__faktor,mhh_partition_hashtable_);
      
eee:
    ENDR("tsh_partition__faktor");
}
#endif

INT tsh_schur__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,SCHUR,"tsh_schur__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_schur__faktor(2)",b);

    T_FORALL_MONOMIALS_IN_A(a,b,f,tsh_partition__faktor); 
   
    ENDR("tsh_schur__faktor");
}

INT tsh_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tsh_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh_hashtable__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tsh_partition__faktor);
    ENDR("tsh_hashtable__faktor");
}


INT tsh___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,SCHUR,PARTITION,"tsh___faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tsh___faktor(2)",b);
    if (S_O_K(a) == INTEGER) {
        erg += tsh_integer__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tsh_partition__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == SCHUR) {
        erg += tsh_schur__faktor(a,b,f);
        goto eee;
        }
    else /* HASHTABLE */ {
        erg += tsh_hashtable__faktor(a,b,f);
        goto eee;
        }
eee:
    ENDR("tsh___faktor");
}


INT t_SCHUR_HOMSYM(a,b) OP a,b;
{
    INT erg = OK;
    INT t = 0;
    CTTTTO(INTEGER,HASHTABLE,SCHUR,PARTITION,"t_SCHUR_HOMSYM",a);
    TCE2(a,b,t_SCHUR_HOMSYM,HOMSYM);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    tsh___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_HOMSYM(b,b);

    ENDR("t_SCHUR_HOMSYM");
}


