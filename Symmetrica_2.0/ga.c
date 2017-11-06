/* SYMMETRICA: ga.c */
/* group algebra */
#include "def.h"
#include "macro.h"

static INT co_posorneg_sum();

#ifdef PERMTRUE
INT konj_perm_perm(perm,konj,res)    OP perm,konj,res;
/* AK 070789 V1.0 */ /* AK 200891 V1.3 */
{
    INT i;
    INT erg = OK;
    CE3(perm,konj,res, konj_perm_perm);

    m_il_p(S_P_LI(konj),res);
    C_O_K(S_P_S(res),INTEGERVECTOR);
    for (i=0L;i<S_P_LI(perm);i++)
         M_I_I(S_P_II(konj,S_P_II(perm,i)-1L),S_P_I(res,S_P_II(konj,i)-1L));
    ENDR("konj_perm_perm");
}
#endif /* PERMTRUE */

#ifdef POLYTRUE
INT mult_gral_gral(eins,zwei,res) OP eins, zwei, res;
/* AK 100789 V1.0 */ /* MB 311290 */ /* AK 200891 V1.3 */
{

    OP  z, ez, zz;
    OP bt;
    INT erg = OK;

    CTO(GRAL,"mult_gral_gral(1)",eins);
    CTO(GRAL,"mult_gral_gral(2)",zwei);
    CE3(eins,zwei,res,mult_gral_gral);
    bt = callocobject();
    erg += init(BINTREE,bt);

    zz = zwei;
    while (zz != NULL)
    {
        ez = eins;
        while (ez != NULL)
        {
            z = callocobject();
            erg += b_sk_mo(callocobject(),callocobject(),z);
            erg += mult(  S_PO_S(ez), S_PO_S(zz), S_MO_S(z) );
            erg += mult(    S_PO_K(ez), S_PO_K(zz), S_MO_K(z) );
            insert(z,bt,add_koeff,comp_monomvector_monomvector);
            ez = S_PO_N(ez);
        };
        zz = S_PO_N(zz);
    };
    t_BINTREE_GRAL(bt,res);
    FREEALL(bt);
    ENDR("mult_gral_gral");
}

INT mult_scalar_gral(von,nach,ergebnis) OP von, nach, ergebnis;
/* AK 230402 */
{
    INT erg = OK;
    CTO(GRAL,"mult_scalar_gral(2)",nach);
    CTO(EMPTY,"mult_scalar_gral(3)",ergebnis);
    MULT_SCALAR_MONOMLIST(von,nach,ergebnis);
    ENDR("mult_scalar_gral");
}
    



INT horizontal_sum(n,a)      OP n,a; 
/* MB 311290 */ /* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    INT erg = OK; /* AK 310892 */
    OP p,q;
    CTO(INTEGER,"horizontal_sum(1)",n);
    SYMCHECK(S_I_I(n)<1,"horizontal_sum: n<=0");

    p= callocobject();
    erg += init(GRAL,a);
    erg += first_permutation(n,p);
    do {
        q = callocobject();
        erg += m_skn_gral(p,cons_eins,NULL,q);
        erg += insert(q,a,NULL,NULL);
    
       } while(next_apply(p));
    FREEALL(p);
    ENDR("horizontal_sum");
}




INT vertikal_sum(n,a)      OP n,a; 
/* MB 311290 */ /* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    OP p,z;
    INT erg = OK;
    CTO(INTEGER,"vertikal_sum(1)",n);
    SYMCHECK(S_I_I(n)<1,"vertikal_sum: n<=0");
    CE2(n,a,vertikal_sum);

    p= callocobject();

    erg += init(GRAL,a);

    erg += first_permutation(n,p);

    do     {
    z = callocobject();
    erg += b_skn_gral(callocobject(),callocobject(),NULL,z);
    erg += copy(p,S_PO_S(z));
    erg += signum_permutation(p,S_PO_K(z));
    insert(z,a,NULL,NULL);
    } 
    while(next(p,p));

    erg += freeall(p);
    ENDR("vertikal_sum");
}
#endif /* PERMTRUE */

#ifdef TABLEAUXTRUE
#ifdef POLYTRUE
INT konjugation(gral,tab,i,d)     OP gral, tab ,d; INT i; 
/* MB 311290 */ /* AK 200891 V1.3 */
{

    OP  p, v, w, x, z, zeiger;
    INT j;
    INT erg = OK;

    p = callocobject();
    v = callocobject();
    w = callocobject();
    x = callocobject();
    z = callocobject();

    erg += init(GRAL,d);

           erg += weight(tab,w);
    
    
        erg += first_permutation(w,v);
    zeiger = gral;
    while (zeiger != NULL)
    {
          erg += copy(v,p);
          for(j=0L;j<s_p_li(S_PO_S(zeiger));j++)
              M_I_I(s_t_iji(tab,i,S_P_II(S_PO_S(zeiger),j)-1L),
                        S_P_I(p,s_t_iji(tab,i,j)-1L));
          erg += m_skn_gral(p,S_PO_K(zeiger),NULL,z);
      erg += add_apply(z,d);
      zeiger = S_PO_N(zeiger);
    };


    erg += freeall(p);
    erg += freeall(x);
    erg += freeall(w);
    erg += freeall(v);
    erg += freeall(z);
    ENDR("konjuation");
}
#endif /* POLYTRUE */
#endif /* TABLEAUXTRUE */



#ifdef TABLEAUXTRUE
INT konjugierende(t,i,cp)   OP t,cp; INT i;  
/* MB 311290 */ /* AK 200891 V1.3 */
{

    OP  v,w,x,y,z;
    INT j;
    INT erg = OK;

    v = callocobject(); w = callocobject();
    x = callocobject();
    z = callocobject();
    erg += weight(S_T_U(t),w);
    erg += first_permutation(w,v);
    erg += copy(v,cp);
    for(j=0L;j<S_PA_II(S_T_U(t),S_T_HI(t)-1-i);j++)
        {
         erg += copy(v,x);
         c_i_i(S_P_I(x,j),s_t_iji(t,i,j));
         c_i_i(S_P_I(x,s_t_iji(t,i,j)-1L),j+1L);
         erg += mult(cp,x,cp);
        }
    erg += freeall(z);
    erg += freeall(w);
    erg += freeall(v);
    erg += freeall(x);
    ENDR("konjugierende");
}
#endif /* TABLEAUXTRUE */
    

#ifdef POLYTRUE
INT konj_gral_perm(gral,perm,res) OP gral, perm, res;
/* MB 311290 */ /* AK 200891 V1.3 */
/* AK 050898 */
{
    OP  x, z, zeiger;
    INT erg = OK;
    CE3(gral,perm,res,konj_gral_perm);
    CTO(GRAL,"konj_gral_perm",gral);
    CTO(PERMUTATION,"konj_gral_perm",perm);


    erg += init(GRAL,res);
    zeiger = gral;
    while (zeiger != NULL)
    {
        z = callocobject();
            erg += b_skn_gral(callocobject(),callocobject(),NULL,z);
        erg += copy(S_PO_K(zeiger),S_PO_K(z));
            erg += konj_perm_perm( S_PO_S(zeiger), perm, S_PO_S(z) );
        erg += insert(z,res,NULL,NULL);
        zeiger = S_PO_N(zeiger);
    };
    ENDR("konj_gral_perm");
}
#endif /* POLYTRUE */


#ifdef TABLEAUXTRUE
INT hplus(tab,h)   OP tab, h; 
/* MB 311290 */ /* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    OP  u,w,x,y,z;
    INT i;
    INT erg = OK;

    CTO(TABLEAUX,"hplus",tab);
    if (S_O_K(S_T_U(tab)) != PARTITION) /* AK 310892 */
        {
        return error("hplus:only for TABLEAUX of PARTITION shape");
        }
        if (check_equal_2(tab,h,hplus,&erg) == EQUAL)
                goto he;


    u = callocobject();
    w = callocobject();
    x = callocobject();
    y = callocobject();
    z = callocobject();
    if (not EMPTYP(h)) 
        erg += freeself(h);
    erg += weight(tab,w);
    erg += first_permutation(w,u);
    erg += m_skn_gral(u,cons_eins,NULL,x);
    for(i=0L;i<S_T_HI(tab);i++)
        {
        if(S_PA_II(s_t_u(tab),S_T_HI(tab)-1-i)>1L)
            {
             erg += horizontal_sum(s_pa_i(s_t_u(tab),S_T_HI(tab)-1L-i),y);
             erg += konjugation(y,tab,i,z);
             erg += mult_gral_gral(x,z,y); 
             erg += copy(y,x);
            }
        }
    erg += copy(x,h);
    erg += freeall(u);
    erg += freeall(w);
    erg += freeall(x);
    erg += freeall(y);
    erg += freeall(z);
he:
    ENDR("hplus");
}




INT vminus(tab,v)   OP tab,v; 
/* MB 311290 */ /* AK 200891 V1.3 */
{
    OP u,w,x,y,z,m,tc;
    INT erg = OK;
    INT i;

    CTO(TABLEAUX,"vminus",tab);
    if (S_O_K(S_T_U(tab)) != PARTITION) /* AK 310892 */
        {
        return error("vminus:only for TABLEAUX of PARTITION shape");
        }
        if (check_equal_2(tab,v,vminus,&erg) == EQUAL)
                goto ve;

    if (tab == v)
        FATALERROR("vminus");
    m = callocobject();
    tc = callocobject();
    u = callocobject();
    w = callocobject();
    y = callocobject();
    z = callocobject();
    if (not EMPTYP(v)) 
        erg += freeself(v);
    erg += transpose(S_T_S(tab),m);
    erg += m_matrix_tableaux(m,tc);
    erg += weight(tc,w);
    erg += first_permutation(w,u);
    erg += m_skn_gral(u,cons_eins,NULL,v);
    for(i=0L;i<S_T_HI(tc);i++)
        {
        if(S_PA_II(S_T_U(tc),S_T_HI(tc)-1-i)>1L)
            {
            erg += vertikal_sum(s_pa_i(S_T_U(tc),S_T_HI(tc)-1-i),y);
            erg += konjugation(y,tc,i,z);
            erg += mult(v,z,v); 
            }
        }
    erg += freeall(m);
    erg += freeall(z);
    erg += freeall(u);
    erg += freeall(w);
    erg += freeall(tc);
    erg += freeall(y);
ve:
    ENDR("vminus");
}



INT idempotent(tab,idp)  OP tab,idp;
/* MB 311290 */ /* AK 200891 V1.3 */
{
    OP  hz,v,h,x;
    INT erg = OK;

    hz = callocobject();
    h = callocobject();
    x = callocobject();
    v = callocobject();
    erg += hplus(tab,h);
    erg += vminus(tab,v);
    erg += mult(h,v,x);
    erg += dimension(S_T_U(tab),hz);
    erg += invers(hz,hz);
    erg += mult(hz,x,idp);
    erg += freeall(x);
    erg += freeall(h);
    erg += freeall(hz);
    erg += freeall(v);
    ENDR("idempotent");
}
#endif /* TABLEAUXTRUE */

#ifdef CHARTRUE
INT zentralprim(part,idp)  OP part,idp;
 /* MB 311290 */ /* AK 200891 V1.3 */
{
     OP  hz,p,v,w,x,y,zt,vecsc;
     INT ind;
         INT erg = OK;

     hz = CALLOCOBJECT();
     p = CALLOCOBJECT();
     v = CALLOCOBJECT();
     w = CALLOCOBJECT();
     x = CALLOCOBJECT();
     y = CALLOCOBJECT();
         init(GRAL,y);
     zt = CALLOCOBJECT();
     vecsc = CALLOCOBJECT();
     m_part_sc(part,vecsc);
     weight(part,w);
     first_permutation(w,p);
     do {
        zykeltyp(p,zt);
        ind = indexofpart(zt);
        if(S_I_I(S_V_I(s_sc_w(vecsc),ind)))
            {
             m_skn_gral(p,S_V_I(s_sc_w(vecsc),ind),
                   NULL, x);
             erg += add_apply(x,y);
            }
        }  while(next_apply(p));
    erg += dimension(part,hz);
    erg += invers(hz,hz);
    erg += mult(hz,y,v);
    erg += copy(v,idp);
    FREEALL(vecsc);
        FREEALL(v);
        FREEALL(hz);
        FREEALL(y);
    FREEALL(zt); 
        FREEALL(x);
        FREEALL(p); 
        FREEALL(w);
    ENDR("zentralprim");
}
#endif /* CHARTRUE */


#ifdef POLYTRUE
INT konjugation2(gral,perm,res)     OP gral, perm, res; 
/* MB 311290 */ /* AK 200891 V1.3 */
{
    OP  p, v,  x, z, zeiger;
    INT j;

    p = callocobject();
    v = callocobject();
    x = callocobject();
    z = callocobject();

        first_permutation(s_p_l(perm),v);
    zeiger = gral;
    while (zeiger != NULL)
    {
          copy(v,p);
          for(j=0L;j<S_P_LI(S_PO_S(zeiger));j++)
              M_I_I(S_P_II(perm,S_P_II(S_PO_S(zeiger),j)-1L),
                        S_P_I(p,S_P_II(perm,j)-1L));
          m_skn_gral(p,S_PO_K(zeiger),NULL,z);
      add_apply(z,x);
      zeiger = S_PO_N(zeiger);
    };
    copy(x,res);
    freeall(p);
    freeall(v);
    freeall(x);
    freeall(z);
    return OK;
}
#endif /* POLYTRUE */

INT objectread_gral(filename,gral)  FILE *filename;OP gral; 
/* MB 311290 */ /* AK 200891 V1.3 */
{
    char antwort[2];

    b_sn_l(callocobject(),NULL,gral);

    objectread_monom(filename,S_L_S(gral));
    fscanf(filename,"%s",antwort);
    if (antwort[0]  == 'j')
    {
        C_L_N(gral,callocobject());
        objectread_gral(filename,S_L_N(gral));
    }
    return(OK);
}
 
INT objectwrite_gral(filename,gral)  FILE *filename;OP gral;
/* ausgabe eines list-objects
ausgabe bis einschliesslich next == NULL */ /* MB 311290 */
/* AK 200891 V1.3 */
{

    OP zeiger = gral;

        {
        fprintf(filename, " %d ",POLYNOM);
        
        objectwrite(filename,S_PO_S(zeiger));
        objectwrite(filename,S_PO_K(zeiger));
        zeiger=S_PO_N(zeiger);
        while (zeiger != NULL) /* abbruch bedingung */
        {
            fprintf(filename,"j\n");
            objectwrite(filename,S_PO_S(zeiger));
            objectwrite(filename,S_PO_K(zeiger));
            zeiger=S_PO_N(zeiger);/*zeiger auf das naechste element*/
        }
        fprintf(filename,"n\n");
        }
    return(OK);
}

#ifdef POLYTRUE
INT scan_gral(a) OP a;
/* AK 200891 V1.3 */
{
    char antwort[2];
    INT erg;


    /* ergebnis ist ein leeres object */
    b_sn_l(callocobject(),NULL,a);
    C_O_K(a,GRAL);
    /* self ist nun initialisiert */

    erg=scan(MONOM,S_L_S(a));
    if (erg == ERROR) {
        error("scan_gral:error in scaning listelement");
        return(ERROR); 
        }

    printeingabe("one more monom  j/n");
    scanf("%s",antwort);
    if (antwort[0]  == 'j')
        {
            C_L_N(a,callocobject());
            scan_gral(S_L_N(a));
        };
    return OK;
}
#endif /* POLYTRUE */

INT add_apply_gral_gral(a,b) OP a,b;
/* AK 200891 V1.3 */
    {
    OP c = callocobject();
    copy_list(a,c);
    return(insert(c,b,NULL,NULL));
    }

#ifdef POLYTRUE
INT add_apply_gral(a,b) OP a,b;
/* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    if (EMPTYP(b)) 
        return(copy_polynom(a,b));
    switch(S_O_K(b)) {
        case GRAL: 
            return add_apply_gral_gral(a,b);
        default:
            { 
            /* 210291 */
            OP c = callocobject();
            INT erg;
            *c = *b;
            C_O_K(b,EMPTY);
            erg = add(a,c,b);
            erg += freeall(c);
            return erg;
            }
        }
}
#endif /* POLYTRUE */


#ifdef GRALTRUE 
INT mult_apply_gral(a,b) OP a,b;
/* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    switch (S_O_K(b))
    {
    case GRAL:
        {
        OP c;
        c = callocobject();
        *c = *b;
        C_O_K(b,EMPTY);
        mult_gral_gral(a,c,b);
        freeall(c);
        return OK;
        }
    default:
        return error("mult_apply_gral:wrong second type");
    }
}

INT mult_gral(a,b,d) OP a,b,d;
/* AK 030902 */
{
    INT erg = OK;
    CTO(GRAL,"mult_gral(1)",a);
    CTO(EMPTY,"mult_gral(3)",d);
    switch(S_O_K(b))
        {
        case GRAL:
            erg += mult_gral_gral(a,b,d);
            break;
        case BRUCH:
        case LONGINT:
        case INTEGER:
        case FF:
            erg+=mult_scalar_gral(b,a,d);
            break;
        default:
            WTO("mult_gral(2)",b);
            break;
        }                                                                                     
    ENDR("mult_gral");
}

INT random_gral(a,b) OP a,b;
/* AK 310892 */
{
    INT i, erg = OK;
    OP c,d,e;
    if (S_O_K(a) != INTEGER)
        return ERROR;
    erg += init(GRAL,b);
    d = callocobject();
    e = callocobject();
    for (i=0L;i<10L;i++)
        {
        c = callocobject();
        random_permutation(a,d);
        random_integer(e,NULL,NULL);
        if (not nullp(e)) {
            m_skn_gral(d,e,NULL,c);
            insert(c,b,NULL,NULL);
            }
        }
    freeall(d);
    freeall(e);
    return erg;
}

INT pos_sum(a,b) OP a,b;
{
return co_posorneg_sum(a,b,1L);
}
INT neg_sum(a,b) OP a,b;
{
return co_posorneg_sum(a,b,0L);
}

static INT co_posorneg_sum(a,b,what) OP a,b; INT what;
/* AK 280193 */
{
    OP c = callocobject();
    OP d = callocobject();
    OP e = callocobject();
    INT erg = OK;
    INT i,k,j;

    if (what == 1L)
        erg += horizontal_sum(S_V_L(a),c);
    else if (what == 0L)
        erg += vertikal_sum(S_V_L(a),c);
    erg += copy(a,d);
    erg += sort(d);
    erg += m_il_p(S_V_II(d,S_V_LI(d)-1L),e); /* identitaet */
    for (i=0L,k=0L,j=S_V_LI(d);i<S_P_LI(e);i++)
        if (i+1L == S_V_II(d,k) )
            {
            erg += m_i_i( S_V_II(d,k) ,S_P_I(e,k));
            k++;
            }
        else
            {
            erg += m_i_i( i+1L ,S_P_I(e,j));
            j++;
            }
    /* e ist die permutation zum konjugieren */
    erg += konj_gral_perm(c,e,b);

    erg += freeall(c);
    erg += freeall(d);
    erg += freeall(e);
    return erg;
}




INT vminus_hecke(a,b) OP a,b;
/* AK 070693 */
/* das element C^lambda(q) aus wybourne: J math Phys 33 (1992) 4-14 */
/* a ist tableaux, b wird group algebra mit koeff polynom in einer variablen */ 
{ 
    INT erg = OK; 
    OP z,l,c; 
    vminus(a,b); 
    z = b; 
    l = callocobject(); 
    c = callocobject(); 
    erg += conjugate(S_T_U(a),c); 
    erg += maxorder_young(c,l);
    while (z != NULL)
        {
        erg += numberof_inversionen(S_PO_S(z),c);
        erg += m_iindex_iexponent_monom(0L,S_I_I(l)-S_I_I(c),S_PO_K(z));
        if ((S_I_I(c) % 2L) == 1L)
            erg += addinvers_apply(S_PO_K(z));
        z = S_PO_N(z);
        }
    erg += freeall(c);
    erg += freeall(l);
    ENDR("vminus_hecke");
}



INT garnir(f,g,h,c) OP f,g,h,c;
/* AK 090693 */
/* g,h INTVECTOREN , f TABLEAUX , c wird GROUPALGEBRA */
{
    OP a = callocobject();
    OP b = callocobject();
    OP d = callocobject();
    OP h2 = callocobject();
    OP z;
    INT i,j,i1;
    INT erg = OK ;


    erg += b_ks_pa(VECTOR,callocobject(),a);
    erg += m_il_integervector(2L,S_PA_S(a));
    M_I_I(S_V_LI(g),S_PA_I(a,0L));
    M_I_I(S_V_LI(h),S_PA_I(a,1L));

    erg += weight(a,c);
    erg += first_permutation(c,b);
    erg += m_skn_gral(b,cons_eins,NULL,d);
    z=d;
    erg += copy(b,c);
    while (next_shuffle_part(a,c,b) != FALSE)
        {
        C_PO_N(z,callocobject());
        erg += m_skn_gral(b,cons_eins,NULL,S_PO_N(z));
        erg += copy(b,c);
        z = S_PO_N(z);
        erg += signum(b,S_PO_K(z));
        }

    erg += weight(f,b); /* grad der permutation, mit der konjugiert wird */
    erg += first_permutation(b,a);

    j=0L;
    erg += append(h,g,h2); 
    erg += sort(h2);
    for (i=0L;i<S_V_LI(g);i++)
        {
        erg += m_i_i(S_V_II(g,i),S_P_I(a,j));
        j++;
        }
    for (i=0L;i<S_V_LI(h);i++)
        {
        erg += m_i_i(S_V_II(h,i),S_P_I(a,j));
        j++;
        }
    i1=0L;
    for (i=1L;i<=S_P_LI(a);i++)
        {
        if ((i1 < S_V_LI(h2)) && (S_V_II(h2,i1) == i)) i1++;
        else {
        erg += m_i_i(i,S_P_I(a,j));
        j++;
        }
    }
    erg += konj_gral_perm(d,a,c); 
    FREEALL(a);
    FREEALL(b);
    FREEALL(d);
    FREEALL(h2);
    ENDR("garnir");
}
#endif /* GRALTRUE */
