/*  SYMMETRICA zykelind.c */

#include "def.h"
#include "macro.h"


static INT zykeltyp_on_pairs_reduced();
static INT zykeltyp_on_2sets();
static INT zykeltyp_on_ksubsets();
static INT zykeltyp_on_ktuples();

static INT zykelind_index_verschieben();

static INT zykelind_operation_for_exp();
static INT zykeltyp_operation_for_exp();

static INT zykeltyp_poly_part();
static INT zykeltyp_hyperbegleitmatrix_poly();
static INT exponenten_bestimmen();
static INT charakteristik_bestimmen();
static INT zykeltyp_poly_part_aff();
static INT zykeltyp_hyperbegleitmatrix_poly_afferg();

static INT zykelind_aff1Zp();
static INT zykelind_aff1Z2();

static INT min_pot();
static INT zykelind_dir_prod_pglkq();
static INT zykelind_dir_prod_pglkq_apply();
static INT zykelind_hoch_dir_prod_pglkq();
static INT mod_mult();
static INT subexponenten_bestimmen();
static INT zyklische_gruppe();
static INT zykeltyp_poly_part_pglkq();
static INT zykeltyp_hyperbegleitmatrix_poly_pglkq();
static INT zykelind_aus_subzykelind();
static INT monom_to_vek();
static INT vek_to_monom();

static INT sum_vector11();
static INT sum_vector1();
static INT zykelind_red();
static INT zykelind_red_apply();
static INT debruijn_formel();

static INT eval_polynom_maxgrad();
static INT mult_po_po_maxgrad();
static INT hoch_po_maxgrad();

static INT zykelind_test1();
static INT comp_vector1();
static INT ordnung();
static INT mu();
static INT vektor_mult_apply();
static INT vektor_prod();
static INT vektor_kgv_prod_durch_kgv();
static INT fmultinom();
static INT fmultinom_ext();
static INT erster_kandidat();
static INT next_kandidat();
static INT next_kandidat2();
static INT first_unordered_part_into_atmost_k_parts();
static INT next_unordered_part_into_atmost_k_parts();
static INT first_part_into_atmost_k_parts();
static INT next_part_into_atmost_k_parts();

static INT redf_f1();
static INT redf_f2(); 
static INT redf_f3();
static INT redf_f1h();
static INT redf_f2h(); 
static INT redf_f3h();
static INT redf_formel();


#ifdef POLYTRUE
INT zykelind_dir_prod(a,b,c)  
/* Berechnet aus den Zykelindizes a und b einen 
   weiteren Zykelindex c. Es operiere G auf X und H 
   auf Y dann operiert  G\times H auf X\times Y. Der 
   Zykelindex c ist der Zykelindex der Operation von 
   G\times H in obiger Situation, falls a der 
   Zykelindex von der Aktion von G auf X und b der 
   Zykelindex der Aktion von H auf Y ist. */
    OP a,b,c;
{
    OP hilfk,hilfmonom,monom1,monom2,monom3;
    INT i1,i2,ex1,ex2;
    INT erg=OK;
    CTO(POLYNOM,"zykelind_dir_prod(1)",a);
    CTO(POLYNOM,"zykelind_dir_prod(2)",b);
    hilfk=callocobject();
    hilfmonom=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,c);
    monom1=a;
    while (monom1!=NULL)
    { 
      monom2=b;
      while (monom2!=NULL)
      {
        erg+=mult(S_PO_K(monom1),S_PO_K(monom2),hilfk);
        erg+=m_scalar_polynom(hilfk,monom3);
        for (i1=0L; i1<S_V_LI(S_PO_S(monom1)) ; ++i1)
        {
          ex1=S_V_II(S_PO_S(monom1),i1);
          if (ex1 != 0L) 
          {
        for (i2=0L; i2<S_V_LI(S_PO_S(monom2)); ++i2)
        {
          ex2=S_V_II(S_PO_S(monom2),i2);
          if (ex2 != 0L) 
          {
            erg+=m_iindex_iexponent_monom(((i1+1L)*(i2+1L)/ggt_i(i1+1L,i2+1L))-1L,ex1*ex2*ggt_i(i1+1L,i2+1L),hilfmonom);
            erg+=mult_apply(hilfmonom,monom3);
          }
        } 
          } 
        }
        monom2=S_PO_N(monom2);
        erg+=add_apply(monom3,c);
      }
      monom1=S_PO_N(monom1);
    }
    FREEALL(hilfk);
    FREEALL(hilfmonom);
    FREEALL(monom3);
    ENDR("zykelind_dir_prod");
}

INT zykelind_dir_prod_apply(a,b) OP a,b;
{
    OP hilf;
    INT erg=OK;
    CTO(POLYNOM,"zykelind_dir_prod_apply(1)",a);
    CTO(POLYNOM,"zykelind_dir_prod_apply(2)",b);
    hilf=callocobject();
    erg+=zykelind_dir_prod(a,b,hilf);
    erg+=copy(hilf,b);
    erg+=freeall(hilf);
    ENDR("zykelind_dir_prod_apply");
}

INT zykelind_dir_summ(a,b,c)  
/* Berechnet aus den Zykelindizes a und b einen
   weiteren Zykelindex c. Es operiere G auf X und H 
   auf Y, wobei X und Y keine gemeinsamen Elemente 
   besitzen, dann operiert  G\times H auf X\cup Y. 
   Der Zykelindex c ist der Zykelindex der Operation 
   von G\times H in obiger Situation, falls a der 
   Zykelindex von der Aktion von G auf X und b der 
   Zykelindex der Aktion von H auf Y ist. */
    OP a,b,c;
{
    INT erg=OK;
    CTO(POLYNOM,"zykelind_dir_summ(1)",a);
    CTO(POLYNOM,"zykelind_dir_summ(2)",b);
    erg+=mult(a,b,c);
    ENDR("zykelind_dir_summ");
}

INT zykelind_dir_summ_apply(a,b)
    OP a,b;
{
    OP hilf;
    INT erg=OK;
    CTO(POLYNOM,"zykelind_dir_summ_apply(1)",a);
    CTO(POLYNOM,"zykelind_dir_summ_apply(2)",b);
    MULT_APPLY(a,b);
    ENDR("zykelind_dir_summ_apply");
}

INT zykelind_hoch_dir_summ(a,c,b) OP a,b,c;
/* Berechnet den Zykelindex b als c-fache direkte Summe des Zykelindex
   a.  */
{
    INT erg=OK;
    CTO(POLYNOM,"zykelind_hoch_dir_summ(1)",a);
    CTO(INTEGER,"zykelind_hoch_dir_summ(2)",c);
    SYMCHECK(S_I_I(c)<0,"zykelind_hoch_dir_summ: exponent<0");
    erg+=hoch(a,c,b);
    ENDR("zykelind_hoch_dir_summ");
}

INT zykelind_hoch_dir_prod(a,c,b) OP a,b,c;
/* Berechnet den Zykelindex b als c-faches direktes Produkt 
   des Zykelindex a.  */
{
    INT erg=OK;
    CTO(POLYNOM,"zykelind_hoch_dir_prod(1)",a);
    CTO(INTEGER,"zykelind_hoch_dir_prod(2)",c);
    SYMCHECK(S_I_I(c)<0,"zykelind_hoch_dir_prod(2) negativ");
    FREESELF(b);
    if (nullp(c))
         return M_I_I(1L,b); 
    else if (einsp(c)) 
         return copy(a,b);
    else    {
            OP n = callocobject();
            OP d = callocobject();
            erg+=copy(c,n);
            erg+=copy(a,b); 
            erg+=dec(n);  
            while (not nullp(n)) {
                erg+=zykelind_dir_prod(a,b,d);    
                erg+=dec(n);
                erg+=copy(d,b);
                }
            FREEALL(d);
            FREEALL(n);
        };
    ENDR("zykelind_hoch_dir_prod");
}

INT eval_polynom_dir_prod(a,v,c) OP a,v,c;
{
    INT i;
    INT erg=OK;
    OP monom,hmonom,hmonom1;
    CTO(POLYNOM,"eval_polynom_dir_prod(1)",a);
    hmonom=callocobject();
    hmonom1=callocobject();
    monom=a;
    erg+=m_i_i(0l,c);
    while (monom!=NULL)
    {
      erg+=m_iindex_monom(0L,hmonom1);
      for (i=0L;i<S_V_LI(S_PO_S(monom));++i)
      {
        if (!nullp(S_PO_SI(monom,i)))
        {
          erg+=zykelind_hoch_dir_prod(S_V_I(v,i),S_PO_SI(monom,i),hmonom);
          erg+=zykelind_dir_prod_apply(hmonom,hmonom1);
        }
      }
      erg+=mult_apply(S_PO_K(monom),hmonom1);
      erg+=add_apply(hmonom1,c);
      monom=S_PO_N(monom);
    }
    erg+=freeall(hmonom); 
    erg+=freeall(hmonom1);
    ENDR("eval_polynom_dir_prod");
}

static INT zykeltyp_on_pairs_reduced(a,b) OP a,b;
/* Berechnet den Zykeltyp einer Permutation, auf der Menge aller
   geordneter Paare (i,j) mit i ungleich j.
   a ist ein Monom (der Zykeltyp der Permutation auf der Menge der 
   Punkte i,j,...)
   b ist ein Monom (der Zykeltyp, der durch obige Permutation 
   mit Zykeltyp a auf der Menge der Paare (i,j) mit i ungleich j 
   induziert wird.) */
{
    INT i1,i2,ex1,ex2;
    INT erg=OK;
    OP hilfmonom;
    if (S_O_K(a)!=POLYNOM) return error("zykeltyp_on_pairs_reduced(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfmonom=callocobject();
        erg+=m_scalar_polynom(S_PO_K(a),b);
        for (i1=0L; i1<S_V_LI(S_PO_S(a))-1L ; ++i1)
        {
          ex1=S_V_II(S_PO_S(a),i1);
          if (ex1 != 0L) 
          {
        for (i2=i1+1L; i2<S_V_LI(S_PO_S(a)); ++i2)
        {
          ex2=S_V_II(S_PO_S(a),i2);
          if (ex2 != 0L) 
          {
            erg+=m_iindex_iexponent_monom(((i1+1L)*(i2+1L)/ggt_i(i1+1L,i2+1L))-1L,2*ex1*ex2*ggt_i(i1+1L,i2+1L),hilfmonom);
            erg+=mult_apply(hilfmonom,b);
          }
        } 
          erg+=m_iindex_iexponent_monom(i1,ex1*((i1+1L)*ex1-1L),hilfmonom);
          erg+=mult_apply(hilfmonom,b);
          }
        } 
          i1=S_V_LI(S_PO_S(a))-1L;
          ex1=S_V_II(S_PO_S(a),i1);
          if (ex1 != 0L) 
          {
        erg+=m_iindex_iexponent_monom(i1,ex1*((i1+1L)*ex1-1L),hilfmonom);
        erg+=mult_apply(hilfmonom,b);
          } 
    erg+=freeall(hilfmonom);
    if (erg != OK) error(" in computation of zykeltyp_on_pairs_reduced(a,b) ");
    return(erg);
}

INT zykelind_on_pairs_reduced(a,b)  
/* Berechnet aus dem Zykelindex a den Zykelindex b 
   der auf der Menge der geordneten Paare (i,j) mit i
   ungleich j induzierten Gruppenaktion, die durch die
   zu a gehoerende Gruppenaktion definiert wird. */
    OP a,b;
{
    OP hilfk,monom1,monom3;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_pairs_reduced(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=zykeltyp_on_pairs_reduced(monom1,monom3);
      erg+=add_apply(monom3,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk); erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_pairs_reduced(a,b) ");
    return(erg);
}

INT zykelind_on_pairs(a,b)  
/* Berechnet aus dem Zykelindex a den Zykelindex b 
   der auf der Menge der geordneten Paare (i,j) [ auch Paare 
   der Form (i,i) ] induzierten Gruppenaktion, die durch die
   zu a gehoerende Gruppenaktion definiert wird. */
    OP a,b;
{
    OP hilfk,hilfmonom,monom1,monom3;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_pairs(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    hilfmonom=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=zykeltyp_on_pairs_reduced(monom1,monom3);
      erg+=m_skn_po(s_po_s(monom1),cons_eins,NULL,hilfmonom);
      erg+=mult_apply(hilfmonom,monom3);
      erg+=add(b,monom3,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk); erg+=freeall(hilfmonom); erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_pairs(a,b) ");
    return(erg);
}

INT zykelind_on_pairs_disjunkt(a,bb)  OP a,bb;
/* Berechnet aus dem Zykelindex a den Zykelindex bb
   der auf der Menge der geordneten Paare (i,j) [ auch Paare 
   der Form (i,i) ] induzierten Gruppenaktion, die durch die
   zu a gehoerende Gruppenaktion definiert wird. Dabei werden fuer
   Kanten und Schlingen verschiedene Unbestimmte verwendet. 
   s_mz_v(bb) ist ein Vektor Objekt, das die Stelle angibt, an der die 
   zwei Familien von Unbestimmten beginnen. Das heisst:
   s_v_ii(s_mz_v(bb),0L) entspricht dem Index der Unbestimmten x_1 und 
   s_v_ii(s_mz_v(bb),1L) entspricht dem Index der Unbestimmten y_1, 
   wobei die 
   Familie der Unbestimmten x_i zu den Kanten und die Familie der y_i
   zu den Schlingen gehoeren.  */
{
    OP hilfk,hilfmonom,monom1,monom3,monom4,vekt;
    OP b,c;
    INT i1,i2,ex1,ex2;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_pairs_disjunkt(a,b) a not POLYNOM");
    if (not EMPTYP(bb)) erg+=freeself(bb);
    hilfk=callocobject();
    hilfmonom=callocobject();
    monom3=callocobject();
    monom4=callocobject();
    b=callocobject();
    c=callocobject();
    vekt=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    erg+=numberofvariables(a,hilfk);
    erg+=m_il_v(2L,c);
    M_I_I(0L,S_V_I(c,0L));
    erg+=copy(hilfk,S_V_I(c,1L));
    monom1=a;
    while (monom1!=NULL)
    { 
          erg+=zykeltyp_on_pairs_reduced(monom1,monom3);
          erg+=copy(S_PO_S(monom1),vekt);
          while (S_V_LI(vekt)<S_I_I(hilfk))
          {
         erg+=inc(vekt);
         M_I_I(0L,S_V_I(vekt,S_V_LI(vekt)-1L));
          }
          erg+=m_skn_po(vekt,cons_eins,NULL,hilfmonom);
          /*if (S_O_K(S_PO_S(hilfmonom))==INTEGERVECTOR) C_O_K(S_PO_S(hilfmonom),VECTOR);*/
          erg+=mult_disjunkt_polynom_polynom(hilfmonom,monom3,monom4);
          /*if (S_O_K(S_PO_S(monom4))==INTEGERVECTOR) C_O_K(S_PO_S(monom4),VECTOR);*/
          erg+=add(b,monom4,b);
          monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk); erg+=freeall(hilfmonom); erg+=freeall(monom3);
    erg+=freeall(monom4); erg+=freeall(vekt);
    m_v_po_mz(c,b,bb);
    erg+=freeall(b); erg+=freeall(c);
    if (erg != OK) error(" in computation of zykelind_on_pairs_disjunkt(a,b) ");
    return(erg);
}

static INT zykeltyp_on_2sets(a,b) OP a,b;
/* Berechnet den Zykeltyp einer Gruppenaktion, auf der Menge aller
   2 elementigen Teilmengen {i,j}.
   a ist ein Monom (der Zykeltyp der Permutation auf der Menge der 
   Punkte i,j,...)
   b ist ein Monom (der Zykeltyp der durch obige Permutation 
   mit Zykeltyp a auf der Menge der 2-elementigen Mengen 
   induziert wird.) */
{
    INT i1,i2,ex1,ex2;
    OP hilfmonom,hilf,hilf1;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykeltyp_on_2sets(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilf=callocobject();
    hilf1=callocobject();
    hilfmonom=callocobject();
    erg+=m_scalar_polynom(S_PO_K(a),b);
    for (i1=0L; i1<S_V_LI(S_PO_S(a))-1L ; ++i1)
    {
      ex1=S_V_II(S_PO_S(a),i1);
      if (ex1 != 0L) 
      {
        for (i2=i1+1L; i2<S_V_LI(S_PO_S(a)); ++i2)
        {
          ex2=S_V_II(S_PO_S(a),i2);
          if (ex2 != 0L) 
          {
        erg+=m_iindex_iexponent_monom(((i1+1L)*(i2+1L)/ggt_i(i1+1L,i2+1L))-1L,ex1*ex2*ggt_i(i1+1L,i2+1L),hilfmonom);
        erg+=mult_apply(hilfmonom,b);
          }
        } 
        if (ex1>=2L)
        {
          M_I_I(ex1,hilf);
          erg+=binom(hilf,cons_zwei,hilf1);
          erg+=m_iindex_iexponent_monom(i1,(i1+1L),hilfmonom);
          erg+=hoch(hilfmonom,hilf1,hilfmonom);
          erg+=mult_apply(hilfmonom,b);
        }
        if (i1 % 2L == 0L) 
        erg+=m_iindex_iexponent_monom(i1,ex1*i1/2L,hilfmonom);
        else
        {
          erg+=m_iindex_iexponent_monom(i1,ex1*((i1+1L)/2L-1L),hilfmonom);
          erg+=m_iindex_iexponent_monom((i1+1L)/2L-1L,ex1,hilf1);
          erg+=mult_apply(hilf1,hilfmonom);
        }    
        erg+=mult_apply(hilfmonom,b);
      }
    } 
    i1=S_V_LI(S_PO_S(a))-1L;
    ex1=S_V_II(S_PO_S(a),i1);
    if (ex1 != 0L) 
    {
      if (ex1>=2L)
      {
        M_I_I(ex1,hilf);
        erg+=binom(hilf,cons_zwei,hilf1);
        erg+=m_iindex_iexponent_monom(i1,(i1+1L),hilfmonom);
        erg+=hoch(hilfmonom,hilf1,hilfmonom);
        erg+=mult_apply(hilfmonom,b);
      }
      if (i1 % 2L == 0L) 
      erg+=m_iindex_iexponent_monom(i1,ex1*i1/2L,hilfmonom);
      else
      {
        erg+=m_iindex_iexponent_monom(i1,ex1*((i1+1L)/2L-1L),hilfmonom);
        erg+=m_iindex_iexponent_monom((i1+1L)/2L-1L,ex1,hilf1);
        erg+=mult_apply(hilf1,hilfmonom);
      }    
      erg+=mult_apply(hilfmonom,b);
    } 
    erg+=freeall(hilf); erg+=freeall(hilf1); erg+=freeall(hilfmonom);
    if (erg != OK) error(" in computation of zykeltyp_on_2sets(a,b) ");
    return(erg);
}

INT zykelind_on_2sets(a,b)  OP a,b;
/* Berechnet aus dem Zykelindex a den Zykelindex b 
   der auf der Menge aller 2-elementigen Teilmengen 
   induzierten Gruppenaktion, die durch die
   zu a gehoerende Gruppenaktion definiert wird. */
{
    OP hilfk,monom1,monom3;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_2sets(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    monom1=a;
    while (monom1!=NULL)
    { 
        erg+=zykeltyp_on_2sets(monom1,monom3);
        erg+=add_apply(monom3,b);
        monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk); erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_2sets(a,b) ");
    return(erg);
}

INT zykelind_superp_lin_dir_graphs(a,bb) OP a,bb;
/* Berechnet den Zyklenzeiger der Gruppenaktion von S_n auf der Menge
   aller Paare (i,j) mit i ungleich j (Kanten eines gerichteten
   Graphen) und auf der Menge aller 2-elementigen Teilmengen von
   {1,2,...,n} (Kanten eines linearen Graphen). 
   Die entsprechenden Zykelverzeichnisse werden dabei
   mit verschiedenen Familien von Unbestimmten versehen.
   a ist ein Integer Objekt, das den Wert von n (Anzahl der Knoten
   der Graphen) angibt. bb ist der errechnete Zyklenzeiger, also
   ein 2-dimensionaler Zykelindex. c=s_mz_v(bb) ist ein Vektor Objekt. 
   Die (zwei) Eintragungen
   von c definieren die Stellen in dem Polynomobjekt an denen eine 
   neue Familie von Unbestimmten beginnt. (Somit ist der erste Wert
   von c gleich 0. Den zweiten Wert kann man in diesem Fall stets 
   gleich (a ueber 2) setzen.)  */
{
    OP b,c,d,cc,hilfmonom,monom1,monom2,monom3,monom4,vekt;
    INT i1,i2,ex1,ex2;
    INT erg=OK;
    if (S_O_K(a)!=INTEGER) return error("zykelind_superp_lin_dir_graphs(a,b) a not INTEGER");
    if (not EMPTYP(bb)) erg+=freeself(bb);
    d=callocobject();
    cc=callocobject();
    b=callocobject();
    c=callocobject();
    hilfmonom=callocobject();
    monom2=callocobject();
    monom3=callocobject();
    monom4=callocobject();
    vekt=callocobject();
    erg+=zykelind_Sn(a,d);
    erg+=m_scalar_polynom(cons_null,b);
    erg+=m_il_v(2L,c);
    M_I_I(0L,S_V_I(c,0L));
    erg+=binom(a,cons_zwei,cc);
    erg+=copy(cc,S_V_I(c,1L));
    monom1=d;
    while (monom1!=NULL)
    { 
      erg+=zykeltyp_on_pairs_reduced(monom1,monom3);
      erg+=zykeltyp_on_2sets(monom1,monom2);
      erg+=copy(S_PO_S(monom2),vekt);
      while (S_V_LI(vekt)<S_I_I(cc))
      {
         erg+=inc(vekt);
         M_I_I(0L,S_V_I(vekt,S_V_LI(vekt)-1L));
      }
      erg+=m_skn_po(vekt,cons_eins,NULL,hilfmonom);
      erg+=mult_disjunkt_polynom_polynom(hilfmonom,monom3,monom4);
      erg+=add_apply(monom4,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfmonom); erg+=freeall(monom2); erg+=freeall(monom3);
    erg+=freeall(monom4); erg+=freeall(vekt); erg+=freeall(d);
    erg+=freeall(cc);
    m_v_po_mz(c,b,bb);
    erg+=freeall(b); erg+=freeall(c);
    if (erg != OK) error(" in computation of zykelind_superp_lin_dir_graphs(a,b) ");
    return(erg);
}

INT zykelind_on_pairs_oriented(a,b)  OP a,b;
/* Berechnet aus dem Zykelindex a den Zykelindex b 
   der auf der Menge der geordneten Paare (i,j) mit i
   ungleich j induzierten Gruppenaktion, die durch die
   zu a gehoerende Gruppenaktion definiert wird. 
   Falls das Paar (i,j) auftritt, darf das Paar (j,i)
   jedoch nicht vorkommen. */
{
    OP hilfk,monom1,monom3;
    INT i1;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_pairs_oriented(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=zykeltyp_on_2sets(monom1,monom3);
      for (i1=0L;(2L*i1+1L<S_V_LI(S_PO_S(monom1))) && (i1<S_V_LI(S_PO_S(monom3)));++i1)
      C_I_I(S_V_I(S_PO_S(monom3),i1),S_V_II(S_PO_S(monom3),i1)-S_V_II(S_PO_S(monom1),2L*i1+1L));
          erg+=add_apply(monom3,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk);
    erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_pairs_oriented(a,b) ");
    return(erg);
}

INT zykelind_on_power_set(a,b) OP a,b;
/* Berechnet den Zykelindex der auf der Potenzmenge induzierten 
   Gruppenaktion. a ist der Zykelindex der urspruenglichen 
   Gruppenaktion. b ist der induzierte Zykelindex. */
{
    OP hilfk,hilf1,monom1,monom2,monom3,teiler,hilf,zwei,verz;
    INT i,j,n;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_power_set(a,b) a not POLYNOM");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    teiler=callocobject();
    verz=callocobject();
    zwei=callocobject();
    hilf1=callocobject();
    hilf=callocobject();
    monom2=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    erg+=numberofvariables(a,hilfk);
    erg+=m_l_v(hilfk,zwei);
    for (i=0L;i<S_V_LI(zwei);++i) M_I_I(2L,S_V_I(zwei,i));
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=m_scalar_polynom(S_PO_K(monom1),monom3);
      erg+=ordnung(monom1,hilfk);
      erg+=alle_teiler(hilfk,teiler);
      erg+=m_il_v(S_V_LI(teiler),verz);
      /* verz enthaelt gewisse Informationen ueber jeden 
      Teiler der in teiler aufgelistet ist. */
      for (i=0L;i<S_V_LI(teiler);++i)
      {
        erg+=zykeltyp_pi_hoch(S_PO_S(monom1),S_V_I(teiler,i),monom2);
        erg+=eval_polynom(monom2,zwei,hilf1);
        erg+=copy(hilf1,S_V_I(verz,i));
      }
      for (i=0L;i<S_V_LI(teiler);++i)
      {
        M_I_I(0L,hilfk);
        for (j=0L;j<=i;++j)
        {
          erg+=quores(S_V_I(teiler,i),S_V_I(teiler,j),hilf,hilf1);
          if (nullp(hilf1))
          {
        M_I_I(mu(hilf),hilf1);
        erg+=mult(hilf1,S_V_I(verz,j),hilf1);
        erg+=add(hilfk,hilf1,hilfk);
          }
        }
        erg+=ganzdiv(hilfk,S_V_I(teiler,i),hilfk);
        erg+=m_iindex_iexponent_monom(s_v_ii(teiler,i)-1L,s_i_i(hilfk),monom2); /* HF 130696 */
        erg+=mult(monom2,monom3,monom3);
      }
      erg+=add(b,monom3,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(zwei);
    erg+=freeall(verz);
    erg+=freeall(teiler);
    erg+=freeall(monom2);
    erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_power_set(a,b) ");
    return(erg);
}

static INT zykeltyp_on_ksubsets(a,c,b)
/* a ist der Zykeltyp einer Permutation. (ein Polynom Opbjekt)
c ist ein Integer Objekt, das den Wert von k enthaelt.
b ist der Zykeltyp einer Permutation auf k-elementigen Mengen, die 
durch Permutationen vom Typ a induziert wird. */
    OP a,b,c;
{
    OP hilfk,hilf,hilf1,teiler,verz,varanz,monom2;
    INT i,j;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykeltyp_on_ksubsets(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykeltyp_on_ksubsets(a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykeltyp_on_ksubsets(a,c,b) c<0");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    teiler=callocobject();
    verz=callocobject();
    varanz=callocobject();
    hilf1=callocobject();
    hilf=callocobject();
    monom2=callocobject();
    erg+=m_scalar_polynom(S_PO_K(a),b);
    erg+=ordnung(a,hilfk);
    erg+=alle_teiler(hilfk,teiler);
    erg+=m_il_v(S_V_LI(teiler),verz);
    /* verz enthaelt gewisse Informationen ueber jeden 
       Teiler der in teiler aufgelistet ist. */
    for (i=0L;i<S_V_LI(teiler);++i)
    {
      erg+=zykeltyp_pi_hoch(S_PO_S(a),S_V_I(teiler,i),monom2);
      erg+=numberofvariables(monom2,varanz);
      erg+=polya_sub(monom2,varanz,hilf1);
      erg+=coeff_of_in(c,hilf1,hilf);
      erg+=copy(hilf,S_V_I(verz,i));
    } 
    for (i=0L;i<S_V_LI(teiler);++i)
    {
      erg+=m_i_i(0L,hilfk);
      for (j=0L;j<=i;++j)
      {
        erg+=quores(S_V_I(teiler,i),S_V_I(teiler,j),hilf,hilf1);
        if (nullp(hilf1))
        {
          erg+=m_i_i(mu(hilf),hilf1);
          erg+=mult_apply(S_V_I(verz,j),hilf1);
          erg+=add_apply(hilf1,hilfk);
        }
      }
      erg+=ganzdiv(hilfk,S_V_I(teiler,i),hilfk);
      erg+=m_iindex_iexponent_monom(s_v_ii(teiler,i)-1L,cons_eins,monom2); /*HF 130696 */
      copy(hilfk,S_PO_SI(monom2,S_V_II(teiler,i)-1L));
      erg+=mult_apply(monom2,b);
    }
    erg+=freeall(hilfk);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(varanz);
    erg+=freeall(verz);
    erg+=freeall(teiler);
    erg+=freeall(monom2);
    if (erg != OK) error(" in computation of zykeltyp_on_ksubsets(a,c,b) ");
    return(erg);
}

INT zykelind_on_ksubsets(a,c,b) OP a,b,c;
/* a ist ein Zykelindex. Die dazu gehoerende Gruppenaktion induziert
   eine Gruppenaktion auf der Menge aller k-elementigen Teilmengen. 
   Der Parameter k wird im Integer Objekt c uebergeben. b ist der
   induzierte Zykelindex. */
{
    OP hilfk,monom1,monom3;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_ksubsets(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykelind_on_ksubsets(a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykelind_on_ksubsets(a,c,b) c<0");
    if (not EMPTYP(b)) erg+=freeself(b);
    monom3=callocobject();
    erg+=m_scalar_polynom(cons_null,b);
    monom1=a;
    while (monom1!=NULL)
      { 
        erg+=zykeltyp_on_ksubsets(monom1,c,monom3);
        erg+=add_apply(monom3,b);
        monom1=S_PO_N(monom1);
    }
    erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_ksubsets(a,c,b) ");
    return(erg);
}

static INT zykeltyp_on_ktuples(a,c,b) OP a,b,c;
{
    OP hilfk,hilfmonom,vekt,exponenten,hilf,hilf1,hilf2;
    INT i1,i2;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykeltyp_on_ktuples(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykeltyp_on_ktuples(a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykeltyp_on_ktuples(a,c,b) c<0");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    vekt=callocobject();
    exponenten=callocobject();
    hilfmonom=callocobject();
    erg+=m_l_v(c,exponenten);
        erg+=m_scalar_polynom(S_PO_K(a),b);
        erg+=copy(S_V_L(S_PO_S(a)),hilfk);
        while(nullp(S_V_I(S_PO_S(a),S_I_I(hilfk)-1L)))
         erg+=dec(hilfk);
        erg+=dec(hilfk);
        erg+=erster_kandidat(S_I_I(c),vekt);
        do
        {  
          for (i1=0L;i1<S_V_LI(vekt);++i1)
          {
        if (!nullp(S_V_I(S_PO_S(a),S_V_II(vekt,i1))))
        erg+=copy(S_V_I(S_PO_S(a),S_V_II(vekt,i1)),S_V_I(exponenten,i1));
        else 
        {
          for (i2=i1+1L;i2<S_V_LI(vekt);++i2)
             erg+=copy(hilfk,S_V_I(vekt,i2));
          goto label;
        }
          }
          erg+=vektor_prod(exponenten,hilf);
          erg+=vektor_kgv_prod_durch_kgv(vekt,hilf1,hilf2);
          erg+=m_iindex_iexponent_monom(s_i_i(hilf1)-1L,1L,hilfmonom);
          erg+=mult(hilf,hilf2,S_PO_SI(hilfmonom,s_i_i(hilf1)-1L));
          erg+=mult_apply(hilfmonom,b);
          label: i1=next_kandidat(S_I_I(hilfk),vekt);
        } while(i1==1L);
    /*if (S_O_K(S_PO_S(b))==INTEGERVECTOR) C_O_K(S_PO_S(b),VECTOR);*/
    erg+=freeall(hilfk);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    erg+=freeall(vekt);
    erg+=freeall(exponenten);
    erg+=freeall(hilfmonom);
    if (erg != OK) error(" in computation of zykeltyp_on_ktuples(a,c,b) ");
    return(erg);
}

INT zykelind_on_ktuples(a,c,b)  
/* Berechnet aus dem Zykelindex a den Zykelindex b 
   der auf der Menge aller c-Tupel induzierten Gruppenaktion, 
   die durch die zu a gehoerende Gruppenaktion definiert wird. */
    OP a,b,c;
{
    OP monom1,monom3;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_ktuples(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykelind_on_ktuples(a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykelind_on_ktuples(a,c,b) c<0");
    if (not EMPTYP(b)) erg+=freeself(b);
    if (einsp(c)) return(copy(a,b));
    monom3=callocobject();
    erg+=m_scalar_polynom(cons_null,b);
    monom1=a;
    while (monom1!=NULL)
    { 
        erg+=zykeltyp_on_ktuples(monom1,c,monom3);
        /*if (S_O_K(S_PO_S(monom3))==INTEGERVECTOR) C_O_K(S_PO_S(monom3),VECTOR);*/
        erg+=add(b,monom3,b);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_on_ktuples(a,c,b) ");
    return(erg);
}

INT zykelind_on_ktuples_injective(a,c,b) OP a,b,c;
{
    OP monom1,monom2,monom3,monom4,hilfk,stirling,koeff;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_on_ktuples_injective(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykelind_on_ktuples_injective(a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykelind_on_ktuples_injective(a,c,b) c<0");
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    koeff=callocobject();
    monom2=callocobject();
    monom3=callocobject();
    monom4=callocobject();
    stirling=callocobject();
    erg+=stirling_first_tafel(c,stirling);
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,b);
    monom1=a;
    while (monom1!=NULL)
      { 
        erg+=m_skn_po(S_PO_S(monom1),S_PO_K(monom1),NULL,monom2);
        erg+=vektor_mult_apply(S_PO_S(monom2),S_M_IJ(stirling,S_I_I(c),1L));
        for (i=2L;i<=S_I_I(c);++i)
        {
          M_I_I(i,hilfk);
          erg+=zykeltyp_on_ktuples(monom1,hilfk,monom3);
          erg+=vektor_mult_apply(S_PO_S(monom3),S_M_IJ(stirling,S_I_I(c),i));
          erg+=add_apply_vector(S_PO_S(monom3),S_PO_S(monom2));
        }
        /*if (S_O_K(S_PO_S(monom2))==INTEGERVECTOR) C_O_K(S_PO_S(monom2),VECTOR);*/
        erg+=add(b,monom2,b);
        monom1=S_PO_N(monom1);
    }
    erg+=freeall(stirling);
    erg+=freeall(hilfk);
    erg+=freeall(koeff);
    erg+=freeall(monom2);
    erg+=freeall(monom3);
    erg+=freeall(monom4);
    if (erg != OK) error(" in computation of zykelind_on_ktuples_injective(a,c,b) ");
    return(erg);
}

INT zykelind_test()
/* Test fuer die in diesem File auftretenden Prozeduren. */
{
    OP a,b,c,d,e;
    INT erg=OK;
    a=callocobject();
    b=callocobject();
    c=callocobject();
    d=callocobject();
    e=callocobject();
    printeingabe("Geben Sie eine Integer Zahl n an (etwa 1<=n<=5).");
    printeingabe("Aus dem Zyklenzeiger von S_n werden weitere Zyklenzeiger bestimmt.");
    scan(INTEGER,a);
    erg+=zykelind_Sn(a,b);
    printf("Zyklenzeiger von S_n\n");
    erg+=println(b);
    erg+=zykelind_on_2sets(b,c);
    printf("Zyklenzeiger auf 2-Mengen\n");
    erg+=println(c);
    erg+=zykelind_on_pairs(b,d);
    printf("Zyklenzeiger auf Paaren\n");
    erg+=println(d);
    erg+=zykelind_dir_prod(c,d,e);
    printf("Direktes Produkt dieser 2 Zyklenzeiger\n");
    erg+=println(e);
    erg+=zykelind_dir_summ(c,d,e);
    printf("Direkte Summe dieser 2 Zyklenzeiger\n");
    erg+=println(e);
    zykelind_Cn(a,d);
    erg+=zykelind_kranz(b,d,e);
    printf("Kranzprodukt von S_n mit C_n\n");
    erg+=println(e);
    erg+=zykelind_on_power_set(b,c);
    printf("Zyklenzeiger auf der Potenzmenge\n");
    erg+=println(c);
    printeingabe("Geben Sie eine weitere Integer Zahl k an. ");
    printeingabe("Es werden nun Zyklenzeiger von k-Tupeln und k-Mengen bestimmt.");
    scan(INTEGER,c);
    erg+=zykelind_on_ktuples(b,c,d);
    printf("Zyklenzeiger auf k-Tupeln\n");
    erg+=println(d);
    erg+=zykelind_on_ktuples_injective(b,c,d);
    printf("Zyklenzeiger auf injektiven k-Tupeln\n");
    erg+=println(d);
    erg+=zykelind_on_ksubsets(b,c,d);
    printf("Zyklenzeiger auf k-Mengen\n");
    erg+=println(d);
    erg+=zykelind_hoch_dir_summ(b,c,d);
    printf("Zyklenzeiger direkte Summe hoch k\n");
    erg+=println(d);
    erg+=zykelind_hoch_dir_prod(b,c,d);
    printf("Zyklenzeiger direktes Produkt hoch k\n");
    erg+=println(d);
    erg+=zykelind_on_pairs_reduced(b,c);
    printf("Zyklenzeiger auf injektiven Paaren\n");
    erg+=println(c);
    erg+=zykelind_on_pairs_oriented(b,c);
    printf("Zyklenzeiger auf orientierten Paaren\n");
    erg+=println(c);
    printf("Spezielle Form der Polyasubstitution\n");
    erg+=numberofvariables(c,d);
    erg+=polya1_sub(c,d,e);
    erg+=println(e);
    erg+=zykelind_on_pairs_disjunkt(b,c);
    printf("Zyklenzeiger auf Paaren mit getrennten Familien von Unbestimmten\n");
    erg+=println(s_mz_po(c));
    printf("Die Familien beginnen bei den Indizes:\n");
    erg+=println(s_mz_v(c));
    erg+=zykelind_superp_lin_dir_graphs(a,c);
    printf("Zyklenzeiger fuer Superpositionen von einem linearen\n");
    printf("und einem gerichteten Graphen\n");
    erg+=println(s_mz_po(c));
    printf("Die Familien beginnen bei den Indizes:\n");
    erg+=println(s_mz_v(c));
    erg+=zykelind_inc(b);
    printf("Einbettung in S_{n+1}\n");
    erg+=println(b);
    M_I_I(2L,a);
    erg+=zykelind_Sn(a,b);
    printf("Zyklenzeiger der S2\n");
    erg+=println(b);
    M_I_I(4L,a);
    erg+=zykelind_Sn(a,c);
    printf("Zyklenzeiger der S4\n");
    erg+=println(c);
    erg+=zykelind_dir_summ(b,c,d);
    printf("Zyklenzeiger von S2 x S4\n");
    erg+=println(d);
    erg+=m_il_v(2L,e);
    erg+=copy(d,s_v_i(e,1L));
    M_I_I(6L,a);
    erg+=zykelind_Dn(a,b);
    printf("Zyklenzeiger der D6\n");
    erg+=println(b);
    erg+=numberofvariables(b,a);
    polya_sub(b,a,c);
    printf("Polya-Substitution\n");
    println(c);
    erg+=copy(b,s_v_i(e,0L));
    erg+=redf_cup(e,d);
    printf("Redfield Cup\n");
    erg+=println(d);
    erg+=redf_cap(e,d);
    printf("Redfield Cap\n");
    erg+=println(d);
    printf("Dies ist der Koeffizient von x^2 bei obiger Polya-Substitution\n");
    erg+=zykelind_tetraeder(c);
    printf("Zyklenzeiger der Drehgruppe des Tetraeders\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Tetraeders\n");
    erg+=println(c);
    erg+=zykelind_cube(a);
    erg+=polya_multi_sub(a,c);
    printf("Moegliche Faerbungen der Ecken, Kanten und Flaechen eines Wuerfels\n");
    printf("mit jeweils 2 Farben bezueglich der Drehsymmetrie des Wuerfels.\n");
    erg+=println(c);
    erg+=m_il_v(3L,c);
    M_I_I(8L,s_v_i(c,0L));
    M_I_I(12L,s_v_i(c,1L));
    M_I_I(6L,s_v_i(c,2L));
    erg+=polya_multi_const_sub(a,c,d);
    printf("Anzahl der moeglichen Faerbungen der Ecken, Kanten und Flaechen eines\n ");
    printf("Wuerfels mit 8, 12, bzw. 6 Farben bezueglich der Drehsymmetrie \n");
    printf("des Wuerfels.\n");
    erg+=println(d);
    erg+=zykelind_cube_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Wuerfels\n");
    erg+=println(c);
    erg+=zykelind_dodecahedron_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Dodecaeders\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_vertices(c);
    printf("Zyklenzeiger der Drehgruppe des Tetraeders auf den Ecken\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_edges(c);
    printf("Zyklenzeiger der Drehgruppe des Tetraeders auf den Kanten\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_faces(c);
    printf("Zyklenzeiger der Drehgruppe des Tetraeders auf den Flaechen\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_vertices_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Tetraeders auf den Ecken\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_edges_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Tetraeders auf den Kanten\n");
    erg+=println(c);
    erg+=zykelind_tetraeder_faces_extended(c);
    printf("Zyklenzeiger der Symmetriegruppe des Tetraeders auf den Flaechen\n");
    erg+=println(c);
    M_I_I(4L,b);
    erg+=polya_const_sub(c,b,d);
    printf("Anzahl der verschiedenen Faerbungen der Flaechen eines Tetraeders\n");
    printf("mit 4 Farben bezueglich der gesamten Symmetriegruppe des Tetraeders.\n");
    erg+=println(d);
    erg+=zykelind_test1();
    erg+=freeall(a);
    erg+=freeall(b);
    erg+=freeall(c);
    erg+=freeall(d);
    erg+=freeall(e);
    if (erg != OK) error(" in computation of zykelind_test() ");
    return(erg);
}

INT zykelind_inc(a) OP a;
/* Natuerliche Einbettung von einer Gruppenaktion von einer Untergruppe
   von S_n in S_{n+1}.  */
{
    OP hilfmonom;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_inc(a) a not POLYNOM");
    hilfmonom=callocobject();
    erg+=m_iindex_iexponent_monom(0L,1L,hilfmonom);
    erg+=mult(a,hilfmonom,a);
    erg+=freeall(hilfmonom);
    ENDR("zykelind_inc");
}

INT zykelind_dec(a,b) OP a,b;
{
    OP hilfm,hilf,hilf1;
    INT erg=OK;
    hilf=callocobject();
    hilf1=callocobject();
    M_I_I(0L,hilf);
    erg+=m_scalar_polynom(hilf,b);
    hilfm=a;
    while (hilfm!=NULL)
    {
      /*if (S_O_K(S_PO_S(hilfm))==INTEGERVECTOR) C_O_K(S_PO_S(hilfm),VECTOR);*/
      erg+=copy(S_PO_S(hilfm),hilf);
      erg+=dec(S_V_I(hilf,0L));
      erg+=m_skn_po(hilf,S_PO_K(hilfm),NULL,hilf1);
      erg+=add_apply(hilf1,b);
      hilfm=S_PO_N(hilfm);
    }
    erg+=freeall(hilf1);
    erg+=freeall(hilf);
    if (erg!=OK) error("in computation of zykelind_dec(a,b) ");
    return(erg);
}

INT zykelind_dec_apply(a) OP a;
{
    OP hilf;
    INT erg=OK;
    hilf=callocobject();
    erg+=zykelind_dec(a,hilf);
    erg+=copy(hilf,a);
    erg+=freeall(hilf);
    if (erg!=OK) error("in computation of zykelind_dec_apply(a) ");
    return(erg);
}

/* ***************************************************************

Computation of the cycle index of the composition and plethysm
of two permutation groups.

****************************************************************** */

static INT zykelind_index_verschieben(a,b,c) OP a,b,c;
/* a ist urspruenglicher Zykelindex;
   c ist der neue Zykelindex: es wird dabei x_i aus a ersetzt
   durch x_{bi}. b ist ein integer Objekt.  */
{
    OP hilfk,hilfmonom,monom1,monom3;
    INT i1,ib,ex1;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("zykelind_index_verschieben(a,b,c) a not POLYNOM");
    if (S_O_K(b)!=INTEGER) return error("zykelind_index_verschieben(a,b,c) b not INTEGER");
    if (not EMPTYP(c)) erg+=freeself(c);
    hilfk=callocobject();
    hilfmonom=callocobject();
    monom3=callocobject();
    M_I_I(0L,hilfk);
    erg+=m_scalar_polynom(hilfk,c);
    ib=S_I_I(b);
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=m_scalar_polynom(S_PO_K(monom1),monom3);
      for (i1=0L; i1<S_V_LI(S_PO_S(monom1)) ; ++i1)
      {
        ex1=S_V_II(S_PO_S(monom1),i1);
        if (ex1 != 0L) 
        {
          erg+=m_iindex_iexponent_monom((i1+1L)*ib-1L,ex1,hilfmonom);
          erg+=mult_apply(hilfmonom,monom3);
        }
      } 
      erg+=add_apply(monom3,c);
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilfk);
    erg+=freeall(hilfmonom);
    erg+=freeall(monom3);
    if (erg != OK) error(" in computation of zykelind_index_verschieben(a,b,c) ");
    return(erg);
}

INT zykelind_kranz(a,b,c) OP a,b,c;
/* Berechnet den Zyklenzeiger der Gruppenaktion des Kranzproduktes
   zweier Gruppen. a ist der erste Zyklenzeiger. In diesem ersetzt
   man x_i durch den Zyklenzeiger der zweiten Gruppenaktion, dessen
   Unbestimmte y_j durch y_{ij} zu ersetzen sind. Das Ergebnis dieser
   Substitutionen ist der neue Zyklenzeiger c. */
/* HF */
/* AK 251198 V2.0 */
{
    OP varanz,substitut,hilf,hilfpoly;
    INT i;
    INT erg=OK;
    CTO(POLYNOM,"zykelind_kranz",a);
    CTO(POLYNOM,"zykelind_kranz",b);
    
    
    
    varanz=callocobject();
    substitut=callocobject();
    hilf=callocobject();
    hilfpoly=callocobject();
    numberofvariables(a,varanz);
    erg+=m_l_v(varanz,substitut);
    for (i=0L;i<S_I_I(varanz);++i)
    {
      M_I_I(i+1L,hilf);
      erg+=zykelind_index_verschieben(b,hilf,hilfpoly);
      erg+=copy(hilfpoly,S_V_I(substitut,i));
    }
    erg+=eval_polynom(a,substitut,c);
    erg+=freeall(varanz);
    erg+=freeall(substitut);
    erg+=freeall(hilf);
    erg+=freeall(hilfpoly);
    ENDR("zykelind_kranz");
}

INT zykelind_plethysm(a,b,c) OP a,b,c;
{
    return zykelind_kranz(b,a,c);
}

/* ***************************************************************

Computation of the cycle index of the exponentiation.

****************************************************************** */

INT zykelind_exponentiation(a,b,c) OP a,b,c;
{
    INT i;
    OP hilf=callocobject();
    OP hilf1=callocobject();
    OP v=callocobject();
    INT erg=OK;
    erg+=numberofvariables(a,hilf);
    erg+=m_l_v(hilf,v);
    erg+=m_i_i(1L,hilf1);
    for (i=0L;i<S_I_I(hilf);++i)
    {
      erg+=zykelind_operation_for_exp(hilf1,b,S_V_I(v,i));
      erg+=inc(hilf1);
    }
    erg+=eval_polynom_dir_prod(a,v,c);
    erg+=freeall(hilf); erg+=freeall(hilf1); erg+=freeall(v);
    ENDR("zykelind_exponentiation");
}

static INT zykelind_operation_for_exp(a,b,c) OP a,b,c;
{
    INT erg=OK;
    OP monom;
    OP hilfmonom=callocobject();
    OP hilf=callocobject();
    monom=b;
    erg+=m_i_i(0L,c);
    while (monom!=NULL)
    {
      erg+=zykeltyp_operation_for_exp(a,S_PO_S(monom),hilf);
      erg+=m_skn_po(hilf,S_PO_K(monom),NULL,hilfmonom);
      erg+=add_apply(hilfmonom,c);
      monom=S_PO_N(monom);
    }
    erg+=freeall(hilfmonom); erg+=freeall(hilf);
    if (erg!=OK) EDC("zykelind_operation_for_exp");
    return erg;
}

static INT zykeltyp_operation_for_exp(a,b,c) OP a,b,c;
{
    INT i,j,k,l;
    INT erg=OK;
    OP pow=callocobject();
    OP hilf=callocobject();
    OP hilf1=callocobject();
    OP hilf2=callocobject();
    OP hilf3=callocobject();
    OP hilf4=callocobject();
    OP hilf5=callocobject();
    OP teiler=callocobject();
    OP teiler1=callocobject();
    erg+=sum_vector1(b,hilf);
    erg+=hoch(hilf,a,pow);
    erg+=m_l_nv(pow,c);
    erg+=m_i_i(1L,hilf);
    for (i=0L;i<s_i_i(pow);++i)
    {
      erg+=alle_teiler(hilf,teiler);
      for (j=0L;j<S_V_LI(teiler);++j)
      {
       erg+=ganzdiv(hilf,S_V_I(teiler,j),hilf1);
       k=mu(hilf1);
       if (k!=0L)
       {
         erg+=ggt(a,S_V_I(teiler,j),hilf2);
         erg+=ganzdiv(S_V_I(teiler,j),hilf2,hilf3);
         erg+=alle_teiler(hilf3,teiler1);
         erg+=m_i_i(0L,hilf5);
         for (l=0L;l<S_V_LI(teiler1);++l)
         {
           if (le(S_V_I(teiler1,l),S_V_L(b)))
           {  
         erg+=mult(S_V_I(teiler1,l),S_V_I(b,S_V_II(teiler1,l)-1L),hilf4);
         erg+=add_apply(hilf4,hilf5);
           } 
         }
         erg+=hoch(hilf5,hilf2,hilf5);
         if (k>0L) erg+=add_apply(hilf5,S_V_I(c,i));
        else erg+=sub(S_V_I(c,i),hilf5,S_V_I(c,i));
       }
      }
      erg+=ganzdiv(S_V_I(c,i),hilf,S_V_I(c,i));
      erg+=inc(hilf);
    }
    erg+=freeall(hilf); erg+=freeall(hilf1); erg+=freeall(hilf2);
    erg+=freeall(hilf3); erg+=freeall(hilf4); erg+=freeall(hilf5); 
    erg+=freeall(pow); erg+=freeall(teiler); erg+=freeall(teiler1);
    if (erg!=OK) EDC("zykeltyp_operation_for_exp");
    return erg;
}

/* **************************************************************

The cycle indices of centralizers of permutations and
stabilizers of partitions.

****************************************************************** */

INT zykelind_centralizer(typ,res) OP typ,res;
/* Berechnet den Zyklenzeiger des Stabilisators einer Permutation, 
vom Zykeltyp typ.*/
{
    INT erg=OK;
    OP typv,typvv;
    OP a=callocobject();
    OP b=callocobject();
    OP c=callocobject();
    OP d=callocobject();
    INT i;
    INT j=0L;
    erg+=m_scalar_polynom(cons_eins,res);
    if (S_O_K(typ)==PERMUTATION)
    { 
      typv=callocobject();
      erg+=zykeltyp(typ,typv);
      t_VECTOR_EXPONENT(typv,typv); 
      typvv=S_PA_S(typv);
      j=1L;
    }
    else if (S_O_K(typ)==PARTITION)
    {
      if (S_PA_K(typ)==VECTOR)
      {
        typv=callocobject();
        t_VECTOR_EXPONENT(typ,typv);
        typvv=S_PA_S(typv);
        j=1L;
      }
      else typvv=S_PA_S(typ);
    }
    else if ((S_O_K(typ)==VECTOR) || (S_O_K(typ)==INTEGERVECTOR)) typvv=typ;
    else if (S_O_K(typ)==POLYNOM) typvv=S_PO_S(typ);
    else error("zykelind_centralizer(a,b) a wrong objectkind");
    for (i=0,M_I_I(1L,d);i<S_V_LI(typvv);++i,inc(d))
    {
      if (!nullp(S_V_I(typvv,i)))
      {
        erg+=zykelind_Cn(d,a);
        erg+=zykelind_Sn(S_V_I(typvv,i),b);
        erg+=zykelind_kranz(b,a,c);
        erg+=zykelind_dir_summ_apply(c,res);
      }
    }
    erg+=freeall(a);erg+=freeall(b);erg+=freeall(c);erg+=freeall(d);
    if (j==1L) erg+=freeall(typv);
    if (erg!=OK) return error("in computation of zykelind_centralizer(a,b)");
    return(erg);
}

INT zykelind_stabilizer_part(a,b) OP a,b;
/* a ist ein PARTITION Objekt vom Typ EXPONENT
   b ist der Zyklenzeiger des Stabilisators von a
*/
{
    if ((S_O_K(a)!=PARTITION) || (S_PA_K(a)!=EXPONENT))
    return error("zykelind_stabilizer_part(a,b) a is not a PARTITION of type EXPONENT");
    else
    {
    INT ret=OK;
    INT i;
    OP hilf=callocobject();
    OP hilf1=callocobject();
    OP hilf2=callocobject();
    OP hilf3=callocobject();
    m_i_i(1L,b);
    for (i=0L,M_I_I(1L,hilf);i<S_PA_LI(a);inc(hilf),++i)
    {
      if (!nullp(S_PA_I(a,i)))
      {
        ret+=zykelind_Sn(S_PA_I(a,i),hilf1);
        ret+=zykelind_Sn(hilf,hilf2);
        ret+=zykelind_kranz(hilf1,hilf2,hilf3);
        ret+=zykelind_dir_summ_apply(hilf3,b);
      }
    }
    ret+=freeall(hilf); ret+=freeall(hilf1); 
    ret+=freeall(hilf2); ret+=freeall(hilf3);
    if (ret!=OK) return error("in computation of zykelind_stabilizer_part(a,b)");
    return(ret);
    }
}

/* ****************************************************************

Some methods for computing the cycle indices of linear and affine
groups. Furthermore to compute the orders of these groups, the
number of irreducible polynomials of given degree over finite
fields. etc.

******************************************************************* */

INT ordnung_glkq(k,q,ord) OP k,q,ord;
/* Berechnet ord als die Ordnung der Gruppe GL(k,Fq)  */
{
    OP hilf,hilf1,hilf2;
    INT i;
    INT erg=OK;
    CTO(INTEGER,"ordnung_glkq(1)",k);
    SYMCHECK(S_I_I(k)<1,"ordnung_glkq:k<1");
    CTO(INTEGER,"ordnung_glkq(2)",q);
    CE3(k,q,ord,ordnung_glkq);
    FREESELF(ord);
    M_I_I(1L,ord);

    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    erg+=hoch(q,k,hilf);
    for (i=0L;i<S_I_I(k);++i)
    {
      erg+=m_i_i(i,hilf1);
      erg+=hoch(q,hilf1,hilf2);
      erg+=sub(hilf,hilf2,hilf1);
      MULT_APPLY(hilf1,ord);
    }
    FREEALL3(hilf,hilf1,hilf2);
    ENDR("ordnung_glkq");
}

INT ordnung_affkq(k,q,ord) OP k,q,ord;
/* Berechnet ord als die Ordnung der Gruppe Aff(k,Fq)  */
{
    OP hilf;
    INT i;
    INT erg=OK;
    if (S_O_K(k)!=INTEGER) return error("ordnung_affkq(k,q,ord) k not INTEGER");
    if (S_I_I(k)<1L) return error("ordnung_affkq(k,q,ord)  k<1");
    if (S_O_K(q)!=INTEGER) return error("ordnung_affkq(k,q,ord) q not INTEGER");
    if (!emptyp(ord)) freeself(ord);
    hilf=callocobject();
    erg+=ordnung_glkq(k,q,ord);
    erg+=hoch(q,k,hilf);
    erg+=mult_apply(hilf,ord);
    erg+=freeall(hilf);
    if (erg!=OK) error("  in computation of ordnung_affkq(k,q,ord)");
    return(erg);
}

INT kung_formel(d,lambda,q,anz) OP d,lambda,q,anz;
/* Berechnet anz nach einer Formel von J.P.Kung als die Anzahl der
Matrizen in GL(cd,Fq) die mit einer Matrix, die aus lambda(1)
Begleitmatrizen eines irreduziblen Polynoms p, lambda(2)
Hyperbegleitmarizen von p^2 usw. besteht.
Dabei ist d der Grad des Polynoms p, lambda eine Partition von c (das
ist die hoechste Potenz von p, die das charakteristische Polynom einer
Matrix teilt, von der D(p,lambda) ein Block ist), q die Maechtigkeit
des Koerpers und anz das Ergebnis.  */
{
    INT i,j;
    INT erg=OK;
    OP hilf,hilf1,hilf2,mu;
    if (S_O_K(d)!=INTEGER) return error("kung_formel(d,lambda,q,anz) d not INTEGER");
    if (S_I_I(d)<1L) return error("kung_formel(d,lambda,q,anz)  d<1");
    if (S_O_K(lambda)!=PARTITION) return error("kung_formel(d,lambda,q,anz) lambda not PARTITION");
    if (S_O_K(q)!=INTEGER) return error("kung_formel(d,lambda,q,anz) q not INTEGER");
    if (!emptyp(anz)) freeself(anz);
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    mu=callocobject();
    if (S_PA_K(lambda)==VECTOR) t_VECTOR_EXPONENT(lambda,lambda);
    M_I_I(0L,mu);
    M_I_I(1L,anz);
    for (i=0;i<S_PA_LI(lambda);++i)
    {
      for (j=i;j<S_PA_LI(lambda);++j)
      {
        erg+=add_apply(S_PA_I(lambda,j),mu);
      }
      erg+=mult(d,mu,hilf);
      erg+=hoch(q,hilf,hilf);
      for (j=1L;j<=S_PA_II(lambda,i);++j)
      {
        erg+=m_i_i(j,hilf1);
        erg+=sub(mu,hilf1,hilf2);
        erg+=mult_apply(d,hilf2);
        erg+=hoch(q,hilf2,hilf2);
        erg+=sub(hilf,hilf2,hilf1);
        erg+=mult_apply(hilf1,anz);
      }
    }
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    erg+=freeall(mu);
    if (erg!=OK) error(" in computation of kung_formel(d,lambda,q,anz)");
    return(erg);
}

static INT zykeltyp_poly_part(d,exp,mu,p,q,ergeb) OP d,exp,mu,p,q,ergeb;
/* Berechnet den Zykeltyp einer Blockdiagonalmatrix besthend aus
Begleit und Hyperbegleitmatrizen eines irreduziblen normierten Polynoms
vom Grad d, Exponenten (=Periode bzw. Ordnung) exp; Die Gestalt dieser
Matrix wird durch die Prtition mu festgelegt, p ist die Charakteristik
des Koerpers, q dessen Maechtigkeit, und ergeb ist der berechnete
Zykeltyp.  */
{
    INT i;
    INT erg=OK;
    OP hilf,hilf1;
    hilf=callocobject();
    hilf1=callocobject();
    erg+=m_iindex_monom(0L,ergeb);
    for (i=0L;i<S_PA_LI(mu);++i)
    {
      if (S_PA_II(mu,i)!=0L)
      {
        erg+=zykeltyp_hyperbegleitmatrix_poly(d,exp,i+1L,p,q,hilf);
        erg+=zykelind_hoch_dir_prod(hilf,S_PA_I(mu,i),hilf1);
        erg+=zykelind_dir_prod_apply(hilf1,ergeb);
      }
    }
    erg+=kung_formel(d,mu,q,hilf);
    erg+=invers_apply(hilf);
    erg+=m_scalar_polynom(hilf,hilf1);
    erg+=mult_apply(hilf1,ergeb);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    if (erg!=OK) error("in computation of zykeltyp_poly_part(d,exp,mu,p,q,ergeb) ");
    return(erg);
}

static INT zykeltyp_hyperbegleitmatrix_poly(d,exp,i,p,q,ergeb) OP d,exp,p,q,ergeb; INT i;
/* Bestimmt den Zykeltyp der Hyperbegleitmatrix von p(x)^i, einem
irreduziblen normierten Polynom vom Grad d mit Exponenten exp, ueber
einem Koerper von Charakteristik p und Maechtigkeit q. Das Ergebnis ist
ergeb*/
{
    OP e,hilf,hilf1,hilf2,hilfpoly;
    INT j,k;
    INT erg=OK;
    e=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    hilfpoly=callocobject();
    erg+=m_il_v(i,e);
    erg+=copy(exp,S_V_I(e,0L));
    k=1L;
    for (j=1L;j<i;++j)
    {
      erg+=copy(S_V_I(e,j-1L),S_V_I(e,j));
      if (k<j+1L)
      {
        k=k*s_i_i(p);
        erg+=mult_apply(p,S_V_I(e,j));
      }
    }
    erg+=m_iindex_monom(0L,ergeb);
    erg+=hoch(q,d,hilf);
    erg+=copy(hilf,hilf1);
    erg+=dec(hilf1);
    erg+=ganzdiv(hilf1,exp,hilf2);
    erg+=m_iindex_iexponent_monom(s_i_i(exp)-1L,s_i_i(hilf2),hilfpoly); /* HF130696 */
    erg+=mult_apply(hilfpoly,ergeb);
    for (j=1L;j<i;++j)
    {
      erg+=mult_apply(hilf,hilf1);
      erg+=ganzdiv(hilf1,S_V_I(e,j),hilf2);
      erg+=m_iindex_iexponent_monom(s_v_ii(e,j)-1L,s_i_i(hilf2),hilfpoly); /* HF130696 */
      erg+=mult_apply(hilfpoly,ergeb);
    }
    erg+=freeall(e);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    erg+=freeall(hilfpoly);
    if (erg!=OK) error("in computation of zykeltyp_hyperbegleitmatrix_poly(d,exp,i,p,q,ergeb) ");
    return(erg);
}

INT number_of_irred_poly_of_degree(d,q,ergeb) OP d,q,ergeb;
/* Berechnet die Anzahl der normierten, irreduziblen Polynome
vom Grad d uber dem Koerper F_q:  */
{
    OP hilf,hilf1;
    INT i,j;
    INT erg=OK;
    hilf=callocobject();
    hilf1=callocobject();
    if (!emptyp(ergeb)) erg+=freeself(ergeb);
    M_I_I(0L,ergeb);
    erg+=alle_teiler(d,hilf);
    for (i=0L;i<S_V_LI(hilf);++i)
    {
      erg+=ganzdiv(d,S_V_I(hilf,i),hilf1);
      erg+=hoch(q,hilf1,hilf1);
      j=mu(S_V_I(hilf,i));
      if (j>0L) erg+=add_apply(hilf1,ergeb);
      else 
      if (j<0L) erg+=sub(ergeb,hilf1,ergeb);
    }
    erg+=ganzdiv(ergeb,d,ergeb);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    if (erg!=OK) error("in computation of number_of_irred_poly_of_degree(d,q,ergeb) ");
    return(erg);
}

static INT exponenten_bestimmen(d,q,a,b) OP d,q,a,b;
{
    INT i,j,k,l;
    OP hilf,hilfv,dd,c,e,f,g,h,speicher;
    OP ax_e;
    INT erg=OK;
    hilf=callocobject();
    hilfv=callocobject();
    dd=callocobject();
    c=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    h=callocobject();
    speicher=callocobject();
    erg+=init(BINTREE,speicher);
    erg+=m_l_v(d,a);
    erg+=m_l_v(d,b);
    for (i=0L;i<S_I_I(d);++i)
    {
      M_I_I(i+1L,dd);
      erg+=m_il_v(0L,hilf);
      erg+=m_il_v(0L,hilfv);
      l=0L;
      erg+=hoch(q,dd,c);
      erg+=dec(c);
      erg+=alle_teiler(c,e);
      for (j=0L;j<S_V_LI(e);++j)
      {
        if (einsp(dd) && einsp(S_V_I(e,j))) 
        {
          erg+=inc(hilf);erg+=inc(hilfv);
          erg+=copy(S_V_I(e,j),S_V_I(hilfv,l));
          M_I_I(1L,S_V_I(hilf,l));
          l=l+1L;
          /*printf("Exponent = %d , Vielfachheit = %d\n",s_v_ii(e,j),1L);*/
        ax_e = callocobject(); erg+=copy(S_V_I(e,j),ax_e);
          insert(ax_e,speicher,NULL,NULL);
        }
        else
        {
          erg+=euler_phi(S_V_I(e,j),f);
          erg+=quores(f,dd,g,h);
          if (nullp(h)) 
          {
        ax_e = callocobject(); erg+=copy(S_V_I(e,j),ax_e);
        if (insert(ax_e,speicher,NULL,NULL)==INSERTOK)
        {
          erg+=inc(hilf);erg+=inc(hilfv);
          erg+=copy(S_V_I(e,j),S_V_I(hilfv,l));
          erg+=copy(g,S_V_I(hilf,l));
          ++l;
          /*printf("Exponent = %d , Vielfachheit = %d\n",s_v_ii(e,j),s_i_i(g));*/
        }
          } 
        } 
      }
      /* e=callocobject(); AK 260594 */
      erg+=copy(hilfv,S_V_I(a,i));
      erg+=copy(hilf,S_V_I(b,i));
    }
    erg+=freeall(e);
    erg+=freeall(hilf);
    erg+=freeall(hilfv);
    erg+=freeall(dd);
    erg+=freeall(c);
    erg+=freeall(f);
    erg+=freeall(g);
    erg+=freeall(h);
    erg+=freeall(speicher);
    if (erg!=OK) error("in computation of exponenten_bestimmen(d,q,a,b)");
    return(erg);
}

INT zykelind_glkq(k,q,ergeb) OP k,q,ergeb;
{
    OP p,null,c,c1,c2,c3,d,hilf,hilf1,zs1,zs2,zs3,zs4,zs5,zs6,v1,v2;
    INT i,j,l;
    INT erg=OK;
    p=callocobject();
    c=callocobject();
    c1=callocobject();
    c2=callocobject();
    c3=callocobject();
    d=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    zs1=callocobject();
    zs2=callocobject();
    zs3=callocobject();
    zs4=callocobject();
    zs5=callocobject();
    zs6=callocobject();
    null=callocobject();
    v1=callocobject();
    v2=callocobject();
    if (charakteristik_bestimmen(q,p)!=OK) return error("in computation of zykelind_glkq(k,q,ergeb)");
    erg+=exponenten_bestimmen(k,q,v1,v2);
    M_I_I(0L,null);
    erg+=m_scalar_polynom(null,ergeb);
    first_part_EXPONENT(k,c);
    do
    {  /*2*/
      erg+=m_iindex_monom(0L,zs1);
      for (i=0L;i<S_PA_LI(c);++i)
      {  /*3*/
        if (S_PA_II(c,i)>0L)
        {  /*4*/
          M_I_I(i+1L,d);
          erg+=m_scalar_polynom(null,zs2);
          first_unordered_part_into_atmost_k_parts(S_PA_II(c,i),S_V_LI(S_V_I(v1,i)),c1);
          do
          { /*5*/
        erg+=m_iindex_monom(0L,zs3);
        for (j=0L;j<S_V_LI(c1);++j)
        { /*6*/
          if (S_V_II(c1,j)!=0L)
          { /*7*/
            erg+=m_scalar_polynom(null,zs4);
            first_part_into_atmost_k_parts(S_V_I(c1,j),S_V_I(S_V_I(v2,i),j),c2);
            do
            { /*8*/
              erg+=m_iindex_monom(0L,zs5);
              for (l=0L;l<S_V_LI(c2);++l)
              {  /*9*/
            if (S_V_II(c2,l)!=0L)
            {  /*10*/
              erg+=m_scalar_polynom(null,zs6);
              first_part_EXPONENT(S_V_I(c2,l),c3);
              do
              {  /*11*/
                erg+=zykeltyp_poly_part(d,S_V_I(S_V_I(v1,i),j),c3,p,q,hilf);
                erg+=add_apply(hilf,zs6);
              } while (next(c3,c3)); /*11*/
              erg+=zykelind_dir_prod_apply(zs6,zs5);
            }  /*10*/
              }  /*9*/
              erg+=fmultinom_ext(S_V_I(S_V_I(v2,i),j),c2,hilf);
              erg+=m_scalar_polynom(hilf,hilf1);
              erg+=mult_apply(hilf1,zs5);
              erg+=add_apply(zs5,zs4);
              l=next_part_into_atmost_k_parts(c2);
            } while(l==1L); /*8*/
            erg+=zykelind_dir_prod_apply(zs4,zs3);
          }  /*7*/
        }  /*6*/
          erg+=add_apply(zs3,zs2);
          j=next_unordered_part_into_atmost_k_parts(c1);
          } while(j==1L); /*5*/
        erg+=zykelind_dir_prod_apply(zs2,zs1);
        }  /*4*/
      }  /*3*/
      erg+=add_apply(zs1,ergeb);
    }  /*2*/
    while (next(c,c));
    erg+=freeall(p); 
    erg+=freeall(c); 
    erg+=freeall(c1); 
    erg+=freeall(c2);
    erg+=freeall(c3); 
    erg+=freeall(d); 
    erg+=freeall(hilf); 
    erg+=freeall(hilf1);
    erg+=freeall(zs1); 
    erg+=freeall(zs2); 
    erg+=freeall(zs3); 
    erg+=freeall(zs4);
    erg+=freeall(zs5); 
    erg+=freeall(zs6); 
    erg+=freeall(null); 
    erg+=freeall(v1);
    erg+=freeall(v2);
    ENDR("zykelind_glkq");
}

static INT charakteristik_bestimmen(q,p) OP q,p;
{
    INT erg=OK;
    OP hilf=callocobject();
    if (S_O_K(q)!=INTEGER) return error("charakteristik_bestimmen(q,p)  q not INTEGER");
    if (S_I_I(q)<2L) return error("charakteristik_bestimmen(q,p)  q<2");
    if (!emptyp(p)) erg+=freeself(p);
        erg+=integer_factor(q,hilf);/* monopoly Faktorisierung von q */
        if (s_l_n(hilf)!=NULL) 
        {
          freeall(hilf);
          return error("q is not a power of a prime");
        } 
        erg+=copy(S_PO_S(hilf),p);
        erg+=freeall(hilf);
        if (erg!=OK) error("in computation of charakteristik_bestimmen(q,p)");
        return erg;
}

INT zykelind_affkq(k,q,ergeb) OP k,q,ergeb;
{
    OP p,null,c,c1,c2,c3,d,hilf,hilf1,zs1,zs2,zs3,zs4,zs5,zs6,v1,v2;
    INT i,j,l;
    INT erg=OK;
    p=callocobject();
    c=callocobject();
    c1=callocobject();
    c2=callocobject();
    c3=callocobject();
    d=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    zs1=callocobject();
    zs2=callocobject();
    zs3=callocobject();
    zs4=callocobject();
    zs5=callocobject();
    zs6=callocobject();
    null=callocobject();
    v1=callocobject();
    v2=callocobject();
    if (charakteristik_bestimmen(q,p)!=OK) return error("in computation of zykelind_affkq(k,q,ergeb)");
    erg+=exponenten_bestimmen(k,q,v1,v2);
    M_I_I(0L,null);
    erg+=m_scalar_polynom(null,ergeb);
    first_part_EXPONENT(k,c);
    do
    {  /*2*/
      erg+=m_iindex_monom(0L,zs1);
      for (i=0L;i<S_PA_LI(c);++i)
      {  /*3*/
        if (S_PA_II(c,i)>0L)
        {  /*4*/
          M_I_I(i+1L,d);
          erg+=m_scalar_polynom(null,zs2);
          first_unordered_part_into_atmost_k_parts(S_PA_II(c,i),S_V_LI(S_V_I(v1,i)),c1);
          do
          { /*5*/
        erg+=m_iindex_monom(0L,zs3);
        for (j=0L;j<S_V_LI(c1);++j)
        { /*6*/
          if (S_V_II(c1,j)!=0L)
          { /*7*/
            erg+=m_scalar_polynom(null,zs4);
            first_part_into_atmost_k_parts(S_V_I(c1,j),S_V_I(S_V_I(v2,i),j),c2);
            do
            { /*8*/
              erg+=m_iindex_monom(0L,zs5);
              for (l=0L;l<S_V_LI(c2);++l)
              {  /*9*/
            if (S_V_II(c2,l)!=0L)
            {  /*10*/
              erg+=m_scalar_polynom(null,zs6);
              first_part_EXPONENT(S_V_I(c2,l),c3);
              do
              {  /*11*/
                erg+=zykeltyp_poly_part_aff(d,S_V_I(S_V_I(v1,i),j),c3,p,q,hilf);
                erg+=add_apply(hilf,zs6);
              } while (next(c3,c3)); /*11*/
              erg+=zykelind_dir_prod_apply(zs6,zs5);
            }  /*10*/
              }  /*9*/
              erg+=fmultinom_ext(s_v_i(s_v_i(v2,i),j),c2,hilf);
              erg+=m_scalar_polynom(hilf,hilf1);
              erg+=mult_apply(hilf1,zs5);
              erg+=add_apply(zs5,zs4);
              l=next_part_into_atmost_k_parts(c2);
            } while(l==1L); /*8*/
            erg+=zykelind_dir_prod_apply(zs4,zs3);
          }  /*7*/
        }  /*6*/
          erg+=add_apply(zs3,zs2);
          j=next_unordered_part_into_atmost_k_parts(c1);
          } while(j==1L); /*5*/
        erg+=zykelind_dir_prod_apply(zs2,zs1);
        }  /*4*/
      }  /*3*/
      erg+=add_apply(zs1,ergeb);
    }  /*2*/
    while (next(c,c));
    erg+=hoch(q,k,hilf);
    erg+=invers_apply(hilf);
    erg+=mult_apply(hilf,ergeb);
    erg+=freeall(p); erg+=freeall(c); erg+=freeall(c1); erg+=freeall(c2);
    erg+=freeall(c3); erg+=freeall(d); erg+=freeall(hilf); erg+=freeall(hilf1);
    erg+=freeall(zs1); erg+=freeall(zs2); erg+=freeall(zs3); erg+=freeall(zs4);
    erg+=freeall(zs5); erg+=freeall(zs6); erg+=freeall(null); erg+=freeall(v1);
    erg+=freeall(v2);
    if (erg!=OK) error("in compuation of zykelind_affkq(k,q,ergeb) ");
    return(erg);
}

static INT zykeltyp_poly_part_aff(d,exp,mu,p,q,ergeb) OP d,exp,mu,p,q,ergeb;
/* Berechnet den Zykeltyp einer Blockdiagonalmatrix besthend aus
Begleit und Hyperbegleitmatrizen eines irreduziblen normierten Polynoms
vom Grad d, Exponenten (=Periode bzw. Ordnung) exp; Die Gestalt dieser
Matrix wird durch die Prtition mu festgelegt, p ist die Charakteristik
des Koerpers, q dessen Maechtigkeit, und ergeb ist der berechnete
Zykeltyp.  */
{
    INT i;
    INT erg=OK;
    OP hilf,hilf1;
    hilf=callocobject();
    hilf1=callocobject();
    erg+=m_iindex_monom(0L,ergeb);
    if ((!einsp(d)) || ((S_I_I(q)!=2L) && (S_I_I(exp)!=1L)))
    {
      for (i=0L;i<S_PA_LI(mu);++i)
      {
        if (S_PA_II(mu,i)!=0L)
        {
          erg+=zykeltyp_hyperbegleitmatrix_poly(d,exp,i+1L,p,q,hilf);
          erg+=m_i_i(i+1L,hilf1);
          erg+=mult_apply(d,hilf1);
          erg+=hoch(q,hilf1,hilf1);
          erg+=mult_apply(hilf1,hilf);
          erg+=zykelind_hoch_dir_prod(hilf,S_PA_I(mu,i),hilf1);
          erg+=zykelind_dir_prod_apply(hilf1,ergeb);
        }
      }
    }
    else
    {
      for (i=0L;i<S_PA_LI(mu);++i)
      {
        if (S_PA_II(mu,i)!=0L)
        {
          erg+=zykeltyp_hyperbegleitmatrix_poly(d,exp,i+1L,p,q,hilf);
          erg+=m_i_i(i,hilf1);
          erg+=hoch(q,hilf1,hilf1);
          erg+=mult_apply(hilf1,hilf);
          erg+=zykeltyp_hyperbegleitmatrix_poly_afferg(exp,i+2L,p,q,hilf1);
          erg+=add_apply(hilf1,hilf);
          erg+=zykelind_hoch_dir_prod(hilf,S_PA_I(mu,i),hilf1);
          erg+=zykelind_dir_prod_apply(hilf1,ergeb);
        }
      }
    }
    erg+=kung_formel(d,mu,q,hilf);
    erg+=invers_apply(hilf);
    erg+=m_scalar_polynom(hilf,hilf1);
    erg+=mult_apply(hilf1,ergeb);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    if (erg!=OK) error(" In computation of zykeltyp_poly_part_aff(d,exp,mu,p,q,ergeb) ");
    return(erg);
}

static INT zykeltyp_hyperbegleitmatrix_poly_afferg(exp,i,p,q,ergeb) OP exp,p,q,ergeb; INT i;
/* Bestimmt den Zykeltyp der Hyperbegleitmatrix von p(x)^i, einem
irreduziblen normierten Polynom vom Grad d mit Exponenten exp, ueber
einem Koerper von Charakteristik p und Maechtigkeit q. Das Ergebnis ist
ergeb*/
{
    OP e,hilf,hilf1,hilf2;
    INT j,k;
    INT erg=OK;
    e=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    M_I_I(1L,e);
    M_I_I(i,hilf);
    while (gt(hilf,e))
    {
      erg+=mult_apply(p,e);
    }
    erg+=dec(hilf);
    erg+=hoch(q,hilf,hilf1);
    erg+=ganzdiv(hilf1,e,hilf2);
    erg+=m_iindex_iexponent_monom(s_i_i(e)-1L,s_i_i(hilf2),ergeb); /* HF130696 */
    erg+=dec(hilf);
    erg+=hoch(q,hilf,hilf1);
    erg+=copy(q,hilf);
    erg+=dec(hilf);
    erg+=mult_apply(hilf,hilf1);
    erg+=mult_apply(hilf1,ergeb);
    erg+=freeall(e);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    if (erg!=OK) error("in computation of zykeltyp_hyperbegleitmatrix_poly_afferg(exp,i,p,q,ergeb) ");
    return(erg);
}

/* *************************************************************

The cycle indices of the natural actions of the general linear
and affine groups over Z modulo kZ.

**************************************************************** */

INT zykelind_glkzn(k,n,cy_ind) OP k,n,cy_ind;
/* Berechnet fuer quadratfreies n>=1 INTEGER objekt den Zyklenzeiger
der Gruppe aller regulaeren $k\times k$ Matrizen (k ein INTEGER objekt)
ueber Z_n=(Z modulo n) als Permutationsgruppe von Z_n^k  */ 
{
    INT erg=OK;
    OP hilf=callocobject();
    OP hilfpoly=callocobject();
    OP q=callocobject();
    if (S_O_K(k)!=INTEGER) return error("zykelind_glkzn(k,n,cy_ind)  k not INTEGER");
    if (S_I_I(k)<1L) return error("zykelind_glkzn(k,n,cy_ind)  k<1");
    if (S_O_K(n)!=INTEGER) return error("zykelind_glkzn(k,n,cy_ind)  n not INTEGER");
    if (S_I_I(n)<1L) return error("zykelind_glkzn(k,n,cy_ind)  n<1");
    if (!emptyp(cy_ind)) erg+=freeself(cy_ind);
    erg+=m_iindex_monom(0L,cy_ind);
    erg+=integer_factor(n,hilf);/* monopoly Faktorisierung von q */
    erg+=copy(hilf,q);
    while(hilf!=NULL)
    {
      if (!einsp(S_PO_K(hilf))) return error(" zykelind_glkzn(k,n,cy_ind)  n not square free");
      hilf=s_l_n(hilf);
    }
    hilf=callocobject();
    erg+=copy(q,hilf);
    while(hilf!=NULL)
    {
      erg+=copy(S_PO_S(hilf),q);
      erg+=zykelind_glkq(k,q,hilfpoly);
      erg+=zykelind_dir_prod_apply(hilfpoly,cy_ind);
      hilf=s_l_n(hilf);
    }
    /*erg+=freeall(hilf);*/
    erg+=freeall(hilfpoly);
    erg+=freeall(q);
    if (erg!=OK) error("in computation of zykelind_glkzn(k,n,cy_ind)");
    return(erg);
}

INT zykelind_affkzn(k,n,cy_ind)
    OP k,n,cy_ind;
/* Berechnet fuer quadratfreies n>=1 INTEGER objekt den Zyklenzeiger
der Gruppe aller affinen Abbildungen Z_n^k -> Z_n^k  mit
Z_n=(Z modulo n) als Permutationsgruppe von Z_n^k  */ 
{
    INT erg=OK;
    OP hilf=callocobject();
    OP hilfpoly=callocobject();
    OP q=callocobject();
    if (S_O_K(k)!=INTEGER) return error("zykelind_affkzn(k,n,cy_ind)  k not INTEGER");
    if (S_I_I(k)<1L) return error("zykelind_affkzn(k,n,cy_ind)  k<1");
    if (S_O_K(n)!=INTEGER) return error("zykelind_affkzn(k,n,cy_ind)  n not INTEGER");
    if (S_I_I(n)<1L) return error("zykelind_affkzn(k,n,cy_ind)  n<1");
    if (!emptyp(cy_ind)) erg+=freeself(cy_ind);
    if (einsp(k)) return zykelind_aff1Zn(n,cy_ind);
    erg+=m_iindex_monom(0L,cy_ind);
    erg+=integer_factor(n,hilf);/* monopoly Faktorisierung von q */
    erg+=copy(hilf,q);
    while(hilf!=NULL)
    {
      if (!einsp(S_PO_K(hilf))) return error(" zykelind_affkzn(k,n,cy_ind)  n not square free");
      hilf=s_l_n(hilf);
    }
    hilf=callocobject();
    erg+=copy(q,hilf);
    while(hilf!=NULL)
    {
      erg+=copy(S_PO_S(hilf),q);
      erg+=zykelind_affkq(k,q,hilfpoly);
      erg+=zykelind_dir_prod_apply(hilfpoly,cy_ind);
      hilf=s_l_n(hilf);
    }
    /*erg+=freeall(hilf);*/
    erg+=freeall(hilfpoly);
    erg+=freeall(q);
    ENDR("internal function zykelind_affkzn");
}

static INT zykelind_aff1Zp(p,a,r)
    OP p,a,r;
/* p sei eine Primzahl ungleich 2
r ist der Zyklenzeiger von der Gruppe aller affinen Abbildungen von
Z_{p^a}.
*/
{
    if (eq(p,cons_zwei)) return zykelind_aff1Z2(a,r);
    else
    {
    INT erg=OK;
    INT i,j,k;
    OP hilf1=callocobject();
    OP hilf2=callocobject();
    OP hilf3=callocobject();
    OP hilf4=callocobject();
    OP hilf5=callocobject();
    OP hmonom=callocobject();
    OP hmonom1=callocobject();
    OP teiler=callocobject();
    OP pp=callocobject();
    erg+=m_i_i(0L,r);
    erg+=copy(p,pp);
    erg+=dec(pp);
    erg+=alle_teiler(pp,teiler);
    erg+=m_i_i(0L,hilf1);
    for (i=0L;i<S_I_I(a);++i)
    { 
      for (j=0L;j<S_V_LI(teiler);++j)
      {
        if (einsp(S_V_I(teiler,j))) 
        {
          erg+=hoch(p,hilf1,hilf2);
          erg+=euler_phi(hilf2,hilf3);
          erg+=mult_apply(hilf3,hilf2);
          erg+=sub(a,hilf1,hilf3);
          erg+=dec(hilf3);
          erg+=hoch(p,hilf3,hilf4);
          erg+=m_iindex_iexponent_monom(0L,s_i_i(hilf4),hmonom);
          erg+=mult_apply(hilf2,hmonom);
          erg+=mult_apply(pp,hilf4);
          for (k=0L;k<=i;++k)
          {
        erg+=m_i_i(k,hilf2);
        erg+=hoch(p,hilf2,hilf3);
        erg+=m_iindex_iexponent_monom(s_i_i(hilf3)-1L,s_i_i(hilf4),hmonom1);
        erg+=mult_apply(hmonom1,hmonom);
          }
        }
        else
        {
          erg+=hoch(p,a,hilf2);
          erg+=hoch(p,hilf1,hilf3);
          erg+=mult_apply(S_V_I(teiler,j),hilf3);
          erg+=euler_phi(hilf3,hilf4);
          erg+=mult_apply(hilf4,hilf2);
          erg+=m_iindex_iexponent_monom(0L,1L,hmonom);
          erg+=mult_apply(hilf2,hmonom);
          erg+=sub(a,hilf1,hilf3);
          erg+=dec(hilf3);
          erg+=hoch(p,hilf3,hilf4);
          erg+=dec(hilf4);
          erg+=ganzdiv(hilf4,S_V_I(teiler,j),hilf2);
          erg+=m_iindex_iexponent_monom(S_V_II(teiler,j)-1L,s_i_i(hilf2),hmonom1);
          erg+=mult_apply(hmonom1,hmonom);
          erg+=inc(hilf4);
          erg+=mult_apply(pp,hilf4);
          erg+=ganzdiv(hilf4,S_V_I(teiler,j),hilf4);
          for (k=0L;k<=i;++k)
          {
        erg+=m_i_i(k,hilf2);
        erg+=hoch(p,hilf2,hilf3);
        erg+=mult_apply(S_V_I(teiler,j),hilf3);
        erg+=m_iindex_iexponent_monom(s_i_i(hilf3)-1L,s_i_i(hilf4),hmonom1);
        erg+=mult_apply(hmonom1,hmonom);
          }
        }
        erg+=add_apply(hmonom,r);
      }
      erg+=mult(cons_zwei,hilf1,hilf2);
      erg+=hoch(p,hilf2,hilf3);
      erg+=mult_apply(pp,hilf3);
      erg+=inc(hilf1);
      erg+=hoch(p,hilf1,hilf2);
      erg+=sub(a,hilf1,hilf4);
      erg+=hoch(p,hilf4,hilf5);
      erg+=m_iindex_iexponent_monom(s_i_i(hilf2)-1L,s_i_i(hilf5),hmonom);
      erg+=mult_apply(hilf3,hmonom);
      erg+=add_apply(hmonom,r);
    }
    erg+=mult(a,cons_zwei,hilf1);
    erg+=dec(hilf1);
    erg+=hoch(p,hilf1,hilf2);
    erg+=mult_apply(pp,hilf2);
    erg+=div(r,hilf2,r);
    erg+=freeall(hilf1); erg+=freeall(hilf2); erg+=freeall(hilf3);
    erg+=freeall(hilf4); erg+=freeall(hilf5); erg+=freeall(hmonom);
    erg+=freeall(hmonom1); erg+=freeall(teiler); erg+=freeall(pp);
    ENDR("internal function zykelind_aff1Zp");
    }
}

static INT zykelind_aff1Z2(a,r)
    OP a,r;
{
    INT erg=OK;
    OP hmonom=callocobject();
    if (eq(a,cons_eins))
    {
      erg+=m_iindex_iexponent_monom(0L,2L,r);
      erg+=m_iindex_iexponent_monom(1L,1L,hmonom);
      erg+=add_apply(hmonom,r);
      erg+=div(r,cons_zwei,r);
    }
    else if (eq(a,cons_zwei))
    {
      OP v=callocobject();
      erg+=m_iindex_iexponent_monom(0L,4L,r);
      erg+=m_il_v(2L,v);
      erg+=m_i_i(2L,S_V_I(v,0L));
      erg+=m_i_i(1L,S_V_I(v,1L));
      erg+=m_skn_po(v,cons_zwei,NULL,hmonom);
      erg+=add_apply(hmonom,r);
      erg+=m_iindex_iexponent_monom(1L,2L,hmonom);
      erg+=m_i_i(3L,S_PO_K(hmonom));
      erg+=add_apply(hmonom,r);
      erg+=m_iindex_iexponent_monom(3L,1L,hmonom);
      erg+=m_i_i(2L,S_PO_K(hmonom));
      erg+=add_apply(hmonom,r);
      erg+=m_i_i(8L,hmonom);
      erg+=div(r,hmonom,r);
      erg+=freeall(v);
    }
    else 
    {
    INT i,j;
    OP hilf1=callocobject();
    OP hilf2=callocobject();
    OP hilf3=callocobject();
    OP hilf4=callocobject();
    OP hilf5=callocobject();
    OP hmonom1=callocobject();
    OP hmonom2=callocobject();
    OP aa=callocobject();
    erg+=copy(a,aa);
    erg+=dec(aa);
    erg+=hoch(cons_zwei,a,hilf1);
    erg+=m_iindex_iexponent_monom(s_i_i(hilf1)-1L,1L,r);
    erg+=mult(cons_zwei,aa,hilf1);
    erg+=dec(hilf1);
    erg+=hoch(cons_zwei,hilf1,S_PO_K(r));
    erg+=hoch(cons_zwei,aa,aa);
    erg+=m_i_i(0L,hilf1);
    for (i=0L;i<S_I_I(a)-1L;++i)
    {
      erg+=hoch(cons_zwei,hilf1,hilf2);
      erg+=euler_phi(hilf2,hilf3);
      erg+=sub(a,hilf1,hilf4);
      erg+=hoch(cons_zwei,hilf4,hilf5);
      erg+=m_iindex_iexponent_monom(0L,s_i_i(hilf5),hmonom);
      erg+=mult_apply(hilf2,hmonom);
      erg+=dec(hilf4);
      erg+=hoch(cons_zwei,hilf4,hilf5);
      erg+=m_iindex_iexponent_monom(0L,2L,hmonom1);
      erg+=m_iindex_iexponent_monom(1L,s_i_i(hilf5)-1L,hmonom2);
      erg+=mult_apply(hmonom2,hmonom1);
      erg+=mult_apply(aa,hmonom1);
      erg+=add_apply(hmonom1,hmonom);
      erg+=mult_apply(hilf3,hmonom);
      for (j=1L;j<=i;++j)
      {
        erg+=m_i_i(j,hilf2);
        erg+=hoch(cons_zwei,hilf2,hilf3);
        erg+=m_iindex_iexponent_monom(s_i_i(hilf3)-1L,s_i_i(hilf5),hmonom1);
        erg+=mult_apply(hmonom1,hmonom);
      }
      erg+=add_apply(hmonom,r);
      erg+=mult(cons_zwei,hilf1,hilf2);
      erg+=hoch(cons_zwei,hilf2,hilf3);
      erg+=hoch(cons_zwei,hilf1,hilf4);
      erg+=euler_phi(hilf4,hilf5);
      erg+=mult_apply(aa,hilf5);
      erg+=add_apply(hilf3,hilf5);
      erg+=inc(hilf1);
      erg+=hoch(cons_zwei,hilf1,hilf2);
      erg+=sub(a,hilf1,hilf3);
      erg+=hoch(cons_zwei,hilf3,hilf4);
      erg+=m_iindex_iexponent_monom(s_i_i(hilf2)-1L,s_i_i(hilf4),hmonom);
      erg+=mult_apply(hilf5,hmonom);
      erg+=add_apply(hmonom,r);
    }
    erg+=mult_apply(aa,aa);
    erg+=mult_apply(cons_zwei,aa);
    erg+=div(r,aa,r);
    erg+=freeall(hilf1); erg+=freeall(hilf2); erg+=freeall(hilf3);
    erg+=freeall(hilf4); erg+=freeall(hilf5); erg+=freeall(hmonom1);
    erg+=freeall(hmonom2); erg+=freeall(aa);
    }
    erg+=freeall(hmonom);
    ENDR("internal function zykelind_aff1Z2");
}

INT zykelind_aff1Zn(a,b) OP a,b;
/* Berechnet den Zyklenzeiger der Gruppe aller affinen Abbildungen
von Z_a nach Z_a.  */
{
    INT erg=OK;
    OP hilf=callocobject();
    OP hilf1=callocobject();
    erg+=m_iindex_iexponent_monom(0L,1L,b);
    erg+=integer_factor(a,hilf);/* monopoly Faktorisierung von q */
    while(hilf!=NULL)
    {
      erg+=zykelind_aff1Zp(S_PO_S(hilf),S_PO_K(hilf),hilf1);
      erg+=zykelind_dir_prod_apply(hilf1,b);
      hilf=s_l_n(hilf);
    }
    erg+=freeall(hilf1);
    if (erg!=OK) EDC("zykelind_aff1Zn");
    return erg;
}

/* ****************************************************************

Routines for the computation of the cycle index of the projective
linear groups PGL(k,q).

******************************************************************* */

INT zykelind_pglkq(k,q,ergeb) OP k,q,ergeb;
/* Berechnet den Zyklenzeiger der projektiven Gruppe PGL(k,F_q) als
   Permutationsgruppe von PG(k-1,F_q).
*/
{
    OP p,null,eins,c,c1,c2,c3,d,hilf,hilf1,zs1,zs2,zs3,zs4,zs5,zs6,v1,v2,v3;
    INT i,j,l;
    INT erg=OK;
    if (S_O_K(k)!=INTEGER) return error(" zykelind_pglkq(k,q,ergeb) k not INTEGER");
    if (S_O_K(q)!=INTEGER) return error(" zykelind_pglkq(k,q,ergeb) q not INTEGER");
    if (S_I_I(k)<1L) return error(" zykelind_pglkq(k,q,ergeb) k<1");
    if (!emptyp(ergeb)) freeself(ergeb);
    p=callocobject();
    c=callocobject();
    c1=callocobject();
    c2=callocobject();
    c3=callocobject();
    d=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    zs1=callocobject();
    zs2=callocobject();
    zs3=callocobject();
    zs4=callocobject();
    zs5=callocobject();
    zs6=callocobject();
    null=callocobject();
    eins=callocobject();
    v1=callocobject();
    v2=callocobject();
    v3=callocobject();
    if (charakteristik_bestimmen(q,p)!=OK) return error("in computation of zykelind_pglkq(k,q,ergeb)");
    erg+=subexponenten_bestimmen(k,q,v1,v2,v3);
    M_I_I(0L,null);
    M_I_I(1L,eins);
    erg+=m_scalar_polynom(null,ergeb);
    first_part_EXPONENT(k,c);
    do
    {  /*2*/
      erg+=m_scalar_polynom(eins,zs1);
      for (i=0L;i<S_PA_LI(c);++i)
      {  /*3*/
        if (S_PA_II(c,i)>0L)
        {  /*4*/
          M_I_I(i+1L,d);
          erg+=m_scalar_polynom(null,zs2);
          first_unordered_part_into_atmost_k_parts(S_PA_II(c,i),S_V_LI(S_V_I(v1,i)),c1);
          do
          { /*5*/
        erg+=m_scalar_polynom(eins,zs3);
        for (j=0L;j<S_V_LI(c1);++j)
        { /*6*/
          if (S_V_II(c1,j)!=0L)
          { /*7*/
            erg+=m_scalar_polynom(null,zs4);
            first_part_into_atmost_k_parts(S_V_I(c1,j),S_V_I(S_V_I(v2,i),j),c2);
            do
            { /*8*/
              erg+=m_scalar_polynom(eins,zs5);
              for (l=0L;l<S_V_LI(c2);++l)
              {  /*9*/
            if (S_V_II(c2,l)!=0L)
            {  /*10*/
              erg+=m_scalar_polynom(null,zs6);
              first_part_EXPONENT(S_V_I(c2,l),c3);
              do
              {  /*11*/
                erg+=zykeltyp_poly_part_pglkq(d,S_V_I(S_V_I(v1,i),j),S_V_I(S_V_I(v3,i),j),c3,p,q,hilf);
                erg+=add_apply(hilf,zs6);
              } while (next(c3,c3)); /*11*/
              erg+=zykelind_dir_prod_pglkq_apply(q,zs6,zs5);
            }  /*10*/
              }  /*9*/
              erg+=fmultinom_ext(S_V_I(S_V_I(v2,i),j),c2,hilf);
              erg+=mult_apply(hilf,zs5); /* Vielleicht hilf in POLY verwandeln?*/
              erg+=add_apply(zs5,zs4);
              l=next_part_into_atmost_k_parts(c2);
            } while(l==1L); /*8*/
            erg+=zykelind_dir_prod_pglkq_apply(q,zs4,zs3);
          }  /*7*/
        }  /*6*/
          erg+=add_apply(zs3,zs2);
          j=next_unordered_part_into_atmost_k_parts(c1);
          } while(j==1L); /*5*/
        erg+=zykelind_dir_prod_pglkq_apply(q,zs2,zs1);
        }  /*4*/
      }  /*3*/
    erg+=zykelind_aus_subzykelind(q,zs1,hilf); /* HF130696 */
    erg+=add_apply(hilf,ergeb); /* HF130696 */
    /*erg+=add_apply(zs1,ergeb);*/ /* HF130696 */
    }  /*2*/
    while (next(c,c));
    erg+=freeall(p); erg+=freeall(c); erg+=freeall(c1);
    erg+=freeall(c2); erg+=freeall(c3); erg+=freeall(d);
    erg+=freeall(hilf1); erg+=freeall(zs1); erg+=freeall(zs2);
    erg+=freeall(zs3); erg+=freeall(zs4); erg+=freeall(zs5);
    erg+=freeall(zs6); erg+=freeall(null); erg+=freeall(eins);
    erg+=freeall(v1); erg+=freeall(v2); erg+=freeall(v3);
    /*erg+=zykelind_aus_subzykelind(q,ergeb,hilf);
    erg+=copy(hilf,ergeb);*/ /* HF130696 */
    erg+=freeall(hilf);
    if (erg!=OK) error(" in computation of zykelind_pglkq(k,q,ergeb) ");
    return(erg);
}

INT co_zykelind_pglkq(k,q,ergeb) OP k,q,ergeb;
/* Berechnet den Zyklenzeiger der projektiven Gruppe PGL(k,F_q) als
   Permutationsgruppe von PG(k-1,F_q).
*/
{
    OP p,null,eins,c,c1,c2,c3,d,hilf,hilf1,zs1,zs2,zs3,zs4,zs5,zs6,v1,v2,v3;
    INT i,j,l;
    INT erg=OK;
    if (S_O_K(k)!=INTEGER) return error(" zykelind_pglkq(k,q,ergeb) k not INTEGER");
    if (S_O_K(q)!=INTEGER) return error(" zykelind_pglkq(k,q,ergeb) q not INTEGER");
    if (S_I_I(k)<1L) return error(" zykelind_pglkq(k,q,ergeb) k<1");
    if (!emptyp(ergeb)) freeself(ergeb);
    p=callocobject();
    c=callocobject();
    c1=callocobject();
    c2=callocobject();
    c3=callocobject();
    d=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    zs1=callocobject();
    zs2=callocobject();
    zs3=callocobject();
    zs4=callocobject();
    zs5=callocobject();
    zs6=callocobject();
    null=callocobject();
    eins=callocobject();
    v1=callocobject();
    v2=callocobject();
    v3=callocobject();
    if (charakteristik_bestimmen(q,p)!=OK) return error("in computation of zykelind_pglkq(k,q,ergeb)");
    erg+=subexponenten_bestimmen(k,q,v1,v2,v3);
    M_I_I(0L,null);
    M_I_I(1L,eins);
    erg+=m_scalar_polynom(null,ergeb);
    /*first_part_EXPONENT(k,c);
    do */
    m_il_v(S_I_I(k),zs2);
    copy(k,S_V_I(zs2,0L));
    for (i=1L;i<S_V_LI(zs2);++i) m_i_i(0L,S_V_I(zs2,i));
    m_ks_pa(EXPONENT,zs2,c);
    println(c);
    {  /*2*/
      erg+=m_scalar_polynom(eins,zs1);
      for (i=0L;i<S_PA_LI(c);++i)
      {  /*3*/
        if (S_PA_II(c,i)>0L)
        {  /*4*/
          M_I_I(i+1L,d);
          erg+=m_scalar_polynom(null,zs2);
          first_unordered_part_into_atmost_k_parts(S_PA_II(c,i),S_V_LI(S_V_I(v1,i)),c1);
          do
          { /*5*/
        erg+=m_scalar_polynom(eins,zs3);
        for (j=0L;j<S_V_LI(c1);++j)
        { /*6*/
          if (S_V_II(c1,j)!=0L)
          { /*7*/
            erg+=m_scalar_polynom(null,zs4);
            first_part_into_atmost_k_parts(S_V_I(c1,j),S_V_I(S_V_I(v2,i),j),c2);
            do
            { /*8*/
              erg+=m_scalar_polynom(eins,zs5);
              for (l=0L;l<S_V_LI(c2);++l)
              {  /*9*/
            if (S_V_II(c2,l)!=0L)
            {  /*10*/
              erg+=m_scalar_polynom(null,zs6);
              first_part_EXPONENT(S_V_I(c2,l),c3);
              do
              {  /*11*/
                erg+=zykeltyp_poly_part_pglkq(d,S_V_I(S_V_I(v1,i),j),S_V_I(S_V_I(v3,i),j),c3,p,q,hilf);
                erg+=add_apply(hilf,zs6);
              } while (next(c3,c3)); /*11*/
              erg+=zykelind_dir_prod_pglkq_apply(q,zs6,zs5);
            }  /*10*/
              }  /*9*/
              erg+=fmultinom_ext(S_V_I(S_V_I(v2,i),j),c2,hilf);
              erg+=mult_apply(hilf,zs5); /* Vielleicht hilf in POLY verwandeln?*/
              erg+=add_apply(zs5,zs4);
              l=next_part_into_atmost_k_parts(c2);
            } while(l==1L); /*8*/
            erg+=zykelind_dir_prod_pglkq_apply(q,zs4,zs3);
          }  /*7*/
        }  /*6*/
          erg+=add_apply(zs3,zs2);
          j=next_unordered_part_into_atmost_k_parts(c1);
          } while(j==1L); /*5*/
        erg+=zykelind_dir_prod_pglkq_apply(q,zs2,zs1);
        }  /*4*/
      }  /*3*/
    erg+=add_apply(zs1,ergeb);
    }  /*2*/
    /*while (next(c,c));*/
    erg+=freeall(p);
    erg+=freeall(c);
    erg+=freeall(c1);
    erg+=freeall(c2);
    erg+=freeall(c3);
    erg+=freeall(d);
    erg+=freeall(hilf1);
    erg+=freeall(zs1);
    erg+=freeall(zs2);
    erg+=freeall(zs3);
    erg+=freeall(zs4);
    erg+=freeall(zs5);
    erg+=freeall(zs6);
    erg+=freeall(null);
    erg+=freeall(eins);
    erg+=freeall(v1);
    erg+=freeall(v2);
    erg+=freeall(v3);
    erg+=zykelind_aus_subzykelind(q,ergeb,hilf);
    erg+=copy(hilf,ergeb);
    erg+=freeall(hilf);
    if (erg!=OK) error(" in computation of zykelind_pglkq(k,q,ergeb) ");
    return(erg);
}

static INT min_pot(a,b,c,d) OP a,b,c,d;
/* 2 Elemente g1,g2 einer zyklischen Gruppe der Ordnung c seien gegeben als
Potenzen eines erzeugenden Elementes g1=g^a und g2=g^b. Die errechnete Zahl
d ist die Ordnung von g1 g2^(-1). Das heisst: d ist minimal mit der 
Eigenschaft, dass g1^d=g2^d.  
*/
{
    OP hilf;
    INT erg=OK;
    /*if (S_O_K(a)!=INTEGER) return error(" min_pot(a,b,c,d) a not INTEGER");
    if (S_O_K(b)!=INTEGER) return error(" min_pot(a,b,c,d) b not INTEGER");
    if (S_O_K(c)!=INTEGER) return error(" min_pot(a,b,c,d) c not INTEGER");
    if (S_I_I(c)<1L) return error(" min_pot(a,b,c,d) c < 1");*/
    if (!emptyp(d)) freeself(d);

    if (EQ(a,b)) { M_I_I(1L,d); goto endr_ende; }

    hilf=callocobject();
    erg+=sub(a,b,hilf);
    erg+=ggt(hilf,c,hilf);
    erg+=ganzdiv(c,hilf,d);
    erg+=freeall(hilf);

    ENDR("min_pot");
}

static INT zykelind_dir_prod_pglkq_apply(q,a,b) OP q,a,b;
/* Berechnet das direkte Produkt der Subzykeltypen a und b und ersetzt b durch
das errechnete Ergebnis. q=Maechtigkeit des Koerpers.
*/
{
    OP hilf=callocobject();
    OP qq=callocobject();
    INT erg=OK;
    /*if (S_O_K(q)!=INTEGER) return error(" zykelind_dir_prod_pglkq_apply(q,a,b) q not INTEGER");
    if (S_I_I(q)<1L) return error(" zykelind_dir_prod_pglkq_apply(q,a,b) q<1");
    if (S_O_K(a)!=POLYNOM) return error(" zykelind_dir_prod_pglkq_apply(q,a,b) a not POLYNOM");
    if (S_O_K(b)!=POLYNOM) return error(" zykelind_dir_prod_pglkq_apply(q,a,b) b not POLYNOM");*/
    erg+=copy(q,qq);erg+=dec(qq);
    erg+=zykelind_dir_prod_pglkq(qq,a,b,hilf);
    erg+=copy(hilf,b);
    erg+=freeall(hilf);
    erg+=freeall(qq);
    if (erg!=OK) error("in computation of zykelind_dir_prod_pglkq_apply(q,a,b) ");
    return(erg);
}

static INT zykelind_hoch_dir_prod_pglkq(q,a,c,b) OP q,a,b,c;
/* Berechnet die c-fache Hintereinanderausfuehrung des direkten Produktes
des Subzykeltyps a mit sich selbst. Das Ergebnis ist c. Der Koerper
enthaelt q Elemente.
*/
{
    INT erg=OK;
    /*if (S_O_K(q)!=INTEGER) return error("zykelind_hoch_dir_prod_pglkq(q,a,c,b)  q not INTEGER");
    if (S_O_K(a)!=POLYNOM) return error("zykelind_hoch_dir_prod_pglkq(q,a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("zykelind_hoch_dir_prod_pglkq(q,a,c,b) c not INTEGER");
    if (S_I_I(c)<0L) return error("zykelind_hoch_dir_prod_pglkq(q,a,c,b) c<0");*/
    if (not EMPTYP(b)) erg+=freeself(b);
    if (nullp(c))
       return M_I_I(1L,b);
    else if (einsp(c)) 
         return copy(a,b);
    else    {
            OP qq = callocobject(); 
            OP n = callocobject();
            OP d = callocobject();
            erg+=copy(q,qq);erg+=dec(qq);
            erg+=copy(c,n);
            erg+=copy(a,b); 
            erg+=dec(n);  
            while (not nullp(n)) {
                erg+=zykelind_dir_prod_pglkq(qq,a,b,d);    
                erg+=dec(n);
                erg+=copy(d,b);
                }
            erg+=freeall(d);
            erg+=freeall(n);
            erg+=freeall(qq);
        };
    if (erg != OK) error(" in computation of zykelind_hoch_dir_prod_pglkq(q,a,c,b) ");
    return(erg);
}

static INT mod_mult(modul,a,b,c) OP modul,a,b,c;
/*  c + a.b mod modul, wobei 1<=c<=modul ist.  */
{
    INT erg=OK;
    /*if (S_O_K(modul)!=INTEGER) return error(" mod_mult(modul,a,b,c)  modul not INTEGER");
    if (S_I_I(modul)<1L) return error(" mod_mult(modul,a,b,c) modul < 1");
    if (S_O_K(a)!=INTEGER) return error(" mod_mult(modul,a,b,c)  a not INTEGER");
    if (S_O_K(b)!=INTEGER) return error(" mod_mult(modul,a,b,c)  b not INTEGER");*/
    if (!emptyp(c)) freeself(c);
    erg+=mult(a,b,c);
    erg+=mod(c,modul,c);
    if (nullp(c)) erg+=add_apply(modul,c);
    ENDR("mod_mult");
}

static INT subexponenten_bestimmen(d,q,a,b,cc) OP d,q,a,b,cc;
/* d=maximaler Grad der Polynome, die auftreten koennen
   q=Maechtigkeiy des Koerpers
   a,b,cc=Vektoren der Laenge d
   s_v_i(a,i) ist ein Vektor, der die Subexponenten enthaelt, die bei Polynomen
              vom Grad i+1 auftreten koennen
   s_v_i(b,i) ist ein Vektor der gleichen Laenge wie s_v_i(a,i), er
              enthaelt die Anzahl der normierten, irreduziblen Polynome
              vom Grad i+1 zu dem entsprechenden Subexponent
   s_v_i(c,i) ist ein Vektor der gleichen Laenge wie s_v_i(a,i), er
              enthaelt die entsprechenden integralen Elemente.
*/
{
    INT i,j,k,l,ii;
    OP hilf,hilfv,hilfv1,dd,c,e,f,g,h,speicher,qq,gruppe;
    OP ax_e;
    INT erg=OK;
    hilf=callocobject();
    hilfv=callocobject();
    hilfv1=callocobject();
    gruppe=callocobject();
    dd=callocobject();
    qq=callocobject();
    c=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    h=callocobject();
    speicher=callocobject();
    erg+=copy(q,qq);
    erg+=dec(qq);
    erg+=zyklische_gruppe(qq,gruppe);
    init(BINTREE,speicher);
    erg+=m_l_v(d,a);
    erg+=m_l_v(d,b);
    erg+=m_l_v(d,cc);
    for (i=0L;i<S_I_I(d);++i)
    {
      M_I_I(i+1L,dd);
      erg+=m_il_v(0L,hilf);
      erg+=m_il_v(0L,hilfv);
      erg+=m_il_v(0L,hilfv1);
      l=0L;
      erg+=hoch(q,dd,c);
      erg+=dec(c);
      erg+=alle_teiler(c,e);
      for (j=0L;j<S_V_LI(e);++j)
      {
        if (einsp(dd) && einsp(S_V_I(e,j))) 
        {
          erg+=inc(hilf);erg+=inc(hilfv);erg+=inc(hilfv1);
          erg+=copy(S_V_I(e,j),S_V_I(hilfv,l));
          erg+=copy(S_V_I(S_V_I(gruppe,0L),0L),S_V_I(hilfv1,l));
          M_I_I(1L,S_V_I(hilf,l));
          l=l+1L;
          ax_e = callocobject(); erg+=copy(S_V_I(e,j),ax_e);
          insert(ax_e,speicher,NULL,NULL);
        }
        else
        {
          erg+=euler_phi(S_V_I(e,j),f);
          erg+=quores(f,dd,g,h);
          if (nullp(h)) 
          {
        ax_e = callocobject(); erg+=copy(S_V_I(e,j),ax_e);
        if (insert(ax_e,speicher,NULL,NULL)==INSERTOK)
        {
          erg+=ggt(S_V_I(e,j),qq,h);
          erg+=ganzdiv(S_V_I(e,j),h,f);
          erg+=euler_phi(h,c);
          erg+=ganzdiv(g,c,c);
          for (ii=0L;ii<S_V_LI(S_V_I(gruppe,S_I_I(h)-1L));++ii)
          {
            erg+=inc(hilf);erg+=inc(hilfv);erg+=inc(hilfv1);
            erg+=copy(f,S_V_I(hilfv,l));
            erg+=copy(c,S_V_I(hilf,l));
            erg+=copy(S_V_I(S_V_I(gruppe,S_I_I(h)-1L),ii),S_V_I(hilfv1,l));
            ++l;
          }
        }
          } 
        } 
      }
      /* e=callocobject(); AK 260594 */
      erg+=copy(hilfv,S_V_I(a,i));
      erg+=copy(hilf,S_V_I(b,i));
      erg+=copy(hilfv1,S_V_I(cc,i));
    }
    erg+=freeall(e);
    erg+=freeall(hilf);
    erg+=freeall(hilfv);
    erg+=freeall(hilfv1);
    erg+=freeall(dd);
    erg+=freeall(qq);
    erg+=freeall(c);
    erg+=freeall(f);
    erg+=freeall(g);
    erg+=freeall(h);
    erg+=freeall(gruppe);
    erg+=freeall(speicher);
    ENDR("subexponenten_bestimmen");
}

static INT zyklische_gruppe(a,b) OP a,b;
/* a ist die Ordnung der zyklischen Gruppe (ein INTEGER-Objekt)
   die Elemente von der Gruppe sind dann die Integer-Objekte 1,2,...,a
   b ist ein Vektor der Laenge a
   s_v_i(b,i) ist ein Vektor der alle Elemente der Gruppe besitzt, deren
              Ordnung i+1 ist
   die Ordnung von dem Element i berechnet man als a/ggt(a,i)
*/
{
    OP index,hilf,hilf1;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=INTEGER) return error("zyklische_gruppe(a,b) a not INTEGER");
    if (S_I_I(a)<1L) return error("zyklische_gruppe(a,b) a <1");

    FREESELF(b);
    CALLOCOBJECT3(index,hilf,hilf1);
    erg+=m_l_v(a,b);
    for (i=0L;i<S_V_LI(b);++i)
        erg+=m_il_v(0L,S_V_I(b,i));
    M_I_I(1L,index);
    while(le(index,a))
    {
        erg+=ggt(index,a,hilf);
        erg+=ganzdiv(a,hilf,hilf);
        i=S_I_I(hilf)-1L;
        INC(S_V_I(b,i));
        erg+=copy(index,S_V_I(S_V_I(b,i),S_V_LI(S_V_I(b,i))-1L));
        INC(index);
    }
    FREEALL3(index,hilf,hilf1);
    ENDR("zyklische_gruppe");
}

static INT zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb) OP d,exp,ew,mu,p,q,ergeb;
/* d   = Grad des Polynoms
   exp = Subexponent des Polynoms
   ew  = integrales Element des Polynoms
   mu  = Partition
   p   = Charakteristik
   q   = Maechtigkeit des Koerpers
   ergeb = Ergebnis  
*/
{
    INT i;
    OP hilf,hilf1;
    INT erg=OK;
    /*if (S_O_K(d)!=INTEGER) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb)  d not INTEGER");
    if (S_O_K(exp)!=INTEGER) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb) exp  not INTEGER");
    if (S_O_K(ew)!=INTEGER) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb) ew not INTEGER");
    if (S_O_K(p)!=INTEGER) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb)  p not INTEGER");
    if (S_O_K(q)!=INTEGER) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb)  q not INTEGER");
    if (S_O_K(mu)!=PARTITION) return error("zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb) mu not PARTITION");*/
    if (!emptyp(ergeb)) erg+=freeself(ergeb);
    hilf=callocobject();
    hilf1=callocobject();
    M_I_I(1L,hilf);
    erg+=m_scalar_polynom(hilf,ergeb);
    for (i=0L;i<S_PA_LI(mu);++i)
    {
      if (S_PA_II(mu,i)!=0L)
      {
        erg+=zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i+1L,p,q,hilf);
        erg+=zykelind_hoch_dir_prod_pglkq(q,hilf,S_PA_I(mu,i),hilf1);
        erg+=zykelind_dir_prod_pglkq_apply(q,hilf1,ergeb);
      }
    }
    erg+=kung_formel(d,mu,q,hilf);
    erg+=invers_apply(hilf);
    erg+=mult_apply(hilf,ergeb);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    if (erg!=OK) error(" in computation of zykeltyp_poly_part_pglkq(d,exp,ew,mu,p,q,ergeb) ");
    return(erg);
}

static INT zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb)
    OP d,exp,ew,p,q,ergeb;
    INT i;
/* Berechnet den Subzykeltyp einer Hyperbegleitmatrix eines irreduziblen,
normierten Polynoms vom Grad d, Subexponenten exp, integralem Element ew,
wobei i mal die Begleutmatrix des Polynoms in der Hyperbegleitmatrix 
erscheint, p=Charakteristik des Koerpers, der aus q Elementen besteht.
*/
{
    OP e,hilf,hilf1,hilf2,hilftyp,qq,hilfpoly;
    INT j,k;
    INT erg=OK;
    /*if (S_O_K(d)!=INTEGER) return error("zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb)  d not INTEGER");
    if (S_O_K(exp)!=INTEGER) return error("zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb) exp  not INTEGER");
    if (S_O_K(ew)!=INTEGER) return error("zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb) ew not INTEGER");
    if (S_O_K(p)!=INTEGER) return error("zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb)  p not INTEGER");
    if (S_O_K(q)!=INTEGER) return error("zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb)  q not INTEGER");*/
    if (!emptyp(ergeb)) freeself(ergeb);
    e=callocobject();
    qq=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    hilftyp=callocobject();
    hilfpoly=callocobject();
    erg+=copy(q,qq);erg+=dec(qq);
    erg+=m_il_v(i,e);
    erg+=copy(exp,S_V_I(e,0L));
    erg+=m_il_v(3L,hilftyp);
    M_I_I(1L,hilf);
    erg+=m_scalar_polynom(hilf,ergeb);
    k=1L;
    for (j=1L;j<i;++j)
    {
      erg+=copy(S_V_I(e,j-1L),S_V_I(e,j));
      if (k<j+1L)
      {
        k=k*S_I_I(p);
        erg+=mult_apply(p,S_V_I(e,j));
      }
    }
    erg+=hoch(q,d,hilf);
    erg+=copy(hilf,hilf1);
    erg+=dec(hilf1);
    erg+=ganzdiv(hilf1,exp,hilf2);
    erg+=copy(hilf2,S_V_I(hilftyp,2L));
    erg+=copy(exp,S_V_I(hilftyp,0L));
    erg+=copy(ew,S_V_I(hilftyp,1L));
    erg+=vek_to_monom(qq,hilftyp,hilfpoly);
    erg+=mult_apply(hilfpoly,ergeb);
    for (j=1L;j<i;++j)
    {
      erg+=mult_apply(hilf,hilf1);
      erg+=ganzdiv(hilf1,S_V_I(e,j),hilf2);
      erg+=copy(hilf2,S_V_I(hilftyp,2L));
      erg+=copy(S_V_I(e,j),S_V_I(hilftyp,0L));
      erg+=ganzdiv(S_V_I(e,j),exp,hilf2);
      erg+=mod_mult(qq,ew,hilf2,S_V_I(hilftyp,1L));
      erg+=vek_to_monom(qq,hilftyp,hilfpoly);
      erg+=mult_apply(hilfpoly,ergeb);
    }
    erg+=freeall(e);
    erg+=freeall(qq);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    erg+=freeall(hilftyp);
    erg+=freeall(hilfpoly);
    if (erg!=OK) error(" in computation of zykeltyp_hyperbegleitmatrix_poly_pglkq(d,exp,ew,i,p,q,ergeb) ");
    return(erg);
}

static INT zykelind_aus_subzykelind(q,a,b) OP q,a,b;
/* Berechnet den Zyklenzeiger von PGL(k,F_q) aus dem Subzyklenzeiger
   von GL(k,F_q) auf F_q^k\{0}.
*/
{
	    INT i,j;
	    INT erg=OK;
	OP qq,hilf,hilfpoly,hmonom,hvekt;
    OP monom;
    if (S_O_K(q)!=INTEGER) return error(" zykelind_aus_subzykelind(q,a,b)  q not INTEGER");
    if (S_O_K(a)!=POLYNOM) return error(" zykelind_aus_subzykelind(q,a,b)  a not POLYNOM");
	CALLOCOBJECT5(qq,hilf,hilfpoly,hmonom,hvekt);
    if (!emptyp(b)) freeself(b);
    M_I_I(0L,qq);
    erg+=m_scalar_polynom(qq,b);
    erg+=copy(q,qq);
	erg+=dec(qq);
    monom=a;
    while (monom!=NULL)
    {
      erg+=monom_to_vek(qq,monom,hvekt);
      erg+=m_scalar_polynom(S_PO_K(monom),hilfpoly);
        for (j=0L;j<S_V_LI(hvekt);++j)
        {
            erg+=m_iindex_iexponent_monom(s_v_ii(S_V_I(hvekt,j),0L)-1L,s_v_ii(S_V_I(hvekt,j),2L),hmonom); /* HF130696 */
            erg+=mult_apply(hmonom,hilfpoly);
        }
        for (j=0L;j<S_V_LI(S_PO_S(hilfpoly));++j)
        {
/*
            erg+=ganzdiv(S_PO_SI(hilfpoly,j),qq,hilf);
            erg+=copy(hilf,S_PO_SI(hilfpoly,j));
*/
            GANZDIV_APPLY(S_PO_SI(hilfpoly,j),qq);
        }
    ADD_APPLY(hilfpoly,b);
    monom=S_PO_N(monom);
    }
	FREEALL5(qq,hilf,hilfpoly,hmonom,hvekt);
	ENDR("zykelind_aus_subzykelind");
}

static INT zykelind_dir_prod_pglkq(q,a,b,c)  
/* Berechnet aus den Subzykelindizes a und b einen 
   weiteren Subzykelindex c. Es operiere G auf X und H 
   auf Y dann operiert  G\times H auf X\times Y.
   q ist die Anzahl der Elemente im Koerper minus 1.  */
    OP a,b,c,q;
{
    OP monom1,monom2,monom3,monom4,avek,bvek,neu;
    OP hilf,hilf0,hilf1,hilf2,hilf3,hilf4; 
    INT i1,i2;
    INT erg=OK;
    if (S_O_K(q)!=INTEGER) return error("zykelind_dir_prod_pglkq(q,a,b,c)  q not INTEGER");
    if (S_O_K(a)!=POLYNOM) return error("zykelind_dir_prod_pglkq(q,a,b,c)  a not POLYNOM");
    if (S_O_K(b)!=POLYNOM) return error("zykelind_dir_prod_pglkq(q,a,b,c)  b not POLYNOM");
    if (not EMPTYP(c)) erg+=freeself(c);
    if (einsp(a)) return copy(b,c);
    else if (einsp(b)) return copy(a,c);
    
    hilf=callocobject();hilf0=callocobject();hilf1=callocobject();
    hilf2=callocobject();hilf3=callocobject();hilf4=callocobject();
    monom3=callocobject();
    monom4=callocobject();
    avek=callocobject();bvek=callocobject();
    neu=callocobject();
    erg+=m_il_v(3L,neu);
    M_I_I(0L,hilf);
    erg+=m_scalar_polynom(hilf,c);
    monom1=a;
    while (monom1!=NULL)
    { 
      erg+=monom_to_vek(q,monom1,avek);
      monom2=b;
      while (monom2!=NULL)
      {
        erg+=monom_to_vek(q,monom2,bvek);
        erg+=m_skn_po(S_PO_S(monom1),S_PO_K(monom1),NULL,monom3);
        erg+=m_skn_po(S_PO_S(monom2),S_PO_K(monom2),NULL,monom4);
        erg+=mult_apply(monom4,monom3);
        for (i1=0L;i1<S_V_LI(avek);++i1)
        {
        for (i2=0L;i2<S_V_LI(bvek);++i2)
        {
            erg+=copy(S_V_I(avek,i1),hilf1);
            erg+=copy(S_V_I(bvek,i2),hilf2);
            erg+=kgv(S_V_I(hilf1,0L),S_V_I(hilf2,0L),hilf);
            erg+=ganzdiv(hilf,S_V_I(hilf1,0L),hilf3);
            erg+=mod_mult(q,S_V_I(hilf1,1L),hilf3,hilf4);
            erg+=copy(hilf4,S_V_I(hilf1,1L));
            erg+=ganzdiv(hilf,S_V_I(hilf2,0L),hilf3);
            erg+=mod_mult(q,S_V_I(hilf2,1L),hilf3,hilf4);
            erg+=copy(hilf4,S_V_I(hilf2,1L));
            erg+=min_pot(S_V_I(hilf1,1L),S_V_I(hilf2,1L),q,hilf0);
            erg+=mod_mult(q,hilf0,S_V_I(hilf1,1L),S_V_I(neu,1L));
            erg+=mult_apply(hilf0,hilf);
            erg+=copy(hilf,S_V_I(neu,0L));
            erg+=mult(S_V_I(hilf1,2L),S_V_I(hilf2,2L),hilf);
            erg+=mult_apply(S_V_I(hilf1,0L),hilf);
            erg+=mult_apply(S_V_I(hilf2,0L),hilf);
            erg+=ganzdiv(hilf,S_V_I(neu,0L),hilf);
            erg+=copy(hilf,S_V_I(neu,2L));
            erg+=vek_to_monom(q,neu,monom4);
            erg+=mult_apply(monom4,monom3);
        }
        }
        monom2=S_PO_N(monom2);
        /*if (S_O_K(S_PO_S(monom3))==INTEGERVECTOR)  C_O_K(S_PO_S(monom3),VECTOR);*/
        erg+=add(c,monom3,c);
      }
      monom1=S_PO_N(monom1);
    }
    erg+=freeall(hilf);
    erg+=freeall(hilf0);
    erg+=freeall(hilf1);
    erg+=freeall(hilf2);
    erg+=freeall(hilf3);
    erg+=freeall(hilf4);
    erg+=freeall(monom3);
    erg+=freeall(monom4);
    freeall(neu);
    freeall(avek);
    freeall(bvek);
    ENDR("zykelind_dir_prod_pglkq");
}

static INT monom_to_vek(q,a,b) OP a,b,q;
/* Bestimmt aus dem Subzykeltyp a (einem Polynom Objekt) einen 
Vektor b, der Subzykellaenge und integrales Element von jedem Zykel
beinhaltet. Ein Zykel wird dann durch ein Tripel dargestellt:
1. Komponente: Subzykellaenge
2. Komponente: integrales Element
3. Komponente: vielfachheit des Subzykels 
q ist die um 1 verringerte Anzahl der Koerperelemente */
{
    INT i;
    INT erg=OK;
    OP typ,hilf;
    typ=callocobject();
    hilf=callocobject();
    m_il_v(3L,typ);
    m_il_v(0L,b);
    for (i=0L;i<S_V_LI(S_PO_S(a));++i)
    {     
        if (!nullp(S_V_I(S_PO_S(a),i)))
        {
          M_I_I(i,hilf);
          erg+=quores(hilf,q,S_V_I(typ,0L),S_V_I(typ,1L));
          erg+=inc(S_V_I(typ,0L));
          erg+=inc(S_V_I(typ,1L));
          erg+=copy(S_V_I(S_PO_S(a),i),S_V_I(typ,2L));
          erg+=inc(b);
          erg+=copy(typ,S_V_I(b,S_V_LI(b)-1L));
        }
    }
    erg+=freeall(typ);erg+=freeall(hilf);
    ENDR("monom_to_vek");
}

static INT vek_to_monom(q,a,b) OP a,b,q;
/* Umkehrung obiger Transformation.
   a ist ein Tripel, das den Subzykeltyp enthaelt.
   b ist ein MONOM
   q ist |F_q|-1
*/
{
    OP aa,bb;
    INT erg=OK;
    aa=callocobject();bb=callocobject();
    erg+=copy(S_V_I(a,0L),aa);
    erg+=dec(aa);
    erg+=copy(S_V_I(a,1L),bb);
    erg+=dec(bb);
    erg+=mult_apply(q,aa);
    erg+=add_apply(bb,aa);
    erg+=m_iindex_iexponent_monom(s_i_i(aa),s_v_ii(a,2L),b); /* HF130696 */
    erg+=freeall(aa);erg+=freeall(bb);
    ENDR("vek_to_monom");
}

/* ***************************************************************

Some SYMMETRICA routine to compute enumeration formulae of 
N.G. de Bruijn.

****************************************************************** */

INT debruijn_all_functions(a,b,c) OP a,b,c;
/* a und b sind Zyklenzeiger, a gehoert zu einer Gruppenaktion auf dem
Definitionsbereich X, b zu einer auf dem Bildbereich Y. c ist die Anzahl
der Orbiten von Funktionen bezueglich der Gruppeneaktion des direkten 
Produktes der zwei Gruppen auf der Menge aller Funktionen von X nach Y. 
*/
{
    INT erg=OK;
    OP hilf,hilf1,hilf2,hilfmonom,vek;
    INT i,j,k;
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    vek=callocobject();
    if (!emptyp(c)) erg+=freeself(c);
    erg+=numberofvariables(a,hilf);
    erg+=m_l_v(hilf,vek);
    M_I_I(0L,c);
    hilfmonom=b;
    while (hilfmonom!=NULL)
    {
      /*if (S_O_K(S_PO_S(hilfmonom))==INTEGERVECTOR) C_O_K(S_PO_S(hilfmonom),VECTOR);*/
      for (i=0L;i<S_V_LI(vek);++i)
      {
        erg+=m_i_i(i+1L,hilf);
        erg+=alle_teiler(hilf,hilf1);
        erg+=m_i_i(0L,hilf2);
        for (j=0L;j<S_V_LI(hilf1);++j)
        {
          if (S_V_II(hilf1,j)<=S_V_LI(S_PO_S(hilfmonom)))
          {
        erg+=mult(S_V_I(hilf1,j),S_PO_SI(hilfmonom,S_V_II(hilf1,j)-1L),hilf);
        erg+=add_apply(hilf,hilf2);
          }
        }
        erg+=copy(hilf2,S_V_I(vek,i));
      }
      erg+=eval_polynom(a,vek,hilf);
      erg+=mult_apply(S_PO_K(hilfmonom),hilf);
      erg+=add_apply(hilf,c);
      hilfmonom=S_PO_N(hilfmonom);
    }
    erg+=freeall(hilf); erg+=freeall(hilf1); erg+=freeall(hilf2);
    erg+=freeall(vek);
    if (erg!=OK) EDC("debruijn_all_functions");
    return erg;
}

static INT zykelind_red(a,c,b) OP a,b,c;
/* Je nachdem ob die Summe \sum_i i typ_i gleich c ist oder nicht  
werden die entsprechenden Monome des Zyklenzeigers a derern Typ  
typ ist zu b zusammengefasst oder nicht.*/ 
{
    OP hilfm,hilf,hilf1;
    INT erg=OK;
    hilf=callocobject();
    hilf1=callocobject();
    M_I_I(0L,hilf);
    erg+=m_scalar_polynom(hilf,b);
    hilfm=a;
    while (hilfm!=NULL)
    {
      /*if (S_O_K(S_PO_S(hilfm))==INTEGERVECTOR) C_O_K(S_PO_S(hilfm),VECTOR);*/
      erg+=sum_vector11(S_PO_S(hilfm),hilf,c);
      if (eq(hilf,c))
      {
        erg+=copy(S_PO_S(hilfm),hilf);
        erg+=m_skn_po(hilf,S_PO_K(hilfm),NULL,hilf1);
        erg+=add_apply(hilf1,b);
      }
      hilfm=S_PO_N(hilfm);
    }
    erg+=freeall(hilf1);
    erg+=freeall(hilf);
    if (erg!=OK) error(" in computation of zykelind_red(a,c,b)");
    return(erg);
}

static INT zykelind_red_apply(a,c) OP a,c;
{
    OP hilf;
    INT erg=OK;
    hilf=callocobject();
    erg+=zykelind_red(a,c,hilf);
    erg+=copy(hilf,a);
    erg+=freeall(hilf);
    if (erg!=OK) error(" in computation of zykelind_red_apply(a,c)");
    return(erg);
}

INT debruijn_inj_functions(a,b,c) OP a,b,c;
{
    OP d,hilfmonom,hilf;
    INT erg=OK;
    d=callocobject();
    hilf=callocobject();
    if (!emptyp(c)) freeself(c);
    M_I_I(0L,c);
    erg+=numberofvariables(a,hilf);
    erg+=polya2_sub(b,hilf,d);
    hilfmonom=a;
    /*if (S_O_K(S_PO_S(hilfmonom))==INTEGERVECTOR) C_O_K(S_PO_S(hilfmonom),VECTOR);*/
    erg+=sum_vector1(S_PO_S(hilfmonom),hilf);
    erg+=zykelind_red_apply(d,hilf);
    while (hilfmonom!=NULL)
    {
      /*if (S_O_K(S_PO_S(hilfmonom))==INTEGERVECTOR) C_O_K(S_PO_S(hilfmonom),VECTOR);*/
      erg+=debruijn_formel(S_PO_S(hilfmonom),d,hilf);
      erg+=mult_apply(S_PO_K(hilfmonom),hilf);
      erg+=add_apply(hilf,c);
      hilfmonom=S_PO_N(hilfmonom);
    }
    erg+=freeall(hilf);
    erg+=freeall(d);
    if (erg!=OK) error("in computation of debruijn_inj_functions(a,b,c)");
    return(erg);
}

static INT debruijn_formel(a,b,c) OP a,b,c;
{
    OP hilfm,hilf;
    INT i;
    INT erg=OK;
    hilf=callocobject();
    if (!emptyp(c)) freeself(c);
    hilfm=b;
    while (hilfm!=NULL)
    {
      /*if (S_O_K(S_PO_S(hilfm))==INTEGERVECTOR) C_O_K(S_PO_S(hilfm),VECTOR);*/
      if (comp_vector1(a,S_PO_S(hilfm))==0L)
      {
        M_I_I(1L,c);
        for (i=0L;i<S_V_LI(a);++i)
        if (S_V_II(a,i)>1L)
        {
          erg+=fakul(S_V_I(a,i),hilf);
          erg+=mult_apply(hilf,c);
        }
      erg+=mult_apply(S_PO_K(hilfm),c);
      erg+=freeall(hilf);
      if (erg!=OK) error("in computation of debruijn_formel(a,b,c)");
      return(erg);
      }
      hilfm=S_PO_N(hilfm);
    }
    M_I_I(0L,c);
    freeall(hilf);
    if (erg!=OK) error("in computation of debruijn_formel(a,b,c)");
    return(erg);
}

static INT sum_vector11(vecobj,ergebnis,gr) OP vecobj,ergebnis,gr;
/* berechnet die Summe 
$\sum_{i=0L}^{s_v_li(vecobj)-1L} (i+1)*s_v_i(vecobj,i)$  falls diese kleiner
als gr bleibt, ansonsten gibt sie die erste Teilsumme groesser als gr
aus.  */
{
    INT i;
    INT erg = OK;
    OP hilf=callocobject();
    if ((S_O_K(vecobj)!=VECTOR)&&(S_O_K(vecobj)!=INTEGERVECTOR)) 
    return error("sum_vector11(vecobj,ergebnis)  vecobj not VECTOR");
    if (!emptyp(ergebnis)) erg+=freeself(ergebnis);
    M_I_I(0L,ergebnis);
    for (    i=0L; i < S_V_LI(vecobj);i++)
        {
        erg+=m_i_i(i+1L,hilf);
        erg+=mult_apply(S_V_I(vecobj,i),hilf);
        erg += add_apply(hilf , ergebnis);
        if (gt(ergebnis,gr)) 
        {
          erg+=freeall(hilf);
          if (erg!=OK) error(" in computation of sum_vector11(vecobj,ergebnis) ");
          return(erg);
        }
        }
    erg+=freeall(hilf);
    if (erg!=OK) error(" in computation of sum_vector11(vecobj,ergebnis) ");
    return erg;
}

static INT sum_vector1(vecobj,ergebnis) OP vecobj,ergebnis;
/* berechnet die Summe 
$\sum_{i=0L}^{s_v_li(vecobj)-1L} (i+1)*s_v_i(vecobj,i)$  */
{
    INT i;
    INT erg = OK;
    OP hilf=callocobject();
    if ((S_O_K(vecobj)!=VECTOR)&&(S_O_K(vecobj)!=INTEGERVECTOR)) 
    return error("sum_vector1(vecobj,ergebnis)  vecobj not VECTOR");
    if (!emptyp(ergebnis)) erg+=freeself(ergebnis);
    M_I_I(0L,ergebnis);
    for (    i=0L; i < S_V_LI(vecobj);i++)
        {
        erg+=m_i_i(i+1L,hilf);
        erg+=mult_apply(S_V_I(vecobj,i),hilf);
        erg += add_apply(hilf , ergebnis);
        }
    if (erg!=OK) error(" in computation of sum_vector1(vecobj,ergebnis) ");
    return erg;
}

INT stirling_numbers_second_kind_vector(a,b) OP a,b;
/* a INTEGER object , 
   the result b is a VECTOR object of length a+1
   with entry s_v_i(i,b) =  2. Stirl. number S(a,i)
*/
/* HF 1994 */
/* AK 200704 V3.0 */
{
    INT erg=OK;
    CTO(INTEGER,"stirling_numbers_second_kind_vector(1)",a);
    SYMCHECK(S_I_I(a)<0,"stirling_numbers_second_kind_vector:parameter <0");
    {
    if (NULLP_INTEGER(a))
        {
        erg += m_o_v(cons_null,b);
        }
    else 
        {
        OP bb,c,d,e,f;
        INT i,j;
        CALLOCOBJECT5(bb,c,d,e,f);
        M_I_I(0L,f);
        erg+=m_il_v(S_I_I(a)+1L,b);
        M_I_I(0L,S_V_I(b,0L));
        i=0L;
        erg+=m_iindex_iexponent_monom(0L,s_i_i(a),d);
        for (j=1;j<=S_I_I(a);j++)
          {
          M_I_I(j,c);
          erg+=zykelind_Sn(c,bb);
          erg+=debruijn_all_functions(d,bb,e);
          erg+=sub(e,f,S_V_I(b,j));
          CLEVER_COPY(e,f);
          }
        FREEALL5(bb,c,d,e,f);
        }
    }
    ENDR("stirling_numbers_second_kind_vector");
}

INT polya1_sub(a,c,b) OP a,b,c;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + 2 q^i */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */ /*FRIP 15.3.94 */
{
    OP d,e,f,g;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("polya1_sub(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("polya1_sub(a,c,b) c not INTEGER");
    if (not EMPTYP(b)) erg+=freeself(b);
    d=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
    M_I_I(2L,d);
    erg += m_il_v(1L,f);
    M_I_I(1L,s_v_i(f,0L));
    erg+=m_skn_po(f,d,NULL,g);
    erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
    {
      erg += add(e,g,f); erg+=copy(f,S_V_I(d,i)); 
      erg += inc(s_v_i(S_PO_S(g),0L));
    } 
    erg += eval_polynom(a,d,b); 
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    erg += freeall(g);
    if (erg != OK) return error("polya1_sub: error during computation");
    return erg;
}

INT polya2_sub(a,c,b) OP a,b,c;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + i q^i */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */ /*FRIP 15.3.94 */
{
    OP d,e,f,g;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("polya2_sub(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("polya2_sub(a,c,b) c not INTEGER");
    if (not EMPTYP(b)) erg+=freeself(b);
    d=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
    /*M_I_I(2L,d);*/
    erg += m_il_v(1L,f);
    M_I_I(1L,s_v_i(f,0L));
    erg+=m_skn_po(f,d,NULL,g);
    erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        erg += add(e,g,f); erg+=copy(f,S_V_I(d,i)); 
        inc(s_po_s(g)); m_i_i(0L,S_PO_SI(g,i)); 
        m_i_i(1L,S_PO_SI(g,i+1L));
        /*erg += inc(S_V_I(S_PO_S(g),0L));*/
        erg += inc(S_PO_K(g));
        } 
        numberofvariables(a,f);
    while (gt(f,c))
    {
          inc(c);inc(d);copy(e,s_v_i(d,s_v_li(d)-1L));
    }
    erg += eval_polynom(a,d,b); 
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    erg += freeall(g);
    if (erg != OK)
        return error("polya2_sub: error during computation");
    return erg;
}

INT polya3_sub(a,c,dd,b) OP a,b,c,dd;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + q^i + q^2i + q^3i + ... */
/* dd ist die hoechste Potenz von q die eingesetzt werden kann  */
/* das Ergebnis stimmt nur bis zu der Potenz q^dd   */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */ /*FRIP 7.6.94 */
{
    OP d,e,f,g,h;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("polya3_sub(a,c,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("polya3_sub(a,c,b) c not INTEGER");
    if (not EMPTYP(b)) erg+=freeself(b);
    d=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    h=callocobject();
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
    erg += m_il_v(1L,f);
    M_I_I(1L,s_v_i(f,0L));
    erg+=m_skn_po(f,d,NULL,g);
    erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        erg += add(e,g,f); 
        mult(g,g,h);
        while (le(S_PO_SI(h,0L),dd)) 
        {
                    add_apply(h,f);
            mult_apply(g,h);
        }
        erg+=copy(f,S_V_I(d,i)); 
        inc(S_PO_SI(g,0L));  
        } 
    erg += eval_polynom(a,d,b); 
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(h);
    erg += freeall(f);
    erg += freeall(g);
    if (erg != OK)
        return error("polya3_sub: error during computation");
    return erg;
}

INT polya_const_sub(a,b,c) OP a,b,c;
/* a ist ein Zyklenzeiger (also ein Polynom Objekt).
b ist ein Integer Objekt. Jede Unbestimmte in a wird durch b ersetzt.
c ist das Ergebnis nach dieser Substitution.  */
{
    OP lan,vekt;
    INT erg=OK;
    INT i;
    if (S_O_K(a)!=POLYNOM) return error("polya_const_sub(a,b,c) a not POLYNOM");
    if (S_O_K(b)!=INTEGER) return error("polya_const_sub(a,b,c) b not INTEGER");
    if (not EMPTYP(c)) erg+=freeself(c);
    lan = callocobject();
    vekt= callocobject();
    erg+=numberofvariables(a,lan);
    erg+=m_l_v(lan,vekt);
    for (i=0L;i<S_I_I(lan);++i) erg+=copy(b,S_V_I(vekt,i));
    erg+=eval_polynom(a,vekt,c);
    erg+=freeall(lan);
    erg+=freeall(vekt);
    if (erg != OK) error(" in computation of polya_const_sub(a,b,c) ");
    return(erg);
}

static INT eval_polynom_maxgrad(a,b,c,d) OP a,b,c,d;
/* a ist ein Polynom in mehreren Unbestimmten
   die Unbestimmte x_i wird durch den i-ten Eintrag des Vektors b ersetzt. (dies
   sollte ein Polynom in einer Unbestimmten sein.)
   c ist ein INTEGER Objekt, das den maximalen Grad angibt.
   d ist das Resultat.
*/
{
    INT erg=OK;
    {
    OP monom1,poly2,poly3,hpoly,hilf;
    INT i;
    CALLOCOBJECT4(poly2,poly3,hpoly,hilf);
    M_I_I(0L,hilf);
    erg+=m_scalar_polynom(hilf,hpoly);
    M_I_I(1L,hilf);
    monom1=a;
    init(POLYNOM,d); // AK 141204
    while (monom1!=NULL)
    {
      erg+=m_scalar_polynom(hilf,poly2);
      for (i=0L; i<S_V_LI(S_PO_S(monom1)); ++i)
      {
        if (!nullp(S_V_I(S_PO_S(monom1),i)))
        {
          erg+=hoch_po_maxgrad(S_V_I(b,i),S_V_I(S_PO_S(monom1),i),c,hpoly);
          erg+=mult_po_po_maxgrad(hpoly,poly2,c,poly3);
          erg+=copy(poly3,poly2);
        }
      } 
      erg+=mult_apply(S_PO_K(monom1),poly2);
      erg+=add_apply(poly2,d);
      monom1=S_PO_N(monom1);
    }
    FREEALL4(poly2,poly3,hpoly,hilf);
    }
    ENDR("eval_polynom_maxgrad");
}

INT co_polya_sub(a,c,maxgrad,b) OP a,b,c,maxgrad;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + q^i */
/* maxgrad ist der maximale Grad der berechnet werden soll */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */ /*FRIP 15.3.94 */
{
    OP d,e,f,g;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("co_polya_sub(a,c,maxgrad,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("co_polya_sub(a,c,maxgrad,b) c not INTEGER");
    if (not EMPTYP(b)) erg+=freeself(b);
    d=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
    /*M_I_I(1L,d);*/
    erg += m_il_v(1L,f);
    M_I_I(1L,s_v_i(f,0L));
    erg+=m_skn_po(f,d,NULL,g);
    erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        erg += add(e,g,f); erg+=copy(f,S_V_I(d,i)); 
        erg += inc(s_v_i(S_PO_S(g),0L));
        } 
    erg += eval_polynom_maxgrad(a,d,maxgrad,b); 
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    erg += freeall(g);
    if (erg != OK)
        return error("co_polya_sub: error during computation");
    return erg;
}

static INT mult_po_po_maxgrad(a,b,maxgrad,res) OP a,b,maxgrad,res;
{
    INT erg=OK;
    OP aexp= callocobject();
    OP ergexp= callocobject();
    OP ergkoeff= callocobject();
    OP ergglied= callocobject();
    OP h3= callocobject();
    OP h1,h2;
    OP aa,bb;
    if(res==a)
    {
      aa= callocobject();
      erg+=copy(a,aa);
    }
    else aa= a;
    if(res==b)
    {
      bb= callocobject();
      erg+=copy(b,bb);
    }
    else bb= b;

    // erg+=freeself(res);
    init(POLYNOM,res); // AK 141204
    for(h1= aa;h1;h1= s_po_n(h1))
    {
      erg+=copy(s_po_si(h1,0L),aexp);
      if(gt(aexp,maxgrad)) break;
      for(h2= bb;h2;h2= s_po_n(h2))
      {
        erg+=add(aexp,s_po_si(h2,0L),ergexp);
        if(gt(ergexp,maxgrad)) break;
        erg+=mult(s_po_k(h1),s_po_k(h2),ergkoeff);
        erg+=m_il_v(1L,h3);
        erg+=copy(ergexp,s_v_i(h3,0L));
        erg+=m_skn_po(h3,ergkoeff,NULL,ergglied);
        erg+=add_apply(ergglied,res);
      }
    }
    if(bb!=b) erg+=freeall(bb);
    if(aa!=a) erg+=freeall(aa);
    FREEALL5(h3,ergglied,ergkoeff,ergexp,aexp);
    ENDR("mult_po_po_maxgrad");
}

static INT hoch_po_maxgrad(poly,expo,maxgrad,res) OP poly,expo,maxgrad,res;

{
    INT erg=OK;
    CTO(POLYNOM,"hoch_po_maxgrad(1)",poly);
    {
    OP h1= callocobject();
    OP h2= callocobject();
    OP pp;
    if(nullp(expo))
    {
      erg+=m_i_i(1L,h1);
      erg+=m_scalar_polynom(h1,res);
      goto fertig;
    }
    if(poly==res)
    {
      pp= callocobject();
      erg+=copy(poly,pp);
    }
    else
    {
      pp= poly;
      erg+=copy(poly,res);
    }
    erg+=m_i_i(2L,h1);
    while(le(h1,expo))
    {
      erg+=mult_po_po_maxgrad(res,res,maxgrad,res);
      erg+=add_apply(h1,h1);
    }
    erg+=m_i_i(2L,h2);
    erg+=div(h1,h2,h1);
    erg+=sub(expo,h1,h2);
    if(!nullp(h2))
    {
      if(einsp(h2)) erg+=copy(pp,h1);
      else erg+=hoch_po_maxgrad(pp,h2,maxgrad,h1);
      erg+=mult_po_po_maxgrad(res,h1,maxgrad,res);
    }
    fertig:
    if(pp!=poly) erg+=freeall(pp); 
    erg+=freeall(h2); erg+=freeall(h1);
    }
    ENDR("hoch_po_maxgrad");
}

INT co_polya3_sub(a,c,dd,b) OP a,b,c,dd;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + q^i + q^2i + q^3i + ... */
/* dd ist die hoechste Potenz von q die eingesetzt werden kann  */
/* das Ergebnis stimmt nur bis zu der Potenz q^dd   */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */ /*FRIP 7.6.94 */
{
    OP d,e,f,g,h;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("co_polya3_sub(a,c,dd,b) a not POLYNOM");
    if (S_O_K(c)!=INTEGER) return error("co_polya3_sub(a,c,dd,b) c not INTEGER");
    if (not EMPTYP(b)) erg+=freeself(b);
    d=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    h=callocobject();
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
    erg += m_il_v(1L,f);
    M_I_I(1L,s_v_i(f,0L));
    erg+=m_skn_po(f,d,NULL,g);
    erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        erg += add(e,g,f); 
        mult(g,g,h);
        while (le(S_PO_SI(h,0L),dd)) 
        {
                    add_apply(h,f);
            mult_apply(g,h);
        }
        erg+=copy(f,S_V_I(d,i)); 
        inc(S_PO_SI(g,0L));  
        } 
    erg += eval_polynom_maxgrad(a,d,dd,b); 
    FREEALL5(d,e,h,f,g);
    ENDR("co_polya3_sub");
}

static INT comp_vector1(a,b) OP a,b;
/* Etwas geaenderte Version von comp_vector(a,b);
   Es werden auch zwei Vektoren unterschiedlicher Laenge verglichen.
   Sind die zusaetzlichen Stellen eines der beiden Vektoren gleich 0
   so werden die Vektoren als gleich angesehen. Das Ergebnis ist gleich
   0 falls a=b
   >0 falls a>b
   <0 falls a<b.
   a und b sind 2 Vektor Objekte. */
/* AK 060488 */ /* AK 280689 V1.0 */ /* AK 201289 V1.1 */
/* AK 200891 V1.3 */
{
    INT i,erg;
    if ((S_O_K(a)!=VECTOR)&&(S_O_K(a)!=INTEGERVECTOR)) 
    return error("comp_vector1(a,b) a not VECTOR");
    if ((S_O_K(b)!=VECTOR)&&(S_O_K(b)!=INTEGERVECTOR)) 
    return error("comp_vector1(a,b) b not VECTOR");
    if (S_V_LI(a)<=S_V_LI(b)) 
    {
      for (    i=0L; i<S_V_LI(a); i++)
      {
        erg= comp(S_V_I(a,i),S_V_I(b,i));
        if (erg != 0L) return(erg);
      }
      i=S_V_LI(a);
      while (i<S_V_LI(b))
      {
        erg= (-1L)*(! nullp(S_V_I(b,i))); 
        /* erg=0 falls s_v_i(b,i) gleich 0 ist, sonst ist erg>0 */
        if (erg != 0L) return(erg);
        ++i;
      }
    }
    else
    {
      for (    i=0L; i<S_V_LI(b); i++)
      {
        erg = comp(S_V_I(a,i),S_V_I(b,i));
        if (erg != 0L) return(erg);
      }
      while (i<S_V_LI(a))
      {
        erg= (! nullp(S_V_I(a,i)));
        /* erg=0 falls s_v_i(a,i) gleich 0 ist, sonst ist erg<0 */
        if (erg != 0L) return(erg);
        ++i;
      }
    }
    return(0L);
}

static INT ordnung(a,ord) OP a,ord;
/* Berechnet die Ordnung einer Permutation vom Zykeltyp a.
   a ist ein Polynom Objekt, das den Zykeltyp der Permutation darstellt.
   ord ist die Ordnung der zugehoerigen Permutation(en).  */
{
    OP  b,c;
    INT i;
    INT erg=OK;
    if (S_O_K(a)!=POLYNOM) return error("ordnung(a,b) a not POLYNOM");
    if (not EMPTYP(ord)) erg+=freeself(ord);
    b=callocobject();
    c=callocobject();
    M_I_I(1L,ord);
    erg+=copy(S_PO_S(a),b);
    for (i=0L;i<S_V_LI(b);++i)
    {
      if (S_V_II(b,i)!=0L)
      {
        M_I_I(i+1L,c);
        erg+=kgv(ord,c,ord);
      }
    }
    erg+=freeall(b);
    erg+=freeall(c);
    if (erg != OK) error(" in computation of ordnung(a,b) ");
    return(erg);
}

INT alle_teiler(a,b) OP a,b;
/* a ist eine Integer Zahl.
   b, ein Vektor Objekt, enthaelt alle Teiler dieser Zahl. */
{
    OP aa,tei,teiler1,vielfachheit,vekt,hilf,hilf1;
    INT i,j,n;
    INT erg=OK;
    CTO(INTEGER,"alle_teiler(1)",a);
    
    if (S_I_I(a)==1L)
    {
        erg+=m_il_v(1L,b);
        M_I_I(1L,S_V_I(b,0L));
        goto endr_ende;
    }
    aa=callocobject();
    teiler1=callocobject();
    vielfachheit=callocobject();
    vekt=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    erg+=integer_factor(a,aa);/* monopoly Faktorisierung von a */
    erg+=m_il_v(0L,teiler1);
    erg+=m_il_v(0L,vielfachheit);
    tei=aa;
    while (tei != NULL)
    {
      erg+=inc(teiler1);
      erg+=inc(vielfachheit);
      erg+=copy(S_PO_S(tei),S_V_I(teiler1,S_V_LI(teiler1)-1L));
      erg+=copy(S_PO_K(tei),S_V_I(vielfachheit,S_V_LI(vielfachheit)-1L));
      /* teiler1 ist vector mit den Primteilern von a als Eintraegen */
      tei=S_L_N(tei);
    }
    n=S_V_LI(teiler1); /* Anzahl der verschiedenen Primteiler von a */
    erg+=m_il_v(0L,b);      /* b enthaelt alle Teiler von a */
    erster_kandidat(n,vekt);
    j= -1L;
    do 
    { 
      erg+=inc(b);
      ++j;
      erg+=m_i_i(1L,hilf);
      for (i=0L; i<n; ++i)
      {
        if (S_V_II(vekt,i)!=0L) 
        {
          erg+=hoch(S_V_I(teiler1,i),S_V_I(vekt,i),hilf1);
          erg+=mult(hilf,hilf1,hilf); 
          /* hilf ist ein Teiler von a */
        }
      }
      erg+=copy(hilf,S_V_I(b,j));
      i=next_kandidat2(vielfachheit,vekt);
    } while(i==1L);
    FREEALL3(aa,hilf,hilf1);
    erg+=freeall(vekt);
    erg+=freeall(vielfachheit);
    erg+=freeall(teiler1);
    ENDR("alle_teiler");
}

INT zykeltyp_pi_hoch(a,b,c)
    OP a,b,c;
/* a ist ein Vektorobjekt, das den Zykeltyp einer Permutation pi 
   enthaelt. c ist ein Polynomobjekt, das den Zykeltyp von pi^b
   enthaelt. */
{
    OP poly1,poly2,vekt;
    INT i,j;
    INT erg=OK;
    if ((S_O_K(a)!=VECTOR)&&(S_O_K(a)!=INTEGERVECTOR)) 
    return error("zykeltyp_pi_hoch(a,b,c) a not VECTOR");
    if (S_O_K(b)!=INTEGER) return error("zykeltyp_pi_hoch(a,b,c) b not INTEGER");
    if (S_I_I(b)<1L) return error("zykeltyp_pi_hoch(a,b,c) b<1");
    if (not EMPTYP(c)) erg+=freeself(c);
    poly1=callocobject();
    erg+=m_skn_po(a,cons_eins,NULL,poly1);
    if (S_I_I(b)==1L)
    {
    erg+=copy(poly1,c);
    erg+=freeall(poly1);
    if (erg != OK) error(" in computation of zykeltyp_pi_hoch(a,b,c) ");
    return(erg);
    }
    vekt=callocobject();
    poly2=callocobject();
    erg+=m_l_v(S_V_L(a),vekt);
    for (i=0L;i<S_V_LI(vekt);++i)
    {
      j=ggt_i(i+1L,S_I_I(b));
      erg+=m_iindex_iexponent_monom(((i+1L)/j)-1L,j,poly2);
      erg+=copy(poly2,S_V_I(vekt,i));
     }
    erg+=eval_polynom(poly1,vekt,c);
    erg+=freeall(vekt);
    erg+=freeall(poly1);
    erg+=freeall(poly2);
    ENDR("zykeltyp_pi_hoch");
}

static INT erster_kandidat(n,v) OP v; INT n;
{
    int i;
    INT erg=OK;
    if (n<1L) return error("erster_kandidat(n,v) n<1");
    if (not EMPTYP(v)) erg+=freeself(v);
    erg+=m_il_v(n,v);
    for (i = 0L;i < n; M_I_I(0L,S_V_I(v,i)) , ++i)
        ;
    if (erg != OK) error(" in computation of erster_kandidat(n,v) ");
    return(erg);
}

static INT next_kandidat(m,v) OP v; INT m;
{
    int i,j,fertig;
    if (m<0L) return error("next_kandidat(m,v) m<0");
    if (S_O_K(v)!=VECTOR) return error("next_kandidat(m,v) v not VECTOR");
    /* for (i=0L;i<S_V_LI(v);++i)
       {
         if (S_O_K(S_V_I(v,i))!=INTEGER) error("next_kandidat(m,v) elements of v not INTEGER");
       }*/
    i=S_V_LI(v)-1L;
    fertig=0L;
    while (fertig==0L && i >= 0L)
    {
       M_I_I(S_V_II(v,i)+1L,S_V_I(v,i));
       if (S_V_II(v,i) > m)
       {
          M_I_I(0L,S_V_I(v,i));
          i=i-1L;
       }
       else
       fertig=1L;
    }
    if (i<0L)
    return(2L); /*  alle Kandidaten aufgelistet  */
    else
    return(1L); /*  kein Fehler aufgetreten  */
}

static INT next_kandidat2(vfh,v) OP v,vfh;
{
    int i,fertig;
    if (S_O_K(vfh)!=VECTOR) return error("next_kandidat2(vfh,v) vfh not VECTOR");
    /* for (i=0;i<S_V_LI(vfh);++i)
    {
       if (S_O_K(S_V_I(vfh,i))!=INTEGER) error("next_kandidat2(vfh,v) elements of vfh not INTEGER");
       if (S_V_II(vfh,i)<0) error("next_kandidat2(vfh,v) elements of vfh <0");
    }*/
    if (S_O_K(v)!=VECTOR) return error("next_kandidat2(vfh,v) v not VECTOR");
    /* for (i=0L;i<S_V_LI(v);++i)
       {
         if (S_O_K(S_V_I(v,i))!=INTEGER) error("next_kandidat2(vfh,v) elements of v not INTEGER");
       }*/
    i=S_V_LI(v)-1L;
    fertig=0L;
    while (fertig==0L && i >= 0L)
    {
      M_I_I(S_V_II(v,i)+1L,S_V_I(v,i));
      if (S_V_II(v,i) > S_V_II(vfh,i))
      {
        M_I_I(0L,S_V_I(v,i));
        i=i-1L;
      }
      else
      fertig=1L;
    }
    if (i<0L)
    return(2L); /*  alle Kandidaten aufgelistet  */
    else
    return(1L); /*  kein Fehler aufgetreten  */
}

static INT mu(a) OP a;
/* Berechnet Moebiusfunktion(a)   */
{
    OP aa,tei;
    INT j;
    INT erg=OK;
    if (S_O_K(a)!=INTEGER) return error("mu(a) a not INTEGER");
    if (S_I_I(a)<1L) return error("mu(a) a<1");
    if (S_I_I(a)==1L) 
    {
      if (erg != OK) error(" in computation of mu(a) ");
      return(1L);
    }
    aa=callocobject();
    erg+=integer_factor(a,aa);/* monopoly Faktorisierung von a */
        j=0L;
        tei=aa;
        while (tei != NULL)
        {
          ++j;
          if(S_PO_KI(tei)>1L)
          {
        erg+=freeall(aa);
        if (erg != OK) error(" in computation of mu(a) ");
        return(0L);
          }
          tei=S_L_N(tei);
        }
        if (j%2L==0L)
        {
          erg+=freeall(aa);
          if (erg != OK) error(" in computation of mu(a) ");
          return(1L);
        }
        else
        {
          erg+=freeall(aa);
          if (erg != OK) error(" in computation of mu(a) ");
          return(-1L);
        }
}

INT coeff_of_in(a,b,c) OP a,b,c;
/* Bestimmt c, den Koeffizienten von x^a in dem Polynom b ( b ist ein
   Polynom in einer Unbestimmten). */
{
    OP poly;
    INT erg=OK;
    if (S_O_K(a)!=INTEGER) return error("coeff_of_in(a,b,c) a not INTEGER");
    if (S_I_I(a)<0L) return error("coeff_of_in(a,b,c) a<0");
    if (S_O_K(b)!=POLYNOM) return error("coeff_of_in(a,b,c) b not POLYNOM");
    if (not EMPTYP(c)) erg+=freeself(c);
    poly=b;
    while (poly!=NULL)
    {
      if (eq(a,S_PO_SI(poly,0L)))
      {
        erg+=copy(S_PO_K(poly),c);
        if (erg != OK) error(" in computation of coeff_of_in(a,b,c) ");
        return(erg);
      }
      poly=S_PO_N(poly);
    }
    M_I_I(0L,c);
    if (erg != OK) error(" in computation of coeff_of_in(a,b,c) ");
    return(erg);
}

static INT vektor_mult_apply(a,b) OP a,b;
/* Sei a[i] das i-te Element von a, dann wird a[i] als a[i]*b berechnet. */
{
    INT i;
    INT erg=OK;
    /*if (S_O_K(a)==INTEGERVECTOR) C_O_K(a,VECTOR);*/
    if ((S_O_K(a)!=VECTOR)&&(S_O_K(a)!=INTEGERVECTOR)) 
    return error("vektor_mult_apply(a,b) a not VECTOR");
    if (S_O_K(b)!=INTEGER) return error("vektor_mult_apply(a,b) b not INTEGER");
    for (i=0L;i<S_V_LI(a);++i)
    erg+=mult_apply(b,S_V_I(a,i));
    if (erg != OK) error(" in computation of vektor_mult_apply(a,b) ");
    return(erg);
}

static INT vektor_prod(a,b) OP a,b;
/* a ist ein Vektorobjekt, das Integerobjekte enthaelt.
   b wird das Produkt all dieser Eintraege des Vektors. */
{
    INT i;
    INT erg=OK;
    if ((S_O_K(a)!=VECTOR)&&(S_O_K(a)!=INTEGERVECTOR)) 
    return error("vektor_prod(a,b) a not VECTOR");
    if (not EMPTYP(b)) erg+=freeself(b);
    M_I_I(1L,b);
    for (i=0L;i<S_V_LI(a);++i)
       erg+=mult_apply(S_V_I(a,i),b);
    if (erg != OK) error(" in computation of vektor_prod(a,b) ");
    return(erg);
}

static INT vektor_kgv_prod_durch_kgv(a,b,c) OP a,b,c;
/* a ist ein Vektorobjekt, das Integerobjekte enthaelt.
   Jedes dieser Integerobjekte wird um 1 vergroessert, und von
   all diesen Zahlen das kgv (=b)  und das Produkt ueber alle Zahlen
   dividiert durch kgv (=c) bestimmt. */
{
    OP aa;
    INT i;
    INT erg=OK;
    if ((S_O_K(a)!=VECTOR)&&(S_O_K(a)!=INTEGERVECTOR)) 
    return error("vektor_kgv_prod_durch_kgv(a,b,c) a not VECTOR");
    if (not EMPTYP(b)) erg+=freeself(b);
    if (not EMPTYP(c)) erg+=freeself(c);
    if (S_V_LI(a)==1L)
    {
      M_I_I(1L,b);
      M_I_I(S_V_II(a,0L)+1L,c);
      if (erg != OK) error(" in computation of vektor_kgv_prod_durch_kgv(a,b,c) ");
      return(erg);
    }
    else
    aa=callocobject();
    erg+=copy(a,aa);
    M_I_I(1L,b);
    for (i=0L;i<S_V_LI(a);++i)
    {
      erg+=inc(S_V_I(aa,i));
      erg+=kgv(b,S_V_I(aa,i),b);
    }
    erg+=vektor_prod(aa,c);
    erg+=ganzdiv(c,b,c);
    erg+=freeall(aa);
    if (erg != OK) error(" in computation of vektor_kgv_prod_durch_kgv(a,b,c) ");
    return(erg);
}

static INT fmultinom_ext(a,b,c) OP a,b,c;
/* a ist ein INTEGER objekt.  b ist ein VECTOR objekt. Die Komponenten
von b sind wieder INTEGER objekte (groesser oder gleich 0). Das Ergebnis
c ist die Anzahl der moeglichen Anordnungen der Elemente von b. */
{
    INT i;
    OP hilfoben,hilfunten,hilf,hilf1,part;
    INT erg=OK;
    CTO(INTEGER,"fmultinom_ext",a);
    CTTO(INTEGERVECTOR,VECTOR,"fmultinom_ext",b);

    
    hilfoben=callocobject();
    hilfunten=callocobject();
    hilf=callocobject();
    hilf1=callocobject();
    part=callocobject();
    m_v_pa(b,part);
    t_VECTOR_EXPONENT(part,part);
    erg+=fakul(a,hilfoben);
    M_I_I(1L,hilfunten);
    M_I_I(0L,hilf1);
    for (i=0L;i<S_PA_LI(part);++i)
    {
      erg+=add_apply(S_PA_I(part,i),hilf1);
      erg+=fakul(S_PA_I(part,i),hilf);
      erg+=mult_apply(hilf,hilfunten);
    }
    erg+=sub(a,hilf1,hilf1);
    erg+=fakul(hilf1,hilf);
    erg+=mult_apply(hilf,hilfunten);
    erg+=div(hilfoben,hilfunten,c);
    erg+=freeall(hilfoben);
    erg+=freeall(hilfunten);
    erg+=freeall(hilf);
    erg+=freeall(hilf1);
    erg+=freeall(part);
    ENDR("internal func fmultinom_ext");
}

static INT fmultinom(a,b,c) OP a,b,c;
/* a ist ein INTEGER objekt. b ist ein VECTOR objekt. c ist der
Multinomialkoeffizient a ueber den Elementen von b.  */
{
    INT i;
    OP hilfoben,hilfunten,hilf;
    INT erg=OK;
    if (S_O_K(a)!=INTEGER) return error("fmultinom(a,b,c)  a not INTEGER");
    if (S_O_K(b)!=VECTOR) return error("fmultinom(a,b,c)  b not VECTOR");
    /* for (i=0L;i<S_V_LI(b);++i)
    {
      if (S_O_K(S_V_I(b,i))!=INTEGER) return error("fmultinom(a,b,c)  b not vector of 
    INTEGERs");
    }*/
    if (!emptyp(c)) freeself(c);
    hilfoben=callocobject();
    hilfunten=callocobject();
    hilf=callocobject();
    erg+=fakul(a,hilfoben);
    M_I_I(1L,hilfunten);
    for (i=0L;i<S_V_LI(b);++i)
    {
      erg+=fakul(S_V_I(b,i),hilf);
      erg+=mult_apply(hilf,hilfunten);
    }
    erg+=div(hilfoben,hilfunten,c);
    erg+=freeall(hilfoben);
    erg+=freeall(hilfunten);
    erg+=freeall(hilf);
    if (erg!=OK) error("  in computation of fmultinom(a,b,c) ");
    return(erg);
}

static INT first_unordered_part_into_atmost_k_parts(s,k,a) OP a; INT k,s;
/*first_pa_into_atmost_k_parts(s,k,a)*/
/* Bestimmt die erste Darstellung von s als Summe von k Summanden >=0.
Diese Darstellung wird als VECTOR a weitergegeben.  */
{
    int i;
    INT erg=OK;
    m_il_nv(k,a);
    if (k>0) M_I_I(s,S_V_I(a,k-1L));
    ENDR("internal func first_unordered_part_into_atmost_k_parts");
}

static INT next_unordered_part_into_atmost_k_parts(a) OP a;
/*next_pa_into_atmost_k_parts(a)*/
/* Berechnet den Nachfolger der Darstellung einer natuerlichen Zahl
als Summe von hoechstens k Summanden >=0.  Die natuerliche Zahl ist
dabei die Summe ueber alle Elemente von a, k ist die Laenge von a. */
{
    int i;
    INT erg = OK;
    CTO(VECTOR,"next_unordered_part_into_atmost_k_parts",a);
    i=S_V_LI(a)-1L;
    while( (i>=0L) && nullp(S_V_I(a,i)) ) --i;
    if (i<=0L)  return(2L); /* alle aufglistet */
    copy(S_V_I(a,i),S_V_I(a,S_V_LI(a)-1L));
    dec(S_V_I(a,S_V_LI(a)-1L));
    inc(S_V_I(a,i-1L));
    if (i<S_V_LI(a)-1L) M_I_I(0L,S_V_I(a,i));
    return(1L); /*  kein Fehler aufgetreten  */
    ENDR("internal func next_unordered_part_into_atmost_k_parts");
}

static INT first_part_into_atmost_k_parts(n,k,v) OP n,k,v;
/* Bestimmte die erste Partition der Zahl n in k Teile. Die Partition
wird durch ein VECTOR objekt v dargestellt.  */
{
    INT i;
    if (! emptyp(v)) freeself(v);
    m_l_v(k,v);
    copy(n,S_V_I(v,0L));
    for (i=1L;i<S_I_I(k);++i) M_I_I(0L,S_V_I(v,i));
    return OK;
}

static INT next_part_into_atmost_k_parts(v) OP v;
{
    OP hilf,hilf1,hilf2,hilf3; 
    INT i,j,l;
    INT res;
    hilf=callocobject();
    hilf1=callocobject();
    hilf2=callocobject();
    hilf3=callocobject();
    i=S_V_LI(v);
    M_I_I(0L,hilf);
    M_I_I(1L,hilf1);
    do
    {
      do
      {
        --i;
        add_apply(S_V_I(v,i),hilf);
      } while ((i>=1L) && (le(S_V_I(v,i),hilf1)));
      if ((i==0L) && (eq(S_V_I(v,i),hilf1)))  
        {
        res=2L;
        goto ende;
        }
      copy(S_V_I(v,i),hilf1);
      dec(hilf1);
      quores(hilf,hilf1,hilf2,hilf3);
      if (nullp(hilf3)) l=0L;
      else l=1L;
      if (S_I_I(hilf2)+i+l<=S_V_LI(v))
      {
        for (j=0L;j<S_I_I(hilf2);++j) copy(hilf1,S_V_I(v,i+j));
        if (l==1L) 
        { 
          copy(hilf3,S_V_I(v,i+j));
          ++j;
        }
        for (;i+j<S_V_LI(v);++j)
        {
          if (!nullp(S_V_I(v,i+j))) copy(cons_null,S_V_I(v,i+j));
        }
        res = 1L;
        goto ende;
      }
      else
      if (i==0L) 
        {
        res=2L;
        goto ende;
        }
      else
      inc(hilf1);
    } while(1L==1L);
ende:
    freeall(hilf);
    freeall(hilf1);
    freeall(hilf2);
    freeall(hilf3);
    return res;
}

INT frip_latex_zykelind(a) OP a;
{
    OP monom;
    INT i;
    if (S_O_K(a)!=POLYNOM) return error("frip_latex_zykelind(a)  a not POLYNOM");
    printf("$ ");
    monom=a;
    while (monom!=NULL)
    {
      if (!einsp(S_PO_K(monom)))
      {
        print(S_PO_K(monom));
        printf(" ");
      }
      for (i=0L;i<S_V_LI(S_PO_S(monom));++i)
      if (!nullp(S_V_I(S_PO_S(monom),i))) 
      {
        if (!einsp(S_V_I(S_PO_S(monom),i))) 
        printf("x_{%d}^{%d}\n",i+1L,S_V_II(S_PO_S(monom),i));
        else
        printf("x_{%d}\n",i+1L);
      }
      if (S_PO_N(monom)!=NULL) printf("+");
      monom=S_PO_N(monom);
    }
    printf("$\n");
    return OK;
}

/* **************************************************************

Routines for computing the Redfield cup and cap product.

***************************************************************** */

INT redf_cap_hoch(a,n,b) OP a,n,b;
{
    INT i,fertig;
    OP hilfk,hilf,c;
    INT erg=OK;
    if (S_O_K(a)!=VECTOR) return error("redf_cap_hoch(a,n,b)  a is not VECTOR");
    if (S_O_K(n)!=VECTOR) return error("redf_cap_hoch(a,n,b)  n is not VECTOR");
    if (!eq(S_V_L(a),S_V_L(n)))
       return error("redf_cap_hoch(a,n,b) a and n of different length");
    if (S_V_LI(a)==0L) return error("redf_cap_hoch(a,n,b) a is a VECTOR of length 0");
    for (i=0L;i<S_V_LI(a);++i)
    {
      if (S_O_K(S_V_I(a,i))!=POLYNOM)
         return error("redf_cap_hoch(a,n,b) elements of a not POLYNOM");
      if (S_O_K(S_V_I(n,i))!=INTEGER)
         return error("redf_cap_hoch(a,n,b) elements of n not INTEGER");
    }
    if (not EMPTYP(b)) erg+=freeself(b);
    M_I_I(0L,b);
    hilfk=callocobject();
    hilf=callocobject();
    if (eq(S_V_L(a),cons_eins))
    {
      c=S_V_I(a,0L);
      while (c!=NULL)
      {
        erg+=redf_formel(S_PO_S(c),S_V_II(n,0L)-1L,hilfk);
        erg+=hoch(S_PO_K(c),S_V_I(n,0L),hilf);
        erg+=mult_apply(hilf,hilfk);
        erg+=add_apply(hilfk,b);
        c=S_PO_N(c);
      }
    }
    else
    {
      OP nn=callocobject();
      OP hilf1=callocobject();
      erg+=copy(S_V_I(a,0L),hilf);
      copy(S_V_I(n,0l),hilf1);
      for (i=1L;i<S_V_LI(a);++i)
      {
        erg+=redf_f1h(hilf,S_V_I(a,i),hilf1,S_V_I(n,i),hilfk);
        erg+=copy(hilfk,hilf);
        if (i==1L) M_I_I(1L,hilf1);
      }
      erg+=sum_vector(n,nn);
      c=hilf;
      while (c!=NULL)
      {
        erg+=redf_formel(S_PO_S(c),S_I_I(nn)-1L,hilfk);
        erg+=mult_apply(S_PO_K(c),hilfk);
        erg+=add_apply(hilfk,b);
        c=S_PO_N(c);
      }
      erg+=freeall(nn);
      erg+=freeall(hilf1);
    }
    erg+=freeall(hilfk);
    erg+=freeall(hilf);
    if (erg != OK) error(" in computation of redf_cap_hoch(a,n,b) ");
    return(erg);
}

INT redf_cup_hoch(a,n,b) OP a,n,b;
{
    INT i,fertig;
    OP hilfk,hilf,c;
    INT erg=OK;
    if (S_O_K(a)!=VECTOR) return error("redf_cup_hoch(a,n,b)  a is not VECTOR");
    if (S_O_K(n)!=VECTOR) return error("redf_cup_hoch(a,n,b)  n is not VECTOR");
    if (!eq(S_V_L(a),S_V_L(n)))
       return error("redf_cup_hoch(a,n,b) a and n of different length");
    if (S_V_LI(a)==0L) return error("redf_cup_hoch(a,n,b) a is a VECTOR of length 0");
    for (i=0L;i<S_V_LI(a);++i)
    {
      if (S_O_K(S_V_I(a,i))!=POLYNOM)
         return error("redf_cup_hoch(a,n,b) elements of a not POLYNOM");
      if (S_O_K(S_V_I(n,i))!=INTEGER)
         return error("redf_cup_hoch(a,n,b) elements of n not INTEGER");
    }
    if (not EMPTYP(b)) erg+=freeself(b);
    hilfk=callocobject();
    hilf=callocobject();
    if (eq(S_V_L(a),cons_eins))
    {
      copy(S_V_I(a,0L),b);
      c=b;
      while (c!=NULL)
      {
        erg+=redf_formel(S_PO_S(c),S_V_II(n,0L)-1L,hilfk);
        erg+=hoch(S_PO_K(c),S_V_I(n,0L),hilf);
        erg+=mult(hilf,hilfk,S_PO_K(c));
        c=S_PO_N(c);
      }
    }
    else
    {
      OP nn=callocobject();
      OP hilf1=callocobject();
      erg+=copy(S_V_I(a,0L),hilf);
      copy(S_V_I(n,0l),hilf1);
      for (i=1L;i<S_V_LI(a);++i)
      {
        erg+=redf_f1h(hilf,S_V_I(a,i),hilf1,S_V_I(n,i),hilfk);
        erg+=copy(hilfk,hilf);
        if (i==1L) M_I_I(1L,hilf1);
      }
      erg+=sum_vector(n,nn);
      c=hilf;
      while (c!=NULL)
      {
        erg+=redf_formel(S_PO_S(c),S_I_I(nn)-1L,hilfk);
        erg+=mult_apply(hilfk,S_PO_K(c));
        c=S_PO_N(c);
      }
      erg+=freeall(nn);
      erg+=freeall(hilf1);
      erg+=copy(hilf,b);
    }
    erg+=freeall(hilfk);
    erg+=freeall(hilf);
    if (erg != OK) error(" in computation of redf_cup_hoch(a,n,b) ");
    return(erg);
}

INT redf_cap(a,b) OP a,b;
/* Berechnet das cap-Produkt der Polynome, die in dem Vektor
   a uebergeben werden. Das Ergebnis ist b. */
{
    INT erg=OK;
    OP hpoly,hpoly1,monom;
    INT i;
    if (S_O_K(a)!=VECTOR) return error("redf_cap(a,b)  a not VECTOR");
    if (S_V_LI(a)<=1L) 
       return error("redf_cap(a,b) there must be at least 2 cycle indices in a");
    for (i=0L;i<S_V_LI(a);++i)
    {
      if (S_O_K(S_V_I(a,i))!=POLYNOM) 
         return error("redf_cap(a,b)  Elements of a not POLYNOM");
    }

    hpoly=callocobject();
    hpoly1=callocobject();
    erg+=m_i_i(0L,b);
    erg+=copy(S_V_I(a,0L),hpoly);
    for (i=1L;i<S_V_LI(a);++i)
    {
      erg+=redf_f1(hpoly,S_V_I(a,i),hpoly1);
      erg+=copy(hpoly1,hpoly);
    }
    monom=hpoly;
    while (monom!=NULL)
    {
      erg+=redf_formel(S_PO_S(monom),S_V_LI(a)-1L,hpoly1);
      erg+=mult_apply(S_PO_K(monom),hpoly1);
      erg+=add_apply(hpoly1,b);
      monom=S_PO_N(monom);
    }
    erg+=freeall(hpoly); 
    erg+=freeall(hpoly1);
    ENDR("redf_cap");
}

INT redf_cup(a,b) OP a,b;
/* Berechnet das cup-Produkt der Polynome, die im Vektor a
   uebergeben werden. Das Ergebnis ist b.  */
{
    INT erg=OK;
    OP hpoly,hpoly1,monom;
    INT i;
    if (S_O_K(a)!=VECTOR) return error("redf_cup(a,b)  a not VECTOR");
    if (S_V_LI(a)<=1L) 
       return error("redf_cup(a,b) there must be at least 2 cycle indices in a");
    for (i=0L;i<S_V_LI(a);++i)
    {
      if (S_O_K(S_V_I(a,i))!=POLYNOM) 
         return error("redf_cup(a,b)  Elements of a not POLYNOM");
    }
    if (not EMPTYP(b)) erg+=freeself(b);
    hpoly=callocobject();
    hpoly1=callocobject();
    erg+=copy(S_V_I(a,0L),hpoly);
    for (i=1L;i<S_V_LI(a);++i)
    {
      erg+=redf_f1(hpoly,S_V_I(a,i),hpoly1);
      erg+=copy(hpoly1,hpoly);
    }
    monom=hpoly;
    while (monom!=NULL)
    {
      erg+=redf_formel(S_PO_S(monom),S_V_LI(a)-1L,hpoly1);
      erg+=mult_apply(hpoly1,S_PO_K(monom));
      monom=S_PO_N(monom);
    }
    erg+=copy(hpoly,b);
    erg+=freeall(hpoly); erg+=freeall(hpoly1);
    if (erg!=OK) return error(" in computation of redf_cup(a,b) ");
    return erg;
}

static INT redf_f1(a,b,c) OP a,b,c;
/* a,b sin POLYNOME, c wird ein neues POLYNOM, dessen MONOMe sowohl in
   a als auch in b vorkommen. Die entsprechenden Koeffizienten werden
   zusammenmultipliziert.
   Dazu werden a und b in Listen umgewandelt. Diese Listen werden in
   redf_f2 auf gleiche MONOM-VECTOREN untersucht, und c wird dann in
   redf_f3 aufgebaut.
*/
{
    INT erg=OK;
    OP al=callocobject();
    OP bl=callocobject();
    erg+=copy_list(a,al);
    erg+=copy_list(b,bl);
    erg+=m_i_i(0L,c);
    erg+=redf_f2(al,bl,c);
    erg+=freeall(al);erg+=freeall(bl);
    if (erg!=OK) return error(" in computation of redf_f1");
    return erg;
}

static INT redf_f2(von,nach,har) OP von,nach,har; 
/* untersucht die Listen von und nach auf gleiche MONOM-VECTORen
   Falls solche auftreten wird redf_f3 aufgerufen.
*/
{
    INT erg;
    OP nn = callocobject();
    *nn = *nach;
    while((von != NULL) && (nn != NULL))
    {
        erg=comp_monomvector_monomvector(S_L_S(von),S_L_S(nn));
        if (erg < 0L) von = S_L_N(von);
        else if (erg >0L) nn = S_L_N(nn);
        else 
        {
          redf_f3(S_L_S(von),S_L_S(nn),har);
          nn = S_L_N(nn);
        }
    }
    return(OK);
}

static INT redf_f3(a,b,c) OP a,b,c;
/* a,b sin MONOMe mit gleichem S_MO_S VECTOR
   ihre Koeffizienten werden zusammenmultipliziert und als neuer
   Term zu c (POLYNOM) mit S_MO_S VECTOR dazuaddiert
*/
{
    INT erg=OK;
    OP hilf=callocobject();
    OP monom=callocobject();
    erg+=mult(S_MO_K(a),S_MO_K(b),hilf);
    erg+=m_skn_po(S_MO_S(a),hilf,NULL,monom);
    erg+=add_apply(monom,c);
    erg+=freeall(hilf); erg+=freeall(monom);
    if (erg!=OK) EDC("redf_f3");
    return erg;
}

static INT redf_f1h(a,b,na,nb,c) OP a,b,na,nb,c;
/* a,b sin POLYNOME, c wird ein neues POLYNOM, dessen MONOMe sowohl in
   a als auch in b vorkommen. Die entsprechenden Koeffizienten werden
   zusammenmultipliziert.
   Dazu werden a und b in Listen umgewandelt. Diese Listen werden in
   redf_f2h auf gleiche MONOM-VECTOREN untersucht, und c wird dann in
   redf_f3h aufgebaut.
   na und nb sind die Vielfachheiten, mit denen a bzw b auftritt
*/
{
    INT erg=OK;
    OP al=callocobject();
    OP bl=callocobject();
    erg+=copy_list(a,al);
    erg+=copy_list(b,bl);
    erg+=m_i_i(0L,c);
    erg+=redf_f2h(al,bl,na,nb,c);
    erg+=freeall(al);erg+=freeall(bl);
    if (erg!=OK) return error(" in computation of redf_f1h");
    return erg;
}

static INT redf_f2h(von,nach,na,nb,har) OP von,nach,na,nb,har; 
/* untersucht die Listen von und nach auf gleiche MONOM-VECTORen
   Falls solche auftreten wird redf_f3h aufgerufen.
*/
{
    INT erg;
    OP nn = callocobject();
    *nn = *nach;
    while((von != NULL) && (nn != NULL))
    {
        erg=comp_monomvector_monomvector(S_L_S(von),S_L_S(nn));
        if (erg < 0L) von = S_L_N(von);
        else if (erg >0L) nn = S_L_N(nn);
        else 
        {
          redf_f3h(S_L_S(von),S_L_S(nn),na,nb,har);
          nn = S_L_N(nn);
        }
    }
    return(OK);
}

static INT redf_f3h(a,b,na,nb,c) OP a,b,na,nb,c;
/* a,b sin MONOMe mit gleichem S_MO_S VECTOR
   ihre Koeffizienten werden zusammenmultipliziert und als neuer
   Term zu c (POLYNOM) mit S_MO_S VECTOR dazuaddiert
*/
{
    INT erg=OK;
    OP hilf=callocobject();
    OP monom=callocobject();
    erg+=hoch(S_MO_K(a),na,hilf);
    erg+=hoch(S_MO_K(b),nb,monom);
    erg+=mult_apply(monom,hilf);
    erg+=freeself(monom);
    erg+=m_skn_po(S_MO_S(a),hilf,NULL,monom);
    erg+=add_apply(monom,c);
    erg+=freeall(hilf); erg+=freeall(monom);
    if (erg!=OK) EDC("redf_f3h");
    return erg;
}

static INT redf_formel(a,n,b) OP a,b; INT n;
/* Berechnet den Koeffizienten fuer die Errechnung des 
   cup bzw. cap Produktes von n+1 gleichen Monomen mit der
   Gestalt a (ist ein Vektor Objekt). Das Ergebnis ist b. */
{
    OP hilf;
    INT i,erg;
    erg=OK;
    if (a==NULL) return m_i_i(0L,b);
    if ((S_O_K(a)!=VECTOR) && (S_O_K(a)!=INTEGERVECTOR)) 
       return error("redf_formel(a,n,b)  a not VECTOR");
    if (not EMPTYP(b)) erg+=freeself(b);
    if (n<1L) return error("redf_formel(a,n,b)  n<1");
    hilf=callocobject();
    erg+=m_i_i(1L,b);
    for (i=0L; i<S_V_LI(a); ++i)
    { 
      if (S_V_II(a,i)!=0L) 
      {
        erg+=fakul(S_V_I(a,i),hilf);
        erg+=mult(b,hilf,b);
        erg+=m_i_i(i+1L,hilf);
        erg+=hoch(hilf,S_V_I(a,i),hilf);
        erg+=mult(b,hilf,b);
      }
    }
    erg+=m_i_i(n,hilf);
    erg+=hoch(b,hilf,b);
    erg+=freeall(hilf);
    if (erg != OK) error(" in computation of redf_formel(a,n,b) ");
    return(erg);
}

/* *************************************************************

Routines for handling multi-dimensional cycle indices. Especially
the cycle indices of the symmetry groups of Platonic solids.

***************************************************************** */

INT mz_vereinfachen(aa,c) OP aa,c;
{
    INT i,j,k,l;
    INT erg=OK;
    OP vector=callocobject();
    OP hilf=callocobject();
    OP monom,a,b;
    a=s_mz_po(aa);
    b=s_mz_v(aa);
    m_i_i(0L,c);
    l=S_V_LI(b);
    monom=a;
    while (monom!=NULL)
    {
      m_il_v(l,vector);
      j=0L;
      for (i=0L;i<S_V_LI(S_PO_S(monom));++i)
      {
        if ((j<l) && (i==S_V_II(b,j))) 
        {
          m_il_v(0L,S_V_I(vector,j));
          ++j;
          k= -1L;
        }
        erg+=inc(S_V_I(vector,j-1L));
        erg+=copy(S_V_I(S_PO_S(monom),i),S_V_I(S_V_I(vector,j-1L),++k));
      }
      for (i=1L;i<l;++i) erg+=add_apply(S_V_I(vector,i),S_V_I(vector,0L));
      erg+=m_skn_po(S_V_I(vector,0L),S_PO_K(monom),NULL,hilf);
      erg+=add_apply(hilf,c);
      erg+=freeself(vector);
      monom=S_PO_N(monom);
    }
    erg+=freeall(vector);
    erg+=freeall(hilf);
    ENDR("mz_vereinfachen");
}

INT mz_extrahieren(aa,c,dd)
    OP aa,c,dd;
/* aa ist ein Zyklenzeiger mit mehreren Familien von Unbekannten.
c ist ein Vektor Objekt. Die Laenge des Vektors gibt an, wieviele
Teilfamilien von Unbestimmten ausgewaehlt werden. Die Eintraege in
c sind die Nummern der Familien von Unbestimmten, also 1,2,3,.... 
Diese sollen der Groesse nach angeordnet sein.
d ist der neue Zyklenzeiger.  (ein oder mehrdimensional, je nachdem
wie viele Familien extrahiert wurden.  */
{
    OP a,b,d,e,variablen,vektor,hilf;
    INT i,j,k,ihilf;
    INT erg=OK;
    if (S_O_K(aa)!=VECTOR) return error("mz_extrahieren(a,b,c) a not a cycle index in several alphabets 1");
    a=s_mz_po(aa);
    b=s_mz_v(aa);
    if (S_O_K(b)!=VECTOR) return error("mz_extrahieren(a,b,c) a not a cycle index in several alphabets 2");
    if (S_O_K(a)!=POLYNOM) return error("mz_extrahieren(a,b,c) a not a cycle index in several alphabets 3");
    if (S_O_K(c)!=VECTOR) return error("mz_extrahieren(a,b,c) b not VECTOR");
    for (i=0L;i<S_V_LI(b);++i)
    {
      if (S_O_K(S_V_I(b,i))!=INTEGER) return error("mz_extrahieren(a,b,c) Elements of s_mz_v(a) not INTEGER");
    }
    for (i=1L;i<S_V_LI(b);++i)
    {
      if (S_V_II(b,i)<=S_V_II(b,i-1L)) return error("mz_extrahieren(a,b,c) Elements of s_mz_v(a) not increasing");
    }
    for (i=0L;i<S_V_LI(c);++i)
    {
      if (S_O_K(S_V_I(c,i))!=INTEGER) return error("mz_extrahieren(a,b,c) Elements of b not INTEGER");
    }
    for (i=1L;i<S_V_LI(c);++i)
    {
      if (S_V_II(c,i)<=S_V_II(c,i-1L)) return error("mz_extrahieren(a,b,c) Elements of b not increasing");
    }
    if (not EMPTYP(dd)) erg+=freeself(dd);
    variablen=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    d=callocobject();
    e=callocobject();
    erg+=m_l_v(s_v_l(c),e);
    M_I_I(0L,S_V_I(e,0L));
    erg+=numberofvariables(a,variablen);
    erg+=m_l_v(variablen,vektor);
    j=0L;
    i=0L;
    for (k=0L; k<S_V_LI(c); ++k)
    {
        ihilf=s_mz_vii(aa,S_V_II(c,k)-1L); 
        for (;i<ihilf;++i) 
        M_I_I(1L,s_v_i(vektor,i));
        while (S_V_II(b,j)<ihilf) ++j;
        if (j+1L<S_V_LI(b))
        {
          if (k<S_V_LI(c)-1L) 
          M_I_I(S_V_II(b,j+1L)-S_V_II(b,j)+S_V_II(e,k),S_V_I(e,k+1L));
          for (i=S_V_II(b,j);i<S_V_II(b,j+1L);++i)
        {
          erg+=m_iindex_monom(i-S_V_II(b,j)+S_V_II(e,k),hilf);
          erg+=copy(hilf,S_V_I(vektor,i));
        }
          if (k==S_V_LI(c)-1L)
          {
        ++j;
        for (i=S_V_II(b,j);i<S_V_LI(vektor);++i) 
        M_I_I(1L,S_V_I(vektor,i)); 
          }
        }
        else
        {
          for (i=S_V_II(b,j);i<S_I_I(variablen);++i)
        {
          erg+=m_iindex_monom(i-S_V_II(b,j)+S_V_II(e,k),hilf);
          erg+=copy(hilf,S_V_I(vektor,i));
        }
        }
     }
    erg+=eval_polynom(a,vektor,d);
    erg+=m_v_po_mz(e,d,dd);
    erg+=freeall(variablen); erg+=freeall(vektor); erg+=freeall(hilf);
    erg+=freeall(d); 
    erg+=freeall(e);
    ENDR("mz_extrahieren");
}

OP s_mz_v(a) OP a;
/* select_multizykelind_vector */
{
    return (s_v_i(a,0L));
}

OP s_mz_vi(a,i) OP a;
/* select_multizykelind_vector-ith */
    INT i;
{
    return(S_V_I(S_V_I(a,0L),i));
}

INT s_mz_vii(a,i) OP a;
/* select_multizykelind_vector-ith as integer */
    INT i;
{
    return(S_V_II(S_V_I(a,0L),i));
}

OP s_mz_po(a) OP a;
/* select_multizykelind_polynom */
{
    return (S_V_I(a,1L));
}

INT m_v_po_mz(v,p,z) OP v,p,z;
/* make_v_polynom_multizykelind */
{
    INT erg=OK;
    if (S_V_LI(v)>1L)
    {
      erg+=m_il_v(2L,z);
      erg+=copy(v,S_V_I(z,0L));
      erg+=copy(p,S_V_I(z,1L));
    }
    else erg+=copy(p,z);
    ENDR("m_v_po_mz");
}

INT zykelind_tetraeder(aa) OP aa;
/* Berechnet den Zyklenzeiger der Drehgruppe des Tetraeders.
Es treten 3 Familien von Unbestimmten auf. Die erste Familie
bezieht sich auf Gruppenaktion auf der Menge der Knoten, die zweite
auf der Menge der Kanten und die dritte auf der Menge der Flaechen
des Tetraeders.  */
{
    OP a,b,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    a=callocobject();
    b=callocobject();
    erg+=m_ioiu_b(1L,12L,koef);
    erg+=m_il_v(11L,vektor);
    for (i=0L;i<S_V_LI(vektor);++i) M_I_I(0L,S_V_I(vektor,i));
    M_I_I(4L,S_V_I(vektor,0L));
    M_I_I(6L,S_V_I(vektor,4L));
    M_I_I(4L,S_V_I(vektor,8L));
    erg+=m_skn_po(vektor,koef,NULL,a);
    erg+=m_ioiu_b(8L,12L,koef);
    M_I_I(1L,S_V_I(vektor,0L));
    M_I_I(1L,S_V_I(vektor,2L));
    M_I_I(0L,S_V_I(vektor,4L));
    M_I_I(2L,S_V_I(vektor,6L));
    M_I_I(1L,S_V_I(vektor,8L));
    M_I_I(1L,S_V_I(vektor,10L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(3L,12L,koef);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(2L,S_V_I(vektor,1L));
    M_I_I(0L,S_V_I(vektor,2L));
    M_I_I(2L,S_V_I(vektor,4L));
    M_I_I(2L,S_V_I(vektor,5L));
    M_I_I(0L,S_V_I(vektor,6L));
    M_I_I(0L,S_V_I(vektor,8L));
    M_I_I(2L,S_V_I(vektor,9L));
    M_I_I(0L,S_V_I(vektor,10L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_il_v(3L,b);
    M_I_I(0L,S_V_I(b,0L));
    M_I_I(4L,S_V_I(b,1L));
    M_I_I(8L,S_V_I(b,2L));
    erg+=freeall(hilf); erg+=freeall(vektor); erg+=freeall(koef);
    erg+=m_v_po_mz(b,a,aa);
    erg+=freeall(a); 
    erg+=freeall(b);
    ENDR("zykelind_tetraeder");
}

INT zykelind_tetraeder_extended(aa) OP aa;
/* Berechnet den Zyklenzeiger der Gruppe aller Symmetrien des 
Tetraeders. Es treten 3 Familien von Unbestimmten auf. Die erste Familie
bezieht sich auf Gruppenaktion auf der Menge der Knoten, die zweite
auf der Menge der Kanten und die dritte auf der Menge der Flaechen
des Tetraeders.  */
{
    OP a,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    erg+=zykelind_tetraeder(aa);
    a=s_mz_po(aa);
    erg+=m_ioiu_b(1L,2L,koef);
    erg+=m_scalar_polynom(koef,hilf);
    erg+=mult(hilf,a,a);
    erg+=m_ioiu_b(1L,4L,koef);
    erg+=m_il_v(12L,vektor);
    for (i=0L;i<s_v_li(vektor);++i) M_I_I(0L,S_V_I(vektor,i));
    M_I_I(2L,S_V_I(vektor,0L));
    M_I_I(1L,S_V_I(vektor,1L));
    M_I_I(2L,S_V_I(vektor,4L));
    M_I_I(2L,S_V_I(vektor,5L));
    M_I_I(2L,S_V_I(vektor,8L));
    M_I_I(1L,S_V_I(vektor,9L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(0L,S_V_I(vektor,1L));
    M_I_I(1L,S_V_I(vektor,3L));
    M_I_I(0L,S_V_I(vektor,4L));
    M_I_I(1L,S_V_I(vektor,5L));
    M_I_I(1L,S_V_I(vektor,7L));
    M_I_I(0L,S_V_I(vektor,8L));
    M_I_I(0L,S_V_I(vektor,9L));
    M_I_I(1L,S_V_I(vektor,11L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=freeall(hilf); erg+=freeall(vektor); erg+=freeall(koef);
    if (erg != OK) error(" in computation of zykelind_tetraeder_extended(a) ");
    return(erg);
}

INT zykelind_tetraeder_vertices(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_vertices(a) ");
    return(erg);
}

INT zykelind_tetraeder_edges(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_edges(a) ");
    return(erg);
}

INT zykelind_tetraeder_faces(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_faces(a) ");
    return(erg);
}

INT zykelind_tetraeder_vertices_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_vertices_extended(a) ");
    return(erg);
}

INT zykelind_tetraeder_edges_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_edges_extended(a) ");
    return(erg);
}

INT zykelind_tetraeder_faces_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_tetraeder_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_tetraeder_faces_extended(a) ");
    return(erg);
}

INT zykelind_cube(aa) OP aa;
/* Berechnet den Zyklenzeiger der Drehgruppe des Wuerfels.
Es treten 3 Familien von Unbestimmten auf. Die erste Familie
bezieht sich auf Gruppenaktion auf der Menge der Knoten, die zweite
auf der Menge der Kanten und die dritte auf der Menge der Flaechen
des Wuerfels. */
{
    OP a,b,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    a=callocobject();
    b=callocobject();
    erg+=m_ioiu_b(1L,24L,koef);
    erg+=m_il_v(16L,vektor);
    for (i=0L;i<S_V_LI(vektor);++i) 
    M_I_I(0L,S_V_I(vektor,i));
    M_I_I(8L,S_V_I(vektor,0L));
    M_I_I(12L,S_V_I(vektor,6L));
    M_I_I(6L,S_V_I(vektor,12L));
    erg+=m_skn_po(vektor,koef,NULL,a);
    erg+=m_ioiu_b(1L,3L,koef);
    M_I_I(2L,S_V_I(vektor,0L));
    M_I_I(2L,S_V_I(vektor,2L));
    M_I_I(0L,S_V_I(vektor,6L));
    M_I_I(4L,S_V_I(vektor,8L));
    M_I_I(0L,S_V_I(vektor,12L));
    M_I_I(2L,S_V_I(vektor,14L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,8L,koef);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(4L,S_V_I(vektor,1L));
    M_I_I(0L,S_V_I(vektor,2L));
    M_I_I(6L,S_V_I(vektor,7L));
    M_I_I(0L,S_V_I(vektor,8L));
    M_I_I(2L,S_V_I(vektor,12L));
    M_I_I(2L,S_V_I(vektor,13L));
    M_I_I(0L,S_V_I(vektor,14L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,4L,koef);
    M_I_I(2L,S_V_I(vektor,6L));
    M_I_I(5L,S_V_I(vektor,7L));
    M_I_I(0L,S_V_I(vektor,8L));
    M_I_I(0L,S_V_I(vektor,12L));
    M_I_I(3L,S_V_I(vektor,13L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    M_I_I(0L,S_V_I(vektor,1L));
    M_I_I(2L,S_V_I(vektor,3L));
    M_I_I(0L,S_V_I(vektor,6L));
    M_I_I(0L,S_V_I(vektor,7L));
    M_I_I(3L,S_V_I(vektor,9L));
    M_I_I(2L,S_V_I(vektor,12L));
    M_I_I(0L,S_V_I(vektor,13L));
    M_I_I(1L,S_V_I(vektor,15L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_il_v(3L,b);
    M_I_I(0L,S_V_I(b,0L));
    M_I_I(6L,S_V_I(b,1L));
    M_I_I(12L,S_V_I(b,2L));
    erg+=freeall(hilf); erg+=freeall(vektor); erg+=freeall(koef);
    erg+=m_v_po_mz(b,a,aa);
    erg+=freeall(a); erg+=freeall(b);
    if (erg != OK) error(" in computation of zykelind_cube(a) ");
    return(erg);
}

INT zykelind_cube_extended(aa) OP aa;
{
    OP a,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    erg+=zykelind_cube(aa);
    a=s_mz_po(aa);
    erg+=m_ioiu_b(1L,2L,koef);
    erg+=m_scalar_polynom(koef,hilf);
    erg+=mult(hilf,a,a);
    erg+=m_ioiu_b(1L,8L,koef);
    erg+=m_il_v(18L,vektor);
    for (i=0L;i<S_V_LI(vektor);++i) M_I_I(0L,S_V_I(vektor,i));
    M_I_I(4L,S_V_I(vektor,0L));
    M_I_I(2L,S_V_I(vektor,1L));
    M_I_I(2L,S_V_I(vektor,6L));
    M_I_I(5L,S_V_I(vektor,7L));
    M_I_I(2L,S_V_I(vektor,12L));
    M_I_I(2L,S_V_I(vektor,13L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(0L,S_V_I(vektor,1L));
    M_I_I(2L,S_V_I(vektor,3L));
    M_I_I(0L,S_V_I(vektor,6L));
    M_I_I(0L,S_V_I(vektor,7L));
    M_I_I(3L,S_V_I(vektor,9L));
    M_I_I(0L,S_V_I(vektor,12L));
    M_I_I(1L,S_V_I(vektor,13L));
    M_I_I(1L,S_V_I(vektor,15L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,48L,koef);
    M_I_I(4L,S_V_I(vektor,1L));
    M_I_I(0L,S_V_I(vektor,3L));
    M_I_I(6L,S_V_I(vektor,7L));
    M_I_I(0L,S_V_I(vektor,9L));
    M_I_I(3L,S_V_I(vektor,13L));
    M_I_I(0L,S_V_I(vektor,15L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,16L,koef);
    M_I_I(4L,S_V_I(vektor,6L));
    M_I_I(4L,S_V_I(vektor,7L));
    M_I_I(4L,S_V_I(vektor,12L));
    M_I_I(1L,S_V_I(vektor,13L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,6L,koef);
    M_I_I(1L,S_V_I(vektor,1L));
    M_I_I(1L,S_V_I(vektor,5L));
    M_I_I(0L,S_V_I(vektor,6L));
    M_I_I(0L,S_V_I(vektor,7L));
    M_I_I(2L,S_V_I(vektor,11L));
    M_I_I(0L,S_V_I(vektor,12L));
    M_I_I(0L,S_V_I(vektor,13L));
    M_I_I(1L,S_V_I(vektor,17L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=freeall(hilf);
    erg+=freeall(vektor);
    erg+=freeall(koef);
    if (erg != OK) error(" in computation of zykelind_cube_extended(a) ");
    return(erg);
}

INT zykelind_cube_vertices(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_vertices(a) ");
    return(erg);
}

INT zykelind_cube_edges(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_edges(a) ");
    return(erg);
}

INT zykelind_cube_faces(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_faces(a) ");
    return(erg);
}

INT zykelind_cube_vertices_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_vertices_extended(a) ");
    return(erg);
}

INT zykelind_cube_edges_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_edges_extended(a) ");
    return(erg);
}

INT zykelind_cube_faces_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_cube_extended(b);
    c=s_mz_v(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_cube_faces_extended(a) ");
    return(erg);
}

INT zykelind_dodecahedron(aa) OP aa;
/* Berechnet den Zyklenzeiger der Drehgruppe des Dodecaeders.
Es treten 3 Familien von Unbestimmten auf. Die erste Familie
bezieht sich auf Gruppenaktion auf der Menge der Knoten, die zweite
auf der Menge der Kanten und die dritte auf der Menge der Flaechen
des Dodecaeders.  */
{
    OP a,b,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    a=callocobject();
    b=callocobject();
    erg+=m_ioiu_b(1L,60L,koef);
    erg+=m_il_v(25L,vektor);
    for (i=0L;i<S_V_LI(vektor);++i) 
    M_I_I(0L,S_V_I(vektor,i));
    M_I_I(20L,S_V_I(vektor,0L));
    M_I_I(30L,S_V_I(vektor,10L));
    M_I_I(12L,S_V_I(vektor,20L));
    erg+=m_skn_po(vektor,koef,NULL,a);
    erg+=m_ioiu_b(1L,3L,koef);
    M_I_I(2L,S_V_I(vektor,0L));
    M_I_I(6L,S_V_I(vektor,2L));
    M_I_I(0L,S_V_I(vektor,10L));
    M_I_I(10L,S_V_I(vektor,12L));
    M_I_I(0L,S_V_I(vektor,20L));
    M_I_I(4L,S_V_I(vektor,22L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,4L,koef);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(10L,S_V_I(vektor,1L));
    M_I_I(0L,S_V_I(vektor,2L));
    M_I_I(2L,S_V_I(vektor,10L));
    M_I_I(14L,S_V_I(vektor,11L));
    M_I_I(0L,S_V_I(vektor,12L));
    M_I_I(6L,S_V_I(vektor,21L));
    M_I_I(0L,S_V_I(vektor,22L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(2L,5L,koef);
    M_I_I(0L,S_V_I(vektor,1L));
    M_I_I(4L,S_V_I(vektor,4L));
    M_I_I(0L,S_V_I(vektor,10L));
    M_I_I(0L,S_V_I(vektor,11L));
    M_I_I(6L,S_V_I(vektor,14L));
    M_I_I(2L,S_V_I(vektor,20L));
    M_I_I(0L,S_V_I(vektor,21L));
    M_I_I(2L,S_V_I(vektor,24L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_il_v(3L,b);
    M_I_I(0L,S_V_I(b,0L));
    M_I_I(10L,S_V_I(b,1L));
    M_I_I(20L,S_V_I(b,2L));
    erg+=freeall(hilf);
    erg+=freeall(vektor);
    erg+=freeall(koef);
    m_v_po_mz(b,a,aa);
    erg+=freeall(a); erg+=freeall(b);
    if (erg != OK) error(" in computation of zykelind_dodecahedron(a) ");
    return(erg);
}

INT zykelind_dodecahedron_extended(aa) OP aa;
{
    OP a,koef,vektor,hilf;
    INT i;
    INT erg=OK;
    koef=callocobject();
    vektor=callocobject();
    hilf=callocobject();
    erg+=zykelind_dodecahedron(aa);
    a=s_mz_po(aa);
    erg+=m_ioiu_b(1L,2L,koef);
    erg+=m_scalar_polynom(koef,hilf);
    erg+=mult(hilf,a,a);
    erg+=m_ioiu_b(1L,120L,koef);
    erg+=m_il_v(30L,vektor);
    for (i=0L;i<S_V_LI(vektor);++i) M_I_I(0L,S_V_I(vektor,i));
    M_I_I(10L,S_V_I(vektor,1L));
    M_I_I(15L,S_V_I(vektor,11L));
    M_I_I(6L,S_V_I(vektor,21L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,6L,koef);
    M_I_I(1L,S_V_I(vektor,1L));
    M_I_I(3L,S_V_I(vektor,5L));
    M_I_I(0L,S_V_I(vektor,11L));
    M_I_I(5L,S_V_I(vektor,15L));
    M_I_I(0L,S_V_I(vektor,21L));
    M_I_I(2L,S_V_I(vektor,25L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,8L,koef);
    M_I_I(4L,S_V_I(vektor,0L));
    M_I_I(8L,S_V_I(vektor,1L));
    M_I_I(0L,S_V_I(vektor,5L));
    M_I_I(4L,S_V_I(vektor,10L));
    M_I_I(13L,S_V_I(vektor,11L));
    M_I_I(0L,S_V_I(vektor,15L));
    M_I_I(4L,S_V_I(vektor,20L));
    M_I_I(4L,S_V_I(vektor,21L));
    M_I_I(0L,S_V_I(vektor,25L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=m_ioiu_b(1L,5L,koef);
    M_I_I(0L,S_V_I(vektor,0L));
    M_I_I(0L,S_V_I(vektor,1L));
    M_I_I(2L,S_V_I(vektor,9L));
    M_I_I(0L,S_V_I(vektor,10L));
    M_I_I(0L,S_V_I(vektor,11L));
    M_I_I(3L,S_V_I(vektor,19L));
    M_I_I(0L,S_V_I(vektor,20L));
    M_I_I(1L,S_V_I(vektor,21L));
    M_I_I(1L,S_V_I(vektor,29L));
    erg+=m_skn_po(vektor,koef,NULL,hilf);
    erg+=add(hilf,a,a);
    erg+=freeall(hilf);
    erg+=freeall(vektor);
    erg+=freeall(koef);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_extended(a) ");
    return(erg);
}

INT zykelind_dodecahedron_vertices(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_vertices(a) ");
    return(erg);
}

INT zykelind_dodecahedron_edges(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_edges(a) ");
    return(erg);
}

INT zykelind_dodecahedron_faces(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_faces(a) ");
    return(erg);
}

INT zykelind_dodecahedron_vertices_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron_extended(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(1L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_vertices_extended(a) ");
    return(erg);
}

INT zykelind_dodecahedron_edges_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron_extended(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(2L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); 
    erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_edges_extended(a) ");
    return(erg);
}

INT zykelind_dodecahedron_faces_extended(a) OP a;
{
    OP b,c,d;
    INT erg=OK;
    if (not EMPTYP(a)) erg+=freeself(a);
    b=callocobject();
    d=callocobject();
    erg+=zykelind_dodecahedron_extended(b);
    c=s_mz_po(b);
    erg+=m_il_v(1L,d);
    M_I_I(3L,S_V_I(d,0L));
    erg+=mz_extrahieren(b,d,a);
    erg+=freeall(b); erg+=freeall(d);
    if (erg != OK) error(" in computation of zykelind_dodecahedron_faces_extended(a) ");
    return(erg);
}

INT polya_multi_sub(aa,b) OP aa,b;
/* aa ist ein Zyklenzeiger mit mehreren Familien von Unbestimmten.
In der i-ten Familie wird die Unbestimmte x_j durch
den Ausdruck 1+y_i^j ersetzt, wobei y_i ebenfalls Unbestimmte sind.
b ist das Resultat nach dieser Substitution.  */
{
    OP a,c,d,e,f,g,h,subvect;
    INT i,j,k;
    INT erg=OK;
    CTO(VECTOR,"polya_multi_sub",aa);
    a=s_mz_po(aa);
    c=s_mz_v(aa);
    if (S_O_K(a)!=POLYNOM) return error("polya_multi_sub(a,b) s_mz_po(a) not POLYNOM");
    if (S_O_K(c)!=VECTOR) return error("polya_multi_sub(a,b) s_mz_v(a) not VECTOR");
    for (i=0L;i<S_V_LI(c);++i)
    {
      if (S_O_K(S_V_I(c,i))!=INTEGER) return error("polya_multi_sub(a,b) Elements of s_mz_v(a) not INTEGER");
    }
    for (i=1L;i<S_V_LI(c);++i)
    {
      if (S_V_II(c,i)<=S_V_II(c,i-1L)) return error("polya_multi_sub(a,b) Elements of s_mz_v(a) not increasing");
    }
    if (not EMPTYP(b)) erg+=freeself(b);
        d=callocobject();
    subvect=callocobject();
    e=callocobject();
    f=callocobject();
    g=callocobject();
    h=callocobject();
    erg+=numberofvariables(a,h);
    M_I_I(1L,d);
    erg += m_scalar_polynom(d,e);
/*    M_I_I(1L,d);*/
    erg += m_il_v(0L,subvect);
    for (j=0L;j<S_V_LI(c);++j)
    {
    erg += m_il_v(j+1L,f);
    M_I_I(1L,S_V_I(f,j));
    for (k=0L;k<j;++k) M_I_I(0L,S_V_I(f,k));
    erg+=m_skn_po(f,d,NULL,g);
    if (j<S_V_LI(c)-1L)
    {
    for (i=S_V_II(c,j);i<S_V_II(c,j+1L);i++)
        {
        erg+=inc(subvect);
        erg += add(e,g,f); 
        erg+=copy(f,S_V_I(subvect,S_V_LI(subvect)-1L)); 
        erg += inc(S_V_I(S_PO_S(g),j));
        }
    }
    else
    {
    for (i=S_V_II(c,j);i<S_I_I(h);i++)
        {
        erg+=inc(subvect);
        erg += add(e,g,f); 
        erg+=copy(f,S_V_I(subvect,S_V_LI(subvect)-1L)); 
        erg += inc(S_V_I(S_PO_S(g),j));
        }
    }
    }
    erg += eval_polynom(a,subvect,b); 
    erg += freeall(subvect);
    erg += freeall(h);
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    erg += freeall(g);
    ENDR("polya_multi_sub");
}

INT polya_multi_const_sub(aa,d,b) OP aa,b,d;
/* aa ist ein Zyklenzeiger mit mehreren Familien von Unbestimmten.
d ist ein Vektor Objekt dessen Laenge der Anzahl der verschiedenen
Familien von Unbestimmten in aa entspricht.
Die Eintragungen in d sind Integer Objekte.
In der i-ten Familie werden die Unbestimmten durch die Ausdruck 
S_V_I(d,i-1L) ersetzt.
b ist das Resultat nach dieser Substitution.  */
{
    OP a,c,h,subvect;
    INT i,j;
    INT erg=OK;
    if (S_O_K(aa)!=VECTOR) return error("polya_multi_const_sub(a,d,b) a not a cycle index in several alphabets");
    a=s_mz_po(aa);
    c=s_mz_v(aa);
    if (S_O_K(a)!=POLYNOM) return error("polya_multi_const_sub(a,d,b) s_mz_po(a) not POLYNOM");
    if (S_O_K(c)!=VECTOR) return error("polya_multi_const_sub(a,d,b) s_mz_v(a) not VECTOR");
    for (i=0L;i<S_V_LI(c);++i)
    {
      if (S_O_K(S_V_I(c,i))!=INTEGER) return error("polya_multi_const_sub(a,d,b) Elements of s_mz_v(a) not INTEGER");
    }
    for (i=1L;i<S_V_LI(c);++i)
    {
      if (S_V_II(c,i)<=S_V_II(c,i-1L)) return error("polya_multi_const_sub(a,d,b) Elements of s_mz_v(a) not increasing");
    }
    if (S_O_K(d)!=VECTOR) return error("polya_multi_const_sub(a,d,b) d not VECTOR");
    if (S_V_LI(c) != S_V_LI(d)) return error("polya_multi_const_sub(a,d,b) s_mz_v(a) and d Vectors not of the same length");
    for (i=0L;i<S_V_LI(d);++i)
    {
      if (S_O_K(S_V_I(d,i))!=INTEGER) return error("polya_multi_const_sub(a,d,b) Elements of d not INTEGER");
    }
    if (not EMPTYP(b)) erg+=freeself(b);
    subvect=callocobject();
    h=callocobject();
    erg+=numberofvariables(a,h);
    erg += m_l_v(h,subvect);
    for (j=0L;j<S_V_LI(c);++j)
    {
    if (j<S_V_LI(c)-1L)
    {
    for (i=S_V_II(c,j);i<S_V_II(c,j+1L);i++)
        {
        erg+=copy(S_V_I(d,j),S_V_I(subvect,i)); 
        }
        }
    else
    {
    for (i=S_V_II(c,j);i<S_I_I(h);i++)
        {
        erg+=copy(S_V_I(d,j),S_V_I(subvect,i)); 
        }
    }
        }
    erg += eval_polynom(a,subvect,b); 
    erg += freeall(subvect);
    erg += freeall(h);
    if (erg != OK)
        return error("polya_multi_const_sub: error during computation");
    return erg;
}

static INT zykelind_test1()
{
    INT erg=OK;
    OP a=callocobject();
    OP b=callocobject();
    OP c=callocobject();
    OP d=callocobject();
    OP e=callocobject();
    m_i_i(4L,a);
    m_i_i(3L,b);
    erg+=zykelind_Sn(a,c);
    erg+=zykelind_Sn(b,d);
    printf("Exponentiation S4 \\wr S3\n");
    erg+=zykelind_exponentiation(c,d,e);
    println(e);
    printf("Zyklenzeiger GL(4,F_3)\n");
    erg+=zykelind_glkq(a,b,e);
    println(e);
    printf("Ordnung Aff(4,F_3)\n");
    erg+=ordnung_affkq(a,b,e);
    println(e);
    printf("Anzahl aller irreduzibler Polynome vom Grad 4 ueber F_3\n");
    erg+=number_of_irred_poly_of_degree(a,b,e);
    println(e);
    m_i_i(6L,b);
    printf("Zykelindex Aff(4,Z_6)\n");
    erg+=zykelind_affkzn(a,b,e);
    println(e);
    printf("Zykelindex Aff(1,Z_4)\n");
    erg+=zykelind_aff1Zn(a,e);
    println(e);
    m_i_i(3L,b);
    printf("Zykelindex PGL(4,F_3)\n");
    erg+=zykelind_pglkq(a,b,e);
    println(e);
    m_i_i(8L,b);
    printf("Zyklenzeiger des Zentralisators der Permutation ");
    random_permutation(a,c);
    println(c);
    erg+=zykelind_centralizer(c,e);
    println(e);
    printf("Zyklenzeiger des Stablisators der Partition ");
    random_partition(a,c);
    t_VECTOR_EXPONENT(c,c);
    println(c);
    erg+=zykelind_stabilizer_part(c,e);
    println(e);
    printf("Stirling Zahlen 2. Art\n");
    erg+=stirling_numbers_second_kind_vector(a,e);
    println(e);
    printf("Redfield Operatoren\n");
    m_il_v(2l,a);
    zykelind_Dn(b,S_V_I(a,0L));
    zykelind_An(b,S_V_I(a,1L));
    erg+=redf_cup(a,e);
    println(e);
    erg+=redf_cap(a,e);
    println(e);
    m_il_v(2L,b);
    m_i_i(3L,S_V_I(b,0L));
    m_i_i(4L,S_V_I(b,1L));
    erg+=redf_cup_hoch(a,b,e);
    println(e);
    erg+=redf_cap_hoch(a,b,e);
    println(e);
    erg+=zykelind_cube_extended(a);
    erg+=mz_vereinfachen(a,e);
    printf("Vereinfachen eines Multidim. Zyklenzeigers\n");
    println(a);println(e);
    m_i_i(1L,S_V_I(b,0L));
    m_i_i(3L,S_V_I(b,1L));
    printf("Extrahieren der 1. und 3. Familie von Variablen eines Multidim. Zyklenzeigers\n");
    erg+=mz_extrahieren(a,b,e);
    println(e);
    freeall(a);
    freeall(b);
    freeall(c);
    freeall(d);
    freeall(e);
    ENDR("zykelind_test1");
}
#endif /* POLYTRUE */
