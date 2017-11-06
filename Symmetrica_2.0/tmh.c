
#include "def.h"
#include "macro.h"

static INT m_k_to_h_lambda();

static OP mh_speicher = NULL;
INT mult_hashtable_hashtable_faktor();
INT mult_hashtable_hashtable();
INT tmh___faktor();
INT teh_integer__faktor();
INT add_apply_hashtable();
INT monomial_recursion();
INT splitpart();
INT mmm_partition_partition_();
INT binom_small();



INT tmh_ende()
{
    INT erg = OK;
    if (mh_speicher != NULL)
        {
        FREEALL(mh_speicher);
        }
    mh_speicher=NULL;
    ENDR("tmh_ende");
}

INT t_MONOMIAL_HOMSYM(a,b) OP a,b;
/* AK 301001 */
{
    INT erg = OK;
    INT t=0;
    INT i,w=0;
    OP z=NULL;
    CTTTTO(HASHTABLE,INTEGER,MONOMIAL,PARTITION,"t_MONOMIAL_HOMSYM(1)",a); 
    TCE2(a,b,t_MONOMIAL_HOMSYM,HOMSYM);

    /* check for the size of the result */
    if (S_O_K(a) == INTEGER) 
        {
        w = numberofpart_i(a);
        goto ww;
        }
    else if (S_O_K(a) == PARTITION) {
        for (i=0;i<S_PA_LI(a);i++) w += S_PA_II(a,i);
        z = CALLOCOBJECT(); M_I_I(w,z);
        w = numberofpart_i(z);
        FREEALL(z);
        goto ww;
        }

    if (NULLP(a))
        {
        if (a == b) {
            if (S_O_K(a) == MONOMIAL) erg += init(HOMSYM,b);
            goto endr_ende;
            }
        init(HOMSYM,b);
        goto endr_ende;
        }

    if (S_O_K(a) == MONOMIAL) {
        z = S_S_S(a);
        for (i=0;i<S_PA_LI(z);i++) w += S_PA_II(z,i);
        z = CALLOCOBJECT(); M_I_I(w,z);
        w = numberofpart_i(z);
        FREEALL(z);
        }
    else {
        FORALL(z,a,{ goto fff; } );
        
fff:
        z = S_MO_S(z);
        for (i=0;i<S_PA_LI(z);i++) w += S_PA_II(z,i);
        z = CALLOCOBJECT(); M_I_I(w,z);
        w = numberofpart_i(z);
        FREEALL(z);
        }
    /* w ist die geschaetzte ergebnis groesse, ist korrekt fuer 
       homogenes m */
ww:
    if (a == b) {
        OP c;
        c = CALLOCOBJECT();
        *c = *a;
        C_O_K(a,EMPTY);
        erg += init_size_hashtable(a,2*w);
        t = 1;
        erg += tmh___faktor(c,b,cons_eins);
        FREEALL(c);
        }
    else if (S_O_K(b) == HOMSYM)
        {
        OP c;
        c = CALLOCOBJECT();
        erg += init_size_hashtable(c,2*w);
        erg += tmh___faktor(a,c,cons_eins);
        INSERT_LIST(c,b,add_koeff,comp_monomhomsym);
        }
    else {
        if (S_O_K(b) == EMPTY) {
            erg += init_size_hashtable(b,2*w);
            t = 1;
            }
        if (S_O_K(b) != HASHTABLE)
            {
            FREESELF(b);
            erg += init_size_hashtable(b,2*w);
            t = 1;
            }
        erg += tmh___faktor(a,b,cons_eins);
        }
    if (t == 1)
        erg += t_HASHTABLE_HOMSYM(b,b);
  

    ENDR("t_MONOMIAL_HOMSYM");
}

INT tmh_integer__faktor();
OP find_tmh_integer(a) OP a;
/* AK 300102 */
{
    INT erg = OK;
    CTO(INTEGER,"find_tmh_integer(1)",a);
    SYMCHECK( (S_I_I(a) < 0) ,"find_tmh_integer:integer < 0");
    if (
         (mh_speicher == NULL)
         ||
         (S_I_I(a) >= S_V_LI(mh_speicher) )
         ||
         (EMPTYP(S_V_I(mh_speicher,S_I_I(a))) )
       )
           {
           OP c;
           NEW_HASHTABLE(c);  
           tmh_integer__faktor(a,c,cons_eins);
           FREEALL(c);
           }


    return S_V_I(mh_speicher,S_I_I(a));
       
    ENDO("find_tmh_integer");
}

INT tmh_integer__faktor(a,b,faktor) OP a,b;OP faktor;
/* called from tme_integer__faktor */
{
    INT erg = OK;
    OP p,c;
    CTO(INTEGER,"tmh_integer__faktor(1)",a);
    CTO(HASHTABLE,"tmh_integer__faktor(2)",b);
    SYMCHECK( (S_I_I(a) < 0) ,"tmh_integer__faktor:integer < 0");


    if (mh_speicher == NULL) { mh_speicher=CALLOCOBJECT();
                               m_il_v(20,mh_speicher); }

    if (S_I_I(a) >= S_V_LI(mh_speicher) ) {
        erg += inc_vector_co(mh_speicher, S_I_I(a)+5- S_V_LI(mh_speicher)); 
        }
 
again:
    if (not EMPTYP(S_V_I(mh_speicher,S_I_I(a)) ) )
        {
        OP d,m;
        FORALL(d,S_V_I(mh_speicher,S_I_I(a)), {
            m = CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
            copy_partition(S_MO_S(d),S_MO_S(m));
            MULT(faktor,S_MO_K(d),S_MO_K(m));
            insert_scalar_hashtable(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
            });
        goto eee;
        }

    SYMCHECK(not EMPTYP(S_V_I(mh_speicher,S_I_I(a))),"tmh_integer__faktor:i1");
    init_size_hashtable(S_V_I(mh_speicher,S_I_I(a)), 2 * numberofpart_i(a)+1);
    /* erg += init(HASHTABLE,S_V_I(mh_speicher,S_I_I(a))); */
    
    if (S_I_I(a) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        first_partition(cons_null,S_MO_S(m));
        M_I_I(1,S_MO_K(m));
        insert_scalar_hashtable(m,
                                S_V_I(mh_speicher,0),
                                add_koeff,
                                eq_monomsymfunc,
                                hash_monompartition);
        goto again;
        }

   
    p  = CALLOCOBJECT();
    erg += first_partition(a,p);

    c = CALLOCOBJECT();
    do {
         OP m;
         m = CALLOCOBJECT();
         b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
         erg += copy_partition(p,S_MO_S(m));
         erg += m_k_to_h_lambda(a,p,S_MO_K(m));
         if (EINSP(faktor)) {
             add_apply_hashtable(m,b,add_koeff,eq_monomsymfunc,
                                      hash_monompartition);
             insert_scalar_hashtable(m,S_V_I(mh_speicher,S_I_I(a)),add_koeff,
                           eq_monomsymfunc,hash_monompartition);
             }
         else{
             OP k1,k2;
             k1 = CALLOCOBJECT();
             k2 = S_MO_K(m);
             MULT(faktor,k2,k1);
             C_MO_K(m,k1);
             add_apply_hashtable(m,b,add_koeff,eq_monomsymfunc,
                                      hash_monompartition);
             C_MO_K(m,k2); FREEALL(k1);
             insert_scalar_hashtable(m,S_V_I(mh_speicher,S_I_I(a)),add_koeff,
                           eq_monomsymfunc,hash_monompartition);
             }

    } while(next_apply(p));

    FREEALL(c);
    FREEALL(p);
 
eee:
    ENDR("tmh_integer__faktor");
}

INT mhh_hashtable_hashtable_();
INT tmh_partition__faktor(a,b,faktor) OP a,b;OP faktor;
{
    INT erg = OK;
    CTO(PARTITION,"tmh_partition__faktor(1)",a);
    CTO(HASHTABLE,"tmh_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0)
        {
        OP d;
        d = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
        COPY(faktor,S_MO_K(d));
        erg += first_partition(cons_null,S_MO_S(d));
        insert_scalar_hashtable(d,b,add_koeff,eq_monomsymfunc,
                                   hash_monompartition);
        goto eee;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += tmh_integer__faktor(S_PA_I(a,0),b,faktor);
        goto eee;
        }
    else if (S_PA_II(a,S_PA_LI(a)-1) == 1) 
        { /* AK 191001 */
        erg += teh_integer__faktor(S_PA_L(a),b,faktor);
        goto eee;
        }
    else {
        erg += monomial_recursion(a,b,faktor,
               tmh_partition__faktor,
               tmh___faktor,
               mhh_hashtable_hashtable_);

        goto eee;
        }
eee:
    ENDR("tmh_partition__faktor");
}

INT monomial_recursion2(a,b,faktor,partf,integerf,elmsymf,multf) OP a,b;OP faktor;
     INT (*partf)(); INT (*multf)(); INT (*integerf)();
     INT (*elmsymf)();
/* implementiert die zweite rekursion fuer monomial symmetric functions */
{
    INT erg = OK;
    OP z,ha,h2,h3;
    /* static INT level=0; */
    CTTO(HASHTABLE,MONOMIAL,"monomial_recursion2(1)",a);
    CTO(HASHTABLE,"monomial_recursion2(2)",b);


    ha = CALLOCOBJECT();
    if (S_O_K(a) == HASHTABLE)
        COPY(a,ha);
    else
        t_MONOMIAL_HASHTABLE(a,ha);

/* die partitionen in ha werden immer kuerzer */
    NEW_HASHTABLE(h2);
    NEW_HASHTABLE(h3);

    while (not NULLP_HASHTABLE(ha)) {
        OP c,p1,p2,m1,m2,coeff;
        /* step one */
        /* find a partition of maximal length */
        z = findmax_monomial(ha,length_comp_part);

        if (S_PA_LI(S_MO_S(z)) == 0) { /* constant term only  */
            OP f;
            f = CALLOCOBJECT();
            MULT(S_MO_K(z),faktor,f);
            (*integerf)(cons_null,b,f);
            FREESELF(z);
            DEC_INTEGER(S_V_I(ha,S_V_LI(ha)));
            FREEALL(f);
            continue;
            }
        if (S_PA_LI(S_MO_S(z)) == 1) { /* powsym */
            OP f;
            f = CALLOCOBJECT();
            MULT(S_MO_K(z),faktor,f);
            (*integerf)(S_PA_I(S_MO_S(z),0),b,f);
            FREESELF(z);
            DEC_INTEGER(S_V_I(ha,S_V_LI(ha)));
            FREEALL(f);
            continue;
            }
        if (S_PA_II(S_MO_S(z), S_PA_LI(S_MO_S(z))-1)  == 1) { /* elmsym */
            OP f;
            f = CALLOCOBJECT();
            MULT(S_MO_K(z),faktor,f);
            (*elmsymf)(S_PA_L(S_MO_S(z)),b,f);
            FREESELF(z);
            DEC_INTEGER(S_V_I(ha,S_V_LI(ha)));
            FREEALL(f);
            continue;
            }
        p1 = CALLOCOBJECT();
        p2 = CALLOCOBJECT();
        splitpart(S_MO_S(z),p1,p2);

        NEW_HASHTABLE(m1);
        erg += mmm_partition_partition_(p1,p2,m1,cons_eins);

        m2 = CALLOCOBJECT();
        erg += b_sk_mo(NULL,NULL,m2);
        C_MO_S(m2,S_MO_S(z));
        
 
        c = find_hashtable(m2,m1,eq_monomsymfunc,hash_monompartition);
        SYMCHECK( (c == NULL) ,"monomial_recursion2:wrong leading monomial");
        coeff = CALLOCOBJECT();
        erg += div(S_MO_K(z),S_MO_K(c),coeff); /* leitkoeff */
        MULT_APPLY(coeff,m1);

        /* es gilt jetzt m_a = (m_p1 * m_p2 )*coeff - m1 */

        /* m1 von ha abziehen */
        addinvers_apply_hashtable(m1);

        INSERT_HASHTABLE(m1,ha,add_koeff,eq_monomsymfunc,hash_monompartition);
        /* ha ist jetzt ohne maximale monom und m1 wurde abgezogen */

        erg += (*partf)(p1,h2,coeff);
        C_MO_S(m2,p1);
        C_MO_K(m2,coeff);
        FREEALL(m2); /* wg NULL in b_sk_mo *//* p1, coeff freed */

        erg += (*partf)(p2,h3,faktor);
        FREEALL(p2);

        erg += (*multf)(h3,h2,b);

  
        CLEAR_HASHTABLE(h2);
        CLEAR_HASHTABLE(h3);
        }
    FREEALL(ha);
    FREEALL(h2);
    FREEALL(h3);
    /* level--; */
    ENDR("monomial_recursion2");
}


INT tmh_monomial__faktor(a,b,faktor) OP a,b;OP faktor;
{
    INT erg = OK;
    CTTO(HASHTABLE,MONOMIAL,"tmh_monomial__faktor(1)",a);
    CTO(HASHTABLE,"tmh_monomial__faktor(2)",b);

    monomial_recursion2(a,b,faktor,
             tmh_partition__faktor,tmh_integer__faktor,teh_integer__faktor,
             mult_homsym_homsym);
    
   
    ENDR("tmh_monomial__faktor");
}

INT tmh___faktor(a,b,faktor) OP a,b;OP faktor;
/* AK 180901 */
/* after multiplication by the faktor 
   the result will be inserted in the hashtable b
*/
/* not static used from tme.c */   
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,MONOMIAL,PARTITION,"tmh___faktor(1)",a);
    CTO(HASHTABLE,"tmh___faktor(2)",b);
    CTO(ANYTYPE,"tmh___faktor(3)",faktor);
    if (mh_speicher == NULL) { mh_speicher=CALLOCOBJECT();
                               m_il_v(20,mh_speicher); }
    if (S_O_K(a) == INTEGER) 
        {
        erg += tmh_integer__faktor(a,b,faktor);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += tmh_partition__faktor(a,b,faktor);
        goto eee;
        }
    else /* HASHTABLE MONOMIAL */
        {
        erg += tmh_monomial__faktor(a,b,faktor);
        goto eee;
        }
eee:
    ENDR("tmh___faktor");
}



static INT m_k_to_h_lambda(a,b,c) OP a,b,c;
/* AK 180901 */
/* computes the single coefficient */
/* of h_b in the expansion of m_k */
{
    INT erg = OK,w,i,l;
    OP exp,oben,mn,bn,unten;
    CTO(INTEGER,"m_k_to_h_lambda",a);
    CTO(PARTITION,"m_k_to_h_lambda",b);

    for (w=0,i=0;i<S_PA_LI(b);i++)
        w += S_PA_II(b,i);

    if (w != S_I_I(a)) {
        error("different weights");
        goto endr_ende; }
       

    exp = CALLOCOBJECT();
    erg += t_VECTOR_EXPONENT(b,exp);
    

    w = w - S_PA_II(exp,0);
    l = S_PA_LI(b)-S_PA_II(exp,0);
    FREESELF(c);

    if (l <= 0) { 
        M_I_I(1,c);
	FREEALL(exp);
	goto faktor;
	}

    oben = CALLOCOBJECT();
    mn = CALLOCOBJECT();
    M_I_I(l,oben); 
    M_I_I(0,S_PA_I(exp,0));
    if (l > 12)
        erg += multinom(oben,S_PA_S(exp),mn);
    else
        erg += multinom_small(oben,S_PA_S(exp),mn);

    FREEALL(exp);
    M_I_I(w,c);
    MULT_APPLY(mn,c);
    GANZDIV_APPLY(c,oben);
    /* erg += div(c,oben,c); */

    if ((S_I_I(a)-w-1+l)  > 0) {
        M_I_I(S_I_I(a)-w-1+l,oben);
        unten = CALLOCOBJECT();
        M_I_I(l-1,unten);
        bn = CALLOCOBJECT();
    
        if (S_I_I(oben) <= 12) {
            erg += binom_small(oben,unten,bn);
            MULT_APPLY_INTEGER(bn,c);
            M_I_I(l,unten);
            C_O_K(bn,EMPTY);
            erg += binom_small(oben,unten,bn);
            MULT_APPLY_INTEGER(mn,bn);
            }
        else {
            erg += binom(oben,unten,bn);
            MULT_APPLY(bn,c);
            M_I_I(l,unten);
            erg += binom(oben,unten,bn);
            MULT_APPLY(mn,bn);
            }
        ADD_APPLY(bn,c);
        FREEALL(unten);
        FREEALL(bn);
        }

    

    FREEALL(oben);
    FREEALL(mn);
faktor:
    if ((S_PA_LI(b)%2)==0) 
        {
        ADDINVERS_APPLY(c);
        }
    ENDR("internal to tmh___faktor");
}


INT mult_hashtable_hashtable_faktor(a,b,d,faktor) OP a,b,d; OP faktor;
/* AK 171001 */
/* a und b sind hashtable */
/* sind beides homogene homsym functions
   sind beide sehr voll besetzt d.h. fast alle partitionenmit coeff != 0
 
   das ergebnis wird mit faktor in d eingefuegt */
{
    OP x=NULL,y=NULL,c;
    OP wx,wy,p;
    INT erg = OK,i,j,k;
 
    CTTTTO(HOMSYM,POWSYM,ELMSYM,HASHTABLE,"mult_hashtable_hashtable(1)",a);
    CTTTTO(HOMSYM,POWSYM,ELMSYM,HASHTABLE,"mult_hashtable_hashtable(2)",b);
    CTO(HASHTABLE,"mult_hashtable_hashtable(3)",d);
 
 
 
    FORALL(x,a, { goto ee; });
ee:
    FORALL(y,b, { goto ff; });
ff: /* x und y sind jetzt monome, das gemeinsame gewicht bestimmen */
    wx=CALLOCOBJECT(); weight(S_MO_S(x),wx);
    wy=CALLOCOBJECT(); weight(S_MO_S(y),wy);
    ADD_APPLY(wx,wy);
    p = CALLOCOBJECT();
 
 
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),p);
    M_I_I(0,S_MO_K(p));
    b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(p));
    m_il_integervector(S_I_I(wy),S_PA_S(S_MO_S(p)));
   
    /* wy ist das gewicht der ergebnispartition
       p ist ein monom mit platz fuer die maximale partition */
 
 
    FORALL(x,a, {
 
        FORALL(y,b, {
            i=j=k=0;
            while ( (i<S_PA_LI(S_MO_S(y))) || (j<S_PA_LI(S_MO_S(x))) )
                {
                if (j==S_PA_LI(S_MO_S(x)))
                    { M_I_I(S_PA_II(S_MO_S(y),i), S_PA_I(S_MO_S(p),k) ); k++;i++; }
                else if (i==S_PA_LI(S_MO_S(y)))
                    { M_I_I(S_PA_II(S_MO_S(x),j), S_PA_I(S_MO_S(p),k) ); k++;j++; }
                else if (S_PA_II(S_MO_S(x),j) < S_PA_II(S_MO_S(y),i) )
                    { M_I_I(S_PA_II(S_MO_S(x),j), S_PA_I(S_MO_S(p),k) ); k++;j++; }
                else
                    { M_I_I(S_PA_II(S_MO_S(y),i), S_PA_I(S_MO_S(p),k) ); k++;i++; }
                }
 
            M_I_I(k,S_PA_L(S_MO_S(p)));
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(p)),j);
            C_PA_HASH(S_MO_S(p),j);
            /* jetzt suchen in der hashtable */
            c = find_hashtable(p,d,eq_monomsymfunc,hash_monompartition);
            if (c == NULL) { /* einfuegen */
                          OP m;
                          m = CALLOCOBJECT();
                          b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
                          MULT(S_MO_K(x),S_MO_K(y),S_MO_K(m));
                          MULT_APPLY(faktor,S_MO_K(m));
                          copy_partition(S_MO_S(p),S_MO_S(m));
                          INSERT_HASHTABLE(m,d,NULL,eq_monomsymfunc,hash_monompartition);
                          }
            else          {
                          FREESELF(wx);
                          MULT(S_MO_K(x),S_MO_K(y),wx);
                          MULT_APPLY(faktor,wx);
                          ADD_APPLY(wx,S_MO_K(c));
                          }
            } );
        } );
     FREEALL(p);
     FREEALL(wx);
     FREEALL(wy);
     ENDR("mult_hashtable_hashtable_faktor");
}


INT mult_hashtable_hashtable(a,b,d) OP a,b,d;
/* AK 171001 */
/* a und b sind hashtable */
/* sind beides homogene homsym functions
   sind beide sehr voll besetzt d.h. fast alle partitionenmit coeff != 0
   das ergebnis wird in d eingefuegt */
{
    OP x=NULL,y=NULL,c;
    OP wx,wy,p;
    INT erg = OK,i,j,k;
 
    CTTTTO(HOMSYM,POWSYM,ELMSYM,HASHTABLE,"mult_hashtable_hashtable(1)",a);
    CTTTTO(HOMSYM,POWSYM,ELMSYM,HASHTABLE,"mult_hashtable_hashtable(2)",b);
    CTO(HASHTABLE,"mult_hashtable_hashtable(3)",d);
 
 
 
    FORALL(x,a, { goto ee; });
ee:
    FORALL(y,b, { goto ff; });
ff: /* x und y sind jetzt monome, das gemeinsame gewicht bestimmen */
    wx=CALLOCOBJECT(); weight(S_MO_S(x),wx);
    wy=CALLOCOBJECT(); weight(S_MO_S(y),wy);
    ADD_APPLY(wx,wy);
    p = CALLOCOBJECT();
 
 
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),p);
    M_I_I(0,S_MO_K(p));
    b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(p));
    m_il_integervector(S_I_I(wy),S_PA_S(S_MO_S(p)));
   
    /* wy ist das gewicht der ergebnispartition
       p ist ein monom mit platz fuer die maximale partition */
 
 
    FORALL(x,a, {
 
        FORALL(y,b, {
            i=j=k=0;
            while ( (i<S_PA_LI(S_MO_S(y))) || (j<S_PA_LI(S_MO_S(x))) )
                {
                if (j==S_PA_LI(S_MO_S(x)))
                    { M_I_I(S_PA_II(S_MO_S(y),i), S_PA_I(S_MO_S(p),k) ); k++;i++; }
                else if (i==S_PA_LI(S_MO_S(y)))
                    { M_I_I(S_PA_II(S_MO_S(x),j), S_PA_I(S_MO_S(p),k) ); k++;j++; }
                else if (S_PA_II(S_MO_S(x),j) < S_PA_II(S_MO_S(y),i) )
                    { M_I_I(S_PA_II(S_MO_S(x),j), S_PA_I(S_MO_S(p),k) ); k++;j++; }
                else
                    { M_I_I(S_PA_II(S_MO_S(y),i), S_PA_I(S_MO_S(p),k) ); k++;i++; }
                }
 
            M_I_I(k,S_PA_L(S_MO_S(p)));
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(p)),j);
            C_PA_HASH(S_MO_S(p),j);
            /* jetzt suchen in der hashtable */
            c = find_hashtable(p,d,eq_monomsymfunc,hash_monompartition);
            if (c == NULL) { /* einfuegen */
                          OP m;
                          m = CALLOCOBJECT();
                          b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
                          MULT(S_MO_K(x),S_MO_K(y),S_MO_K(m));
                          copy_partition(S_MO_S(p),S_MO_S(m));
                          INSERT_HASHTABLE(m,d,NULL,eq_monomsymfunc,hash_monompartition);
                          }
            else          {
                          FREESELF(wx);
                          MULT(S_MO_K(x),S_MO_K(y),wx);
                          ADD_APPLY(wx,S_MO_K(c));
                          }
            } );
        } );
     FREEALL(p);
     FREEALL(wx);
     FREEALL(wy);
     ENDR("mult_hashtable_hashtable_faktor");
}

