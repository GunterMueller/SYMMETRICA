#include "def.h"
#include "macro.h"

static INT ek_to_h();

static OP  teh_speicher = NULL;
INT teh_ende()
{
    INT erg = OK;
    if (teh_speicher != NULL)
        {
        FREEALL(teh_speicher);
        teh_speicher=NULL;
        }
   
    ENDR("teh_ende");
}

OP find_teh_integer(a) OP a;
{
    INT erg = OK;
    CTO(INTEGER,"teh_integer__faktor(1)",a);
    SYMCHECK((S_I_I(a) < 0),"teh_integer__faktor:parameter < 0");
 
    if (teh_speicher == NULL) {
        teh_speicher = CALLOCOBJECT();
        erg += m_il_v(100,teh_speicher);
        }
    if (S_I_I(a) > S_V_LI(teh_speicher)) {
        inc_vector_co(teh_speicher, S_I_I(a)-S_V_LI(teh_speicher)+5);
        }

    if (not EMPTYP(S_V_I(teh_speicher, S_I_I(a))))
        {
        return S_V_I(teh_speicher, S_I_I(a));
        }
    else {
        ek_to_h(a,S_V_I(teh_speicher, S_I_I(a)));
        return S_V_I(teh_speicher, S_I_I(a));
        }
    
    ENDO("find_teh_integer");
    
}

INT teh_integer__faktor(a,b,f) OP a,b,f;
/* also called from tsh_partition__faktor */
/* also called from the_integer__faktor */
{
    INT erg = OK;
    OP m;
    CTO(INTEGER,"teh_integer__faktor(1)",a);
    CTTTO(HASHTABLE,HOMSYM,ELMSYM,"teh_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0),"teh_integer__faktor:parameter < 0");

    if (teh_speicher == NULL) {
        teh_speicher = CALLOCOBJECT();
        erg += m_il_v(100,teh_speicher);
        }
    if (S_I_I(a) > S_V_LI(teh_speicher)) {
        inc_vector_co(teh_speicher, S_I_I(a)-S_V_LI(teh_speicher)+5);
        }
    if (not EMPTYP(S_V_I(teh_speicher, S_I_I(a))))
        {
        m = CALLOCOBJECT();
        COPY(S_V_I(teh_speicher, S_I_I(a)),m);
        MULT_APPLY(f,m);
        if (S_O_K(b) == HASHTABLE)
            INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
        else
            INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
        goto eee;
        }

    m = CALLOCOBJECT();
    ek_to_h(a,m);
    COPY(m,S_V_I(teh_speicher, S_I_I(a)));

    MULT_APPLY(f,m);
    if (S_O_K(b) == HASHTABLE)
        INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
    else
        INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
eee:
    ENDR("teh_integer__faktor");
}

INT teh_partition__faktor_pre290102(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"teh_partition__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"teh_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        erg += first_partition(cons_null,S_MO_S(m));
        COPY(f,S_MO_K(m));
        INSERT_HOMSYMMONOM_(m,b);
        }
    else if ( S_PA_LI(a) == 1 ){
        erg += teh_integer__faktor(S_PA_I(a,0),b,f);
        }
    else {
        INT t_loop_partition();
        erg += t_loop_partition(a,b,f,teh_integer__faktor,mult_homsym_homsym,mult_apply_homsym_homsym);

/*      slower one 

        INT t_splitpart();;
        erg += t_splitpart(a,b,f,teh_partition__faktor,mult_homsym_homsym);
*/
        }
     
    ENDR("teh_partition__faktor");
}

 
static INT special_teh_integer(a,b,w,ff) OP a,b; INT w; OP (*ff)();
{
    INT erg = OK,i;
    OP h,z,m;
    CTO(HASHTABLE,"special_teh_integer(2)",b);
    h = (*ff)(a);
    FORALL(z,h, {
       m = CALLOCOBJECT();
       b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
       COPY(S_MO_K(z),S_MO_K(m));
       b_ks_pa(EXPONENT,CALLOCOBJECT(),S_MO_S(m));
       m_il_nv(w,S_PA_S(S_MO_S(m)));
       C_O_K(S_PA_S(S_MO_S(m)), INTEGERVECTOR);
       for (i=0;i<S_PA_LI(S_MO_S(z));i++) INC_INTEGER(S_PA_I(S_MO_S(m), S_PA_II(S_MO_S(z),i)-1));
       HASH_INTEGERVECTOR(S_PA_S(S_MO_S(z)),i);
       C_PA_HASH(S_MO_S(z),i);
       INSERT_HOMSYMMONOM_(m,b);
       });
    CTO(HASHTABLE,"special_teh_integer(e2)",b);
    ENDR("special_teh_integer");
}
 
INT special_eq(a,b) OP a,b; {
    /* both partitions of equal length */
    OP av,bv;
    INT l;
    av = S_V_S(S_PA_S(S_MO_S(a)));
    bv = S_V_S(S_PA_S(S_MO_S(b)));
    l = S_PA_LI(S_MO_S(b)) -1;
    for (; l>=0;l--,av++,bv++)
        if (S_I_I(av) != S_I_I(bv)) return FALSE;
    return TRUE;
}

INT special_mult_apply_homsym_homsym(a,b,mpm) OP a,b,mpm;
/* both are hashtable */
/* both labelling partitions are are of expnent type */
/* both labelling partitions are of the same length */
/* the external variable mpm is initialised */
{
    OP c,z1,z2,p1,p2,p3;
    INT erg = OK,i,j;
    CTO(HASHTABLE,"special_mult_apply_homsym_homsym(1)",a);
    CTO(HASHTABLE,"special_mult_apply_homsym_homsym(2)",b);
    CTO(MONOM,"special_mult_apply_homsym_homsym(3)",mpm);

    NEW_VECTOR(c,WEIGHT_HASHTABLE(b));
    i=0;
    FORALL_HASHTABLE(z2,b, { SWAP(S_V_I(c,i),z2); i++; });

    /* entries in c */
    /* b is empty */

    for (i=S_V_LI(b)-1,z1=S_V_S(b);i>=0; i--,z1++) 
        {
        if (not EMPTYP(z1) ) 
            FREESELF_INTEGERVECTOR(z1);
        C_I_I(z1,-1);
        }
    M_I_I(0,S_V_I(b,S_V_LI(b)));

    /* b is a empty */

    FORALL_HASHTABLE(z1,a, {
       for (j=0,z2 = S_V_S(c);j<S_V_LI(c);j++,z2++) 
           {
           for (i=0,p1=S_V_S(S_PA_S(S_MO_S(z1))),p2=S_V_S(S_PA_S(S_MO_S(z2))),
                    p3 = S_V_S(S_PA_S(S_MO_S(mpm)));
                i<S_PA_LI(S_MO_S(z1));
                i++,p1++,p2++,p3++)

               C_I_I(p3,S_I_I(p1) + S_I_I(p2)); /* addition der exponentenvectoren */
                     
 
           CLEVER_MULT(S_MO_K(z1),S_MO_K(z2),S_MO_K(mpm));
           HASH_INTEGERVECTOR(S_PA_S(S_MO_S(mpm)),i);
           C_PA_HASH(S_MO_S(mpm),i);
           add_apply_hashtable(mpm,b,add_koeff,special_eq,hash_monompartition);
           }
       });
    FREEALL(c);

    ENDR("special_mult_apply_homsym_homsym");
}

INT t_productexponent();


INT teh_partition__faktor(a,b,f) OP a,b,f;
/* AK 300102 */
{
    return t_productexponent(a,b,f,teh_integer__faktor,find_teh_integer);
}

INT t_productexponent(a,b,f,tf,ff) OP a,b,f; INT (*tf)(); OP (*ff)();
/* AK 300102 */
/* ff is find function for integer */
/* tf is trans function for integer */
{
    INT erg = OK;
    CTO(PARTITION,"t_productexponent(1)",a);
    CTTTO(HASHTABLE,HOMSYM,POWSYM,"t_productexponent(2)",b);

    if (S_PA_LI(a) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        erg += first_partition(cons_null,S_MO_S(m));
        COPY(f,S_MO_K(m));
        if (S_O_K(b) == HASHTABLE)
            INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
        else
            INSERT_LIST(m,b,add_koeff,comp_monomhomsym);
        
        goto ende;
        }
    else if ( S_PA_LI(a) == 1 ){
        erg += (*tf)(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        INT i,w;
        OP c,d,mpm;


        w = S_PA_II(a,S_PA_LI(a)-1);
        NEW_HASHTABLE(d);
        special_teh_integer(S_PA_I(a,0),d,w,ff);
       
        mpm = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),mpm);
        b_ks_pa(EXPONENT,CALLOCOBJECT(),S_MO_S(mpm));
        m_il_nv(w,S_PA_S(S_MO_S(mpm)));
        C_O_K(S_PA_S(S_MO_S(mpm)), INTEGERVECTOR);
      

        NEW_HASHTABLE(c);
        for (i=1;i<S_PA_LI(a);i++)
            {
            special_teh_integer(S_PA_I(a,i),c,w,ff);
            special_mult_apply_homsym_homsym(c,d,mpm);
            CLEAR_HASHTABLE(c);
            }

        FREEALL(mpm); 
        FREEALL(c); 

        { OP z,mm; 
          FORALL(z,d,{
                 t_EXPONENT_VECTOR_apply(S_MO_S(z)); 
                 HASH_INTEGERVECTOR(S_PA_S(S_MO_S(z)),i);
                 C_PA_HASH(S_MO_S(z),i);
                 if (not EINSP(f)) 
                     MULT_APPLY(f,S_MO_K(z));
                 mm = CALLOCOBJECT();
                 SWAP(mm,z);
                 if (S_O_K(b) == HASHTABLE)
                     INSERT_HASHTABLE(mm,b,
                                      add_koeff,
                                      eq_monomsymfunc,hash_monompartition);
                 else
                     INSERT_LIST(mm,b,add_koeff,comp_monomhomsym);
                 
                 DEC_INTEGER(S_V_I(d,S_V_LI(d)));
                 }); 
        }
        FREEALL(d);

        goto ende;
        }
 
ende:
    ENDR("t_productexponent");
}
 

INT teh_elmsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,ELMSYM,"teh_elmsym__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"teh_elmsym__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,teh_partition__faktor);
    ENDR("teh_elmsym__faktor");
}
 
INT teh_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"teh_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"teh_hashtable__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,teh_partition__faktor);
    ENDR("teh_hashtable__faktor");
}



INT teh___faktor(a,b,f) OP a,b; OP f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,ELMSYM,PARTITION,"teh___faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"teh___faktor(2)",b);

    if (teh_speicher == NULL) { 
        teh_speicher = CALLOCOBJECT();
        erg += m_il_v(100,teh_speicher);
        }

    if (S_O_K(a) == INTEGER) {
        erg += teh_integer__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += teh_partition__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == ELMSYM) {
        erg += teh_elmsym__faktor(a,b,f);
        goto eee;
        }
    else /* HASHTABLE */ {
        erg += teh_hashtable__faktor(a,b,f);
        goto eee;
        }


eee:
     ENDR("internal to t_ELMSYM_HOMSYM");
}

static INT ek_to_h(a,b) OP a,b;
/* a is INTEGER */
/* AK 060901 */
{
    INT i,l,ml,so,w=S_I_I(a);
    INT erg = OK;
    INT binom_small();
    OP c,d,oben,unten;
    OP res;
    CTO(INTEGER,"ek_to_h(1)",a);
    SYMCHECK((S_I_I(a)<0),"ek_to_h: parameter < 0");

    if (S_I_I(a) == 0)  {
        erg += m_scalar_homsym(cons_eins,b);
        goto ende;
        }
    
    d = CALLOCOBJECT();
    oben = CALLOCOBJECT();
    unten = CALLOCOBJECT();
    c = CALLOCOBJECT();
    erg += first_partition(a,c);
    erg += init(HASHTABLE,b);
    do {
        l = S_PA_LI(c);
        if (l == 1) {
            res = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),res); 
                /* first entry in the result */
            erg += copy_partition(c,S_MO_S(res));
            if ((w+l)%2 == 1) /* negativ */
                M_I_I(-1,S_MO_K(res));
            else
                M_I_I(1,S_MO_K(res));
            INSERT_HOMSYMMONOM_(res,b);
            }
        else    {
            res=CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),res);
            erg += copy_partition(c,S_MO_S(res));
    
            if (S_PA_II(c,S_PA_LI(c)-1) == 1) {
                /* last one */
                M_I_I(1,S_MO_K(res));
                INSERT_HOMSYMMONOM_(res,b);
                continue;
                }
            erg += t_VECTOR_EXPONENT(c,d);
            for (ml=0,so=0,i=1;i<S_PA_LI(d);i++)  
                {
                so += S_PA_II(d,i);
                if (S_PA_II(d,i) != 0) ml++;
                }
            if (so != l) /* einsen da */
                {
                FREESELF(unten);
                M_I_I(so,unten);
                M_I_I(l,oben);
    
                if ( (l > 12) )
                    erg += binom(oben,unten,S_MO_K(res));
                else
                    erg += binom_small(oben,unten,S_MO_K(res));
    
                }
            else {
                M_I_I(1,S_MO_K(res));
                }
            /* faktor bestimmen */
            M_I_I(so,oben);
            m_il_v(ml,unten);
            for (ml=0,i=1;i<S_PA_LI(d);i++)
                if (S_PA_II(d,i) != 0) 
                      { M_I_I(S_PA_II(d,i), S_V_I(unten,ml)); ml++; }
            if (so > 12) {
                erg += multinom(oben,unten,d);
                MULT_APPLY(d,S_MO_K(res));
                }
            else {
                FREESELF(d);
                erg += multinom_small(oben,unten,d);
                MULT_APPLY_INTEGER(d,S_MO_K(res));
                }
            if ((w+l)%2 == 1) /* negativ */
                ADDINVERS_APPLY(S_MO_K(res));

            INSERT_HOMSYMMONOM_(res,b);
            }
    } while (next_apply(c));
    
    FREEALL(c);
    FREEALL(d);
    FREEALL(oben);
    FREEALL(unten);
ende:
    ENDR("ek_to_h");
}

INT t_ELMSYM_HOMSYM(a,b) OP a,b;
/* AK 050901 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,ELMSYM,PARTITION,INTEGER,"t_ELMSYM_HOMSYM",a);
    TCE2(a,b,t_ELMSYM_HOMSYM,HOMSYM);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    teh___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_HOMSYM(b,b);

    ENDR("t_ELMSYM_HOMSYM");
}
