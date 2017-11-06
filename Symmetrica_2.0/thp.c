#include "def.h"
#include "macro.h"

INT thp___faktor();
INT thp_integer__faktor();
INT mhp_integer_hashtable_();
INT t_splitpart();
INT mpp___();

INT t_HOMSYM_POWSYM(a,b) OP a,b;
/* AK 190901 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"t_HOMSYM_POWSYM(1)",a);
    TCE2(a,b,t_HOMSYM_POWSYM,POWSYM);

    if (S_O_K(b) == EMPTY) {
        init_hashtable(b);t=1;
        }
    CTTO(HASHTABLE,POWSYM,"t_HOMSYM_POWSYM(2)",b);

    thp___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_POWSYM(b,b);

    ENDR("t_HOMSYM_POWSYM");
}

static OP htop_sp=NULL;
INT thp_ende()
{
    INT erg = OK;
    if (htop_sp != NULL)
        {
        FREEALL(htop_sp);
        }
    htop_sp = NULL;
    ENDR("thp_ende");
}

OP find_thp_integer(a) OP a;
/* AK 221101 */
/* zeiger auf gespeicherten wert */
{
    INT erg = OK;
    CTO(INTEGER,"find_thp_integer(1)",a);

    SYMCHECK((S_I_I(a) <= 0) , "find_thp_integer:parameter <=0");
    if (htop_sp == NULL) 
        NEW_VECTOR(htop_sp,20);
        
    if (S_V_LI(htop_sp) <= S_I_I(a))
        erg += inc_vector_co(htop_sp , S_I_I(a)-S_V_LI(htop_sp)+2);

    if (not EMPTYP(S_V_I(htop_sp, S_I_I(a))))
        return S_V_I(htop_sp, S_I_I(a));
    else {
        OP c;
        NEW_HASHTABLE(c);
        thp_integer__faktor(a,c,cons_eins);
        FREEALL(c);
        return S_V_I(htop_sp, S_I_I(a));
        }
    ENDO("find_thp_integer");
}

INT thp_integer__faktor(a,b,faktor) OP a,b; OP faktor;
/* AK 311001 */
/* b = b + h_a * f */
{
    INT erg = OK;
    OP c,ergebnis,sp;
    OP bb;

    CTO(INTEGER,"thp_integer__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"thp_integer__faktor(2)",b);
    CTO(ANYTYPE,"thp_integer__faktor(3)",faktor);
    SYMCHECK((S_I_I(a) < 0), "thp_integer__faktor:parameter < 0");

    if (S_I_I(a) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        COPY(faktor,S_MO_K(m));
        erg += first_partition(cons_null,S_MO_S(m));
        if (S_O_K(b) == POWSYM)
            INSERT_LIST(m,b,add_koeff,comp_monompowsym);
        else
            INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
        goto ende;
        }

    SYMCHECK((S_I_I(a) <= 0), "thp_integer__faktor:(i1)");
    if (htop_sp == NULL) { htop_sp = CALLOCOBJECT(); erg += m_il_v(100,htop_sp); }
    if (S_V_LI(htop_sp) <= S_I_I(a)) erg += inc_vector_co(htop_sp , S_I_I(a)-S_V_LI(htop_sp)+2);

    if (not EMPTYP(S_V_I(htop_sp, S_I_I(a))))
        {
        OP m;
        FORALL(c,S_V_I(htop_sp, S_I_I(a)), {
            m = CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
            MULT(S_MO_K(c), faktor, S_MO_K(m));
            copy_partition(S_MO_S(c),S_MO_S(m));
            if (S_O_K(b) == POWSYM)
                INSERT_LIST(m,b,add_koeff,comp_monompowsym);
            else
                INSERT_HASHTABLE(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
            });
        goto ende;
        }
 
    c=CALLOCOBJECT();
    sp=CALLOCOBJECT();
    bb=CALLOCOBJECT();

    /* erg += init(POWSYM,bb); */
    erg += init(HASHTABLE,bb);
    erg += first_partition(a,c);
    do {
        OP d;
        INT i;
        CTO(PARTITION,"thp_integer__faktor(i1)",c);
        M_I_I(1,sp);
        ergebnis=CALLOCOBJECT();
        M_I_I(1,ergebnis);
        d = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
        erg += copy_partition(c,S_MO_S(d));
        /* compute coeff */
        for (i=(INT)0; i<S_PA_LI(c);i++)
            {
            if (i>(INT)0)
                {
                if (S_PA_II(c,i) == S_PA_II(c,(i-1L)))
                    {
                    INC_INTEGER(sp);
                    MULT_APPLY_INTEGER(sp,ergebnis);
                    }
                else M_I_I(1L,sp);
                };
            MULT_APPLY_INTEGER(S_PA_I(c,i),ergebnis);
            };
        /* in ergebnis ist der coeff, es muss durch ihn geteilt werden */

        erg += b_ou_b(CALLOCOBJECT(),ergebnis,S_MO_K(d));
        M_I_I(1,S_B_O(S_MO_K(d)));
        C_B_I(S_MO_K(d), GEKUERZT);
        /* INSERT_LIST(d,bb,NULL,comp_monompowsym); */
        insert_scalar_hashtable(d,bb,NULL,eq_monomsymfunc,hash_monompartition);
    } while(next_apply(c));

    FREEALL(c);
    FREEALL(sp);
    COPY(bb,S_V_I(htop_sp, S_I_I(a)));

    MULT_APPLY(faktor,bb);

    if (S_O_K(b) == POWSYM)
        INSERT_LIST(bb,b,add_koeff,comp_monompowsym);
    else
        INSERT_HASHTABLE(bb,b,add_koeff,eq_monomsymfunc,hash_monompartition);
 
ende:
    CTTO(HASHTABLE,POWSYM,"thp_integer__faktor(e2)",b);
    ENDR("thp_integer__faktor");
}

INT mpp_hashtable_hashtable_();
INT t_productexponent();

INT thp_partition__faktor(a,b,f) OP a,b; OP f;
/* AK 300102 */
{
    INT erg = OK;
    CTO(PARTITION,"thp_partition__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"thp_partition__faktor(2)",b);
    erg += t_productexponent(a,b,f,thp_integer__faktor,find_thp_integer);
    ENDR("thp_partition__faktor");
}

INT thp_partition__faktor_pre300102(a,b,faktor) OP a,b; OP faktor;
{
    INT erg = OK;
    CTO(PARTITION,"thp_partition__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"thp_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0)
        {
        erg += thp_integer__faktor(cons_null,b,faktor);
        goto endr_ende;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += thp_integer__faktor(S_PA_I(a,0),b,faktor);
        goto endr_ende;
        }
    else if (S_PA_LI(a) == 2)
        {
        OP p1,p2;
        p1 = find_thp_integer(S_PA_I(a,0));
        p2 = find_thp_integer(S_PA_I(a,1));
        erg += mpp___(p1,p2,b,faktor);
        }
    else if (S_PA_LI(a) == 3)
        {
        OP p1,p2;
        p1 = find_thp_integer(S_PA_I(a,2));
        M_I_I(2,S_PA_L(a));
        p2 = CALLOCOBJECT();init_hashtable(p2);
        thp_partition__faktor(a,p2,cons_eins);
        erg += mpp___(p1,p2,b,faktor);
        M_I_I(3,S_PA_L(a));
        FREEALL(p2);
        }
    else {
        erg += t_splitpart(a,b,faktor,thp_partition__faktor,mpp_hashtable_hashtable_);
        goto endr_ende;
        }
 
    ENDR("thp_partition__faktor");
}

INT thp_homsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    static int level=0;
    level += 2;
    CTO(HOMSYM,"thp_homsym__faktor(1)",a);
    CTTO(POWSYM,HASHTABLE,"thp_homsym__faktor(2)",b);

    if (S_L_S(a) == NULL) goto eee;
    if (S_S_N(a) == NULL) { 
        OP ff;
        ff = CALLOCOBJECT(); 
        MULT(S_S_K(a),f,ff);
        erg += thp_partition__faktor(S_S_S(a),b,ff); 
        FREEALL(ff);
        goto eee;}
    if (S_S_SLI(a) == 0) {
        if (EINSP(f))
            erg += thp_partition__faktor(S_S_S(a),b,S_S_K(a));
        else {
            OP ff = CALLOCOBJECT();
            MULT(f,S_S_K(a),ff);
            erg += thp_partition__faktor(S_S_S(a),b,ff);
            FREEALL(ff);
            }
        erg += thp_homsym__faktor(S_S_N(a),b,f);
        goto eee;
        }
    else {
        OP z,zv,hi,ff;
        INT i,j;
        i = S_S_SII(a,0);
        z = a;zv = NULL;
again:
        if (S_S_SII(z,0) == i)
            {
            for (j=0;j<S_S_SLI(z)-1;j++)
                M_I_I(S_S_SII(z,j+1),S_S_SI(z,j));
            M_I_I(S_S_SLI(z)-1,S_S_SL(z));
            zv = z; z = S_S_N(z);
            if (z != NULL) goto again;
            }
/* jetzt ist z der erste teil mit dem kleinsten teil partition >i */
/* zv ist der letzte teil mit kleinsten teil = i */
/* berechne : h_i *  h_a +  h_z */
        C_S_N(zv,NULL);
 
        ff = CALLOCOBJECT();
        init_hashtable(ff);
        hi = CALLOCOBJECT();
        M_I_I(i,hi);
        erg += thp_homsym__faktor(a,ff,cons_eins);
        erg += mhp_integer_hashtable_(hi,ff,b,f);
 
        if (z != NULL)
            erg += thp_homsym__faktor(z,b,f);
        FREEALL(hi);
        FREEALL(ff);
/* a wieder richtig zusammen bauen */
 
        zv = a;
aa:
        for (j=S_S_SLI(zv);j>0;j--)
            M_I_I(S_S_SII(zv,j-1),S_S_SI(zv,j));
        M_I_I(i,S_S_SI(zv,0));
        M_I_I(S_S_SLI(zv)+1,S_S_SL(zv));
        if (S_S_N(zv) != NULL) { zv = S_S_N(zv); goto aa; }
 
        C_S_N(zv,z);
        }


eee:
    level -= 2;
    ENDR("thp_homsym__faktor");
}

INT thp___faktor(a,b,f) OP a,b; OP f;
/* AK 190901 */
{
    INT erg = OK;
    CTTTTO(INTEGER,PARTITION,HASHTABLE,HOMSYM,"thp___faktor(1)",a);
    CTTO(POWSYM,HASHTABLE,"thp___faktor(2)",b);

    if (S_O_K(a) == INTEGER) 
        erg += thp_integer__faktor(a,b,f);
    else if (S_O_K(a) == PARTITION) 
        erg += thp_partition__faktor(a,b,f);
    else if (S_O_K(a) == HOMSYM)
        erg += thp_homsym__faktor(a,b,f);
    else  /* HASHTABLE */
        {
        T_FORALL_MONOMIALS_IN_A(a,b,f,thp_partition__faktor);
        }

    ENDR("thp___faktor");
}

