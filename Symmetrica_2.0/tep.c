#include "def.h"
#include "macro.h"

INT tep_integer__faktor();
INT mpp_hashtable_hashtable_();
INT t_loop_partition();
OP find_tep_integer();
INT t_productexponent();


INT tep_partition__faktor_pre040202(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tep_partition__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        erg += tep_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += tep_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        /* erg += t_splitpart(a,b,f,tep_partition__faktor,mpp_hashtable_hashtable_); */
        erg += t_loop_partition(a,b,f,tep_integer__faktor,mult_powsym_powsym, mult_apply_powsym_powsym);
        goto ende;
        }
ende:
    ENDR("tpe_partition__faktor");
}

INT tep_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tep_partition__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        erg += tep_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += tep_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        erg += t_productexponent(a,b,f,tep_integer__faktor,find_tep_integer);
        goto ende;
        }
ende:
    ENDR("tpe_partition__faktor");
}



INT tep_elmsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,ELMSYM,"tep_elmsym__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep_elmsym__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tep_partition__faktor); 
    ENDR("tep_elmsym__faktor");
}

 
INT tep_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tep_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep_hashtable__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tep_partition__faktor); 
    ENDR("tep_hashtable__faktor");
}
 

INT tep___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"tep___faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep___faktor(2)",b);

    if (S_O_K(a) == INTEGER)
        {
        tep_integer__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)
        {
        tep_partition__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == HASHTABLE)
        {
        tep_hashtable__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == ELMSYM)
        {
        tep_elmsym__faktor(a,b,f);
        goto ende;
        }
ende:
    ENDR("tep___faktor");
}

static OP tep_sp=NULL;

INT tep_ende() 
{
    INT erg = OK;
    if (tep_sp != NULL)
        {
        FREEALL(tep_sp);
        }
    tep_sp = NULL;
    ENDR("tep_ende");
}

OP find_tep_integer(a) OP a;
/* AK 040202 */
{
    INT erg = OK;
    CTO(INTEGER,"find_tep_integer(1)",a);
    SYMCHECK((S_I_I(a) < 0), "find_tep_integer:parameter < 0");

    if ( 
        (tep_sp == NULL)
        ||
        (S_I_I(a) >= S_V_LI(tep_sp))
        ||
        (EMPTYP(S_V_I(tep_sp,S_I_I(a))))
       ) 
        {
        OP c;
        NEW_HASHTABLE(c);
        erg += tep_integer__faktor(a,c,cons_eins);
        FREEALL(c);
        }
    return S_V_I(tep_sp,S_I_I(a));
        
    ENDO("find_tep_integer");
}

INT tep_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tep_integer__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tep_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0), "tep_integer__faktor:parameter < 0");

    /* first check on the stored result */
    if (tep_sp == NULL)  NEW_VECTOR(tep_sp,100);
    if (S_I_I(a) >= S_V_LI(tep_sp)) 
        erg += inc_vector_co(tep_sp, S_I_I(a) - S_V_LI(tep_sp)+5);
    if (not EMPTYP(S_V_I(tep_sp, S_I_I(a) ) ) )
        {
        OP m,c;
        FORALL(c,S_V_I(tep_sp, S_I_I(a)), {
            m = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
            MULT(S_MO_K(c), f, S_MO_K(m));
            erg += copy_partition(S_MO_S(c),S_MO_S(m));
            INSERT_POWSYMMONOM_(m,b);
            });
        goto ende;
        }

    /* now we know */
    /* the result is not stored */
 
    if (S_I_I(a) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        COPY(f,S_MO_K(m));
        erg += first_partition(cons_null,S_MO_S(m));
        INSERT_POWSYMMONOM_(m,b);

        init_size_hashtable(S_V_I(tep_sp,0),3);
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        M_I_I(1,S_MO_K(m));
        erg += first_partition(cons_null,S_MO_S(m));
        INSERT_POWSYMMONOM_(m,S_V_I(tep_sp,0));

        goto ende;
        }
    else {
        OP c,coeff,ergebnis,sp;
        OP bb;
        

        c=CALLOCOBJECT();
        coeff=CALLOCOBJECT();
        ergebnis=CALLOCOBJECT();
        sp=CALLOCOBJECT();
        bb=CALLOCOBJECT();
        erg += init(HASHTABLE,bb);
        erg += first_partition(a,c);
        do {
            OP d;
            INT i;
            m_i_i(1,sp);
            m_i_i(1,ergebnis);
            d = CALLOCOBJECT();
            b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
            COPY(c,S_MO_S(d));

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
            erg += m_ou_b(cons_eins,ergebnis,S_MO_K(d));
            C_B_I(S_MO_K(d),GEKUERZT);
            if ( (S_I_I(a) - S_PA_LI(c)) %2 == 1 )
                M_I_I(-1,S_B_O(S_MO_K(d)));
            insert_scalar_hashtable(d,bb,NULL,eq_monomsymfunc,hash_monompartition);

        } while(next_apply(c));

        FREEALL(c);
        FREEALL(coeff);
        FREEALL(ergebnis);
        FREEALL(sp);

        COPY(bb,S_V_I(tep_sp, S_I_I(a) ) );
        MULT_APPLY(f,bb);
 
        if (S_O_K(b) == POWSYM)
            INSERT_LIST(bb,b,add_koeff,comp_monompowsym);
        else
            INSERT_HASHTABLE(bb,b,add_koeff,eq_monomsymfunc,hash_monompartition);
        }
ende:
    ENDR("tep_integer__faktor");
}

INT t_ELMSYM_POWSYM(a,b) OP a,b;
/* AK 190901 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"t_ELMSYM_POWSYM(1)",a);
    TCE2(a,b,t_ELMSYM_POWSYM,POWSYM);

    if (S_O_K(b) == EMPTY) {
        init_hashtable(b); t=1;
        }
    tep___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_POWSYM(b,b);
    ENDR("t_ELMSYM_POWSYM");
}
