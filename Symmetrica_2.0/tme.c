/* SYMMETRICA sr.c */
#include "def.h"
#include "macro.h"

OP me_speicher = NULL;

INT tme___faktor();
INT tme_monomial__faktor();
INT tmh_integer__faktor();
INT mee_integer_hashtable_();
INT mem_integer_hashtable_();
INT txx_null__faktor();
INT t_splitpart();

INT tme_ende()
{
    INT erg = OK;
    if (me_speicher != NULL)
        {
        FREEALL(me_speicher);
        }
    me_speicher=NULL;
    ENDR("tme_ende");
}

INT t_MONOMIAL_ELMSYM(a,b) OP a,b;
/* AK 121101 */
{
    INT erg = OK;
    INT t = 0;
    CTTTTO(INTEGER,PARTITION,MONOMIAL,HASHTABLE,"t_MONOMIAL_ELMSYM(1)",a);
    if (a == b) {
        OP c;
        c = CALLOCOBJECT();
        *c = *a;
        C_O_K(a,EMPTY);
        erg += init_hashtable(b);
        t = 1;
        erg += tme___faktor(c,b,cons_eins);
        FREEALL(c);
        }
    else if (S_O_K(b) == ELMSYM)
        {
        OP c;
        c = CALLOCOBJECT();
        erg += init_hashtable(c);
        erg += tme___faktor(a,c,cons_eins);
        insert(c,b,add_koeff,comp_monomelmsym);
        }

    else {
        if (S_O_K(b) == EMPTY) {
            erg += init_hashtable(b);
            t = 1;
            }
        if (S_O_K(b) != HASHTABLE)
            {
            FREESELF(b);
            erg += init_hashtable(b);
            t = 1;
            }
        erg += tme___faktor(a,b,cons_eins);
        }
    if (t == 1) 
        erg += t_HASHTABLE_ELMSYM(b,b);
    ENDR("t_MONOMIAL_ELMSYM");
}

OP find_tmh_integer();

OP find_tme_integer(a) OP a;
/* AK 300102 */
{
    INT erg = OK;
    CTO(INTEGER,"find_tme_integer(1)",a);
    SYMCHECK(S_I_I(a) < 0, "find_tme_integer:integer <0");

    if (S_I_I(a) % 2 == 1) 
        return find_tmh_integer(a);

    if (me_speicher == NULL) { 
        me_speicher=CALLOCOBJECT();
        erg += m_il_v(40,me_speicher);
        }

    if (S_I_I(a) >= S_V_LI(me_speicher)) {
        erg += inc_vector_co(me_speicher,S_I_I(a)-S_V_LI(me_speicher)+5);
        }

    if (EMPTYP(S_V_I(me_speicher,S_I_I(a))) ) {
        OP c;
        c = find_tmh_integer(a);
        MULT_INTEGER(cons_negeins,c,S_V_I(me_speicher,S_I_I(a) ) ) ;
        }
      
    return S_V_I(me_speicher,S_I_I(a));

    ENDO("find_tme_integer");
}

INT tme_integer__faktor(a,b,f) OP a,b; OP f;
{
    INT erg = OK;
    CTO(INTEGER,"tme_integer__faktor(1)",a);
    CTO(HASHTABLE,"tme_integer__faktor(2)",b);
    SYMCHECK(S_I_I(a) < 0, "tme_integer__faktor:integer <0");
    if (S_I_I(a) == 0)
        {
        txx_null__faktor(b,f);
        goto ende;
        }
    else if (S_I_I(a) %2 == 0)
        {
        OP c;
        c = CALLOCOBJECT();
        ADDINVERS(f,c);
        erg += tmh_integer__faktor(a,b,c);
        FREEALL(c);
        goto ende;
        }
    else
        {
        erg += tmh_integer__faktor(a,b,f);
        goto ende;
        }
ende:
    ENDR("tme_integer__faktor");
}

INT tme_partition__faktor(a,b,f) OP a,b; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"tme_partition__faktor(1)",a);
    CTO(HASHTABLE,"tme_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0) {
        txx_null__faktor(b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) 
        {
        erg +=  tme_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else{

        OP e;
        e = CALLOCOBJECT();
        erg += m_pa_mon(a,e);
        erg += tme_monomial__faktor(e,b,f);
        FREEALL(e);
        goto ende;
        }
ende: 
    ENDR("tme_partition__faktor");
}

INT tme_hashtable__faktor(a,b,f) OP a,b; OP f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tme_hashtable__faktor(1)",a);
    CTO(HASHTABLE,"tme_hashtable__faktor(2)",b);
    erg += tme_monomial__faktor(a,b,f);
    ENDR("tme_hashtable__faktor");
}

INT tme_monomial__faktor(a,b,f) OP a,b; OP f;
{
    INT erg = OK;
    OP z=NULL,ha,e_i,ohne_i,e_ohne_i;
    INT i;
    CTTO(HASHTABLE,MONOMIAL,"tme_monomial__faktor(1)",a);
    CTO(HASHTABLE,"tme_monomial__faktor(2)",b);
    CTO(ANYTYPE,"tme_monomial__faktor(3)",f);




    if (S_O_K(a) == MONOMIAL) {
        if (S_L_S(a) == NULL) {
            goto endr_ende;
            }
        if (S_L_N(a) == NULL) {
            if (S_PA_LI(S_S_S(a)) == 0) {
                OP e;
                e = CALLOCOBJECT();
                erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),e);
                erg += first_partition(cons_null,S_MO_S(e));
                COPY(S_S_K(a),S_MO_K(e));
                MULT_APPLY(f,S_MO_K(e));
                INSERT_HASHTABLE(e,b,add_koeff,eq_monomsymfunc,hash_monompartition);
                goto ende;
                }
            else if (S_PA_LI(S_S_S(a)) == 1) {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_S_K(a),w);
                erg += tme_integer__faktor(S_PA_I(S_S_S(a),0),b,w);
                FREEALL(w);
                goto ende;
                }
            }
        }
    else if (S_O_K(a) == HASHTABLE) {
        if (S_V_II(a,S_V_LI(a)) == 0) {
            goto ende;
            }
        if (S_V_II(a,S_V_LI(a)) == 1) {
            FORALL(z,a, { goto fff; } );
fff:
            if (S_PA_LI(S_MO_S(z)) == 0) {
                OP e;
                e = CALLOCOBJECT();
                erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),e);
                erg += first_partition(cons_null,S_MO_S(e));
                COPY(S_MO_K(z),S_MO_K(e));
                MULT_APPLY(f,S_MO_K(e));
                INSERT_HASHTABLE(e,b,add_koeff,eq_monomsymfunc,hash_monompartition);
                goto ende;
                }
            else if (S_PA_LI(S_MO_S(z)) == 1) {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_MO_K(z),w);
                erg += tme_integer__faktor(S_PA_I(S_MO_S(z),0),b,w);
                FREEALL(w);
                goto ende;
                }
            }
        }


    /* die eigentliche rekursion */

        /* step one: find the minimum length of the partitions in a */
        z = findmin_monomial(a,length_comp_part);
        i = S_PA_LI(S_MO_S(z));
        ha = CALLOCOBJECT();
        COPY(a,ha);

        NEW_HASHTABLE(ohne_i);
        NEW_HASHTABLE(e_ohne_i);

        e_i = CALLOCOBJECT(); 

        while (i>=0) {
            /* hole alle partitionen der laenge i aus dem MONOMIAL ha */
            OP v,m,p;
            INT j,k;
 
            CTTO(MONOMIAL,HASHTABLE,"tme_monomial__faktor(i-ha)",ha);
            if (S_O_K(ha) == MONOMIAL) {
                /* abbruch bedingung */
                if (S_L_S(ha) == NULL) break;
                /* zweite abbruch bedingung */
                if (S_L_N(ha) == NULL)
                if ((S_PA_LI(S_S_S(ha)) == 0) ||
                    (S_PA_II(S_S_S(ha), S_PA_LI(S_S_S(ha))-1 ) == 1)
                   )
                    {
                    OP h=CALLOCOBJECT();
                    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),h);
                    erg +=first_partition(S_PA_L(S_S_S(ha)),S_MO_S(h));
                    COPY(S_S_K(ha),S_MO_K(h));
                    if (not EINSP(f))
                        MULT_APPLY(f,S_MO_K(h));
                    INSERT_HASHTABLE(h,b,add_koeff,eq_monomsymfunc,
                                         hash_monompartition);
                    break;
                    }
                }
            else if (S_O_K(ha) == HASHTABLE) {
                /* abbruch bedingung */
                if (S_V_II(ha,S_V_LI(ha)) == 0) break;
                /* zweite abbruch bedingung */
                if (S_V_II(ha,S_V_LI(ha)) == 1) 
                    {
                    FORALL(z,ha,{goto eee;});
eee:
                    if ((S_PA_LI(S_MO_S(z)) == 0) ||
                        (S_PA_II(S_MO_S(z), S_PA_LI(S_MO_S(z))-1 ) == 1)
                       )
                        {
                        OP h=CALLOCOBJECT();
                        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),h);
                        erg +=first_partition(S_PA_L(S_MO_S(z)),S_MO_S(h));
                        COPY(S_MO_K(z),S_MO_K(h));
                        if (not EINSP(f))
                            MULT_APPLY(f,S_MO_K(h));
                        INSERT_HASHTABLE(h,b,add_koeff,eq_monomsymfunc,
                                       hash_monompartition);
                        break;
                        }
                    }
                }
 

            FORALL(z,ha, {
                if (S_PA_LI(S_MO_S(z)) == i) /* kommt nach ohne_i */
                    {
                    for (j=0;j<i;j++)
                        if (S_PA_II(S_MO_S(z),j) > 1) break;
                    /* an der stelle j geht die eigentliche partition los */
                    v = CALLOCOBJECT();
                    erg +=m_il_v(i-j,v);
                    for (k=0;k<S_V_LI(v);k++)
                        M_I_I(S_PA_II(S_MO_S(z),k+j)-1,S_V_I(v,k));
                    p = CALLOCOBJECT();
                    erg +=b_ks_pa(VECTOR,v,p);
                    m = CALLOCOBJECT();
                    erg +=b_sk_mo(p,CALLOCOBJECT(),m);
                    COPY(S_MO_K(z),S_MO_K(m));
                    CTO(MONOM,"(i1)",m);
                    INSERT_HASHTABLE(m,ohne_i,add_koeff,eq_monomsymfunc,
                                      hash_monompartition);
                    }
                });
            /* falls ohne_i leer zum naechsten i */

            if (S_V_II(ohne_i,S_V_LI(ohne_i)) == 0) {
                i++;
                continue;
                }
 
            /* der beitrag zum ergebnis ist jetzt e_i \times ohne_i */

            erg += tme_monomial__faktor(ohne_i,e_ohne_i,f);
            M_I_I(i,e_i);
            erg += mee_integer_hashtable_(e_i,e_ohne_i,b,cons_eins);
 
            /* jetzt muss noch ha geupdatet werden, es wird der entsprechende
               teil abgezogen */
 
           
            erg += mem_integer_hashtable_(e_i,ohne_i,ha,cons_negeins);

            i++;
            /* ohne_i leeren */
            CLEAR_HASHTABLE(ohne_i);
            CLEAR_HASHTABLE(e_ohne_i);
            }
        FREEALL(ha);
        FREEALL(ohne_i);
        FREEALL(e_ohne_i);
        FREEALL(e_i);

ende:
    CTO(HASHTABLE,"tme_monomial__faktor(e2)",b);
    ENDR("tme_monomial__faktor");
}
 

INT tme___faktor(a,b,f) OP a,b; OP f;
/* AK 161001 */
{
    INT erg = OK;
    CTTTTO(INTEGER,PARTITION,MONOMIAL,HASHTABLE,"tme___faktor(1)",a);
    CTO(HASHTABLE,"tme___faktor(2)",b);

    if (S_O_K(a) == INTEGER)
        {
        erg += tme_integer__faktor(a,b,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += tme_partition__faktor(a,b,f);
        }
    else if (S_O_K(a) == MONOMIAL)
        {
        erg += tme_monomial__faktor(a,b,f);
        }
    else if (S_O_K(a) == HASHTABLE)
        {
        erg += tme_hashtable__faktor(a,b,f);
        }
    ENDR("t_MONOMIAL_ELMSYM");
}

