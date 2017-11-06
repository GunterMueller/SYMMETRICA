#include "def.h"
#include "macro.h"

INT thm_integer__faktor();
INT mem_integer_hashtable_();
INT mes_integer_hashtable_();

INT t_SCHUR_MONOMIAL_pre211101(a,b) OP a,b;
/* AK 190901 */
/* fastest up to now */
/* with kostka number */
{
    INT erg = OK;
    CTTO(SCHUR,PARTITION,"t_SCHUR_MONOMIAL(1)",a);
    CE2(a,b,t_SCHUR_MONOMIAL_pre211101);
    if (S_O_K(a) == PARTITION)
       {
       /* definition mittels kostkanumber */
       OP c;
       if (S_PA_LI(a) == 0) {
           erg += b_skn_mon(callocobject(),callocobject(),NULL,b);
           M_I_I(1,S_S_K(b));
           erg += first_partition(cons_null,S_S_S(b));
           goto endr_ende;
           }
       else if (S_PA_LI(a) == 1) {
           erg += t_HOMSYM_MONOMIAL(S_PA_I(a,0),b);
           goto endr_ende;
           }
       c = callocobject();
       erg += copy_partition(a,c);
       erg += init(MONOMIAL,b);
       do {
          OP m;
          m = callocobject();
          erg += m_pa_mon(c,m);
          erg += kostka_number(c,a,S_S_K(m));
          if (not NULLP(S_S_K(m)))
              INSERT_LIST(m,b,NULL,comp_monommonomial);
          else 
              erg += freeall(m);
       } while (next_apply(c));
       erg += freeall(c);
       goto endr_ende;
       }
    else if (S_O_K(a) == SCHUR)
       {
       OP z,res;
       erg += init(MONOMIAL,b);
       FORALL(z,a, {
          res=callocobject();
          erg += t_SCHUR_MONOMIAL_pre211101(S_MO_S(z),res);
          MULT_APPLY(S_MO_K(z),res);
          INSERT_LIST(res,b,add_koeff,comp_monommonomial);
          } );
       }
    ENDR("t_SCHUR_MONOMIAL_pre211101");
}


INT tsm_schur__faktor();
INT tsm_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tsm_integer__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tsm_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0), "tsm_integer__faktor:parameter <0");
    erg += thm_integer__faktor(a,b,f);
    ENDR("tsm_integer__faktor");
}

INT tsm_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tsm_partition__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tsm_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0)
        {
        erg += thm_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += thm_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
#ifdef UNDEF
/* ist langsamer */
    else if (S_PA_LI(a) == 2) 
        { /* determinanten formel */
        OP h1,h2;
        OP m;
        OP find_thm_integer();

        h1 = find_thm_integer(S_PA_I(a,0));
        h2 = find_thm_integer(S_PA_I(a,1));

        mmm___(h1,h2,b,f);

        DEC_INTEGER(S_PA_I(a,0));
        INC_INTEGER(S_PA_I(a,1));
        h1 = find_thm_integer(S_PA_I(a,0));
        h2 = find_thm_integer(S_PA_I(a,1));
        m = CALLOCOBJECT();
        ADDINVERS(f,m);
        mmm___(h1,h2,b,m);
        FREEALL(m);
        INC_INTEGER(S_PA_I(a,0));
        DEC_INTEGER(S_PA_I(a,1));
        
        /* erg += thm_integer__faktor(S_PA_I(a,0),b,f); */
        goto ende;
        }
#endif
    else {
        OP m;
        m = CALLOCOBJECT();
        erg += m_pa_s(a,m);
        erg += tsm_schur__faktor(m,b,f);
        FREEALL(m);
        goto ende;
        }
ende:
    ENDR("tsm_partition__faktor");
}

INT tsm___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"tsm___faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tsm___faktor(2)",b);


    if (S_O_K(a) == INTEGER)
       {
       erg += tsm_integer__faktor(a,b,f);
       goto ende;
       }
    else if (S_O_K(a) == PARTITION)
       {
       erg += tsm_partition__faktor(a,b,f);
       goto ende;
       }
    else 
       {
       erg += tsm_schur__faktor(a,b,f);
       goto ende;
       }
ende:
    CTTO(HASHTABLE,MONOMIAL,"tsm___faktor(e2)",b);
    ENDR("tsm___faktor");
}

INT tsm_schur__faktor(a,b,f) OP a,b,f;
/* AK 260503: changed error in computation of factor in the trival cases at the beginning */
{
    INT erg = OK;
    OP z,ha,ohne_i,h_ohne_i;
    INT i;
    OP h_i;

    CTTO(HASHTABLE,SCHUR,"tsm_schur__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tsm_schur__faktor(2)",b);
    CTO(ANYTYPE,"tsm_schur__faktor(3)",f);

    if (NULLP(a)) { goto endr_ende; }

    if (S_O_K(a) == SCHUR)
        {
        if (S_L_N(a) == NULL) {
            if (S_PA_LI(S_S_S(a)) == 0) {
                z=CALLOCOBJECT(); 
                MULT(f,S_S_K(a),z);
                erg += thm_integer__faktor(cons_null,b,S_S_K(a));
                FREEALL(z);
                goto ende;
                }
            if (S_PA_LI(S_S_S(a)) == 1) {
                z=CALLOCOBJECT();
                MULT(f,S_S_K(a),z);
                erg += thm_integer__faktor(S_S_SI(a,0),b,z);
                FREEALL(z);
                goto ende;
                }
            }
        }
    else /* HASHTABLE */
        {
        if (S_V_II(a,S_V_LI(a)) == 1) {
            OP z=NULL;
            FORALL(z,a, { goto eee; } );
            eee:
            if (S_PA_LI(S_MO_S(z)) == 0) {
                ha = CALLOCOBJECT();
                MULT(f,S_MO_K(z),ha);
                erg += thm_integer__faktor(cons_null,b,ha);
                FREEALL(ha);
                goto ende;
                }
            if (S_PA_LI(S_MO_S(z)) == 1) {
                ha = CALLOCOBJECT();
                MULT(f,S_MO_K(z),ha);
                erg += thm_integer__faktor(S_PA_I(S_MO_S(z),0),b,ha);
                FREEALL(ha);
                goto ende;
                }
            }
        }
    
/* such die partition mit den wenigsten teilen */
    z = findmin_schur(a,length_comp_part);
    i = S_PA_LI(S_MO_S(z));
    ha = CALLOCOBJECT();
    
    COPY(a,ha);

    NEW_HASHTABLE(ohne_i);
    NEW_HASHTABLE(h_ohne_i);
    h_i = CALLOCOBJECT();


    while (i>=0) {
        OP v,p,m;
        INT k,j;
        if (NULLP(ha)) break;

        FORALL(z,ha, {
             if (S_PA_LI(S_MO_S(z)) == i) /* kommt nach ohne_i */
                 {
                 v = CALLOCOBJECT();
                 for (j=0;j<S_PA_LI(S_MO_S(z));j++)
                     if (S_PA_II(S_MO_S(z),j) > 1) break;
                 erg +=m_il_v(S_PA_LI(S_MO_S(z))-j,v);
                 for (k=0;k<S_V_LI(v);k++)
                     M_I_I(S_PA_II(S_MO_S(z),k+j)-1,S_V_I(v,k));
                 p = CALLOCOBJECT();
                 erg +=b_ks_pa(VECTOR,v,p);
                 m = CALLOCOBJECT();
                 erg +=b_sk_mo(p,CALLOCOBJECT(),m);
                 COPY(S_MO_K(z),S_MO_K(m));
                 INSERT_HASHTABLE(m,ohne_i,add_koeff,eq_monomsymfunc,hash_monompartition);
                 }
             });
        /* falls ohne_i leer zum naechsten i */

        if (NULLP(ohne_i)) { i++; continue; }

        erg += tsm_schur__faktor(ohne_i,h_ohne_i,f);

        M_I_I(i,h_i);

        
        erg += mem_integer_hashtable_(h_i,h_ohne_i,b,cons_eins);
        /* b = b + e_i * h_ohne_i */


        CLEAR_HASHTABLE(h_ohne_i);

        erg += mes_integer_hashtable_(h_i,ohne_i,ha,cons_negeins);

        CLEAR_HASHTABLE(ohne_i);
        i++;
        }
    FREEALL(ha);
    FREEALL(ohne_i);
    FREEALL(h_ohne_i);
    FREEALL(h_i); 
ende:
    ENDR("tsm_faktor");
}

INT t_SCHUR_MONOMIAL(a,b) OP a,b;
/* AK 191001 */
/* rekursion s_i1,i2,..,in = s_in \times s_i1,...,in-1 - ...... */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"t_SCHUR_MONOMIAL(1)",a);
    TCE2(a,b,t_SCHUR_MONOMIAL,MONOMIAL);

    if (S_O_K(b) == EMPTY) {
        t=1;
        init_hashtable(b);
        }

    CTTO(HASHTABLE,MONOMIAL,"t_SCHUR_MONOMIAL(2)",b);
    tsm___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_MONOMIAL(b,b);
    CTTO(HASHTABLE,MONOMIAL,"t_SCHUR_MONOMIAL(e2)",b);
    ENDR("t_SCHUR_MONOMIAL");
}
