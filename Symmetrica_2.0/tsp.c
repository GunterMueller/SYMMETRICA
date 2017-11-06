#include "def.h"
#include "macro.h"

INT tsp_schur__faktor();
INT thp_integer__faktor();
INT tep_integer__faktor();
INT mhp_integer__();
INT mhp_integer_hashtable_();
INT mhs_integer__();
INT tsp_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tsp_integer__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tsp_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0), "tsp_integer__faktor:parameter <0");
    erg += thp_integer__faktor(a,b,f);
    ENDR("tsp_integer__faktor");
}

INT tsp_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tsp_partition__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tsp_partition__faktor(2)",b);
    CTO(ANYTYPE,"tsp_partition__faktor(3)",f);
    if (S_PA_LI(a) == 0)
        {
        erg += thp_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += thp_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        OP m;
        m = CALLOCOBJECT();
        erg += m_pa_s(a,m);
        erg += tsp_schur__faktor(m,b,f);
        FREEALL(m);
        goto ende;
        }
ende:
    CTTO(HASHTABLE,POWSYM,"tsp_partition__faktor(e2)",b);
    ENDR("tsp_partition__faktor");
}

INT tsp___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"tsp___faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tsp___faktor(2)",b);
    CTO(ANYTYPE,"tsp___faktor(3)",f);


    if (S_O_K(a) == INTEGER)
       {
       erg += tsp_integer__faktor(a,b,f);
       goto ende;
       }
    else if (S_O_K(a) == PARTITION)
       {
       erg += tsp_partition__faktor(a,b,f);
       goto ende;
       }
    else 
       {
       erg += tsp_schur__faktor(a,b,f);
       goto ende;
       }
ende:
    CTTO(HASHTABLE,POWSYM,"tsp___faktor(e2)",b);
    ENDR("tsp___faktor");
}

INT tsp_schur__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP z,ha,ohne_i,h_ohne_i,p_i;
    INT i;
    OP h_i;

    CTTO(HASHTABLE,SCHUR,"tsp_schur__faktor(1)",a);
    CTTO(HASHTABLE,POWSYM,"tsp_schur__faktor(2)",b);
    CTO(ANYTYPE,"tsp_schur__faktor(3)",f);

    if (NULLP(a)) { goto ende; }

    if (S_O_K(a) == SCHUR)
        {
        if (S_L_N(a) == NULL) {
            if (S_PA_LI(S_S_S(a)) == 0) {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_S_K(a),w);
                erg += thp_integer__faktor(cons_null,b,w);
                FREEALL(w);
                goto ende;
                }
            if (S_PA_LI(S_S_S(a)) == 1) {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_S_K(a),w);
                erg += thp_integer__faktor(S_S_SI(a,0),b,w);
                FREEALL(w);
                goto ende;
                }
            if (S_PA_II(S_S_S(a), S_PA_LI(S_S_S(a))-1) == 1) /* elmsym */
                {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_S_K(a),w);
                erg += tep_integer__faktor(S_PA_L(S_S_S(a)),b,w);
                FREEALL(w);
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
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_MO_K(z),w);
                erg += thp_integer__faktor(cons_null,b,w);
                FREEALL(w);
                goto ende;
                }
            if (S_PA_LI(S_MO_S(z)) == 1) {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_MO_K(z),w);
                erg += thp_integer__faktor(S_PA_I(S_MO_S(z),0),b,w);
                FREEALL(w);
                goto ende;
                }
            if (S_PA_II(S_MO_S(z), S_PA_LI(S_MO_S(z))-1) == 1) /* elmsym */
                {
                OP w;
                w = CALLOCOBJECT();
                MULT(f,S_MO_K(z),w);
                erg += tep_integer__faktor(S_PA_L(S_MO_S(z)),b,w);
                FREEALL(w);
                goto ende;
                }
            }
        }
    
/* such die partition mit dem kuerzesten maximalen teil */
    z = findmin_schur(a,maxpart_comp_part);
    if (S_PA_LI(S_MO_S(z)) == 0) 
        i = 0;
    else
        i = S_PA_II(S_MO_S(z),S_PA_LI(S_MO_S(z))-1);

    ha = CALLOCOBJECT();
    if (S_O_K(a) == HASHTABLE)
        COPY(a,ha);
    else
        t_SCHUR_HASHTABLE(a,ha);

    CTO(HASHTABLE,"tsp_schur__faktor(i1)",ha);
    if (i==0) /* s[0] in ha */
        {
        OP m;
        FORALL(z,ha, { if (S_PA_LI(S_MO_S(z)) == 0) goto jjj; } );
        jjj: 
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(), m);
        MULT(f,S_MO_K(z),S_MO_K(m));
        COPY(S_MO_S(z),S_MO_S(m));
        FREESELF(z); 
        DEC_INTEGER(S_V_I(ha,S_V_LI(ha))); /* counter-- */
        i = 1;
        INSERT_POWSYMMONOM_(m,b);
        }

    NEW_HASHTABLE(ohne_i);
    NEW_HASHTABLE(h_ohne_i);
    NEW_HASHTABLE(p_i);
    h_i = CALLOCOBJECT();


    while (i>0) {
        OP v,p,m;
        INT k;
        if (NULLP(ha)) break;

        FORALL(z,ha, {
             if (S_PA_II(S_MO_S(z),S_PA_LI(S_MO_S(z))-1) == i) /* kommt nach ohne_i */
                 {
                 v = CALLOCOBJECT();
                 erg +=m_il_v(S_PA_LI(S_MO_S(z))-1,v);
                 for (k=0;k<S_V_LI(v);k++)
                     M_I_I(S_PA_II(S_MO_S(z),k),S_V_I(v,k));
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

        erg += tsp_schur__faktor(ohne_i,h_ohne_i,f);

        M_I_I(i,h_i);
        erg += mhp_integer_hashtable_(h_i,h_ohne_i,b,cons_eins);
        /* b = b + p_i * h_ohne_i */

        CLEAR_HASHTABLE(p_i);
        CLEAR_HASHTABLE(h_ohne_i);
        mhs_integer__(h_i,ohne_i,ha,cons_negeins);
        CLEAR_HASHTABLE(ohne_i);
        i++;
        }
    FREEALL(ha);
    FREEALL(ohne_i);
    FREEALL(h_ohne_i);
    FREEALL(p_i); 
    FREEALL(h_i); 
ende:
    CTTO(HASHTABLE,POWSYM,"tsp_schur__faktor(e2)",b);
    ENDR("tsp_schur__faktor");
}

INT t_SCHUR_POWSYM(a,b) OP a,b;
/* AK 191001 */
/* rekursion s_i1,i2,..,in = s_in \times s_i1,...,in-1 - ...... */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"t_SCHUR_POWSYM(1)",a);
    TCE2(a,b,t_SCHUR_POWSYM,POWSYM);

    if (S_O_K(b) == EMPTY) {
        t=1;
        init_hashtable(b);
        }

    CTTO(HASHTABLE,POWSYM,"t_SCHUR_POWSYM(2)",b);
    tsp___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_POWSYM(b,b);
    CTTO(HASHTABLE,POWSYM,"t_SCHUR_POWSYM(2)",b);
    ENDR("t_SCHUR_POWSYM");
}
