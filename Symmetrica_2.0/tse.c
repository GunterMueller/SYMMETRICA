#include "def.h"
#include "macro.h"


INT the_integer__faktor();
INT tse_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tse_integer__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a)<0),"tse_integer__faktor:integer < 0");

    erg += the_integer__faktor(a,b,f);

    ENDR("tse_integer__faktor");
}
 

INT tsh_integer__faktor();
INT mee_partition__();

INT tse_partition__faktor_pre040202(a,b,f) OP a,b,f;
{
    INT t_schur_naegelsbach();
    INT erg = OK;
    CTO(PARTITION,"tse_partition__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0) {
        erg += the_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += the_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else 
        {
        erg += t_schur_naegelsbach(a,b,f,tsh_integer__faktor,mee_partition__);
        goto ende;
        }
ende:
    CTTO(HASHTABLE,ELMSYM,"tse_partition__faktor(2-ende)",b);
    ENDR("tse_partition__faktor");
}

INT tse_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tse_partition__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0) {
        erg += the_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1)
        {
        erg += the_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else 
        {
        OP m,p;
        m = CALLOCOBJECT();
        p = CALLOCOBJECT();
        conjugate_partition(a,p);
        tsh_jt(p,m);
        FREEALL(p);
        tsh_eval_jt(b,f,m);
        FREEALL(m);

        goto ende;
        }
ende:
    CTTO(HASHTABLE,ELMSYM,"tse_partition__faktor(2-ende)",b);
    ENDR("tse_partition__faktor");
}



INT tse___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"tse___faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse___faktor(2)",b);
    if (S_O_K(a) == INTEGER) {
        erg += tse_integer__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tse_partition__faktor(a,b,f);
        goto ende;
        }
    else {
        T_FORALL_MONOMIALS_IN_A(a,b,f,tse_partition__faktor);
        }
ende:
    ENDR("tse___faktor");
}

INT tse_schur__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP z,ha;
 
    CTTO(HASHTABLE,SCHUR,"tse_schur__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse_schur__faktor(2)",b);
 
    if (NULLP(a)) { goto endr_ende; }
 

    if (S_O_K(a) == SCHUR)
        {
        if (S_L_N(a) == NULL) {
            erg += tse_partition__faktor(S_S_S(a),b,f);
            goto ende;
            }
        }
    else /* HASHTABLE */
        {
        if (S_V_II(a,S_V_LI(a)) == 1) {
            OP z;
            FORALL(z,a, { goto eee; } );
            eee:
            erg += tse_partition__faktor(S_MO_S(z),b,f);
            goto ende;
            }
        }


    ha = CALLOCOBJECT();
    if (S_O_K(a) == HASHTABLE)
        COPY(a,ha);
    else
        t_SCHUR_HASHTABLE(a,ha);

/* such die lex max partition  */
/* die partition werden lex immer kleiner */
    CTO(HASHTABLE,"tse_schur__faktor(ha)",ha);
    while (not NULLP_HASHTABLE(ha)) {
        OP ff,m;
        z = findmax_monomial(ha,comp_partition);
        ff = CALLOCOBJECT();
        m = CALLOCOBJECT();
        MULT(S_MO_K(z),f,ff);
        erg += b_sk_mo(CALLOCOBJECT(),ff,m);
        erg += conjugate_partition(S_MO_S(z),S_MO_S(m));

        if (S_PA_II(S_MO_S(z), S_PA_LI(S_MO_S(z))-1)  == 1) { /* elmsym */
            FREESELF(z);
            DEC_INTEGER(S_V_I(ha,S_V_LI(ha)));
            }
        else {
            INT tes_partition__faktor();
            OP inf;
            inf = CALLOCOBJECT(); /* invers koeff */
            ADDINVERS(S_MO_K(m),inf);
            erg += tes_partition__faktor(S_MO_S(m),ha,inf);
            FREEALL(inf);
            }

        CTO(HASHTABLE,"tse_schur__faktor(ha-i)",ha);
        CTTO(HASHTABLE,ELMSYM,"tse_schur__faktor(b-i)",b);

        if (S_O_K(b) == HASHTABLE)
            insert_scalar_hashtable(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
        else
            insert_list(m,b,add_koeff,comp_monomelmsym);
        }


    FREEALL(ha);
ende:
    CTTO(HASHTABLE,ELMSYM,"tse_schur__faktor(2-ende)",b);
    ENDR("tse_schur__faktor");
}
 






INT tse___faktor_slow(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,SCHUR,PARTITION,INTEGER,"tse___faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tse___faktor(2)",b);
    if (S_O_K(a) == INTEGER) {
        erg += tse_integer__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tse_partition__faktor(a,b,f);
        goto ende;
        }
    else {
        tse_schur__faktor(a,b,f);
        goto ende;
        }
ende:
    ENDR("tse___faktor");
}




INT t_SCHUR_ELMSYM(a,b) OP a,b;
{
    INT erg = OK;
    INT t = 0;
    CTTTTO(INTEGER,HASHTABLE,SCHUR,PARTITION,"t_SCHUR_HOMSYM",a);
    TCE2(a,b,t_SCHUR_ELMSYM,ELMSYM);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    tse___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_ELMSYM(b,b);
 
    ENDR("t_SCHUR_ELMSYM");
}
