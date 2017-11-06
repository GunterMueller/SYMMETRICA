#include "def.h"
#include "macro.h"

INT t_ELMSYM_SCHUR_pre041201(a,b) OP a,b;
/* AK 121001 */
/* conjugate to t_HOMSYM_SCHUR */
{
    INT erg = OK;
    OP c;
    CTTO(PARTITION,ELMSYM,"t_ELMSYM_SCHUR_pre041201",a);
    if (S_O_K(a) == PARTITION)
        {
        c = callocobject();
        erg += t_HOMSYM_SCHUR(a,c);
        erg += freeself(b);
        erg += conjugate_schur(c,b);
        erg += freeall(c);
        }
    else {
        OP z;
        z=a;
        while (z != NULL)
            {    C_O_K(z,HOMSYM); z = S_L_N(z); }
        c = callocobject();
        erg += t_HOMSYM_SCHUR(a,c);
        erg += freeself(b);
        erg += conjugate_schur(c,b);
        erg += freeall(c);
        z=a;
        while (z != NULL)
            {    C_O_K(z,ELMSYM); z = S_L_N(z); }
        }
    ENDR("t_ELMSYM_SCHUR_pre041201");
}

INT tes_integer__faktor();

INT mes_partition__();
INT tes_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tes_partition__faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tes_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        erg += tes_integer__faktor(cons_null,b,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += tes_integer__faktor(S_PA_I(a,0),b,f);
        }
    else {
        OP c;
        c = CALLOCOBJECT();
        first_partition(cons_null,c);
        mes_partition__(a,c,b,f);
        FREEALL(c);
        }
    ENDR("tpe_partition__faktor");
}


INT tes_elmsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,ELMSYM,"tes_elmsym__faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tes_elmsym__faktor(2)",b);

    T_FORALL_MONOMIALS_IN_A(a,b,f,tes_partition__faktor); 
 
    ENDR("tes_elmsym__faktor");
}

 
INT tes_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tes_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tes_hashtable__faktor(2)",b);
 
    T_FORALL_MONOMIALS_IN_A(a,b,f,tes_partition__faktor); 
    ENDR("tes_hashtable__faktor");
}
 

INT tes___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"tes___faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tes___faktor(2)",b);

    if (S_O_K(a) == INTEGER)
        {
        tes_integer__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)
        {
        tes_partition__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == HASHTABLE)
        {
        tes_hashtable__faktor(a,b,f);
        goto ende;
        }
    else if (S_O_K(a) == ELMSYM)
        {
        tes_elmsym__faktor(a,b,f);
        goto ende;
        }
ende:
    ENDR("tes___faktor");
}

INT tes_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP m;
    CTO(INTEGER,"tes_integer__faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tes_integer__faktor(2)",b);
    SYMCHECK((S_I_I(a) < 0), "tes_integer__faktor:parameter < 0");
 
    m = CALLOCOBJECT();
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    COPY(f,S_MO_K(m));
    erg += last_partition(a,S_MO_S(m));
    if (S_O_K(b) == SCHUR)
        INSERT_LIST(m,b,add_koeff,comp_monomschur);
    else
        insert_scalar_hashtable(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
    ENDR("tes_integer__faktor");
}

INT t_ELMSYM_SCHUR(a,b) OP a,b;
/* AK 190901 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"t_ELMSYM_SCHUR(1)",a);
    TCE2(a,b,t_ELMSYM_SCHUR,SCHUR);

    if (S_O_K(b) == EMPTY) {
        init_hashtable(b); t=1;
        }
    tes___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_SCHUR(b,b);
    ENDR("t_ELMSYM_SCHUR");
}
