#include "def.h"
#include "macro.h"

INT tme_integer__faktor();
INT tpe_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tpe_integer__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe_integer__faktor(2)",b);
    erg += tme_integer__faktor(a,b,f);
    ENDR("tpe_integer__faktor");
}

OP find_tme_integer();

OP find_tpe_integer(a) OP a;
/* AK 300102 */
{
    INT erg = OK;
    CTO(INTEGER,"find_tpe_integer(1)",a);
    return find_tme_integer(a);
    ENDO("find_tpe_integer");
}

INT mee_hashtable_hashtable_();

INT t_splitpart();
INT t_productexponent();
INT tpe_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tpe_partition__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe_partition__faktor(2)",b);
    erg += t_productexponent(a,b,f,tpe_integer__faktor,find_tpe_integer);
    ENDR("tpe_partition__faktor");
}

#ifdef UNDEF
INT tpe_partition__faktor_pre300102(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tpe_partition__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        erg += tpe_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += tpe_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        erg += t_splitpart(a,b,f,tpe_partition__faktor,mee_hashtable_hashtable_);
        goto ende;
        }
ende:
    ENDR("tpe_partition__faktor");
}
#endif

INT tpe_powsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,POWSYM,"tpe_powsym__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe_powsym__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tpe_partition__faktor);
    ENDR("tpe_powsym__faktor");
}

 
INT tpe_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tpe_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe_hashtable__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tpe_partition__faktor);
    ENDR("tpe_hashtable__faktor");
}


INT tpe___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,POWSYM,PARTITION,"tpe___faktor(1)",a);
    CTTO(HASHTABLE,ELMSYM,"tpe___faktor(2)",b);

    if (S_O_K(a) == INTEGER) {
        erg += tpe_integer__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tpe_partition__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == POWSYM) {
        erg += tpe_powsym__faktor(a,b,f);
        goto eee;
        }
    else /* HASHTABLE */ {
        erg += tpe_hashtable__faktor(a,b,f);
        goto eee;
        }
eee:
    ENDR("tpe___faktor");
}

INT t_POWSYM_ELMSYM(a,b) OP a,b;
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"t_POWSYM_ELMSYM",a);
    TCE2(a,b,t_POWSYM_ELMSYM,ELMSYM);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    tpe___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_ELMSYM(b,b);
 

    ENDR("t_POWSYM_ELMSYM");
}
