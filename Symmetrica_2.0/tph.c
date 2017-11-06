
#include "def.h"
#include "macro.h"

INT tmh_integer__faktor();
INT tph_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(INTEGER,"tph_integer__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tph_integer__faktor(2)",b);
    erg += tmh_integer__faktor(a,b,f);
    ENDR("tph_integer__faktor");
}

OP find_tmh_integer();
OP find_tph_integer(a) OP a;
/* AK 300102 */
{
    INT erg = OK;
    CTO(INTEGER,"find_tph_integer(1)",a);
    return find_tmh_integer(a);
    ENDO("find_tph_integer");
}

INT mhh_hashtable_hashtable_();
INT t_splitpart();

INT t_productexponent();

INT tph_partition__faktor(a,b,f) OP a,b,f;
/* AK 300102 */
{
    return t_productexponent(a,b,f,tph_integer__faktor,find_tph_integer);
}
 
INT tph_partition__faktor_pre300102(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tph_partition__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tph_partition__faktor(2)",b);

    if (S_PA_LI(a) == 0) {
        erg += tph_integer__faktor(cons_null,b,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += tph_integer__faktor(S_PA_I(a,0),b,f);
        goto ende;
        }
    else {
        t_splitpart(a,b,f,tph_partition__faktor,mhh_hashtable_hashtable_);
        goto ende;
        }
ende:
    ENDR("tph_partition__faktor");
}



INT tph_powsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;

    CTTO(HASHTABLE,POWSYM,"tph_powsym__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tph_powsym__faktor(2)",b);

    T_FORALL_MONOMIALS_IN_A(a,b,f,tph_partition__faktor); 
 
    ENDR("tph_powsym__faktor");
}

 
INT tph_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;

    CTO(HASHTABLE,"tph_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tph_hashtable__faktor(2)",b);
 
    T_FORALL_MONOMIALS_IN_A(a,b,f,tph_partition__faktor); 

    ENDR("tph_hashtable__faktor");
}


INT tph___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,POWSYM,PARTITION,"tph___faktor(1)",a);
    CTTO(HASHTABLE,HOMSYM,"tph___faktor(2)",b);

    if (S_O_K(a) == INTEGER) {
        erg += tph_integer__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tph_partition__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == POWSYM) {
        erg += tph_powsym__faktor(a,b,f);
        goto eee;
        }
    else /* HASHTABLE */ {
        erg += tph_hashtable__faktor(a,b,f);
        goto eee;
        }
eee:
    ENDR("tph___faktor");
}

INT t_POWSYM_HOMSYM(a,b) OP a,b;
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"t_POWSYM_HOMSYM",a);
    TCE2(a,b,t_POWSYM_HOMSYM,HOMSYM);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    tph___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_HOMSYM(b,b);
 
    ENDR("t_POWSYM_HOMSYM");
}
