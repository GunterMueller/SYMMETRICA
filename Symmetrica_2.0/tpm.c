#include "def.h"
#include "macro.h"
INT t_splitpart();

INT tpm_integer__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP m;
    CTO(INTEGER,"tpm_integer__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tpm_integer__faktor(2)",b);
    SYMCHECK( (S_I_I(a) < 0), "tpm_integer__faktor:integer < 0");

    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(), m);
    erg += first_partition(a,S_MO_S(m));
    COPY(f,S_MO_K(m));
 
    if (S_O_K(b) == MONOMIAL) 
        INSERT_LIST(m,b,add_koeff,comp_monommonomial);
    else
        insert_scalar_hashtable(m,b,add_koeff,eq_monomsymfunc,hash_monompartition);
 
    ENDR("tpm_integer__faktor");
}

INT mmm_hashtable_hashtable_();
INT tpm_partition__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(PARTITION,"tpm_partition__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tpm_partition__faktor(2)",b);
    if (S_PA_LI(a) == 0) {
        erg += tpm_integer__faktor(cons_null,b,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += tpm_integer__faktor(S_PA_I(a,0),b,f);
        }
    else {
        erg += t_splitpart(a,b,f,tpm_partition__faktor,mmm_hashtable_hashtable_);
        }
    ENDR("tpm_partition__faktor");
}

INT tpm_powsym__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTO(HASHTABLE,POWSYM,"tpm_powsym__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tpm_powsym__faktor(2)",b);

    T_FORALL_MONOMIALS_IN_A(a,b,f,tpm_partition__faktor); 
 
    ENDR("tpm_powsym__faktor");
}

 
INT tpm_hashtable__faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"tpm_hashtable__faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tpm_hashtable__faktor(2)",b);
    T_FORALL_MONOMIALS_IN_A(a,b,f,tpm_partition__faktor); 
    ENDR("tpm_hashtable__faktor");
}


INT tpm___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,POWSYM,PARTITION,"tpm___faktor(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"tpm___faktor(2)",b);

    if (S_O_K(a) == INTEGER) {
        erg += tpm_integer__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == PARTITION) {
        erg += tpm_partition__faktor(a,b,f);
        goto eee;
        }
    else if (S_O_K(a) == POWSYM) {
        erg += tpm_powsym__faktor(a,b,f);
        goto eee;
        }
    else /* HASHTABLE */ {
        erg += tpm_hashtable__faktor(a,b,f);
        goto eee;
        }
eee:
    ENDR("tpm___faktor");
}

INT t_POWSYM_MONOMIAL(a,b) OP a,b;
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"t_POWSYM_MONOMIAL",a);
    TCE2(a,b,t_POWSYM_MONOMIAL,MONOMIAL);

    if (S_O_K(b) == EMPTY)
        {
        erg += init_hashtable(b);
        t=1;
        }
    tpm___faktor(a,b,cons_eins);
    if (t==1) t_HASHTABLE_MONOMIAL(b,b);
 

    ENDR("t_POWSYM_MONOMIAL");
}
