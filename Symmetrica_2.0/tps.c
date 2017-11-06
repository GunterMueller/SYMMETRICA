#include "def.h"
#include "macro.h"

INT tps___faktor(a,b,f) OP a,b,f;
{
    INT erg = OK;
    OP m;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"tps___faktor(1)",a);
    CTTO(HASHTABLE,SCHUR,"tps___faktor(2)",b);
    CTO(ANYTYPE,"tps___faktor(3)",f);

    m=CALLOCOBJECT();
    erg += first_partition(cons_null,m);
    erg += mps___(a,m,b,f);
    FREEALL(m);

    ENDR("tps___faktor");
}

INT t_POWSYM_SCHUR(a,b) OP a,b;
/* AK 270901 */
/* using multiplication p_k * S_I = \sum S_J */
/* fastest up to now */
{
    INT erg = OK;
    OP m;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"t_POWSYM_SCHUR",a);
    TCE2(a,b,t_POWSYM_SCHUR,SCHUR);

    m=CALLOCOBJECT();
    erg += first_partition(cons_null,m);
    erg += mult_powsym_schur(a,m,b);
    FREEALL(m);
    CTTO(SCHUR,HASHTABLE,"t_POWSYM_SCHUR(e2)",b);
    ENDR("t_POWSYM_SCHUR");
}

