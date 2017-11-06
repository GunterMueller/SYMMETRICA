#include "def.h"
#include "macro.h"

INT t_MONOMIAL_SCHUR(a,b) OP a,b;
{
    INT erg = OK;
    OP m;
    CTTTTO(HASHTABLE,INTEGER,MONOMIAL,PARTITION,"t_MONOMIAL_SCHUR",a);
    TCE2(a,b, t_MONOMIAL_SCHUR,SCHUR);

    m=CALLOCOBJECT();
    erg += first_partition(cons_null,m);
    erg += mult_monomial_schur(a,m,b);
    FREEALL(m);
    ENDR("t_MONOMIAL_SCHUR");
}
