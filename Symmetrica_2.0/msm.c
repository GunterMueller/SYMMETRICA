#include "def.h"
#include "macro.h"

extern INT tsm___faktor();

INT mult_schur_monomial(a,b,c) OP a,b,c;
/* AK 081001 */
{
    OP d;
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,SCHUR,PARTITION,"mult_schur_monomial",a);
    CTTTO(MONOMIAL,PARTITION,HASHTABLE,"mult_schur_monomial",b);
    CTTTO(EMPTY,MONOMIAL,HASHTABLE,"mult_schur_monomial",c);

    NEW_HASHTABLE(d);
    erg += tsm___faktor(a,d,cons_eins);
    erg += mult_monomial_monomial(d,b,c);
    FREEALL(d);
    ENDR("mult_schur_monomial");
}

