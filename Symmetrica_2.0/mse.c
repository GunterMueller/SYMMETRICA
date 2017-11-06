
#include "def.h"
#include "macro.h"

INT tse___faktor();

INT mult_schur_elmsym(a,b,c) OP a,b,c;
/* AK 081001 */
{
    OP d;
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,SCHUR,PARTITION,"mult_schur_elmsym(1)",a);
    CTTTO(ELMSYM,PARTITION,HASHTABLE,"mult_schur_elmsym(2)",b);
    CTTTO(EMPTY,ELMSYM,HASHTABLE,"mult_schur_elmsym(3)",c);

    NEW_HASHTABLE(d);
    erg += tse___faktor(a,d,cons_eins);
    erg += mult_elmsym_elmsym(d,b,c);
    FREEALL(d);
    ENDR("mult_schur_monomial");
}

