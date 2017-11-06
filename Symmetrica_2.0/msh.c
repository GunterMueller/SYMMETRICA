#include "def.h"
#include "macro.h"
INT mult_schur_homsym(a,b,c) OP a,b,c;
/* AK 081001 */
{
    OP d;
    INT erg = OK;
    CTTTO(HASHTABLE,SCHUR,PARTITION,"mult_schur_homsym",a);
    CTTTO(HASHTABLE,HOMSYM,PARTITION,"mult_schur_homsym",b);
    CTTTO(HOMSYM,HASHTABLE,EMPTY,"mult_schur_homsym",c);

    d = CALLOCOBJECT();
    erg += t_SCHUR_HOMSYM(a,d);
    erg += mult_homsym_homsym(d,b,c);
    FREEALL(d);
    ENDR("mult_schur_homsym");
}

