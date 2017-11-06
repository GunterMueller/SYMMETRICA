#include "def.h"
#include "macro.h"


INT tep___faktor();
INT ppm___();

INT plet_elmsym_monomial(a,b,c) OP a,b,c;
/* AK 111201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"plet_elmsym_monomial(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"plet_elmsym_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_elmsym_monomial(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }

    {
    /* via ppm with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tep___faktor(a,f,cons_eins);
    erg += ppm___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("plet_elmsym_monomial");
}


