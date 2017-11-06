#include "def.h"
#include "macro.h"

INT tep___faktor();
INT ppe___();
INT plet_elmsym_elmsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"plet_elmsym_elmsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"plet_elmsym_elmsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"plet_elmsym_elmsym(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    {
    /* via ppe with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tep___faktor(a,f,cons_eins);
    erg += ppe___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_ELMSYM(c,c);
    ENDR("plet_elmsym_elmsym");
}


