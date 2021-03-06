#include "def.h"
#include "macro.h"


INT tep___faktor();
INT pph___();
INT plet_elmsym_homsym(a,b,c) OP a,b,c;
/* AK 111201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"plet_elmsym_homsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,HOMSYM,"plet_elmsym_homsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,HOMSYM,"plet_elmsym_homsym(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    else if (S_O_K(c) == HOMSYM)
         { t=1; t_HOMSYM_HASHTABLE(c,c); }

    {
    /* via pph with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tep___faktor(a,f,cons_eins);
    erg += pph___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_HOMSYM(c,c);
    ENDR("plet_elmsym_homsym");
}


