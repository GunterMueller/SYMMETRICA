#include "def.h"
#include "macro.h"

INT tsp___faktor();
INT tep___faktor();
INT ppp___();

INT plet_schur_elmsym_pre101201(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_elmsym_pre101201(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"plet_schur_elmsym_pre101201(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"plet_schur_elmsym_pre101201(3)",c);
 
/*
    if (S_O_K(c) == EMPTY)
         t=1; init_hashtable(c); }
    pph___(a,b,c,cons_eins);
*/
    {
    /* via ppp with change of basis */
    OP d = CALLOCOBJECT();
    OP e = CALLOCOBJECT();
    OP f = CALLOCOBJECT();
    erg += init_hashtable(e);
    erg += init_hashtable(d);
    erg += init_hashtable(f);
    erg += tsp___faktor(a,f,cons_eins);
    erg += tep___faktor(b,d,cons_eins);
    erg += ppp___(f,d,e,cons_eins);
    FREEALL(d);
    FREEALL(f);
    erg += t_POWSYM_ELMSYM(e,c);
    FREEALL(e);
    }
/*
    if (t==1) t_HASHTABLE_ELMSYM(c,c);
*/
    ENDR("plet_schur_elmsym_pre101201");
}

INT ppe___();
INT plet_schur_elmsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_elmsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,ELMSYM,"plet_schur_elmsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"plet_schur_elmsym(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
/*
    pse___(a,b,c,cons_eins);
*/
    {
    /* via ppe with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tsp___faktor(a,f,cons_eins);
    erg += ppe___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_ELMSYM(c,c);
    ENDR("plet_schur_elmsym");
}


