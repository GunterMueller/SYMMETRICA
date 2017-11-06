#include "def.h"
#include "macro.h"

INT psm_ende()
{
    return OK;
}

INT psm___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"psm___(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"psm___(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"psm___(3)",c);

    NYI("psm___");
    ENDR("psm___");
}


INT tsp___faktor();
INT ppm___();

INT plet_schur_monomial(a,b,c) OP a,b,c;
/* AK 111201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_monomial(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"plet_schur_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_schur_monomial(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }

    {
    /* via ppm with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tsp___faktor(a,f,cons_eins);


    CTO(HASHTABLE,"plet_schur_monomial(i1)",f);
    erg += ppm___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("plet_schur_monomial");
}

INT plet_schur_monomial_new(a,b,c) OP a,b,c;
/* AK 111201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_monomial(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"plet_schur_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_schur_monomial(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
 
    erg += psm___(a,b,c,cons_eins);
 
    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("plet_schur_monomial");
}



