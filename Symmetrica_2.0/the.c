#include "def.h"
#include "macro.h"
OP find_teh_integer();

INT the_integer__faktor( a,b,f) OP a,b,f;
{
    return teh_integer__faktor(a,b,f);
}

OP find_the_integer(a) OP a;
{
    return find_teh_integer(a);
}
 
INT t_HOMSYM_ELMSYM(a,b) OP a,b;
/* AK 231192 */
{
    INT erg = OK;
    INT s=0;
    OP z;
    CTTTTO(HASHTABLE,HOMSYM,INTEGER,PARTITION,"t_HOMSYM_ELMSYM(1)",a);
    TCE2(a,b,t_HOMSYM_ELMSYM,ELMSYM);
    
    if (S_O_K(a) == HOMSYM) {
        z = a;
        while(z!=NULL) { C_O_K(z,ELMSYM); z = S_S_N(z); }
        s = 1;
        }
    if (S_O_K(b) == ELMSYM) {
        z = b;
        while(z!=NULL) { C_O_K(z,HOMSYM); z = S_S_N(z); }
        }

    erg += t_ELMSYM_HOMSYM(a,b);

    if (S_O_K(b) == HOMSYM) {
        z = b;
        while(z!=NULL) { C_O_K(z,ELMSYM); z = S_S_N(z); }
        }
    if (s == 1) {
        z = a;
        while(z!=NULL) { C_O_K(z,HOMSYM); z = S_S_N(z); }
        }
    ENDR("t_HOMSYM_ELMSYM");
}
 

