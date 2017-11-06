#include "def.h"
#include "macro.h"

INT t_HOMSYM_SCHUR(a,b) OP a,b;
/* AK 121001 */
/* faster using newmultiplication
   h_n \times S_I = \sum c_n,I,J S_J
*/
{
    INT erg = OK;
    OP m;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"t_HOMSYM_SCHUR",a);
    TCE2(a,b,t_HOMSYM_SCHUR,SCHUR);
   
    m=CALLOCOBJECT();
    erg += first_partition(cons_null,m);
    erg += m_pa_s(m,m);
    erg += mult_homsym_schur(a,m,b);
    FREEALL(m);
    CTTO(HASHTABLE,SCHUR,"t_HOMSYM_SCHUR(e2)",b);
    ENDR("t_HOMSYM_SCHUR");
}

