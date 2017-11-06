

#include "def.h"
#include "macro.h"

INT ppe_ende()
{
    INT erg = OK;
    ENDR("ppe_ende");
}

INT m_merge_partition_partition();
INT ppe_integer_partition_();
INT ppe_integer_hashtable_();
INT ppe___();
INT ppe_null__(b,c,f) OP b,c,f;
{
    return mxx_null__(b,c,f);
}

INT ppe_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"ppe_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"ppe_integer__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"ppe_integer__:integer < 0");
    if (S_I_I(a) == 0) 
        erg += ppe_null__(b,c,f);
    

    if (S_O_K(b) == PARTITION)
        erg += ppe_integer_partition_(a,b,c,f);
    else
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,ppe_integer_partition_);

    
    ENDR("ppe_integer__");
}

INT mee_hashtable_hashtable_();
INT ppe_null_partition_();

INT ppe_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"ppe_partition__(1)",a);
    CTTTO(HASHTABLE,ELMSYM,PARTITION,"ppe_partition__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += ppe_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += ppe_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        erg += p_splitpart(a,b,c,f,ppe_partition__,
                                   mee_hashtable_hashtable_);
        }
    
    ENDR("ppe_partition__");
}



INT ppe_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"ppe_powsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"ppe_powsym__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe_powsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppe_partition__);
    ENDR("ppe_powsym__");
}

INT ppe_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppe_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,ELMSYM,"ppe_hashtable__(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,ppe_partition__);
    ENDR("ppe_hashtable__");
}

INT ppe_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"ppe_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"ppe_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe_hashtable_hashtable_(3)",c);
    NYI("ppe_hashtable_hashtable_");
    ENDR("ppe_hashtable_hashtable_");
}

INT ppe_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"ppe_null_partition(1)",b);
    CTTO(ELMSYM,HASHTABLE,"ppe_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("ppe_null_partition");
}

INT ppe_integer_integer_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    OP m;
    INT i;
 
    CTO(INTEGER,"ppe_integer_integer_(1)",a);
    CTO(INTEGER,"ppe_integer_integer_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"ppe_integer_integer_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"ppe_integer_integer_:integer(1)<0");
    SYMCHECK ((S_I_I(b) < 0),"ppe_integer_integer_:integer(2)<0");
 
    if (S_I_I(a) == 0) {
        erg += ppe_null__(b,c,f);
        goto ende;
        }
    m = CALLOCOBJECT();
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),m);
    erg += m_il_v(S_I_I(b),S_PA_S(m));
    C_O_K(S_PA_S(m),INTEGERVECTOR);
 
    for (i=0;i<S_I_I(b);i++)
        M_I_I(S_I_I(a),S_PA_I(m,i));
 
    tme_partition__faktor(m,c,f);
 
    FREEALL(m);

ende:
    CTTO(ELMSYM,HASHTABLE,"ppe_integer_integer_(3-ende)",c);
    ENDR("ppe_integer_integer_");
}

INT ppe_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    OP m;
    INT i;

    CTO(INTEGER,"ppe_integer_partition_(1)",a);
    CTO(PARTITION,"ppe_integer_partition_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"ppe_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"ppe_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += ppe_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 0) {
        erg += ppe_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 1) {
        erg += ppe_integer_integer_(a,S_PA_I(b,0),c,f);
        goto ende;
        }
    else
        erg += p_splitpart2(a,b,c,f,ppe_integer_partition_,
                                   mee_hashtable_hashtable_);

    

ende:
    CTTO(ELMSYM,HASHTABLE,"ppe_integer_partition_(3-ende)",c);
    ENDR("ppe_integer_partition_");
}

INT ppe_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"ppe_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,ELMSYM,"ppe_integer_hashtable_(2)",b);
    CTTO(ELMSYM,HASHTABLE,"integer_hashtable_(3)",c);

    NYI("ppe_integer_hashtable_");
    
    ENDR("ppe_integer_hashtable_");
}



INT plet_powsym_elmsym(a,b,c) OP a,b,c;
/* AK 051201
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->ELMSYM necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_elmsym(1)",a);
    CTTTTO(HASHTABLE,PARTITION,ELMSYM,INTEGER,"plet_powsym_elmsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,ELMSYM,"plet_powsym_elmsym(3)",c);

    if (S_O_K(c) == EMPTY) 
        if (S_O_K(a) == INTEGER) init_elmsym(c);
        else { t=1; init_hashtable(c); }

    ppe___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_ELMSYM(c,c);
    ENDR("plet_powsym_elmsym");
}

INT ppe___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"ppe___(1)",a);
    CTTTTO(HASHTABLE,PARTITION,ELMSYM,INTEGER,"ppe___(2)",b);
    CTTO(HASHTABLE,ELMSYM,"ppe___(3)",c);
    if (S_O_K(b) == INTEGER)
        {
        OP d;
        d = CALLOCOBJECT();
        erg += m_i_pa(b,d);
        erg += ppe___(a,d,c,f);
        FREEALL(d);
        }
    else if (S_O_K(a) == INTEGER)
        {
        erg += ppe_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += ppe_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += ppe_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += ppe_hashtable__(a,b,c,f);
        }
 
    ENDR("ppe___");
}

