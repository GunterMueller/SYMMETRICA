

#include "def.h"
#include "macro.h"

INT pph_ende()
{
    return OK;
}

INT m_merge_partition_partition();
INT pph_integer_partition_();
INT pph_integer_hashtable_();
INT pph_integer_integer_();
INT pph___();
INT tsp___faktor();
INT ppp___();
INT tep___faktor();
INT thp___faktor();
INT tmp___faktor();

INT pph_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}

INT pph_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"pph_integer__(1)",a);
    CTTTTO(HASHTABLE,PARTITION,HOMSYM,INTEGER,"pph_integer__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"pph_integer__(3)",c);

    if (S_O_K(b) == PARTITION)
        erg += pph_integer_partition_(a,b,c,f);
    else if (S_O_K(b) == INTEGER)
        erg += pph_integer_integer_(a,b,c,f);
    else
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,pph_integer_partition_);

    
    ENDR("pph_integer__");
}

INT mpp_hashtable_hashtable_();
INT pph_null_partition_();
INT pph_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"pph_partition__(1)",a);
    CTTTTO(HASHTABLE,HOMSYM,PARTITION,INTEGER,"pph_partition__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"pph_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += pph_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += pph_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        INT mhh_hashtable_hashtable_();
        INT p_splitpart();
        erg += p_splitpart(a,b,c,f,pph_partition__,
                                   mhh_hashtable_hashtable_);
        }
    ENDR("pph_partition__");
}



INT pph_powsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(POWSYM,"pph_powsym__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,HOMSYM,"pph_powsym__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"pph_powsym__(3)",c);

    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pph_partition__);

    ENDR("pph_powsym__");
}

INT pph_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pph_hashtable__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,HOMSYM,"pph_hashtable__(2)",b);
    CTTO(HASHTABLE,HOMSYM,"pph_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pph_partition__);

    ENDR("pph_hashtable__");
}

INT pph_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pph_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"pph_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,HOMSYM,"pph_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,pph_partition__);

    ENDR("pph_hashtable_hashtable_");
}

INT pph_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"pph_null_partition(1)",b);
    CTTO(HOMSYM,HASHTABLE,"pph_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("pph_null_partition");
}

INT pph_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"pph_integer_partition_(1)",a);
    CTO(PARTITION,"pph_integer_partition_(2)",b);
    CTO(HASHTABLE,"pph_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"pph_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += pph_null_partition_(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 0) {
        erg += pph_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 1) {
        erg += pph_integer_integer_(a,S_PA_I(b,0),c,f);
        goto ende;
        }
    else
        {
        INT mhh_hashtable_hashtable_();
        INT p_splitpart2();
        erg += p_splitpart2(a,b,c,f,pph_integer_partition_,
                                   mhh_hashtable_hashtable_);
        goto ende;
        }

ende:
    ENDR("pph_integer_partition_");
}

INT pph_integer_integer_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    INT ppe_integer_integer_();
 
    CTO(INTEGER,"pph_integer_integer_(1)",a);
    CTO(INTEGER,"pph_integer_integer_(2)",b);
    CTO(HASHTABLE,"pph_integer_integer_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"pph_integer_integer_:integer<0");
 
    if (S_I_I(a) == 0) {
        erg += pph_null__(b,c,f);
        goto ende;
        }
 
    if (S_I_I(a) % 2 == 1)
        {
        erg += ppe_integer_integer_(a,b,c,f);
        goto ende;
        }
    else if (S_I_I(b) % 2 == 0)
        {
        erg += ppe_integer_integer_(a,b,c,f);
        goto ende;
        }
    else
        {
        OP ff;
        ff = CALLOCOBJECT();
        ADDINVERS(f,ff);
        erg += ppe_integer_integer_(a,b,c,ff);
        FREEALL(ff);
        goto ende;
        }
ende:
    CTO(HASHTABLE,"pph_integer_integer_(3-ende)",c);
    ENDR("pph_integer_integer_");
}


INT pph_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"pph_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,HOMSYM,"pph_integer_hashtable_(2)",b);
    CTTO(POWSYM,HASHTABLE,"integer_hashtable_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"pph_integer_hashtable_:integer<0");

    if (S_I_I(a) == 0) {
        erg += pph_null__(b,c,f);
        goto ende;
        }

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,pph_integer_partition_);
    
ende:
    ENDR("pph_integer_hashtable_");
}




INT pph___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"pph___(1)",a);
    CTTTTO(HASHTABLE,PARTITION,HOMSYM,INTEGER,"pph___(2)",b);
    CTO(HASHTABLE,"pph___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += pph_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += pph_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += pph_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += pph_hashtable__(a,b,c,f);
        }
 
    ENDR("pph___");
}

INT plet_powsym_homsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"plet_powsym_homsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,HOMSYM,"plet_powsym_homsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,HOMSYM,"plet_powsym_homsym(3)",c);
 

    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }
    else if (S_O_K(c) == HOMSYM)
         { t=1; t_HOMSYM_HASHTABLE(c,c); }
    pph___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_HOMSYM(c,c);
    ENDR("plet_powsym_homsym");
}



INT plet_schur_powsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"plet_schur_powsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,POWSYM,"plet_schur_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"plet_schur_powsym(3)",c);


    if (S_O_K(c) == EMPTY) {
         t=1; init_hashtable(c); }
/*
    pph___(a,b,c,cons_eins);
*/
    {
    /* via ppp with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tsp___faktor(a,f,cons_eins);
    erg += ppp___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_POWSYM(c,c);

    ENDR("plet_schur_powsym");
}

/* elmsym plethysm */


INT plet_elmsym_powsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"plet_elmsym_powsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,POWSYM,"plet_elmsym_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"plet_elmsym_powsym(3)",c);


    if (S_O_K(c) == EMPTY) {
         t=1; init_hashtable(c); }
/*
    pph___(a,b,c,cons_eins);
*/
    {
    /* via ppp with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tep___faktor(a,f,cons_eins);
    erg += ppp___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_POWSYM(c,c);

    ENDR("plet_elmsym_powsym");
}

/* homsym plethysm */



INT plet_homsym_powsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"plet_homsym_powsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,POWSYM,"plet_homsym_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"plet_homsym_powsym(3)",c);


    if (S_O_K(c) == EMPTY) {
         t=1; init_hashtable(c); }
/*
    pph___(a,b,c,cons_eins);
*/
    {
    /* via ppp with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += thp___faktor(a,f,cons_eins);
    erg += ppp___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_POWSYM(c,c);

    ENDR("plet_homsym_powsym");
}

/* monomial plethysm */
INT plet_monomial_schur(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,MONOMIAL,"plet_monomial_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"plet_monomial_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_monomial_schur(3)",c);

    {
    /* via ppp with change of basis */
    OP d,e,f;
    NEW_HASHTABLE(d);
    NEW_HASHTABLE(e);
    NEW_HASHTABLE(f);

    erg += tmp___faktor(a,f,cons_eins);
    erg += tsp___faktor(b,d,cons_eins);
    erg += ppp___(f,d,e,cons_eins);

    FREEALL(d);
    FREEALL(f);
    erg += t_POWSYM_SCHUR(e,c);
    CTO(HASHTABLE,"plet_monomial_schur(ie)",e);
    FREEALL(e);
    }

    CTTO(HASHTABLE,SCHUR,"plet_monomial_schur(e3)",c);
    ENDR("plet_monomial_schur");
}

INT plet_monomial_monomial(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,MONOMIAL,"plet_monomial_monomial(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"plet_monomial_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_monomial_monomial(3)",c);

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
    erg += tmp___faktor(a,f,cons_eins);
    erg += tmp___faktor(b,d,cons_eins);
    erg += ppp___(f,d,e,cons_eins);
    FREEALL(d);
    FREEALL(f);
    erg += t_POWSYM_MONOMIAL(e,c);
    FREEALL(e);
    }
/*
    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
*/
    ENDR("plet_monomial_monomial");
}


INT plet_monomial_powsym(a,b,c) OP a,b,c;
/* AK 061201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,MONOMIAL,"plet_monomial_powsym(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,POWSYM,"plet_monomial_powsym(2)",b);
    CTTTO(EMPTY,HASHTABLE,POWSYM,"plet_monomial_powsym(3)",c);


    if (S_O_K(c) == EMPTY) {
         t=1; init_hashtable(c); }
/*
    pph___(a,b,c,cons_eins);
*/
    {
    /* via ppp with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += tmp___faktor(a,f,cons_eins);
    erg += ppp___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_POWSYM(c,c);

    ENDR("plet_monomial_powsym");
}
