
#include "def.h"
#include "macro.h"


INT plet_homsym_monomial(a,b,c) OP a,b,c;
/* AK 051201 */
{
    INT erg = OK;
#ifdef PLETTRUE
    INT t=0; /* is 1 if transfer HASHTABLE->MONOMIAL necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"plet_homsym_monomial(1)",a);
    CTTTTO(HASHTABLE,PARTITION,MONOMIAL,INTEGER,"plet_homsym_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_homsym_monomial(3)",c);

    if (S_O_K(c) == EMPTY) 
        if (S_O_K(a) == INTEGER) init_monomial(c);
        else { t=1; init_hashtable(c); }

    phm___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
#endif
    ENDR("plet_homsym_monomial");
}
INT phm_ende()
{
    INT erg = OK;
    return erg;
}

#ifdef PLETTRUE
INT phm_integer_partition_();
INT phm_integer_hashtable_();
INT phm_integer_integer_();
INT phm___();
INT phm_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}

INT phm_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"phm_integer__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"phm_integer__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"phm_integer__:integer < 0");
    if (S_I_I(a) == 0) 
        erg += phm_null__(b,c,f);
    

    if (S_O_K(b) == PARTITION)
        erg += phm_integer_partition_(a,b,c,f);
    else if (S_O_K(b) == INTEGER)
        erg += phm_integer_integer_(a,b,c,f);
    else
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,phm_integer_partition_);

    
    ENDR("phm_integer__");
}

INT phm_null_partition_();

INT phm_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"phm_partition__(1)",a);
    CTTTO(HASHTABLE,MONOMIAL,PARTITION,"phm_partition__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += phm_null__(b,c,f);
        }
    else if (S_PA_LI(a) == 1) {
        erg += phm_integer__(S_PA_I(a,0),b,c,f);
        }
    else{
        INT mmm_hashtable_hashtable_();
        INT p_splitpart();
        erg += p_splitpart(a,b,c,f,phm_partition__,
                                   mmm_hashtable_hashtable_);
        }
    
    ENDR("phm_partition__");
}



INT phm_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HOMSYM,"phm_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"phm_homsym__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm_homsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,phm_partition__);
    ENDR("phm_homsym__");
}

INT phm_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"phm_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"phm_hashtable__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,phm_partition__);
    ENDR("phm_hashtable__");
}

INT phm_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"phm_hashtable_hashtable_(1)",a);
    CTO(HASHTABLE,"phm_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm_hashtable_hashtable_(3)",c);
    NYI("phm_hashtable_hashtable_");
    ENDR("phm_hashtable_hashtable_");
}

INT phm_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"phm_null_partition(1)",b);
    CTTO(MONOMIAL,HASHTABLE,"phm_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("phm_null_partition");
}

INT phm_integer_integer_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
 
    CTO(INTEGER,"phm_integer_integer_(1)",a);
    CTO(INTEGER,"phm_integer_integer_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"phm_integer_integer_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"phm_integer_integer_:integer(1)<0");
    SYMCHECK ((S_I_I(b) < 0),"phm_integer_integer_:integer(2)<0");
 
    if (S_I_I(a) == 0) {
        erg += phm_null__(b,c,f);
        goto ende;
        }
    else {
        OP z,m = CALLOCOBJECT();
        INT i;
        INT thm_integer__faktor();

        init_hashtable(m);
        thm_integer__faktor(a,m,f);        
        FORALL(z,m,{
            OP mm;
            for (i=0;i<S_PA_LI(S_MO_S(z));i++)
                M_I_I((S_I_I(b) * S_PA_II(S_MO_S(z),i)), S_PA_I(S_MO_S(z),i));
            mm=CALLOCOBJECT();
            SWAP(z,mm);
            if (S_O_K(c) == HASHTABLE)
                {
                C_PA_HASH(S_MO_S(mm),-1);
                insert_hashtable(mm,c,add_koeff,eq_monomsymfunc,hash_monompartition);
                }
            else
                insert_list(mm,c,add_koeff,comp_monommonomial);
            });
         
        FREEALL(m);
        goto ende;
        }


ende:
    CTTO(MONOMIAL,HASHTABLE,"phm_integer_integer_(3-ende)",c);
    ENDR("phm_integer_integer_");
}

INT phm_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"phm_integer_partition_(1)",a);
    CTO(PARTITION,"phm_integer_partition_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"phm_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"phm_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += phm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 0) {
        erg += phm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 1) {
        erg += phm_integer_integer_(a,S_PA_I(b,0),c,f);
        goto ende;
        }
    else {
        INT ak_plet_phm_integer_partition_();
        ak_plet_phm_integer_partition_(a,b,c,f);
        goto ende;
        }

    

ende:
    CTTO(MONOMIAL,HASHTABLE,"phm_integer_partition_(3-ende)",c);
    ENDR("phm_integer_partition_");
}

INT phm_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"phm_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"phm_integer_hashtable_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,phm_integer_partition_);
    
    ENDR("phm_integer_hashtable_");
}




INT phm___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"phm___(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"phm___(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"phm___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += phm_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += phm_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == HOMSYM)
        {
        erg += phm_homsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += phm_hashtable__(a,b,c,f);
        }
 
    ENDR("phm___");
}


INT thp___faktor();
INT ppm___();

INT plet_homsym_monomial_via_ppm(a,b,c) OP a,b,c;
/* AK 111201
*/
{
    INT t=0,erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"plet_homsym_monomial(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,MONOMIAL,"plet_homsym_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"plet_homsym_monomial(3)",c);
 
    if (S_O_K(c) == EMPTY)
         { t=1; init_hashtable(c); }

    {
    /* via phm with change of basis */
    OP f = CALLOCOBJECT();
    erg += init_hashtable(f);
    erg += thp___faktor(a,f,cons_eins);
    erg += ppm___(f,b,c,cons_eins);
    FREEALL(f);
    }

    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("plet_homsym_monomial");
}

#endif /* PLETTRUE */
