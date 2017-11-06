#include "def.h"
#include "macro.h"

INT plet_elmsym_schur(a,b,c) OP a,b,c;
/* AK 051201 */
{
    INT erg = OK;
#ifdef PLETTRUE
    INT t=0; /* is 1 if transfer HASHTABLE->SCHUR necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"plet_elmsym_schur(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"plet_elmsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"plet_elmsym_schur(3)",c);

    if (S_O_K(c) == EMPTY) 
        { t=1; init_hashtable(c); }

    pes___(a,b,c,cons_eins);
    if (t==1) t_HASHTABLE_SCHUR(c,c);
#endif
    ENDR("plet_elmsym_schur");
}
INT pes_ende()
{
    return OK;
}

#ifdef PLETTRUE
INT m_merge_partition_partition();
INT pes_integer_partition_();
INT pes_integer_hashtable_();
INT pes___();

INT pes_null__(b,c,f) OP b,c,f;
{
    INT mxx_null__();
    return mxx_null__(b,c,f);
}
 
INT pes_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"pes_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,SCHUR,"pes_integer_hashtable_(2)",b);
    CTTO(SCHUR,HASHTABLE,"pes_integer_hashtable_(3)",c);
    NYI("pes_integer_hashtable_");
 
    ENDR("pes_integer_hashtable_");
}


INT pes_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 051201 */
{
    INT erg = OK;

    CTO(INTEGER,"pes_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pes_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pes_integer__(3)",c);

    if (S_O_K(b) == PARTITION)
        erg += pes_integer_partition_(a,b,c,f);
    else if (S_O_K(b) == SCHUR)
        {
        INT mss_hashtable_hashtable_();
        INT p_schursum();
        if (S_S_N(b) == NULL)
            erg += pes_integer_partition_(a,S_S_S(b),c,f);
        else
            erg += p_schursum(a,b,c,f,NULL,pes_integer__,mss_hashtable_hashtable_);
        }
    else
        {
        erg += pes_integer_hashtable_(a,b,c,f);
        }


    
    ENDR("pes_integer__");
}

INT mpp_hashtable_hashtable_();
INT pes_null_partition_();
INT pes_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"pes_partition__(1)",a);
    CTTTO(HASHTABLE,SCHUR,PARTITION,"pes_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pes_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += pes_null_partition_(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += pes_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else{
        INT mss_hashtable_hashtable_();
        INT p_splitpart();
        erg += p_splitpart(a,b,c,f,pes_partition__,
                                   mss_hashtable_hashtable_);
        goto ende;
        }
    
ende:
    ENDR("pes_partition__");
}



INT pes_elmsym__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(ELMSYM,"pes_elmsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pes_elmsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pes_elmsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pes_partition__);
    ENDR("pes_elmsym__");
}

INT pes_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += p_a [p_b]  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"pes_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pes_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"pes_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,pes_partition__);
    ENDR("pes_hashtable__");
}


INT pes_null_partition_(b,c,f) OP b,c,f;
/* AK 061201 */
{
    INT erg = OK;
    CTO(PARTITION,"pes_null_partition(1)",b);
    CTTO(SCHUR,HASHTABLE,"pes_null_partition(2)",c);
    _NULL_PARTITION_(b,c,f);
    ENDR("pes_null_partition");
}

INT pes_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    INT cc_plet_pes_integer_partition();

    CTO(INTEGER,"pes_integer_partition_(1)",a);
    CTO(PARTITION,"pes_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"pes_integer_partition_(3)",c);
    SYMCHECK ((S_I_I(a) < 0),"pes_integer_partition_:integer<0");

    if (S_I_I(a) == 0) {
        erg += pes_null_partition_(b,c,f);
        goto ende;
        }

    erg += cc_plet_pes_integer_partition(a,b,c,f);   

ende:
    ENDR("pes_integer_partition_");
}



INT pes___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"pes___(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"pes___(2)",b);
    CTTO(HASHTABLE,SCHUR,"pes___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += pes_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += pes_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == ELMSYM)
        {
        erg += pes_elmsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += pes_hashtable__(a,b,c,f);
        }
 
    ENDR("pes___");
}
#endif /* PLETTRUE */
