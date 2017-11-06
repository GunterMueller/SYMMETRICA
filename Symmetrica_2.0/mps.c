#include "def.h"
#include "macro.h"

INT mps_integer_partition_();
INT mxx_null__();
INT mps_hashtable__();

static OP mps_ip_d = NULL;
static INT mps_ip_l = 50;
INT mps_ende()
{
    INT erg = OK;
    if (mps_ip_d != NULL)
        {
        CTO(MONOM,"mps_ende(i1)",mps_ip_d);
        FREEALL(mps_ip_d);
        mps_ip_d = NULL;
        }
    ENDR("mps_ende");
}

INT mult_power_schur(a,b,c) OP a,b,c;
/* for compability */
    { return  mult_powsym_schur(a,b,c); }

INT mps_null__(b,c,f) OP b,c,f;
/* c = c + p_0 * s_b * f */
{
    INT erg = OK;
    
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mps_null__(1)",b);
    CTTO(SCHUR,HASHTABLE,"mps_null__(2)",c);
    erg += mxx_null__(b,c,f);
    ENDR("mps_null");
}

INT mps_integer__(a,b,c,f) OP a,b,c,f;
{   
    INT erg = OK;
    CTO(INTEGER,"mps_integer__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mps_integer__(2)",b);
    CTTO(SCHUR,HASHTABLE,"mps_integer__(3)",c);
    CTO(ANYTYPE,"mps_integer__(4)",f);
    SYMCHECK((S_I_I(a) < 0),"mps_integer__:parameter<0");

    if (S_I_I(a) == 0) 
        {
        erg += mps_null__(b,c,f);
        goto eee;
        }
    else if (S_O_K(b) == INTEGER) {
        OP ff;
        ff = CALLOCOBJECT();
        erg += first_partition(b,ff);
        erg += mps_integer_partition_(a,ff,c,f);
        FREEALL(ff);
        goto eee;
        }
    else if (S_O_K(b) == PARTITION) {
        erg += mps_integer_partition_(a,b,c,f);
        goto eee;
        }
    else /* SCHUR   HASHTABLE */ {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mps_integer_partition_);
        goto eee;
        }
eee:
    CTTO(SCHUR,HASHTABLE,"mps_integer__(e3)",c);
    ENDR("mps_integer__");
}

INT mps_partition__(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(PARTITION,"mps_partition__(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mps_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mps_partition__(3)",c);
    if (S_PA_LI(a) == 0) 
        {
        erg += mps_integer__(cons_null,b,c,f);
        }
    else if (S_PA_LI(a) == 1) 
        {
        erg += mps_integer__(S_PA_I(a,0),b,c,f);
        }
    else {

        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();
 
        erg += init_hashtable(e);
        erg += mps_integer__(S_PA_I(a,0),b,e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mps_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
        if (S_O_K(c) == SCHUR)
            INSERT_LIST(e,c,add_koeff,comp_monomschur);
        else
            INSERT_HASHTABLE(e,c,add_koeff,eq_monomsymfunc,hash_monompartition);

        }

    ENDR("mps_partition__");
}


INT mps_powsym__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(POWSYM,"mps_powsym__(1)",a);
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"mps_powsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mps_powsym__(3)",c);

    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mps_partition__);
 
    ENDR("mps_powsym__");
}

INT mps_hashtable__pre100102(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"mps_hashtable__(1)",a);
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"mps_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mps_hashtable__(3)",c);

    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mps_partition__);
    
    ENDR("mps_hashtable__");
}

INT mps___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"mps___(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mps___(2)",b);
    CTTO(SCHUR,HASHTABLE,"mps___(3)",c);

    if (S_O_K(a) == INTEGER)
        {
        erg += mps_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += mps_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == POWSYM)
        {
        erg += mps_powsym__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += mps_hashtable__(a,b,c,f);
        }
    ENDR("mps___");
}




INT mult_powsym_schur(a,b,c) OP a,b,c;
/* a is INTEGER, PARTITION  b is SCHUR c becomes SCHUR */
/* AK 200891 V1.3 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,POWSYM,"mult_powsym_schur(1)",a);
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mult_powsym_schur(2)",b);
    CTTTO(SCHUR,HASHTABLE,EMPTY,"mult_powsym_schur(3)",c);

    if (S_O_K(a) == INTEGER)
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_schur(c);
           else if (S_O_K(b) == INTEGER) init_schur(c);
           else { t=1; init_hashtable(c); }
           }
        }
    else if (S_O_K(c) == EMPTY)
        { t=1; init_hashtable(c); }

    mps___(a,b,c,cons_eins);
 
    if (t==1) t_HASHTABLE_SCHUR(c,c);


    CTTTO(SCHUR,HASHTABLE,EMPTY,"mult_powsym_schur(e3)",c);
    ENDR("mult_powsym_schur");
}


INT mps_integer_partition_(a,b,c,f) OP a,b,c; OP f;
/* a is INTEGER b is PARTITION c is SCHUR or HASHTABLE */
/* AK 200891 V1.3 */
/* called from mms_integer_partition() */
{
    OP d;
    INT i,j;
    INT erg=OK;

    EOP("mps_integer_partition_(4)",f);
 
    CTO(INTEGER,"mps_integer_partition_(1)",a);
    CTO(PARTITION,"mps_integer_partition_(2)",b);
    CTTO(HASHTABLE,SCHUR,"mps_integer_partition_(3)",c);
    CTO(ANYTYPE,"mps_integer_partition_(4)",f);
    SYMCHECK(S_I_I(a) < 0, "mps_integer_partition_:integer < 0");

 
 
    if (mps_ip_d == NULL)
        {
        d = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
        erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(d));
        erg += m_il_v(mps_ip_l,S_PA_S(S_MO_S(d)));
        C_O_K(S_PA_S(S_MO_S(d)),INTEGERVECTOR);
        mps_ip_d = d;
        }
   
    d = mps_ip_d;

    if (S_I_I(a)+S_PA_LI(b) > mps_ip_l) {
        M_I_I(mps_ip_l, S_PA_L(S_MO_S(d)));
        inc_vector_co(S_PA_S(S_MO_S(d)), S_I_I(a)+S_PA_LI(b)-mps_ip_l);
        mps_ip_l  = S_I_I(a)+S_PA_LI(b);
        }

    C_I_I( S_PA_L(S_MO_S(d)) , S_I_I(a)+S_PA_LI(b));

    for (i=(INT)0; i<S_I_I(a)+S_PA_LI(b); i++)
        {
        for (j=(INT)0;j<S_I_I(a);j++)
            M_I_I((INT)0,S_PA_I(S_MO_S(d),j));
        for (j=(INT)0;j<S_PA_LI(b);j++)
            M_I_I(S_PA_II(b,j),S_PA_I(S_MO_S(d),j+S_I_I(a)));
        /* now we have copied the partition with leading zeros */
        M_I_I(S_I_I(a)+S_PA_II(S_MO_S(d),i),S_PA_I(S_MO_S(d),i));

        j = reorder_vector_apply(S_PA_S(S_MO_S(d))); 
        if (j == 0) { continue; }
        else {
             if ((S_O_K(S_MO_K(d)) == BRUCH) && (S_O_K(f) == BRUCH) )
                 {
                 FREESELF(S_B_O(S_MO_K(d)));
                 FREESELF(S_B_U(S_MO_K(d)));
                 COPY(S_B_U(f),S_B_U(S_MO_K(d)));
                 if (j==1)
                     COPY(S_B_O(f),S_B_O(S_MO_K(d)));
                 else
                     ADDINVERS(S_B_O(f),S_B_O(S_MO_K(d)));
                 }
             else {
                 FREESELF(S_MO_K(d));
                 if (j==1)
                     COPY(f,S_MO_K(d));
                 else
                     ADDINVERS(f,S_MO_K(d));
                 }
           
             if (S_O_K(c) == SCHUR)
                 {
                 OP dd;
                 dd = CALLOCOBJECT();
                 copy_monom(d,dd);
                 INSERT_LIST(dd,c,add_koeff,comp_monomschur);
                 }
             else
                 {
                 HASH_INTEGERVECTOR(S_PA_S(S_MO_S(d)),j);
                 C_PA_HASH(S_MO_S(d),j);
                 add_apply_hashtable(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
                 }
             }

        C_I_I(S_PA_L(S_MO_S(d)), S_I_I(a)+S_PA_LI(b));
        }


    CTTO(HASHTABLE,SCHUR,"mps_integer_partition_(e3)",c);
    ENDR("mps_integer_partition_");
}


INT mps_hashtable__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    INT w;
    CTO(HASHTABLE,"mps_hashtable__(1)",a);
    CTTTTO(HASHTABLE,INTEGER,PARTITION,SCHUR,"mps_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mps_hashtable__(3)",c);

    w = WEIGHT_HASHTABLE(a);
    if (w == 0) goto ende;
    if (w == 1) {
        M_FORALL_MONOMIALS_IN_A(a,b,c,f,mps_partition__);
        goto ende;
        }

    {
    OP z=NULL,zz=NULL;
    OP v;
    OP h1,h2,h3;
    INT m;
    INT h2s, h3s;
    v = CALLOCOBJECT();
    z = findmax_powsym(a,maxpart_comp_part);
    if (S_PA_LI(S_MO_S(z)) == 0) {
        SYMCHECK(w != 1, "mps_hashtable__(i2)"); 
        FREESELF(v);
        MULT(S_MO_K(z),f,v);
        erg += mxx_null__(b,c,v);
        FREEALL(v);
        goto ende;
        }

    m = 100000;
    FORALL(z,a,{if (S_PA_II(S_MO_S(z),0) < m) m = S_PA_II(S_MO_S(z),0); });
    zz = CALLOCOBJECT(); M_I_I(m,zz);

    CTO(INTEGER,"mps_hashtable__(i2)",zz);
    NEW_HASHTABLE(h1);
    mps_integer__(zz,b,h1,cons_eins);
    CTO(HASHTABLE,"mps_hashtable__(h1)",h1);
    NEW_HASHTABLE(h2);
    NEW_HASHTABLE(h3);
    /* h2 partitionen ohne zz */
    /* h3 partitionen wo zz gestrichen */
    h2s = h3s = 0;
    FORALL(z,a,{
         if (S_PA_II(S_MO_S(z),0) != m) {
             OP h;
             h = CALLOCOBJECT();
             SWAP(z,h); 
             insert_scalar_hashtable(h,h2,add_koeff,eq_monomsymfunc,hash_monompartition);
             h2s++;
             DEC_INTEGER(S_V_I(a,S_V_LI(a)));
             }
         else {
             OP h;
             h = CALLOCOBJECT();
             b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),h);
             COPY(S_MO_K(z),S_MO_K(h));
             remove_part_integer(S_MO_S(z),zz,S_MO_S(h));
             if (S_PA_LI(S_MO_S(h)) == 0) {
                 FREESELF(h);
                 MULT(S_MO_K(z),f,h);
                 erg += mxx_null__(h1,c,h);
                 FREEALL(h);
                 }
             else {
                 C_PA_HASH(S_MO_S(h),-1);
                 insert_scalar_hashtable(h,h3,add_koeff,eq_monomsymfunc,hash_monompartition);
                 h3s++;
                 }
             }
               } );
    CTO(HASHTABLE,"mps_hashtable__(i3)",h2);
    CTO(HASHTABLE,"mps_hashtable__(i4)",h3);
    if (h3s) mps_hashtable__(h3,h1,c,f);
    if (h2s) mps_hashtable__(h2,b,c,f);

    insert_hashtable_hashtable(h2,a,NULL,eq_monomsymfunc,hash_monompartition);

    

    FREEALL(h1);
    FREEALL(h3);
    FREEALL(v);
    FREEALL(zz);
    }
ende:
    CTTO(HASHTABLE,SCHUR,"mps_hashtable__(e3)",c);
    ENDR("mps_hashtable__");
}

