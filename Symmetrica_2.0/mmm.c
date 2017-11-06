#include "def.h"
#include "macro.h"

INT mmm_integer_partition_();
INT mmm_partition_partition_();
INT mmm_integer_hashtable_();
INT mmm_null_partition_();
INT mmm___();
static INT verf2();
static INT coeff_mmm();


INT mmm_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;

    CTO(INTEGER,"mmm_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm_integer__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_integer__(3)",c);

    if (S_O_K(b) == PARTITION) 
        erg += mmm_integer_partition_(a,b,c,f);
    else 
        erg += mmm_integer_hashtable_(a,b,c,f);
    ENDR("mmm_integer__");
}

INT mmm_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mmm_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm_partition__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_partition__(3)",c);

    if (S_O_K(b) == PARTITION)
        {
        erg += mmm_partition_partition_(a,b,c,f);
        goto ende;
        }
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mmm_partition_partition_);
        goto ende;
        }

ende:
    ENDR("mmm_partition__");
}

INT mmm_monomial__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(MONOMIAL,"mmm_monomial__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm_monomial__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_monomial__(3)",c);
 
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mmm_partition__);   

    ENDR("mmm_monomial__");
}

INT mmm_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += m_a \times m_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mmm_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm_hashtable__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_hashtable__(3)",c);

    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mmm_partition__);   

    ENDR("mmm_hashtable__");
}

INT mmm_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 051201 */
/* c += m_a \times m_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mmm_hashtable_hashtable_(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_hashtable_hashtable_(3)",c);
 
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mmm_partition_partition_);
 
    ENDR("mmm_hashtable_hashtable_");
}


INT mmm_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    OP m;
    INT i,k;

    CTO(INTEGER,"mmm_integer_partition_(1)",a);
    CTO(PARTITION,"mmm_integer_partition_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"mmm_integer_partition_(3)",c);
    SYMCHECK((S_I_I(a) < 0), "mmm_integer_partition_:integer < 0");
    if (S_I_I(a) == 0) {
        erg += mmm_null_partition_(b,c,f);
        goto eee;
        }

    
    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
    erg += m_il_v(S_PA_LI(b)+1,S_PA_S(S_MO_S(m)));
    C_O_K(S_PA_S(S_MO_S(m)),INTEGERVECTOR);

    for (i=0,k=0; k<S_PA_LI(S_MO_S(m)); k++,i++)
        if (k == S_PA_LI(b))
            M_I_I(S_I_I(a), S_PA_I(S_MO_S(m),k) );
        else if (S_PA_II(b,i) < S_I_I(a))  
            M_I_I(S_PA_II(b,i), S_PA_I(S_MO_S(m),k) );
        else 
            {
            M_I_I(S_I_I(a), S_PA_I(S_MO_S(m),k) );
            break;
            }

    for (k++;k<S_PA_LI(S_MO_S(m)); k++,i++)
        M_I_I(S_PA_II(b,i), S_PA_I(S_MO_S(m),k) );

    COPY(f, S_MO_K(m));
    if (S_O_K(c) == MONOMIAL)
        INSERT_LIST(m,c,add_koeff,comp_monommonomial);
    else
        insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);

eee:
    ENDR("mmm_integer_partition_");
}

INT mmm_integer_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
 
    CTO(INTEGER,"mmm_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"mmm_integer_hashtable_(2)",b);
    CTTO(MONOMIAL,HASHTABLE,"integer_hashtable_(3)",c);

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mmm_integer_partition_);
    
    ENDR("mmm_integer_hashtable_");
}

OP mmm_ce = NULL;
INT mmm_ende()
{
    INT erg = OK;
    if (mmm_ce != NULL)
        {
        FREEALL(mmm_ce);
        mmm_ce = NULL;
        }
    ENDR("mmm_ende");
}

INT mmm_null_partition_(b,c,f) OP b,c,f;
/* AK 051201 */
{
    INT erg = OK;
    _NULL_PARTITION_(b,c,f);
    ENDR("mmm_null_partition");
}

INT mmm_partition_partition_(a,b,c,f) OP a,b,c; OP f;
/* AK 091101 */
/* mit der routine verf2 werden alle partitionen im ergebnis geliefert */
{
    INT erg = OK;
    INT i,im;
    OP w,ae,be,z,m;
   
    CTO(PARTITION,"mmm_partition_partition_(1)",a);
    CTO(PARTITION,"mmm_partition_partition_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm_partition_partition_(3)",c);

 
    if (S_PA_LI(a) == 0) {
        erg += mmm_null_partition_(b,c,f);
        goto eee;
        }
 
    if (S_PA_LI(b) == 0) {
        erg += mmm_null_partition_(a,c,f);
        goto eee;
        }


 
    if (S_PA_LI(a) > S_PA_LI(b)) { w = a; a = b; b=w; }

    im = S_PA_II(a,S_PA_LI(a)-1) + S_PA_II(b,S_PA_LI(b)-1);
   
    ae = CALLOCOBJECT();
    be = CALLOCOBJECT();
    w = CALLOCOBJECT();
    if (mmm_ce == NULL) {
        mmm_ce = CALLOCOBJECT();
        erg += init_hashtable(mmm_ce);
        }
    erg += weight(a,w);
   
    t_VECTOR_EXPONENT(b,be);
    if (S_PA_LI(be) >= im) M_I_I(im,S_PA_L(be));
    else {
        i = S_PA_LI(be);
        inc_vector_co(S_PA_S(be),im-S_PA_LI(be));
        for (;i<S_PA_LI(be);i++) M_I_I(0,S_PA_I(be,i));
        }
    t_VECTOR_EXPONENT(a,ae);
    if (S_PA_LI(ae) >= im) M_I_I(im,S_PA_L(ae));
    else {
        i = S_PA_LI(ae);
        inc_vector_co(S_PA_S(ae),im-S_PA_LI(ae));
        for (;i<S_PA_LI(ae);i++) M_I_I(0,S_PA_I(ae,i));
        }
    erg += m_l_nv(S_PA_L(be),w);

    C_O_K(w,INTEGERVECTOR);
    erg += verf2(w,a,be,mmm_ce,im-1);

    FORALL(z,mmm_ce,{
        m = CALLOCOBJECT();
        *m = *z;
        C_O_K(z,EMPTY);
        FREESELF(S_MO_K(m));
        M_I_I(0,S_MO_K(m));
        coeff_mmm(S_MO_S(m),ae,be,S_MO_K(m),1,im-1);
        if (not EINSP(f))
            {
            MULT_APPLY(f,S_MO_K(m));
            }
        erg += t_EXPONENT_VECTOR_apply(S_MO_S(m));
        if (S_O_K(c) == MONOMIAL)
            INSERT_LIST(m,c,add_koeff,comp_monommonomial);
        else
            {
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(m)),i);
            C_PA_HASH(S_MO_S(m),i); /* hash value is computed, insert hash is faster */
            insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }

    });

    M_I_I(0,S_V_I(mmm_ce,S_V_LI(mmm_ce)));
 
 
    FREEALL(ae);
    FREEALL(be);
    FREEALL(w);
eee:   
    ENDR("mmm_partition_partition_");
}

static INT coeff_mmm(a,b,c,res,faktor,starti) OP a,b,c,res; INT faktor,starti;
/* a b c sind in exponenten schreibweise */
{
    INT erg = OK;
    INT i,j;
    CTO(PARTITION,"coeff_mmm(1)",a);
    CTO(PARTITION,"coeff_mmm(2)",b);
    CTO(PARTITION,"coeff_mmm(3)",c);

    for (;starti >=0;starti--) 
        if (S_PA_II(a,starti)>0) break;
    for (i=starti; i>=0;i--)
        {
        /* zuerst schauen ob nicht noch zu grosse teile da sind */
 
        if (S_PA_II(a,i) == 0) continue;
        /* nun versuchen i zu zerlegen */

        if ( (S_PA_II(b,i) > 0) && (S_PA_II(c,i) > 0) &&
             (S_PA_II(b,i) == S_PA_II(c,i))
           ) {
            DEC_INTEGER(S_PA_I(b,i));
            DEC_INTEGER(S_PA_I(a,i));
            coeff_mmm(a,b,c,res,2*faktor,i);
            INC_INTEGER(S_PA_I(b,i));
            INC_INTEGER(S_PA_I(a,i));
            goto weiter;
            }
        if (S_PA_II(b,i) > 0) {
            DEC_INTEGER(S_PA_I(b,i));
            DEC_INTEGER(S_PA_I(a,i));
            coeff_mmm(a,b,c,res,faktor,i);
            INC_INTEGER(S_PA_I(b,i));
            INC_INTEGER(S_PA_I(a,i));
            }
        if (S_PA_II(c,i) > 0) {
            DEC_INTEGER(S_PA_I(c,i));
            DEC_INTEGER(S_PA_I(a,i));
            coeff_mmm(a,b,c,res,faktor,i);
            INC_INTEGER(S_PA_I(a,i));
            INC_INTEGER(S_PA_I(c,i));
            }
weiter:
        for (j=0;j<i;j++)
            {
            if (
               (S_PA_II(b,j) > 0) && (S_PA_II(c,i-j-1) > 0)
               /* aber verschieden */
               )
                {
                    DEC_INTEGER(S_PA_I(b,j));
                    DEC_INTEGER(S_PA_I(c,i-j-1));
                    DEC_INTEGER(S_PA_I(a,i));
                    coeff_mmm(a,b,c,res,faktor,starti);
                    INC_INTEGER(S_PA_I(a,i));
                    INC_INTEGER(S_PA_I(c,i-j-1));
                    INC_INTEGER(S_PA_I(b,j));
                }
 
 
            }
        goto eee;
        }
    if (i<0) /* null , blatt res erhoehen */
        {
        M_I_I(1*faktor + S_I_I(res),res);
        goto eee;
        }
eee:       
    ENDR("internal to mult_monomial_monomial");
}



INT mult_monomial_monomial(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->MONOMIAL necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,MONOMIAL,"mult_monomial_monomial(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mult_monomial_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"mult_monomial_monomial(3)",c);

    if (S_O_K(c) == EMPTY) {
       if (S_O_K(a) == INTEGER)
           {
           if (S_O_K(b) == PARTITION) init_monomial(c);
           else { t=1; init_hashtable(c); }
           }
       else { t=1; init_hashtable(c); }
       }

    erg += mmm___(a,b,c,cons_eins);

    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("mult_monomial_monomial");
}

INT mmm___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,MONOMIAL,"mmm___(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mmm___(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mmm___(3)",c);

    if (S_O_K(a) == INTEGER)
        {
        erg += mmm_integer__(a,b,c,f);
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += mmm_partition__(a,b,c,f);
        }
    else if (S_O_K(a) == MONOMIAL)
        {
        erg += mmm_monomial__(a,b,c,f);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += mmm_hashtable__(a,b,c,f);
        }

    ENDR("mmm___");
}

static INT verf2(v,a,b,c,limit) OP a,b,c; OP v; INT limit;
{
    INT erg = OK;
    INT i,j;
    OP m;
    CTO(PARTITION,"verf2(1)",a);
    CTO(PARTITION,"verf2(2)",b);
    CTO(HASHTABLE,"verf2(3)",c);

     
     
    if (S_PA_LI(a) == 1)
        {
        OP d,ps,z,h,h2,p2;
        d = b;

        m = CALLOCOBJECT();
        ps = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        erg += m_il_integervector(S_PA_LI(d),ps);
        erg += b_ks_pa(EXPONENT,ps,S_MO_S(m));

        for (i = 0,z=S_V_S(S_PA_S(d));i<S_PA_LI(d);i++,z++)  
            {
            if (S_I_I(z) != 0) {
                DEC_INTEGER(z);
                INC_INTEGER(S_PA_I(d,i+S_PA_II(a,0)));
                for (j=0,h=S_V_S(ps),h2=S_V_S(v),p2=S_V_S(S_PA_S(d));
                     j<S_V_LI(ps);
                     j++,h++,h2++,p2++)
                            M_I_I(S_I_I(h2)+S_I_I(p2), h );
                HASH_INTEGERVECTOR(S_PA_S(S_MO_S(m)),j);
                C_PA_HASH(S_MO_S(m),j);
                M_I_I(S_PA_II(d,i+S_PA_II(a,0)), S_MO_K(m));

                add_apply_hashtable(m,c,add_koeff,eq_monomsymfunc,
                                               hash_monompartition);
                DEC_INTEGER(S_PA_I(d,i+S_PA_II(a,0)));
                INC_INTEGER(z);
                }
            }
     
        /* noch das monom ohne addition der exponenten */
     
        INC_INTEGER(S_PA_I(d,S_PA_II(a,0)-1));
        for (j=0,h=S_V_S(ps),h2=S_V_S(v),p2=S_V_S(S_PA_S(d));
             j<S_V_LI(ps);
             j++,h++,h2++,p2++)
                    M_I_I(S_I_I(h2)+S_I_I(p2), h );
        HASH_INTEGERVECTOR(S_PA_S(S_MO_S(m)),j);
        C_PA_HASH(S_MO_S(m),j);
        M_I_I(S_PA_II(d,S_PA_II(a,0)-1), S_MO_K(m));
        add_apply_hashtable(m,c,add_koeff,eq_monomsymfunc,
                                       hash_monompartition);

        DEC_INTEGER(S_PA_I(d,S_PA_II(a,0)-1));
        FREEALL(m);
        }
    else{
    /* in die rekursion */
        INT pi;OP z,h;
     
        pi = S_PA_II(a,S_PA_LI(a)-1);
        DEC_INTEGER(S_PA_L(a));
        for (i = 0,z=S_V_S(S_PA_S(b)),h = S_V_I(v,pi);
            i<S_PA_LI(b);i++,z++,h++)  
            {
            if (S_I_I(z) != 0) {
                DEC_INTEGER(z);
                INC_INTEGER(h);
                verf2(v,a,b,c,i+pi-1);
                DEC_INTEGER(h);
                INC_INTEGER(z);
                }
            }
     
        INC_INTEGER(S_V_I(v, pi-1) );
        verf2(v,a,b,c,pi-1);
        DEC_INTEGER(S_V_I(v, pi-1) );
        INC_INTEGER(S_PA_L(a));
    }
     
     
     
    ENDR("verf2");
}
 

