/* multiplication homsym \times monomial = monomial */
#include "def.h"
#include "macro.h"



   INT mhm_integer_partition_();
   INT mhm_integer_partition_hashtable();
   INT mhm_integer_hashtable_hashtable();
   INT thm_integer__faktor();

static INT SYMMETRICA_mhm_co_ip();
static INT hm_coeff();

INT mhm_null__(b,c,f) OP b,c,f;
{
    INT erg = OK;
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mhm_null__(1)",b);
    CTO(HASHTABLE,"mhm_null__(2)",c);
    if (S_O_K(b) == PARTITION) {
        _NULL_PARTITION_(b,c,f);
        }
    else /* monomial or hashtable */
        {
        OP z;
        FORALL(z,b,{
            OP d;
            d = CALLOCOBJECT();
            erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
            erg += copy_partition(S_MO_S(z),S_MO_S(d));
            COPY(S_MO_K(z),S_MO_K(d));
            if (not EINSP(f))
                {
                MULT_APPLY(f,S_MO_K(d));
                }
            INSERT_HASHTABLE(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            });
        }
    ENDR("mhm_null__");
}

INT mhm_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;

    CTO(INTEGER,"mhm_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mhm_integer__(2)",b);
    CTO(HASHTABLE,"mhm_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0),"mhm_integer__:parameter < 0");
    if (S_I_I(a) == 0) {
        erg += mhm_null__(b,c,f);
        goto ende;
        }
    else if (S_O_K(b) == PARTITION) {
        erg += mhm_integer_partition_hashtable(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mhm_integer_hashtable_hashtable(a,b,c,f);
        goto ende;
        }
ende:
    ENDR("mhm_integer__");
}

INT mhm_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mhm_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mhm_partition__(2)",b);
    CTO(HASHTABLE,"mhm_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        erg += mhm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(a) == 1) {
        erg += mhm_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else { /* partition of length >= 1 */
        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();
 
        erg += init_hashtable(e);
        erg += thm_integer__faktor(S_PA_I(a,0),e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mhm_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);

        mult_monomial_monomial(e,b,c);
        FREEALL(e);
        }

ende:
    ENDR("mhm_partition__");
}

INT mhm_homsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    OP z,ff;
    CTO(HOMSYM,"mhm_homsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mhm_homsym__(2)",b);
    CTO(HASHTABLE,"mhm_homsym__(3)",c);

    if (S_L_S(a) == NULL) { /* empty list */
        goto eee;
        }
    if (S_S_N(a) == NULL) {
        if (EINSP(f))
            erg += mhm_partition__(S_S_S(a),b,c,S_S_K(a));
        else {
            ff = CALLOCOBJECT();
            MULT(f,S_S_K(a),ff);
            erg += mhm_partition__(S_S_S(a),b,c,ff);
            FREEALL(ff);
            }
        goto eee;
        }
    else if (S_S_SLI(a) == 0) {
        if (EINSP(f))
            erg += mhm_partition__(S_S_S(a),b,c,S_S_K(a));
        else {
            ff = CALLOCOBJECT();
            MULT(f,S_S_K(a),ff);
            erg += mhm_partition__(S_S_S(a),b,c,ff);
            FREEALL(ff);
            }
        erg += mhm_homsym__(S_S_N(a),b,c,f);
        goto eee;
        }
    else {
        OP zv,hi;
        INT i,j;
        i = S_S_SII(a,0);
        z = a;zv = NULL;
again:
        if (S_S_SII(z,0) == i)
            {
            for (j=0;j<S_S_SLI(z)-1;j++)
                M_I_I(S_S_SII(z,j+1),S_S_SI(z,j));
            M_I_I(S_S_SLI(z)-1,S_S_SL(z));
            zv = z; z = S_S_N(z);
            if (z != NULL) goto again;
            }
/* jetzt ist z der erste teil mit dem kleinsten teil partition >i */
/* zv ist der letzte teil mit kleinsten teil = i */
/* berechne : h_i * b * h_a + b* h_z */
	C_S_N(zv,NULL);
        
        ff = CALLOCOBJECT(); 
        init_hashtable(ff);
        hi = CALLOCOBJECT();
        M_I_I(i,hi);
        erg += mhm_integer__(hi,b,ff,f);
        erg += mhm_homsym__(a,ff,c,cons_eins);

        if (z != NULL)
            erg += mhm_homsym__(z,b,c,f);
        FREEALL(hi);
        FREEALL(ff);
/* a wieder richtig zusammen bauen */
        
        zv = a;
aa:
        for (j=S_S_SLI(zv);j>0;j--)
            M_I_I(S_S_SII(zv,j-1),S_S_SI(zv,j));
        M_I_I(i,S_S_SI(zv,0));
        M_I_I(S_S_SLI(zv)+1,S_S_SL(zv));
        if (S_S_N(zv) != NULL) { zv = S_S_N(zv); goto aa; }

        C_S_N(zv,z);
        
        }
    
    
eee:
    ENDR("mhm_homsym__");
}

INT mhm_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mhm_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mhm_hashtable__(2)",b);
    CTO(HASHTABLE,"mhm_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mhm_partition__); 
    ENDR("mhm_homsym__");
}

INT mhm_integer_partition_hashtable(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;

    CTO(INTEGER,"mhm_integer_partition_(1)",a);
    CTO(PARTITION,"mhm_integer_partition_(2)",b);
    CTO(HASHTABLE,"mhm_integer_partition_(3)",c);
    SYMCHECK((S_I_I(a) < 0),"mhm_integer_partition_hashtable:integer < 0");

    if (S_I_I(a) == 0) {
        erg += mhm_null__(b,c,f);
        goto ende;
        }
    else if (S_PA_LI(b) == 0)
        {
        erg += thm_integer__faktor(a,c,f); /* generates sum over all partitions */
        goto ende;
        }
    else 
        {
        erg += SYMMETRICA_mhm_co_ip(a,b,c,f);
        goto ende;
        }

ende:
    ENDR("mhm_integer_partition_hashtable");
}

INT mhm_integer_hashtable_hashtable(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
{
    INT erg = OK;
    CTO(INTEGER,"mhs_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"mhs_integer_hashtable_(2)",b);
    CTO(HASHTABLE,"integer_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mhm_integer_partition_hashtable);
    ENDR("mhm_integer_hashtable_hashtable");
}



INT mult_homsym_monomial(a,b,c) OP a,b,c;
/* AK 111001
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->MONOMIAL necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,HOMSYM,"mult_homsym_monomial(1)",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mult_homsym_monomial(2)",b);
    CTTTO(EMPTY,HASHTABLE,MONOMIAL,"mult_homsym_monomial(3)",c);

    if (S_O_K(c) == EMPTY) {
        t=1;
        init_hashtable(c);
        }
    else if (S_O_K(c) == MONOMIAL) {
        t=1;
        t_MONOMIAL_HASHTABLE(c,c);
        }

    if (S_O_K(a) == INTEGER)        
        {
        erg += mhm_integer__(a,b,c,cons_eins);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)  
        {
        erg += mhm_partition__(a,b,c,cons_eins);
        goto ende;
        }
    else if (S_O_K(a) == HOMSYM)
        {
        erg += mhm_homsym__(a,b,c,cons_eins);
        goto ende;
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        erg += mhm_hashtable__(a,b,c,cons_eins);
        goto ende;
        }

ende:
    if (t==1) t_HASHTABLE_MONOMIAL(c,c);
    ENDR("mult_homsym_monomial");
}

static INT next_part_EXPONENT_apply_limit(p,be,bp) OP p,be; INT bp;
/* next with limit be */
/* bp maximaler eintrag != 0 */
{
    INT j,i,w,t,h;
    INT erg = OK;
    OP z,zz;
    
    i = S_PA_LI(p);t=0;
    for (j=bp, z = S_PA_I(p,bp);j>0;j--,z--)
        {
        w = S_I_I(z);
        if (w > 0) /* schauen ob frei */
            {
            t+=w; 
            if (j >= S_PA_LI(be)) 
                { 
                i = j; 
                }
            else if (S_PA_II(be,j) == 0) 
                { 
                i = j; 
                }
            else /* S_PA_II(be,j) > 0 */ {
                t -= S_PA_II(be,j); 
                if (t>0) 
                    i = j;
                }
            }
        else {
            if (j < S_PA_LI(be))  
                {
                if (S_PA_II(be,j) > 0)  t-=S_PA_II(be,j);
                }
            }
        }
            
    if (i ==  S_PA_LI(p))       return LASTPARTITION;
    /* an der stelle i kann decrementiert werden */
    w=0;
    for(j=1,z=S_V_S(S_PA_S(p));j<=i;j++,z++)
        {
        h = S_I_I(z);
        C_I_I(z,0);
        while (h--) w+=j;
        }

    w += (i+1);
    DEC_INTEGER(S_PA_I(p,i));
    /* nun das gewicht w in den kleineren teilen unter bringen,
       aber das limit beruecksichtigen */
    
    /* zuerst feststellen wie viel vom limit bereits abgearbeitet ist */
    for (t=0,j=bp;j>=i;j--) 
        t+= S_PA_II(p,j);
    /* t teile in p > i */
    /* nun feststellen wieviel teile davon das limit ueberdecken */
    for (j=S_PA_LI(be)-1,z = S_PA_I(p,j),
         zz = S_PA_I(be,j);j>=0;j--,z--,zz--)
        {
        h = S_I_I(zz);
        if (t >= h) 
            t -= h;
        else if (t > 0)     
            { 
            C_I_I(z,h-t);
            t = 0;
            w -= S_I_I(z)*(j+1); 
            }
        else /* t == 0 */ 
            { 
            C_I_I(z,h);
            w -= h*(j+1); 
            }
        }
    i--; 
    t = i;
    while (w > 0) {
        if (i==0) /* kein limit mehr, bei t einfuegen */
            {
            M_I_I( S_PA_II(p,t) + (w/ (t+1)) ,S_PA_I(p,t));
            if ( (w % (t+1) ) > 0 )
            INC_INTEGER(S_PA_I(p, w % (t+1) -1));
            return OK;
            }
    
        /* nach links kleineres teil aus dem limit suchen und vergroessern */
        for (j=i-1, z = S_PA_I(p,j);j>=0;j--,z--)
            {
    nochmal:
            if ((i-j) > w) continue;
            if (S_I_I(z) > 0) {
                DEC_INTEGER(z);
                INC_INTEGER(S_PA_I(p,i));
                w += j;
                w -= i;
                if (w == 0) return OK;
                goto nochmal;
                }
            }
        i--;   
        }
     SYMCHECK(1,"next_part_EXPONENT_apply_limit:should never be here");
     ENDR("next_part_EXPONENT_apply_limit");
}

static OP hm_coeff_lo,hm_coeff_oben,hm_coeff_unten;
static INT SYMMETRICA_mhm_co_ip(a,b,c,faktor) OP a,b,c; OP faktor;
/* addiert das ergebnis von h_a \times m_b zu c */
/* dabei gibt es den coeffizienten  faktor */
{
    INT erg = OK;
    INT bp;
    INT i,w,j;
    OP p;
    OP be,m,z;
    CTO(INTEGER,"SYMMETRICA_mhm_co_ip(1)",a);
    CTO(PARTITION,"SYMMETRICA_mhm_co_ip(2)",b);
    CTO(HASHTABLE,"SYMMETRICA_mhm_co_ip(3)",c);

    hm_coeff_lo = CALLOCOBJECT();
    hm_coeff_oben=CALLOCOBJECT(); C_O_K(hm_coeff_oben,INTEGER);
    hm_coeff_unten=CALLOCOBJECT(); C_O_K(hm_coeff_unten,INTEGER);

    for (i=0,w=S_I_I(a),z=S_V_S(S_PA_S(b));i<S_PA_LI(b);i++,z++) w+= S_I_I(z);
    /* w is the weight of the result */


    p=CALLOCOBJECT();
    be=CALLOCOBJECT();
   
    
    erg += t_VECTOR_EXPONENT(b,be);

    erg += copy_partition(be,p);
    /* increase the partition, filling with zero */
    i = S_PA_LI(p);



    inc_vector_co(S_PA_S(p),S_I_I(a));
    for (;i<S_PA_LI(p);i++) M_I_I(0,S_PA_I(p,i));



    for (i=S_PA_LI(p)-1;i>=0;i--)
        if (S_PA_II(p,i) > 0 ) break;
    DEC_INTEGER(S_PA_I(p,i));
    M_I_I(1,S_PA_I(p,i+S_I_I(a)));

    m = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(m));
    erg += m_il_nv(w,S_PA_S(S_MO_S(m)));
    C_O_K(S_PA_S(S_MO_S(m)), INTEGERVECTOR);

    do {
            FREESELF(S_MO_K(m));
            erg += hm_coeff(be,p,S_MO_K(m));
            {
            INT i,j=0,ba=0;
            OP l;
            for (l=S_V_S(S_PA_S(p)),i=0; i<S_PA_LI(p); i++,l++)
                 if (S_I_I(l)>0) 
                     { 
                     j += S_I_I(l); 
                     ba=i; 
                     }

            /* ba is the last non zero entry in p */
            C_I_I(S_PA_L(S_MO_S(m)),j);
            
            for (l=S_V_S(S_PA_S(S_MO_S(m))),i=0;i<=ba;i++)
                if (S_PA_II(p,i)>0)
                    for (j=(INT)0;j<S_PA_II(p,i);j++)
                        {
                            C_I_I(l,i+1);
                            l++;
                        }
            }

            bp = S_PA_II(S_MO_S(m), S_PA_LI(S_MO_S(m))-1) -1;
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(m)),j);
            C_PA_HASH(S_MO_S(m),j);
            if (not EINSP(faktor))
                MULT_APPLY(faktor,S_MO_K(m));

            add_apply_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);

    } while(next_part_EXPONENT_apply_limit(p,be,bp) != LASTPARTITION);

    FREEALL(m);
    FREEALL(p);
    FREEALL(be);
    FREEALL(hm_coeff_lo);
    FREEALL(hm_coeff_oben);
    FREEALL(hm_coeff_unten);
    ENDR("internal to mhm(2)");
}

 
 
static INT hm_coeff(ae,be,c) OP ae,be,c;
/* ae ist kleine partition (exponent), be ist grosse partition (exponent)*/
/* c wird das ergebnis, der coeff von be beim produkt h_n * ae */
{
    INT i,j,k,t=0,w;
    INT erg = OK;
    OP z;
    CTO(EMPTY,"hm_coeff(3)",c);
    M_I_I(1,c);
    
    for (i=S_PA_LI(ae)-1,j=S_PA_LI(be)-1,k=0,
         z = S_PA_I(be,j);
         i>=0;i--)
        {
        w = S_PA_II(ae,i);
        if (w > 0) {
            while(j>=i) { 
                k+= S_I_I(z);
                j--;z--;
                }
            if (k < w)
                {
                if (S_O_K(c) == INTEGER) M_I_I(0,c);
                else m_i_i(0,c);
                goto endr_ende;
                }
 
            C_I_I(hm_coeff_oben,k);
            C_I_I(hm_coeff_unten,w);
            if (t==0)
                {
                BINOM_POSINTEGER_POSINTEGER(hm_coeff_oben,hm_coeff_unten,c);
                t=1;
                }
            else {
                BINOM_POSINTEGER_POSINTEGER(hm_coeff_oben,hm_coeff_unten,hm_coeff_lo);
                MULT_APPLY(hm_coeff_lo,c);
                FREESELF(hm_coeff_lo);
                }

            k -=  w;
            }
        }
 
 
    ENDR("internal(2) to mult_homsym_monomial");
}
 
