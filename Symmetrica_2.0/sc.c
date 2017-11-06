#include "def.h"
#include "macro.h"
/* AK 141086 */
/* symchar.c */

static struct symchar * callocsymchar();
static INT calculate();
static INT removestrip();
static INT addstrip();
static INT removestrip_char();
static INT addstrip_char();
static INT stripexistp();
static INT stripexistp_char();
static INT (*sef)() = NULL, (*asf)() = NULL, (*rsf)() = NULL;

INT chartafel_symfunc();

#ifdef CHARTRUE
INT augpart(part) OP part;
/* bsp: 1113 --> 1236 */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
{
    INT i;
    C_O_K(part,AUG_PART);
    for (i=(INT)0;i<S_PA_LI(part); i++)
        C_I_I(S_PA_I(part,i),S_PA_II(part,i)+i);
    return OK;
}



static INT stripexistp_char(part,length,i) OP part; register INT  length,i;
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
    {
    /* register INT j; */
    unsigned char *z = S_PA_CI(part,i);
    register INT h2;

    h2 = *z;

    for (; i>=(INT)0;i--,z--)
        if ( (*z + length) == h2) 
            return(FALSE);
    return(TRUE);
    }




static INT stripexistp(part,length,i) OP part; register INT  length,i;
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
    {
    /* register INT j; */
    OP z = S_PA_I(part,i);
    register INT h2;

    h2 = S_I_I(z);

    for (; i>=(INT)0;i--,z--)
        if ( (S_I_I(z) + length) == h2) 
            return(FALSE);
    return(TRUE);
    }




static INT addstrip_char(part,k,i,hi) OP part; register INT  k,hi,i;
/* part vom Typ CHARPARTITION */
{
    /* register INT l; */
    i=i-hi;
    /* in l wird angesetzt */
    while ((k--)>(INT)0)
        {
        if (i == S_PA_LI(part)-(INT)1)
            {
            S_PA_CII(part,i)=S_PA_CII(part,i)
                +(unsigned char)k+(unsigned char)1;
            goto addstripende; 
            }
        else if (S_PA_CII(part,i) < S_PA_CII(part,(i+(INT)1)))
            S_PA_CII(part,i)++;
        else if (S_PA_CII(part,i) == S_PA_CII(part,(i+(INT)1)))
            S_PA_CII(part,++i)++;
        else
            error("addstrip_char:");
        }
addstripende:
    return OK;
}




static INT addstrip(part,k,i,hi) OP part; register INT  k,hi,i;
{
    /* register INT l; */
    OP z;
    i -=hi;
    /* in l wird angesetzt */
    z = S_PA_I(part,i);
    while ((k--)>(INT)0)
        {
        if (i == S_PA_LI(part)-(INT)1)
            {
            C_I_I(z,S_I_I(z)+k+1);
            goto addstripende; 
            }
/*
        else if (S_I_I(z) < S_I_I(z+1))
            INC_INTEGER(z);
        else if (S_I_I(z) == S_I_I(z+1))
            {
            i++;
            z++;
            INC_INTEGER(z);
            }
        else
            error("addstrip:");
*/
        if (S_I_I(z) == S_I_I(z+1)) 
            { i++; z++; }
        INC_INTEGER(z);
        }
addstripende:
    return OK;
}




static INT removestrip_char(part,k,i) OP part; register INT  k; INT i;
/* erzeugt neue partition part in der ab der zeile i ein
streifen der laenge length entfernt wurde .
ergebnis ist die hakenlaenge */
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
    {
    register INT l;
    l=i;
    while ((k--)>(INT)0)
        {
        if (i == (INT)0) 
            S_PA_CII(part,(INT)0)--;
        else if (S_PA_CII(part,i) > S_PA_CII(part,(i-(INT)1)))
            S_PA_CII(part,i)--;
        else     
            S_PA_CII(part,--i)--;
        };
    return(l-i);
    }



static INT removestrip(part,k,i) OP part; register INT  k; INT i;
/* erzeugt neue partition part in der ab der zeile i ein
streifen der laenge length entfernt wurde .
ergebnis ist die hakenlaenge */
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
    {
    register INT l;
    OP z;
    l=i;
    z = S_PA_I(part,i);
    while ((k--)>0)
        {
        if (i == 0) 
            {
            DEC_INTEGER(z);
            }
        else if (S_I_I(z) > S_I_I(z-1) )
            {
            DEC_INTEGER(z);
            }
        else     
            {
            z--;
            i--;
            DEC_INTEGER(z);
            }
        };
    return(l-i);
    }
#endif /* CHARTRUE */
#define REMOVESTRIP(part,length,j)\
    k=length;l=j;m=j;\
    while ((k--)>(INT)0)\
        {\
        if (m == (INT)0) \
            DEC_INTEGER(S_PA_I((part),(INT)0));\
        else if (S_PA_II((part),m) > S_PA_II((part),(m-(INT)1)))\
            DEC_INTEGER(S_PA_I((part),m));\
        else     \
            DEC_INTEGER(S_PA_I((part),--m));\
        };\
    hooklength=l-m;

#ifdef CHARTRUE
static INT calculate(sign,rep,part,res) INT  sign; OP part, res, rep;
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 250291 V1.2 */
/* AK 200891 V1.3 */
    {
    INT i,hooklength,l;
    OP newrep;
    INT erg=OK; 
    INT (*lsef)() = sef, (*lasf)() = asf, (*lrsf)() = rsf;

    if (S_PA_LI(part) == (INT)0)
        { 
        if (sign==(INT)1) 
            INC(res); 
        else if (sign == -1L) 
            DEC(res);
        else 
            erg += ERROR;
        goto ende;
        };
    if (S_PA_LI(part) == 1L) /* Robinson Lemma 4.11 */
        {
        if (S_PA_LI(rep) == 1L)
            {
            M_I_I(1L,res);
            goto ende;
            }
        if (S_PA_II(rep,S_PA_LI(rep)-2L) > S_PA_LI(rep)-1L )
            goto ende;

        /* rep is haken */
        for (i=(INT)0;i<S_PA_LI(rep);i++)
            if (S_PA_II(rep,i) > i) break;
        i = S_PA_LI(rep)-i;
        /* i is laenge der part */
        if (sign==1L)
            if (i % 2L == (INT)0)
                DEC(res);
            else 
                INC(res);
        else
            if (i % 2L == (INT)0)
                INC(res);
            else 
                DEC(res);
        goto ende;
        }
    if (S_PA_II(part,S_PA_LI(part)-1) == 1L)
        /* AK 150988 */ /* dimension */
        /* all parts are 1, so we compute the dimension */
        { 
        newrep = CALLOCOBJECT();
        erg += dimension_augpart(rep,newrep);
        if (sign == -1L) 
            ADDINVERS_APPLY(newrep);
        ADD_APPLY(newrep,res); 
        FREEALL(newrep); 
        goto ende;
        }
    l = S_PA_LI(part)-1L; /* AK 040293 */
    for (i=S_PA_LI(rep)-1L;i>=(INT)0;i--)
    if (S_PA_II(part,l) <= S_PA_II(rep,i))
        if     ((*lsef)( rep, S_PA_II(part,l), i))
        
            { 
            hooklength = (*lrsf)( rep, S_PA_II(part,l), i); 
            if (S_O_K(part) == PARTITION)
                DEC_INTEGER(S_PA_L(part));
            else if (S_O_K(part) == CHARPARTITION) /* AK 130593 */
                S_PA_C(part)[0]--;
            erg += calculate( ((hooklength % 2L == (INT)0) ? 
                    sign : - sign),
                rep, part, res); 
            if (S_O_K(part) == PARTITION) /* AK 130593 */
                INC_INTEGER(S_PA_L(part));
            else if (S_O_K(part) == CHARPARTITION)
                S_PA_C(part)[0]++;
            erg += (*lasf)(rep, S_PA_II(part,l), i,hooklength);
        };
ende:
    ENDR("calculate");
    }



INT charvalue_tafel_part(rep,part,res,tafel,pv)    OP part,rep,res,tafel,pv;
/* AK 260690 V1.1 */ /* AK 250291 V1.2 */
/* tafel ist charactertafel, pv ist vector der partitionen */
/* AK 200891 V1.3 */
    {
    INT i=0,j=0,k;
    INT erg = OK;
    CTO(PARTITION,"charvalue_tafel_part(1)",rep);
    CTO(PARTITION,"charvalue_tafel_part(2)",part);
    CTO(VECTOR,"charvalue_tafel_part(5)",pv);
    CTO(MATRIX,"charvalue_tafel_part(4)",tafel);

    for (k=(INT)0; k<= S_V_LI(pv); k++)
        if (EQ(rep,S_V_I(pv,k))) {i=k; break; }
    for (k=(INT)0; k<= S_V_LI(pv); k++)
        if (EQ(part,S_V_I(pv,k))) {j=k; break; }
    COPY(S_M_IJ(tafel,i,j),res); 
    ENDR("charvalue_tafel_part");
    }
    
INT charvalue(rep,part,res,tafel) OP part, rep, res; OP tafel;
/* tafel ist zeiger auf charactertafel mit werten, sonst NULL AK 130189  */
/* part ist der zykeltyp  oder eine PERMUTATION */
/* rep ist irr. darstellung */
/* AK 140789 V1.0 */ /* AK 080290 V1.1 */ /* AK 050391 V1.2 */
/* AK 200891 V1.3 */
    {    
    OP newrep;
    INT erg=OK;

    CTTTO(CHARPARTITION,PARTITION,SKEWPARTITION, "charvalue(1)",rep); 
    CTTTO(CHARPARTITION,PARTITION,PERMUTATION, "charvalue(2)",part);

    if (S_O_K(rep) == SKEWPARTITION) /* AK 170392 */
        {
        erg += error("charvalue:rep == SKEWPARTITION not yet implemented");        
        goto endr_ende;
        }

    if (S_O_K(part) == PERMUTATION)
        { 
        OP newpart;
        newpart = CALLOCOBJECT(); 
        erg += zykeltyp(part,newpart); 
        erg += charvalue(rep,newpart,res,tafel);
        FREEALL(newpart); 
        goto endr_ende;
        }
    if (tafel != NULL)
        { 
        INT i = indexofpart(rep), 
            j = indexofpart(part);
        CTO(MATRIX,"charvalue(4)",tafel);
        erg += copy(S_M_IJ(tafel,i,j),res); 
        goto endr_ende;
        }
    
    if (S_PA_II(part,S_PA_LI(part)-1L) == 1L)
        /* es wird die dimension berechnet */
        { 
        erg += dimension_partition(rep,res); 
        goto endr_ende;
        };


    if (rep == part)
        {
        newrep = callocobject();
        erg += copy(rep,newrep);
        erg += charvalue(newrep,part,res,NULL);
        erg += freeall(newrep);
        return erg;
        }

    FREESELF(res);

    if (S_O_K(rep) == PARTITION)
        erg += c_PARTITION_AUGPART(rep);
    else if (S_O_K(rep) == CHARPARTITION)
        erg += c_CHARPARTITION_CHARAUGPART(rep);

    if (S_O_K(rep) == AUG_PART) 
        {
        sef = stripexistp;
        asf = addstrip;
        rsf = removestrip;
        }
    if (S_O_K(rep) == CHAR_AUG_PART) 
        {
        sef = stripexistp_char;
        asf = addstrip_char;
        rsf = removestrip_char;
        }

    M_I_I((INT)0,res); 
    erg += calculate(1L,rep,part,res);

    if (S_O_K(rep) == AUG_PART)
        erg += c_AUGPART_PARTITION(rep);
    else if (S_O_K(rep) == CHAR_AUG_PART)
        erg += c_CHARAUGPART_CHARPARTITION(rep);
    ENDR("charvalue");
    }
    
    

INT chartafel_partvector(a,erg,pv) OP a; OP erg,pv;
/* AK 260690 V1.1 */ /* AK 200891 V1.3 */
    {
    return chartafel(a,erg);
    }


#ifdef MATRIXTRUE

INT chartafel(a,b) OP a,b;
/* computes the table of irreducible characters of the symmetric group
   of degree a */
/* AK V2.0 300998 */ /* AK V3.0 280705 */
{
    INT erg=OK;
    CTO(INTEGER,"chartafel(1)",a);
    SYMCHECK(S_I_I(a)<0,"chartafel: input < 0");
    CE2(a,b,chartafel);
    if (S_I_I(a) <= (INT) 1)
        {
        erg += m_ilih_m((INT)1,(INT)1,b);
        M_I_I(1,S_M_IJ(b,0,0));
        goto ende;
        }
    C1R(a,"char_tafel",b); /* AK 171297 */

    if (S_I_I(a) <= 16)
        erg += chartafel_nonbit(a,b);
    else
        erg += chartafel_symfunc(a,b);

    S1R(a,"char_tafel",b);
ende:
    CTO(MATRIX,"chartafel(e2)",b);
    ENDR("chartafel");
}

static INT newindexofpart(a,b) OP a,b;
/* AK 030102 */
{
    INT h;
    if (S_PA_HASH(a) == -1) C_PA_HASH(a,hash_partition(a));
    h = S_PA_HASH(a) % S_V_LI(b);
    if (h < 0) h += S_V_LI(b);
    return (S_V_II(b,h));
}

static INT newchartafel(a,b) OP a,b;
/* AK 030102 */
{
    INT erg = OK,i,j;
    INT f = 2;
    OP c,h1,h2;
    
    CTO(INTEGER,"chartafel(1)",a);
    c = CALLOCOBJECT();
    h2 = CALLOCOBJECT();
    erg += makevectorofpart(a,c);
again:
    init_size_hashtable(h2,S_V_LI(c)*f);
    C_O_K(h2,INTEGERVECTOR);
    for (i=0;i<S_V_LI(h2);i++) M_I_I(-1,S_V_I(h2,i));
    for (i=0;i<S_V_LI(c);i++)
        {
        INT h;
        C_PA_HASH(S_V_I(c,i),hash(S_V_I(c,i)));
        h = S_PA_HASH(S_V_I(c,i)) % S_V_LI(h2);
        if (h <0) h += S_V_LI(h2);
 
        if (S_V_II(h2, h) != -1) /* coll */ { f++; goto again; }
        M_I_I(i, S_V_I(h2,h));
        }
 
 
    erg += m_ilih_nm(S_V_LI(c),S_V_LI(c),b);
    NEW_HASHTABLE(h1);
    for (i=0;i<S_V_LI(c);i++)
         {
         OP z;
         t_POWSYM_SCHUR(S_V_I(c,i),h1);
         FORALL(z,h1, {
            j = newindexofpart(S_MO_S(z),h2);
            CLEVER_COPY(S_MO_K(z),S_M_IJ(b,j,i));
            FREESELF(S_MO_K(z));
            M_I_I(0,S_MO_K(z));
            });
         }
    FREEALL3(c,h1,h2);
    ENDR("chartafel");
}


INT chartafel_symfunc(a,b) OP a,b;
{
    INT erg = OK;
    CTO(INTEGER,"chartafel_symfunc",a);
    SYMCHECK(S_I_I(a)<0,"chartafel_symfunc: input < 0");
    if (S_I_I(a) <= 1)
        {
        erg += m_ilih_m((INT)1,(INT)1,b);
        M_I_I(1,S_M_IJ(b,0,0));
        goto ende;
        }
    newchartafel(a,b);
ende:
    ENDR("chartafel_symfunc");
}

INT chartafel_bit(a,res) OP a; OP res;
/* AK 161294 */
/* a and res may be equal */
{
    OP conjpart,vec,bitvec;
    INT dim; /* 231187 AK dimension der matrix */
    INT i,j; INT index; 
    INT erg = OK;
    CTO(INTEGER,"chartafel_bit",a);
    SYMCHECK(S_I_I(a)<0,"chartafel_bit: input < 0");
    if (S_I_I(a) <= 1)
        {
        erg += m_ilih_m((INT)1,(INT)1,res);
        M_I_I(1,S_M_IJ(res,0,0));
        goto endr_ende;
        }

    conjpart = callocobject();  /* AK 290888 */
    vec = callocobject();
    bitvec = callocobject();

    erg += makevectorofpart(a,vec);
    dim = S_V_LI(vec);
    erg += m_il_v(dim,bitvec);
    for (i=0L;i<dim;i++)
        t_VECTOR_BIT(S_V_I(vec,i),S_V_I(bitvec,i));


    erg += m_ilih_m(dim,dim,res);

    i = dim-1L; j=(INT)0;
    do    { 
        erg += charvalue_bit(S_V_I(bitvec,i),S_V_I(vec,j),
            S_M_IJ(res,S_M_HI(res)-1L,j),NULL);
        j++; 
        } 
    while( j < dim);
    /* das war der alternierende Character */


    for (j=(INT)0;j<S_M_LI(res);j++) 
        M_I_I(1L,S_M_IJ(res,(INT)0,j));
    /* das war der eins - Character */

    i=(INT)0;
    do    {
        if (EMPTYP(S_M_IJ(res,i,(INT)0))) 
            /* d.h. zeile noch nicht berechnet */
            {
            j=(INT)0;
            do    { 
    if (  (        S_PA_LI(S_V_I(vec,i))   /* vgl JK Cor 2.4.9 */
            -1L
            +S_PA_II(S_V_I(vec,i),S_PA_LI(S_V_I(vec,i))-1L) 
        )
        >= 
        (    S_PA_II(S_V_I(vec,j),S_PA_LI(S_V_I(vec,j))-1L)  )
          )
                erg += charvalue_bit(S_V_I(bitvec,i),S_V_I(vec,j),
                    S_M_IJ(res,i,j),NULL);
    else
            M_I_I((INT)0,S_M_IJ(res,i,j));
                j++;
                }
            while( j < dim);
            /* AK 290888 berechnung des assozierten characters */
            conjugate(S_V_I(vec,i),conjpart);

            for (index = i+1L;index<dim;index ++) 
                if (EQ(conjpart,S_V_I(vec,index))) 
                    break;
            
            if (index < dim) 
                for (j=(INT)0;j<S_M_LI(res);j++)
                    erg += mult(    S_M_IJ(res,i,j),
                        S_M_IJ(res,S_M_HI(res)-1L,j),
                        S_M_IJ(res,index,j));
                        /* character * 
                        alternierender character */
            };
        i++;
        }
    while( i < dim);

    erg += freeall(conjpart); 
    erg += freeall(vec); 
    erg += freeall(bitvec); 
    ENDR("chartafel_bit");
}

INT chartafel_nonbit(a,res) OP a; OP res;
/* AK 221187 ergebnis ist vom typ matrix*/
/* AK 240387 */ /* berechnet chartafel der s-a aus */
/* AK 170789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
/* AK 121297    a == res is possible
        a is of type INTEGER 
        if a = 0 the result is the 1  1x1 matrix */
    {
    OP conjpart;
    OP vec;
    INT dim; /* 231187 AK dimension der matrix */
    INT i,j;
    INT index;
    
    INT erg = OK;
    CTO(INTEGER,"chartafel_nonbit",a);
    SYMCHECK(S_I_I(a)<0,"chartafel_nonbit: input < 0");
    if (S_I_I(a) <= 1)
        {
        m_ilih_m((INT)1,(INT)1,res);
        M_I_I(1,S_M_IJ(res,0,0));
        goto ende;
        }

    conjpart = callocobject();  /* AK 290888 */
    vec = callocobject();

    erg += makevectorofpart(a,vec);
    dim = S_V_LI(vec);
    erg += m_ilih_m(dim,dim,res); /* AK 231187 res ist damit initialisiert */    

    i = dim-1L; j=(INT)0;
    do    { 
        erg += charvalue(S_V_I(vec,i),S_V_I(vec,j),
            S_M_IJ(res,S_M_HI(res)-1L,j),NULL);
        j++; } 
    while( j < dim);
    /* das war der alternierende Character */

    for (j=(INT)0;j<S_M_LI(res);j++) 
        M_I_I(1L,S_M_IJ(res,(INT)0,j));
    /* das war der eins - Character */

    i=(INT)0;
    do    {
        if (EMPTYP(S_M_IJ(res,i,(INT)0))) 
            /* d.h. zeile noch nicht berechnet */
            {
            j=(INT)0;
            do    { 
    if (  (        S_PA_LI(S_V_I(vec,i))   /* vgl JK Cor 2.4.9 */
            -1L
            +S_PA_II(S_V_I(vec,i),S_PA_LI(S_V_I(vec,i))-1L) 
        )
        >= 
        (    S_PA_II(S_V_I(vec,j),S_PA_LI(S_V_I(vec,j))-1L)  )
          )
                erg += charvalue(S_V_I(vec,i),S_V_I(vec,j),
                    S_M_IJ(res,i,j),NULL);
    else
            M_I_I((INT)0,S_M_IJ(res,i,j));
                j++;
                }
            while( j < dim);
            /* AK 290888 berechnung des assozierten characters */
            conjugate(S_V_I(vec,i),conjpart);

            for (index = i+1L;index<dim;index ++) 
                if (EQ(conjpart,S_V_I(vec,index))) 
                    break;
            
            if (index < dim) 
                for (j=(INT)0;j<S_M_LI(res);j++)
                    erg += mult(    S_M_IJ(res,i,j),
                        S_M_IJ(res,S_M_HI(res)-1L,j),
                        S_M_IJ(res,index,j));
                        /* character * 
                        alternierender character */
            };
        i++;
        }
    while( i < dim);

    erg += freeall(conjpart); 
    erg += freeall(vec); 
ende:
    ENDR("chartafel_nonbit");
    }
#endif /* CHARTRUE */
#endif /* MATRIXTRUE */


INT c_i_n(mu,n,erg,tafel) OP mu,n,erg,tafel;
/* berechnet aus n INTEGER
mu PARTITION den wert c_mu,n =
Mittelwert der summe ueber die Werte des mu-ten
irreduziblen Charakters von den n-ten Potenzen der
x aus S_m, m= gewicht von mu */
/* AK 190988 */
/* AK wenn tafel != NULL ist dies ein zeiger auf die
zugehoerige charactertafel */
/* AK 200789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
#ifdef CHARTRUE
    OP m = callocobject(),ord=callocobject();  
    OP laufpart=callocobject(),exp=callocobject(); 
    OP zw=callocobject(),zwerg=callocobject(),hocherg=callocobject(); 
    weight(mu,m);
    first_partition(m,laufpart); /* vom typ VECTOR */
    freeself(erg);M_I_I((INT)0,erg); /* vorbesetzen mit 0 */

    do    {
        ordcon(laufpart,ord);
        t_VECTOR_EXPONENT(laufpart,exp);
        zykeltyp_hoch_n(exp,n,hocherg);
        t_EXPONENT_VECTOR(hocherg,zw);
        charvalue(mu,zw,zwerg,tafel);
        mult(zwerg,ord,zwerg);
        add(erg,zwerg,erg);
        }
    while(next(laufpart,laufpart));

    fakul(m,zwerg);
    div(erg,zwerg,erg); /* noch durch gruppenordnung dividieren */

    freeall(m);freeall(zwerg);freeall(laufpart);freeall(ord);freeall(exp);
    freeall(hocherg);freeall(zw);
    return(OK);
#else
    error("c_i_n:SYMCHAR not available");return(ERROR);
#endif /* CHARTRUE */
    }


INT symchar_hoch_n(a,n,erg) OP a,n,erg;
/* der SYMCHAR a wird verallgemeinert zu a^n
d.h. die klasse alpha erhaelt den wert auf alpha hoch n */
/* AK 200988 */
/* AK 200789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
#ifdef CHARTRUE
    INT i,index;
    OP zw=callocobject(),zw2=callocobject(); 
    copy(a,erg);
    for (i=(INT)0;i<S_SC_WLI(erg);i++)
        {
        t_VECTOR_EXPONENT(S_SC_PI(erg,i),zw);
        zykeltyp_hoch_n(zw,n,zw2);
        freeself(zw);
        t_EXPONENT_VECTOR(zw2,zw);
        index=indexofpart(zw);
        copy(S_SC_WI(a,index),S_SC_WI(erg,i));
        freeself(zw); freeself(zw2);
        }
    return(OK);
#else
    error("symchar_hoch_n:SYMCHAR not available");return(ERROR);
#endif /* CHARTRUE */
    }

INT c_i_n_an(mu,n,erg,tafel) OP mu,n,erg,tafel;
/* berechnet aus n INTEGER
mu PARTITION den wert c_mu,n =
Mittelwert der summe ueber die Werte des mu-ten
irreduziblen Charakters von den n-ten Potenzen der
x aus S_m, m= gewicht von mu */
/* AK 190988 */
/* AK wenn tafel != NULL ist dies ein zeiger auf die
zugehoerige charactertafel */
/* AK 200789 V1.0 */ /* AK 260690 V1.1 */ /* AK 200891 V1.3 */
    {
#ifdef CHARTRUE
    OP m = callocobject(),ord=callocobject();  
    OP laufpart=callocobject(),exp=callocobject(); 
    OP zw=callocobject(),zwerg=callocobject(),hocherg=callocobject(); 
    weight(mu,m);
    first_partition(m,laufpart); /* vom typ VECTOR */
    freeself(erg);M_I_I((INT)0,erg); /* vorbesetzen mit 0 */

    do    {
        if ((s_i_i(m) - s_pa_li(laufpart))%2 == 0) {
        ordcon(laufpart,ord);
        t_VECTOR_EXPONENT(laufpart,exp);
        zykeltyp_hoch_n(exp,n,hocherg);
        t_EXPONENT_VECTOR(hocherg,zw);
        charvalue(mu,zw,zwerg,tafel);
        mult(zwerg,ord,zwerg);
        add(erg,zwerg,erg);}
        }
    while(next(laufpart,laufpart));

    fakul(m,zwerg);
    div(erg,zwerg,erg); /* noch durch gruppenordnung dividieren */
    freeself(zw);
    M_I_I(2L,zw);mult(erg,zw,erg);

    freeall(m);freeall(zwerg);freeall(laufpart);freeall(ord);freeall(exp);
    freeall(hocherg);freeall(zw); return(OK);
#else
    error("c_i_n_an:SYMCHAR not available");return(ERROR);
#endif /* CHARTRUE */
    }


#ifdef CHARTRUE
INT m_part_centralsc(part,c) OP part,c;
/* AK 010888 curtis/reiner p.235 */
/* AK 140789 V1.0 */ /* AK 100191 V1.1 */ /* AK 220791 V1.3 */
/* AK 010498 V2.0 */
    {
    INT i,erg=OK;
    OP zw,zw2;
    CTO(PARTITION,"m_part_centralsc(1)",part);
    zw = callocobject(); 
    zw2 = callocobject(); 
    erg += m_part_sc(part,c); 
        erg += dimension(part,zw); /* fehler vorher ordcen */
    for (i=(INT)0; i<S_SC_PLI(c);i++)
        { 
        erg += ordcon(S_SC_PI(c,i),zw2);
        erg += mult_apply(zw2,S_SC_WI(c,i)); 
        }
    erg += div(c,zw,c); 
    erg += freeall(zw); 
    erg += freeall(zw2); 
    ENDR("m_part_centralsc");
    }

INT m_part_sc(part,res) OP part,res; 
/* AK 200891 V1.3 */
    {
    INT erg = OK;
    CTO(PARTITION,"m_part_sc(1)",part);
    erg += m_part_sc_tafel(part,res,NULL);
    ENDR("m_part_sc");
    }


INT m_part_sc_tafel(part,res,ct) OP part,res;OP ct;
/* den irreduziblen character zur partition part */
/* AK 140789 V1.0 */
/* AK 210690 V1.1 */ /* ct == NULL oder charactertafel */
/* AK 200891 V1.3 */
/* AK 060498 V2.0 */
    {
    OP dim;
    INT i=(INT)0,j;
    INT erg = OK;
    CTO(PARTITION,"m_part_sc_tafel",part);

    dim = callocobject();
    erg += weight(part,dim);
    erg += b_d_sc(dim,res);
    if (S_I_I(dim) < 2) /* AK 060498 */
        {
        M_I_I(1,S_SC_WI(res,0));
        goto endr_ende;
        }
    if (ct == NULL) {    
        for (i=(INT)0;i<S_SC_PLI(res);i++)
            erg += charvalue(part,S_SC_PI(res,i),
                    S_SC_WI(res,i),NULL);
        }
    else    {
        j = indexofpart(part);
        for (i=(INT)0;i<S_SC_PLI(res);i++)
            erg += copy(S_M_IJ(ct,j,i),S_SC_WI(res,i));
        }
    ENDR("m_part_sc_tafel");
    }


INT ntopaar_symchar(a,b) OP a,b; /* sind symchar */
/* 280488 ohne representanten */
/* diese  routine berechnet den induzierten charcter
aus s_n in s_(n ueber 2) */
/* AK 170789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    { 
    OP dimb;
    OP perm;
    OP grosseperm;
    OP faktor;
    OP typ;
    OP ordnung;
    OP ordnung2;
    OP help;
    
    INT j,index, erg = OK;

    CTO(SYMCHAR,"ntopaar_symchar(1)",a);

    perm = callocobject(); 
    grosseperm = callocobject(); 
    faktor = callocobject(); 
    typ = callocobject(); 
    ordnung = callocobject(); 
    ordnung2 = callocobject(); 
    help = callocobject(); 

    dimb=callocobject(); 
    M_I_I(2L,dimb);
    erg += binom(S_SC_D(a),dimb,dimb);
    /* dimb ist dimension von b */
    erg += m_d_sc(dimb,b);
    /* b ist nun initialisiert */
    
    erg += fakul(S_SC_D(b),help);
    erg += fakul(S_SC_D(a),faktor);
    erg += div(help,faktor,faktor);    /* der konstante faktor */

    for (j=(INT)0;j<S_SC_PLI(a);j++) 
        /* dies ist eine schleife ueber alle
        konjugiertenklassen der unter-gruppe
        */
        {
        if (not nullp(S_SC_WI(a,j)))
            {
            erg += m_part_perm(S_SC_PI(a,j),perm);
            erg += m_perm_paareperm(perm,grosseperm);
            erg += zykeltyp(grosseperm,typ);
            /* typ ist der zykeltyp der induzierten
            permutation */
            index=indexofpart(typ);
            erg += ordcon(S_SC_PI(a,j),ordnung);
            erg += ordcon(typ,ordnung2);
            erg += freeself(help);

            erg += mult(S_SC_WI(a,j) , ordnung,help);
            erg += mult(help,faktor,help);
            erg += div(help, ordnung2,help);
            erg += add(help,S_SC_WI(b,index),S_SC_WI(b,index));
            }
        };

    erg += freeall(dimb);
    erg += freeall(help);
    erg += freeall(ordnung);
    erg += freeall(perm);
    erg += freeall(grosseperm);
    erg += freeall(faktor);
    erg += freeall(typ);
    erg += freeall(ordnung2);
    ENDR("ntopaar_symchar");
    }



INT reduce_symchar(a,b) OP a,b; 
/* AK 200891 V1.3 */
    {
    INT erg = OK;
    CE2(a,b,reduce_symchar);
    erg += reduce_symchar_tafel(a,b,NULL);
    ENDR("reduce_symchar");
    }

#ifdef SCHURTRUE
INT reduce_symchar_tafel(a,b,ct) OP a,b;OP ct;
/* a ist symchar , b ist wird schurfunktion */
/* AK 170789 V1.0 */
/* AK 030190 V1.1 */ /* AK 210690 ct==NULL oder charactertafel */
/* AK 200891 V1.3 */
/* AK 290998 V2.0 */
/* a and b may be equal */
    {
    INT i;
    INT erg = OK;
    OP zw1,res;

    CTO(SYMCHAR,"reduce_symchar_tafel",a);
    if (a == b) /* AK 290998 */
        {
        zw1 = callocobject();
        erg += reduce_symchar_tafel(a,zw1,ct);
        erg += freeall(zw1);
        goto endr_ende;
        }
    erg += init(SCHUR,b);
    zw1=callocobject();
    res=callocobject();

    for (i=(INT)0;i<S_SC_PLI(a);i++)
        {
        erg += m_part_sc_tafel(S_SC_PI(a,i),zw1,ct);
        erg += scalarproduct_symchar(zw1,a,res);
        if (not nullp(res))
            { 
            OP zw = callocobject();
            erg += b_skn_s(callocobject(),callocobject(),NULL,zw);
            erg += copy(S_SC_PI(a,i),S_S_S(zw));
            erg += copy(res,S_S_K(zw));
            insert(zw,b,NULL,comp_monomvector_monomvector);
            }
        else    {
            }
        };

    erg += freeall(res); 
    erg += freeall(zw1); 
    ENDR("reduce_symchar_tafel");
    }
#endif /* SCHURTRUE */


INT scalarproduct_symchar(a,b,c) OP a,b,c;
/* skalarproduct von a und b nach c */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
/* a b and c may be equal */
/* AK 120898 V2.0 */
    {
    INT i;
    OP zw,  zw2, invord;
    INT erg = OK;
    CTO(SYMCHAR,"scalarproduct_symchar",a);
    CTO(SYMCHAR,"scalarproduct_symchar",b);


    if (neq(S_SC_D(a), S_SC_D(b)))
        {
        erg += error("scalarproduct_symchar: different degrees");
        goto endr_ende;
        }

    zw = callocobject();
    zw2 = callocobject();
    invord = callocobject();
    M_I_I(0,zw);

    for (i=(INT)0;i<S_SC_PLI(a);i++)
        {
        erg += mult(S_SC_WI(a,i),S_SC_WI(b,i),zw2);
        erg += inversordcen(S_SC_PI(a,i),invord);
        erg += mult_apply(invord,zw2);
        erg += add_apply(zw2,zw);
        };

    erg += swap(zw,c);
    erg += freeall(zw);
    erg += freeall(invord);
    erg += freeall(zw2);
    ENDR("scalarproduct_symchar");
    }



INT char_matrix_scalar_product(a,i,b,j,partvec,erg,convec) OP a,b,erg,partvec;
    INT i,j; OP convec;
/* AK Tue Jan 24 07:36:11 MEZ 1989 */
/* berechnet skalarproduct bei charactertafeln
dabei wird aus a zeile i und aus b zeile j verwendet 
partvec ist vectorofpartition zu den tafeln
AK 260189
convec ist wenn != NULL vector konjugiertenklassen ordnung */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT k;
    OP zw = callocobject(),zw2 = callocobject(), fak, hcv;


    if (neq (s_m_l(a),s_m_l(b)))
        error("char_matrix_scalar_product:different length of matrix");

    if (convec == NULL)
        {
        hcv = callocobject(); 
        m_il_v(S_V_LI(partvec),hcv);
        for (k=(INT)0;k<s_m_li(a);k++)
            ordcon(S_V_I(partvec,k),S_V_I(hcv,k));
        }
    else    hcv = convec;


    freeself(erg);
    M_I_I((INT)0,erg);

    for (k=(INT)0;k<S_M_LI(a);k++)
        {
        mult(S_M_IJ(a,i,k),S_M_IJ(b,j,k),zw2);
        mult(S_V_I(hcv,k),zw2,zw);
        add(zw,erg,erg);
        freeself(zw);
        };

    fak=callocobject(); 
    fakul(s_pa_i(S_V_I(partvec,(INT)0),(INT)0),fak);
    div(erg,fak,erg);


    freeall(zw);
    freeall(fak);
    freeall(zw2);
    if (convec == NULL) freeall(hcv);
    return(OK);
    }



INT mult_apply_symchar(a,b) OP a,b;
/* a is SYMCHAR */
/* AK 050391 V1.2 */ /* AK 160891 V1.3 */
/* AK 060498 V2.0 */
    {
    OP c;
    INT erg = OK;
    CTO(SYMCHAR,"mult_apply_symchar(1)",a);
    EOP("mult_apply_symchar(2)",b);

    switch (S_O_K(b))
        {
        case SYMCHAR:
            erg += mult_apply(S_SC_W(a),S_SC_W(b));
            goto masende;
        default: /* AK 160891 */
            c = callocobject();
            *c = *b;
            erg += C_O_K(b,EMPTY);
            erg += mult(a,c,b);
            erg += freeall(c);
            break;    
        }
masende:
    ENDR("mult_apply_symchar");
    }



INT mult_symchar_symchar(a,b,c) OP a,b,c;
/* AK Wed Mar  8 10:32:46 MEZ 1989 */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT erg = OK;
    erg += copy(b,c);
    erg += mult(S_SC_W(a),S_SC_W(b),S_SC_W(c));
    return erg;
    }



INT comp_symchar(a,b) OP a,b;
/* AK Thu Jan  3 14:53:38 MEZ 1991 */
/* AK 050391 V1.2 */ /* AK 200891 V1.3 */
{
    if (S_O_K(b) != SYMCHAR) 
        {
        error("comp_symchar: wrong second kind");
        return ERROR;
        }
    if ( neq( S_SC_D(a), S_SC_D(b) ) ) 
        {
        debugprint(S_SC_D(a));
        debugprint(S_SC_D(b));
        error("comp_symchar:  different degrees");
        return ERROR;
        }
    return 
        comp( S_SC_W(a), S_SC_W(b) );
}


INT mult_apply_scalar_symchar(a,b) OP a,b;
/* AK 060498 V2.0 */
{
    INT erg = OK;
    CTO(SYMCHAR,"mult_apply_scalar_symchar(2)",b);
    erg += mult_apply_scalar_vector(a,S_SC_W(b));
    ENDR("mult_apply_scalar_symchar");
}

INT mult_scalar_symchar(a,b,c) OP a,b,c; 
/* AK 010888 */
/* a skalar b symchar c wird symchar */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
/* AK 060498 V2.0 */
    {
    INT erg = OK;
    CTO(SYMCHAR,"mult_scalar_symchar",b);
    erg += copy(b,c);
    erg += mult(a,S_SC_W(b),S_SC_W(c));
    ENDR("mult_scalar_symchar");
    }



INT copy_symchar(a,b) OP a,b; 
/* AK 110588 */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT erg=OK;
    erg += b_wpd_sc(callocobject(),callocobject(),callocobject(),b);
    erg += copy(S_SC_D(a),S_SC_D(b));
    erg += copy(S_SC_P(a),S_SC_P(b));
    erg += copy(S_SC_W(a),S_SC_W(b));
    return erg;
    }



INT reduce_inner_tensor_sc(a,b,c) OP a,b,c;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
/* AK 070898 V2.0 */
/* a,b,c, may be equal */
    {
    OP d,e,f;
    INT erg = OK;
    CTO(PARTITION,"reduce_inner_tensor_sc",a);
    CTO(PARTITION,"reduce_inner_tensor_sc",b);
    d = callocobject(); 
    e = callocobject(); 
    f = callocobject(); 
    erg += m_part_sc(a,d); 
    erg += m_part_sc(b,e); 
    erg += inner_tensor_sc(d,e,f);
    erg += reduce_symchar(f,c); 
    erg += freeall(d); 
    erg += freeall(e); 
    erg += freeall(f);
    ENDR("reduce_inner_tensor_sc");
    }

INT inner_tensor_sc(a,b,c) OP a,b,c;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    if (neq(S_SC_D(a),S_SC_D(b))) {
        error("inner_tensor_sc:different degrees");
        return(ERROR);
        };

    copy(a,c);
    mult(S_SC_W(a),S_SC_W(b),S_SC_W(c));
    return(OK);
    }

INT reduceninpaar(a,b) OP a,b;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    OP c;
    OP d;
    INT erg = OK;
    CTO(PARTITION,"reduceninpaar(1)",a);
     c = callocobject(); d = callocobject();

    erg += m_part_sc(a,c); 
    erg += ntopaar_symchar(c,d);
    erg += reduce_symchar(d,b); 
    erg += freeall(c);
    erg += freeall(d);
    ENDR("reduceinpaar");
    }


INT makevectorofshuffle(max,len,vec) OP max,len,vec;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT i;
    INT erg = OK;

    erg += m_il_v(numberof_shufflepermutation(max,len),vec);
    erg += first_permutation(len,S_V_I(vec,(INT)0));
    for (i=1L;i<S_V_LI(vec);i++)
        next_shufflepermutation(max,S_V_I(vec,i-1),S_V_I(vec,i));
    return erg;
    }


INT add_apply_symchar(a,b) OP a,b;
/* AK 250391 V1.2 */ /* AK 200891 V1.3 */
    {
    INT erg = OK;
    CTO(SYMCHAR,"add_apply_symchar",b);
    erg += add_apply(S_SC_W(a),S_SC_W(b));
    ENDR("add_apply_symchar");
    }



INT add_symchar(a,b,c) OP a,b,c;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT erg = OK;
    CTO(SYMCHAR,"add_symchar",a);
    CTO(SYMCHAR,"add_symchar",b);
    if (S_SC_DI(a) != S_SC_DI(b))
        {
        erg += error("add_symchar: different weight");
        goto endr_ende;
        }
    erg += b_wpd_sc(callocobject(),callocobject(),callocobject(),c);
    erg += copy_integer(S_SC_D(a),S_SC_D(c));     
    erg += copy_vector(S_SC_P(a),S_SC_P(c));
    erg += add_vector(S_SC_W(a),S_SC_W(b),S_SC_W(c));
    ENDR("add_symchar");
    }

INT addinvers_apply_symchar(a) OP a;
/* AK 201289 V1.1 */ /* AK 200891 V1.3 */
    {
    return(addinvers_apply(S_SC_W(a)));
    }


INT addinvers_symchar(a,c) OP a,c;
/* AK 140789 V1.0 */ /* AK 201289 V1.1 */ /* AK 250391 V1.2 */
/* AK 200891 V1.3 */
    {
    INT erg = OK;
    CTO(SYMCHAR,"addinvers_symchar(1)",a);
    erg += b_wpd_sc(callocobject(),callocobject(),callocobject(),c);
    COPY(S_SC_D(a),S_SC_D(c)); 
    COPY(S_SC_P(a),S_SC_P(c));
    erg += addinvers(S_SC_W(a),S_SC_W(c));
    ENDR("addinvers_symchar");
    }


INT freeself_symchar(a) OP a;
/* AK 140789 V1.0 */ /* AK 060290 V1.1 */ /* AK 250391 V1.2 */
/* AK 200891 V1.3 */
    {
    OBJECTSELF d;
    INT erg = OK;
    CTO(SYMCHAR,"freeself_symchar(1)",a);
    erg += freeall(S_SC_W(a)); 
    erg += freeall(S_SC_P(a)); 
    erg += freeall(S_SC_D(a));
    d = S_O_S(a);
    SYM_free(d.ob_symchar);
    C_O_K(a,EMPTY);
    ENDR("freeself_symchar");
    }

INT objectread_symchar(fp,a) FILE *fp; OP a;
/* AK 260291 V1.2 */ /* AK 200891 V1.3 */
    {
    INT erg =OK;
    erg += b_wpd_sc(callocobject(),callocobject(),callocobject(),a);
    erg += objectread(fp,S_SC_D(a));
    erg += objectread(fp,S_SC_P(a));
    erg += objectread(fp,S_SC_W(a));
    return erg;
    }

INT objectwrite_symchar(fp,a) FILE *fp; OP a;
/* AK 260291 V1.2 */ /* AK 200891 V1.3 */
    {
    INT erg=OK;
    fprintf(fp,"%ld\n",(INT)SYMCHAR);
    erg += objectwrite(fp,S_SC_D(a));
    erg += objectwrite(fp,S_SC_P(a));
    erg += objectwrite(fp,S_SC_W(a));
    return erg;
    }

INT nullp_symchar(a) OP a;
/* AK 010692 */
    {
    return nullp(S_SC_W(a));
    }

INT tex_symchar(a) OP a;
/* AK 150692 */
    {
    return tex(S_SC_W(a));
    }

INT einsp_symchar(a) OP a;
/* AK 010692 */
    {
    return einsp(S_SC_W(a));
    }

INT fprint_symchar(fp,a) FILE *fp; OP a;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT i;
    for (i=(INT)0; i<S_SC_WLI(a);i++)
        {
        fprint(fp,S_SC_PI(a,i)); fprintf(fp,":");
        fprint(fp,S_SC_WI(a,i)); fprintf(fp,",");
        if (fp == stdout)
            if (zeilenposition>(INT)70)
                { zeilenposition = (INT)0; fprintf(fp,"\n"); }
            else     zeilenposition += 2L;
        }
    return(OK);
    }

INT scan_symchar(a) OP a;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    OP dim;
    INT i;
    extern INT zeilenposition;
    INT erg = OK;
    CTO(EMPTY,"scan_symchar(1)",a);
    erg += printeingabe(" enter the degree of the symmetric group");
    dim = callocobject();
    erg += scan(INTEGER,dim); 
    erg += b_d_sc(dim,a);

    erg += printeingabe(" enter the character-value on the given class");
    for (i=(INT)0;i<S_SC_PLI(a);i++)
        { 
        erg += print(S_SC_PI(a,i)); 
        printf(" "); 
        zeilenposition++;
        erg += scan(INTEGER,S_SC_WI(a,i)); 
        };
    ENDR("scan_symchar");
    }

INT m_d_sc(dim,ergebnis) OP dim,ergebnis;
/* AK 040391 V1.2 */ /* AK 200891 V1.3 */
/* dim, ergebnis may be equal */
    {
    OP c;
    INT erg = OK;
    CTO(INTEGER,"m_d_sc(1)",dim);
    c = callocobject();
    M_I_I(S_I_I(dim),c);
    erg += b_d_sc(c,ergebnis);
    ENDR("m_d_sc");
    }

INT b_d_sc(dim,ergebnis) OP dim,ergebnis;
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    INT erg = OK; /* AK 301091 */
    CTO(INTEGER,"b_d_sc(1)",dim);
    SYMCHECK (dim == ergebnis, "b_d_sc:input and output are equal");

    erg += b_wpd_sc(callocobject(),callocobject(),dim,ergebnis);
    erg += makevectorofpart(dim,S_SC_P(ergebnis));
    erg += m_il_nv(S_SC_PLI(ergebnis),S_SC_W(ergebnis));
    ENDR("b_d_sc");
    }


static struct symchar * callocsymchar()
/* 110488 AK erste prozedur beim einfuehren eines neuen datentyps */
/* AK 140789 V1.0 */ /* AK 260790 V1.1 */ /* AK 200891 V1.3 */
    {
    struct  symchar *erg
    = (struct symchar *) SYM_calloc((int)1,sizeof(struct symchar));
    if (erg == NULL) 
        no_memory();
    return(erg);
    }

INT m_wpd_sc(wert,parlist,dim,ergebnis) OP wert,parlist,dim,ergebnis;
/* AK Fri Jan  4 09:25:43 MEZ 1991 */
/* AK 200891 V1.3 */
{
    b_wpd_sc(callocobject(),callocobject(),callocobject(),ergebnis);
    copy(wert, S_SC_W(ergebnis));
    copy(parlist, S_SC_P(ergebnis));
    copy(dim, S_SC_D(ergebnis));
    return OK;
}

INT b_wpd_sc(wert,parlist,dim,ergebnis) OP wert,parlist,dim,ergebnis;
/* die zweite prozedur bei neuen typen */
/* AK 110488 erzeugt aus der werteliste den symcharacter */
/* AK 140789 V1.0 */ /* AK 030190 V1.1 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF d;

    if (ergebnis==NULL)/* kein speicher reserviert fuer das ergebnis */
        {/*020488*/error("ergebnis == NULL in m_w_sc");return(ERROR);};

    d.ob_symchar = callocsymchar();  /* AK 161189 */
    b_ks_o(SYMCHAR, d, ergebnis);

    c_sc_w(ergebnis,wert); 
    c_sc_p(ergebnis,parlist); 
    c_sc_d(ergebnis,dim);
    return(OK);
    }

OP s_sc_w(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    return(c.ob_symchar->sy_werte);
    }

OP s_sc_wi(a,i) OP a;INT i;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_v_i(s_sc_w(a),i));
    }

INT s_sc_wii(a,i) OP a;INT i;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_v_ii(s_sc_w(a),i));
    }

INT s_sc_wli(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_v_li(s_sc_w(a)));
    }

OP s_sc_p(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    return(c.ob_symchar->sy_parlist);
    }

OP s_sc_pi(a,i) OP a;INT i;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_v_i(s_sc_p(a),i));
    }

INT s_sc_pli(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_v_li(s_sc_p(a)));
    }

INT s_sc_di(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    return(s_i_i(s_sc_d(a)));
    }
OP s_sc_d(a) OP a;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    return(c.ob_symchar->sy_dimension);
    }

INT c_sc_d(a,b) OP a,b;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    c.ob_symchar->sy_dimension = b;
    return(OK);
    }

INT c_sc_p(a,b) OP a,b;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    c.ob_symchar->sy_parlist = b;
    return(OK);
    }

INT c_sc_w(a,b) OP a,b;
/* AK 140789 V1.0 */ /* AK 200891 V1.3 */
    {
    OBJECTSELF c;
    c = s_o_s(a);

    c.ob_symchar->sy_werte = b;
    return(OK);
    }

#endif /* CHARTRUE */

INT innermaxmofn(m,n,erg) OP m,n,erg;
    {
/* AK 091189 */
/* geschrieben fuer regev, diese routine berechnet fuer
eingebe 
INTEGER m
INTEGER n die zerlegung der summe der inneren tensorquadrate der
partitionen von n die hoechstens m teile haben 
ergebnis ist vom typ SCHUR 
*/
/* AK 200891 V1.3 */
#ifdef CHARTRUE
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();
    OP d = callocobject();
    first_partition(n,a);
    do {
       if (le(s_pa_l(a),m)) {
        m_part_sc(a,b);mult(b,b,c);
        add(c,d,d);
        }
       } while(next(a,a));
    reduce_symchar(d,erg);
    freeall(a); freeall(b); freeall(c); freeall(d);
    return(OK);
#endif /* CHARTRUE */
    }


#ifdef CHARTRUE
#ifdef KOSTKATRUE
INT young_tafel(a,res,ct,kt) OP a, res, ct, kt;
/* AK Mon Jan 23 09:59:22 MEZ 1989 */
/* a ist dimension res wird MATRIX
ct ist wenn ungleich NULL die charatertafel
kt ist wenn ungleich NULL die kostkatafel */
/* AK 200789 V1.0 */ /* AK 020290 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* a and res may be equal */
    {
    OP zw    /* zwischenergebnis */,
        hct,hkt;
    INT i,j,k,dim;
    INT erg = OK;
    C1R(a,"young_tafel",res);


    if (a == res)
        {
        zw = callocobject();
        erg += copy(a,zw);
        erg += young_tafel(zw,res,ct,kt);
        erg += freeall(zw);
                goto endr_ende;
        }

    dim = numberofpart_i(a);
    erg += m_ilih_nm(dim,dim,res);

    if (ct == NULL) 
        { 
        hct = callocobject(); 
        erg += chartafel(a,hct);    
        }
    else    hct = ct;
    if (kt == NULL) 
        { 
        hkt = callocobject(); 
        erg += kostka_tafel(a,hkt);    
        }
    else    hkt = kt;

    /* hct und hkt zeigen nun auf charactertafel und kostkatafel */
    /* um den youngcharacter zu berechnen sind nur mehr multiplikation
    von zeilen und spalten noetig */

    zw = callocobject(); 
    for (i=(INT)0; i<S_M_HI(res); i++)
       for (j=(INT)0; j<S_M_HI(res); j++)
        {
        for (k=(INT)0; k<S_M_HI(res); k++)
            { 
            erg += mult(S_M_IJ(hkt,i,k),S_M_IJ(hct,k,j),zw);
            erg += add_apply(zw,S_M_IJ(res,i,j)); 
            }
        };

    if (kt == NULL) 
        erg += freeall(hkt);
    if (ct == NULL) 
        erg += freeall(hct);
    /* die berechneten tafeln werden wieder geloescht */

    erg += freeall(zw);

    S1R(a,"young_tafel",res);
    ENDR("young_tafel");
    }
#endif /* KOSTKATRUE */




INT m_part_youngsc(a,b) OP a,b;
/* AK 020591 V1.2 */ /* AK 200891 V1.3 */
    {
    return young_character(a,b,NULL);
    }

INT young_character(a,res,yt) OP a,res,yt;
/* AK Mon Jan 23 13:04:51 MEZ 1989    */
/* a ist PARTITION res wird SYMCHAR 
yt ist NULL oder sonst young_tafel */
/* AK 200789 V1.0 */ /* AK 100190 V1.1 */ /* AK 020591 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* a and res may be equal */
    {
    OP hyt;
    OP d;
    INT i,j,erg=OK;

    d = callocobject(); 

    if (a == res)
        {
        erg += copy(a,d);
        erg += young_character(d,res,yt);
        erg += freeall(d);
        goto endr_ende;
        }

    erg += weight(a,d);
    if  (yt == NULL) 
        { 
        hyt = callocobject(); 
        erg += young_tafel(d,hyt,NULL,NULL); 
        }
    else    
        hyt = yt;

    /* hyt zeigt nun auf youngtafel, nun nurmehr zeile rauslesen */
    erg += b_d_sc(d,res);
    i = indexofpart(a);

    for (j=(INT)0; j<S_SC_PLI(res); j++)
        erg += copy(S_M_IJ(hyt,i,j),S_SC_WI(res,j));

    if (yt == NULL) 
        erg += freeall(hyt);
    
    ENDR("young_character");
    }

#endif /* CHARTRUE */

#ifdef CHARTRUE
#ifdef MATRIXTRUE
INT young_scalar_tafel(n,res,yt) OP n,res,yt;
/* AK Tue Jan 24 07:24:26 MEZ 1989 */
/* tafel der skalar produkte der young_charactere
n ist INTEGER dimension
res wird MATRIX des ergebnis
yt ist wenn != NULL die young_tafel */
/* AK 200789 V1.0 */ /* AK 260790  V1.1 */ /* AK 200891 V1.3 */
    {
    OP hyt, vecpart = callocobject(); 
    OP convec = callocobject();  /* vector mit der konjugiertenklassen
                        ordnung */
    INT i,j,k,dim;
    makevectorofpart(n,vecpart);
    dim = S_V_LI(vecpart);
    m_il_v(dim,convec);
    for (k=(INT)0;k<dim;k++) 
        ordcon(S_V_I(vecpart,k), S_V_I(convec,k));
    m_ilih_m(dim,dim,res);
    if (yt == NULL) 
        { 
        hyt = callocobject(); 
        young_tafel(n,hyt,NULL,NULL);
        }
    else    
        hyt = yt;
    /* hyt zeigt auf youngtafel */
    for ( i=(INT)0;i<S_M_HI(res);i++)
      for ( j=(INT)0;j<S_M_HI(res);j++)
        char_matrix_scalar_product(hyt,i,hyt,j,vecpart,S_M_IJ(res,i,j),
        convec);
    if (yt == NULL) 
        freeall(hyt);
    freeall(vecpart); 
    freeall(convec); 
    return(OK);
    }
#endif /* MATRIXTRUE */
#endif /* CHARTRUE */

#ifdef CHARTRUE
#ifdef MATRIXTRUE
INT young_alt_scalar_tafel(n,res,yt) OP n,res,yt;
/* AK Tue Jan 24 09:05:18 MEZ 1989 */
/* tafel der skalar produkte des young_characters
mit dem young_character * alternierenden character
n ist INTEGER dimension
res wird MATRIX des ergebnis
yt ist wenn != NULL die young_tafel */
/* AK 200789 V1.0 */ /* AK 260790  V1.1 */ /* AK 200891 V1.3 */
    {
    OP hyt;
    OP vecpart = callocobject(); 
    OP hat = callocobject();  /* wird tafel des alternierenden mal 
        youngcharacter */
    OP altchar = callocobject(); /* alternierender character */
    OP lastpart = callocobject(); /* index des alt. character */
    INT i,j,k,dim;
    OP convec = callocobject();  
                

    makevectorofpart(n,vecpart);
    dim = S_V_LI(vecpart);
    m_il_v(dim,convec);
    for (k=(INT)0;k<dim;k++) ordcon(S_V_I(vecpart,k), S_V_I(convec,k));
    m_ilih_m(dim,dim,res);
    if (yt == NULL) { hyt = callocobject(); young_tafel(n,hyt,NULL,NULL);}
    else    hyt = yt;
    /* hyt zeigt auf youngtafel */
    last_partition(n,lastpart);
    m_part_sc(lastpart,altchar);
    copy(hyt,hat);
    for ( i=(INT)0;i<S_M_HI(res);i++)
      for ( j=(INT)0;j<S_M_HI(res);j++)
        mult(S_SC_WI(altchar,j),S_M_IJ(hat,i,j),S_M_IJ(hat,i,j));
    freeall(altchar);freeall(lastpart);
    for ( i=(INT)0;i<S_M_HI(res);i++)
      for ( j=(INT)0;j<S_M_HI(res);j++)
        char_matrix_scalar_product
                    (hyt,i,hat,j,vecpart,
                    S_M_IJ(res,i,j),
                    convec);
    if (yt == NULL) freeall(hyt);
    freeall(vecpart); freeall(hat); freeall(convec); return(OK);
    }
#endif /* MATRIXTRUE */
#endif /* CHARTRUE */

#ifdef CHARTRUE
INT test_symchar() 
/* AK 200891 V1.3 */
    {
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();
    FILE *fp1, *fp2;

    printf("test_symchar:scan(a)"); scan(SYMCHAR,a);println(a);
    printf("test_symchar:add(a,a,b)"); add(a,a,b); println(b);
    printf("test_symchar:add_apply(a,b)"); add_apply(a,b); println(b);
    printf("test_symchar:mult(a,b,b)"); mult(a,b,b); println(b);
    printf("test_symchar:mult_apply(a,b)"); mult_apply(a,b); println(b);
    printf("test_symchar:reduce_symchar(b,c)");
        reduce_symchar(b,c); println(c);
    printf("test_symchar:M_I_I(-1L,c);mult(c,b,b)");
    M_I_I(-1L,c); mult(c,b,b); println(b);
    printf("test_symchar:objectwrite(,b)");
    fp1 = fopen("klo","w"); objectwrite(fp1,b); fclose(fp1);
    printf("test_symchar:objectread(,b)");
    fp2 = fopen("klo","r"); objectread(fp2,b); fclose(fp2); println(b);
    printf("test_symchar:tex(b)"); tex(b);
    printf("test_symchar:hoch(a,cons_zwei,b)"); 
    hoch(a,cons_zwei,b); println(b);
    printf("test_symchar:scalarproduct(a,b,b)"); scalarproduct(a,b,b); 
    println(b);
    printf("test_symchar:charvalue(a,b,c);scan(PARTITION,a)");
    scan(PARTITION,a);
    printf("test_symchar:charvalue(a,b,c);scan(PERMUTATION,b)");
    scan(PERMUTATION,b);
    printf("test_symchar:charvalue(a,b,c)");charvalue(a,b,c,NULL);
    println(c);
    printf("test_symchar:M_I_I(7L,c);chartafel(c,b)");
    M_I_I(7L,c); chartafel(c,b); println(b);
    printf("test_symchar:M_I_I(7L,c);young_tafel(c,b)");
    M_I_I(7L,c); young_tafel(c,b,NULL,NULL); println(b);
    printf("test_symchar:M_I_I(7L,c);an_tafel(c,b)");
    M_I_I(7L,c); an_tafel(c,b); println(b);

    freeall(a);freeall(b);freeall(c);
    return(OK);
    }
    
#endif /* CHARTRUE */
/* now follows spechts method to compute an irreducible character */

#ifdef CHARTRUE
INT specht_m_part_sc(a,b) OP a,b;
/* AK 200891 V1.3 */
{
    OP c = callocobject();
    INT erg = OK;
    erg += specht_irred_characteristik(a,c);
    erg += characteristik_to_symchar(c,b);
    erg += freeall(c);
    return erg;
}
#endif /* CHARTRUE */
#ifdef MATRIXTRUE
#ifdef CHARTRUE
INT specht_irred_characteristik(a,b) OP a,b;
/* input PARTITION a
   output POLYNOM b */
/* AK 200891 V1.3 */
{
    INT i,j;
    OP c,d;
    if (S_O_K(a) != PARTITION) 
        return error("specht_ireed_characteristik: not PART");
    c = callocobject();
    if (S_PA_K(a) != VECTOR) 
        {
        t_EXPONENT_VECTOR(a,c);
        i = specht_irred_characteristik(c,b);
        freeall(c);
        return i;
        }
    d = callocobject();
    m_ilih_m(S_PA_LI(a),S_PA_LI(a),c);
    for (i=(INT)0;i<S_PA_LI(a);i++)
        for (j=(INT)0;j<S_PA_LI(a);j++)
            {
            m_i_i(S_PA_II(a,S_PA_LI(a)-1L-i)+j-i,d);
            specht_powersum(d,S_M_IJ(c,i,j));
            }
    det_imm_matrix(c,b);
    freeall(c); freeall(d);
    return OK;
}
#endif /* MATRIXTRUE */
#endif /* CHARTRUE */

#ifdef CHARTRUE
INT specht_powersum(a,b) OP a,b;
/* input INTEGERobject a
   output POLYNOMobject */
/* AK 200891 V1.3 */
{
    static OP speicher = NULL; /* for the computed results */
    OP c,d,e,f,g;
    INT j;
    if (S_O_K(a) != INTEGER) return error("specht_powersum:a != INTEGER");
    if (nullp(a)) return m_scalar_polynom(cons_eins,b);
    if (negp(a)) return m_scalar_polynom(cons_null,b);
    if (S_I_I(a) >= (INT)100) return error("specht_powersum:a too big");

    if (speicher == NULL) { 
            speicher = callocobject();m_il_v((INT)100,speicher); }
    if (not EMPTYP(S_V_I(speicher, S_I_I(a)))) 
        return copy(S_V_I(speicher, S_I_I(a)),b);

    /* not yet computed */
    c = callocobject(); d = callocobject(); g=callocobject();
    e = callocobject(); f = callocobject();
    if (not EMPTYP(b)) freeself(b);
    first_part_EXPONENT(a,c);
    do {
        b_skn_po(callocobject(),callocobject(),NULL,d);
        m_il_v(S_PA_LI(c),S_PO_S(d));
        for (j=(INT)0;j<S_PA_LI(c);j++)
            m_i_i(S_PA_II(c,j), S_PO_SI(d,j) );
        /* now the exponents of the monom are ok */
        m_i_i((INT)1,g);
        for (j=(INT)0;j<S_PA_LI(c);j++)
            {
            fakul(S_PA_I(c,j), e);
            /* div(S_PO_K(d),e,S_PO_K(d)); */
            m_i_i(j+(INT)1,f);
            hoch(f,S_PA_I(c,j),f); mult_apply(e,f);
            mult_apply(f,g);
            /* div(S_PO_K(d),f,S_PO_K(d)); */
            }
        invers(g,S_PO_K(d));
        add_apply(d,b);
    } while(next(c,c));

    freeall(c); freeall(d); freeall(e); freeall(f); freeall(g);
    copy(b, S_V_I(speicher, S_I_I(a)));
    return OK;
}


INT characteristik_to_symchar(a,b) OP a,b;
/* input: characteristik a
   output: coressponding sym character b */
/* AK 200891 V1.3 */
{
    INT i,j,oben,unten,mitte;
        INT erg = OK;
    OP z = a;
    OP c,d,e,f,h;
        CTO(POLYNOM,"characteristik_to_symchar(1)",a);
    c = callocobject(); d = callocobject();
    e = callocobject(); f = callocobject();
    h = callocobject();

    m_ks_pa(EXPONENT,S_PO_S(z),d);
    weight (d,c); /* c is the degree of the symm group */
    m_d_sc(c,b);  /* b is a SYMCHAR object */
    m_il_v(S_SC_WLI(b),h);
    for (i=(INT)0;i<S_SC_PLI(b);i++)
        t_VECTOR_EXPONENT(S_SC_PI(b,i),S_V_I(h,i));
    while (z != NULL)
        {
        m_ks_pa(EXPONENT,S_PO_S(z),c);
        t_EXPONENT_VECTOR(c,d);
        unten=(INT)0;oben=S_V_LI(h)-(INT)1;
aaa:
        mitte = unten + (oben-unten) /2L;
        if ((i=comp_colex_part(d,S_SC_PI(b,mitte))) == (INT)0)  
            {i = mitte;goto aab;}
        else if (i>(INT)0)  unten=mitte+(INT)1; 
        else oben=mitte-(INT)1;
        if ( oben < unten ) {
            fprintln(stderr,d);
            fprintln(stderr,h);
            error("characteristik_to_symchar:part not found");
            }
        goto aaa;
aab:    /* part gefunden */
        /* i = indexofpart(c); */
        copy(S_PO_K(z), S_SC_WI(b,i));
        for (j=(INT)0;j<S_PA_LI(c);j++)
            {
            fakul(S_PA_I(c,j), e);
            mult_apply(e,S_SC_WI(b,i));
            m_i_i(j+(INT)1,f);
            hoch(f,S_PA_I(c,j),f);
            mult_apply(f,S_SC_WI(b,i));
            }
        z = S_PO_N(z);
        }
    freeall(c); freeall(f); freeall(e); freeall(h); freeall(d); 
    ENDR("characteristik_to_symchar");
}



INT characteristik_symchar(a,b) OP a,b;
/* AK 020191 */
/* enter symchar a 
   out:  polynom b */
/* AK 200891 V1.3 */
{
    INT i,j;
    OP c = callocobject();
    OP d = callocobject();
    OP e = callocobject();
    OP f = callocobject();

    if (not EMPTYP(b)) freeself(b);

    for (i = (INT)0; i< S_SC_PLI(a); i++)
        {
        t_VECTOR_EXPONENT(S_SC_PI(a,i),c);
        b_skn_po(callocobject(),callocobject(),NULL,d);
        m_il_v(S_SC_DI(a),S_PO_S(d));
        for (j=(INT)0;j<S_SC_DI(a);j++)
            if (j >= S_PA_LI(c) ) m_i_i((INT)0,S_PO_SI(d,j));
            else m_i_i(S_PA_II(c,j), S_PO_SI(d,j) );
        /* now the exponents of the monom are ok */
        copy(S_SC_WI(a,i) , S_PO_K(d) );
        for (j=(INT)0;j<S_PA_LI(c);j++)
            {
            fakul(S_PA_I(c,j), e);
            div(S_PO_K(d),e,S_PO_K(d));
            m_i_i(j+(INT)1,f);
            hoch(f,S_PA_I(c,j),f);
            div(S_PO_K(d),f,S_PO_K(d));
            }
        add(d,b,b);
        }

    freeall(c); freeall(d); freeall(e); freeall(f);
    return OK;
}



INT c_ijk_sn(a,b,c,g) OP a,b,c,g;
/* structur constanten classen multiplikation in s_n
Curtis Reiner Methods of representation theory I p.216
AK 020891 V1.3 */
{
    return c_ijk_sn_tafel(a,b,c,g,NULL);
}


INT c_ijk_sn_tafel(a,b,c,g,ct) OP a,b,c,g,ct;
/* ct may be the corresponding charactertable 
   or NULL */
/* AK 150206 C3.0 */
{
    OP d,e,f,h,h2;
    INT i,erg=OK;

    CTO(PARTITION,"c_ijk_sn(1)",a);
    CTO(PARTITION,"c_ijk_sn(2)",b);
    CTO(PARTITION,"c_ijk_sn(3)",c);
    if (a == g) {
        e = CALLOCOBJECT();
        SWAP(g,e);
        erg += c_ijk_sn_tafel(e,b,c,g,ct);
        FREEALL(e);
        goto endr_ende;
        }
    if (b == g) {
        e = CALLOCOBJECT();
        SWAP(g,e);
        erg += c_ijk_sn_tafel(a,e,c,g,ct);
        FREEALL(e);
        goto endr_ende;
        } 
    if (c == g) {
        e = CALLOCOBJECT();
        SWAP(g,e);
        erg += c_ijk_sn_tafel(a,b,e,g,ct);
        FREEALL(e);
        goto endr_ende;
        } 


    d=callocobject(); 
    e=callocobject(); 
    f=callocobject(); 
    h=callocobject(); 
    h2=callocobject(); 

    erg += weight_partition(a,d);
    erg += weight_partition(b,h2);
    if (neq (d,h2) )
        {
        erg += error("c_ijk_sn_tafel: different weights of partitions");
        goto ee;
        }
    erg += weight(c,h2);
    if (neq (d,h2) )
        {
        erg += error("c_ijk_sn_tafel: different weights of partitions");
        goto ee;
        }
    erg += makevectorofpart(d,e);
    erg += ordcon(a,f); 
    erg += ordcon(b,g);
    erg += mult_apply(f,g); 
    erg += m_i_i((INT)0,h);
    if (ct == NULL) {
        for (i=(INT)0;i<S_V_LI(e);i++)
            {
            erg += charvalue(S_V_I(e,i),a,f,NULL);
            erg += charvalue(S_V_I(e,i),b,h2,NULL);
            MULT_APPLY(f,h2);
            erg += charvalue(S_V_I(e,i),c,f,NULL);
            MULT_APPLY(f,h2);
            erg += dimension(S_V_I(e,i),f);
            erg += div_apply(h2,f); /* h2 = h2/f */
            ADD_APPLY(h2,h);
            }
        }
    else {
        INT ai,bi,ci;
        ai = indexofpart(a);
        bi = indexofpart(b);
        ci = indexofpart(c);
        

        for (i=(INT)0;i<S_V_LI(e);i++)
            {
            FREESELF(h2);
            MULT(S_M_IJ(ct,i,ai), S_M_IJ(ct,i,bi), h2);
            MULT_APPLY(S_M_IJ(ct,i,ci),h2);
            erg += div_apply(h2,S_M_IJ(ct,i,S_V_LI(e)-1)); /* dimension */
            ADD_APPLY(h2,h);
            }
        }
    MULT_APPLY(h,g);
    erg += fakul(d,f);
    erg += div_apply(g,f);

ee:
    FREEALL5(d,e,f,h,h2); 
    ENDR("c_ijk_sn_tafel");
}

static INT co_290802(ai,bi,ci,f,ct,factor) INT ai,bi,ci; OP f,ct,factor;
/* special verison of c_ijk_sn */
{
    INT i;
    INT erg = OK;
    OP h2;
    h2 = CALLOCOBJECT();
    m_i_i(0,f);
    
    for (i=(INT)0;i<S_M_HI(ct);i++)
        {
        FREESELF(h2);
        MULT(S_M_IJ(ct,i,ai), S_M_IJ(ct,i,bi), h2);
        MULT_APPLY(S_M_IJ(ct,i,ci),h2);
        erg += div_apply(h2,S_M_IJ(ct,i,S_M_LI(ct)-1)); /* dimension */
        ADD_APPLY(h2,f);
        }                                                                                 
    MULT_APPLY(factor,f);
    FREEALL(h2);
    ENDR("internal:co_290802");
}


INT c_ij_sn(a,b,c) OP a,b,c;
{
    return class_mult_part_part(a,b,c);
}

INT class_mult(a,b,c) OP a,b,c;
/* class multiplication in the symmetric group */
/* input may also be SCHUR, in this case these are class sums */
/* AK 280802 */
{
    INT erg = OK;
    CTTO(SCHUR,PARTITION,"class_mult(1)",a);
    CTTO(SCHUR,PARTITION,"class_mult(2)",b);
    CE3(a,b,c,class_mult);
    if (S_O_K(a) == PARTITION) {
        if (S_O_K(b) == PARTITION) 
            erg += class_mult_part_part(a,b,c);
        else /* SCHUR */
            {
            OP z,d;
            init(SCHUR,c);
            FORALL(z,b,{
                d = CALLOCOBJECT();
                class_mult_part_part(a,S_MO_S(z),d);
                MULT_APPLY(S_MO_K(z),d);
                insert(d,c,add_koeff,comp_monomschur);
                });
            }
        }
    else {
        if (S_O_K(b) == PARTITION) 
            {
            OP z,d;
            init(SCHUR,c);
            FORALL(z,a,{
                d = CALLOCOBJECT();
                class_mult_part_part(b,S_MO_S(z),d);
                MULT_APPLY(S_MO_K(z),d);
                insert(d,c,add_koeff,comp_monomschur);
                });
            }
        else /* two schur functions */
            {
            OP z1,z2,d;
            init(SCHUR,c);
            FORALL(z1,a,{
               FORALL(z2,b,{
                  d = CALLOCOBJECT(); 
                  class_mult_part_part(S_MO_S(z2),S_MO_S(z1),d);
                  MULT_APPLY(S_MO_K(z1),d);
                  MULT_APPLY(S_MO_K(z2),d);
                  insert(d,c,add_koeff,comp_monomschur);
                  });
               });
            }
        }
        
    ENDR("class_mult");
}

INT class_mult_part_part(a,b,c) OP a,b,c;
/* complete expansion of class multiplication
   result: SCHUR
   input: two partitions of the same weight */
/* AK 270802 */
{
   INT erg = OK;
   CTO(PARTITION,"class_mult_part_part(1)",a);
   CTO(PARTITION,"class_mult_part_part(2)",b);
   {
   OP d,e,f,ct,factor;
   INT ai,bi,ei;
   d = callocobject();
   e = callocobject();
   weight(a,d);
   weight(b,e);
   if (neq(d,e)) {
       error("class_mult_part_part:partitions of different weight");
       goto ee;
       }
   f = callocobject();
   ct = callocobject();
   factor = callocobject();
   ordcon(a,factor);
   ordcon(b,f); mult_apply(f,factor);
   fakul(e,f); div_apply(factor,f);
   /* factor is computed */

   chartafel(e,ct);
   init(SCHUR,c);
   first_partition(d,e);
   ai = indexofpart(a);
   bi = indexofpart(b);
   ei = 0;
   do  {
       co_290802(ai,bi,ei,f,ct,factor);
       if (not nullp(f)) {
           OP m;
           m = callocobject();
           m_sk_mo(e,f,m);
           insert(m,c,add_koeff,comp_monomschur);
           }
       ei++;
       }
   while (next_apply(e));
   FREEALL(f);
   FREEALL(ct);
   FREEALL(factor);
ee:
   erg += freeall(d);
   erg += freeall(e);
   }
   ENDR("class_mult_part_part");
}



#ifdef SCHURTRUE
INT t_SCHUR_SYMCHAR(a,b) OP a,b;
/* input SCHUR output character */
{
    OP z = a;
    OP c;
    INT erg = OK;

    if (S_O_K(a) != SCHUR) 
        {
        cast_apply_schur(a); /* AK 280494 */
        if (S_O_K(a) != SCHUR) 
            return WTO("t_SCHUR_SYMCHAR",a);
        }

    CE2(a,b,t_SCHUR_SYMCHAR);
    c = callocobject();

    while(z != NULL)
        {
        erg += m_part_sc(S_S_S(z),c);
        erg += mult_apply(S_S_K(z),c);
        if (z != a)
            erg += add_apply(c,b);
        else
            erg += swap(c,b);
        z = S_S_N(z);
        }
    erg += freeall(c);

    ENDR("t_SCHUR_SYMCHAR");
}
#endif /* SCHURTRUE */


INT vminus_tabloid(a,b) OP a,b;
/* eingabe tableau, ausgabe tabloid */
/* AK 270295 */
{
    OP f,g,x,z,h;
    INT erg = OK;
    CTO(TABLEAUX,"vminus_tabloid(1)",a);
    CE2(a,b,vminus_tabloid);

    x = callocobject();
    f = callocobject();
    g = callocobject();
    erg += vminus(a,f);
    z =f;
    erg += init(LIST,b);
    while (z!=NULL) {
        erg += operate_perm_tableaux(S_PO_S(z),a,x);
        h=callocobject();
        erg += sort_rows_tableaux_apply(x);
        erg += m_sk_mo(x,S_PO_K(z),h);
        insert(h,b,add_koeff,NULL);
        z = S_PO_N(z);
    }
    erg += freeall(x);
    erg += freeall(f);
    erg += freeall(g);

    ENDR("vminus_tabloid");
}

#endif /* CHARTRUE */
