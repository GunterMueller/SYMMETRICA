/* SYMMETRICA     nb.c */
/* 4.11.91: TPMcD */

#include       <math.h>
/* #include       <ctype.h> AK 200206 */  /* for isspace AK 160192 */




#include "def.h"
#include "macro.h"

int myisspace (int i) 
	{
        if (i=='\t') return 1;
        if (i=='\n') return 1;
        if (i=='\r') return 1;
        if (i=='\v') return 1;
        if (i=='\f') return 1;
        if (i==' ') return 1;
	return 0;
	}


#define INIT_CYCLO(a) \
do {\
erg +=  b_ksd_n(CYCLOTOMIC, CALLOCOBJECT(), NULL, a);\
} while(0)


#define  nb_quores(a,b,c,d) quores(a,b,c,d) /* AK 050393 */

static INT      space_saving = TRUE;
static INT    basis_type = STD_BASIS;

/*    STATIC VARIABLES RELATING TO THE MAINTENANCE OF CYCLOTOMIC DATA    */

#ifdef    CYCLOTRUE

/*    cyclo_table points to an array of CYCLO_DATA with     */
/*    no_cyclos cyclos.  cyclo_table_set is a flag which    */
/*    indicates whether the table is present or not.        */

static    INT    cyclo_table_set = 0L, cyclo_list_set = 0L;
static    INT    zzno_cyclos;
static    CYCLO_DATA    *zzcyclo_table;
static    OP    zzcyclo_list = NULL, zzcyclo_tail = NULL;
static INT number_mem;

#endif /* CYCLOTRUE */

static INT setup_prime_table();
static INT integer_factor_0();
static INT integer_factor_1();
static INT insert_zero_into_monopoly();
static INT integer_coefficients();
static INT find_sqrad_data();
static INT adjust_sqrad_data();
static INT fprint_sqrad();
static INT fprint_cyclo();
static INT standardise_cyclo_0();
static INT make_index_monopoly_cyclo();
static INT add_cyclo_cyclo_0();
static INT mult_cyclo_cyclo_0();
static INT invers_cyclo_norm();
static INT SCMPCO();

# ifdef    CYCLOTRUE

static INT setup_cyclotomic_table();
static CYCLO_DATA *cyclo_ptr();
static CYCLO_DATA *add_cyclo_data();
static INT free_cyclo_list();
static INT free_cyclo_table();

# endif
OP s_n_s(a) OP a;
/* AK 080891 V1.3 */
{    
    if (a == NULL)
    {    
        error("s_n_s:a == NULL");
        return (OP) NULL;
    }
    return (((a)->ob_self).ob_number)->n_self;
}

INT c_n_s(a,b) OP a,b;
/* AK 200891 V1.3 */
{     
    ((a->ob_self).ob_number)->n_self = b;
    return OK;
}

OP s_n_d(a) OP a;
/* AK 200891 V1.3 */
{    
    if (a == NULL)
    {    
        error("s_n_d:a == NULL");
        return (OP) NULL;
    }
    return (((((a)->ob_self).ob_number)->n_data).o_data);
}

INT c_n_d(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    ((((((a)->ob_self).ob_number)->n_data).o_data) = (b));
    return OK;
}

OP s_n_dci(a) OP a;
/* AK 200891 V1.3 */
{    
    return ((((((a)->ob_self).ob_number)->n_data).c_data)->index);
}

OP s_n_dcd(a) OP a;
/* AK 200891 V1.3 */
{    
    return ((((((a)->ob_self).ob_number)->n_data).c_data)->deg);
}

OP s_n_dcp(a)OP a;
/* AK 200891 V1.3 */
{    
    return  ((((((a)->ob_self).ob_number)->n_data).c_data)->poly);
}

/******************        factors.c        **********************/
/* 26.07.91: TPMcD.                                             */
/*************************************************************/
/*    Determines and returns the number of digits of the    */
/*    integer a. a may be an INTEGER  or a LONGINT.        */

INT number_of_digits(a) OP a;
/* 04.04.90: TPMcD */
/* AK 200891 V1.3 */
{    
    INT    i = 1L;
    OP    b = CALLOCOBJECT();    
    OP ten = CALLOCOBJECT();

    M_I_I(10L,ten);
    copy(a,b);
    if (LT(b,cons_null) == TRUE)
        addinvers_apply(b);

    while (GE(b,ten) == TRUE)
    {    
        ganzdiv(b,ten,b); 
        i++; 
    }
    freeall(b); 
    freeall(ten);
    return(i);
}

INT number_of_bits(a) OP a;
/* 04.04.90: TPMcD */
/* AK 200891 V1.3 */
/* AK 300102 */
/* AK 180902 V2.1 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"number_of_bits(1)",a);
    {
    INT    i = 1L;
    OP b,ten;

    if (S_O_K(a) == INTEGER) /* AK 280705 */
        {
        INT ai = S_I_I(a);
        while (ai >= 2) { ai /= 2; i++; }
        return i;
        }

    b = CALLOCOBJECT();
 
    COPY(a,b);
    if (LT(b,cons_null) == TRUE)
        ADDINVERS_APPLY(b);
 
    while (GE(b,cons_zwei) == TRUE)
    {
        ganzdiv(b,cons_zwei,b);
        i++;
    }
    freeall(b);
    return(i);
    }
    ENDR("number_of_bits");
}


INT integer_factors_to_integer(l,a) OP l,a;
/* 10.05.90: TPMcD */
/* AK 200891 V1.3 */
/* 01.10.91: TPMcD */
{    
    INT    ret    = ERROR;
#ifdef    MONOPOLYTRUE
    OP    b = CALLOCOBJECT();
    OP    ptr;

    if (S_O_K(l) != MONOPOLY)
        goto exit_label;
    if (not EMPTYP(a))
        freeself(a);
    M_I_I(1L,a);
    ptr    = l;
    if (EMPTYP(S_PO_S(ptr)))
        ptr    = S_L_N(ptr);    /* skip the empty term    */
    while (ptr != NULL)
    {    
        hoch(S_PO_S(ptr),S_PO_K(ptr),b);
        mult(a,b,a);
        ptr    = S_L_N(ptr);
    }
    ret    = OK;
exit_label:
    freeall(b);
#else
    error("integer_factors_to_integer: MONOPOLY not available");
#endif
    return(ret);
}

/*Given the number n, which should be an positive INTEGER or LONGINT    */
/*or a MONOPOLY representing a factorisation of an integer greater    */
/*than 1 , the result returns the list of positive integers coprime to n.*/

INT make_coprimes(number,result) OP number, result;
/* 01.05.91: TPMcD */ /* AK 200891 V1.3 */ /* 01.10.91: TPMcD */
{    
    INT    end_flag = 0L, flag= -1L; /* AK 040292 */
    INT    erg    = ERROR;
    OP    ptr, ptr_zwei, ptr_drei, num=NULL;
#ifdef MONOPOLYTRUE
    OP    new, list=NULL;
    OP vec,prime,count_eins,count_zwei;

    CTTTO(INTEGER,MONOPOLY,LONGINT,"make_coprimes(1)",number);

    vec = CALLOCOBJECT();
    prime = CALLOCOBJECT();
    count_eins = CALLOCOBJECT();
    count_zwei = CALLOCOBJECT();

    init(LIST,result);
    if (S_O_K(number) == MONOPOLY)
    {    
        list    = number;
        num    = CALLOCOBJECT();
        flag    = 1L;    /* remember to free num    */
        integer_factors_to_integer(list,num);
    }
    else
    {    
        if (((S_O_K(number) != INTEGER) && (S_O_K(number) != LONGINT))
            || (LT(number,cons_eins) == TRUE))
            goto exit_label;
        if (EQ(number,cons_eins) == TRUE)
        {    
            new    = CALLOCOBJECT();
            M_I_I((INT)1,new);
            insert(new,result,NULL,NULL);
            erg    = OK;
            goto exit_label;
        }
        num    = number;
        list    = CALLOCOBJECT();
        flag    = 0L;    /* remember to free list    */
        integer_factor(num,list);
    }
    m_i_i((INT)1,count_eins);
    init(LIST,vec);
    ptr    = vec;
    while (TRUE)
    {    /*    vec is initialised to the list of numbers 1 , . . ., num    */
        S_L_S(ptr)    = CALLOCOBJECT();
        copy(count_eins,S_L_S(ptr));
        if (LT(count_eins,num) == TRUE)
        {    
            new    = CALLOCOBJECT();
            S_L_N(ptr)    = new;
            ptr    = new;
            init(LIST,new);
            INC(count_eins);
        }
        else
        {    
            S_L_N(ptr)    = NULL;
            break;
        }
    }
    ptr    = list;
    while (ptr != NULL)
    {    
        copy(S_PO_S(ptr),prime);
/*
        copy(cons_eins,count_eins);
        copy(cons_eins,count_zwei);
*/
	M_I_I(1,count_eins);
	M_I_I(1,count_zwei);
        ptr_zwei    = vec;
        while (LE(count_eins,num) == TRUE)
        {    /*    delete all multiples of prime from vec    */
            if (EQ(count_zwei,prime) == TRUE)
            {    
/*
                copy(cons_eins,count_zwei);
*/
		M_I_I(1,count_zwei);
                if (not EMPTYP(S_L_S(ptr_zwei))) /* AK */
                    FREESELF(S_L_S(ptr_zwei));
            }
            else
                INC_INTEGER(count_zwei);
            INC_INTEGER(count_eins);
            ptr_zwei    = S_L_N(ptr_zwei);
        }
        ptr    = S_L_N(ptr);
    }
    ptr    = result;
    ptr_drei    = result;
    copy(cons_eins,count_eins);
    ptr_zwei    = vec;
    while (TRUE)
    {    
        if (EQ(count_eins,num) == TRUE)
            end_flag    = 1L;
        if (not EMPTYP(S_L_S(ptr_zwei)))
        {    
            S_L_S(ptr)    = CALLOCOBJECT();
            copy(count_eins,S_L_S(ptr));
            if (end_flag)
            {    
                S_L_N(ptr)    = NULL;
                break;
            }
            else
            {    
                new    = CALLOCOBJECT();
                init(LIST,new);
                S_L_N(ptr)    = new;
                ptr_drei    = ptr;
                ptr    = new;
            }
        }
        if (end_flag)
        {    
            freeall(ptr);
            S_L_N(ptr_drei)    = NULL;
            break;
        }
        INC(count_eins);
        ptr_zwei    = S_L_N(ptr_zwei);
    }
    erg    = OK;
exit_label:
	FREEALL4(vec,prime,count_eins,count_zwei);
    if (flag == 1L) freeall(num);
    else  if (flag != -1L) freeall(list); /* AK 040292 */
#endif
    ENDR("make_coprimes");
}

INT euler_phi(a,b) OP a,b;
/* AK number of numbers coprime to a */
/* AK 310191 V1.2 */ /* AK 200891 V1.3 */
{    
    OP c = CALLOCOBJECT();
    INT erg;
    erg    = make_coprimes(a,c);
    erg += length(c,b);
    erg += freeall(c);
    return erg;
}

INT prime_power_p(a) OP a;
/* AK 290304 true if power of a prime */
/* AK 161204 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"prime_power_p(1)",a);
    if (NULLP(a)) return FALSE;
    if (NEGP(a)) return FALSE;

    {
    OP b; INT res;
    b = CALLOCOBJECT();
    factorize(a,b);
    if (EQ(S_V_I(b,0),S_V_I(b,S_V_LI(b)-1))) res = TRUE;
    else res = FALSE;
    FREEALL(b); 
    return res;
    }

    ENDR("prime_power_p");
}

INT primep(a) OP a;
/* AK 220294 true if prime */
/* AK 161204 V3.0 */
{
    OP c,d,e;
    INT erg = TRUE;

    if (EQ(a,cons_zwei))
        {
        erg = TRUE;
        goto p1;
        }
    if (negp(a) || NULLP(a) || EVEN(a) )
        {
        erg = FALSE; 
        goto p1;
        }
    CALLOCOBJECT3(c,d,e);
    
    ganzsquareroot(a,c);
    M_I_I(3,d);
    while (le(d,c))
        {
        mod(a,d,e);
        if (NULLP(e) ) 
            { erg = FALSE; break; } 
        ADD_APPLY(cons_zwei,d);
        }
    FREEALL3(c,d,e);
p1:
    return erg;
    ENDR("primep");
}

/*    INTEGER SQUARE ROOTS    */

/*    If a is a non-negative integer (INTEGER or LONGINT)    */
/*    s is set to the integer part of its square root.    */
/*    In this case, the return value is OK or IMPROPER    */
/*    according as the integer is a perfect square or not.    */
/*    Otherwise, the return value is ERROR.            */

static INT nb_square_root(a,s) OP a,s;
/* 04.04.90: TPMcD */ /* AK 200891 V1.3 */
{    
    INT    a_eins,d_eins,e_eins,ret    = ERROR;
    INT erg = OK;
    OP b,c,d,e,diff;
    CTTO(INTEGER,LONGINT,"nb_square_root(1)",a);

    b = CALLOCOBJECT();    
    c = CALLOCOBJECT();
    d = CALLOCOBJECT();    
    e = CALLOCOBJECT();
    diff = CALLOCOBJECT();



    if (negp(a))    /* a < 0L */
    {    
        fprintf(stderr,"Negative number has no real square root\n");
        goto exit_label;
    }
    if (NULLP(a))
    {    
        m_i_i(0l,s);
        ret    = OK;
        goto exit_label;
    }
    d_eins    = number_of_digits(a);

    e_eins    = (d_eins + 1L) / 2L;

    M_I_I(10L,d);
    M_I_I(e_eins-1L,b);
    hoch(d,b,b);
    MULT(d,b,c);
    FREESELF(d); MULT(b,b,d);
    if (EQ(a,d) == TRUE)
    {    
        copy(b,s);
        ret    = OK;
        goto exit_label;
    }
    do
    {    
        FREESELF(d);
        ADD(b,c,d);
        if (negp(d))
            error("square_root : negative integer unexpectedly encountered\n");
        
        half_apply(d);
        FREESELF(diff);
        ADDINVERS(b,diff);
        ADD_APPLY(c,diff);
        FREESELF(e); MULT(d,d,e);
        a_eins    = COMP(a,e);
        if (a_eins < 0L)
            copy(d,c);
        else if (a_eins > 0L)
            copy(d,b);
        else
        {    
            copy(d,s);
            ret    = OK;
            goto exit_label;
        }

    }        while (GE(diff,cons_zwei) == TRUE);
    copy(b,s);
    ret = IMPROPER;
exit_label:
    FREEALL5(b,c,d,e,diff); 
    CTTO(INTEGER,LONGINT,"nb_square_root(e2)",s);
    return(ret);
    ENDR("nb_square_root");
}

#ifdef LONGINTTRUE
INT ganzsquareroot_longint(a,b) OP a,b;
/* AK 040291 */ /* AK 200891 V1.3 */
{
    INT erg ;
    erg = nb_square_root(a,b);
    return (erg == IMPROPER ? OK : erg); /* AK 200194 */
}
#endif /* LONGINTTRUE */

INT ganzsquareroot_integer(a,b) OP a,b;
/* AK 040291 */ /* AK 200891 V1.3 */
{
    INT erg ;
    erg = nb_square_root(a,b);
    return (erg == IMPROPER ? OK : erg); /* AK 200194 */
}

/*  INTEGER FACTORISATION    */

/*    Routines for prime factorization of integers.    */
/*    prime_table points to an array of INT with the first no_primes primes.*/
/*    prime_table_set is a flag which indicates whether the table is present*/
/*    or not.        */

static INT    prime_table_set    = 0L, no_primes;
static INT  *prime_table;

/*Reads the table of primes from the file PRIMES.DAT. The first entry    */
/*should be no_primes, then the list of primes.  Assumes that INT means    */
/*long int.  Returns OK if the table is set; otherwise, returns ERROR.    */

static INT setup_prime_table()
/* 040490 TPMcD */
/* AK 200891 V1.3 */
/* 29.10.91 TPMcD */
{
# ifdef PRIMES_FILE

    FILE    *f;
    if ( (f = fopen("PRIMES.DAT","r")) == NULL ||
        fscanf(f," %ld",&no_primes) == 0 || no_primes < 1L ||
        (prime_table = (INT *)SYM_calloc((int)no_primes,sizeof(INT))) == NULL )
    {    
        no_primes    = 0L;
        return(ERROR);
    }
    for (i=0L;i<no_primes;i++)
        if (fscanf(f," %ld",&prime_table[i]) != 1)
        {    
            SYM_free(prime_table);
            no_primes    = 0L;
            return(ERROR);
        }
    prime_table_set    = 1L;
# else
    no_primes    = 15L;
    if ((prime_table = (INT *)SYM_calloc((int)no_primes,sizeof(INT))) == NULL )
    {    
        no_primes    = 0L;        /* The previous version had incompatible */
        return(ERROR);            /* uses for prime_table in the two parts */
    }                            /* of the #ifdef construct */
    prime_table[0] = 2L;
    prime_table[1] = 3L;
    prime_table[2] = 5L;
    prime_table[3] = 7L;
    prime_table[4] = 11L;
    prime_table[5] = 13L;
    prime_table[6] = 17L;
    prime_table[7] = 19L;
    prime_table[8] = 23L;
    prime_table[9] = 29L;
    prime_table[10] = 31L;
    prime_table[11] = 37L;
    prime_table[12] = 41L;
    prime_table[13] = 43L;
    prime_table[14] = 47L;
    prime_table_set    = 1L;

# endif /* PRIMES_FILE */

    return(OK);
}

/*    This routine factorizes an integer using the table of primes.    */
/*    a -- the integer to be factored;                */
/*    l -- a list in which the prime factors of a, which are contain-    */
/*    ed in the table, and their exponents are inserted as monomials    */
/*    with the primes as the selfs and the exponents as the koeffs;    */
/*    g -- the remaining factor;                    */
/*    m -- the last number tried as a factor.                */
/*    first_prime -- the variable to point to the first prime factor    */
/*    if that is all that is required. For a full factorization, it    */
/*    must be set to NULL.                        */
/*    l must be a MONOPOLY. a,l,g,m and first_prime must be different.    */

#ifdef    MONOPOLYTRUE
static INT integer_factor_0(a,l,g,m,first_prime) OP a,l,g,m, first_prime;
/* 04.04.90: TPMcD */
/* AK 200891 V1.3 */
{    
    INT    i,erg    = ERROR;
    OP    b = CALLOCOBJECT(), c = CALLOCOBJECT(), d = CALLOCOBJECT(),
        e = CALLOCOBJECT(), k = CALLOCOBJECT(), f;

    if (S_O_K(a) != INTEGER && S_O_K(a) != LONGINT)
        goto exit_label;
    if (S_O_K(l) != MONOPOLY)
        goto exit_label;
    if (a == b || a == c || a == l || a == first_prime || b == c || b == l
        || a == first_prime  || c == l || c == first_prime|| l == first_prime)
        goto exit_label;
    copy(a,b);
    if (EQ(b,cons_eins) == TRUE)
    {    
        f    = CALLOCOBJECT();
        m_sk_mo(cons_eins,cons_eins,f);
        insert(f,l,add_koeff,NULL);
    }
    else if (LT(b,cons_null) == TRUE)
    {    
        addinvers_apply(b); /* AK 090891 */
        f    = CALLOCOBJECT();
        M_I_I(-1L,c);
        m_sk_mo(c,cons_eins,f);
        insert(f,l,add_koeff,NULL);
    }
    if (EINSP(b))
    {    
        erg    = OK;
        copy(b,g);
        copy(b,m);
        goto exit_label;
    }
    nb_square_root(b,e); /* e    = sqrt(a) */

    CTTO(INTEGER,LONGINT,"integer_factor_0(i1)",e);
    if (!prime_table_set)
        if (setup_prime_table() == ERROR) goto exit_label;
    for (i=0L;i<no_primes;i++)
    {    
        m_i_i(0,k);
        /* 29.10.91: TPMcD: type of prime_table changed back to INT[] */
        m_i_i((INT)prime_table[i],c);
        if (GT(c,e) == TRUE)    /*    all primes not greater than    */
        {                        /*    sqrt(b) have been tried.    */
            if (first_prime != NULL)
            {    
                copy(b,first_prime);
                erg    = OK;
                goto exit_label;
            }
            f    = CALLOCOBJECT();
            m_i_i(1L,d);
            m_sk_mo(b,d,f);
            insert(f,l,add_koeff,NULL);
            m_i_i(1L,b);
            break;
        }
        mod(b,c,d);

        while(NULLP(d))
        {    
            if (first_prime != NULL)
            {    
                copy(c,first_prime);
                erg    = OK;
                goto exit_label;
            }
            INC(k);
            ganzdiv(b,c,b);
            mod(b,c,d);
            nb_square_root(b,e); /* e    = sqrt(b) */
        }
        if (GT(k,cons_null) == TRUE)
        {    
            f    = CALLOCOBJECT();
            m_sk_mo(c,k,f);
            insert(f,l,add_koeff,NULL);
        }
        if (EINSP(b)) break;
            
    }
    erg    = OK;
    copy(b,g); 
    copy(c,m);
exit_label:
    FREEALL(b); 
    FREEALL(c); 
    FREEALL(d); 
    FREEALL(e); 
    FREEALL(k);
    CTO(MONOPOLY,"integer_factor_0(e2)",l);
    CTO(INTEGER,"integer_factor_0(e3)",g);
    ENDR("integer_factor_0");
}
#endif /* MONOPOLYTRUE */

/*    This routine finds all prime factors between two bounds                */
/*    a -- the integer to be factored;                                    */
/*    l -- a list in which the prime factors of a, between the given        */
/*    bounds, and their exponents are inserted as monomials                */
/*    with the primes as the selfs and the exponents as the koeffs;        */
/*    if l is not a MONOPOLY, it is initialised to one;                    */
/*    b -- the remaining factor;                                            */
/*    f_eins -- the lower bound on trial factors.                                */
/*    If it is even, it is replaced by f_eins+1.                                */
/*    f_zwei -- the upper bound on trial factors.                                */
/*    first_prime -- the variable to point to the first prime factor        */
/*    if that is all that is required. For a full factorization, it        */
/*    must be set to NULL.                                                */
/*    l must be a MONOPOLY. a,l,b,f_eins,f_zwei,first_prime must be different.    */

static INT integer_factor_1(a,f_eins,f_zwei,b,l,first_prime) OP a,f_eins,f_zwei,b,l,first_prime;
/* 04.04.90: TPMcD */
/* AK 200891 V1.3 */
{    
    INT    flag = 1L;
    INT erg = OK;
    INT    ret = ERROR, new_factor = 0L, myfirst = 1L;
#ifdef    MONOPOLYTRUE
    OP    c = CALLOCOBJECT(), f = CALLOCOBJECT(), e = CALLOCOBJECT(),
        e_eins = CALLOCOBJECT(), q = CALLOCOBJECT(), r = CALLOCOBJECT(),
        k, g;
    if (S_O_K(l) != MONOPOLY)
        init(MONOPOLY,l);
    copy(a,c);
    if (LT(c,cons_null) == TRUE)
    {    
        addinvers(c,c);
        M_I_I(1L,f);
        M_I_I(-1L,e);
        k = CALLOCOBJECT();
        m_sk_mo(e,f,k);
        insert(k,l,add_koeff,NULL);
    }
    k    = CALLOCOBJECT();
    copy(f_zwei,e);
    copy(f_eins,f);
    if (LT(f,cons_eins) == TRUE)    /* Make the initial divisor >= 2 */
        copy(cons_zwei,f);
    nb_quores(f,cons_zwei,q,r);
    if (nullp(r))
    {    
        if (einsp(q)) /*    f = 2    */
            flag = 0L;
        else    /*    f is even and greater than 2 */
            INC(f);
    }
    nb_quores(c,f,q,r);

    while (LE(f,e) == TRUE)
    {    
        while (nullp(r))
{    /* The value of c entering this loop is divisible
               by f exactly k times, where k refers to its
                       value exiting the loop. */
            if (first_prime != NULL)
            {    
                copy(f,first_prime);
                ret    = OK;
                goto exit_label;
            }
            if (myfirst)
            {    
                M_I_I(1L,k);
                new_factor    = 1L;
                myfirst    = 0L;
            }
            else
                INC(k);
            ganzdiv(c,f,c);
            nb_quores(c,f,q,r);
        }
        if (new_factor)
        {    /* make new monomial and insert in the factor list */
            g    = CALLOCOBJECT();
            m_sk_mo(f,k,g);
            insert(g,l,add_koeff,NULL);
            new_factor    = 0L;
            if (EQ(c,cons_eins) == TRUE)
                break;
            nb_square_root(c,e_eins);
            /* reduce the upper limit of the trial factors */
            if (LT(e_eins,e) == TRUE)
                copy(e_eins,e);
            /*    the current c is a prime or it has prime factors    */
            /*    are less than f_eins, and the factorization is 'complete'.    */
            if (LT(e,f) == TRUE)
                break;
        }
        myfirst    = 1L;
        /* Increase f by 2 and find corresponding q and r */
        INC(f);
        if (flag) INC(f);
        flag    = 1L;
        nb_quores(c,f,q,r);
    }
    copy(c,b);
    ret    = OK;
exit_label:
    freeall(c); 
    freeall(q); 
    freeall(r); 
    freeall(f); 
    freeall(k);
    freeall(e); 
    freeall(e_eins);
#else /* MONOPOLYTRUE */
    error("integer_factor_1: MONOPOLY not available");
#endif /* MONOPOLYTRUE */
    return(ret);
}

/*    This is the main integer factorization routine.        */
/*    a -- the integer to be factored;            */
/*    l -- a list in which the prime factors of a and their exponents    */
/*    are inserted as monomials with the primes as the selfs and the    */
/*    exponents as the koeffs. l need not be initialized to a MONOPOLY.    */

INT integer_factor(a,l) OP a,l;
/* 040490: TPMcD */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT    erg    = ERROR;

    OP b,c,d,e;
    CTTO(INTEGER,LONGINT,"integer_factor(1)",a);
    CE2(a,l,integer_factor);

    b = CALLOCOBJECT();
    c = CALLOCOBJECT();
    d = CALLOCOBJECT();
    e = CALLOCOBJECT();

    init(MONOPOLY,l);

    /*First factorize using the list of primes in "PRIMES.DAT"    */

    if (integer_factor_0(a,l,b,c,NULL) != OK)
    {    
        copy(a,b);
        M_I_I(1L,c);
    }
    if (EQ(b,cons_eins) == TRUE)    /*    Factorization complete.        */
    {    
        erg    = OK;
        goto exit_label;
    }
    copy(b,d);
    if (integer_factor_1(b,c,d,e,l,NULL) == OK)
    {
        /*    If e > 1 , it is a prime greater than those in l    */
        m_i_i(1L,c);
        if (gt(e,c) == TRUE)
        {    
            m_sk_mo(e,c,d);
            insert(d,l,add_koeff,NULL);
            m_i_i(1L,e);
            d    = CALLOCOBJECT();
        }
        erg    = OK;
    }
    else
        printf("\ninteger_factor: factorization error");
exit_label:
    FREEALL4(b,c,d,e);
    CTO(MONOPOLY,"integer_factor(e2)",l);
    ENDR("integer_factor");
}

/*    This routine finds the smallest prime factor of an integer.    */
/*    a -- the integer; first_prime -- its smallest prime factor.    */

INT first_prime_factor(a,first_prime) OP a,first_prime;
/* 04.04.90: TPMcD */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT    ret    = ERROR;
#ifdef    MONOPOLYTRUE
    OP    b = CALLOCOBJECT();    
    OP    c = CALLOCOBJECT();
    OP    d = CALLOCOBJECT();    
    OP    e = CALLOCOBJECT();
    OP    l = CALLOCOBJECT();

    if (S_O_K(a) != INTEGER && S_O_K(a) != LONGINT)
        goto exit_label;
    init(MONOPOLY,l);
    m_i_i(1L,first_prime);
    copy(a,d);
    if (LT(d,cons_null) == TRUE)
        addinvers(d,d);
    if (einsp(d))
    {    
        ret    = OK;
        goto exit_label;
    }
    if (integer_factor_0(d,l,b,c,first_prime) == OK)
        if (einsp(first_prime))
            if (integer_factor_1(d,c,d,e,l,first_prime) != OK
                || einsp(first_prime))
                goto exit_label;
    ret    = OK;
exit_label:
    if (ret != OK)
        printf("\nfirst_prime_factor: factorization error");
    freeall(b); 
    freeall(c); 
    freeall(d); 
    freeall(e); 
    freeall(l);
#else
    error("integer_factor: MONOPOLY not available");
#endif
    return(ret);
}

/*    SQUARE-FREE PARTS    */

/*    This routine find the square-free part of the integer, which is        */
/*    given as a prime factors list.                                        */
/*    la -- a MONOPOLY containing the prime factorization of the integer     */
/*    lb, lc -- return the MONOPOLYs containing the prime factorization     */
/*    of the square-free and square parts, respectively.                    */
/*    The parameters la,lb,lc must be distinct.                            */

INT square_free_part_0(la,lb,lc) OP la,lb,lc;
/* 14.06.90: TPMcD */
/* AK 200891 V1.3 */
{    
    INT    erg    = ERROR;
    INT    flag_b    = 1L, flag_c    = 1L;
    OP    u , x , y ,
        z , ptr, w;

    CTO(MONOPOLY,"square_free_part_0(1)",la);

    u = CALLOCOBJECT();
    x = CALLOCOBJECT();
    y = CALLOCOBJECT();
    z = CALLOCOBJECT();

    ptr    = la;
    init(MONOPOLY,lb); 
    init(MONOPOLY,lc);
    while (ptr != NULL)
    {    
        copy(S_PO_S(ptr),u);    /*    the prime        */
        copy(S_PO_K(ptr),x);    /*    the exponent    */
        if (negp(x))
            error("square_free_part_0 : unexpected negative exponent");
        nb_quores(x,cons_zwei,z,y);
        if (nullp(y))            /*    even power        */
        {    
            w    = CALLOCOBJECT();
            m_sk_mo(u,z,w);
            insert(w,lc,add_koeff,NULL);
            flag_c    = 0L;
        }
        else
        {    
            if (not nullp(z))
            {    
                w    = CALLOCOBJECT();
                m_sk_mo(u,z,w);
                insert(w,lc,add_koeff,NULL);
                flag_c    = 0L;
            }
            w    = CALLOCOBJECT();
            m_sk_mo(u,cons_eins,w);
            insert(w,lb,add_koeff,NULL);
            flag_b    = 0L;
        }
        ptr    = S_L_N(ptr);
    }
    if (flag_b)
    {    
        w    = CALLOCOBJECT();
        m_sk_mo(cons_eins,cons_eins,w);
        insert(w,lb,add_koeff,NULL);
    }
    if (flag_c)
    {    
        w    = CALLOCOBJECT();
        m_sk_mo(cons_eins,cons_eins,w);
        insert(w,lc,add_koeff,NULL);
    }
    erg    = OK;

    freeall(u); 
    freeall(x); 
    freeall(y); 
    freeall(z);
    CTO(MONOPOLY,"square_free_part_0(e2)",lb);
    CTO(MONOPOLY,"square_free_part_0(e3)",lc);
    ENDR("square_free_part_0");
}

/*    This routine find the square-free part of the integer, i.e. the    */
/*    product of the prime factors (and -1 , if the integer is < 0.    */
/*    a -- the integer, it is either an INTEGER, LONGINT or a        */
/*    MONOPOLY containing the prime factorization of an integer.    */
/*    b -- the square-free part.        a    = b * c  2        */
/*    c -- the square-root of the square part.            */
/*    la -- returns a MONOPOLY containing the prime factorization of    */
/*    a if a is not a MONOPOLY and la is not NULL.            */
/*    lb, lc -- returns the MONOPOLYs containing the prime        */
/*    factorizations of b and c.                    */
/*    The parameters a,b,c must be distinct.  If la,lb,lc are not    */
/*    NULL they must be distinct also.                */

INT square_free_part(a,b,c,la,lb,lc) OP a,b,c,la,lb,lc;
/* 14.06.90: TPMcD */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT    erg    = ERROR;
    OP    la_tmp=NULL, lb_tmp=NULL, lc_tmp=NULL;

    CTTTO(INTEGER,LONGINT,MONOPOLY,"square_free_part(1)",a);

    if (S_O_K(a) == INTEGER || S_O_K(a) == LONGINT)
    {    
        if (la == NULL)
            la_tmp    = CALLOCOBJECT();
        else
            la_tmp    = la;
        init(MONOPOLY,la_tmp);
        integer_factor(a,la_tmp);
    }
    else if (S_O_K(a) == MONOPOLY)
        la_tmp    = a;
    else
        goto exit_label;
    if (lb == NULL)
        lb_tmp    = CALLOCOBJECT();
    else
        lb_tmp    = lb;
    init(MONOPOLY,lb_tmp);
    if (lc == NULL)
        lc_tmp    = CALLOCOBJECT();
    else
        lc_tmp    = lc;
    init(MONOPOLY,lc_tmp);
    square_free_part_0(la_tmp,lb_tmp,lc_tmp);
    integer_factors_to_integer(lb_tmp,b);
    integer_factors_to_integer(lc_tmp,c);
    erg    = OK;
exit_label:
    if (la == NULL && la_tmp != a) freeall(la_tmp);
    if (lb == NULL) freeall(lb_tmp);
    if (lc == NULL) freeall(lc_tmp);



    CTTO(INTEGER,LONGINT,"square_free_part(e2)",b);
    CTTO(INTEGER,LONGINT,"square_free_part(e3)",c);
    ENDR("square_free_part");
}

/*
    The Jacobi Symbol: (a/b) b odd.
    a and b are integers. c must point to a location different from a and b.
    if a and b have a common factor, c is set to 0 and ERROR is returned.
    otherwise, c is set to the the jacobi symbol (a/b). Note that b must
    be odd.
*/

INT jacobi(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
{    
    INT erg = OK;
    OP    x , y , z , w , y_eins , y_zwei ,
        z_eins , z_zwei , four , eight    ;
    INT    ret    = ERROR;
    INT    d, f = 0L;

    CTTO(INTEGER,LONGINT,"jacobi(1)",a);
    CTTO(INTEGER,LONGINT,"jacobi(2)",b);
    CE3(a,b,c,jacobi);
    M_I_I(0,c);

    if (EVEN(b))
    {    
        printf("Jacobi Symbol: Second integer must be odd\n");
        goto e2;
    }
    x =CALLOCOBJECT(), y = CALLOCOBJECT(), z = CALLOCOBJECT(),
    w = CALLOCOBJECT(), y_eins = CALLOCOBJECT(), y_zwei = CALLOCOBJECT(),
    z_eins = CALLOCOBJECT(), z_zwei = CALLOCOBJECT(),
    four = CALLOCOBJECT(), eight    = CALLOCOBJECT();
    M_I_I(4,four);
    M_I_I(8,eight);

    COPY(a,x);
    COPY(b,y);
    if (NEGP(y)) ADDINVERS_APPLY(y);

    while (NEQ(y,cons_eins))
    {    
        mod(x,y,z);
        if (NULLP(z))    /*    The numbers not relatively prime*/
            goto exit_label;
        if (ODD(z))
        {    
            FREESELF(w);
            ADDINVERS(y,w);
            ADD_APPLY(w,z);
        }
        d        = 0L;
        while (EVEN(z))
        {    
            d    = 1L - d;
            ganzdiv(z,cons_zwei,z);
            if (NULLP(z))    /*The numbers not relatively prime*/
                goto exit_label;
        }
        FREESELF(x);COPY(y,x);
        FREESELF(y_eins);COPY(y,y_eins);
        DEC(y_eins);
        mod(y_eins,eight,y_zwei);
        FREESELF(z_eins);COPY(z,z_eins);
        DEC(z_eins);
        mod(z_eins,eight,z_zwei);
        FREESELF(y_eins);MULT(y_zwei,z_zwei,y_eins);
        mod(y_eins,eight,y_eins);
        if (GE(y_eins,four))
            f    = 1L - f;
        if (d)    /* an odd power of two */
        {    
            INC(y);
            mod(y,eight,y_eins);
            if (GE(y_eins,four))
                f    = 1L - f;
        }
        if (NEGP(z))
            ADDINVERS_APPLY(z);
        FREESELF(y);COPY(z,y);
    }
    m_i_i(1,c);
    if (f)
        M_I_I(-1,c);
    ret    = OK;
exit_label:
    FREEALL(x); 
    FREEALL(y); 
    FREEALL(z); 
    FREEALL(w);
    FREEALL(y_eins); 
    FREEALL(y_zwei); 
    FREEALL(z_eins); 
    FREEALL(z_zwei);
    FREEALL(four); 
    FREEALL(eight);
e2:
    return(ret);
    ENDR("jacobi");
}

/*
    The Kronecker Symbol: (a/b). a square-free and congruent to 0 or 1 mod 4.
    a and b are integers. c must point to a location different from a and b.
    if a and b have a common factor, c is set to 0 and ERROR is returned.
    otherwise, c is set to the the jacobi symbol (a/b). Note that b must
    be odd.
*/

INT kronecker(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
{    
    INT    flag    = 0L;
    INT    ret    = ERROR;
    INT erg = OK;
    OP    a_eins = CALLOCOBJECT(), a_zwei = CALLOCOBJECT(), b_null = CALLOCOBJECT(),
        b_eins = CALLOCOBJECT(), b_zwei = CALLOCOBJECT(), b_drei = CALLOCOBJECT(),
        four = CALLOCOBJECT();

    if (c == a || c == b || nullp(a) || nullp(b))
        goto exit_label;
    COPY(a,a_eins);
    COPY(b,b_eins);
    if (NEGP(b_eins))
        ADDINVERS_APPLY(b_eins);
    M_I_I(4L,four);
    copy(cons_null,c);
    mod(a_eins,four,a_zwei);
    if (NULLP(a_zwei))
        flag    = 1L;
    else if (!einsp(a_zwei))
        goto exit_label;
    nb_quores(b_eins,cons_zwei,b_zwei,b_drei);
    copy(cons_null,b_null);
    if (NULLP(b_drei))    /*    b is even.    */
    {    
        if (flag)    /*    a is even also.    */
            goto exit_label;
        do
        {    
            INC(b_null);
            copy(b_zwei,b_eins);
            nb_quores(b_eins,cons_zwei,b_zwei,b_drei);
        }        while (nullp(b_drei));
    }                /*    b_eins is the largest odd factor of b.    */
    nb_quores(b_null,cons_zwei,b_null,b_zwei);
    if (NULLP(b_zwei))    /*    b is divisible by an odd power of two and a is odd.    */
    {    
        m_i_i(8L,b_drei);
        mod(a_eins,b_drei,b_zwei);
        if (NEQ(b_zwei,cons_eins))
            flag    = 1L;        /* negate the final value */
    }
    else
        flag    = 0L;
    /*    At this point, b_eins is odd */
    jacobi(a_eins,b_eins,c);
    if (flag)
        ADDINVERS_APPLY(c);
    ret    = OK;
exit_label:
    FREEALL(a_eins); 
    FREEALL(a_zwei); 
    FREEALL(four);
    FREEALL(b_null); 
    FREEALL(b_eins); 
    FREEALL(b_zwei); 
    FREEALL(b_drei);
    return(ret);
    ENDR("kronecker");
}
/******************        fields_0.c        **********************/
/* 26.07.91: TPMcD.                                             */
/*************************************************************/
INT eq_cyclotomic(a,b) OP a,b;
/* AK 210202 */
{
    INT erg = OK,r;
    OP c;
    CTO(CYCLOTOMIC,"eq_cyclotomic(1)",a);
    if (S_O_K(b) != CYCLOTOMIC) return FALSE;
    c = CALLOCOBJECT();
    sub(a,b,c);
    r = NULLP(c);
    FREEALL(c);
    return r;
    ENDR("eq_cyclotomic");
}

INT eq_sqrad(a,b) OP a,b;
/* AK 180702 */
{
    INT erg = OK,r;
    OP c;
    CTO(SQ_RADICAL,"eq_sqrad(1)",a);
    if (S_O_K(b) != SQ_RADICAL) return FALSE;
    c = CALLOCOBJECT();
    sub(a,b,c);
    r = NULLP(c);
    FREEALL(c);
    return r;
    ENDR("eq_sqrad");
} 

INT eq_fieldobject_int(type,a,i) OBJECTKIND type; OP a; INT i;
/* AK 200891 V1.3 */
{    
    INT    ret = FALSE;
    OP    b = CALLOCOBJECT();
    OP    c = CALLOCOBJECT();
    INT erg = OK; 
    M_I_I(-i,b);
    switch(S_O_K(a))
    {
#ifdef MONOPOLYTRUE
    case MONOPOLY:        
        add_scalar_monopoly(b,a,c);
        ret    = nullp_monopoly(c);
        break;
#endif /* MONOPOLYTRUE */
#ifdef CYCLOTRUE
    case CYCLOTOMIC:    
        add_scalar_cyclo(b,a,c);
        ret    = nullp_monopoly(S_N_S(c));
        break;
#endif /* CYCLOTRUE */
#ifdef SQRADTRUE
    case SQ_RADICAL:    
        add_scalar_sqrad(b,a,c);
        ret    = nullp_monopoly(S_N_S(c));
        break;
#endif /* SQRADTRUE */
    default:    
        error("eq_fieldobject_int: invalid type\n");
    }
    FREEALL(b); 
    FREEALL(c);
    return(ret);
    ENDR("eq_fieldobject_int");
}

#ifdef NUMBERTRUE

static struct number * callocnumber()
/* 22.06.90: TPMcD */
/* AK 200891 V1.3 */
{
    struct number *result=(struct number *) 
        SYM_calloc(1,sizeof(struct number));
    if (result == NULL) error("callocnumber:no mem");
    number_mem++;
    return(result);
}
#endif /* NUMBERTRUE */

INT m_ksd_n(kind,self,data,result) OBJECTKIND kind; OP self,data,result;
/* AK 230191 */
/* AK 200891 V1.3 */
{    
    INT erg = ERROR;
#ifdef NUMBERTRUE
    erg = b_ksd_n(kind,CALLOCOBJECT(),CALLOCOBJECT(),result);
    if ((S_O_K(self) != MONOPOLY)  || 
          ((kind == SQ_RADICAL) && (S_O_K(data) != LIST)))
        return( error("m_ksd_n: invalid self or data") );
    erg += copy(self,S_N_S(result));
    erg += copy(data,S_N_D(result));
#endif /* NUMBERTRUE */
    return erg;
}

INT init_sqrad(a) OP a;
/* AK 010993 */
{
    INT erg = OK;
    CTO(EMPTY,"init_sqrad(1)",a);
    erg +=  b_ksd_n(SQ_RADICAL, CALLOCOBJECT(), CALLOCOBJECT(), a);
    ENDR("init_sqrad");
}



INT init_cyclo(a) OP a;
/* AK 010993 */
{
    INT erg = OK;
    CTO(EMPTY,"init_cyclo(1)",a);

    erg +=  b_ksd_n(CYCLOTOMIC, CALLOCOBJECT(), NULL, a);

    ENDR("init_cyclo");
}


#ifdef NUMBERTRUE
INT b_ksd_n(kind,self,data,result) OBJECTKIND kind; OP self,data,result;
/* 22.06.90: TPMcD */ /* 3.04.91: TPMcD. */
/* AK 200891 V1.3 */
{
    OBJECTSELF obself;
    if (not EMPTYP(result))
        freeself(result);
    obself.ob_number = callocnumber();
    b_ks_o(kind,obself,result);
    if (EMPTYP(self))
        init(MONOPOLY,self);
    if (kind == SQ_RADICAL && EMPTYP(data))
        init(LIST,data);
    if ((S_O_K(self) != MONOPOLY)  || 
        ((kind == SQ_RADICAL) && (S_O_K(data) != LIST)))
            return( error("b_ksd_n: invalid self or data") );
    S_N_S(result)    = self;
    S_N_D(result)    = data;
    return(OK);
}
#endif /* NUMBERTRUE */

INT objectwrite_number(f,number) FILE *f; OP number;
/* AK 200891 V1.3 */
{
#ifdef NUMBERTRUE
    fprintf(f," %ld\n",(INT)S_O_K(number));
    objectwrite(f,S_N_S(number));
    switch (S_O_K(number))
    {    
    case    SQ_RADICAL:
        objectwrite(f,S_N_D(number));
        break;
    case    CYCLOTOMIC:
        objectwrite(f,S_N_DCI(number));
        break;
    default:
        error("Invalid number type\n");
    }
    return(OK);
#else /* NUMBERTRUE */
    error("objectwrite_number:NUMBER not available");
    return(ERROR);
#endif /* NUMBERTRUE */
}

INT objectread_number(f,number,type) FILE *f; OP number; OBJECTKIND type;
/* AK 200891 V1.3 */
{
#ifdef NUMBERTRUE
    init(type,number);
    objectread(f,S_N_S(number));
    switch (S_O_K(number))
    {    
    case    SQ_RADICAL:
        objectread(f,S_N_D(number));
        break;
    case    CYCLOTOMIC:
        {    
            OP    index = CALLOCOBJECT();
            objectread(f,index);
            S_N_DC(number)    = add_cyclo_data(index);
        }
        break;
    default:
        error("Invalid number type\n");
    }
    return(OK);
#endif /* NUMBERTRUE */
}

INT fprint_number(f,n) FILE *f; OP n;
/* AK 200891 V1.3 */
{    
    INT    saving;
#ifdef NUMBERTRUE
    switch (S_O_K(n))
    {    
    case    SQ_RADICAL:
        /*    Are all coefficients fractions with denominator 2    */
        if (S_O_K(S_PO_K(S_N_S(n))) == BRUCH)
        {    
            OP    nn = CALLOCOBJECT();
            saving    = space_saving;
            space_saving = FALSE;
            mult_scalar_sqrad(cons_zwei,n,nn);
            space_saving = saving;
            if (integer_coefficients(S_N_S(nn)) == TRUE)
            {
                fprintf(f," 1/2 (");
                fprint_sqrad(f,nn);
                fprintf(f,")");
                freeall(nn);
                zeilenposition    += 7L;
                return(OK);
            }
            freeall(nn);
        }
        fprintf(f," ( ");
        fprint_sqrad(f,n);
        fprintf(f," )");
        zeilenposition    += 5L;
        break;
    case    CYCLOTOMIC:
        fprintf(f," ( ");
        fprint_cyclo(f,n);
        fprintf(f," )");
        zeilenposition    += 5L;
        break;
    default:    
        ;
    }
#endif /* NUMBERTRUE */
    return(OK);
}

INT freeself_number(n) OP n;
/* AK 200891 V1.3 */
{
#ifdef NUMBERTRUE
    OBJECTSELF d;
    INT erg = OK;
    d = S_O_S(n);
    erg = freeall(S_N_S(n));
    if (erg == ERROR)
        return error("freeself_number:error in freeall S_N_S");

    switch (S_O_K(n))
    {    
    case    SQ_RADICAL:
        if (not EMPTYP(S_N_D(n)))
            freeall(S_N_D(n));
        else
            error("freeself_number: no data to release");
        break;
    case    CYCLOTOMIC:
        break;
    default:    
        ;
    }
    SYM_free(d.ob_number);
    number_mem--;
    C_O_K(n,EMPTY);
#endif /* NUMBERTRUE */
    return OK;
}

INT comp_number(a,b) OP a,b;
/* 21.07.91 TPMcD: still incomplete */
/* AK 200891 V1.3 */
{
#ifdef NUMBERTRUE
    switch (S_O_K(a))
    {    
    case    SQ_RADICAL:
        comp_sqrad(a,b);
        break;
    case    CYCLOTOMIC:
        comp_cyclo(a,b);
        break;
    default:
        return error("comp_number:invalid number type\n");
    }
    return(OK);
#else /* NUMBERTRUE */
    return error("comp_number:NUMBER not available");
#endif /* NUMBERTRUE */
}

INT copy_number(a,b) OP a,b;
/* AK 200891 V1.3 */
/* AK 060498 V2.0 */
{
#ifdef NUMBERTRUE
    if (a == b)
        error("copy_number: First and second arguments are the same\n");
    init(S_O_K(a),b);
    if (S_N_S(a) != NULL) copy(S_N_S(a),S_N_S(b));
    switch (S_O_K(a))
    {    
    case    SQ_RADICAL:
        copy(S_N_D(a),S_N_D(b));
        break;
    case    CYCLOTOMIC:
        S_N_DC(b)    = S_N_DC(a);
        break;
    default:
        return error("copy_number:invalid number type\n");
    }
    return(OK);
#endif /* NUMBERTRUE */
}

INT complex_conjugate(a,b) OP a,b;
{    
    OP    ptr;
    if (a != b)
        copy(a,b);
#ifdef NUMBERTRUE
    switch (S_O_K(b))
    {    
    case    SQ_RADICAL:
        ptr    = S_N_S(b);
        while (ptr != NULL)
        {    
            if (not EMPTYP(S_PO_K(ptr)))
                complex_conjugate(S_PO_K(ptr),S_PO_K(ptr));
            if (LT(S_PO_S(ptr),cons_null) == TRUE)
                addinvers_apply(S_PO_K(ptr));
            ptr    = S_L_N(ptr);
        }
        break;
    case    CYCLOTOMIC:
        ptr    = S_N_S(b);
        while (ptr != NULL)
        {    
            if (not EMPTYP(S_PO_K(ptr)))
            {    
                complex_conjugate(S_PO_K(ptr),S_PO_K(ptr));
                addinvers_apply(S_PO_S(ptr));
                add_apply(S_N_DCI(b),S_PO_S(ptr));
            }
            ptr    = S_L_N(ptr);
        }
        break;
    default:
        break;
    }
#endif /* NUMBERTRUE */
    return(OK);
}

INT setup_numbers(basis,saving,filename) INT basis, saving; 
char *filename;
/* 29.10.91: TPMcD */
{
#ifdef CYCLOTRUE
    number_mem = (INT)0;
#endif /* CYCLOTRUE */
#ifdef    MONOPOLYTRUE
    setup_prime_table();
#endif  /* MONOPOLYTRUE */
#ifdef    NUMBERTRUE
    basis_type        = basis;
    space_saving    = saving;
    setup_cyclotomic_table(filename);
#endif /* NUMBERTRUE */
    return(OK);
}

INT release_numbers()
/* 29.10.91: TPMcD */
{
#ifdef    MONOPOLYTRUE
    if (prime_table_set)
        {
        SYM_free(prime_table);
        prime_table = NULL;
        }
#endif
#ifdef    NUMBERTRUE
    if (cyclo_table_set)
        {
        free_cyclo_table();
        SYM_free(zzcyclo_table);
        cyclo_table_set = 0; /* AK 120202 */
        }
    if (cyclo_list_set)
        {
        free_cyclo_list();
        freeall(zzcyclo_list);
        cyclo_list_set = 0; /* AK 120202 */
        }
#endif
    return(OK);
}

INT nb_ende()
{
#ifdef CYCLOTRUE
    if (number_mem != 0L)
        fprintf(stderr,"error in number memory %ld\n",number_mem);
    return OK;
#endif
}

INT reset_basis(basis) INT basis;
{
#ifdef    NUMBERTRUE
    basis_type    = basis;
    if (basis == NO_REDUCE || basis == POWER_REDUCE)
        printf("\nWARNING: not a valid basis\n");
#endif
    return(OK);
}

INT reset_saving(saving) INT saving;
{
#ifdef    NUMBERTRUE
    space_saving    = saving;
#endif
    return(OK);
}

INT tex_monom_plus(form,a) INT form; OP a;
/* AK 200891 V1.3 */
{    
    return tex_monom(a);/* AK return */
}

#ifdef UNDEF
/*Multiplies the entries in two lists pairwise, putting the resulting    */
/*objects in a list.  Duplicate objects are ignored.        */

static INT mult_lists(a,b,c) OP a, b, c;
/* 26.08.90: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    INT    flag = 0L;
#ifdef    LISTTRUE
    OP    new, a_ptr, b_ptr, c_tmp;

    if (c == a || c == b)
    {    
        flag    = 1L;
        c_tmp    = CALLOCOBJECT();
    }
    else
        c_tmp    = c;
    init(LIST, c_tmp);
    b_ptr = b;
    while (b_ptr != NULL)
    {    
        a_ptr = a;
        while (a_ptr != NULL)
        {    
            new    = CALLOCOBJECT();
            mult(S_L_S(a_ptr), S_L_S(b_ptr), new);
            insert(new,c_tmp,NULL,NULL);
            a_ptr = S_L_N(a_ptr);
        };
        b_ptr = S_L_N(b_ptr);
    }
    if (flag)
    {    
        copy(c_tmp,c);
        freeall(c_tmp);
    }
    return(OK);
#else
    error("mult_lists: LIST not available");
    return(ERROR);
#endif
}
#endif

INT tidy(a) OP a;
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT    i,j; 
    OP    ptr;
    switch (S_O_K(a))
    {
#ifdef BRUCHTRUE
    case BRUCH : 
        tidy(S_B_O(a)); 
        tidy(S_B_U(a)); 
        break;
#endif /* BRUCHTRUE */
    case INTEGER : 
        break;
#ifdef LISTTRUE
    case POLYNOM:
    case LIST : 
        ptr = a;
        while (ptr != NULL)
        {    
            tidy(S_L_S(ptr));
            ptr    = S_L_N(ptr);
        }
        break;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
    case LONGINT : 
        break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
    case MATRIX :
        for (i=0L;i<S_M_LI(a);i++)
            for (j=0L;j<S_M_HI(a);j++)
                tidy(S_M_IJ(a,i,j));
        break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
    case MONOM : 
        tidy(S_MO_S(a)); 
        tidy(S_MO_K(a)); 
        break;
#endif /* MONOMTRUE */
#ifdef NUMBERTRUE
    case SQ_RADICAL: 
        break;
    case CYCLOTOMIC: 
        standardise_cyclo_0(a,basis_type); 
        break;
#endif /* NUMBERTRUE */
#ifdef VECTORTRUE
    case VECTOR :
        for (i=0L;i<S_V_LI(a);i++)
            tidy(S_V_I(a,i));
        break;
#endif /* VECTORTRUE */
    default:
        return error("tidy: invalid type\n");
    }
    return(OK);
}
/******************        fields_1.c        **********************/
/* 26.07.91: TPMcD.                                             */
/*************************************************************/

/*    MONOPOLYS    */

#ifdef    MONOPOLYTRUE

INT eval_monopoly(a,b,c) OP a,b,c;
/*AK 290395 */
{
    INT erg = OK;
    OP z,d;

    CTO(MONOPOLY,"eval_monopoly",a);
    CE3(a,b,c,eval_monopoly);

    erg += m_i_i((INT)0,c);
    z = a;
    d = CALLOCOBJECT();
    while (z != NULL)
        {
        CTO(INTEGER,"eval_monopoly:non integer self part",
                S_MO_S(S_L_S(z)));
        erg += hoch(b,S_MO_S(S_L_S(z)),d);
        MULT_APPLY(S_MO_K(S_L_S(z)),d);
        erg += add_apply(d,c);
        z = S_L_N(z);
        }
    erg += freeall(d);

    ENDR("eval_monopoly");
}

INT einsp_monopoly(a) OP a;
{
    if (S_L_S(a) == NULL)
        return FALSE;
    if (S_L_N(a) != NULL) 
        return FALSE;
    if (not nullp(S_MO_S(S_L_S(a))))
        return FALSE;
    if (not einsp(S_MO_K(S_L_S(a))))
                return FALSE;
    return TRUE;
}

INT m_skn_mp(s,k,n,e) OP s,k,n,e;
/* make self koeff next monopoly */
/* AK 040291 */ /* AK 200891 V1.3 */
/* AK 080306 V3.0 */
{    
    INT erg=OK;
    COP("m_skn_mp(4)",e);

    if ( n == NULL) {
        erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,e);
        COPY(s,S_PO_S(e));
        COPY(k,S_PO_K(e));
    }
    else {
        erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),CALLOCOBJECT(),e);
        COPY(s,S_PO_S(e));
        COPY(k,S_PO_K(e));
        COPY(n,S_PO_N(e));
    }
    ENDR("m_skn_mp");
}



INT b_skn_mp(s,k,n,e) OP s,k,n,e;
/* build self koeff next monopoly */
/* AK 040291 */ /* AK 200891 V1.3 */ /* 231091: TPMcD */
/* AK 080306 V3.0 */
{
    INT erg=OK;
    COP("b_skn_mp(4)",e);

    FREESELF(e);
    erg += b_sn_l(CALLOCOBJECT(),n,e);
    C_O_K(e,MONOPOLY);
    erg += b_sk_mo(s,k,S_L_S(e));
    ENDR("b_skn_mp");
}

INT cast_apply_monopoly(a) OP a;
/* tries to convert the parameter in to a MONOPOLY object */
/* AK 200498 V2.0 */
/* AK 271005 V3.1 */
{
    INT erg = OK;
    EOP("cast_apply_monopoly(1)",a); /* check if empty object */
    {
    switch (S_O_K(a))
        {
        case BRUCH:
        case INTEGER:
        case LONGINT:
        case FF:
            erg += m_skn_mp(cons_null,a,NULL,a);
            break;
	case POLYNOM:
	    NYI("cast_apply_monopoly:POLYNOM->MONOPOLY");
	    break;
        default:
            erg += WTO("cast_apply_monopoly:can not convert",a);
            break;
        }
    }
    ENDR("cast_apply_monopoly");
}




INT scan_monopoly(a) OP a;
/* AK 200990 */ /* AK 220191 V1.2 */
/* a becomes a monopoly */ /* AK 200891 V1.3 */
{
    OBJECTKIND kt,st;
    INT erg = OK;
    CTO(EMPTY,"scan_monopoly(1)",a);

    erg += printeingabe("type of monopoly self ");
    st=scanobjectkind();
    erg += printeingabe("type of monopoly koeff ");
    kt=scanobjectkind();
    erg += SCMPCO(st,kt,a);

    ENDR("scan_monopoly");
}
#endif /* MONOPOLYTRUE */

static INT SCMPCO(self_type,coeff_type,result) /* scan_monopoly_co */
    OBJECTKIND self_type,coeff_type; 
    OP result;
/* 04.06.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{    
    INT    ret = ERROR; 
    INT    i,n;
# ifdef    MONOPOLYTRUE
    OP    x = CALLOCOBJECT(), y = CALLOCOBJECT(), z;
    char a[30];

    init(MONOPOLY,result);
    printeingabe("Length of list: ");  /* AK 080891 */
    scanf("%ld",&n);
    for (i=0L;i<n;i++)
    {    
        sprintf(a,"%ld-th monomial (self) ",i);
        printeingabe(a);
        scan(self_type,x);
        sprintf(a,"%ld-th monomial (koeff) ",i);
        printeingabe(a);
        scan(coeff_type,y);
        if (nullp(y))
            continue;
        z = CALLOCOBJECT();
        m_sk_mo(x,y,z);
        insert(z,result,add_koeff,NULL);
    }
    if (empty_listp(result))
        insert_zero_into_monopoly(result);
    freeall(x); 
    freeall(y);
    ret    = OK;
#else
    error("SCMPCO: MONOPOLY not available");
#endif
    return(ret);
}

/*    Removes those terms from a MONOPOLY with zero coefficients unless    */
/*    this makes the list empty. In this case, one term with self and        */
/*    koeff both 0 is left.    */

# ifdef    MONOPOLYTRUE
INT remove_zero_terms(a) OP a;
/* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
{
    OP    term, ptr = a, a_tmp;
    INT erg = OK;

    CTO(MONOPOLY,"remove_zero_terms",a);
/*
    a_tmp = CALLOCOBJECT();
    erg += init(MONOPOLY,a_tmp);
    if (!empty_listp(ptr))
        while (ptr != NULL)
        {    
            if (not NULLP(S_PO_K(ptr)))
            {    
                term = CALLOCOBJECT();
                COPY(S_L_S(ptr),term);
                insert(term,a_tmp,add_koeff,NULL);
            }
            ptr    = S_L_N(ptr);
        }
    if (empty_listp(a_tmp))
        insert_zero_into_monopoly(a_tmp);
    SWAP(a_tmp,a);
    FREEALL(a_tmp);
*/
    ptr = a; term = NULL;
again:
    if (!empty_listp(ptr))
    while (ptr != NULL)
        {
        if (not NULLP(S_PO_K(ptr)) ) 
            {
            term = ptr;
            ptr = S_L_N(ptr);
            }
        else {
            a_tmp = ptr;
            ptr = S_L_N(ptr);
            C_L_N(a_tmp, NULL);
            if (term == NULL)
                {
                /* first element will be removed */
                if (ptr == NULL) { M_I_I(0,S_PO_S(a)); goto ende; } 
                FREESELF(a);
                *a = *ptr;
                C_O_K(ptr,EMPTY);
                FREEALL(ptr);
                ptr = a;
                goto again;
                }
            else {
                C_L_N(term,ptr);
                FREEALL(a_tmp);
                }
            }
        }

    if (empty_listp(a))
        insert_zero_into_monopoly(a);
   
ende: 
    ENDR("remove_zero_terms");
}


/*    This is used to convert an empty monopoly into a non-empty one    */


static INT insert_zero_into_monopoly(a) OP a;
/* 1.04.91: TPMcD. */ /* AK 200891 V1.3 */
{
    OP  m = CALLOCOBJECT();
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    M_I_I(0L,S_MO_K(m));
    M_I_I(0L,S_MO_S(m));
    insert(m,a,add_koeff,NULL);
    return(OK);
}
# endif /* MONOPOLYTRUE */

static INT integer_coefficients(a) OP a;
/* 25.09.91: TPMcD. */
{    
    OP    ptr = a;
# ifdef    MONOPOLYTRUE
    if (S_O_K(a) != MONOPOLY)
        error("integer_coefficients: parameter is not a MONOPOLY");
    if (!empty_listp(ptr))
        while (ptr != NULL)
        {    
            if (S_O_K(S_PO_K(ptr)) != INTEGER && S_O_K(S_PO_K(ptr)) != LONGINT)
                return(FALSE);
            ptr    = S_L_N(ptr);
        }
#else
    error("integer_coefficients: MONOPOLY not available");
#endif
    return(TRUE);
}

# ifdef    MONOPOLYTRUE
INT add_scalar_monopoly(a,b,c) OP a,b,c;
/* 30.05.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    OP    ptr;
    INT erg = OK;
    CTO(MONOPOLY,"add_scalar_monopoly",b);
    if (c == a)
        erg += ERROR;
    if (c != b)
        copy(b,c);
    ptr    = CALLOCOBJECT();
    erg += init(MONOPOLY,ptr);
    C_L_S(ptr,CALLOCOBJECT());
    erg += m_sk_mo(cons_null,a,S_L_S(ptr));
    erg += add_apply(ptr,c);
    erg += remove_zero_terms(c);
    erg += freeall(ptr);
    ENDR("add_scalar_monopoly");
}
#endif

INT mult_apply_scalar_monopoly(a,b) OP a,b;
/* AK 210202 */
{
    INT erg = OK;
    OP z;
    CTO(MONOPOLY,"mult_apply_scalar_monopoly(2)",b);
    if (NULLP(a))
        erg += init(MONOPOLY,b);
    else {
        FORALL(z,b,{MULT_APPLY(a,S_MO_K(z)); } );
        }
    ENDR("mult_apply_scalar_monopoly");
}

INT mult_scalar_monopoly(a,b,c) OP a,b,c;
/* 30.05.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
/* AK 200498 V2.0 */
{    
    INT erg = OK;
    CTO(ANYTYPE,"mult_scalar_monopoly(1)",a);
    CTO(MONOPOLY,"mult_scalar_monopoly(2)",b);
    CTO(EMPTY,"mult_scalar_monopoly(3)",c);
    if (NULLP(a)) {
        erg += init(MONOPOLY,c);
        }
    else {
        OP z;
        COPY(b,c);
        FORALL(z,c, { MULT_APPLY(a,S_MO_K(z)); } );
        }
    CTO(MONOPOLY,"mult_scalar_monopoly(e3)",c);
/*
    {
    OP d,z;
    d = CALLOCOBJECT();
    copy(c,d);
    FORALL(z,d, { div_apply(S_MO_K(z),a); } ); 
    if (NEQ(d,b)) {
        TCTO(ANYTYPE,"mult_scalar_monopoly(b)",b);
        TCTO(ANYTYPE,"mult_scalar_monopoly(d)",d);
        error("mult_scalar_monopoly:wrong result");
        }
    FREEALL(d);
    }
*/
    ENDR("mult_scalar_monopoly");
}

# ifdef    MONOPOLYTRUE
INT add_monopoly_monopoly(a,b,c) OP a, b, c;
/* 30.05.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{
    OP temp_eins, temp_zwei;
    INT erg = OK;
    CTO(MONOPOLY,"add_monopoly_monopoly(1)",a);
    CTO(MONOPOLY,"add_monopoly_monopoly(2)",b);
    CTO(EMPTY,"add_monopoly_monopoly(3)",c);

    temp_eins = CALLOCOBJECT();    
    temp_zwei = CALLOCOBJECT();
    copy(a,temp_eins);
    copy(b,temp_zwei);
    init(S_O_K(a), c);
    insert(temp_eins,c,add_koeff,NULL);
    insert(temp_zwei,c,add_koeff,NULL);
    erg += remove_zero_terms(c);
    ENDR("add_monopoly_monopoly");
}


INT mult_monopoly_monopoly(a,b,c) OP a, b, c;
/* 30.05.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    OP    new, a_ptr, b_ptr, c_tmp;
    OP    temp_eins, temp_zwei;
    INT erg = OK;
    CTO(MONOPOLY,"mult_monopoly_monopoly(1)",a);
    CTO(MONOPOLY,"mult_monopoly_monopoly(2)",b);
    CTO(EMPTY,"mult_monopoly_monopoly(3)",c);

    c_tmp    = c;

    erg += init(MONOPOLY, c_tmp);

    if (S_L_S(b) == NULL) /* AK 191093 */
        goto mmm_ende;
    if (S_L_S(a) == NULL) /* AK 220596 */
        goto mmm_ende;

    b_ptr = b;
    if (EMPTYP(S_PO_S(b_ptr)))        /* skip the empty term */
        b_ptr = S_L_N(b_ptr);
    while (b_ptr != NULL)
    {    
        a_ptr = a;
        if (EMPTYP(S_PO_S(a_ptr)))        /* skip the empty term */
            a_ptr = S_L_N(a_ptr);
        while (a_ptr != NULL)
        {    
            temp_eins = CALLOCOBJECT();
            temp_zwei = CALLOCOBJECT();
            ADD(S_PO_S(a_ptr), S_PO_S(b_ptr), temp_eins);
            MULT(S_PO_K(a_ptr), S_PO_K(b_ptr), temp_zwei);
            new    = CALLOCOBJECT();
            erg += b_sk_mo(temp_eins,temp_zwei,new);
            insert(new,c_tmp,add_koeff,NULL);
            a_ptr = S_L_N(a_ptr);
        }
        b_ptr = S_L_N(b_ptr);
    }
    erg += remove_zero_terms(c);
mmm_ende: 
    CTO(MONOPOLY,"mult_monopoly_monopoly(e3)",c);
    ENDR("mult_monopoly_monopoly");
}
#endif /* MONOPOLYTRUE */

/*    This routine deals with MONOPOLYs which are effectively        */
/*    LISTs of MONOMs whose coefficients are scalars and selfs    */
/*    are non-negative integers -- they correspond to polynomials    */
/*    in one variable. The quotient (qpoly) and remainder (rpoly)    */
/*    of the division of poly by dpoly are calculated.  The        */
/*    parameters poly,dpoly,qpoly and rpoly must all be different.*/

INT quores_monopoly_pre300402(poly,dpoly,qpoly,rpoly) OP poly,dpoly,qpoly,rpoly;
/* 30.05.90: TPMcD. */ /* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT    ret    = ERROR,erg=OK;

    OP    term , temp, sz, ptr_a, coeff ,
        minus  , ddeg  , dlead  ,
        rdeg  , rlead  ;

    CTO(MONOPOLY,"quores_monopoly(1)",poly);
    CTO(MONOPOLY,"quores_monopoly(2)",dpoly);
    SYMCHECK(NULLP(dpoly),"quores_monopoly: divisor is zero");

    term = NULL; sz=NULL; 
    coeff = CALLOCOBJECT();
    minus = CALLOCOBJECT(); ddeg = CALLOCOBJECT(); dlead = CALLOCOBJECT();
    rdeg = CALLOCOBJECT(); rlead = CALLOCOBJECT();
    M_I_I(-1L,minus);

    /*    Find the leading term of dpoly    */
    ptr_a = dpoly;
    while (ptr_a != NULL)
    {    
        sz = ptr_a;
        ptr_a = S_L_N(ptr_a);
    }
    COPY(S_PO_S(sz),ddeg);
    COPY(S_PO_K(sz),dlead);
    if (NULLP(ddeg) && NULLP(dlead))
        error("quores_monopoly: divisor is zero");
    ADDINVERS_APPLY(ddeg);
    ADDINVERS_APPLY(dlead);

    copy(poly,rpoly);
    init(MONOPOLY,qpoly);
    ptr_a    = rpoly;
    while(ptr_a != NULL)
    {    /*  If the remainder is zero, break from the loop    */
        if (empty_listp(rpoly))
        {    
            insert_zero_into_monopoly(rpoly);
            ret    = OK;
            break;
        }
        /*    Find the leading term of the current rpoly    */
        while (ptr_a != NULL)
        {    
            sz = ptr_a;
            ptr_a = S_L_N(ptr_a);
        }
        copy(S_PO_S(sz),rdeg);
        copy(S_PO_K(sz),rlead);
        ADD_APPLY(ddeg,rdeg);
        /*    The remainder has degree less than the divisor    */
        if (LT(rdeg,cons_null))
        {    
            ret    = OK;
            goto exit_label;
        }
        div(rlead,dlead,coeff);
        temp    = CALLOCOBJECT();
        init(MONOPOLY,temp);
        term    = CALLOCOBJECT();
        m_sk_mo(rdeg,coeff,term);
        insert(term,temp,add_koeff,NULL);

        term    = CALLOCOBJECT();
        init(MONOPOLY,term);
        C_L_S(term,CALLOCOBJECT());
        m_sk_mo(rdeg,cons_eins,S_L_S(term));
        MULT_APPLY(coeff,term);

        insert(term,qpoly,add_koeff,NULL);
        term = CALLOCOBJECT();
        mult_monopoly_monopoly(temp,dpoly,term);
        insert(term,rpoly,add_koeff,NULL);
        freeall(temp);
        ptr_a = rpoly;
    }
exit_label:
    remove_zero_terms(rpoly);
    if (empty_listp(qpoly))
        insert_zero_into_monopoly(qpoly);
    mult_apply_scalar_monopoly(minus,qpoly);
    remove_zero_terms(qpoly);
    FREEALL(coeff); /* AK 080891 */
    FREEALL(minus);
    FREEALL(ddeg); 
    FREEALL(rdeg); 
    FREEALL(dlead); 
    FREEALL(rlead);
    erg = ret;
    {
    OP c;
    c = CALLOCOBJECT();
    MULT(dpoly,qpoly,c);
    ADD_APPLY(rpoly,c);
    if (NEQ(c,poly)) {
        println(poly);
        println(dpoly);
        println(qpoly);
        println(rpoly);
        println(c);
        error("quores_monopoly:wrong result");
        }
    FREEALL(c);
    }
    ENDR("quores_monopoly");
}



INT quores_monopoly(a,b,c,d) OP a,b,c,d;
/* a/b = c rest d */
/* with monopoly = univariate polynomial */
/* AK 300402 */
/* simple verion, not optimized */
{
    INT erg = OK;
    OP degree_d,degree_b,leading_coeff_b,leading_coeff_d;
    OP h,z,ca;
    CTO(MONOPOLY,"quores_monopoly(1)",a);
    CTO(MONOPOLY,"quores_monopoly(2)",b);
    CTO(EMPTY,"quores_monopoly(3)",c);
    CTO(EMPTY,"quores_monopoly(4)",d);
    SYMCHECK(c==d,"quores_monopoly:should be different objects");

    if (NULLP(b)) error("quores_monopoly(2):null");

    if (NULLP(a))  {
		erg += copy(a,c);
		erg += copy(a,d);
		goto endr_ende;
		}

    init(MONOPOLY,c);
    COPY(a,d);

    CALLOCOBJECT6(degree_d,degree_b,leading_coeff_b,leading_coeff_d,h,ca);

    degree_monopoly(b,degree_b);
    ldcf_monopoly(b,leading_coeff_b);
 
again:
    CTO(MONOPOLY,"quores_monopoly(i3)",c);
    CTO(MONOPOLY,"quores_monopoly(i4)",d);
    FREESELF(degree_d);
    degree_monopoly(d,degree_d);
    if (LT(degree_d,degree_b))  goto ee; /* finished */

    /* else
       multiply b by leadcoeff_d/leadcoeff_b
       subtract this from d 
       */
    FREESELF(leading_coeff_d);
    ldcf_monopoly(d,leading_coeff_d);
    m_iindex_monopoly( S_I_I(degree_d) - S_I_I(degree_b),ca);
    div(leading_coeff_d,leading_coeff_b,h);
    copy(h,S_PO_K(ca));
    mult_apply(b,h); 
    FORALL(z,h,M_I_I(S_I_I(S_MO_S(z)) + S_I_I(degree_d) - S_I_I(degree_b),
                     S_MO_S(z)));
    addinvers_apply(h); 
    ADD_APPLY(h,d); 
    ADD_APPLY(ca,c);
    goto again;
ee:
    FREEALL6(degree_d,degree_b,leading_coeff_b,leading_coeff_d,h,ca);
    CTO(MONOPOLY,"quores_monopoly(e3)",c);
    CTO(MONOPOLY,"quores_monopoly(e4)",d);
/*
    {
    OP e;
    e = CALLOCOBJECT();
    MULT(b,c,e);
    ADD_APPLY(d,e);
    if (NEQ(e,a)) {
        println(a);
        println(b);
        println(c);
        println(d);
        println(e);
        error("quores_monopoly:wrong result");
        }
    FREEALL(e);
    }                                                                           
*/
    ENDR("quores_monopoly");
}

#ifdef    MONOPOLYTRUE
INT add_monopoly(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
{
    INT erg = OK;
    OP d;
    CTO(MONOPOLY,"add_monopoly(1)",a);
    CTO(EMPTY,"add_monopoly(3)",c);

    switch(S_O_K(b))
    {
    case INTEGER:
    case FF:
    case LONGINT:
        erg += add_scalar_monopoly(b,a,c);
        goto ee;
    case BRUCH: 
        erg += add_bruch(b,a,c);
        goto ee;

    case MONOPOLY: 
        erg += add_monopoly_monopoly(a,b,c);
        goto ee;
    case LAURENT:
        d = CALLOCOBJECT();
        erg += t_LAURENT_OBJ(b,d);
        erg += add(a,d,c);
        erg += freeall(d);
        goto ee;
    case POLYNOM:
        d=CALLOCOBJECT();
        erg += t_POLYNOM_MONOPOLY(b,d);
        erg += add_monopoly_monopoly(a,d,c);
        erg += freeall(d);
        goto ee;

    default: 
        WTO("add_monopoly(2)",b);
        goto ee;
    }
ee:
    ENDR("add_monopoly");
}


INT mult_monopoly_polynom(a,b,c) OP a,b,c;
/* CC because of laurent */
{
    INT erg = OK;
    CTO(POLYNOM,"mult_monopoly_polynom(2)",b);
    CTO(MONOPOLY,"mult_monopoly_polynom(1)",a);
    CTO(EMPTY,"mult_monopoly_polynom(3)",c);
    if(has_one_variable(b)==TRUE) /* CC */
        {
        OP d;
        d=CALLOCOBJECT();
        erg += t_POLYNOM_MONOPOLY(b,d);
        erg += mult_monopoly_monopoly(a,d,c);
        FREEALL(d);
        }
    else
        erg += mult_scalar_polynom(a,b,c); 
    ENDR("mult_monopoly_polynom");
}


INT mult_monopoly(a,b,c) OP a,b,c;
/* 24.07.91: TPMcD. */
/* AK 200891 V1.3 */
{
    OP d;
    INT erg = OK;
    CTO(MONOPOLY,"mult_monopoly(1)",a);
    CTO(ANYTYPE,"mult_monopoly(2)",b);
    CTO(EMPTY,"mult_monopoly(3)",c);

    switch(S_O_K(b))
    {
    case BRUCH:
        if (scalarp(S_B_O(b)) && scalarp(S_B_U(b)))
            erg += mult_scalar_monopoly(b,a,c);
        else
            {
            erg += copy(b,c);
            erg += mult(a,S_B_O(b),S_B_O(c));
            erg += kuerzen(c);
            }
        goto ee;
    case INTEGER:
    case FF:
    case LONGINT:
        erg += mult_scalar_monopoly(b,a,c);
        goto ee;
    case MONOPOLY: 
        erg += mult_monopoly_monopoly(a,b,c);
        goto ee;
#ifdef MATRIXTRUE
    case MATRIX: 
        erg += mult_scalar_matrix(a,b,c);
        goto ee;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
    case MONOM: 
        erg += mult_scalar_monom(a,b,c);
        break;
#endif /* MONOMTRUE */
#ifdef LAURENTTRUE
    case LAURENT: 
        d = CALLOCOBJECT();
        erg += t_LAURENT_OBJ(b,d);
        erg += mult(a,d,c);
        erg += freeall(d);
        break;
#endif /* LAURENTTRUE */
#ifdef POLYTRUE
    case POLYNOM: 
        erg += mult_monopoly_polynom(a,b,c);
        break;
#endif /* POLYTRUE */
#ifdef SCHUBERTTRUE
    case SCHUBERT: erg +=  mult_scalar_schubert(a,b,c);
            break;
#endif /* SCHUBERTTRUE */
    case VECTOR: 
         erg += mult_scalar_vector(a,b,c);
        break;
    default: 
        WTT("mult_monopoly",a,b);
    }

ee:
    CTO(ANYTYPE,"mult_monopoly(3)",c);
    ENDR("mult_monopoly");
}

INT addinvers_monopoly(a,b) OP a,b;
/* AK 200891 V1.3 */
/* AK 200498 V2.0 */
/* a and b may be equal */
{    
    INT erg = OK;
    CTO(MONOPOLY,"addinvers_monopoly(1)",a);
    CTO(EMPTY,"addinvers_monopoly(2)",b);
    erg += mult_scalar_monopoly(cons_negeins,a,b);
    ENDR("addinvers_monopoly");
}


INT add_apply_monopoly(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT    erg = OK;
    OP    c;
    CTO(MONOPOLY,"add_apply_monopoly(1)",a);
    EOP("add_apply_monopoly(2)",b);

    c = CALLOCOBJECT();
    SWAP(c,b);
    erg +=  add_monopoly(a,c,b);
    FREEALL(c);
    ENDR("add_apply_monopoly");
}


INT mult_apply_monopoly(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT    erg = OK;
    OP    c;
    CTO(MONOPOLY,"mult_apply_monopoly(1)",a);
    EOP("mult_apply_monopoly(2)",b);

    c = CALLOCOBJECT();
    erg += mult_monopoly(a,b,c);
    erg += copy(c,b);
    erg += freeall(c);

    ENDR("mult_apply_monopoly");
}

INT addinvers_apply_monopoly(a) OP a;
/* AK 200891 V1.3 */
/* AK 290402 */
{
    INT erg = OK;
    OP z;
    CTO(MONOPOLY,"addinvers_apply_monopoly(1)",a);
    /* return(addinvers_monopoly(a,a)); */
    FORALL(z,a,ADDINVERS_APPLY(S_MO_K(z)));
    ENDR("addinvers_apply_monopoly");
}
#endif /* MONOPOLYTRUE */

INT nullp_monopoly(a) OP a;
/* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
{
    INT erg = OK;
# ifdef    MONOPOLYTRUE
    OP ptr = a;
    CTO(MONOPOLY,"nullp_monopoly",a);

    if (empty_listp(a))
        return(TRUE);
    if (EMPTYP(S_L_S(ptr)))
        ptr = S_L_N(ptr);
    if (ptr == NULL || empty_listp(ptr))
        return(TRUE);
    if (S_L_N(ptr) != NULL)
        return(FALSE);
    if (EQ(S_PO_S(ptr),cons_null) && EQ(S_PO_K(ptr),cons_null))
        return(TRUE);
#endif
    return(FALSE);
    ENDR("nullp_monopoly");
}

INT comp_monopoly(a,b) OP a,b;
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
    INT erg = OK,ret;
    CTO(MONOPOLY,"comp_monopoly(1)",a);
    CTO(MONOPOLY,"comp_monopoly(2)",b);
    ret = comp_list(a,b);
    return ret;
    ENDR("comp_monopoly");
}

INT raise_power_monopoly(a,b) OP a, b;
/* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
{    
    INT erg = OK;
    OP    ptr;
    CTTO(INTEGER,LONGINT,"raise_power_monopoly(1)",a);
    CTO(MONOPOLY,"raise_power_monopoly(2)",b);

    if (EINSP(a))  {
        }
    else if (POSP(a)) 
        {
        FORALL(ptr,b,{ MULT_APPLY(a,S_MO_S(ptr)); });
        }
    else {
        SYMCHECK(1,"raise_power_monopoly: exponent <= 0");
        }
    CTO(MONOPOLY,"raise_power_monopoly(e2)",b);
    ENDR("raise_power_monopoly");
}

INT scale_monopoly(a,b) OP a, b;
/* MD */
/* AK 200891 V1.3 */
{    
    OP    ptr;
# ifdef    MONOPOLYTRUE
    OP    factor = CALLOCOBJECT(), minus = CALLOCOBJECT();
    M_I_I(-1L,minus);
    ptr    = b;
    if (EMPTYP(S_PO_S(ptr)))
        ptr    = S_L_N(ptr);
    if (EQ(a,minus) == TRUE)
        while (ptr != NULL)
        {    
            mod(S_PO_S(ptr),cons_zwei,factor);
            if (EQ(factor,cons_eins) == TRUE)
                mult(minus,S_PO_K(ptr),S_PO_K(ptr));
            ptr    = S_L_N(ptr);
        }
    else
        while (ptr != NULL)
        {    
            hoch(a,S_PO_S(ptr),factor);
            mult(factor,S_PO_K(ptr),S_PO_K(ptr));
            ptr    = S_L_N(ptr);
        }
    freeall(factor); 
    freeall(minus);
#endif
    return(OK);
}

INT objectread_monopoly(f,a) FILE *f; OP a;
/* 4.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
# ifdef    MONOPOLYTRUE
    objectread_list(f,a);
    C_O_K(a,MONOPOLY);
#endif
    return(OK);
}

# ifdef    MONOPOLYTRUE
INT tex_monopoly(a) OP a;
/* 2.04.91: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    INT myfirst = 1L;
    OP    ptr = a;
    fprintf(texout," ");
    while (ptr != NULL)
    {    
        if (!negp(S_PO_K(ptr)) && !myfirst)
            fprintf(texout," + {");
        else
            fprintf(texout,"{");
        tex(S_PO_K(ptr));
        fprintf(texout,"} x {");
        tex(S_PO_S(ptr));
        fprintf(texout,"}\n");
        ptr    = S_L_N(ptr);
        myfirst = 0L;
        texposition += 6;
    }
    fprintf(texout,"\n");
    texposition = 0;
    return(OK);
}

/*    CONSTRUCTION OF SPECIAL TYPES OF MONOPOLY    */

/*    Given the number n, which should be an positive INTEGER or LONGINT,*/
/*    the result returns the polynomial x**n-1.            */

INT m_iindex_monopoly(ii,mon) INT ii; OP mon;
{
    INT erg = OK;
    COP("m_iindex_monopoly",mon);
    erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,mon);
    erg += m_i_i(ii,S_PO_S(mon));
    erg += m_i_i(1L,S_PO_K(mon));
    ENDR("m_iindex_monopoly");
}

INT make_unitary0_monopoly(number,result) OP number, result;
/* 10.06.90: TPMcD. */ /* AK 200891 V1.3 */
{    
    OP    new;
    OP    e = CALLOCOBJECT(), coeff = CALLOCOBJECT();
    init(MONOPOLY,result);
    M_I_I(0L,e); /* we use the macro, beacuse e is empty */
    M_I_I(-1L,coeff);
    new = CALLOCOBJECT();
    m_sk_mo(e,coeff,new);
    insert(new,result,add_koeff,NULL);
    m_i_i(1L,coeff);
    new = CALLOCOBJECT();
    m_sk_mo(number,coeff,new);
    insert(new,result,add_koeff,NULL);
    freeall(e); 
    freeall(coeff);
    return(OK);
}
#endif /* MONOPOLYTRUE */

/*    Given the number n, which should be an positive INTEGER or LONGINT,*/
/*    the result returns the MONOPOLY x**(n-1)+x**(n-2)+...+x+1.    */

INT make_unitary_eins_monopoly(number,result) OP number, result;
/* 10.06.90: TPMcD. */ /* AK 200891 V1.3 */
{    
    OP    new, ptr;
    INT erg = OK;
# ifdef    MONOPOLYTRUE
    OP    e = CALLOCOBJECT(), coeff = CALLOCOBJECT();
    init(MONOPOLY,result);
    ptr    = result;
    M_I_I(0L,e);
    M_I_I(1L,coeff);
    while (LT(e,number) == TRUE)
    {    
        new = CALLOCOBJECT();
        init(MONOPOLY,new);
        S_L_S(new) = CALLOCOBJECT();
        m_sk_mo(e,coeff,S_L_S(new));
        insert(new,result,NULL,NULL);
        INC(e);
    }
    freeall(e); 
    freeall(coeff);
    return(OK);
#else
    return(ERROR);
#endif
}

/*    Given the number n, which should be an positive INTEGER or LONGINT*/
/*    or a MONOPOLY representing a prime factorisation of an integer greater*/
/*    than 1 , the result returns the cyclotomic polynomial of index n.*/

INT make_cyclotomic_monopoly(number,result) OP number, result;
/* 100690: TPMcD. */ /* AK 200891 V1.3 */
{    
    INT    ret = ERROR;
    OP    ptr;
# ifdef    MONOPOLYTRUE
    OP    minus, e, factor, poly_eins, poly_zwei, poly_drei,
        list = CALLOCOBJECT();

    if (S_O_K(number) == MONOPOLY)
        copy(number,list);
    else
    {    
        if (((S_O_K(number) != INTEGER) && (S_O_K(number) != LONGINT))
            || (LT(number,cons_eins) == TRUE))
            goto exit_label;

        if (einsp(number))
        {    
            make_unitary0_monopoly(number,result);
            ret    = OK;
            goto exit_label;
        }
        integer_factor(number,list);
    }
    ptr    = list;
    if (EMPTYP(S_PO_S(ptr)))
        ptr    = S_L_N(ptr);
    factor = CALLOCOBJECT();
    copy(S_PO_S(ptr),factor);

    if (S_L_N(ptr) == NULL)    /* list has just one prime factor */ 
    {    
        make_unitary_eins_monopoly(factor,result);
        dec(S_PO_K(ptr));
        e = CALLOCOBJECT();
        integer_factors_to_integer(ptr,e);
        raise_power_monopoly(e,result);
        freeall(e);
        ret    = OK;
        freeall(factor); /* AK 060993 */
        goto exit_label;
    }
    else
    {    
        poly_eins = CALLOCOBJECT();
        ptr    = S_L_N(ptr);
        make_cyclotomic_monopoly(ptr,poly_eins);
        if (EQ(factor,cons_zwei) == TRUE)
        {    
            minus    = CALLOCOBJECT();
            M_I_I(-1L,minus);
            scale_monopoly(minus,poly_eins);
            copy(poly_eins,result);
            freeall(minus);
        }
        else
        {    
            poly_zwei = CALLOCOBJECT(); 
            poly_drei = CALLOCOBJECT();
            copy(poly_eins,poly_zwei);
            raise_power_monopoly(factor,poly_eins);
            quores_monopoly(poly_eins,poly_zwei,result,poly_drei);
            freeall(poly_zwei); 
            freeall(poly_drei);
        }
        freeall(poly_eins);
        ret    = OK;
    }
    ptr    = list;
    if (EMPTYP(S_PO_S(ptr)))
        /* ptr    = S_L_N(ptr); */
        error("nb internal error 234");
    dec(S_PO_K(ptr));
    ptr     = S_L_N(ptr);
    while (ptr != NULL)
    {    
        /* dec(S_PO_K(ptr)); */
        m_i_i(0L,S_PO_K(ptr));
        ptr    = S_L_N(ptr);
    }
    integer_factors_to_integer(list,factor);
    raise_power_monopoly(factor,result);
    freeall(factor);
exit_label:
    freeall(list);
#endif
    return(ret);
}
/******************        fields_2.c        **********************/
/* 26.07.91: TPMcD.                                             */
/*************************************************************/

/*    SQUARE RADICALS        */

#ifdef    SQRADTRUE
INT make_monopoly_sqrad(a,b) OP a,b;
/* 30.05.90: TPMcD. */ /* 3.04.91: TPMcD. */
/* AK 200891 V1.3 */
{    
    INT    flag = 0L;
    INT erg = OK;
    OP    ptr, new, b_tmp, sqfree , sqpart ;

    CTO(MONOPOLY,"make_monopoly_sqrad(1)",a);
    if (b == a)
    {    
        flag    = 1L;
        b_tmp    = CALLOCOBJECT();
    }
    else
    {    
        init(SQ_RADICAL,b);
        b_tmp    = S_N_S(b);
    }
    sqfree = CALLOCOBJECT();
    sqpart = CALLOCOBJECT();
    init(MONOPOLY, b_tmp);
    ptr = a;
    while (ptr != NULL)
    {    
        if (not nullp(S_PO_S(ptr)))  /* AK 120891 */
        {    
            square_free_part(S_PO_S(ptr),sqfree,
                sqpart,NULL,NULL,NULL);
            MULT_APPLY(S_PO_K(ptr),sqpart);
            new     = CALLOCOBJECT();
            m_sk_mo(sqfree,sqpart,new);
            insert(new,b_tmp,add_koeff,
                comp_monomvector_monomvector);
        }
        ptr = S_L_N(ptr);
    }
    if (flag)
    {    
        init(SQ_RADICAL,b);
        freeall(S_N_S(b)); /* AK 060993 */
        S_N_S(b)    =  b_tmp;
    }
    remove_zero_terms(S_N_S(b));
    find_sqrad_data(b);
    freeall(sqfree); 
    freeall(sqpart);
    ENDR("make_monopoly_sqrad");
}
#endif /* SQRADTRUE */
/*    a: the scalar; b: the result.    */

#ifdef    SQRADTRUE
INT make_scalar_sqrad(a,b) OP a,b;
/* 5.04.91: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    OP c;
    INT erg = OK;
    EOP("make_scalar_sqrad(1)",a);

    c    = CALLOCOBJECT();
    erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,c);
    erg += copy(a,S_PO_K(c));
    M_I_I(1L,S_PO_S(c));
    erg += make_monopoly_sqrad(c,b);
    if (not EMPTYP(S_N_D(b)))
        erg += freeself(S_N_D(b));
    erg += find_sqrad_data(b);
    erg += freeall(c);

    ENDR("make_scalar_sqrad");
}
#endif

#ifdef SQRADTRUE
INT scan_sqrad(a) OP a;
/* AK 300191 V1.2 */ /* a becomes sqrad */
/* 3.04.91: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{
    OP c = CALLOCOBJECT();
    INT erg=OK;
    erg += printeingabe("self of sqrad");
    erg += scan(MONOPOLY,c);
    erg += make_monopoly_sqrad(c,a);
    erg += find_sqrad_data(a);
    erg += freeall(c);
    return erg;
}
#endif /* SQRADTRUE */

#ifdef SQRADTRUE
INT add_scalar_sqrad(a,b,c) OP a,b,c;
/* 30.05.90: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    OP    ptr;
    INT erg = OK;
    CTO(SQ_RADICAL,"add_scalar_sqrad(2)",b);
    CTO(EMPTY,"add_scalar_sqrad(3)",c);
    
    erg += copy(b,c);
    ptr = CALLOCOBJECT();
    erg += init(MONOPOLY,ptr);
    C_L_S(ptr,CALLOCOBJECT());
    erg += m_sk_mo(cons_eins,a,S_L_S(ptr));
    ADD_APPLY(ptr,S_N_S(c));
    erg += freeall(ptr);
    if (space_saving)
        convert_sqrad_scalar(c);

    ENDR("add_scalar_sqrad");
}



INT mult_apply_scalar_sqrad(a,b) OP a,b;
/* AK 060498 V2.0 */
{
    OP c;
    INT erg = OK;
    CTO(SQ_RADICAL,"mult_apply_scalar_sqrad(2)",b);
    c = CALLOCOBJECT();
    SWAP(c,b);
    erg += mult_scalar_sqrad(a,c,b);
    FREEALL(c);
    ENDR("mult_apply_scalar_sqrad");
}

INT mult_scalar_sqrad(a,b,c) OP a, b, c;
/* 30.05.90: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    OP    ptr;
    INT erg = OK;
    CTO(SQ_RADICAL,"mult_scalar_sqrad(2)",b);
    CTTO(INTEGER,EMPTY,"mult_scalar_sqrad(3)",c);

    if (S_O_K(c)==INTEGER) C_O_K(c,EMPTY);

    if (space_saving && nullp(a))
    {    
        COPY(a,c);
        goto endr_ende;
    }

    COPY(b,c);
    ptr = S_N_S(c);
    if (EMPTYP(S_PO_S(ptr)))
        ptr = S_L_N(ptr);
    while (ptr != NULL)
    {    

        MULT_APPLY(a,S_PO_K(ptr));
        ptr = S_L_N(ptr);
    }

    remove_zero_terms(S_N_S(c));
    if (nullp_sqrad(c))
        find_sqrad_data(c);

    ENDR("mult_scalar_sqrad");
}

INT add_sqrad_sqrad(a,b,c) OP a, b, c;
/* 23.06.90: TPMcD. */ /* 3.04.91: TPMcD. */
/* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
/* AK 060498 V2.0 */
{    
    INT    flag = 0L;
    INT erg = OK;
    OP    c_tmp, data_a ,data_b;
    CTO(SQ_RADICAL,"add_sqrad_sqrad(1)",a);
    CTO(SQ_RADICAL,"add_sqrad_sqrad(2)",b);
    CTO(EMPTY,"add_sqrad_sqrad(3)",c);
    
    data_a = CALLOCOBJECT();
    data_b = CALLOCOBJECT();
    find_sqrad_data(a);
    find_sqrad_data(b);
    copy(S_N_D(a),data_a);
    copy(S_N_D(b),data_b);
    if (!empty_listp(data_b))
        insert(data_b,data_a,NULL,NULL);
    else
        freeall(data_b);
    if (c == a || c == b)
    {    
        flag    = 1L;
        c_tmp    = CALLOCOBJECT();
    }
    else
    {    
        init(SQ_RADICAL,c);
        c_tmp    = S_N_S(c);
    }
    /* erg += init(MONOPOLY,c_tmp); */
    FREESELF(c_tmp);
    erg += add_monopoly_monopoly(S_N_S(a),S_N_S(b),c_tmp);
    if (flag)
    {    
        if (not EMPTYP(S_N_S(c)))
            erg += freeall(S_N_S(c));
        S_N_S(c)    = c_tmp;
    }
    if (not EMPTYP(S_N_D(c)))
        erg += freeall(S_N_D(c));
    S_N_D(c)    = data_a;
    adjust_sqrad_data(c);
    ENDR("add_sqrad_sqrad");
}

#endif /* SQRADTRUE */
INT mult_sqrad_sqrad(a,b,c) OP a, b, c;
/* 30.05.90: TPMcD. */ /* 3.04.91: TPMcD. */
/* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{    
    INT    flag = 0L;
    INT erg = OK;

    OP    a_ptr, b_ptr, c_tmp, new;
    OP    temp_eins, temp_zwei, temp_drei, data_a, data_b;
    CTO(SQ_RADICAL,"mult_sqrad_sqrad(1)",a);
    CTO(SQ_RADICAL,"mult_sqrad_sqrad(2)",b);
    
    find_sqrad_data(a);
    find_sqrad_data(b);
    data_a = CALLOCOBJECT(); 
    data_b = CALLOCOBJECT();
    COPY(S_N_D(a),data_a); 
    COPY(S_N_D(b),data_b);
    if (!empty_listp(data_b))
        insert(data_b,data_a,NULL,NULL);
    else
        freeall(data_b);
    if (c == a || c == b)
    {    
        flag    = 1L;
        c_tmp    = CALLOCOBJECT();
    }
    else
    {    
        init(SQ_RADICAL,c);
        c_tmp    = S_N_S(c);
    }
    init(MONOPOLY,c_tmp);
    b_ptr = S_N_S(b);
    if (EMPTYP(S_PO_S(b_ptr)))        /* skip the empty term */
        b_ptr = S_L_N(b_ptr);
    temp_eins = CALLOCOBJECT(); 
    temp_zwei = CALLOCOBJECT(); 
    temp_drei = CALLOCOBJECT();
    while (b_ptr != NULL)
    {
        if (not nullp(S_PO_S(b_ptr))) /* AK 120891 */
        {
            a_ptr = S_N_S(a);
            while (a_ptr != NULL)
            {
                if (not nullp(S_PO_S(a_ptr))) /* AK 120891 */
                {
                ggt(S_PO_S(a_ptr), S_PO_S(b_ptr), temp_eins); 
                if (NEGP(S_PO_S(a_ptr)) && NEGP( S_PO_S(b_ptr) ) )
                    ADDINVERS_APPLY(temp_eins); /* AK 259492 */
                ganzdiv(S_PO_S(a_ptr), temp_eins, temp_zwei);
                ganzdiv(S_PO_S(b_ptr), temp_eins, temp_drei);
                MULT_APPLY(S_PO_K(a_ptr),temp_eins);
                MULT_APPLY(S_PO_K(b_ptr),temp_eins);
                MULT_APPLY(temp_drei,temp_zwei);
                new    = CALLOCOBJECT();
                m_sk_mo(temp_zwei,temp_eins,new);
                insert(new,c_tmp,add_koeff,NULL);
                }
                a_ptr = S_L_N(a_ptr);
            }
        }
        b_ptr = S_L_N(b_ptr);
    }
    if (empty_listp(c_tmp))
        insert_zero_into_monopoly(c_tmp);
    if (flag)
    {    
        init(SQ_RADICAL,c);
        freeall(S_N_S(c)); /* AK 060993 */
        S_N_S(c)    = c_tmp;
    }
    if (not EMPTYP(S_N_D(c)))
        freeall(S_N_D(c));
    S_N_D(c)    = data_a;
    adjust_sqrad_data(c);
    freeall(temp_eins); 
    freeall(temp_zwei); 
    freeall(temp_drei);
    return(OK);
    ENDR("mult_sqrad_sqrad");
}

#ifdef    SQRADTRUE
INT add_sqrad(a,b,c) OP a,b,c;
/* AK 070891 V1.3 */
/* 04.10.91: TPMcD */
{    
    INT erg = OK;
    CTO(SQ_RADICAL,"add_sqrad(1)",a);
    CTO(EMPTY,"add_sqrad(3)",c);

    switch(S_O_K(b))
    {
    case CYCLOTOMIC: /* SQ + CYC = CYC */
        erg += add_cyclo(b,a,c); 
        break;
    case INTEGER:
    case LONGINT:
    case BRUCH: 
        erg += add_scalar_sqrad(b,a,c);
        break;
    case POLYNOM:
        erg += add_scalar_polynom(a,b,c);
        break;
    case SQ_RADICAL:
        erg += add_sqrad_sqrad(a,b,c);
        break;
    case EMPTY:
        erg += copy_number(a,c);
        break;
    default:
        WTO("add_sqrad(2)",b);
        goto ende;
    };
    if (space_saving)
        convert_sqrad_scalar(c);

ende:
    ENDR("add_sqrad");
}
#endif /* SQRADDTRUE */

INT mult_sqrad(a,b,c) OP a,b,c;
/* AK 200291 V1.2 */ /* 24.07.91: TPMcD. */
/* typ a ist SQ_RADICAL */
/* AK 130891 V1.3 */
/* 04.10.91: TPMcD */
/* AK 060498 V2.0 */
{    
    INT erg = OK;
    CTO(SQ_RADICAL,"mult_sqrad(1)",a);
    if (S_O_K(c)!=EMPTY) FREESELF(c);


    switch(S_O_K(b))
    {
    case INTEGER:
    case LONGINT:
    case CYCLOTOMIC:
    case BRUCH: 
        erg += mult_scalar_sqrad(b,a,c); 
        goto ende;;

#ifdef MATRIXTRUE
    case MATRIX: 
        erg += mult_scalar_matrix(a,b,c); 
        break;
#endif /* MATRIXTRUE */

#ifdef MONOMTRUE
    case MONOM: /* AK 200291 */
        erg += mult_scalar_monom(a,b,c); 
        break;
#endif /* MONOMTRUE */

    case SQ_RADICAL: 
        erg += mult_sqrad_sqrad(a,b,c); 
        break;

#ifdef POLYTRUE
    case POLYNOM: /* AK 200291 */
        erg +=  mult_scalar_polynom(a,b,c); 
        break;
#endif /* POLYTRUE */

#ifdef SCHUBERTTRUE
    case SCHUBERT: /* AK 200291 */
        erg +=  mult_scalar_schubert(a,b,c); 
        break;
#endif /* SCHUBERTTRUE */

    case VECTOR: 
        erg += mult_scalar_vector(a,b,c); 
        break;

    default:
        WTO("mult_sqrad(2)",b);
        break;
    }
    if (space_saving)
        convert_sqrad_scalar(c);
ende:
    ENDR("mult_sqrad");
}

#ifdef    MONOPOLYTRUE
INT addinvers_sqrad(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    if (S_O_K(a) != SQ_RADICAL)
        return error("addinvers_sqrad:object not sqrad");
    find_sqrad_data(a);
    mult_scalar_sqrad(cons_negeins,a,b);
    return(OK);
}
#endif /* MONOPOLYTRUE */

#ifdef    SQRADTRUE
INT invers_sqrad(a,b) OP a,b;
/* 23.06.90: TPMcD. */ /* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{    
    INT    ret = OK;
    INT    flag = 0L;
    OP    b_tmp=NULL, y_tmp, new, ptr,  prime, x_tmp = CALLOCOBJECT(),
        data_length = CALLOCOBJECT(), mono_length = CALLOCOBJECT();

    if (S_O_K(a) != SQ_RADICAL)
    {    
        ret    += invers(a,b);    /*    try the general routine    */
        goto exit_label;
    }
    ret += find_sqrad_data(a);
    if (nullp_sqrad(a))
        error("invers_sqrad: 0 has no inverse\n");
    if (b == a)
    {    
        b_tmp    = CALLOCOBJECT();
        flag    = 1L;
    }
    else
        b_tmp    = b;
    ret += init(SQ_RADICAL,b_tmp);
    ret += init(MONOPOLY,S_N_S(b_tmp));
    ret += length(S_N_D(a),data_length);
    ret += length(S_N_S(a),mono_length);
    if (nullp(data_length))    /*    No radicals    */
    {    
        ptr    = S_N_S(a);
        ret += invers(S_PO_K(ptr),x_tmp);
        new    = CALLOCOBJECT();
        ret += m_sk_mo(cons_eins,x_tmp,new);
        insert_list(new,S_N_S(b_tmp),NULL,NULL);
        goto exit_label;
    }
    else if (einsp(mono_length))    /*    One radical    */
    {    
        ptr    = S_N_S(a);
        mult(S_PO_S(ptr),S_PO_K(ptr),x_tmp);
        invers(x_tmp,x_tmp);
        new    = CALLOCOBJECT();
        m_sk_mo(S_PO_S(ptr),x_tmp,new);
        insert_list(new,S_N_S(b_tmp),NULL,NULL);
        ret    = OK;
        goto exit_label;
    }
    /*    more than one radical    */
    /*    the conjugate is built up in b_tmp    */

    y_tmp    = CALLOCOBJECT();
    copy(a,x_tmp);
    make_scalar_sqrad(cons_eins,b_tmp);
    ptr    = S_N_D(a);
    while (ptr != NULL)
    {    
        prime        = S_L_S(ptr);
        if (S_O_K(x_tmp) != SQ_RADICAL)
            make_scalar_sqrad(x_tmp,x_tmp);
        conj_sqrad(x_tmp,prime,y_tmp);
        if (comp_sqrad(x_tmp,y_tmp) != 0L)
        {    
            mult_sqrad_sqrad(x_tmp,y_tmp,x_tmp);
            mult_sqrad_sqrad(b_tmp,y_tmp,b_tmp);
        }
        ptr    = S_L_N(ptr);
    }
    /*    at this point x_tmp should be scalar    */
    if (convert_sqrad_scalar(x_tmp) == ERROR)
    {    
        freeall(y_tmp);
        error("invers_sqrad: the norm is not a scalar\n");
        goto exit_label;
    }
    if (negp(x_tmp))
    {    
        ret +=  mult_apply_scalar_sqrad(cons_negeins,b_tmp);
        ret += addinvers_apply(x_tmp);
    }

    ret += invers(x_tmp,y_tmp);
    ret += mult_apply_scalar_sqrad(y_tmp,b_tmp);

    ret += freeall(y_tmp);
exit_label:
    if (flag)
    {    
        copy(b_tmp,b);
        freeall(b_tmp);
    }
    freeall(x_tmp); 
    freeall(data_length); 
    freeall(mono_length);
    return(ret);
}



INT add_apply_sqrad(a,b) OP a,b;
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{    
    INT    erg=OK;
    OP    c = CALLOCOBJECT();
    erg += add_sqrad(a,b,c);
    erg += copy(c,b);
    erg += freeall(c);
    return erg;
}
#endif /* SQRADTRUE */

INT mult_apply_sqrad(a,b) OP a,b;
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{    
    INT    ret = ERROR;
#ifdef SQRADTRUE
    OP    c;
    c = CALLOCOBJECT();
    ret    = mult_sqrad(a,b,c);
    copy(c,b);
    freeall(c);
#endif /* SQRADTRUE */
    return(ret);
}

#ifdef SQRADTRUE
INT addinvers_apply_sqrad(a) OP a;
/* AK 200891 V1.3 */
{
    INT erg = OK;
    OP b;
    CTO(SQ_RADICAL,"addinvers_apply_sqrad(1)",a);
    b = CALLOCOBJECT();
    SWAP(a,b);
    erg += addinvers_sqrad(b,a);
    FREEALL(b);
    ENDR("addinvers_apply_sqrad");
}



INT nullp_sqrad(a) OP a;
/* 1.04.91: TPMcD. */
/* AK 200891 V1.3 */
{
    INT erg = OK;
    OP ptr;
    CTO(SQ_RADICAL,"nullp_sqrad(1)",a);
    ptr = S_N_S(a);
    if (nullp_monopoly(ptr))
        return(TRUE);
    return(FALSE);
    ENDR("nullp_sqrad");
}

INT einsp_sqrad(a) OP a;
/* AK 230402 */
{
    INT erg = OK;
    OP ptr;
    CTO(SQ_RADICAL,"einsp_sqrad(1)",a);
    ptr  = S_N_S(a);
    if (ptr == NULL) return FALSE;
    if (S_L_S(ptr) == NULL) return FALSE;
    if (not EINSP(S_PO_S(ptr))) return FALSE;
    if (not EINSP(S_PO_K(ptr))) return FALSE;
    if (S_PO_N(ptr) != NULL) return FALSE;
    return TRUE;
    
    ENDR("einsp_sqrad");
}
#endif /* SQRADTRUE */

#ifdef CYCLOTRUE
INT einsp_cyclotomic(a) OP a;
/* AK 240402 */
{
    INT erg = OK;
    OP ptr;
    CTO(CYCLOTOMIC,"einsp_cyclotomic(1)",a);
    ptr  = S_N_S(a);
    if (ptr == NULL) return FALSE;
    if (S_L_S(ptr) == NULL) return FALSE;
    if (not EINSP(S_PO_S(ptr))) return FALSE;
    if (not EINSP(S_PO_K(ptr))) return FALSE;
    if (S_PO_N(ptr) != NULL) return FALSE;
    return TRUE;
 
    ENDR("einsp_cyclotomic");
}          
#endif /*CYCLOTRUE */

INT comp_sqrad(a,b) OP a,b;
/* AK 200891 V1.3 */
{
#ifdef SQRADTRUE
    return(comp_list(S_N_S(a),S_N_S(b)));
#endif /* SQRADTRUE */
}

#ifdef SQRADTRUE
static INT fprint_sqrad(f,a) FILE *f; 
    OP a;
/* 25.09.91: TPMcD. */
{    
    INT myfirst = 1L, rational = 0L;
    OP    ptr;
    ptr = S_N_S(a);
    zeilenposition    += 4L;
    if (nullp_sqrad(a))
    {    
        fprintf(f," 0");
        return(OK);
    }
    while (ptr != NULL)
    {       
        if (zeilenposition > 60L)
        {       
            zeilenposition  = 0L;
            fprintf(f,"\n");
        }
        if (einsp(S_PO_S(ptr)))
            rational    = 1L;    /* A rational term    */
        else
            rational    = 0L;
        /*    print the coefficient part of a term    */
        if (!negp(S_PO_K(ptr)) && !myfirst)
            fprintf(f," +");
        if (negeinsp(S_PO_K(ptr)))
        {    
            if (rational)
                fprintf(f," - 1");
            else
                fprintf(f," -");
        }
        else if (einsp(S_PO_K(ptr)))
        {    
            if (rational)
                fprintf(f," 1");
        }
        else
        {
            fprintf(f," ");
            fprint(f,S_PO_K(ptr));
        }

        if (not rational)        /*    print the radical part of a term    */
        {    
            fprintf(f," sqr(");
            fprint(f,S_PO_S(ptr));
            fprintf(f,")");
            zeilenposition    += 6L;
        }
        ptr    = S_L_N(ptr);
        myfirst = 0L;
    }
    return(OK);
}
#endif /* SQRADTRUE */

INT tex_sqrad(a) OP a;
/* 020491: TPMcD. */
/* AK 200891 V1.3 */
/* 041091: TPMcD */
{    
    INT myfirst = 1L;
# ifdef    SQRADTRUE
    OP    ptr = S_N_S(a);
    find_sqrad_data(a);
    if (nullp_sqrad(a))
    {    
        fprintf(texout," 0\n");
        return(OK);
    }
    fprintf(texout," ");
    while (ptr != NULL)
    {    
        if (!negp(S_PO_K(ptr)) && !myfirst)
            fprintf(texout," + {");
        else
            fprintf(texout,"{");
        tex(S_PO_K(ptr));
        if (NEQ(S_PO_S(ptr),cons_eins))
        {    
            fprintf(texout,"} \\sqrt{");
            tex(S_PO_S(ptr));
        }
        fprintf(texout,"}");
        ptr    = S_L_N(ptr);
        myfirst = 0L;
    }
    fprintf(texout," ");
    return(OK);
#else
    error("tex_sqrad: SQ_RADICAL not available");
    return(ERROR);
#endif
}

static INT find_sqrad_data(a) OP a;
/* 23.06.90: TPMcD. */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{
#ifdef    SQRADTRUE
    OP    new, num, next_num, ptr, next_ptr, data_ptr, list_ptr,
        list_copy = CALLOCOBJECT(),    prime_list = CALLOCOBJECT(),
        quo = CALLOCOBJECT(), rem = CALLOCOBJECT();

    if (S_N_D(a) == NULL)
        S_N_D(a)    = CALLOCOBJECT();
    data_ptr    = S_N_D(a);
    /*    Assume the data is OK if it is a non-empty LIST    */
    if (not EMPTYP(data_ptr) && S_O_K(data_ptr) == LIST
        && not empty_listp(data_ptr))
        {
        goto fsd_ende;
        }
    init(LIST,data_ptr);
    copy(S_N_S(a),list_copy);
    ptr    = list_copy;
    num    = S_PO_S(ptr);
    if (LT(num,cons_null) == TRUE)    /*    negative radicals    */
    {    
        new    = CALLOCOBJECT();
        M_I_I(-1L,new);
        insert_list(new,data_ptr,NULL,NULL);
        while (ptr != NULL)    /*multiply negative radicals by -1*/
        {    
            num    = S_PO_S(ptr);
            if (LT(num,cons_null) == TRUE)
                addinvers_apply(num);
            else
                break;
            ptr    = S_L_N(ptr);
        }
    }
    ptr    = list_copy;
    while (ptr != NULL)
    {    
        num    = S_PO_S(ptr);
        if (not einsp(num) && not nullp(num))
        {    
            integer_factor(num,prime_list);
            list_ptr    = prime_list;
            while (list_ptr != NULL)
            {    
                new    = CALLOCOBJECT();
                copy(S_PO_S(list_ptr),new);/* new is the next prime    */
                next_ptr    = S_L_N(ptr);
                while (next_ptr != NULL)
                {    
                    next_num    = S_PO_S(next_ptr);
                    if (NEQ(next_num,cons_eins) == TRUE)
                    {    
                        nb_quores(next_num,new,quo,rem);
                        if (nullp(rem)) /* AK 120891 */
                            copy(quo,next_num);
                    }
                    next_ptr    = S_L_N(next_ptr);
                }
                insert_list(new,data_ptr,NULL,NULL);
                list_ptr    = S_L_N(list_ptr);
            }
            freeself(prime_list);
        }
        ptr    = S_L_N(ptr);
    }
fsd_ende:
    freeall(list_copy); 
    freeall(prime_list); 
    freeall(rem); 
    freeall(quo);
    return(OK);
#else
    error("find_sqrad_data: SQ_RADICAL not available");
    return(ERROR);
#endif
}

/*    a: the sqrad */

static INT adjust_sqrad_data(a) OP a;
/* 15.04.91: TPMcD. */
/* AK 200891 V1.3 */
{    
    INT    inserted = 1L;
    INT erg = OK;

    OP    new=NULL, quo, rem, ptr, data_ptr, a_copy, prime_list, num_ptr;
    if (S_O_K(a) != SQ_RADICAL)
        return(ERROR);
    if (S_N_D(a) == NULL || EMPTYP(S_N_D(a)))
        return(find_sqrad_data(a));
    if (empty_listp(S_N_D(a)))
        return(OK);
    prime_list    = CALLOCOBJECT();
    init(LIST,prime_list);
    a_copy    = CALLOCOBJECT();
    copy(a,a_copy);
    ptr    = S_N_S(a_copy);
    num_ptr    = S_PO_S(ptr);
    if (LT(num_ptr,cons_null) == TRUE)    /*negative radicals    */
    {    
        new    = CALLOCOBJECT();
        M_I_I(-1L,new);
        insert_list(new,prime_list,NULL,NULL);
        while (ptr != NULL)/*multiply negative radicals by -1    */
        {    
            num_ptr    = S_PO_S(ptr);
            if (LT(num_ptr,cons_null) == TRUE)
                addinvers_apply(num_ptr);
            else
                break;
            ptr    = S_L_N(ptr);
        }
    }
    data_ptr    = S_N_D(a);
    quo = CALLOCOBJECT();
    rem = CALLOCOBJECT();
    while (data_ptr != NULL)
    {
    if (negeinsp(S_L_S(data_ptr))) /* negatives have been taken care of*/
        {    
            data_ptr    = S_L_N(data_ptr);
            continue;
        }
        if (inserted)
            new    = CALLOCOBJECT();
        copy(S_L_S(data_ptr),new);    /* new is the next prime*/
        inserted    = 0L;
        ptr    = S_N_S(a_copy);
        while (ptr != NULL)
        {    
            num_ptr    = S_PO_S(ptr);
            if (einsp(num_ptr) || nullp(num_ptr))
            {    
                ptr    = S_L_N(ptr);
                continue;
            }
            nb_quores(num_ptr,new,quo,rem);
            if (nullp(rem))
            {    
                copy(quo,num_ptr);
                if (not inserted)
                {    
                    insert(new,prime_list,NULL,NULL);
                    inserted    = 1L;
                }
            }
            ptr    = S_L_N(ptr);
        }
        data_ptr    = S_L_N(data_ptr);
    }
    if (not inserted)
        FREESELF(new);
    else
        new    = CALLOCOBJECT();
    make_monopoly_sqrad(S_N_S(a_copy),new);    /* reconstitute the sqrad */
    if (convert_sqrad_scalar(new) == ERROR)
    {
        FREESELF(S_N_D(a));
        FREEALL(prime_list);
        find_sqrad_data(a);
    }
    else
    {    
        FREEALL(S_N_D(a));
        S_N_D(a)    = prime_list;
    }
    FREEALL(quo); 
    FREEALL(rem); 
    FREEALL(new); 
    FREEALL(a_copy);
    return(OK);
    ENDR("adjust_sqrad_data");
}

/*    a: the sqrad; b: the radical; c: the conjugate    */

INT conj_sqrad(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{    
    OP    la, lb, rem, minus, ptr, new;
#ifdef    SQRADTRUE

    if (not EMPTYP(c))  /* AK 060993 */
        freeself(c);

    la = CALLOCOBJECT(); 
    lb = CALLOCOBJECT();
    rem = CALLOCOBJECT(); 
    minus = CALLOCOBJECT();
    M_I_I(-1L,minus);
    init(MONOPOLY,la);
    init(MONOPOLY,lb);
    ptr    = S_N_S(a);
    if (EQ(b,minus) == TRUE)
        while (ptr != NULL)
        {    
            new    = CALLOCOBJECT();
            copy(S_L_S(ptr),new);
            if (LT(S_MO_S(new),cons_null) == TRUE)
                insert_list(new,lb,NULL,NULL);
            else
                insert_list(new,la,NULL,NULL);
            ptr    = S_L_N(ptr);
        }
    else
        while (ptr != NULL)
        {    
            new    = CALLOCOBJECT();
            copy(S_L_S(ptr),new);
            mod(S_MO_S(new),b,rem);
            if (nullp(rem)) /* AK 120891 */
                insert_list(new,lb,NULL,NULL);
            else
                insert_list(new,la,NULL,NULL);
            ptr    = S_L_N(ptr);
        }
    if (empty_listp(lb))
        insert_zero_into_monopoly(lb);
    mult_apply_scalar_monopoly(minus,lb);
    insert(lb,la,NULL,NULL);
    if (c == a)
        freeall(S_N_S(a));
    else
        {    
            init(SQ_RADICAL,c);
            copy(S_N_D(a),S_N_D(c));
        }
    remove_zero_terms(la);
    if (S_N_S(c) != NULL)
        {
        freeall(S_N_S(c)); /* AK 060993 */
        }
    S_N_S(c)    = la;
    freeall(rem);    
    freeall(minus);
    return(OK);
#else /* SQRADTRUE */
    error("conj_sqrad: SQ_RADICAL not available");
    return(ERROR);
#endif /* SQRADTRUE */
}

#ifdef SQRADTRUE
INT squareroot_integer(a,b) OP a,b;
/* AK 040291 V1.2 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP c;
    CTTO(INTEGER,LONGINT,"squareroot_integer(1)",a);
    CTO(EMPTY,"squareroot_integer(2)",b);

    if (NULLP_INTEGER(a)) {
        M_I_I(0,b);
        goto ende;
        }

    c = CALLOCOBJECT();
    erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,c);
    COPY_INTEGER(a,S_PO_S(c));
    M_I_I(1,S_PO_K(c));
    erg += make_monopoly_sqrad(c,b);
    FREEALL(c);
ende:
    ENDR("squareroot_integer");
}



INT squareroot_longint(a,b) OP a,b;
/* AK 040291 V1.2 */ /* AK 200891 V1.3 */
{
    return squareroot_integer(a,b);
}
#endif /* SQRADTRUE */

#ifdef    SQRADTRUE
INT squareroot_bruch(a,b) OP a,b;
/* AK 040291 V1.2 */ /* AK 200891 V1.3 */ /* 04.10.91: TPMcD */
{
    INT erg=OK;
    OP  c,d;
    CTO(BRUCH,"squareroot_bruch(1)",a);
    CTO(EMPTY,"squareroot_bruch(2)",b);
    
   
    c = CALLOCOBJECT(); 
    d = CALLOCOBJECT();
    MULT(S_B_O(a),S_B_U(a),c);
    erg += squareroot(c,b);
    erg += invers(S_B_U(a),d);
    MULT_APPLY(d,b);
    FREEALL(c);
    FREEALL(d);
    CTO(SQ_RADICAL,"squareroot_bruch(e2)",b);
    ENDR("squareroot_bruch");
}



INT convert_sqrad_scalar(a) OP a;
/* 5.04.91: TPMcD. */ /* AK 200891 V1.3 */
{    
    INT    ret = ERROR;
    OP tmp;
    if (S_O_K(a) != SQ_RADICAL || S_L_N(S_N_S(a)) != NULL)
        return(ret);
    tmp    = S_PO_S(S_N_S(a));
    if (not einsp(tmp) && not nullp(tmp))
        return(ret);
    ret    = OK;
    if (nullp(tmp))
    {    
        m_i_i(0L,a);
        return(ret);
    }
    tmp    = CALLOCOBJECT();
    copy(S_PO_K(S_N_S(a)),tmp);
    copy(tmp,a);
    freeall(tmp);
    return OK;
}
#endif /* SQRADTRUE */

/*    Convert the square root of an integer a to a cyclotomic number    */

INT convert_radical_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */ /* 29.10.91: TPMcD */
{    
    INT    myeven, posi, last = 1L,ff=0;
    OP    new, ptr, mono_ptr;
    INT    erg = OK;
# ifdef NUMBERTRUE
    OP k,m,mpos,x,y,z,w,atmp,four;


    CTTO(INTEGER,LONGINT,"convert_radical_cyclo(1)",a);
    if (EINSP(a)) ff=1;


    k = CALLOCOBJECT();
    m = CALLOCOBJECT();
    mpos = CALLOCOBJECT();
    x = CALLOCOBJECT();
    y = CALLOCOBJECT();
    z = CALLOCOBJECT();
    w = CALLOCOBJECT();
    four = CALLOCOBJECT();

    
   
    if (not negp(a) && nb_square_root(a,k) == OK)
    {    
        make_scalar_cyclo(k,b);
        goto exit_label;
    }
    if (a == b)
    {    
        atmp    = CALLOCOBJECT();
        copy(a,atmp);
    }
    else
        atmp    = a;
    
    
    FREESELF(b); INIT_CYCLO(b);

    mono_ptr    = CALLOCOBJECT();
    init(MONOPOLY,mono_ptr);
    M_I_I(4L,four);
    integer_factor_1(atmp,cons_zwei,cons_zwei,m,y,NULL);
    /*    a = 4k * 2l * m
     *  l=0 ,m=1(4): return 2k * r(m)
     *    l=0 ,m=3(4): return 2(k-1) * r(4*m)
     *    l=1            return 2(k-1) * r(8*m)
     */
    ptr    = y;
    if (empty_listp(ptr))    /*    a > 0 and a is odd    */
    {    
        myeven    = 0L;
        posi    = 1L;
    }
    else if (EQ(S_PO_S(ptr),cons_zwei))    /*    a > 0 and a is even    */
    {    
        myeven    = 1L;
        posi    = 1L;
    }
    else
    {    
        ptr    = S_L_N(ptr);
        if (ptr == NULL)    /*    a < 0 and a is odd    */
        {    
            myeven    = 0L;
            posi    = 0L;
        }
        else
        {    
            myeven    = 1L;
            posi    = 0L;
        }
    }
    if (!posi)
        addinvers_apply(m);
    if (myeven)
    {    
        nb_quores(S_PO_K(ptr),cons_zwei,k,z);
        if (NULLP(z)) /* AK 120891 */    /*    a = 4k * m    */
            last = 0L;
        hoch(cons_zwei,k,w);            /*    w = 2k    */
    }
    else
    {    
        copy(cons_eins,w);
        last = 0L;
    }
    if (!last)
    {    
        mod(m,four,z);
        if (!EINSP(z))
        {    
            div_apply(w,cons_zwei);
            MULT_APPLY(four,m);
        }
    }
    else
    {    
        div_apply(w,cons_zwei); /* w := w/2 */
        MULT_APPLY(four,m);
        MULT_APPLY(cons_zwei,m);
    }
    copy(m,mpos);
    if (NEGP(mpos))
        addinvers_apply(mpos);
    make_coprimes(mpos,y);
    ptr    = y;
    while (ptr != NULL)
    {    
        if (kronecker(m,S_L_S(ptr),z) == OK)
        {    
            new    = CALLOCOBJECT();
            m_sk_mo(S_L_S(ptr),z,new);
            insert(new,mono_ptr,add_koeff,NULL);
        }
        ptr    = S_L_N(ptr);
    }
    remove_zero_terms(mono_ptr);
    make_index_monopoly_cyclo(mpos,mono_ptr,b,0L);
    MULT_APPLY(w,b);

    FREEALL(mono_ptr);
    if (a == b)
        FREEALL(atmp);
exit_label:
    FREEALL(k); 
    FREEALL(m); 
    FREEALL(mpos); 
    FREEALL(x); 
    FREEALL(y); 
    FREEALL(z);
    FREEALL(w); 
    FREEALL(four);
    erg += standardise_cyclo_0(b,basis_type);
    { /* so to get the positive squareroot */
    double realpart=0.0;
    double fac = 6.2830 / ((double) S_N_DCII(b) );
    FORALL(w,S_N_S(b), {
        realpart += (double)(S_MO_KI(w)) * cos( fac* (double)S_I_I(S_MO_S(w)) ); 
        });
    

    if (realpart < 0.0 ) 
    if (ff==0) ADDINVERS_APPLY(b);
    }
# endif
    CTO(ANYTYPE,"convert_radical_cyclo(e2)",b);
    ENDR("convert_radical_cyclo");
}


# ifdef NUMBERTRUE
INT convert_sqrad_cyclo(a,b) OP a,b;
/* 29.10.91: TPMcD */
{    
    OP c, ptr;
    INT erg = OK;
    CTO(SQ_RADICAL,"convert_sqrad_cyclo(1)",a);
    CE2(a,b,convert_sqrad_cyclo);

    M_I_I(0,b);

    c    = CALLOCOBJECT();
    ptr    = S_N_S(a);
    while (ptr != NULL)
        {    
        convert_radical_cyclo(S_PO_S(ptr),c);
        MULT_APPLY(S_PO_K(ptr),c);  
        ADD_APPLY(c,b);
        ptr    = S_L_N(ptr);
        }

    FREEALL(c);
    ENDR("convert_sqrad_cyclo");
}
#endif /* NUMBERTRUE */

/******************        fields_3.c        **********************/
/* 26.07.91: TPMcD.                                             */
/*************************************************************/

/*    CYCLOTOMIC    */

/*    a : the index, b : the monopoly, c : the result    */

INT trans_index_monopoly_cyclo(a,b,c) OP a,b,c;
/* AK 300791 for compatibility */
/* AK 200891 V1.3 */
{
    return make_index_monopoly_cyclo(a,b,c,POWER_REDUCE);
}

static INT make_index_monopoly_cyclo(a,b,c,tid) OP a,b,c; INT tid;
/* 30.05.90: TPMcD. */ /* 3.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{    
    OP    c_tmp;
    INT    flag = 0L;
    INT erg = OK;
    CYCLO_DATA    *c_ptr = NULL;

    if (S_O_K(b) != MONOPOLY)
        error("make_index_monopoly_cyclo: 2nd parameter is wrong type\n");
    if ((c_ptr = add_cyclo_data(a)) == (CYCLO_DATA *) NULL)
        error("make_index_monopoly_cyclo: unable to create cyclotomic data\n");
    if (c == b)
    {    
        flag    = 1L;
        c_tmp    = CALLOCOBJECT();
    }
    else
    {    
        FREESELF(c); INIT_CYCLO(c);
        c_tmp    = S_N_S(c);
    }
    init(MONOPOLY, c_tmp);
    if (empty_listp(c_tmp))
        insert_zero_into_monopoly(c_tmp);
    copy(b, c_tmp);
    if (flag)
    {    
        init(CYCLOTOMIC,c);
        S_N_S(c)    = c_tmp;
    }
    S_N_DC(c)    = c_ptr;
    if (tid != NO_REDUCE)
        standardise_cyclo_0(c,tid);
    ENDR("make_index_monopoly_cyclo");
}

INT standardise_cyclo(a) OP a;
/* 25.10.91: TPMcD */
{
    return(standardise_cyclo_0(a,basis_type));
}

static INT standardise_cyclo_0(a,tid) OP a; 
    INT tid;
/* 09.09.90: TPMcD. */ /* 4.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 25.10.91: TPMcD */
{    
    INT    erg=OK, ret = ERROR;
    CYCLO_DATA    *c_ptr;
    OP    ptr, new, mono, e, poly_eins, poly_zwei;
/*    OP half=NULL; */
    

    if (S_O_K(a) != CYCLOTOMIC || tid == NO_REDUCE)
        return(OK);

/*
    if (EVEN(S_N_DC(a)->index)) {
        half = CALLOCOBJECT();
        ganzdiv(S_N_DC(a)->index,cons_zwei,half);
        }
*/
    ptr        = S_N_S(a);
    c_ptr    = S_N_DC(a);
    mono    = CALLOCOBJECT();
    init(MONOPOLY,mono);
    e    = CALLOCOBJECT();
    if ( not empty_listp(ptr))
        while (ptr != NULL)
        {    
            erg =  mod(S_PO_S(ptr),c_ptr->index,e);
            new     = CALLOCOBJECT();
            m_sk_mo(e,S_PO_K(ptr),new);
/*
            if (EVEN(c_ptr->index)) 
                if (GE(e,half)) {
                    sub_apply(half,S_MO_S(new));
                    ADDINVERS_APPLY(S_MO_K(new));
                }
*/
            insert(new,mono,add_koeff,NULL);
            ptr = S_L_N(ptr);
        }
    FREEALL(e);

    /* if (EVEN(S_N_DC(a)->index)) FREEALL(half); */

    if (empty_listp(mono))
        insert_zero_into_monopoly(mono);
    switch((int)tid)
    {    
    case (int)POWER_REDUCE:
        poly_zwei    = mono;
        break;
    case (int)STD_BASIS:
        poly_eins    = CALLOCOBJECT();
        poly_zwei    = CALLOCOBJECT();
        quores_monopoly(mono,c_ptr->poly,poly_eins,poly_zwei);
        FREEALL(mono); 
        FREEALL(poly_eins);
        break;
    default:
        return error("standardise_cyclo_0: unknown cyclotomic basis");
        break;
    }
    FREEALL(S_N_S(a));
    S_N_S(a)    = poly_zwei;
    ret    = OK;
    return(ret);
    ENDR("standardise_cyclo_0");
}

#ifdef    CYCLOTRUE
INT make_scalar_cyclo(a,b) OP a,b;
/* 5.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
    OP c = CALLOCOBJECT(); 
    OP d = CALLOCOBJECT();
    M_I_I(1L,c);
    b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,d);
    copy(a,S_PO_K(d));
    M_I_I(0L,S_PO_S(d));
    make_index_monopoly_cyclo(c,d,b,NO_REDUCE);
    freeall(c); 
    freeall(d);
    return(OK);
}


INT make_index_power_cyclo(a,c,d) OP a,c,d;
{
    return make_index_coeff_power_cyclo(a,cons_eins,c,d);
}

INT make_index_coeff_power_cyclo(a,b,c,d) OP a,b,c,d;
/* 30.05.90: TPMcD. */ /* 17.07.91: TPMcD. */
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{
    INT erg = OK;
    erg += init(CYCLOTOMIC,d);
    erg += b_skn_mp(CALLOCOBJECT(),CALLOCOBJECT(),NULL,S_N_S(d));
    erg += mod(c,a,S_PO_S(S_N_S(d)));
    erg += copy(b,S_PO_K(S_N_S(d)));

    if (S_N_DC(d) != NULL)
        error("internal error:MIC1");

    S_N_DC(d)    = add_cyclo_data(a);

    if (space_saving)
        convert_cyclo_scalar(d);

    ENDR("make_index_coeff_power_cyclo");
}


INT scan_cyclo(a) OP a;
/* AK 240191 V1.2 */ /* a becomes cyclotomic */
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{
    OP b = CALLOCOBJECT(); 
    OP c = CALLOCOBJECT();
    INT erg = OK;
    erg += printeingabe("degree of cyclotomic field");
    erg += scan(INTEGER,b);
    erg += printeingabe("self of cyclotomic field");
    erg += scan(MONOPOLY,c);
    erg += make_index_monopoly_cyclo(b,c,a,basis_type);
    erg += freeall(b); 
    erg += freeall(c);
    return erg;
}
#endif /* CYCLOTRUE */

/*    a: the scalar, b: the cyclo, c: the result    */

INT add_scalar_cyclo(a,b,c) OP a,b,c;
/* 30.05.90: TPMcD. */ /* AK 080891 V1.3 */ /* 23.10.91: TPMcD */
{    
    OP    ptr; 
    INT erg = OK;
#ifdef    CYCLOTRUE
    if (c == a)
        error("First and third arguments equal\n");
    if (c != b)
        copy(b,c);
    ptr    = CALLOCOBJECT();
    erg += init(MONOPOLY,ptr);
    C_L_S(ptr,CALLOCOBJECT());
    erg += m_sk_mo(cons_null,a,S_L_S(ptr));
    erg += add_apply(ptr,S_N_S(c));
    erg += freeall(ptr);
    if (space_saving)
        convert_cyclo_scalar(c);
#endif /* CYCLOTRUE */
    return erg;
}

/*    a: the scalar, b: the cyclo, c: the result */

#ifdef    CYCLOTRUE
INT mult_apply_scalar_cyclo(a,b) OP a,b;
/* AK 060498 V2.0 */
{
    OP c;
    INT erg = OK;
    CTO(CYCLOTOMIC,"mult_apply_scalar_cyclo",b);
    c = CALLOCOBJECT();
    SWAP(c,b);
    erg += mult_scalar_cyclo(a,c,b);
    erg += freeall(c);
    ENDR("mult_apply_scalar_cyclo");
}

INT mult_scalar_cyclo(a,b,c) OP a, b, c;
/* 06.09.90: TPMcD. */ /* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{    
    INT erg = OK;
    CTO(CYCLOTOMIC,"mult_scalar_cyclo(2)",b);
    CTO(EMPTY,"mult_scalar_cyclo(3)",c);

    if (NULLP(a)) {
        M_I_I(0,c);
        }
    else {
        erg += init(CYCLOTOMIC,c);
        FREESELF(S_N_S(c));
        erg += mult_scalar_monopoly(a,S_N_S(b),S_N_S(c));
        S_N_DC(c)    = S_N_DC(b);
        if (space_saving)
            convert_cyclo_scalar(c);
        }
    ENDR("mult_scalar_cyclo");
}

#endif
/*    a,b: the cyclos, c: the result    */

INT add_cyclo_cyclo(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
    return( add_cyclo_cyclo_0(a,b,c,basis_type) );
}

static INT add_cyclo_cyclo_0(a,b,c,tid) OP a,b,c; INT tid;
/* 06.09.90: TPMcD. */ /* 5.04.91: TPMcD. */
/* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{
    OP    temp_eins, temp_zwei, temp_drei, temp_vier;
    INT erg = OK;

    if (S_O_K(a) != CYCLOTOMIC || S_O_K(b) != CYCLOTOMIC)
        return( error ("add_cyclo_cyclo_0: argument not CYCLOTOMIC") );
    temp_eins = CALLOCOBJECT();    
    temp_zwei = CALLOCOBJECT();
    temp_drei = CALLOCOBJECT();    
    temp_vier = CALLOCOBJECT();
    copy(S_N_S(a),temp_eins);
    copy(S_N_S(b),temp_zwei);
    ggt(S_N_DCI(a),S_N_DCI(b),temp_drei);
    ganzdiv(S_N_DCI(a),temp_drei,temp_vier);
    raise_power_monopoly(temp_vier,temp_zwei);
    ganzdiv(S_N_DCI(b),temp_drei,temp_vier);
    raise_power_monopoly(temp_vier,temp_eins);
    MULT_APPLY(S_N_DCI(a),temp_vier);
    init(CYCLOTOMIC, c);
    FREESELF(S_N_S(c));
    add_monopoly_monopoly(temp_eins,temp_zwei,S_N_S(c));
    S_N_DC(c)    = add_cyclo_data(temp_vier);
    if (tid != NO_REDUCE)
        standardise_cyclo_0(c,tid);
    if (space_saving)
        convert_cyclo_scalar(c);
    FREEALL(temp_eins); 
    FREEALL(temp_zwei); 
    FREEALL(temp_drei); 
    FREEALL(temp_vier);
    ENDR("nb.c:add_cyclo_cyclo_0");
}

INT mult_cyclo_cyclo(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
{    
    INT    erg = OK;
    CTO(CYCLOTOMIC,"mult_cyclo_cyclo(1)",a);
    CTO(CYCLOTOMIC,"mult_cyclo_cyclo(2)",b);
    CTO(EMPTY,"mult_cyclo_cyclo(3)",c);

    erg += mult_cyclo_cyclo_0(a,b,c,basis_type); /* AK return inserted */
    CTO(ANYTYPE,"mult_cyclo_cyclo(i3)",c);
    erg += standardise_cyclo_0(c,basis_type);
    CTO(ANYTYPE,"mult_cyclo_cyclo(e3)",c);
    ENDR("mult_cyclo_cyclo");
}

static INT mult_cyclo_cyclo_0(a,b,c,tid) OP a,b,c; INT tid;
/* 06.09.90: TPMcD. */ /* 5.04.91: TPMcD. */
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
    OP    temp_eins, temp_zwei, temp_drei, temp_vier;
    INT erg = OK;
    CTO(CYCLOTOMIC,"mult_cyclo_cyclo_0(1)",a);
    CTO(CYCLOTOMIC,"mult_cyclo_cyclo_0(2)",b);

    if ( (NULLP(a) || NULLP(b)) && space_saving )
    {    
        m_i_i(0L,c);
        return(OK);
    }
    temp_eins = CALLOCOBJECT();    
    temp_zwei = CALLOCOBJECT();
    temp_drei = CALLOCOBJECT();    
    temp_vier = CALLOCOBJECT();
    COPY(S_N_S(a),temp_eins);
    COPY(S_N_S(b),temp_zwei);
    ggt(S_N_DCI(a),S_N_DCI(b),temp_drei);
    ganzdiv(S_N_DCI(a),temp_drei,temp_vier);
    raise_power_monopoly(temp_vier,temp_zwei);
    ganzdiv(S_N_DCI(b),temp_drei,temp_vier);
    raise_power_monopoly(temp_vier,temp_eins);
    MULT_APPLY(S_N_DCI(a),temp_vier);
    init(CYCLOTOMIC, c);
    FREESELF(S_N_S(c));
    mult_monopoly_monopoly(temp_eins,temp_zwei,S_N_S(c));
    if ((S_N_DC(c) = add_cyclo_data(temp_vier)) == (CYCLO_DATA *) NULL)
        error("Unable to find cyclotomic data\n");
    if (tid != NO_REDUCE)
        standardise_cyclo_0(c,tid);
    if (space_saving)
        convert_cyclo_scalar(c);
    FREEALL(temp_eins); 
    FREEALL(temp_zwei);
    FREEALL(temp_drei); 
    FREEALL(temp_vier);
    ENDR("mult_cyclo_cyclo_0");
}

INT add_cyclo(a,b,c) OP a,b,c;
/* AK 070891 V1.3 */
{    
    INT erg = OK;
#ifdef    CYCLOTRUE
    switch(S_O_K(b))
    {    
    case INTEGER:
    case LONGINT:
    case SQ_RADICAL:
    case BRUCH:  
        erg += add_scalar_cyclo(b,a,c);
        break;
    case CYCLOTOMIC:  
        erg += add_cyclo_cyclo(a,b,c);
        break;
    case POLYNOM: 
        erg += add_scalar_polynom(a,b,c);
        break;
    default:
        printobjectkind(b);
        erg += error("add_cyclo: wrong second type\n");
        break;
    }
    convert_cyclo_scalar(c);
#endif
    return erg;
}

INT mult_cyclo(a,b,c) OP a,b,c;
/* 24.07.91: TPMcD. */
/* AK 200891 V1.3 */
{    
    INT erg = OK;
    CTO(CYCLOTOMIC,"mult_cyclo(1)",a);
    CTO(EMPTY,"mult_cyclo(3)",c);

    if (NULLP(a)){
        M_I_I(0,c);
        goto ende;
    }
    if (NULLP(b)){
        M_I_I(0,c);
        goto ende;
    }
    switch(S_O_K(b))
    {
    case INTEGER:
    case SQ_RADICAL: /* AK 220891 */
    case LONGINT:
    case BRUCH: 
        erg += mult_scalar_cyclo(b,a,c);
        break;
#ifdef MATRIXTRUE
    case MATRIX: 
        erg += mult_scalar_matrix(a,b,c);
        break;
#endif /* MATRIXTRUE */
#ifdef POLYTRUE
    case SCHUR:
    case POW_SYM:
    case HOM_SYM:
    case ELM_SYM:
    case MONOMIAL:
    case POLYNOM: 
        erg += mult_scalar_polynom(a,b,c);
        break;
#endif /* POLYTRUE */
#ifdef SCHUBERTTRUE
    case SCHUBERT: 
        erg +=  mult_scalar_schubert(a,b,c);
        break;
#endif /* SCHUBERTTRUE */
    case VECTOR: 
        erg += mult_scalar_vector(a,b,c);
        break;
    case CYCLOTOMIC: 
        erg += mult_cyclo_cyclo(a,b,c);
        break;
    default:
        WTO("mult_cyclo(2)",b);
        break;
    }
    convert_cyclo_scalar(c);
ende:
    ENDR("mult_cyclo");
}

INT addinvers_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT erg = OK;
    CTO(CYCLOTOMIC,"addinvers_cyclo(1)",a);
    CTO(EMPTY,"addinvers_cyclo(2)",b);
    erg += mult_scalar_cyclo(cons_negeins,a,b);
    CTO(CYCLOTOMIC,"addinvers_cyclo(e2)",b);
    ENDR("addinvers_cyclo");
}

/* a: the cyclo, b: the auto, c: the conjugate    */

INT conj_cyclo(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
/* 23.10.91: TPMcD */
{
# ifdef    CYCLOTRUE
    if (S_O_K(a) != CYCLOTOMIC)
        return(ERROR);
    if (c != a)
        copy(a,c);
    raise_power_monopoly(b,S_N_S(c));
    standardise_cyclo_0(c,basis_type);
# endif
    return(OK);
}

/*    a: the cyclo, b: the inverse    */

INT invers_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT    ret = ERROR;
# ifdef    CYCLOTRUE
    OP    c = CALLOCOBJECT();
    ret    = invers_cyclo_norm(a,b,c);
    freeall(c);
# endif
    return(ret);
}

/*    a: the cyclo, b: the inverse, c: the norm    */

static INT invers_cyclo_norm(a,b,c) OP a,b,c;
/* AK 200891 V1.3 */
{    
    INT    flag = 0L, saving = space_saving;
# ifdef    CYCLOTRUE
    OP    ptr, tmp, b_tmp;
    if (S_O_K(a) != CYCLOTOMIC)
        return(ERROR);
    if (nullp_cyclo(a))
        return(error("invers_cyclo_norm: cannot invert 0\n"));
    if (c == a || c == b)
        return(error("invers_cyclo_norm: illegal 3rd parameter\n"));
    if (b == a)
    {    
        b_tmp    = CALLOCOBJECT();
        flag    = 1L;
    }
    else
    {    
        if (not EMPTYP(b)) /* AK */
            freeself(b);
        b_tmp    = b;
    }
    space_saving    = FALSE;
    tmp    = CALLOCOBJECT();
    /*
    M_I_I(1L,tmp);
    */
    make_scalar_cyclo(cons_eins,b_tmp);
    ptr    = S_N_DC(a)->autos;
    ptr    = S_L_N(ptr);    /*    Skip the trivial automorphism    */
    while (ptr != NULL)
    {    
        conj_cyclo(a,S_L_S(ptr),tmp);
        mult_cyclo_cyclo_0(tmp,b_tmp,b_tmp,POWER_REDUCE);
        ptr    = S_L_N(ptr);
    }
    mult_cyclo_cyclo_0(a,b_tmp,tmp,basis_type);
    if (convert_cyclo_scalar(tmp) == ERROR)
    {    
        freeall(tmp);
        if (flag)
            freeall(b_tmp);
        return(error("invers_cyclo_norm: norm is not scalar\n"));
    }
    copy(tmp,c);
    if (negp(tmp))
    {    
        mult_scalar_sqrad(cons_negeins,b_tmp,b_tmp);
        addinvers_apply(tmp);
    }
    invers(tmp,tmp);
    mult_apply_scalar_cyclo(tmp,b_tmp);
    if (flag)
    {    
        copy(b_tmp,b);
        freeall(b_tmp);
    }
    freeall(tmp);
    space_saving    = saving;
# endif
    return(OK);
}

INT add_apply_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT    erg = OK;
    OP    c;
    CTO(CYCLOTOMIC,"add_apply_cyclo(1)",a);
    c = CALLOCOBJECT();
    SWAP(c,b);
    erg += add_cyclo(a,c,b);
    FREEALL(c);
    ENDR("add_apply_cyclo");
}

INT mult_apply_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */
{    
    INT    ret;
#ifdef    CYCLOTRUE
    OP    c;
    c = CALLOCOBJECT();
    ret    = mult_cyclo(a,b,c);
    copy(c,b);
    freeall(c);
#endif
    return(ret);
}

INT addinvers_apply_cyclo(a) OP a;
/* AK 200891 V1.3 */
{
    OP b;
    INT erg = OK;
    CTO(CYCLOTOMIC,"addinvers_apply_cyclo(1)",a);
    b = CALLOCOBJECT();
    SWAP(b,a);
    erg += addinvers_cyclo(b,a);
    FREEALL(b);
    ENDR("addinvers_apply_cyclo");
}

INT nullp_cyclo(a) OP a;
/* AK 200891 V1.3 */
{
#ifdef    CYCLOTRUE
    if (S_O_K(a) != CYCLOTOMIC)
        return(ERROR);
    if (EMPTYP(S_N_S(a)))
    {    
        error("nullp_cyclo: cyclo with empty self\n");
        return(TRUE);
    }
    return(nullp_monopoly(S_N_S(a)));
#else
    return(ERROR);
#endif
}
#ifdef CYCLOTRUE
INT comp_cyclo(a,b) OP a,b;
/* AK 200891 V1.3 */
{
    return(comp_list(S_N_S(a),S_N_S(b)));
}
#endif /* CYCLOTRUE */


# ifdef    CYCLOTRUE
INT convert_cyclo_scalar(a) OP a;
/* 5.04.91: TPMcD. */
/* AK 200891 V1.3 */
{    
    INT    ret = ERROR;
    OP tmp;

    if (S_O_K(a) != CYCLOTOMIC || S_L_N(S_N_S(a)) != NULL)
        goto exit_label;
    tmp    = S_PO_S(S_N_S(a));
    if (not nullp(tmp))
        goto exit_label;
    tmp    = CALLOCOBJECT();
    copy(S_PO_K(S_N_S(a)),tmp);
    copy(tmp,a);
    freeall(tmp);
    ret    = OK;
exit_label:
    return(ret);
}
#endif /* CYCLOTRUE */

#ifdef    CYCLOTRUE
static INT fprint_cyclo(f,a) FILE *f; 
    OP a;
/* 25.09.91: TPMcD. */
{    
    INT myfirst = 1L, flag;
    OP    ptr;

    standardise_cyclo_0(a,basis_type);
    ptr = S_N_S(a);
    zeilenposition    += 2L;
    if (nullp_cyclo(a))
    {    
        fprintf(f," 0");
        return(OK);
    }
    while (ptr != NULL)
    {    
        flag    = 0L;
        if (zeilenposition > 60L)
        {       
            zeilenposition  = 0L;
            fprintf(f,"\n");
        }
        if (!negp(S_PO_K(ptr)) && !myfirst)
            fprintf(f," +");
        if (negeinsp(S_PO_K(ptr)))
        {    
            flag    = 1L;
            fprintf(f," -");
        }
        else if (!einsp(S_PO_K(ptr)))
        {
            fprintf(f," ");
            fprint(f,S_PO_K(ptr));
        }
        else
        {
            fprintf(f," ");
            flag    = 1L;
        }

        if (not nullp(S_PO_S(ptr)))
        {    
            fprintf(f," E(");
            fprint(f,S_N_DCI(a));
            fprintf(f,")");
            if (!einsp(S_PO_S(ptr)))
            {
                fprintf(f,"^");
                fprint(f,S_PO_S(ptr));
            }
            zeilenposition    += 5L;
        }
        else if (flag)
            fprintf(f," 1");
        ptr    = S_L_N(ptr);
        myfirst = 0L;
    }
    return(OK);
}
#endif /* CYCLOTRUE */

#ifdef    CYCLOTRUE
INT tex_cyclo(a) OP a;
/* 4.04.91: TPMcD. */ /* AK 200891 V1.3 */ /* 23.10.91: TPMcD */
{
    INT myfirst = 1L;
    OP    ptr = S_N_S(a);

    if (nullp_cyclo(a))
    {    
        fprintf(texout," 0\n");
        return(OK);
    }
    fprintf(texout,"\n");
    while (ptr != NULL)
    {    
        if (!negp(S_PO_K(ptr)) && !myfirst)
            fprintf(texout," + {");
        else
            fprintf(texout,"{");
        tex(S_PO_K(ptr));

        if (not nullp(S_PO_S(ptr)))
        {    
            fprintf(texout,"} \\omega_{");
            tex(S_N_DCI(a));
            fprintf(texout,"} {");
            tex(S_PO_S(ptr));
        }
        fprintf(texout,"}\n");
        ptr    = S_L_N(ptr);
        myfirst = 0L;
    }
    fprintf(texout,"\n");
    return(OK);
}
#endif /* CYCLOTRUE */

/*    ROUTINES RELATING TO THE MAINTENANCE OF CYCLOTOMIC DATA    */

# ifdef    CYCLOTRUE

/*Reads the table of cyclos from the file CYCLOS.DAT. The first entry    */
/*should be no_cyclos, then the list of cyclo_data.  Returns OK if the    */
/*table is set; otherwise, returns ERROR.        */

static INT setup_cyclotomic_table(filename) char *filename;
/* 30.08.90: TPMcD */ /* AK 200891 V1.3 */
{    
    INT    i=0; 
    FILE    *f;
    CYCLO_DATA    *ptr;
    char    name[50], *char_ptr;

    if (cyclo_table_set || filename == NULL)
        return(OK);
    if ((f = fopen(filename,"r")) == NULL)
    {    
        printf("\nFile containing cyclo data: ");
        char_ptr    = name;
        while( (*char_ptr = fgetc(stdin)) != '\n')
        {    
            if (myisspace(*char_ptr)) continue;
            char_ptr++; 
            i++;
            if (i > (INT)48) break;
        }
        *char_ptr    = /* NULL; AK 290494 */ '\0';
        if (strlen(name) == 0)
            return(ERROR);
        if ((f = fopen(name,"r")) == NULL)
        {    
            printf("Unable to open %s\n",name);
            return(ERROR);
        }
    }
    if ( fscanf(f," %ld",&zzno_cyclos) == 0 || zzno_cyclos < 1L ||
        (zzcyclo_table
        = (CYCLO_DATA *) SYM_calloc((int)zzno_cyclos,sizeof(CYCLO_DATA))
        ) == NULL
        )
    {    
        zzno_cyclos    = 0L;
        printf("\nCyclo data table creation error");
        return(ERROR);
    }
    ptr    = zzcyclo_table - 1;
    for (i=0L;i<zzno_cyclos;i++)
    {    
        ptr++;
        ptr->index    = CALLOCOBJECT();
        objectread(f,ptr->index);
        ptr->deg    = CALLOCOBJECT();
        objectread(f,ptr->deg);
        ptr->poly    = CALLOCOBJECT();
        objectread(f,ptr->poly);
        ptr->autos    = CALLOCOBJECT();
        objectread(f,ptr->autos);
    }
    cyclo_table_set    = 1L;
    fclose(f);
    return(OK);
}

static CYCLO_DATA *add_cyclo_data(index) OP index;
/* AK 200891 V1.3 */
{    
    CYCLO_DATA    *ptr = NULL;
    OP    ptr_eins, ptr_zwei=NULL;
    
    if ((ptr = cyclo_ptr(index)) != NULL)
        return(ptr);
    ptr    = (CYCLO_DATA *) SYM_calloc(1,sizeof(CYCLO_DATA));
    if (ptr == NULL)
        return(NULL);
    ptr->index    = CALLOCOBJECT();
    COPY(index,ptr->index);
    ptr->poly    = CALLOCOBJECT();
    if (make_cyclotomic_monopoly(index,ptr->poly) == ERROR)
    {    
        SYM_free(ptr);
        return(NULL);
    }
    ptr_eins    = ptr->poly;
    while(ptr_eins != NULL)
    {    
        ptr_zwei    = ptr_eins;
        ptr_eins    = S_L_N(ptr_eins);
    }
    ptr->deg    = CALLOCOBJECT();
    COPY(S_PO_S(ptr_zwei),ptr->deg);
    ptr->autos    = CALLOCOBJECT();
    make_coprimes(ptr->index,ptr->autos);
    ptr_eins    = CALLOCOBJECT();
    init(LIST,ptr_eins);
    /*    Some compilers require this cast, others dislike it    */
    /* (CYCLO_DATA *) S_L_S(ptr_eins)    = ptr; */
    C_L_S(ptr_eins,ptr);
    /* S_L_N(ptr_eins)    = NULL; */
    C_L_N(ptr_eins,NULL);
    if (cyclo_list_set)
        S_L_N(zzcyclo_tail)    =    ptr_eins;
    else
    {    
        cyclo_list_set    = 1L;
        zzcyclo_list    = ptr_eins;
    }
    zzcyclo_tail    = ptr_eins;
    return(ptr);
}

static CYCLO_DATA *cyclo_ptr(index) OP index;
/* AK 200891 V1.3 */
{    
    CYCLO_DATA    *ptr = NULL;
    OP    list_ptr;
    INT    i;
    if (cyclo_table_set)
    {    
        ptr    = zzcyclo_table - 1;
        for (i=0L;i<zzno_cyclos;i++)
        {    
            ptr++;
            if (EQ(index,ptr->index) == TRUE)
                return(ptr);
        }
    }
    if (cyclo_list_set)
    {    
        list_ptr    = zzcyclo_list;
        while (list_ptr != NULL)
        {    
            ptr    = (CYCLO_DATA *) S_L_S(list_ptr);
            if (ptr == NULL)
                error("cyclo_ptr: null pointer\n");
            if (EQ(index,ptr->index) == TRUE)
                return(ptr);
            list_ptr    = S_L_N(list_ptr);
        }
    }
    return(NULL);
}

static INT free_cyclo_list()
/* 29.10.91: TPMcD */
{    
    OP    list_ptr;
    OBJECTSELF list_self;
    CYCLO_DATA *cp;
    list_ptr = zzcyclo_list;
    while (list_ptr != NULL)
    {    
        list_self    = S_O_S(list_ptr);
        cp = (CYCLO_DATA *)S_L_S(list_ptr);
        freeall(cp->index);
        freeall(cp->deg);
        freeall(cp->poly);
        freeall(cp->autos);
        SYM_free(cp);
        C_L_S(list_ptr,NULL); /* Wg speicherverwaltung */
        list_ptr    = S_L_N(list_ptr);
    }
    return(OK);
}

INT print_cyclo_data(ptr) CYCLO_DATA *ptr;
/* AK 200891 V1.3 */
{    
    printf("Index ");
    print(ptr->index);
    printf("\tDegree ");
    println(ptr->deg);
    printf("Polynomial ");
    println(ptr->poly);
    printf("Automorphism exponents ");
    println(ptr->autos);
    return OK;
}

static INT free_cyclo_table()
/* AK 310893 */
{
    CYCLO_DATA    *ptr;
    INT    i;

    if (!cyclo_table_set)
        return(ERROR);
    ptr    = zzcyclo_table;
    for (i=0L;i<zzno_cyclos;i++)
    {    
        freeall(ptr->index);
        freeall(ptr->deg);
        freeall(ptr->poly);
        freeall(ptr->autos);
        ptr++;
    }
    return(OK);
}

INT print_cyclo_table()
/* AK 200891 V1.3 */
{    
    CYCLO_DATA    *ptr;
    INT    i;

    if (!cyclo_table_set)
        return(ERROR);
    printf("Number of cyclo data on table: %ld\n",zzno_cyclos);
    ptr    = zzcyclo_table;
    for (i=0L;i<zzno_cyclos;i++)
    {    
        printf("Table item %ld: ",i);
        print_cyclo_data(ptr);
        ptr++;
    }
    return(OK);
}

INT print_cyclo_list()
/* AK 200891 V1.3 */
{    
    OP    list_ptr;
    INT    i = 0L;

    if (!cyclo_list_set)
        return(ERROR);
    printf("Cyclo data in list:\n");
    list_ptr    = zzcyclo_list;
    while (list_ptr != NULL)
    {    
        printf("List item %ld: ",i++);
        print_cyclo_data((CYCLO_DATA *) S_L_S(list_ptr));
        list_ptr    = S_L_N(list_ptr);
    }
    return(OK);
}

INT save_cyclo_list(filename) char *filename;
/* 4.04.91: TPMcD. */ /* AK 200891 V1.3 */
{
    CYCLO_DATA    *ptr;
    OP    list_ptr;
    INT    i = 0L, new = 0L;
    FILE    *f;
    char    name[50], *char_ptr;

    if (filename == NULL || (f = fopen(filename,"r+")) == NULL)
    {    
        fflush(stdin);
        printf("\nFile to receive cyclo data: ");
        char_ptr    = name;
        while( (*char_ptr = fgetc(stdin)) != '\n')
        {    
            if (myisspace(*char_ptr)) continue;
            char_ptr++; 
            i++;
            if (i > (INT)48) break;
        }
        *char_ptr    = /* NULL; AK 290494 */ '\0';
        if (strlen(name) == 0)
            return(ERROR);
        if ((f = fopen(name,"r+")) == NULL)
        {    
            if((f = fopen(name,"w")) == NULL)
            {    
                printf("Unable to open %s\n",name);
                return(ERROR);
            }
            else
                new    = 1L;
        }
    }
    else
        strcpy(name,filename);
    if (new)
    {    
        fprintf(f,"              \n\n");
        printf("Initialising %s\n",name);
        i    = 0L;
    }
    else
    {    
        fseek(f,0L,0);
        fscanf(f,"%ld",&i);
        fseek(f,0L,2);
        printf("Cyclo data being appended to file %s.\n",name);
    }
    list_ptr    = zzcyclo_list;
    while (list_ptr != NULL)
    {    
        ptr    = (CYCLO_DATA *) S_L_S(list_ptr);
        fprintf(f,"\n");
        objectwrite(f,ptr->index);
        objectwrite(f,ptr->deg);
        objectwrite(f,ptr->poly);
        objectwrite(f,ptr->autos);
        list_ptr    = S_L_N(list_ptr);
        i++;
    }
    fseek(f,0L,0);
    fprintf(f,"%8ld",i);
    fclose(f);
    return(OK);
}

#endif

#ifdef NUMBERTRUE
INT test_number()
{
    OP a = CALLOCOBJECT();
    OP b = CALLOCOBJECT();
    printeingabe("test_number: squareroot(2L,a)");
    squareroot(cons_zwei,a); 
    println(a);
    printeingabe("test_number: squareroot(11L,a)^-1");
    m_i_i(19L,b); 
    squareroot(b,a); 
    invers(a,b); 
    println(b);
    printeingabe("test_number: euler_phi(311L,a)");
    m_i_i(311L,b); 
    euler_phi(b,a); 
    println(b);
    freeall(a);
    freeall(b);
    return OK;
}
#endif /* NUMBERTRUE */

INT t_MONOPOLY_POLYNOM(a,b) OP a,b;
/* AK 171194 */
/* AK 170206 V3.0 */
{
    INT erg = OK;
    CTO(MONOPOLY,"t_MONOPOLY_POLYNOM(1)",a);
    CE2(a,b,t_MONOPOLY_POLYNOM);

    {
    OP c;
    init(POLYNOM,b);
    if (S_L_S(a) != NULL) {
	    while (a != NULL)
		{
		c = CALLOCOBJECT();
		m_iindex_iexponent_monom(0,S_I_I(S_PO_S(a)),c);
		copy(S_PO_K(a),S_PO_K(c));
		insert(c,b,NULL,NULL);
		a = S_L_N(a);
		}
	}
    }

    ENDR("t_MONOPOLY_POLYNOM");
}
        

INT invers_monopoly(lau, res) OP lau,res;
{
        INT erg = OK;
        CTO(MONOPOLY,"invers_monopoly(1)",lau);
        CTO(EMPTY,"invers_monopoly(2)",res);

        erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),res);
        M_I_I((INT)1,S_B_O(res));
        erg += copy(lau,S_B_U(res));
        C_B_I(res,GEKUERZT);

        ENDR("invers_monopoly");
}


INT degree_monopoly(mp,dg) OP mp,dg;
/*CC 010496*/
/* -1 if null */
{
/* Puts in dg the degree of the MONOPOLY object mp*/
    OP z,za=NULL;
    INT erg = OK;
    CTO(MONOPOLY,"degree_monopoly(1)",mp);
    FREESELF(dg);
    
    if(NULLP(mp)) 
        M_I_I(-1L,dg);
    else {
        z=mp;
        while(z !=NULL) { za=z; z=S_L_N(z); }
        COPY(S_PO_S(za),dg);
        }
    ENDR("degree_monopoly");
}

/*
Puts in ld the leading coefficient of the MONOPOLY object mp.
*/

INT ldcf_monopoly(mp,ld) OP mp,ld;
{
	INT erg=OK;
        OP z,za=NULL;
	FREESELF(ld);
	if (NULLP(mp)) error("ldcf_monopoly: null monopoly");
	else {
		z=mp;
		while(z !=NULL) { za=z; z=S_L_N(z); }
		COPY(S_PO_K(za),ld);
		}
        ENDR("ldcf_monopoly");
}



INT has_one_variable(a) OP a;
/* AK 310106 */
{
/*
Returns TRUE, if a is an  MONOPOLY object, or
                is of type POLYNOM with 0 or 1 variable.
*/
        OP nb;
	INT erg =OK;
        if(S_O_K(a)==MONOPOLY)
                return TRUE;
        if(S_O_K(a)==POLYNOM)
        {
                nb=CALLOCOBJECT();
                numberofvariables(a,nb);
                if(S_I_I(nb)<=1L)
                {
                        FREEALL(nb);return TRUE;
                }
                FREEALL(nb);
        }
        return FALSE;
	ENDR("has_one_variable");
}

