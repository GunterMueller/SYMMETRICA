#include "def.h" 
#include "macro.h"

/* SYMMETRICA vector.c */
/* AK 160986 */

struct vector * callocvectorstruct();
static INT charvalue_bit_co();
static INT mem_counter_vec=0;
static int vector_speicherindex=-1; /* AK 231001 */
static int vector_speichersize=0; /* AK 231001 */
static struct vector **vector_speicher=NULL; /* AK 231001 */

INT freevectorstruct();

#define B_LS_V(l,s,r) \
do { FREESELF(r);\
     C_O_K(r,VECTOR); \
     r->ob_self.ob_vector = callocvectorstruct();\
     C_V_S(r,s);\
     C_V_L(r,l); } while(0)


#ifdef VECTORTRUE
INT vec_anfang()
/* AK 100893 */
    {
    INT erg = OK;
#ifdef UNDEF
    mem_counter_vec=0;
    return OK;
#endif
    

    ANFANG_MEMMANAGER(vector_speicher,
                    vector_speicherindex,
                    vector_speichersize,
                    mem_counter_vec);
    ENDR("vec_anfang");

    }

INT vec_ende()
/* AK 100893 */
    {
    INT erg = OK;
    if (no_banner != TRUE)
    if (mem_counter_vec != (INT)0)
        {
        fprintf(stderr,"mem_counter_vec = %ld\n",mem_counter_vec);
        erg += error("vec memory not freed");
        }
#ifdef UNDEF
    erg += vec_speicher_ende();
    return erg;
#endif
    ENDE_MEMMANAGER(vector_speicher,
                    vector_speicherindex,
                    vector_speichersize,
                    mem_counter_vec,"vec speicher not freed");

    ENDR("vec_ende");
    }


INT einsp_vector(a) OP a;
/* AK 010692 */
/* AK 040398 V2.0 */
{
    INT i;
    for (i=(INT)0;i<S_V_LI(a);i++)
        if (not einsp(S_V_I(a,i))) return FALSE;
    return TRUE;
}

INT einsp_integervector(a) OP a;
/* AK 040398 V2.0 */
{
    INT i;
    for (i=(INT)0;i<S_V_LI(a);i++)
        if (S_V_II(a,i) != (INT)1) return FALSE;
    return TRUE;
}

INT decreasingp_vector(a) OP a;
/* AK 151196 */
{
    INT i;
    if (S_V_LI(a) <= 1) return TRUE;

        for (i=S_V_LI(a)-2;i>=0;i--)
        if (LT(S_V_I(a,i),S_V_I(a,i+1)))  return FALSE;
    return TRUE;
}

#endif /* VECTORTRUE */

INT vectorp(a) OP a;
/* AK 210192 */ 
/* AK 011098 V2.0 */
/* AK 110902 V2.1 */
{
#ifdef VECTORTRUE
    if (
        (s_o_k(a) == VECTOR)
        ||
        (s_o_k(a) == WORD)
        ||
        (s_o_k(a) == KRANZ)
        ||
        (s_o_k(a) == LAURENT)
        ||
        (s_o_k(a) == COMPOSITION)
        ||
        (s_o_k(a) == INTEGERVECTOR)
        ||
        (s_o_k(a) == SUBSET)
        ||
        (s_o_k(a) == HASHTABLE)
        ||
        (s_o_k(a) == FF)
       ) return TRUE;
#endif /* VECTORTRUE */
    return FALSE;
}

#ifdef VECTORTRUE
INT m_o_v(ob,vec) OP ob,vec;
/* make_object_vector */
/* AK 260488 */
/* AK 270689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* input: arbitrary object 
   output: VECTOR object with one component = copy of first
           parameter */
/* ob and vec may be equal */
{ 
    INT erg = OK;
    CE2(ob,vec,m_o_v);
    erg += m_il_v((INT)1,vec); 
    COPY(ob,S_V_I(vec,(INT)0));
    ENDR("m_o_v");
}

INT b_o_v(ob,vec) OP ob,vec;
/* build_object_vector */ 
/* AK 170590 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    INT erg = OK;
    OP l;
    SYMCHECK( ob == vec, "b_o_v: the two parameters are equal");
    NEW_INTEGER(l,1);
    B_LS_V(l,ob,vec); 
    ENDR("b_o_v");
}

INT m_l_nv(il,vec)  OP il,vec;
/* AK 160791 V1.3 */
/* AK 011098 V2.0 */
/* il and vec may be equal */
{
    INT erg = OK;
    CTO(INTEGER,"m_l_nv",il);
    SYMCHECK(S_I_I(il) < 0,"m_l_nv:length < 0");
    erg += m_il_nv(S_I_I(il),vec);
    ENDR("m_l_nv");
}

INT m_il_nv(il,vec) INT il; OP vec;
/* AK 160791 V1.3 */
/* AK 011098 V2.0 */
{
    INT i;
    INT erg = OK;
    SYMCHECK(il < 0,"m_il_nv:length < 0");
    erg += m_il_v(il,vec);
    for (i=(INT)0;i<S_V_LI(vec);i++)
        M_I_I((INT)0,S_V_I(vec,i));
    ENDR("m_il_nv");
}

/* object BITVECTOR */
/* S_V_LI = length in bit
   S_BV_LI = length in byte */

INT s_bv_li(a) OP a;
/* AK 050399 */
{
    INT erg = OK,l;
    CTO(BITVECTOR,"s_bv_li",a);
    C_O_K(a,VECTOR);
    l = s_v_li(a);
    C_O_K(a,BITVECTOR);
    return (l % 8 == 0 ? (l>>3) : (l>>3) +1);
    ENDR("s_bv_li");
}


INT m_il_bv(il,bitvec) INT il; OP bitvec;
/* AK 161294 */
/* AK 190298 V2.0 */
/* il is length in bit */
{
    INT erg = OK;
    SYMCHECK(il < 0,"m_il_bv: negativ length");

    B_LS_V(callocobject(),NULL,bitvec);
    M_I_I(il,S_V_L(bitvec));
    if (il > 0)
        C_V_S(bitvec,SYM_calloc(S_BV_LI(bitvec)/8+1,8));
    C_O_K(bitvec,BITVECTOR);
    ENDR("m_il_bv");
}

INT m_il_nbv(il,bitvec) INT il; OP bitvec;
/* AK 161294 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    COP("m_il_nbv(2)",bitvec);
    SYMCHECK(il < 0,"m_il_nbv: negativ length");
    B_LS_V(callocobject(),NULL,bitvec);
    M_I_I(il,S_V_L(bitvec));
    if (il > (INT)0)
        C_V_S(bitvec,SYM_calloc(S_BV_LI(bitvec)/8+1,8));
    C_O_K(bitvec,BITVECTOR);
    ENDR("m_il_nbv");
}


INT m_il_v(il,vec) INT il; OP vec;
/* make_integerlength_vector */
/* AK 250587 */ /* AK 270689 V1.0 */ /* AK 211289 V1.1 */
/* AK 080291 V1.2 test on negativ
                  test on zero length */
/* AK 200891 V1.3 */
/* AK 020398 V2.0 */
{
    INT erg = OK,i;
    OP l;
    COP("m_il_v(2)",vec);
    SYMCHECK(il < 0,"m_il_v: negativ length");

    if (S_O_K(vec) == VECTOR) /* AK 261006 */
	{
	if (S_V_LI(vec)==il) 
		{
		for (i=0,l=S_V_S(vec);i<il;i++,l++) FREESELF(l);
		goto endr_ende;
		}
        }

    NEW_INTEGER(l,il);
   
    if (il == (INT)0) 
        B_LS_V(l,NULL,vec);
    else if (il == (INT)1) 
        B_LS_V(l,CALLOCOBJECT(),vec);
    else
        B_LS_V(l, (OP) SYM_MALLOC(il * sizeof(struct object)),vec);

    for (i=0,l=S_V_S(vec);i<il;i++,l++) 
        C_O_K(l,EMPTY);
    ENDR("m_il_v");
}

INT m_il_integervector(il,vec) INT il; OP vec;
/* AK 121101 */
{
    INT erg = OK,i;
    OP l;
    COP("m_il_integervector(2)",vec);
    SYMCHECK(il < 0,"m_il_integervector: negativ length");
    NEW_INTEGER(l,il);
    if (il == (INT)0)
        B_LS_V(l,NULL,vec);
    else if (il == (INT)1)
        B_LS_V(l,CALLOCOBJECT(),vec);
    else
        B_LS_V(l, (OP) SYM_MALLOC((int)il * sizeof(struct object)),vec);
    
    for (i=0,l=S_V_S(vec);i<il;i++,l++) 
        C_O_K(l,EMPTY);
    C_O_K(vec,INTEGERVECTOR);
    ENDR("m_il_v");
}

INT mem_size_vector(a) OP a;
/* AK 150295 */
/* AK 011098 V2.0 */
{
    INT erg = 0,i; OP z;
    if (a == NULL) return 0;
    if (not VECTORP(a)) WTO("mem_size_vector",a);
    erg += sizeof(struct object);
    erg += sizeof(struct vector);
    erg += mem_size(S_V_L(a));
    for (i=0,z = S_V_S(a);i<S_V_LI(a);i++,z++)
        erg += mem_size(z);
    return erg;
}


INT b_l_v(length,a) OP length, a;
/* build_length_vector
    build length becomes part of the result */
/* AK 170590 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{

    INT erg = OK,i;
    OP self ; /* self komponente des vectors */

    CTO(INTEGER,"b_l_v",length);
    if (length == a)
        {
        erg += error("b_l_v:two identic parameter");
        goto endr_ende;
        }
    

    if (NULLP_INTEGER(length)) 
        {
        B_LS_V(length,NULL,a); /* AK 021291 */
        goto endr_ende;
        }

    if (S_I_I(length) == (INT)1)
        self = CALLOCOBJECT();
    else
        self = (OP) SYM_MALLOC((int)S_I_I(length) * 
                sizeof(struct object));
    if (self == NULL) 
        {
        erg += error("b_l_v:no memory");
        goto endr_ende;
        }

    B_LS_V( length , self, a);

    for (i=(INT)0;i<S_V_LI(a);i++) /* AK 271191 DOS */
        C_O_K(S_V_I(a,i),EMPTY);
    ENDR("b_l_v");
}

INT b_l_nv(a,b) OP a,b;
/* AK 170692 */
/* AK 011098 V2.0 */
/* AK 271006 V3.1 */
    {
    INT i,erg = OK;;
    CTO(INTEGER,"b_l_nv",a);
    erg += b_l_v(a,b);
    for (i=0;i<S_V_LI(b);i++)
        M_I_I(0,S_V_I(b,i));
    ENDR("b_l_nv");
    }

INT m_l_v(length,a) OP length,a;
/* make_length_vector
    make means: working with a copy of length in the result */
/* AK 170590 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* length and a may be equal */
{
    OP l ;
    INT erg = OK;
    CTO(INTEGER,"m_l_v",length);
    l = CALLOCOBJECT();
    COPY_INTEGER(length,l);
    erg += b_l_v(l,a);
    ENDR("m_l_v");
}

INT add_apply_vector(a,b) OP a, b;
/* b = b+a */
/* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,erg = OK,t=0;
    OP c;
    CTTO(VECTOR,INTEGERVECTOR,"add_apply_vector(1)",a);
    CTTO(VECTOR,INTEGERVECTOR,"add_apply_vector(2)",b);

    if (S_V_LI(a) > S_V_LI(b))
    {
        c = CALLOCOBJECT();
        COPY(a,c);
        for (i=(INT)0;i<S_V_LI(a);i++)
            if     (i < S_V_LI(b))
                {
                ADD_APPLY(S_V_I(b,i),S_V_I(c,i));
                if (S_O_K(S_V_I(c,i)) != INTEGER) t=1;
                }
            else break;
        FREESELF(b);
        *b = *c;
        C_O_K(c,EMPTY);
        FREEALL(c);
    }
    else {
        for (i=0;i<S_V_LI(b);i++)
            if     (i < S_V_LI(a))
                {
                ADD_APPLY(S_V_I(a,i),S_V_I(b,i));
                if (S_O_K(S_V_I(b,i)) != INTEGER) t=1;
                }
            else break;
    };
    if (t) C_O_K(b,VECTOR);
    ENDR("add_apply_vector");
}


INT add_vector(a,b,c) OP a, b, c;
/* AK 221086 */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 260298 V2.0 */
{
    INT i;
    INT erg = OK;
    CTO(EMPTY,"add_vector(3)",c);
    if (not VECTORP(b))
        {
        erg += WTO("add_vector(2)",b);
        goto endr_ende;
        }
    if (not VECTORP(a))
        {
        erg += WTO("add_vector(1)",a);
        goto endr_ende;
        }
    CTO(EMPTY,"add_vector(3)",c);

    if (S_V_LI(a) > S_V_LI(b))
    {
        erg += copy_vector(a,c);
        for (i=(INT)0;i<S_V_LI(a);i++)
            if     (i < S_V_LI(b))
                {
                ADD_APPLY(S_V_I(b,i),S_V_I(c,i));
                }
            else break;
    }
    else {
        erg += copy_vector(b,c);
        for (i=(INT)0;i<S_V_LI(b);i++)
            if     (i < S_V_LI(a))
                {
                ADD_APPLY(S_V_I(a,i),S_V_I(c,i));
                }
            else break;
    };
    ENDR("add_vector");
}

INT add_integervector(a,b,c) OP a, b, c;
/* AK 260298 V2.0 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGERVECTOR,"add_integervector(1)",a);
    CTO(EMPTY,"add_integervector(3)",c);
    {
    INT i,t=0;
    if (S_O_K(b)!=INTEGERVECTOR) {
        erg += add_vector(a,b,c);
        goto endr_ende;
        }
    CTO(INTEGERVECTOR,"add_integervector(2)",b);
    if (S_V_LI(a) > S_V_LI(b))
    {
        erg += copy_integervector(a,c);
        for (i=0;i<S_V_LI(a);i++)
            if     (i < S_V_LI(b))
                {
                erg += add_apply_integer_integer(S_V_I(b,i),S_V_I(c,i));
                if (S_O_K(S_V_I(c,i)) != INTEGER)t=1;
                }
            else break;
    }
    else {
        erg += copy_integervector(b,c);
        for (i=0;i<S_V_LI(b);i++)
            if     (i < S_V_LI(a))
                {
                erg += add_apply_integer_integer(S_V_I(a,i),S_V_I(c,i));
                if (S_O_K(S_V_I(c,i)) != INTEGER)t=1;
                }
            else break;
    };
    if (t==1) C_O_K(c,VECTOR);
    }
    ENDR("add_integervector");
}

INT qsort_vector(vec) OP vec;
/* sorts a vector object vec 
 at the end the vector is increasing according to the routine comp
 AK 060488 */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"qsort_vector(1)",vec);
        {
        qsort(
              S_V_S(vec),(int)S_V_LI(vec),
              sizeof(struct object),comp
             );
        return(OK);
        }
    CTTO(INTEGERVECTOR,VECTOR,"qsort_vector(1e)",vec);
    ENDR("qsort_vector");
}

INT usersort_vector(vec,f) OP vec;INT (*f)();
/* sorting with a user defined comparion */
/* AK 011098 V2.0 */ /* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"usersort_vector(1)",vec);
        {
        qsort(S_V_S(vec),(int)S_V_LI(vec),sizeof(struct object),f);
        return(OK);
        }
    CTTO(INTEGERVECTOR,VECTOR,"usersort_vector(1e)",vec);
    ENDR("usersort_vector");
}

INT sort_vector(vec) OP vec;
/* insertion-sort (knuth) AK 270787 */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"sort_vector(1)",vec);
        {
        INT i,j,k;
        OBJECTSELF zeiger;
        OBJECTKIND art;

        for (i=0;i<S_V_LI(vec);i++)
            for (j=0;j<i;j++)
                if (LT(S_V_I(vec,i),S_V_I(vec,j)))
                {
                    zeiger =  S_O_S(S_V_I(vec,i));
                    art =  S_O_K(S_V_I(vec,i));
                    for (k=i;k>j;k--)
                        *S_V_I(vec,k) = *S_V_I(vec,k-1);
                    C_O_S(S_V_I(vec,j),zeiger);
                    C_O_K(S_V_I(vec,j),art);
                };
        return(OK);
        }
    CTTO(INTEGERVECTOR,VECTOR,"sort_vector(1e)",vec);
    ENDR("sort_vector");
}



INT random_bv(a,b) OP a,b;
/* AK 250194 */
/* AK 011098 V2.0 */
{
    INT erg = OK,i;
    int rand();
    CTO(INTEGER,"random_bv",a);
    erg += m_il_bv(S_I_I(a),b);
    C_O_K(b,BITVECTOR);
    for (i=(INT)0;i<S_V_LI(b);i++)
        {
        if (rand()%2)
            SET_BV_I(b,i);
        }
    ENDR("random_bv");
}
    
INT sscan_bitvector(t,a) OP a; char *t;
/* AK 011098 V2.0 */
{
    INT erg = OK;
    OP c;
    COP("sscan_bitvector(1)",t);
    COP("sscan_bitvector(2)",a);
    c = callocobject();
    erg += sscan_integervector(t,c);
    erg += t_INTVECTOR_BITVECTOR(c,a);
    FREEALL(c);    
    ENDR("sscan_bitvector");
}
    
INT sscan_integervector(t,a) OP a; char *t;
/* AK 050194 to read integervector from string
        format [1,2,3,..]
*/
/* AK 011098 V2.0 */
{
    INT i,n,erg = OK;
    char *v,*w;
    int SYM_isdigit();

    COP("sscan_integervector(1)",t);
    COP("sscan_integervector(2)",a);

    v = t;
    while (*v == ' ') v++;
    if (*v != '[')
        {erg = ERROR; goto spe;}
    w = v; n = (INT)1;
    /* now we count the number of parts */
    w++;
    while (*w != ']')
        {
        if (*w == ' ') ; /* AK 060397 */
        else if (*w == ',') n++;
        else if (*w == '-'); /* AK 280197 */
        else if (not SYM_isdigit(*w))
            {erg = ERROR; goto spe;}
        w++;
        }
    /* n is the number of parts */
    m_il_v(n,a);
    C_O_K(a,INTEGERVECTOR);
    w = v;
    w++;
    for (i=(INT)0; i<n; i++)
        {
        erg += sscan(w,INTEGER,S_V_I(a,i));
        if (erg != OK) goto spe;
        if (*w == '-') w++; /* AK 151097 */
        while (SYM_isdigit(*w)) w++;
        w++;
        }
spe:
    ENDR("sscan_integervector");
}

INT sscan_permvector(t,a) OP a; char *t;
/* AK 180998 to read permutationvector from string
        format [[..],[...],[...],..]
*/
/* AK 011098 V2.0 */
{
    INT i,n,erg = OK;
    char *v,*w;
    COP("sscan_permvector(1)",t);
    COP("sscan_permvector(2)",a);

    v = t;
    while (*v == ' ') v++;
    if (*v != '[')
        {erg = ERROR; goto spe;}
    w = v; n = (INT)1;
    /* now we count the number of parts */
    w++;
    while (*w != ']')
        {
        if (*w == ' ') ;
        else if (*w == '[')
            {
            w++;
            while (*w != ']')
                {
                if (w == '\0')  {erg = ERROR; goto spe;}
                else w++;
                }
            }
        else if (*w == ',') n++;
        else 
            {erg = ERROR; goto spe;}
        w++;
        }
    /* n is the number of parts */
    m_il_v(n,a);
    C_O_K(a,VECTOR);
    w = v;
    while (*w != '[') w++;
    w++;
    for (i=(INT)0; i<n; i++)
       {
       while (*w != '[') w++;
       erg += sscan(w,PERMUTATION,S_V_I(a,i));
       if (erg != OK) goto spe;
       while (*w != ']') w++;
       w++;
       }
spe:
    ENDR("sscan_permvector");
}

INT random_integervector(a,b) OP a,b;
/* AK 250194 */
/* AK 011098 V2.0 */
{
    INT erg = OK,i;
    CTO(INTEGER,"random_integervector",a);

    erg += m_l_v(a,b);
    C_O_K(b,INTEGERVECTOR);
    for (i=(INT)0;i<S_V_LI(b);i++)
        erg += random_integer(S_V_I(b,i),NULL,NULL);
    ENDR("random_integervector");
}

INT freeself_galois(a) OP a;
{
	INT erg =OK;
	{
	SYM_free(S_V_S(a));
	FREEALL(S_V_L(a));
        freevectorstruct(S_O_S(a).ob_vector);
        C_O_K(a,EMPTY);
	}
	ENDR("freeself_galois");
}

INT freeself_integervector(a) OP a;
/* AK 110394 */ /* AK 020698 V2.0 */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTTO(COMPOSITION,SUBSET,INTEGERVECTOR,"freeself_integervector(1)",a);
        {
   
        if (S_V_LI(a) == 1) 
            FREEALL(S_V_S(a)); 
        else if (S_V_LI(a) > 0) 
            SYM_free(S_V_S(a));

        FREEALL(S_V_L(a)); 
        freevectorstruct(S_O_S(a).ob_vector);
        C_O_K(a,EMPTY);
        }
    CTO(EMPTY,"freeself_integervector(1e)",a);
    ENDR("freeself_integervector");
}



INT freeself_hashtable(vec) OP vec;
/* AK 231001 AK 100307*/
/* length > 1 */
{
    INT  i,erg=OK,j;
    OP z,zj;
 
    CTO(HASHTABLE,"freeself_hashtable(1)",vec);
 
    if (S_V_II(vec,S_V_LI(vec)) > 0)
        {
        for (i=(INT)0,z=S_V_S(vec);i<S_V_LI(vec);i++,z++)
            if (not EMPTYP(z))
                {
                for (j=0,zj=S_V_S(z);j<S_V_LI(z);j++,zj++)
                    FREESELF(zj);
                FREESELF_INTEGERVECTOR(z);
                }
            else if (S_I_I(z) == -1) goto ee;
            else { i = S_I_I(z)-1; z = S_V_I(vec,i); }
        }
    else {
        for (i=(INT)0,z=S_V_S(vec);i<S_V_LI(vec);i++,z++)
            if (not EMPTYP(z))
                {
                C_O_K(z,INTEGERVECTOR);
                FREESELF_INTEGERVECTOR(z);
                }
            else if (S_I_I(z) == -1) goto ee;
            else { i = S_I_I(z)-1; z = S_V_I(vec,i); }
        }
 
ee: 
    SYM_free(S_V_S(vec));
    FREEALL(S_V_L(vec));
    freevectorstruct(S_O_S(vec).ob_vector);
    C_O_K(vec,EMPTY);
 
    ENDR("freeself_hashtable");
}



INT freeself_bitvector(a) OP a;
/* AK 081294 */
/* AK 020698 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"freeself_bitvector",a);

    if (S_V_S(a) != NULL)
        SYM_free(S_V_S(a));
    FREEALL(S_V_L(a)); 
    freevectorstruct(S_O_S(a).ob_vector);
    C_O_K(a,EMPTY);
    ENDR("freeself_bitvector");
}

#define FREESELF_VC(vec)\
    if (S_V_LI(vec) == 1)\
        FREEALL(S_V_S(vec));\
    else if (S_V_LI(vec) > 0)\
        {\
        OP z;INT i;\
        for (z = S_V_S(vec),i=0;i<S_V_LI(vec);i++,z++)\
            FREESELF(z);\
 \
        SYM_free(S_V_S(vec));\
        }\
    FREEALL(S_V_L(vec));\
    freevectorstruct(S_O_S(vec).ob_vector);\
    C_O_K(vec,EMPTY);                                                           


INT freeself_laurent(vec) OP vec;
/* AK 060502 */
{
    INT  erg=OK;
    CTO(LAURENT,"freeself_laurent",vec);
    FREESELF_VC(vec);
    ENDR("freeself_laurent");
}




INT freeself_vector(vec) OP vec;
/* 
   frees the memory allocated to a vector object,
   after this routine vec is an empty object 
*/
/* AK 280689 V1.0 */ /* AK 211189 V1.1 */ /* AK 130691 V1.2 */ 
/* AK 200891 V1.3 */ /* AK 011098 V2.0 */
/* AK 271006 V3.1 */
{
    INT  erg=OK;
    CTTTO(QUEUE,WORD,VECTOR,"freeself_vector",vec);


	{
	FREESELF_VC(vec);
	}


    ENDR("freeself_vector");
}




INT addinvers_vector(vec,res) OP vec,res;
/* AK 270887 */ /* AK 280689 V1.0 */ /* AK 201289 V1.1 */
/* AK 200891 V1.3 */ /* AK 011098 V2.0 */
/* AK 271006 V3.1 */
{
    INT erg = OK;
    CTO(VECTOR,"addinvers_vector(1)",vec);
    CTO(EMPTY,"addinvers_vector(2)",res);

	    {
	    INT i;

	    erg += m_l_v(S_V_L(vec),res);
	    C_O_K(res,S_O_K(vec));
	    for (i=0;i<S_V_LI(vec);i++) 
		erg += addinvers(S_V_I(vec,i),S_V_I(res,i));
	    }

    ENDR("addinvers_vector");
}


INT addinvers_apply_vector(vec) OP vec;
/* AK 201289 V1.1 */ /* AK 080591 V1.2 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,erg=OK;
    CTO(VECTOR,"addinvers_apply_vector(1)",vec);

    for (i=(INT)0;i<S_V_LI(vec);i++) 
        erg += addinvers_apply(S_V_I(vec,i));

    ENDR("addinvers_apply_vector");
}

INT mod_vector(vec,mo,res) OP vec,mo,res;
/* AK 101198 V2.0 */
{
    INT i,erg=OK;
    CTO(VECTOR,"mod_vector(1)",vec);
    erg += m_l_v(S_V_L(vec),res);
        C_O_K(res,S_O_K(vec));
    for (i=(INT)0;i<S_V_LI(vec);i++) 
        erg += mod(S_V_I(vec,i),mo, S_V_I(res,i) );
    ENDR("mod_vector");
}


INT addtoallvectorelements(zahl,vector,res) OP zahl,vector,res;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT        i;
    INT erg = OK;
    CTO(VECTOR,"addtoallvectorelements(2)",vector);

    erg += m_l_v(S_V_L(vector),res);
    C_O_K(res,S_O_K(vector));
    for(    i = (INT)0; i < S_V_LI(res);
        erg += add(zahl,S_V_I(res,i),S_V_I(res,i)),
        i++);
    ENDR("addtoallvectorelements");
}

INT absolute_vector(vec,res) OP vec, res;
/* AK 240293 */
/* AK 011098 V2.0 */
{
    INT        i,erg=OK;
    CTO(VECTOR,"absolute_vector(1)",vec);
    CTO(EMPTY,"absolute_vector(2)",res);

    m_il_v(    S_V_LI(vec), res);

    for(    i=(INT)0; i < S_V_LI(vec); i++)
        {
        erg += absolute(S_V_I(vec,i),S_V_I(res,i));
        }
    C_O_K(res,S_O_K(vec));
    ENDR("absolute_vector");
}

INT absolute_integervector(vec,res) OP vec, res;
/* AK 070502 */
{
    INT        i,erg=OK;
    CTO(INTEGERVECTOR,"absolute_vector(1)",vec);
    CTO(EMPTY,"absolute_vector(2)",res);
 
    erg += m_il_integervector(    S_V_LI(vec), res);
 
    for(    i=(INT)0; i < S_V_LI(vec); i++)
        ABSOLUTE_INTEGER(S_V_I(vec,i),S_V_I(res,i));
        
    ENDR("absolute_vector");
}  

#define COPY_VC(vec,res)\
    {\
    OP zv,zr;\
    INT i;\
    erg += m_il_v( S_V_LI(vec), res); \
    for(zv=S_V_S(vec), i=0, zr = S_V_S(res);\
        i < S_V_LI(vec); \
        i++,zv++,zr++)  \
            COPY(zv,zr);   \
    }

INT copy_vector(vec,res) OP vec, res;
/* AK 021286 */ /* AK 280689 V1.0 */ /* AK 081289 V1.1 */
/* AK 120391 V1.2 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(VECTOR,"copy_vector(1)",vec);
    CTO(EMPTY,"copy_vector(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,VECTOR);
    ENDR("copy_vector");
}

INT copy_word(vec,res) OP vec, res;
{
    INT erg = OK;
    CTO(WORD,"copy_word(1)",vec);
    CTO(EMPTY,"copy_word(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,WORD);
    ENDR("copy_word");
}  
INT copy_kranz(vec,res) OP vec, res;
{
    INT erg = OK;
    CTO(KRANZ,"copy_kranz(1)",vec);
    CTO(EMPTY,"copy_kranz(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,KRANZ);
    ENDR("copy_kranz");
}  

INT copy_subset(vec,res) OP vec, res;
{
    INT erg = OK;
    CTO(SUBSET,"copy_subset(1)",vec);
    CTO(EMPTY,"copy_subset(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,SUBSET);
    ENDR("copy_subset");
}  
INT copy_laurent(vec,res) OP vec, res;
{
    INT erg = OK;
    CTO(LAURENT,"copy_laurent(1)",vec);
    CTO(EMPTY,"copy_laurent(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,LAURENT);
    ENDR("copy_laurent");
}  
INT copy_queue(vec,res) OP vec, res;
{
    INT erg = OK;
    CTO(QUEUE,"copy_queue(1)",vec);
    CTO(EMPTY,"copy_queue(2)",res);
    COPY_VC(vec,res);
    C_O_K(res,QUEUE);
    ENDR("copy_queue");
}  



INT sub_comp_bv(a,b) OP a,b;
/* AK 180396 */
/* AK 011098 V2.0 */
{
    INT erg=0,i,ai,bi;
    CTO(BITVECTOR,"comp_bv",a);
    CTO(BITVECTOR,"comp_bv",b);
    if (S_V_LI(a) != S_V_LI(b)) 
        return NONCOMPARABLE;
    for (i=0;i<S_V_LI(a);i++)
        {
        ai = GET_BV_I(a,i);
        bi = GET_BV_I(b,i);
        if (ai == bi) continue;
        if ((ai < bi) && (erg == 1)) return NONCOMPARABLE;
        if ((ai < bi) && (erg == 0)) { erg = -1; continue; }
        if ((ai > bi) && (erg == -1)) return NONCOMPARABLE;
        if ((ai > bi) && (erg == 0)) { erg = 1; continue; }
        }
    return erg;
    ENDR("sub_comp_bv");
}

INT comp_bv(a,b) OP a,b;
/* AK 200395 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"comp_bv",a);
    CTO(BITVECTOR,"comp_bv",b);
    if (S_V_LI(a) != S_V_LI(b)) 
        error("comp_bv:different lengths");
/*
    for (i=0;i<S_V_LI(a);i++)
        if (GET_BV_I(a,i) < GET_BV_I(b,i)) return (INT)-1;
        else if (GET_BV_I(a,i) > GET_BV_I(b,i)) return (INT)1;
    return (INT) 0;
*/
/*
    println(a);
    println(b);
*/
    erg = (INT) memcmp((void *)S_V_S(a), (void *)S_V_S(b), (size_t)S_BV_LI(a));
/*
    printf("comp=%ld\n",erg);
*/
    return erg;

    

    ENDR("comp_bv");
}


INT eq_vector(a,b) OP a,b;
/* AK 201201 */
/* AK 291104 V3.0 */
{
    INT erg = OK;
    CTO(VECTOR,"eq_vector(1)",a);
    if (S_O_K(b) != VECTOR) return FALSE;
    CTO(VECTOR,"eq_vector(2)",b);
    if (S_V_LI(b) != S_V_LI(a)) return FALSE;

    {
    INT i,l=S_V_LI(a);
    for (i=0;i<l;i++)
        if (not EQ(S_V_I(a,i), S_V_I(b,i)) ) return FALSE;

    return TRUE;
    }
    ENDR("eq_vector");
}

INT eq_integervector_integervector(a,b) OP a,b;
/* AK 120104 */ /* AK 280804 V3.0 */
{
    INT erg = OK;
    CTO(INTEGERVECTOR,"eq_integervector_integervector(1)",a);
    CTO(INTEGERVECTOR,"eq_integervector_integervector(2)",b);
    {
    OP za,zb;INT i;
    if (S_V_LI(a) != S_V_LI(b)) return FALSE;
    for (i=0,za=S_V_S(a),zb=S_V_S(b);
         i<S_V_LI(a);
         i++,za++,zb++)
        if (S_I_I(za)!=S_I_I(zb)) return FALSE;
    return TRUE;
    }
    ENDR("eq_integervector_integervector");
}

#define COMP_VC(a,b)\
    {/*lex comp for vector objects */\
    INT i,res;\
    OP az,bz;\
    for (az=S_V_S(a),bz=S_V_S(b),i=0; \
         i<S_V_LI(a); i++,az++,bz++)\
    {\
        if (i >=  S_V_LI(b)) return(1);\
        res = comp(az,bz);\
        if (res != 0) return(res);\
    };\
    if (S_V_LI(a) < S_V_LI(b)) return  -1;\
    return(0);\
    }

INT comp_integervector(a,b) OP a,b;
/* AK 011098 V2.0 *//* AK 270804 V3.0 */
{
    INT erg = OK;
    CTTTO(INTEGERVECTOR,COMPOSITION,SUBSET,"comp_integervector(1)",a);
    if (S_O_K(b) == VECTOR) { /* AK 080502 */ COMP_VC(a,b); }
    CTTTO(INTEGERVECTOR,COMPOSITION,SUBSET,"comp_integervector(2)",b);
    {
    OP za,zb;
    INT i;

    za = S_V_S(a);zb=S_V_S(b);
    for (    i=0; i<S_V_LI(a); i++,za++,zb++)
    {
        if (i >=  S_V_LI(b)) return 1;
        if (S_I_I(za) > S_I_I(zb)) return 1;
        if (S_I_I(za) == S_I_I(zb)) continue;
        return -1;
    };
    if (i < S_V_LI(b))
        return  -1;
    return 0;
    }
    ENDR("comp_integervector");
}

INT comp_galois(a,b) OP a,b;
{
	INT erg = OK;
	CTO(GALOISRING,"comp_galois(1)",a);
	CTO(GALOISRING,"comp_galois(2)",b);
	{
    OP za,zb;
    INT i;

    za = S_V_S(a);zb=S_V_S(b);
    for (    i=0; i<S_V_LI(a); i++,za++,zb++)
    {
        if (i >=  S_V_LI(b)) return 1;
        if (S_I_I(za) > S_I_I(zb)) return 1;
        if (S_I_I(za) == S_I_I(zb)) continue;
        return -1;
    };
    if (i < S_V_LI(b))
        return  -1;
    return 0;
    }
	ENDR("comp_galois");
}

INT comp_vector(a,b) OP a,b;
/* AK 060488 */ /* AK 280689 V1.0 */ /* AK 201289 V1.1 */
/* AK 200891 V1.3 */
/* AK 260298 V2.0 */
{
    INT erg = OK;
    CTO(VECTOR,"comp_vector(1)",a);
    CTTTO(VECTOR,INTEGERVECTOR,WORD,"comp_vector(2)",b);
    COMP_VC(a,b);

    ENDR("comp_vector");
}

INT comp_word(a,b) OP a,b;
/* AK 060502 from comp_vector */
{
    INT erg = OK;
    CTO(WORD,"comp_word(1)",a);
    CTTTO(VECTOR,INTEGERVECTOR,WORD,"comp_word(2)",b);
    COMP_VC(a,b);
 
    ENDR("comp_word");
}   


INT scan_bitvector(res) OP res;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 080591 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,erg =OK;
    OP d,e;
    COP("scan_bitvector(1)",res);

    d = callocobject();
    e = callocobject();
    erg += printeingabe("input of a bitvector (0-1 vector)");
    erg += printeingabe("length of bit vector ");
    erg += scan(INTEGER,d);
    erg += b_l_v(d,e);
    for (i=(INT)0;i<S_V_LI(e); erg += scan(INTEGER,S_V_I(e,i++)));
    erg += t_INTVECTOR_BITVECTOR(e,res);
    FREEALL(e);
    ENDR("scan_bitvector");
}

INT scan_integervector(res) OP res;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 080591 V1.2 */
/* AK 200891 V1.3 */ /* AK 180998 V2.0 */
{
    INT i,erg =OK;
    OP d;
    COP("scan_integervector(1)",res);

    d = callocobject();
    erg += printeingabe("length of INTEGER vector ");
    erg += scan(INTEGER,d);
    erg += b_l_v(d,res);
    for (i=(INT)0;i<S_V_LI(res); erg += scan(INTEGER,S_V_I(res,i++)));
    C_O_K(res,INTEGERVECTOR);
    ENDR("scan_integervector");
}

INT scan_permvector(res) OP res;
/* AK 180998 V2.0 */
{
    INT i,erg =OK;
    OP d;
    COP("scan_permvector(1)",res);

    d = callocobject();
    erg += printeingabe("length of PERMUATION vector ");
    erg += scan(INTEGER,d);
    erg += b_l_v(d,res);
    for (i=(INT)0;i<S_V_LI(res); erg += scan(PERMUTATION,S_V_I(res,i++)));
    C_O_K(res,VECTOR);
    ENDR("scan_permvector");
}




INT scan_vector(res) OP res;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,erg=OK;
    OBJECTKIND kind;
    OP d;
    COP("scan_vector(1)",res);

    d = callocobject();
    erg += printeingabe("length of vector "); 
    erg += scan(INTEGER,d);
    erg += b_l_v(d,res);
    erg += printeingabe("kind of vector elements ");
    kind = scanobjectkind();
    for (i=(INT)0;i < S_V_LI(res); erg += scan(kind,S_V_I(res,i++)));
    ENDR("scan_vector");
}



struct vector * callocvectorstruct()
/* AK 170889 V1.1 malloc statt calloc */ /* AK 211289 V1.1 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    struct vector * res;
    INT erg = OK;
#ifdef UNDEF
    if (vector_speicherindex >= 0) /* AK 231001 */
        {
        res=vector_speicher[vector_speicherindex--];
        goto ende;
        }

    res = (struct vector *) SYM_MALLOC(sizeof(struct vector));
    if (res == NULL) 
        no_memory();
ende:
    mem_counter_vec++;
#endif
    CALLOC_MEMMANAGER(struct vector,
                      vector_speicher,
                      vector_speicherindex,
                      mem_counter_vec,
                      res);
    return res;
    ENDTYP("callocvectorstruct", struct vector * );
}

INT freevectorstruct(v) struct vector *v;
/* AK 231001 */
{
    INT erg = OK;
#ifdef UNDEF
    if (vector_speicherindex+1 == vector_speichersize) {
       if (vector_speichersize == 0) {
           vector_speicher = (struct vector **) SYM_MALLOC(100 * sizeof(struct vector *));
           if (vector_speicher == NULL) {
               erg += error("no memory"); 
               goto endr_ende;
               }
           vector_speichersize = 100;
           }
       else {
           vector_speicher = (struct vector **) SYM_realloc (vector_speicher,
               2 * vector_speichersize * sizeof(struct vector *));
           if (vector_speicher == NULL) {
               erg += error("no memory"); 
               goto endr_ende;
               }
           vector_speichersize = 2 * vector_speichersize;
           }
       }
    vector_speicher[++vector_speicherindex] = v;
    mem_counter_vec--;
#endif
    FREE_MEMMANAGER(struct vector *,
                    vector_speicher,
                    vector_speicherindex,
                    vector_speichersize,
                    mem_counter_vec,
                    v);
    ENDR("freevectorstruct");
}

#ifdef UNDEF
static INT vec_speicher_ende()
/* AK 230101 */
{
    INT erg = OK,i;

    for (i=0;i<=vector_speicherindex;i++)
        SYM_free(vector_speicher[i]);
    if (vector_speicher!= NULL) {
        COP("vec_speicher_ende:vector_speicher",vector_speicher);
        SYM_free(vector_speicher);
        }
    vector_speicher=NULL;
    vector_speicherindex=-1;
    vector_speichersize=0; 
    ENDR("vec_speicher_ende");
}
#endif

     
INT b_ls_v(length,self,res) OP length, self,res;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* self will be freed */
{
    OBJECTSELF d;
    INT erg = OK;
    COP("b_ls_v(3)",res);

    d.ob_vector = callocvectorstruct();
    erg += b_ks_o(VECTOR, d,res); /* res will be freed */
    C_V_S(res,self); 
    C_V_L(res,length);
    ENDR("b_ls_v");
}


OP s_v_s(a) OP a; 
/* AK 270689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a);
    if (a==NULL) 
        { 
        error("s_v_s:object == NULL"); 
        return(NULL); 
        }
    if (c.ob_vector==NULL) 
        { 
        error( "s_v_s:vector pointer == NULL");
        return(NULL); 
        }
    if (not vectorp(a)) { /* AK 210192 */
        error("s_v_s: not VECTOR");
        return NULL;
        }
    return(c.ob_vector->v_self);
}

OP s_v_l(a) OP a; 
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    OBJECTSELF c; 
    OP erg=NULL;
    c = s_o_s(a);
    if (a==NULL) 
        { 
        error("s_v_l:object == NULL"); 
        return(NULL); 
        }
    if (c.ob_vector==NULL)
        {  
        error( "s_v_l:vector pointer == NULL"); 
        return(NULL); 
        }
    if (not vectorp(a)) { /* AK 210192 */
        WTO("s_v_l",a);
        return NULL;
        }
    erg = c.ob_vector->v_length;
    if (s_o_k(erg) != INTEGER) 
        {  
        printobjectkind(erg);
        error( "s_v_l:length != INTEGER");
        return(NULL); 
        }
    if (s_i_i(erg) < (INT)0) 
        {  
        error( "s_v_l:length <0");
        return(NULL); 
        }
    return erg;
}


INT s_v_li(a) OP a; 
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    INT erg = s_i_i(s_v_l(a)); 
    return erg;
}

OP s_v_i(a,i) OP a; INT i; 
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT j;
    if (i<(INT)0) 
        { 
        fprintf(stderr,"index = %ld\n",i);
        error("s_v_i:negative index"); 
        return(NULL); 
        }
    if (s_o_k(a) == HASHTABLE)
        {
        if (i > (j=s_v_li(a)) ) 
        { 
        fprintf(stderr,"index = %ld dimension = %ld\n",i,j);
        error("s_v_i hashtable:index too big"); 
        return(NULL); 
        }
        }
    else if (i >= (j=s_v_li(a)) ) 
        { 
        fprintf(stderr,"index = %ld dimension = %ld\n",i,j);
        error("s_v_i:index too big"); 
        return(NULL); 
        }
    return(s_v_s(a) + (i));
}

INT c_v_i(a,i,b) OP a,b; INT i;
/* AK 170889 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    c_o_k(s_v_i(a,i),s_o_k(b)); 
    c_o_s(s_v_i(a,i),s_o_s(b)); 
    return(OK); 
}

INT s_v_ii(a,i) OP a; INT i;
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    return(s_i_i(s_v_i(a,i))); 
}

INT c_v_s(a,b) OP a,b;
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    (c.ob_vector->v_self)=b; 
    return(OK); 
}

INT c_v_l(a,b) OP a,b;
/* AK 270689 V1.0 */ /* AK 201289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    (c.ob_vector->v_length)=b; 
    return(OK); 
}

#define LASTOF_V(a,b)\
SYMCHECK(S_V_LI(a) == 0,"LASTOF_V:length of vector == 0");\
if (S_V_LI(a)>0) COPY(S_V_I(a,S_V_LI(a)-(INT)1),b);


INT lastof_vector(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */ /* AK 020398 V2.0 */
{
    INT erg = OK;
    CTO(VECTOR,"lastof_vector(1)",a);
    CTO(EMPTY,"lastof_vector(2)",b);
    LASTOF_V(a,b);
    ENDR("lastof_vector");
}

INT lastof_integervector(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */ /* AK 020398 V2.0 */
{
    INT erg = OK;
    CTO(INTEGERVECTOR,"lastof_integervector(1)",a);
    CTO(EMPTY,"lastof_integervector(2)",b);
    LASTOF_V(a,b);
    ENDR("lastof_integervector");
}


INT length_vector(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 180691 V1.2 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    return(copy(S_V_L(a),b));
}


INT tex_vector(vecobj) OP vecobj;
/* AK 101187 */
/* mit tex werden alle elemente ausgegeben */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */
/* AK 070291 V1.2 prints to texout */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,ot=texmath_yn;
    
    if (texmath_yn==0)
        {
        fprintf(texout,"\\ $[");
        texmath_yn = 1;
        }
    else
        fprintf(texout,"\\ [");

    for(    i = (INT)0; i<S_V_LI(vecobj); i++)
    {
        texposition += (INT)6;
        tex(S_V_I(vecobj,i));
        if (i != S_V_LI(vecobj)-1)
            { fprintf(texout,","); texposition ++; }
    };

    fprintf(texout,"]\\ ");
    texposition += (INT)6;
    if (ot == 0) {
        fprintf(texout,"$ ");
        texmath_yn = 0;
        }
    return(OK);
}


INT sprint_vector(t,a) char *t; OP a;
/* AK 240398 V2.0 */
{
    INT erg = OK;
        INT i;
    if (not VECTORP(a))
        {
        WTO("sprint_vector",a);
        goto endr_ende;
        }
        sprintf(t,"["); t++;
    for (i=0;i<S_V_LI(a);i++)
        {
        if (i>0) { sprintf(t,","); t++; }
        erg += sprint(t,S_V_I(a,i));
        if (erg != OK)
            {
            WTO("sprint_vector: wrong type of vector-entry",S_V_I(a,i));
            goto endr_ende;
            }
        t += strlen(t);
        }
    sprintf(t,"]"); 
    ENDR("sprint_vector");

}

INT sprint_integervector(t,a) char *t; OP a;
/* AK 240398 V2.0 */
{
    INT erg = OK;
    INT i;
    CTO(INTEGERVECTOR,"sprint_integervector",a);
    sprintf(t,"["); t++;
    for (i=0;i<S_V_LI(a);i++)
        {
        if (i>0) { sprintf(t,","); t++; }
        sprintf(t,"%ld",S_V_II(a,i));
        t += intlog(S_V_I(a,i));
        if (S_V_II(a,i) < 0) t++;
        }
    sprintf(t,"]"); 
    ENDR("sprint_integervector");
}

INT fprint_vector(f,vecobj) FILE *f; OP vecobj;
/* AK 171186 */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 190298 V2.0 */ /* AK 201204 V3.0 */
{
    INT i, erg = OK;
    COP("fprint_vector(1)",f);

    putc('[',f);
    if (f == stdout) zeilenposition++;
    for(    i = 0; i<S_V_LI(vecobj); i++)
    {
        erg += fprint(f,S_V_I(vecobj,i));
        if (i != S_V_LI(vecobj)-1)
        {
            putc(',',f);
            if (f == stdout) { 
                zeilenposition++;
                check_zeilenposition(stdout);
                }
            
        }
    }

    putc(']',f);
    if (f == stdout) zeilenposition++;
    ENDR("fprint_vector");
}




INT objectread_bv(filename,vec) FILE *filename; OP vec;
/* AK 220395 */
/* AK 011098 V2.0 */
{
    INT erg = OK,n;
    B_LS_V(callocobject(),NULL,vec);
    C_O_K(vec,BITVECTOR);
    objectread(filename,S_V_L(vec));
    fgetc(filename);
    C_V_S(vec,SYM_calloc(S_BV_LI(vec)/8+1,8) );
    n = fread(S_V_S(vec),(size_t)1,(size_t)S_BV_LI(vec),filename);
    if (n != S_BV_LI(vec))
        {
        erg += error("objectread_bv: error during read");
        goto endr_ende;
        }
    ENDR("objectread_bv");
}

INT objectread_vector(filename,vec) FILE *filename; OP vec;
/* AK 131086 */ /* AK 280689 V1.0 */ /* AK 211289 V1.1 */
/* AK 200891 V1.3 */ /* AK 011098 V2.0 */
{
    INT i,erg = OK;
    OP length;
    COP("objectread_vector(1)",filename);
    COP("objectread_vector(2)",vec);

    length = callocobject();
    erg += objectread(filename,length);
    erg += b_l_v(length,vec);
    for (i=(INT)0;i<S_I_I(length);i++) 
        erg += objectread(filename,S_V_I(vec,i));
    ENDR("objectread_vector");
}
INT objectwrite_bv(filename,vec) FILE *filename; OP vec;
/* AK 220395 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    size_t n;
    COP("objectwrite_bv(1)",filename);
    COP("objectwrite_bv(2)",vec);
    fprintf(filename," %ld ",S_O_K(vec));
    objectwrite(filename,S_V_L(vec));
    n = fwrite(S_V_S(vec),(size_t)1,(size_t)S_BV_LI(vec),filename);
    if (n != S_BV_LI(vec))
        {
        erg += error("objectwrite_bv: error during write");
        goto endr_ende;
        }
    ENDR("objectwrite_bv");
}


INT objectwrite_vector(filename,vec) FILE *filename; OP vec;
/* AK 131086 */ /* AK 280689 V1.0 */ /* AK 211289 V1.1 */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i;
    INT erg = OK;
    COP("objectwrite_vector(1)",filename);
    COP("objectwrite_vector(2)",vec);
    fprintf(filename," %ld ",S_O_K(vec));

    erg += objectwrite(filename,S_V_L(vec));

    for (i=(INT)0;i<S_V_LI(vec);i++) 
        erg += objectwrite(filename,S_V_I(vec,i));
    ENDR("objectwrite_vector");
}


INT inc_vector(a) OP a;
/* AK 011098 V2.0 */
/* AK 020206 V3.0 */
/* increase the length by one empty object at the end */
{
    return inc_vector_co(a,(INT) 1);
}

INT inc_vector_co(a,r) OP a; INT r;
/* AK 270887 */
/* increase the length by r empty objects at the end */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */ /* AK 280705 V3.0 */
{
    INT i,erg=OK;
    OP z;
    CTTTTO(QUEUE,HASHTABLE,VECTOR,INTEGERVECTOR,"inc_vector_co(1)",a);
    if (r == (INT)0) goto endr_ende;
    SYMCHECK((r < 0), "inc_vector_co: neg increment");


    if ((S_V_LI(a) == (INT)0)&&(r==1))
        {
        z = CALLOCOBJECT();
        }
    else if (S_V_LI(a) == (INT)0)
        {
        i = (r) * (sizeof(struct object));
        z =  (OP ) SYM_MALLOC((unsigned) i);
        }
    else if (S_V_LI(a) == (INT)1)  /* AK 310197 */
        {
        i = (r+1) * (sizeof(struct object));
        z =  (OP ) SYM_MALLOC((unsigned) i);
        *z = *S_V_S(a);
        C_O_K(S_V_S(a),EMPTY);
        FREEALL(S_V_S(a)); /* vector of length, the self part was allocated 
                        using callocobject */
        }
    else {
        i = (S_V_LI(a) + r) * (sizeof(struct object));
        z =  (OP ) SYM_realloc((char*) S_V_S(a),(unsigned) i);
        }

    SYMCHECK(z == NULL,"inc_vector_co:self == NULL");

    C_V_S(a,z);
    M_I_I(S_V_LI(a) + r, S_V_L(a));
    if (S_O_K(a) == INTEGERVECTOR)
        for (i=0;i<r;i++)
            M_I_I(0,S_V_I(a,S_V_LI(a)-1-i));
    else
        for (i=0;i<r;i++)
            C_O_K(S_V_I(a,S_V_LI(a)-1-i),EMPTY);
    ENDR("inc_vector_co");
}

INT sum_integervector(vecobj,res) OP vecobj,res;
/* AK V2.0 250298 */
{
    INT i;
    INT erg = OK;
    CTTO(COMPOSITION,INTEGERVECTOR,"sum_integervector(1)",vecobj);
    CTTO(INTEGER,EMPTY,"sum_integervector(2)",res);

    M_I_I((INT)0,res);
    for (    i=(INT)0; i < S_V_LI(vecobj);i++)
        {
        ADD_APPLY_INTEGER(S_V_I(vecobj,i), res);
        }

    ENDR("sum_integervector");
}

INT sum_vector(vecobj,res) OP vecobj,res;
/* AK 280689 V1.0 */ /* AK 081289 V1.1 */ /* AK 070891 V1.3 */
/* AK V2.0 250298 */
{
    INT i;
    INT erg = OK;
    CTO(EMPTY,"sum_vector(2)",res);
    M_I_I((INT)0,res);
    for (    i=(INT)0; i < S_V_LI(vecobj);i++)
        {
        ADD_APPLY(     S_V_I(vecobj,i), res);
        }
    ENDR("sum_vector");
}



INT max_integervector(vec,m) OP vec,m;
/* return copy of the maximal element */
/* AK 061098 V2.0 */
{
    INT i;
    INT erg = OK;
    INT zm;
    CE2(vec,m,max_integervector);
    zm = S_V_II(vec,(INT)0);
    for(i=(INT)1;i<S_V_LI(vec);i++)
        if (S_V_II(vec,i) > zm) zm = S_V_II(vec,i);
    erg += m_i_i(zm,m);
    ENDR("max_integervector");
}


INT min_integervector(vec,m) OP vec,m;
/* return copy of the minimal element */
/* AK 140703 */
{
    INT i;
    INT erg = OK;
    INT zm;
    CE2(vec,m,min_integervector);
    zm = S_V_II(vec,(INT)0);
    for(i=(INT)1;i<S_V_LI(vec);i++)
        if (S_V_II(vec,i) < zm) zm = S_V_II(vec,i);
    erg += m_i_i(zm,m);
    ENDR("min_integervector");
}



INT max_vector(vec,m) OP vec,m;
/* return copy of the maximal element */
/* AK 280689 V1.0 */ /* AK 050390 V1.1 */ /* AK 100691 V1.2 */ 
/* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i;
    INT erg = OK;
    OP zm;
    CTO(VECTOR,"max_vector(1)",vec);
    CE2(vec,m,max_vector);
    zm = S_V_I(vec,(INT)0);
    for(i=(INT)1;i<S_V_LI(vec);i++)
        if (GR(S_V_I(vec,i),zm)) zm = S_V_I(vec,i);
    erg += copy(zm,m);
    ENDR("max_vector");
}


INT min_vector(vec,m) OP vec,m;
/* return copy of the minimal element */
/* AK 140703 */
{
    INT i;
    INT erg = OK;
    OP zm;
    CTO(VECTOR,"min_vector(1)",vec);
    CE2(vec,m,min_vector);
    zm = S_V_I(vec,(INT)0);
    for(i=(INT)1;i<S_V_LI(vec);i++)
        if (LT(S_V_I(vec,i),zm)) zm = S_V_I(vec,i);
    CLEVER_COPY(zm,m);
    ENDR("min_vector");
}



OP findmax_vector(vec) OP vec;
/* AK 100102 */
{
    INT erg = OK;
    CTO(VECTOR,"findmax_vector(1)",vec);
    {
    OP res; INT i;
    if (S_V_LI(vec) == 0) return NULL;
    res = S_V_S(vec);
    for (i=1; i<S_V_LI(vec);i++)
         if (GR(S_V_I(vec,i),res) ) res = S_V_I(vec,i);
    return res;
    }
    ENDO("findmax_vector");
}

INT mult_apply_scalar_vector(a,b) OP a,b;
/* AK 060498 V2.0 */
{
    INT erg = OK;
    INT i;
    CTO(VECTOR,"mult_apply_scalar_vector(2)",b);
    for (i=(INT)0; i<S_V_LI(b); i++)
        MULT_APPLY(a, S_V_I(b,i));
    ENDR("mult_apply_scalar_vector");
}

INT mult_apply_integer_integervector(a,b) OP a,b;
/* AK 090703 V2.0 */
{
    INT erg = OK;
    INT i;
    CTO(INTEGERVECTOR,"mult_apply_integer_integervector(2)",b);
    CTO(INTEGER,"mult_apply_integer_integervector(1)",a);
    for (i=(INT)0; i<S_V_LI(b); i++)
        {
        MULT_APPLY_INTEGER_INTEGER(a, S_V_I(b,i));
        if (S_O_K(S_V_I(b,i)) != INTEGER)
            C_O_K(b,VECTOR);
        }
    ENDR("mult_apply_integer_integervector");
}


INT mult_scalar_vector(a,b,c) OP a,b,c;
/* AK 010888 skalarmultiplikation */
/* a ist skalar b ist vector c wird vector */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i = (INT)0;
    INT erg = OK;
    CTO(VECTOR,"mult_scalar_vector(2)",b);
    CTO(EMPTY,"mult_scalar_vector(3)",c);
    erg += m_il_v(S_V_LI(b),c);
    C_O_K(c,S_O_K(b));
    for (i=(INT)0; i<S_V_LI(c); i++)
        erg += mult(a, S_V_I(b,i), S_V_I(c,i));
    ENDR("mult_scalar_vector");
}

#ifdef MATRIXTRUE
INT mult_vector_matrix(a,b,c) OP a, b, c;
/* AK 200192 */
/* AK 011098 V2.0 */
{
    INT i,j;
    INT erg = OK;
    OP d;
    CTO(VECTOR,"mult_vector_matrix(1)",a);
    CTO(MATRIX,"mult_vector_matrix(2)",b);
    CTO(EMPTY,"mult_vector_matrix(3)",c);
    SYMCHECK(S_V_LI(a)!=S_M_HI(b),"mult_vector_matrix:length of vector != height of matrix");

    erg += m_il_v(S_M_LI(b),c);
    d = CALLOCOBJECT();
    for (i=0;i<S_V_LI(c);i++)
    {
    for (j=0;j<S_V_LI(a);j++)
        {
        FREESELF(d); 
        MULT(S_V_I(a,j),S_M_IJ(b,j,i),d);
        if (j==0)
            SWAP(d,S_V_I(c,i));
        else
            ADD_APPLY(d,S_V_I(c,i));
        }
    }
    FREEALL(d);
    ENDR("mult_vector_matrix");
}
#endif /* MATRIXTRUE */

INT mult_vector_vector(a,b,c) OP a, b, c;
/* AK 110588  componentenweise multiplication */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i = 0, erg = OK;
    CTO(VECTOR,"mult_vector_vector(1)",a);
    CTO(VECTOR,"mult_vector_vector(2)",b);
    CTO(EMPTY,"mult_vector_vector(3)",c);
    SYMCHECK( (S_V_LI(a) !=  S_V_LI(b)), "mult_vector_vector:different size of vectors");
    
    
    erg += m_il_v(S_V_LI(a),c);
    for (i=(INT)0;i<S_V_LI(b);i++)
        MULT(S_V_I(a,i),S_V_I(b,i),S_V_I(c,i));

    ENDR("mult_vector_vector");
}

INT scalarproduct_vector(a,b,d) OP a,b,d;
/* AK 141189 V1.1 */ /* AK 070891 V1.3 */ /* AK 011098 V2.0 */
/* AK 230904 V3.0 */
{
    INT erg = OK; /* AK 200192 */
    CTO(VECTOR,"scalarproduct_vector(1)",a);
    CTO(VECTOR,"scalarproduct_vector(2)",b);
    CTO(EMPTY,"scalarproduct_vector(3)",d);
    SYMCHECK( (S_V_LI(a) != S_V_LI(b)), "scalarproduct_vector:different length");

    {
    OP c,za=S_V_S(a),zb=S_V_S(b);
    INT i;
    c = CALLOCOBJECT();
    null(za,d);
    for (i=S_V_LI(a)-1;i>=0;i--,za++,zb++)
        {
        if ( (not NULLP(za)) && (not NULLP(zb))) { /* AK 230904 */
            CLEVER_MULT(za,zb,c);
            ADD_APPLY(c,d);
            }
        }
    FREEALL(c);
    }

    CTO(ANYTYPE,"scalarproduct_vector(e)",d);
    ENDR("scalarproduct_vector");
}

INT dec_vector(a) OP a;
/* AK 120187  kuerzt den vector um 1 */
/* das letzte element wird gestrichen */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT erg = OK; /* AK 100893 */
    OP zz;
    CTO(VECTOR,"dec_vector(1)",a);

    SYMCHECK(S_V_LI(a) == 0, "dec_vector:initial length == 0");

    FREESELF(S_V_I(a,S_V_LI(a)-1));
    /* freigeben des speicherplatzes des letzten vectorelements */
    DEC_INTEGER(S_V_L(a));
    /* verkuerzen der laenge um eins */
    if (S_V_LI(a) == (INT)1) /* AK 111093 */
        {
        zz = S_V_S(a);
        C_V_S(a,CALLOCOBJECT());
        *(S_V_S(a)) = *zz;
        SYM_free(zz);
        }
    else if (S_V_LI(a) == (INT)0) /* AK 100893 */
        {
        FREEALL(S_V_S(a));
        C_V_S(a,NULL);
        }

    ENDR("dec_vector");
}

INT dec_integervector(a) OP a;
/* AK 230402 */
/* AK 230904 V3.0 */
{
    INT erg = OK; /* AK 100893 */
    CTO(INTEGERVECTOR,"dec_integervector(1)",a);
    SYMCHECK(S_V_LI(a) == 0, "dec_integervector:initial length == 0");
    {
    OP zz;
 
    DEC_INTEGER(S_V_L(a));
    /* verkuerzen der laenge um eins */
    if (S_V_LI(a) == (INT)1) /* AK 111093 */
        {
        zz = S_V_S(a);
        C_V_S(a,CALLOCOBJECT());
        *(S_V_S(a)) = *zz;
        SYM_free(zz);
        }
    else if (S_V_LI(a) == (INT)0) /* AK 100893 */
        {
        FREEALL(S_V_S(a));
        C_V_S(a,NULL);
        }
    }
    ENDR("dec_integervector");
}  

INT reverse_vector(a,b) OP a, b;
/* AK 160802 */
/* AK 230904 V3.0 */
{
    INT erg = OK;
    CTTTO(WORD,INTEGERVECTOR,VECTOR,"reverse_vector(1)",a);
    CE2(a,b,reverse_vector);
    {
    INT i,j;
    erg += m_il_v(S_V_LI(a),b);
    C_O_K(b,S_O_K(a));
    for (i=0,j=S_V_LI(b)-1;i<S_V_LI(b);i++,j--) 
        COPY(S_V_I(a,i),S_V_I(b,j));
    }
    ENDR("reverse_vector");
}

INT append_vector(a,b,c) OP a, b, c;
/* haengt den vector b an den vector a an */
/* c = [a1,..,ak,b1,...,bl] */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT        i,length;
    INT erg = OK;
    CTTTTO(QUEUE,WORD,INTEGERVECTOR,VECTOR,"append_vector(1)",a);
    if (a == c)  /* a = [a1,..,ak,b1,..,bl] */
        {
        erg +=  append_apply_vector(a,b);
        goto endr_ende;
        }
    if (b == c)   /* b = [a1,...,ak,b1,....,bl] */
        {
        OP d;
        d = callocobject();
        erg += append_vector(a,b,d);
        erg += swap(b,d);
        FREEALL(d);
        goto endr_ende;
        }

    if (not VECTORP(b)) /* AK 291292 */
        {
                /* c = [a1,...,ak,b] */
                erg += m_il_v(S_V_LI(a)+1,c);
                C_O_K(c,S_O_K(a));
                for(    i=(INT)0;i<S_V_LI(a);i++)
                     COPY(S_V_I(a,i),S_V_I(c,i));
                COPY(b,S_V_I(c,S_V_LI(a)));
        goto endr_ende;
        }
    length=S_V_LI(a)+S_V_LI(b);
    erg += m_il_v(length,c);
    if (S_O_K(a) == S_O_K(b)) /* AK 030295 */
        C_O_K(c,S_O_K(a));
    else
        C_O_K(c,VECTOR);
    for(    i=(INT)0;i<length; i++)
        if (i < S_V_LI(a))
            erg += copy(S_V_I(a,i),S_V_I(c,i));
        else
            erg += copy(S_V_I(b,i-S_V_LI(a)),S_V_I(c,i));
    ENDR("append_vector");
}

INT append_apply_vector(a,b) OP a,b;
/* AK 060901 */
/* a is of vector type */
/* a = [a1,...,ak,b1,...,bl */
/* a and b may be equal */
{
     INT erg = OK,i,j;
     CTTTO(QUEUE,VECTOR,INTEGERVECTOR,"append_apply_vector(1)",a);
     if (a == b)
         {
         i = S_V_LI(a);
         erg += inc_vector_co(a,i);
         for (j=0;i<S_V_LI(a);i++,j++)
             {
             COPY(S_V_I(b,j),S_V_I(a,i));
             }
         }
     else if (not VECTORP(b))
         {
         erg += inc_vector(a);
         COPY(b,S_V_I(a,S_V_LI(a)-1));
         }
     else {
         j = S_V_LI(b);
         i = S_V_LI(a);
         erg += inc_vector_co(a,j);
         for (j=0;j<S_V_LI(b);j++)
             {
             COPY(S_V_I(b,j),S_V_I(a,i+j));
             }
         }
     ENDR("append_apply_vector");
}

INT mult_apply_vector(a,b) OP a, b;
/* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    switch (S_O_K(b)) {
        case VECTOR: 
            erg += mult_apply_vector_vector(a,b); break;
        default:
            erg = error("mult_apply_vector: wrong type"); break;
        }
    return erg;
}

INT mult_apply_vector_vector(a,b) OP a, b;
/* AK 110588  componentenweise multiplication */
/* AK 280689 V1.0 */ /* AK 211289 V1.1 */ /* AK 070891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i = (INT)0;
    INT erg = OK;
    CTO(VECTOR,"mult_apply_vector_vector(1)",a);
    CTO(VECTOR,"mult_apply_vector_vector(2)",b);
    SYMCHECK(S_V_LI(a) !=  S_V_LI(b),"mult_apply_vector_vector:different size of vectors ");

    for (i=(INT)0;i<S_V_LI(b);i++)
        MULT_APPLY(S_V_I(a,i),S_V_I(b,i));

    ENDR("mult_apply_vector_vector");
}

INT weight_vector(a,b) OP a,b;
/* number of nonzero entries */
/* a and b may be equal */
/* AK 131206 V3.1 */
{
	INT erg = OK;
	INT i,j=0;
	OP z;
	for (i=0,z=S_V_S(a);i<S_V_LI(a);i++,z++)
		if (NULLP(z)!=TRUE) j++;
	erg += m_i_i(j,b);
	ENDR("weight_vector");
}

INT nullp_integervector(a) OP a;
/* AK 311091 */
/* AK 190298 V2.0 */
/* AK 131206 V3.1 */
{
    INT i;
    INT erg = OK;
    CTO(INTEGERVECTOR,"nullp_integervector(1)",a);
    for (i=(INT)0;i<S_V_LI(a); i++)
        {
        if (not INTEGERP(S_V_I(a,i)))
            {
            C_O_K(a, VECTOR);
            if (not nullp(S_V_I(a,i)))
                return FALSE;
            }
        else    {
            if (S_V_II(a,i) != (INT)0) return FALSE;
            }
        }
    return TRUE;

    ENDR("nullp_integervector");
}

INT nullp_vector(a) OP a;
/* AK 311091 */
/* AK 011098 V2.0 */
/* AK 131206 V3.1 */
{
    INT i;
    for (i=(INT)0;i<S_V_LI(a); i++)
        if (not nullp(S_V_I(a,i)))
            return FALSE;
    return TRUE;
}

INT posp_vector(a) OP a;
/* AK 190298 V2.0 */
{
    INT erg = OK;
    INT i;
    CTO(VECTOR,"posp_vector(1)",a);
    for (i=(INT)0;i<S_V_LI(a); i++)
        if (not posp(S_V_I(a,i))) return FALSE;
    return TRUE;

    ENDR("posp_vector");
}

INT index_vector(a,b) OP a,b;
/* AK 010393 */ /* AK 011098 V2.0 */
/* get index of a in b */
/* AK 291104 V3.0 */
{
    INT erg = OK;
    CTO(VECTOR,"index_vector(2)",b);
    {
    INT i;
    for (i=0;i<S_V_LI(b);i++)
        if (EQ(S_V_I(b,i),a)) return i;
    return -1;
    }
    ENDR("index_vector");
}

static INT index_vector_binary_co(a,b,left,right) OP a,b;INT left,right;
/* AK 211100 */
{
    INT erg=OK,mitte,res;
    if (left > right) return -1;
    mitte = (left+right)/2;
    res = COMP(a,S_V_I(b,mitte));
    if (res == 0) return mitte;
    if (res < 0) 
        return index_vector_binary_co(a,b,left,mitte-1);
    else
        return index_vector_binary_co(a,b,mitte+1,right);
    ENDR("local:index_vector_binary_co");
}

INT index_vector_binary(a,b) OP a,b;
/* AK 211100 */
/* assumes sorted according to comp */
{
    return index_vector_binary_co(a,b,0,S_V_LI(b)-1);
}

INT insert_entry_vector(a,index,b) OP a,b; INT index;
/* AK 280607 */
/* new empty object add position index */
{
    INT erg = OK;
    SYMCHECK(not VECTORP(a),"insert_entry_vector(1): not VECTORP");
    {
    INT i,j;
    if (a == b) 
        {
        OP c;
	c = CALLOCOBJECT();
        *c = *b;
        C_O_K(b,EMPTY);
        erg += insert_entry_vector(c,index,b);
        FREEALL(c);
        goto endr_ende;
        }
    if (index<0) erg += copy(a,b);
    else if (index>=S_V_LI(a)) erg += copy(a,b);
    else {
	    erg += m_il_v(S_V_LI(a)+1,b);
	    C_O_K(b,S_O_K(a));
	    for (i=0;i<index;i++)
		{
		COPY(S_V_I(a,i),S_V_I(b,i));
		}
            for (i=index;i<S_V_LI(a);i++)
		{
		COPY(S_V_I(a,i),S_V_I(b,i+1));
		}
          }
    }
    ENDR("insert_entry_vector");
}

INT delete_entry_vector(a,index,b) OP a,b; INT index;
/* AK 220296 */
/* AK 011098 V2.0 */
/* in the case of an index outside the vector, 
   no deletion , otherwise the vector shrinks */
/* AK 210804 V3.0 */
{
    INT erg = OK;
    SYMCHECK(not VECTORP(a),"delete_entry_vector(1): not VECTORP");
    {
    INT i,j;
    if (a == b) 
        {
/* old:211107
        OP c;
	c = CALLOCOBJECT();
        *c = *b;
        C_O_K(b,EMPTY);
        erg += delete_entry_vector(c,index,b);
        FREEALL(c);
*/
	if (index < 0) goto endr_ende;
	if (index >= S_V_LI(a)) goto endr_ende;
	FREESELF(S_V_I(a,index));
	DEC_INTEGER(S_V_L(a));
	if (index == S_V_LI(a)) goto endr_ende;

	for (i=index;i<S_V_LI(a);i++)
		SWAP(S_V_I(a,i),S_V_I(a,i+1));
        goto endr_ende;
        }
    erg += m_il_v(S_V_LI(a)-1,b);
    C_O_K(b,S_O_K(a));
    for (i=0,j=0;i<S_V_LI(b);i++)
        {
        if (j == index) j++;
        COPY(S_V_I(a,j),S_V_I(b,i));
        j++;
        }
    }
    ENDR("delete_entry_vector");
}

OP find_vector(a,b) OP a,b;
/* AK 010393 */
/* AK 011098 V2.0 */
/* null if a not in b */
{
    INT i = index_vector(a,b);
    if (i == (INT)-1)
        return NULL;
    else
        return S_V_I(b,i);
}


INT t_INTVECTOR_UCHAR(a,b) OP a; char **b;
/* AK 011098 V2.0 */
{
    INT i;
    INT erg = OK;
    CTO(INTEGERVECTOR,"t_INTVECTOR_UCHAR(1)",a);
    *b = SYM_MALLOC((int) S_V_LI(a)+1);
    SYMCHECK( (*b) == NULL,"t_INTVECTOR_UCHAR:no memory");

    (*b)[0]=(unsigned char) S_V_LI(a);
    for (i=(INT)1;i<=S_V_LI(a);i++)
        (*b)[i] = (unsigned char) S_V_II(a,i-(INT)1);
    ENDR("t_INTVECTOR_UCHAR");
}
INT t_UCHAR_INTVECTOR(a,b) OP b; char *a;
/* AK 011098 V2.0 */
{
    INT erg = OK;
    INT i;
    COP("t_UCHAR_INTVECTOR(1)",a);
    COP("t_UCHAR_INTVECTOR(2)",b);

    erg += m_il_v((INT)a[0],b);
    for (i=(INT)0;i<S_V_LI(b);i++)
        M_I_I(a[i+1], S_V_I(b,i));
    ENDR("t_UCHAR_INTVECTOR");
}

INT comp_numeric_vector(a,b) OP a,b;
/* AK 020893 */
/* AK 011098 V2.0 */
{
    INT i,m,erg=OK;
    OP c;
    if (not VECTORP(a) || not VECTORP(b))
            {
            WTT("comp_numeric_vector",a,b);
            goto endr_ende;
            }
    if (S_V_LI(a) > S_V_LI(b))   /* error wrong: < corrected AK 130199 */
        { c = a; a = b; b = c; m = (INT)-1; }
    else
        m = (INT)1;

    /* the vector a is the shorter one */

    for (i=(INT)0;i<S_V_LI(a);i++)
        if (S_O_K(S_V_I(a,i)) != INTEGER)
            return error("comp_numeric_vector:no INTEGER entry");
        else if (S_O_K(S_V_I(b,i)) != INTEGER)
            return error("comp_numeric_vector:no INTEGER entry");
        else if (S_V_II(a,i) < S_V_II(b,i))
            return m * (INT)-1;
        else if (S_V_II(a,i) > S_V_II(b,i))
            return m ;
    for (;i<S_V_LI(b);i++)
        if (S_O_K(S_V_I(b,i)) != INTEGER)
            return error("comp_numeric_vector:no INTEGER entry");
        else if (S_V_II(b,i) < (INT)0)
            return m ;
        else if (S_V_II(b,i) > (INT)0)
            return m * (INT)-1;
    return (INT)0;
    ENDR("comp_numeric_vector");
}

INT add_apply_integervector(a,b) OP a, b;
/* b = b+a */
/* AK 211289 V1.1 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT i,erg = OK;
    CTO(INTEGERVECTOR,"add_apply_integervector(1)",a);
    CTTO(INTEGERVECTOR,VECTOR,"add_apply_integervector(2)",b);

    if (S_V_LI(a) > S_V_LI(b))
    {
        i  = S_V_LI(b);
        inc_vector_co(b,S_V_LI(a) - S_V_LI(b));
        for (; i<S_V_LI(a); i++)
            M_I_I((INT)0,S_V_I(b,i));
    }
    if (S_O_K(b) == INTEGERVECTOR)
        {
        for (i=(INT)0;i<S_V_LI(b);i++)
            if     (i < S_V_LI(a))
            {
            erg += add_apply_integer_integer(S_V_I(a,i),S_V_I(b,i));
            if (not INTEGERP(S_V_I(b,i))) /* AK 310195 */
            C_O_K(b,VECTOR);
            }
            else
                break;
        }
    else
        {
        for (i=(INT)0;i<S_V_LI(b);i++)
            if     (i < S_V_LI(a))
                {
                if (INTEGERP(S_V_I(a,i)) && INTEGERP(S_V_I(b,i)))
                {
                erg += add_apply_integer_integer(S_V_I(a,i),S_V_I(b,i));
                if (not INTEGERP(S_V_I(b,i))) /* AK 310195 */
                    C_O_K(b,VECTOR);
                }
                else if (INTEGERP(S_V_I(a,i))) {
                    erg += add_apply(S_V_I(a,i),S_V_I(b,i));
                    C_O_K(b,VECTOR);
                    }
                else {
                    erg += add_apply(S_V_I(a,i),S_V_I(b,i));
                    C_O_K(a,VECTOR);
                if (not INTEGERP(S_V_I(b,i))) /* AK 310195 */
                C_O_K(b,VECTOR);
                           }
                }
            else break;
        }
    ENDR("add_apply_integervector");
}

INT copy_bitvector(vec,res) OP vec, res;
/* AK 180396 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"copy_bitvector(1)",vec);
    CTO(EMPTY,"copy_bitvector(2)",res);

    erg += m_il_bv(    S_V_LI(vec), res); /* length in bit */
    memcpy(S_V_S(res),S_V_S(vec), S_BV_LI(vec)); /* length in byte */
    C_O_K(res,S_O_K(vec));

    ENDR("copy_bitvector");
}

INT reverse_bitvector(vec,res) OP vec,res;
/* AK 090703 */
{
    INT erg = OK,i,j;
    CTO(BITVECTOR,"reverse_bitvector(1)",vec);
    CE2(vec,res,reverse_bitvector);

    erg += m_il_bv(    S_V_LI(vec), res); /* length in bit */
    C_O_K(res,S_O_K(vec));
    for (i=S_V_LI(vec)-1,j=0;i>=0;i--,j++)
        if (GET_BV_I(vec,i)==1)
            SET_BV_I(res,j);
        else
            UNSET_BV_I(res,j);

    ENDR("reverse_bitvector");
}

INT einsp_bitvector(vec) OP vec;
/* AK 200606
   all one vector ?
*/
{
    INT erg = OK,i;
    CTO(BITVECTOR,"einsp_bitvector(1)",vec);
	for (i=S_V_LI(vec)-1;i>=0;i--)
		if (GET_BV_I(vec,i)==0) return FALSE;
	return TRUE;
    ENDR("einsp_bitvector");
}


INT invers_bitvector(vec,res) OP vec,res;
/* AK 090703 */
/* the complement */
{
    INT erg = OK,i;
    CTO(BITVECTOR,"invers_bitvector(1)",vec);
    CE2(vec,res,invers_bitvector);

    erg += m_il_bv(    S_V_LI(vec), res); /* length in bit */
    C_O_K(res,S_O_K(vec));
    for (i=S_V_LI(vec)-1;i>=0;i--)
        if (GET_BV_I(vec,i)==1)
            UNSET_BV_I(res,i);
        else
            SET_BV_I(res,i);
    ENDR("invers_bitvector");
}



INT inc_bitvector(v) OP v;
/* AK 020698 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"inc_bitvector(1)",v);
    if ((S_V_LI(v) % 8) == 0) 
        {
        C_V_S(v, SYM_realloc(S_V_S(v), S_V_LI(v)/8 + 1));
        }
    INC_INTEGER(S_V_L(v));
    ENDR("inc_bitvector");
}

INT copy_integervector(vec,res) OP vec, res;
/* AK 021286 */ /* AK 280689 V1.0 */ /* AK 081289 V1.1 */
/* AK 120391 V1.2 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(INTEGERVECTOR,"copy_integervector(1)",vec);
    CTO(EMPTY,"copy_integervector(2)",res);

    erg += m_il_v(    S_V_LI(vec), res);
    memcpy(S_V_S(res),S_V_S(vec), S_V_LI(vec) * sizeof(struct object));
    C_O_K(res,S_O_K(vec));

    ENDR("copy_integervector");
}

INT copy_galois(vec,res) OP vec, res;
/* AK 211106 V3.1 */
{
    INT erg = OK;
    CTO(GALOISRING,"copy_galois(1)",vec);
    CTO(EMPTY,"copy_galois(2)",res);

    erg += m_il_v(    S_V_LI(vec), res);
    memcpy(S_V_S(res),S_V_S(vec), S_V_LI(vec) * sizeof(struct object));
    C_O_K(res,S_O_K(vec));

    ENDR("copy_integervector");
}


INT copy_composition(vec,res) OP vec, res;
/* AK 070102 */
/* identic to copy_integervector */
{
    INT erg = OK;
    CTO(COMPOSITION,"copy_composition(1)",vec);
    CTO(EMPTY,"copy_composition(2)",res);
 
    erg += m_il_v(    S_V_LI(vec), res);
    memcpy(S_V_S(res),S_V_S(vec), S_V_LI(vec) * sizeof(struct object));
    C_O_K(res,S_O_K(vec));
 
    ENDR("copy_composition");
}



INT comp_colex_vector(a,b) OP a,b;
/* a,b vectors colex order */
/* AK V1.1 151189 */ /* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
        INT i = S_V_LI(a)-1;
        INT j = S_V_LI(b)-1;
        INT erg;

        if (not VECTORP(a))
                error("comp_colex_vector:kind != VECTOR");
        if (not VECTORP(b))
                error("comp_colex_vector:kind != VECTOR");


        for (;(i >= (INT)0) || (j>=(INT)0); i--,j--)
        {
                if (i<(INT)0) return((INT)1);
                if (j<(INT)0) return((INT)-1);
                erg = comp(S_V_I(a,i),S_V_I(b,j));
                if (erg <(INT)0) return((INT)1);
                if (erg >(INT)0) return((INT)-1);
        }
        return((INT)0);
}




/* laenge in byte */
INT unset_bv_i(a,i) OP a; INT i;
/* ite bit auf 0 setzen */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"unset_bv_i",a);
    if (S_V_LI(a) < i)
        return error("unset_bv_i: index to big");
    if (i< 0)
        return error("unset_bv_i: index negativ");
    *((unsigned char *)S_V_S(a)  + (i/8))  &= (~(1 << (i%8)));

    ENDR("unset_bv_i");
}
INT set_bv_i(a,i) OP a; INT i;
/* ite bit setzen */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"set_bv_i",a);
    if (S_V_LI(a) < i)
        return error("set_bv_i: index to big");
    if (i< 0)
        return error("set_bv_i: index negativ");
    *((unsigned char *)S_V_S(a)  + (i/8))  |= (1 << (i%8));

    ENDR("set_bv_i");
}
INT get_bv_i(a,i) OP a; INT i;
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(BITVECTOR,"set_bv_i",a);
    if (S_V_LI(a) < i)
        return error("set_bv_i: index to big");
    if (i< 0)
        return error("set_bv_i: index negativ");
    return (*(((unsigned char *)S_V_S(a) ) + i/8)  >> (i%8))%2;
    ENDR("get_bv_i");
    
}


INT fprint_bitvector(fp,a) OP a; FILE *fp;
/* AK 011098 V2.0 */
{
    INT i,erg = OK;
    CTO(BITVECTOR,"fprint_bitvector",a);
    for (i=0;i<S_V_LI(a);i++)
        {
        fprintf(fp,"%d",GET_BV_I(a,i));
        if (fp == stdout)
            {
            zeilenposition ++;
            if (zeilenposition > 70)
                {
                printf("\n");
                zeilenposition = 0;
                }
            }
        }
    ENDR("fprint_bitvector");
}


INT t_INTVECTOR_BITVECTOR(a,b) OP a,b;
/* AK 011098 V2.0 */
/* a and b may be equal */
{
    INT erg = OK;
    INT i,l;
    if (not VECTORP(a))
        {
        WTO("t_INTVECTOR_BITVECTOR",a);
        goto endr_ende;
        }
    CE2(a,b,t_INTVECTOR_BITVECTOR);
    /* a is INTVECTOR object */
    l =  S_V_LI(a);
    erg += m_il_bv(l,b);

    for (i=0;i<S_V_LI(b);i++)
        if ((S_V_II(a,i)%2) == 0)
            UNSET_BV_I(b,i);
        else
            SET_BV_I(b,i);

    ENDR("t_INTVECTOR_BITVECTOR");
}

INT nullp_bitvector(bit) OP bit;
/* AK 011098 V2.0 */
{
    unsigned char *self;
    INT l,i;
    self = (unsigned char *) S_V_S(bit);
    l =  S_V_LI(bit);
    for (i=0;i<= (l/8);i++)
        if (self[i] != 0) return FALSE;
    return TRUE;
}

INT sup_bitvector(bit1, bit2, res) OP bit1,bit2,res;
/* AK 011098 V2.0 */
{
    unsigned char  *self, *bs1, *bs2;
    INT erg = OK;
    INT i,l;
    CTO(BITVECTOR,"sup_bitvector(1)",bit1);
    CTO(BITVECTOR,"sup_bitvector(2)",bit2);
    if (S_V_LI(bit1) != S_V_LI(bit2))
        error("sup_bitvector:diff lengths");
    l =  S_V_LI(bit1);
    bs1 = (unsigned char *) S_V_S(bit1);
    bs2 = (unsigned char *) S_V_S(bit2);
    self = (unsigned char  *)SYM_calloc(l/8+1,8);
    for (i=0;i<= (l/8);i++)
        self[i] = bs1[i] | bs2[i];
    B_LS_V(callocobject(),self,res);
    M_I_I(l,S_V_L(res));
    C_O_K(res,BITVECTOR);
    ENDR("sup_bitvector");
}

INT inf_bitvector(bit1, bit2, res) OP bit1,bit2,res;
/* AK 011098 V2.0 */
{
    unsigned char  *self, *bs1, *bs2;
    INT erg = OK;
    INT i,l;
    CTO(BITVECTOR,"inf_bitvector(1)",bit1);
    CTO(BITVECTOR,"inf_bitvector(2)",bit2);
    if (S_V_LI(bit1) != S_V_LI(bit2))
        error("inf_bitvector:diff lengths");
    l =  S_V_LI(bit1);
    bs1 = (unsigned char *) S_V_S(bit1);
    bs2 = (unsigned char *) S_V_S(bit2);
    self = (unsigned char  *)SYM_calloc(l/8+1,8);
    for (i=0;i<= (l/8);i++)
        self[i] = bs1[i] & bs2[i];
    B_LS_V(callocobject(),self,res);
    M_I_I(l,S_V_L(res));
    C_O_K(res,BITVECTOR);
    ENDR("inf_bitvector");
}

INT exor_bitvector_apply(bit1,  res) OP bit1,res;
/* AK 011098 V2.0 */
{
    unsigned char  *bs1, *bs2;
    INT erg = OK;
    INT i,l;
    CTO(BITVECTOR,"exor_bitvector_apply(1)",bit1);
    CTO(BITVECTOR,"exor_bitvector_apply(2)",res);
    if (S_V_LI(bit1) != S_V_LI(res))
        error("exor_bitvector_apply:diff lengths");
    l =  S_V_LI(bit1);
    bs1 = (unsigned char *) S_V_S(bit1);
    bs2 = (unsigned char *) S_V_S(res);
    for (i=l/8;i>=0;i--)
        bs2[i] ^= bs1[i] ;
    ENDR("exor_bitvector_apply");
}



INT inf_bitvector_apply(bit1,  res) OP bit1,res;
/* AK 011098 V2.0 */
{
    unsigned char  *bs1, *bs2;
    INT erg = OK;
    INT i,l;
    CTO(BITVECTOR,"inf_bitvector_apply(1)",bit1);
    CTO(BITVECTOR,"inf_bitvector_apply(2)",res);

    if (S_V_LI(bit1) != S_V_LI(res))
        error("inf_bitvector_apply:diff lengths");
    l =  S_V_LI(bit1);
    bs1 = (unsigned char *) S_V_S(bit1);
    bs2 = (unsigned char *) S_V_S(res);
    for (i=0;i<= (l/8);i++)
        bs2[i] &= bs1[i] ;
    ENDR("inf_bitvector_apply");
}

INT sup_bitvector_apply(bit1,  res) OP bit1,res;
/* AK 200606 V2.0 */
{
    unsigned char  *bs1, *bs2;
    INT erg = OK;
    INT i,l;
    CTO(BITVECTOR,"sup_bitvector_apply(1)",bit1);
    CTO(BITVECTOR,"sup_bitvector_apply(2)",res);

    if (S_V_LI(bit1) != S_V_LI(res))
        error("sup_bitvector_apply:diff lengths");
    l =  S_V_LI(bit1);
    bs1 = (unsigned char *) S_V_S(bit1);
    bs2 = (unsigned char *) S_V_S(res);
    for (i=0;i<= (l/8);i++)
        bs2[i] |= bs1[i] ;
    ENDR("sup_bitvector_apply");
}




INT t_BITVECTOR_INTVECTOR(a,b) OP a,b;
/* AK 011098 V2.0 */
{
    unsigned char  *self;
    INT i,j,k;
    if (a == b)
        return ERROR;
    /* a is INTVECTOR object */
    self = (unsigned char  *) S_V_S(a);
    m_il_v(S_V_LI(a),b);
    for (i=0,j=0,k=1;i<S_V_LI(b);i++,k*=2 )
        {
        if (k==256) { j ++; k = 1;}
        if (self[j] & k) 
            M_I_I((INT)1,S_V_I(b,i));
        else 
            M_I_I((INT)0,S_V_I(b,i));
        }
    C_O_K(b,INTEGERVECTOR);
    return OK;
}

INT t_VECTOR_BIT(a,b) OP a,b;
/* AK 091294 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    INT il=0,i,j= -1,k=0;
    unsigned char *self;
    CTO(PARTITION,"t_VECTOR_BIT(1)",a);
    if (S_PA_K(a) != VECTOR)
        {
        erg += error("t_VECTOR_BIT input no VECTOR kind PARTITION object");
        goto endr_ende;
        }
    CE2(a,b,t_VECTOR_BIT);
    
    if (S_PA_LI(a) > 0)
        il = S_PA_LI(a) + S_PA_II(a,S_PA_LI(a)-(INT)1); 
        /* laenge des bit vectors i n bit */

    erg += b_ks_pa(BITVECTOR,callocobject(),b);
    B_LS_V(callocobject(),NULL,S_PA_S(b));
    M_I_I(il,S_PA_L(b));
    C_O_K(S_PA_S(b),BITVECTOR);
    if (il == 0) goto endr_ende;

    self = (unsigned char *) SYM_calloc(il/64+1,8);
    C_V_S(S_PA_S(b),self);
    
    for  (i=(INT)0,j=S_PA_LI(a)-1,k=S_PA_II(a,S_PA_LI(a)-1);i<il;i++)
        {
        if (j== -1) /* nur noch einsen */
            {
            SET_BV_I(S_PA_S(b),i);
            k--;
            }
        else if (k > S_PA_II(a,j))
            {
                        SET_BV_I(S_PA_S(b),i);
                        k--;
            }
        else     {
            j--;
            }
        }
    C_PA_K(b,BITVECTOR);
    if (k != 0)
        return error("t_VECTOR_BIT: internal error tVB-0");
    if (j != -1)
        return error("t_VECTOR_BIT: internal error tVB-1");
    ENDR("t_VECTOR_BIT");
}

static INT maxpart_bitvector_part_i(a) OP a;
/* AK 011098 V2.0 */
{
    INT i,j=0;
    for (i=0;i<=S_V_LI(a);i++)
        {
        if (GET_BV_I(a,i) != (INT)1) break;
        }
    /* d.h. i ist die 0 */
    for (;i<=S_V_LI(a);i++)
        if (GET_BV_I(a,i) == (INT)1) j++;
    return j;
    /* maximaler teil */
}

static INT length_bitvector_part_i(a) OP a;
/* AK 011098 V2.0 */
{
    INT i,j=0,k;
    for (i=S_V_LI(a)-1;i>=0;i--)
        {
        if ((k=GET_BV_I(a,i)) != (INT)0) break;
        }
    /* d.h. i ist die letzte 1 */
    for (k=(INT)0;k<i;k++)
        if (GET_BV_I(a,k) == (INT)0) j++;
    return j;
}

INT t_BIT_VECTOR(a,b) OP a,b;
/* AK 121294 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    INT il, i,j,k;
    CTO(PARTITION,"t_BIT_VECTOR(1)",a);

    if (S_PA_K(a) != BITVECTOR)
        return error("t_BIT_VECTOR input no BITVECTOR kind PARTITION object");
    if (check_equal_2(a,b,t_BIT_VECTOR,&erg) == EQUAL)
                return erg;

    il = length_bitvector_part_i(S_PA_S(a)); /* Anzahl teile */

    b_ks_pa(VECTOR,callocobject(),b);
    m_il_integervector(il,S_PA_S(b));
    j=0;k=0;
    for (i=S_PA_LI(a)-1;i>=0;i--)
        {
        if(GET_BV_I(S_PA_S(a),i) == 1) break;
        }
    for (;k<il;i--)
        if (GET_BV_I(S_PA_S(a),i) == 1) 
            j++;
        else
            {
            M_I_I(j,S_PA_I(b,k));
            k++;
            }
    ENDR("t_BIT_VECTOR");
}

static INT dimension_bit_co();
INT dimension_bit(a,b) OP a,b;
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTO(PARTITION,"dimension_bit",a);
        if (S_PA_K(a) != BITVECTOR)
        {
        erg += error("dimension_bit input no BITVECTOR kind PARTITION object");
        goto endr_ende;
        }
    CE2(a,b,dimension_bit);
    m_i_i((INT)0,b);
    println(a);
    erg += dimension_bit_co(S_PA_S(a),b,(INT)1);
    println(b);
    ENDR("dimension_bit");
}

static INT dimension_bit_co(a,b,sig) OP a,b; INT sig;
/* AK 141294 */
{
    INT nu,is,i,il,j,jo=0,k,l,erg=OK;
    OP c,d;
    CTO(BITVECTOR,"dimension_bit_co(1)",a);
    CTTO(INTEGER,LONGINT,"dimension_bit_co(2)",b);
                
    il = length_bitvector_part_i(a);
    is = maxpart_bitvector_part_i(a);
    c = callocobject();
    d = callocobject();
    erg += m_il_v(is,c);
    C_O_K(c,INTEGERVECTOR);
    M_I_I((INT)1,d);
    j=0;k=0;
        for (i=S_V_LI(a)-1;i>=0;i--)
                {
                if(GET_BV_I(a,i) == 1) break;
                }
    /* hier geht die partition los */
    nu = 0;
        for (;k<il;i--)
                if (GET_BV_I(a,i) == 1)
                        j++;
                else
                        {
            if (k==0)
                {
                for (l=0;l<j;l++)
                    M_I_I(j-l,S_V_I(c,l));
                nu += j;
                jo = j;
                }
            else {
                for (l=0;l<jo;l++)
                    {
                    MULT_APPLY_INTEGER(S_V_I(c,l),d);
                    M_I_I(S_V_II(c,l)+1+j-jo, S_V_I(c,l));
                    }
                for (;l<j;l++)
                    M_I_I(j-l,S_V_I(c,l));
                nu += j;
                jo = j;
                 }
                        k++;
                        }

    k=0;
    for (i=(INT)0;i<jo;i++)
        MULT_APPLY_INTEGER(S_V_I(c,i),d);    
    erg += freeself(c);
    M_I_I(nu,c);
    erg += fakul(c,c);
    erg += ganzdiv(c,d,c);
    if (sig == (INT)1)
        ADD_APPLY(c,b);
    else
        sub(b,c,b);
    FREEALL(c);
    FREEALL(d);
    ENDR("internal routine:dimension_bit_co");
}

INT charvalue_bit (a,b,scv) OP a,b,scv;
/* AK 011098 V2.0 */
{
    INT erg = OK;
    if (S_O_K(a) != PARTITION)
        if (S_PA_K(a) != BITVECTOR)
            return ERROR;
    if (S_O_K(b) != PARTITION)
        if (S_PA_K(b) != VECTOR)
            return ERROR;

    FREESELF(scv); M_I_I(0,scv);
    erg += charvalue_bit_co(S_PA_S(a),S_PA_S(b),scv,S_PA_LI(b)-(INT)1,(INT)1);
    ENDR("charvalue_bit");
}

static INT charvalue_bit_co(a,b,c,index,sig) 
    OP a,b,c;
    register INT index,sig; 
{ 
    INT i,j,k,l,lh,hakenlaenge, ol; 
    unsigned char *uc,*uch;

    if ((S_V_II(b,index) == (INT)1) 
        &&
        (index >= 6) 
    )        
            {
            dimension_bit_co(a,c,sig);
            return OK;
            }

    i=S_V_LI(a)-1;
    uc = ((unsigned char *) S_V_S(a)) + (i/8); 
    l = i%8;
    for (;i>=0;i--,l--)
        {
        if (l < 0) {l+=8;uc--;}
        if (GET_BV_I(a,i) != 0) break; 
        /* if (GET_BIT_I(uc,l) != 0) break; */
        }
    ol = S_V_LI(a);
    M_I_I(i+1,S_V_L(a));
    /* i index erster wagrechter eintrag */
    hakenlaenge = S_V_II(b,index); 
    uch = ((unsigned char *) S_V_S(a)) + ((i-hakenlaenge)/8); 
    lh = (i-hakenlaenge)%8;
    for (;i>=hakenlaenge;i--,l--,lh--)
        {
        if (l < 0) {l+=8;uc--;} 
        if (lh < 0) {lh+=8;uch--;} 
        if (GET_BV_I(a,i) != 1) continue; 
        /* if (GET_BIT_I(uc,l) != 1) continue; */
        if (GET_BV_I(a,i-hakenlaenge) != 0) continue; 
        /* if (GET_BIT_I(uch,lh) != 0) continue; */
        k = 0;
        for (j=i-1;j>i-hakenlaenge;j--)
            if (GET_BV_I(a,j) == 0) k++;

        /* k is leglength */
        if (index == (INT)0)
            {
            if (k%2 == 1) sig *= -1;
            if (sig==1) inc(c); else dec(c);
            goto ende;
            }

        UNSET_BV_I(a,i); 
        /* UNSET_BIT_I(uc,l);*/
        SET_BV_I(a,i-hakenlaenge); 
        /*SET_BIT_I(uch,lh);*/
        if (k%2 == 0)
            charvalue_bit_co(a,b,c,index-1,sig);
        else 
            charvalue_bit_co(a,b,c,index-1,sig* ((INT)-1));
         SET_BV_I(a,i); 
        /*SET_BIT_I(uc,l);*/
         UNSET_BV_I(a,i-hakenlaenge); 
        /*UNSET_BIT_I(uch,lh);*/
        }
ende:
    M_I_I(ol,S_V_L(a));
    return OK;
}

INT next_lex_vector(a,b) OP a,b;
/* AK 060802 */
/* computes the next vector */
/* a and b may be equal */
/* return TRUE if there was a lexicoigraphic next vector
          FALSE if it is already the biggest one */
{
    INT erg = OK;
    INT i,j,k;
    OP m;
    CTTO(INTEGERVECTOR,VECTOR,"next_lex_vector(1)",a);
    if (a != b) erg += copy(a,b);
    if (S_V_LI(b) <= 1) return FALSE;
    /* vector has length >= 1 */
     
    /* to left till decrease */
    for (i=S_V_LI(b)-2;i>=0;i--)
         if (LT(S_V_I(b,i),S_V_I(b,i+1))) break;
     
     
    if (i==-1) return FALSE;
     
    k = i+1;
    for (j=i+1;j<S_V_LI(b);j++)
        if (LT(S_V_I(b,j),S_V_I(b,k)) && GT(S_V_I(b,j),S_V_I(b,i))) k=j;
    /* exchange elements at i and k */
    swap(S_V_I(b,k),S_V_I(b,i));
    /* sort remain part from i+1 */
    m = S_V_S(b);
    j = S_V_LI(b);
    C_V_S(b,S_V_I(b,i+1));
    M_I_I(j-i-1,S_V_L(b));
    qsort_vector(b);
    C_V_S(b,m);
    M_I_I(j,S_V_L(b));
     
    return TRUE;
    ENDR("next_lex_vector");
}                                                                                                        

INT fprint_queue(fp,q) FILE *fp; OP q;
/* AK 251103 */
{
    fprint_vector(fp,q);
    return OK;
}

INT init_queue(q) OP q;
/* AK 251103 */
{
    INT erg = OK;
    m_il_v(0,q);C_O_K(q,QUEUE);
    ENDR("init_queue");
}

INT push(a,q) OP a,q;
/* AK 251103 */
{
    INT erg =OK;
    C_O_K(q,VECTOR);
    inc(q);
    C_V_I(q,S_V_LI(q)-1,a);
    C_O_K(q,QUEUE);
    CTO(QUEUE,"push(e)",q);
    ENDR("push");
}

OP pop(q) OP q;
/* AK 251103 */
{
    OP z;
    INT i,erg =OK;
    CTO(QUEUE,"pop(1)",q);

    for (i=0;i<S_V_LI(q);i++)
    if (not EMPTYP(S_V_I(q,i))) { z=callocobject();*z = *S_V_I(q,i); 
             C_O_K(S_V_I(q,i),EMPTY);
             if (i>100) { INT j; /* AK 210104 */
                        for (j=0;i+j<S_V_LI(q);j++) *S_V_I(q,j)=*S_V_I(q,i+j);
                        M_I_I(j,S_V_L(q));
                        }
             return z; }

    return NULL;
    ENDO("pop");
}


    
#endif /* VECTORTRUE */
    
