#include "def.h"
#include "macro.h"

static INT hash1();
static INT eq1();
static OP lookup2=NULL;
static OP lookup1=NULL;

INT t_HASHTABLE_POLYNOM_apply();

INT hash_ende()
{
    INT erg = OK;
    if (lookup2 != NULL) {
        INT i;
        for (i=0;i<3;i++)
             C_O_K(S_V_I(lookup2,i),EMPTY);
        FREEALL(lookup2);
        lookup2=NULL;
        }
    if (lookup1 != NULL) {
        INT i;
        for (i=0;i<2;i++)
             C_O_K(S_V_I(lookup1,i),EMPTY);
        FREEALL(lookup1);
        lookup2=NULL;
        }
    ENDR("hash_ende");
}

INT copy_hashtable(a,b) OP a,b;
/* AK 011101 */
{
    INT erg = OK;
    INT i;
    OP ap,bp;
    CTO(HASHTABLE,"copy_hashtable(1)",a);
    CTO(EMPTY,"copy_hashtable(2)",b);

    erg += m_il_v(S_V_LI(a)+1,b);
    C_O_K(b,HASHTABLE);
    DEC_INTEGER(S_V_L(b));
    M_I_I(WEIGHT_HASHTABLE(a), S_V_I(b,S_V_LI(b)));

    for (ap=S_V_S(a), bp = S_V_S(b), i=S_V_LI(b); i>0 ;i--,ap++,bp++)
       {
       if (not EMPTYP(ap))
           erg += copy_vector(ap,bp);
       else
           C_I_I(bp,S_I_I(ap));
       }
    ENDR("copy_hashtable");
}

INT mem_size_hashtable(a) OP a;
/* AK 080903 */
{
    INT erg = OK, res = 0;
    CTO(HASHTABLE,"mem_size_hashtable(1)",a);
    res = mem_size_vector(a);
    res += sizeof(struct object); /* length of hashtable as appendix */
    return res;
    ENDR("mem_size_hashtable");
}

INT mult_apply_scalar_hashtable(a,b) OP a,b;
/* AK 171001 */
{
    INT erg = OK;
    OP z;

    CTO(HASHTABLE,"mult_apply_scalar_hashtable(1)",b);

    FORALL(z,b, {
        MULT_APPLY(a,z);
        } );

    CTO(HASHTABLE,"mult_apply_scalar_hashtable(1-end)",b);
    ENDR("mult_apply_scalar_hashtable");
}

INT mult_apply_integer_hashtable(a,b) OP a,b;
/* AK 171001 */
{
    INT erg = OK;
    OP z;
 
    CTO(HASHTABLE,"mult_apply_integer_hashtable(2)",b);
    CTO(INTEGER,"mult_apply_integer_hashtable(1)",a);
 
    FORALL(z,b, {
        MULT_APPLY_INTEGER(a,z);
        } );
 
    ENDR("mult_apply_integer_hashtable");
}

INT mult_integer_hashtable(a,b,c) OP a,b,c;
/* AK 310102 */
{
    INT erg = OK;
    OP z;
 
    CTO(HASHTABLE,"mult_integer_hashtable(2)",b);
    CTO(INTEGER,"mult_integer_hashtable(1)",a);
    CTO(EMPTY,"mult_integer_hashtable(3)",c);

    erg += copy_hashtable(b,c);
 
    FORALL(z,c, {
        MULT_APPLY_INTEGER(a,z);
        } );
 
    ENDR("mult_integer_hashtable");
}

INT mult_bruch_hashtable(a,b,c) OP a,b,c;
/* AK 310102 */
{
    INT erg = OK;
    OP z;
 
    CTO(HASHTABLE,"mult_bruch_hashtable(2)",b);
    CTO(BRUCH,"mult_bruch_hashtable(1)",a);
    CTO(EMPTY,"mult_bruch_hashtable(3)",c);
 
    erg += copy_hashtable(b,c);
 
    FORALL(z,c, {
        MULT_APPLY_BRUCH(a,z);
        } );
 
    ENDR("mult_bruch_hashtable");
}



INT mult_apply_bruch_hashtable(a,b) OP a,b;
/* AK 171001 */
{
    INT erg = OK;
    OP z;
 
    CTO(HASHTABLE,"mult_apply_bruch_hashtable(2)",b);
    CTO(BRUCH,"mult_apply_bruch_hashtable(1)",a);
 
    FORALL(z,b, {
        MULT_APPLY_BRUCH(a,z);
        } );
 
    ENDR("mult_apply_bruch_hashtable");
}



INT addinvers_apply_hashtable(a) OP a;
/* AK 231001 */
{
    INT erg = OK;
    OP z;
    CTO(HASHTABLE,"addinvers_apply_hashtable(1)",a);

    FORALL(z,a, {
        ADDINVERS_APPLY(z);
        } );

    ENDR("addinvers_apply_hashtable");
}


INT add_apply_hashtable(a,b,eh,ef,hf) OP a,b; INT (*ef)();INT (*hf)(); INT (*eh)();
/* AK 141101 */
/* first lookup a in b, if not yet here it inserts a copy, else
   it applys the eh function */
{
    INT erg = OK;
    OP z;
    CTO(HASHTABLE,"add_apply_hashtable(2)",b);
    z = find_hashtable(a,b,ef,hf);
    if (z == NULL) {
        OP m;
        m = CALLOCOBJECT();
        COPY(a,m);
        INSERT_HASHTABLE(m,b,eh,ef,hf);
        }
    else {
        if (eh == NULL) ;
        else if (eh == add_koeff) {
            ADD_KOEFF(a,z);
            if (EMPTYP(z))
                DEC_INTEGER(S_V_I(b,S_V_LI(b))); /* counter-- */
            }
        else {
            (*eh)(a,z);
            if (EMPTYP(z))
                DEC_INTEGER(S_V_I(b,S_V_LI(b))); /* counter-- */
            }
        }
    ENDR("add_apply_hashtable");
}


OP find_hashtable(a,b,ef,hf) OP a,b; INT (*ef)();INT (*hf)();
/* AK 281097 */
/* find a object in hashtable b */
/* return s NULL if not find, else returns OP pointer */
{
    OP z,z1;
    INT i,hi,hh,hhh;
    INT erg = OK;

    CTO(HASHTABLE,"find_hashtable(2)",b);
    if (hf == NULL) hf = hash;

    if (hf == hash_monompartition)
        hh = HASH_MONOMPARTITION(a);
    else if (hf == hash)
        hh = HASH(a);
    else if (hf == hash1) 
        hh = HASH(S_V_I(a,0));
    else 
        hh = (*hf)(a);

    hi = hh % S_V_LI(b);
    if (hi < 0) 
         hi += S_V_LI(b);
    
    
    z = S_V_I(b,hi);

    if (EMPTYP(z)) return NULL;

    for (i=0,z1 = S_V_S(z) ;i<S_V_LI(z);i++,z1++)
        if (not EMPTYP(z1)) 
            {
            if (hf == hash)
                hhh = HASH(z1);
            else if (hf == hash_monompartition)
                hhh = HASH_MONOMPARTITION(z1);
            else if (hf == hash1)
                hhh = HASH(S_V_I(z1,0));
            else
                hhh = (*hf)(z1);

            if (hh == hhh)
                {
                if (ef == NULL) 
                    hhh = EQ(a,z1);
                else if (ef == eq_monomsymfunc) 
                    hhh = eq_partition_partition(S_MO_S(a),S_MO_S(z1));
                else if (ef == eq1)
                    hhh = EQ(S_V_I(a,0),S_V_I(z1,0));
                else 
                    hhh = (*ef)(a,z1);

                if (hhh == TRUE) return z1;
                }
            }

    return NULL;
    ENDO("find_hashtable");
}


INT fprint_hashtable(f,h) FILE *f; OP h;
/* AK 131101 */
{
    INT erg = OK;
    OP z;
    COP("fprint_hashtable(1)",f);
    CTO(HASHTABLE,"fprint_hashtable(2)",h);

    fprintf(f,"s=");
    erg += fprint(f,S_V_I(h,S_V_LI(h)));
    fprintf(f," ");
    if (f == stdout) zeilenposition += 3;

    FORALL(z,h, {
        fprint(f,z); fprintf(f," ");
        if (f == stdout) zeilenposition ++;
        });
    ENDR("fprint_hashtable");
}

INT objectread_hashtable(fp, h) FILE *fp; OP h;
/* AK 100307 */
{
	INT erg = OK,i,j=-1,k;
	erg += objectread_vector(fp,h);
	/* next pointer update */
	M_I_I(S_V_LI(h)-1,S_V_L(h));
	for (i=0;i<S_V_LI(h);i++)
		{
		if (S_O_K(S_V_I(h,i))  == VECTOR)
			{
			for (j++;j<i;j++)
				C_I_I(S_V_I(h,j),i);
			}
		}
	// printf("j=%d i=%d\n",j,i);
	for (j++;j<i;j++)
		C_I_I(S_V_I(h,j),-1);
	M_I_I(S_V_LI(h)+1,S_V_L(h));
/*
	for (i=0;i<S_V_LI(h);i++) if (not EMPTYP(S_V_I(h,i))) println(S_V_I(h,i));
				  else printf("%d\n",S_V_II(h,i));
*/
	M_I_I(S_V_LI(h)-1,S_V_L(h));
	C_O_K(h,HASHTABLE);
	// println(h);
	ENDR("objectread_hashtable");
}

INT objectwrite_hashtable(fp, h) FILE *fp; OP h;
/* AK 100307 */
{
        INT erg = OK;
        M_I_I(S_V_LI(h)+1,S_V_L(h));
        erg += objectwrite_vector(fp,h);
        M_I_I(S_V_LI(h)-1,S_V_L(h));
        ENDR("objectread_hashtable");
}



#define INIT_HASH_TABLE_SIZE(a,i)\
do { \
    INT ihts_i; OP ihts_z;\
    erg += m_il_v(i+1,a);\
    M_I_I(i,S_V_L(a));\
    C_O_K(a,HASHTABLE);\
    for (ihts_i=0,ihts_z=S_V_S(a);ihts_i<i;ihts_i++,ihts_z++) \
        { ihts_z->ob_self.ob_INT  = -1; }\
    M_I_I(0,S_V_I(a,i)); \
} while(0)

INT init_hashtable(a) OP a;
/* AK 281097 */
/* initialize a hashtable */
    {
    INT erg = OK;
    CTO(EMPTY,"init_hashtable(1)",a);
    INIT_HASH_TABLE_SIZE(a,1009);
    ENDR("init_hashtable");
    }


INT init_size_hashtable(a,b) OP a; INT b;
    {
    OP c;
    INT erg = OK;
    SYMCHECK( b < 1, "non positive size in init_size_hashtable(2)");

    NEW_INTEGER(c,b);
    while (not primep(c)) INC_INTEGER(c);
    INIT_HASH_TABLE_SIZE(a,S_I_I(c));
    FREEALL(c);
    ENDR("init_size_hashtable");
    }

INT clone_size_hashtable(a,b) OP a; INT b;
    {
    INT erg = OK;
    CTO(EMPTY,"clone_size_hashtable(1)",a);
    CTO(INTTYPE,"clone_size_hashtable(2)",b);
    INIT_HASH_TABLE_SIZE(a,b);
    ENDR("clone_size_hashtable");
    }



INT insert_hashtable_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
{
    INT erg = OK;
    OP z;
    CTO(HASHTABLE,"insert_hashtable_hashtable(1)",a);
    CTO(HASHTABLE,"insert_hashtable_hashtable(2)",b);

    FORALL(z,a, {
        OP f;
        f = CALLOCOBJECT();
        SWAP(z,f);
        insert_scalar_hashtable(f,b,eh , cf,hf);
        } );

    M_I_I(0,S_V_I(a,S_V_LI(a)));
    FREEALL(a);
    ENDR("insert_hashtable_hashtable");
}

#define INSERT_SF_HASHTABLE(a,b,eh , cf,hf)\
do {OP z; \
    z = a;\
    if (S_L_S(z) != NULL)\
    while (z!= NULL)\
        {\
        erg +=  insert_scalar_hashtable(S_L_S(z), b,eh , cf,hf);\
        C_L_S(z,NULL);\
        z = S_L_N(z);\
        }\
    FREEALL(a); \
    } while(0)

INT insert_monomial_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 131101 */
{
    INT erg = OK;
    CTO(MONOMIAL,"insert_monomial_hashtable(1)",a);
    CTO(HASHTABLE,"insert_monomial_hashtable(2)",b);
    INSERT_SF_HASHTABLE(a,b,eh , cf,hf);
    ENDR("insert_monomial_hashtable");
}

INT insert_schur_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 131101 */
{
    INT erg = OK;
    CTO(SCHUR,"insert_schur_hashtable(1)",a);
    CTO(HASHTABLE,"insert_schur_hashtable(2)",b);
    INSERT_SF_HASHTABLE(a,b,eh , cf,hf);
    ENDR("insert_schur_hashtable");
}

INT insert_homsym_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 131101 */
{
    INT erg = OK;
    CTO(HOMSYM,"insert_homsym_hashtable(1)",a);
    CTO(HASHTABLE,"insert_homsym_hashtable(2)",b);
    INSERT_SF_HASHTABLE(a,b,eh , cf,hf);
    ENDR("insert_homsym_hashtable");
}
 
INT insert_powsym_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 131101 */
{
    INT erg = OK;
    CTO(POWSYM,"insert_powsym_hashtable(1)",a);
    CTO(HASHTABLE,"insert_powsym_hashtable(2)",b);
    INSERT_SF_HASHTABLE(a,b,eh , cf,hf);
    ENDR("insert_powsym_hashtable");
}

INT insert_elmsym_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 131101 */
{
    INT erg = OK;
    CTO(ELMSYM,"insert_elmsym_hashtable(1)",a);
    CTO(HASHTABLE,"insert_elmsym_hashtable(2)",b);
    INSERT_SF_HASHTABLE(a,b,eh , cf,hf);
    ENDR("insert_elmsym_hashtable");
}
 


INT insert_hashtable(a,b,eh , cf,hf) OP a,b; INT (*eh)(), (*cf)(), (*hf)();
/* AK 281097 */
/* insert into a hashtable */
/* AK 131101 */
{
    INT erg = OK;
    CTO(HASHTABLE,"insert_hashtable(2)",b);

    if (S_O_K(a) == HASHTABLE)
        erg += insert_hashtable_hashtable(a,b,eh,cf,hf);
    else if (S_O_K(a) == MONOMIAL)
        erg += insert_monomial_hashtable(a,b,eh,cf,hf);
    else if (S_O_K(a) == SCHUR)
        erg += insert_schur_hashtable(a,b,eh,cf,hf);
    else if (S_O_K(a) == ELMSYM)
        erg += insert_elmsym_hashtable(a,b,eh,cf,hf);
    else if (S_O_K(a) == HOMSYM)
        erg += insert_homsym_hashtable(a,b,eh,cf,hf);
    else if (S_O_K(a) == POWSYM)
        erg += insert_powsym_hashtable(a,b,eh,cf,hf);
    else 
        erg += insert_scalar_hashtable(a,b,eh,cf,hf);
        
    ENDR("insert_hashtable");
}

INT insert_scalar_hashtable(a,b,eh,ef,hf)  OP a,b; INT (*eh)(), (*ef)(), (*hf)();
/* AK 281097 */
/* AK 131101 */
{
    INT i,index,freeindex=-1,hv,hvv;
    INT erg = OK;
    OP z,zz;

    COP("insert_scalar_hashtable(1)",a);
    CTO(HASHTABLE,"insert_scalar_hashtable(2)",b);
    /* einfach einfuegen */
    

    if (hf == NULL) hf = hash;
    if (hf == hash)
        hv = HASH(a);
    else if (hf == hash_monompartition)
        hv = HASH_MONOMPARTITION(a);
    else
        hv =  (*hf)(a);
    index = hv % S_V_LI(b);

    if (index < 0) index += S_V_LI(b);
    z = S_V_I(b,index);

    if (EMPTYP(z))
        {
        B_O_V(a,z);
        INC_INTEGER(S_V_I(b,S_V_LI(b))); /* counter++ */
        for (zz=S_V_I(b,index-1),i=index-1; i>=0; i--,zz--)
            if (EMPTYP(zz)) S_O_S(zz).ob_INT=index;
            else break;
        }
    else    {
        /* collision test */
        if (ef == NULL) ef = eq;
        for (zz= S_V_I(z,S_V_LI(z)-1),i=S_V_LI(z)-1;i>=0;i--,zz--)
            {
            if (EMPTYP(zz)) 
                freeindex = i;
            else {
                 if (hf == hash)
                     hvv=HASH(zz);
                 else if (hf == hash_monompartition)
                     hvv=HASH_MONOMPARTITION(zz);
                 else
                     hvv=(*hf)(zz);
                 if ( 
                     (hv == hvv) 
                     && 
                     ((*ef)(a,zz) == TRUE)
                    )
                    {
                    /* there is a collision */
                    if (eh != NULL) {
                         if (eh == add_koeff) {ADD_KOEFF(a,zz);}
                         else (*eh)(a,zz);
                         FREEALL(a);
                         if (EMPTYP(zz))
                            DEC_INTEGER(S_V_I(b,S_V_LI(b))); /* counter-- */
                         }
                    else
                        { FREEALL(a); }
                    goto ende;
                    }
                }
            }
        /* nicht da */
        if (freeindex < 0) { freeindex = S_V_LI(z); inc_vector_co(z,3); }

            
        INC_INTEGER(S_V_I(b,S_V_LI(b))); /* counter++ */
        SWAP(a,S_V_I(z,freeindex));
        FREEALL(a);
        }

    /* AK 240901 */
    /* if the table is full, i.e. number of entires > length
       increase the size by factor 2 */
    if ( 
        (S_V_LI(b) < WEIGHT_HASHTABLE(b))
       )
        erg += double_hashtable(b,hf);

ende:
    ENDR("insert_scalar_hashtable");
    }

#ifdef UNDEF
    INT double_hashtable_pre091101(b,hf) OP b; INT (*hf)();
{
    INT erg = OK;
    OP d;
    CTO(HASHTABLE,"double_hashtable(1)",b);
    d = CALLOCOBJECT();
    SWAP(b,d);
    erg += init_size_hashtable(b,S_V_LI(d)*2);
    insert_hashtable_hashtable(d,b,NULL,NULL,hf);
    ENDR("double_hashtable");
}
#endif

INT print_stat_hashtable(a) OP a;
/* AK 0602002 */
{
    INT i;
    printf("entries = %ld size = %ld\n",S_V_II(a,S_V_LI(a)),S_V_LI(a));
    printf("entires per slot (>1 == collision)\n");
    for (i=0;i<S_V_LI(a);i++)
        printf(" %ld ",(EMPTYP(S_V_I(a,i)) ? -S_V_II(a,i) : S_V_LI(S_V_I(a,i)) ) );
    printf("\n");
    return OK;
}

INT double_hashtable(b,hf) OP b; INT (*hf)();
{
    INT erg = OK;
    INT i,l,j,hh,index,k;
    OP z;
    CTO(HASHTABLE,"double_hashtable(1)",b);
    l = S_V_LI(b);
    i = S_V_II(b,l);
    C_O_K(S_V_I(b,l),EMPTY);
    inc_vector_co(b,l+1);
    M_I_I(S_V_LI(b)-1,S_V_L(b));
    

    M_I_I(i,S_V_I(b,S_V_LI(b)));
    /* die anzahl der eintraege ist o.k. */

    for (i=l-1;i>=0;i--)
        {
        if (not EMPTYP(S_V_I(b,i)))
            {
            z = S_V_I(b,i);
            for (j=0;j<S_V_LI(z);j++)
                if (not EMPTYP(S_V_I(z,j)))
                    {
                    /* schauen ob der eintrag in die zweite haelfte muss */
                    if (hf == hash_monompartition) 
                        hh = HASH_MONOMPARTITION(S_V_I(z,j));
                    else if (hf == hash)
		        hh = HASH(S_V_I(z,j));
                    else
                        hh = (*hf)(S_V_I(z,j));
                    index = hh % S_V_LI(b);
                    if (index < 0) index += S_V_LI(b);
                    if (index == i) ;
                    else if (index == (i+l) ) 
                        {
                        /* muss in die zweite haelfte */
                        if (EMPTYP(S_V_I(b,index))) { 
                            erg += m_il_v(1,S_V_I(b,index));
                            SWAP(S_V_I(z,j), S_V_I(S_V_I(b,index),0));
                            }
                        else {
                            inc_vector_co(S_V_I(b,index),1);
                            SWAP(S_V_I(z,j), S_V_I(S_V_I(b,index),S_V_LI(S_V_I(b,index))-1 ) );
                            }
                        }
                    else 
                        {
                        erg += error("double_hashtable(i)");
                        goto ende;
                        }
                    }
            }
        }
ende:
    /* pointer updaten */
    k = -1;
    for (i=S_V_LI(b)-1,z = S_V_I(b,S_V_LI(b)-1) ; i>=l;i--,z--)
        if (EMPTYP(z)) C_I_I(z,k);
        else k = i;
    for (;i>=0;i--,z--)
        if (EMPTYP(z)) {
            /* SYMCHECK(S_I_I(z) != -1,"double_hashtable:e2"); */
            C_I_I(z,k);
            }
        else
            break;

    CTO(HASHTABLE,"double_hashtable(1-end)",b);
    ENDR("double_hashtable");
}

INT split_hashtable(a,b,c) OP a,b,c;
/* AK 201201 */
{
    INT i,t=0,h=0,erg = OK;
    OP z;
    CTO(HASHTABLE,"split_hashtable(1)",a);
    CTO(EMPTY,"split_hashtable(2)",b);
    CTO(EMPTY,"split_hashtable(3)",c);
    SYMCHECK(WEIGHT_HASHTABLE(a)<=1, "split_hashtable:<2 entries");

    m_il_v(S_V_LI(a)+1,b);C_O_K(b,HASHTABLE);M_I_I(S_V_LI(a),S_V_L(b));
    m_il_v(S_V_LI(a)+1,c);C_O_K(c,HASHTABLE);M_I_I(S_V_LI(a),S_V_L(c));
    for (i=0;i<S_V_LI(a);i++)
        {
        if (not EMPTYP(S_V_I(a,i)))
           {
           if (t++%2) COPY(S_V_I(a,i),S_V_I(b,i));
           else  COPY(S_V_I(a,i),S_V_I(c,i));
           h = i;
           }
        }

    if (t == 1) /* only entires at one adress, split them */
        {
        m_il_v(S_V_LI(S_V_I(c,h)), S_V_I(b,h));
        for (i=0;i<S_V_LI(S_V_I(c,h));i++)
            if (i%2) { SWAP(S_V_I(S_V_I(c,h),i), S_V_I(S_V_I(b,h),i) ); }
        }

    t = 0; FORALL(z,b, { t++; } ); M_I_I(t,S_V_I(b, S_V_LI(b)));
    h = 0; FORALL(z,c, { h++; } ); M_I_I(h,S_V_I(c, S_V_LI(c)));
    SYMCHECK( h+t != WEIGHT_HASHTABLE(a) ,"split_hashtable:weight doesnt add");
    CTO(HASHTABLE,"split_hashtable(2-res)",b);
    CTO(HASHTABLE,"split_hashtable(3-res)",c);
    ENDR("split_hashtable");
}




INT hash_partition(a) OP a;
/* AK 261001 */
{
    INT erg = OK,i;
    CTO(PARTITION,"hash_partition(1)",a);
    if (S_PA_HASH(a) == -1)  /* no hash value up to now */
        {
        i = hash(S_PA_S(a));
        C_PA_HASH(a,i);
        return i; 
        }
    else
        return S_PA_HASH(a);

    ENDR("hash_partition");
}

INT hash_monompartition(a) OP a;
/* AK 261001 */
{
    INT erg = OK,res;
    CTO(MONOM,"hash_monompartition(1)",a);
    CTO(PARTITION,"hash_monompartition(1)",S_MO_S(a));
    if (S_PA_HASH(S_MO_S(a)) == -1) 
        {
        HASH_INTEGERVECTOR(S_PA_S(S_MO_S(a)),res);
        C_PA_HASH(S_MO_S(a),res);
        return res; 
        }
    else
        return S_PA_HASH(S_MO_S(a));
 
    ENDR("hash_monompartition");
}

INT hash_integervector(a) OP a;
/* AK 261001 */
{
    INT res;
    HASH_INTEGERVECTOR(a,res);
    return res;
}

INT hash(a) OP a;
/* returns hash-number unsigned 32 bit */
/* AK 281097 */
{
    INT i,erg=OK;
    COP("hash(1)",a);
    again:
    switch(S_O_K(a))
        {
        case EMPTY: 
            return 0;
        case INTEGER: 
            return S_I_I(a);
        case MONOM: 
            a=S_MO_S(a);
            goto again;
        case POLYNOM: 
        case LIST: 
            return hash_list(a);
        case SKEWPARTITION: 
            return hash_skewpartition(a);
        case PARTITION: 
            return hash_partition(a);
        case PERMUTATION: a=S_P_S(a);goto again;
        case SUBSET:
	case GALOISRING:
        case INTEGERVECTOR:
            return hash_integervector(a);
#ifdef FFTRUE
        case FF:
            return hash_ff(a);
#endif
        case MATRIX:
        case INTEGERMATRIX:
        case KRANZTYPUS:
            return hash_matrix(a);
        case VECTOR: 
            {
            INT res;
            if (S_V_LI(a) == 0) return 4711; /* AK 300802 4711 instead of 11 */
            res = hash(S_V_I(a,0));
            for (i=1;i<S_V_LI(a);i++)
                {
                res *= 4711;   /* AK 300802 4711 instead of 11 */
                res += hash(S_V_I(a,i));
                }
            return res;
            }
        default:
            erg += WTO("hash(1)",a);
            break;
        }
    ENDR("hash");
}
#define t_HASHTABLE_SF(a,b,af,t,cf,tf)\
do {\
    INT i,j;\
    OP z;\
    if (a == b)  { erg += (*af)(a); goto ende; }\
   \
    if (WEIGHT_HASHTABLE(a) > 30 ) /* more then 30 entries *//* AK 260901 */\
         erg += init(BINTREE,b);\
    else\
         erg += init(t,b);\
 \
    for (i=0;i<S_V_LI(a);i++)\
    {\
    z = S_V_I(a,i);\
    if (not EMPTYP(z))\
        {\
        for (j=0;j<S_V_LI(z);j++)\
        if (not EMPTYP(S_V_I(z,j)))\
        if (not NULLP(S_MO_K(S_V_I(z,j))))\
            {\
            OP d = CALLOCOBJECT();\
            erg += m_skn_s(S_MO_S(S_V_I(z,j)),\
                    S_MO_K(S_V_I(z,j)),NULL,d);\
            INSERT(d,b,NULL,cf);\
            }\
        }\
 \
    }\
    if (S_O_K(b) == BINTREE) erg += (*tf)(b,b);\
} while(0)

INT t_HASHTABLE_SCHUR(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_SCHUR(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_SCHUR_apply,
                   SCHUR,comp_monomschur,t_BINTREE_SCHUR);
ende:
    CTO(SCHUR,"t_HASHTABLE_SCHUR(e2)",b);
    ENDR("t_HASHTABLE_SCHUR");
}

INT t_HASHTABLE_MONOMIAL(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_MONOMIAL(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_MONOMIAL_apply,
                   MONOMIAL,comp_monommonomial,t_BINTREE_MONOMIAL);
ende:
    CTO(MONOMIAL,"t_HASHTABLE_MONOMIAL(e2)",b);
    ENDR("t_HASHTABLE_MONOMIAL");
}

INT t_HASHTABLE_HOMSYM(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_HOMSYM(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_HOMSYM_apply,HOMSYM,
                   comp_monomhomsym,t_BINTREE_HOMSYM);
ende:
    CTO(HOMSYM,"t_HASHTABLE_HOMSYM(e2)",b);
    ENDR("t_HASHTABLE_HOMSYM");
}

INT t_HASHTABLE_ELMSYM(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_ELMSYM(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_ELMSYM_apply,ELMSYM,
                   comp_monomelmsym,t_BINTREE_ELMSYM);
ende:
    CTO(ELMSYM,"t_HASHTABLE_ELMSYM(e2)",b);
    ENDR("t_HASHTABLE_ELMSYM");
}

INT t_HASHTABLE_POWSYM(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_POWSYM(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_POWSYM_apply,POWSYM,
                   comp_monompowsym,t_BINTREE_POWSYM);
ende:
    CTO(POWSYM,"t_HASHTABLE_POWSYM(e2)",b);
    ENDR("t_HASHTABLE_POWSYM");
}

INT t_HASHTABLE_POLYNOM(a,b) OP a,b;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_POLYNOM(1)",a);
    t_HASHTABLE_SF(a,b,t_HASHTABLE_POLYNOM_apply,POLYNOM,
                   comp_monomvector_monomvector,t_BINTREE_POLYNOM);
ende:
    CTO(POLYNOM,"t_HASHTABLE_POLYNOM(e2)",b);
    ENDR("t_HASHTABLE_POLYNOM");
}


#define t_HASHTABLE_SF_apply(a,typ,cf,tf)\
{\
    OP b;\
    INT i,j;\
    OP z;\
    b = CALLOCOBJECT();\
    if (WEIGHT_HASHTABLE(a) > 30 ) /* more then 30 entries *//* AK 260901 */\
         erg += init_bintree(b);\
    else\
         erg += init(typ,b);\
\
    for (i=0;i<S_V_LI(a);i++)\
    {\
    z = S_V_I(a,i);\
    if (not EMPTYP(z))\
        {\
        for (j=0;j<S_V_LI(z);j++)\
        if (not EMPTYP(S_V_I(z,j)))\
        if (not NULLP(S_MO_K(S_V_I(z,j))))\
            {\
            OP d;\
            d = CALLOCOBJECT();\
            erg += b_sn_l(CALLOCOBJECT(),NULL,d);\
            SWAP(S_L_S(d),S_V_I(z,j));\
            C_O_K(d,typ);\
            INSERT(d,b,NULL,cf);\
            }\
        else {\
            FREESELF(S_V_I(z,j));\
            }\
        }\
    }\
\
    if (S_O_K(b) == BINTREE)\
        erg += (*tf)(b,b);\
\
    SWAP(a,b);\
    M_I_I(0,S_V_I(b,S_V_LI(b))); /* keine eintraege mehr in der hashtable */\
    FREEALL(b);\
}

INT t_HASHTABLE_POLYNOM_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_POLYNOM_apply(1)",a);
    t_HASHTABLE_SF_apply(a,POLYNOM,comp_monomvector_monomvector,t_BINTREE_POLYNOM);
    ENDR("t_HASHTABLE_POLYNOM_apply");
}

INT t_HASHTABLE_SCHUR_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_SCHUR_apply(1)",a);
    t_HASHTABLE_SF_apply(a,SCHUR,comp_monomschur,t_BINTREE_SCHUR);
    ENDR("t_HASHTABLE_SCHUR_apply");
}

INT t_HASHTABLE_POWSYM_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_POWSYM_apply(1)",a);
    t_HASHTABLE_SF_apply(a,POWSYM,comp_monompowsym,t_BINTREE_POWSYM);
    ENDR("t_HASHTABLE_POWSYM_apply");
}

INT t_HASHTABLE_HOMSYM_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_HOMSYM_apply(1)",a);
    t_HASHTABLE_SF_apply(a,HOMSYM,comp_monomhomsym,t_BINTREE_HOMSYM);
    ENDR("t_HASHTABLE_HOMSYM_apply");
}


INT t_HASHTABLE_ELMSYM_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_ELMSYM_apply(1)",a);
    t_HASHTABLE_SF_apply(a,ELMSYM,comp_monomelmsym,t_BINTREE_ELMSYM);
    ENDR("t_HASHTABLE_ELMSYM_apply");
}



INT t_HASHTABLE_MONOMIAL_apply(a) OP a;
/* AK 240901 */
{
    INT erg = OK;
    CTO(HASHTABLE,"t_HASHTABLE_MONOMIAL_apply(1)",a);
    t_HASHTABLE_SF_apply(a,MONOMIAL,comp_monommonomial,t_BINTREE_MONOMIAL);
    ENDR("t_HASHTABLE_MONOMIAL_apply");
}


INT t_POWSYM_HASHTABLE(a,b) OP a,b;
/* AK 171001 */
{
    OP z;
    INT erg = OK;
    CTO(POWSYM,"t_POWSYM_HASHTABLE",a);
    CE2(a,b,t_POWSYM_HASHTABLE);
    erg += init(HASHTABLE,b);
    FORALL(z,a,{ OP d = CALLOCOBJECT();
             COPY(z,d);
             INSERT_HASHTABLE(d,b,NULL,eq_monomsymfunc,hash_monompartition); } );
    ENDR("t_POWSYM_HASHTABLE");
}

INT t_HOMSYM_HASHTABLE(a,b) OP a,b;
/* AK 171001 */
{
    OP z;
    INT erg = OK;
    CTO(HOMSYM,"t_HOMSYM_HASHTABLE",a);
    CE2(a,b,t_HOMSYM_HASHTABLE);
    erg += init(HASHTABLE,b);
    FORALL(z,a,{ OP d = CALLOCOBJECT();
             COPY(z,d);
             INSERT_HASHTABLE(d,b,NULL,eq_monomsymfunc,hash_monompartition); } );
    ENDR("t_HOMSYM_HASHTABLE");
}

INT t_SCHUR_HASHTABLE(a,b) OP a,b;
/* AK 171001 */
{
    OP z;
    INT erg = OK;
    CTO(SCHUR,"t_SCHUR_HASHTABLE",a);
    CE2(a,b,t_SCHUR_HASHTABLE);
    erg += init(HASHTABLE,b);
    FORALL(z,a,{ OP d = CALLOCOBJECT();
             COPY(z,d);
             INSERT_HASHTABLE(d,b,NULL,eq_monomsymfunc,hash_monompartition); } );
    ENDR("t_SCHUR_HASHTABLE");
}



INT t_ELMSYM_HASHTABLE(a,b) OP a,b;
/* AK 171001 */
{
    OP z;
    INT erg = OK;
    CTO(ELMSYM,"t_ELMSYM_HASHTABLE(1)",a);
    CE2(a,b,t_ELMSYM_HASHTABLE);
    erg += init(HASHTABLE,b);
    FORALL(z,a,{ OP d = CALLOCOBJECT();
             COPY(z,d);
             INSERT_HASHTABLE(d,b,NULL,eq_monomsymfunc,hash_monompartition); } );
    ENDR("t_ELMSYM_HASHTABLE");
}



INT t_MONOMIAL_HASHTABLE(a,b) OP a,b;
/* AK 171001 */
{
    OP z;
    INT erg = OK;
    CTO(MONOMIAL,"t_MONOMIAL_HASHTABLE(1)",a);
    CE2(a,b,t_MONOMIAL_HASHTABLE);
    erg += init(HASHTABLE,b);
    FORALL(z,a,{ 
             OP d = CALLOCOBJECT();
             COPY(z,d);
             INSERT_HASHTABLE(d,b,NULL,eq_monomsymfunc,hash_monompartition); } );

    ENDR("t_MONOMIAL_HASHTABLE");
}

static INT hash2(a) OP a;
{
    INT erg = OK;
    INT res;
    CTO(VECTOR,"hash2(1)",a);
    M_I_I(2,S_V_L(a));
    res = HASH(a);
    M_I_I(3,S_V_L(a));
    return res;
    ENDR("hash2");
}
static INT hash1(a) OP a;
{
    INT erg = OK;
    INT res;
    CTO(VECTOR,"hash1(1)",a);
    SYMCHECK(S_V_LI(a) != 2,"hash1:vector length != 2");
    res = HASH(S_V_I(a,0));
    return res;
    ENDR("hash1");
}


static INT eq2(a,b) OP a,b;
{
    INT erg = OK;
    INT res;
    CTO(VECTOR,"eq2(1)",a);
    CTO(VECTOR,"eq2(2)",b);

    M_I_I(2,S_V_L(a));
    M_I_I(2,S_V_L(b));
    res = EQ(a,b);
    M_I_I(3,S_V_L(a));
    M_I_I(3,S_V_L(b));
    return res;
    ENDR("eq2");
}

static INT eq1(a,b) OP a,b;
{
    INT erg = OK;
    INT res;
    CTO(VECTOR,"eq1(1)",a);
 
/*
    M_I_I(1,S_V_L(a));
    M_I_I(1,S_V_L(b));
    res = EQ(a,b);
    M_I_I(2,S_V_L(a));
    M_I_I(2,S_V_L(b));
    return res;
*/
    return EQ(S_V_I(a,0), S_V_I(b,0)); 
    ENDR("eq1");
}
 


OP find_1result_hashtable(a,h) OP a,h;
{
    INT erg = OK;
    OP res,v;
    CTO(ANYTYPE,"find_1result_hashtable(1)",a);
    CTO(HASHTABLE,"find_1result_hashtable(2)",h);
 
    if (lookup1 == NULL)
        NEW_VECTOR(lookup1,2);
    C_V_I(lookup1,0,a);
    res = find_hashtable(lookup1,h,eq1,hash1);
    
    if (res == NULL) return res;
 
    res = S_V_I(res,1);
    
    return res;
 
    ENDO("find_1result_hashtable");
}

OP find_2result_hashtable(a,b,h) OP a,b,h;
{
    INT erg = OK;
    OP res,v;
    CTO(ANYTYPE,"find_2result_hashtable(1)",a);
    CTO(ANYTYPE,"find_2result_hashtable(2)",b);
    CTO(HASHTABLE,"find_2result_hashtable(3)",h);

    NEW_VECTOR(v,3);
    COPY(a,S_V_I(v,0));
    COPY(b,S_V_I(v,1));
    res = find_hashtable(v,h,eq2,hash2);
    FREEALL(v);
    if (res == NULL) return res;

    res = S_V_I(res,2);
    
    return res;

    ENDO("find_2result_hashtable");
}

INT move_2result_hashtable(a,b,c,h) OP a,b,c,h;
{
    INT erg = OK;
    OP v;
    CTO(ANYTYPE,"move_2result_hashtable(1)",a);
    CTO(ANYTYPE,"move_2result_hashtable(2)",b);
    CTO(ANYTYPE,"move_2result_hashtable(3)",c);
    CTO(HASHTABLE,"move_2result_hashtable(4)",h);
    NEW_VECTOR(v,3);
    COPY(a,S_V_I(v,0));
    COPY(b,S_V_I(v,1));
    C_V_I(v,2,c);
    C_O_K(c,EMPTY);
    FREEALL(c);
    insert_scalar_hashtable(v,h,NULL,eq2,hash2);
    CTO(HASHTABLE,"move_2result_hashtable(4-res)",h);
    ENDR("move_2result_hashtable");
}

INT move_1result_hashtable(a,c,h) OP a,c,h;
{
    INT erg = OK;
    OP v;
    CTO(ANYTYPE,"move_1result_hashtable(1)",a);
    CTO(ANYTYPE,"move_1result_hashtable(2)",c);
    CTO(HASHTABLE,"move_1result_hashtable(3)",h);
    NEW_VECTOR(v,2);
    COPY(a,S_V_I(v,0));
    C_V_I(v,1,c);
    C_O_K(c,EMPTY);
    FREEALL(c);
    insert_scalar_hashtable(v,h,NULL,eq1,hash1);
    CTO(HASHTABLE,"move_1result_hashtable(e3)",h);
    ENDR("move_1result_hashtable");
}

INT filter_apply_hashtable(a,f) OP a; INT (*f)();
/* AK 130603 */
/* if f return true the elemnts stay in the hashtable */
{
    OP z;
    INT erg = OK;
    CTO(HASHTABLE,"filter_apply_hashtable(1)",a);
    FORALL(z,a, {
        if ((*f)(z) != TRUE)
            {
            FREESELF(z);
            DEC_INTEGER(S_V_I(a,S_V_LI(a))); /* counter-- */
            }
        });
    ENDR("filter_apply_hashtable");          
}

INT t_HASHTABLE_VECTOR(a,v) OP a,v;
/* AK 040803 */
{
    INT erg =OK;INT i=0;
    OP z;
    CTO(HASHTABLE,"t_HASHTABLE_VECTOR(1)",a);
    CE2(a,v,t_HASHTABLE_VECTOR);
    m_il_v(S_V_II(a,S_V_LI(a)),v);
    FORALL(z,a,{ COPY(z,S_V_I(v,i)); i++; });
    ENDR("t_HASHTABLE_VECTOR");
}
