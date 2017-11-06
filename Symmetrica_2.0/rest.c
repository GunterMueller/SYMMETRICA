/* SYMMETRICA file:rest.c */
#include "def.h"
#include "macro.h"


#ifdef SKEWPARTTRUE
static struct skewpartition * callocskewpartition();
#endif /* SKEWPARTTRUE */
#ifdef WORDTRUE
static INT coroutine250488();
#endif /* WORDTRUE */




INT callocobject_anfang()
{        
    return OK;
}

INT callocobject_ende()
{
    return OK;
}

INT check_equal_3(a,b,c,f,e) OP a,b,c; INT (*f)(), *e;
/* the OP a and b and c are compared 
   return : EQUAL if a == c or b==c , is in this case the function was 
        evaluated in *e we have the return value
    b is freed
*/
/* AK 240398 V2.0 */
{
    if ((a==c) && (b == c))
        {
        OP d = callocobject();
        *d = *c;
        C_O_K(c,EMPTY);
        *e = (*f)(d,d,c);
        *e += freeall(d);
        return EQUAL;
        }
    else if (a==c)
        {
        OP d = callocobject();
        *d = *c;
        C_O_K(c,EMPTY);
        *e = (*f)(d,b,c);
        *e += freeall(d);
        return EQUAL;
        }
    else if (b==c)
        {
        OP d = callocobject();
        *d = *c;
        C_O_K(c,EMPTY);
        *e = (*f)(a,d,c);
        *e += freeall(d);
        return EQUAL;
        }
    else 
        {
        *e = OK;
        if (c != NULL)
        if (not EMPTYP(c))
            *e += freeself(c);
        return OK;
        }
}
INT check_equal_4(a,b,c,d,f,e) OP a,b,c,d; INT (*f)(), *e;
/* the OP a and b and c are compared 
   return : EQUAL if a == d or b==d or d==c, is in this case the function was 
        evaluated in *e we have the return value
*/
{
    if (a==d)
        {
        OP dd = callocobject();
        *dd = *d;
        C_O_K(d,EMPTY);
        *e = (*f)(dd,b,c,d);
        *e += freeall(dd);
        return EQUAL;
        }
    else if (b==d)
        {
        OP dd = callocobject();
        *dd = *d;
        C_O_K(d,EMPTY);
        *e = (*f)(a,dd,c,d);
        *e += freeall(dd);
        return EQUAL;
        }
    else if (c==d)
        {
        OP dd = callocobject();
        *dd = *d;
        C_O_K(d,EMPTY);
        *e = (*f)(a,b,dd,d);
        *e += freeall(dd);
        return EQUAL;
        }
    else 
        {
        *e = OK;
        if (d != NULL)
        if (not EMPTYP(d))
            *e += freeself(d);
        return OK;
        }
}

INT check_equal_2(a,b,f,e) OP a,b; INT (*f)(), *e;
/* the OP a and b are compared 
   return : EQUAL if a == b , is in this case the function was 
        evaluated in *e we have the return value
    b is freed
*/
{
    INT erg = OK;
    if (a==b)
        {
        OP c;
        c = CALLOCOBJECT();
        *c = *b;
        C_O_K(b,EMPTY);
        *e = (*f)(c,b);
        FREEALL(c);
        return EQUAL;
        }
    else 
        {
        *e = OK;
        FREESELF(b);
        return OK;
        }
    ENDR("check_equal_2");
}
INT check_equal_2a(a,b,f,e) OP a,b; INT (*f)(), *e;
/* apply version, work with copy of a */
/* the OP a and b are compared 
   return : EQUAL if a == b , is in this case the function was 
        evaluated in *e we have the return value
    b is freed
*/
/* AK 240398 V2.0 */
{
    if (a==b)
        {
        OP c = callocobject();
        *e = copy(a,c);
        *e += (*f)(c,b);
        *e += freeall(c);
        return EQUAL;
        }
    else 
        {
        *e = OK;
        return OK;
        }
}


#define SYMDIR "./symresults"
INT sym_no_results=0;     /* 0 == stored results will be used */
            /* 1 == stored results will not be used */

static FILE *check_fopen(f,r) char *f, *r;
/* AK 240398 V2.0 */
{
    char t1[300];
    if (sym_no_results==1) 
        return NULL;
    sprintf(t1,"%s/%s",SYMDIR,f);
    return fopen(t1,r);
}

INT check_result_0(t,c) OP c; char *t;
/* testet ob ein vorberechnetes result da ist */
/* AK 280705 V3.0 */
{
    char t1[100],t3[100];
    FILE *fp;
    INT erg = OK;

    COP("check_result_0(1)",t);

    fp = check_fopen(t,"r");
    if (fp == NULL) 
        return NORESULT;
    erg += objectread(fp,c);
    fclose(fp);
    ENDR("check_result_0");
}

INT check_result_1(a,t,c) OP a,c; char *t;
/* testet ob ein vorberechnetes result da ist */
/* AK 020996 */
/* AK 240398 V2.0 */
{
    char t1[100],t3[100];
    FILE *fp;
    INT erg = OK;

    COP("check_result(2)",t);
    EOP("check_result(1)",a);

    sprint(t1,a);
    sprintf(t3,"%s_%s",t,t1);
    fp = check_fopen(t3,"r");
    if (fp == NULL) 
        return NORESULT;
    erg += objectread(fp,c);
    fclose(fp);
    ENDR("check_result_1");
}

INT check_result_2(a,b,t,c) OP a,b,c; char *t;
/* testet ob ein vorberechnetes result da ist */
/* AK 020996 */
/* AK 240398 V2.0 */
{
    char t1[100],t2[100],t3[100];
    FILE *fp;
    INT erg = OK;
    COP("check_result(3)",t);
    EOP("check_result(1)",a);
    EOP("check_result(2)",b);

    sprint(t1,a);
    sprint(t2,b);
    sprintf(t3,"%s_%s_%s",t,t1,t2);
    fp = check_fopen(t3,"r");
    if (fp == NULL) 
        return NORESULT;
    erg += objectread(fp,c);
    fclose(fp);
    ENDR("check_result_2");
}

INT check_result_3(a,b,d,t,c) OP a,b,d,c; char *t;
/* check if there is a stored result */
/* AK 020996 */ /* AK 240398 V2.0 */
{
    char t1[100],t2[100],t3[100],t4[100];
    FILE *fp;
    INT erg = OK;
    COP("check_result(4)",t);
    EOP("check_result(1)",a);
    EOP("check_result(2)",b);
    EOP("check_result(3)",d);

    sprint(t1,a); sprint(t2,b); sprint(t4,d);
    sprintf(t3,"%s_%s_%s_%s",t,t1,t2,t4);
    fp = check_fopen(t3,"r");
    if (fp == NULL) 
        return NORESULT;
    erg += objectread(fp,c);
    fclose(fp);
    ENDR("check_result_3");
}

INT check_result_5(a,b,d,e,f,t,c) OP a,b,d,c,e,f; char *t;
/* check if there is a stored result */
/* AK 240805 */
{
    char t1[100],t2[100],t3[100],t4[100],t5[100],t6[100];
    FILE *fp;
    INT erg = OK;
    COP("check_result(6)",t);
    EOP("check_result(1)",a);
    EOP("check_result(2)",b);
    EOP("check_result(3)",d);
    EOP("check_result(4)",e);
    EOP("check_result(5)",f);

    sprint(t1,a); sprint(t2,b); sprint(t4,d);
    sprint(t5,e);sprint(t6,f);

    sprintf(t3,"%s_%s_%s_%s_%s_%s",t,t1,t2,t4,t5,t6);
    fp = check_fopen(t3,"r");
    if (fp == NULL) 
        return NORESULT;
    erg += objectread(fp,c);
    fclose(fp);
    ENDR("check_result_5");
}



INT store_result_0(t,c) OP c; char *t; 
/* stores a result without parameter */
/* AK 280705 V3.0 */
{
    FILE *fp;
    INT erg = OK;
    fp = check_fopen(t,"w");
    if (fp == NULL)  { goto endr_ende; } /* error, silently not storing */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_0");
}

INT store_result_1(a,t,c) OP a,c; char *t; 
/* speichere ein berechnetes result  zu einem parameter */ /* AK 020996 */
/* AK 240398 V2.0 */
{
    char t1[100],t3[100];
    FILE *fp;
    INT erg = OK;
    sprint(t1,a);
    sprintf(t3,"%s_%s",t,t1);
    fp = check_fopen(t3,"w");
    if (fp == NULL)  { goto endr_ende; } /* nicht gespeichert */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_1");
}

INT store_result_2(a,b,t,c) OP a,b,c; char *t;
/* speichere ein berechnetes result  zu zwei parametern */
/* AK 020996 */
/* AK 240398 V2.0 */
{
    char t1[100],t2[100],t3[100];
    FILE *fp;
    INT erg = OK;
    sprint(t1,a);
    sprint(t2,b);
    sprintf(t3,"%s_%s_%s",t,t1,t2);
    fp = check_fopen(t3,"w");
    if (fp == NULL)  {  goto endr_ende; } /* nicht gespeichert */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_2");
}

INT store_result_3(a,b,d,t,c) OP d,a,b,c; char *t;
/* speichere ein berechnetes result  zu zwei parametern */
/* AK 020996 */
/* AK 240398 V2.0 */
{
    char t1[100],t2[100],t3[100],t4[100];
    FILE *fp;
    INT erg = OK;
    sprint(t1,a); sprint(t2,b); sprint(t4,d);
    sprintf(t3,"%s_%s_%s_%s",t,t1,t2,t4);
    fp = check_fopen(t3,"w");
    if (fp == NULL)  {  goto endr_ende; } 
        /* nicht gespeichert */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_2");
}

INT store_result_5(a,b,d,e,f,t,c) OP d,a,b,c,e,f; char *t;
/* stores a result indexed by 5 parameters */
/* AK 240805 */
{
    char t1[100],t2[100],t3[100],t4[100],t5[100],t6[100];
    FILE *fp;
    INT erg = OK;
    sprint(t1,a); sprint(t2,b); sprint(t4,d);
    sprint(t5,e);sprint(t6,f);
    sprintf(t3,"%s_%s_%s_%s_%s_%s",t,t1,t2,t4,t5,t6);
    fp = check_fopen(t3,"w");
    if (fp == NULL)  {  goto endr_ende; }
        /* nicht gespeichert */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_5");
}

INT store_result_4(a,b,d,e,t,c) OP d,a,b,c,e; char *t;
/* stores a result indexed by 4 parameters */
/* AK 250607 */
{
    char t1[100],t2[100],t3[100],t4[100],t5[100],t6[100];
    FILE *fp;
    INT erg = OK;
    sprint(t1,a); sprint(t2,b); sprint(t4,d);
    sprint(t5,e);
    sprintf(t3,"%s_%s_%s_%s_%s",t,t1,t2,t4,t5);
    fp = check_fopen(t3,"w");
    if (fp == NULL)  {  goto endr_ende; }
        /* nicht gespeichert */
    erg += objectwrite(fp,c);
    fclose(fp);
    ENDR("store_result_4");
}




INT empty_object(t) char *t;
/* AK 220997 */
/* AK 240398 V2.0 */
    {
    fprintf(stderr,"function: %s \n",t);
    return error("empty object as parameter");
    }

INT null_object(t) char *t;
/* AK 211093 */
/* AK 240398 V2.0 */
    {
    fprintf(stderr,"function: %s \n",t);
    return error("null object as parameter");
    }

INT not_yet_implemented(t) char *t;
/* AK 211093 */
/* AK 240398 V2.0 */
    {
    fprintf(stderr,"function: %s \n",t);
    return error("not yet implemented");
    }

INT equal_2_error() {
    fprintf(stderr,"internal error: two parameter equal, this should not happen");
    return I2PE;
    }
INT error_during_computation(t) char *t;
/* AK 090393 */ /* AK 240398 V2.0 */
    {
    INT err;
    fprintf(stderr,"function: %s \n",t);
    err = error("error during computation");
    return ERROR;
    }
INT error_during_computation_code(t,code) char *t; INT code;
/* AK 170698 V2.0 */
    {
    INT err;
    fprintf(stderr,"function: %s code: %ld \n",t,code);
    err = error("error during computation");
    return ERROR;
    }


INT wrong_type_twoparameter(t,a,b) char *t; OP a,b;
/* AK 090393 */
/* AK 240398 V2.0 */
    {
    fprintf(stderr,"function: %s not definied for object types:\n",t);
    fprintf(stderr,"type of first parameter:");
    printobjectkind(a);
    fprintf(stderr,"type of second parameter:");
    printobjectkind(b);
    return error("function with wrong input types");
    }

INT wrong_type_oneparameter(t,a) char *t; OP a;
/* AK 090393 */
/* AK 240398 V2.0 */
    {
    fprintf(stderr,"function: %s not definied for object type:\n",t);
    printobjectkind(a);
    return error("function with wrong input type");
    }

INT swap(a,b) OP a,b;
/* AK 280388 */ /* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* a becomes b and b becomes a */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    struct object c;
    SYMCHECK(a == b,"swap:identical");
       
    c = *a; 
    *a = *b; 
    *b = c; 
    ENDR("swap");
    }

INT rz(a,b) OP a, b;
/* AK 261087 berechnet die reduzierte Zerlegung */
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 120391 V1.2 */
/* AK 210891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    EOP("rz(1)",a);
    COP("rz(2)",b);
    CE2(a,b,rz);

    switch(S_O_K(a))
        {
#ifdef PERMTRUE
        case PERMUTATION : 
            switch(S_P_K(a))
                {
                case VECTOR: 
                    erg += rz_perm(a,b);break;
                case BAR: 
                    erg += rz_bar(a,b);break;
                }
            break;
        case INTEGERVECTOR:
        case VECTOR: 
            switch(S_O_K(S_V_I(a,0L)))
                {
                case INTEGER: 
                    erg += rz_lehmercode(a,b);
                    break;
                case VECTOR: 
                    erg += rz_lehmercode_bar(a,b);
                    break;
                }
            break;
#endif /* PERMTRUE */
        default: 
            erg+= WTO("rz(1)",a); 
            break;
            
        };
    ENDR("rz");
}
 
INT lastof(a,res) OP a,res;
/* AK 280689 V1.0 */ /* AK 090790 V1.1 */ /* AK 200691 V1.2 */
/* AK 210891 V1.3 */
/* AK 020398 V2.0 */
/* input: ..
   output: a copy of the last elemnent */
    {
    INT erg = OK; 
    EOP("lastof(1)",a);
    COP("lastof(2)",res);
    CE2(a,res,lastof);

    switch(S_O_K(a))
        {
#ifdef PARTTRUE
        case PARTITION: 
            erg+=lastof_partition(a,res);
            break;
#endif /* PARTTRUE */

#ifdef SKEWPARTTRUE
        case SKEWPARTITION : 
            erg+=lastof_skewpartition(a,res);
            break;
#endif /* SKEWPARTTRUE */

#ifdef VECTORTRUE
        case INTEGERVECTOR:
            erg+=lastof_integervector(a,res);
            break;

        case VECTOR : 
            erg+=lastof_vector(a,res);
            break;
#endif /* VECTORTRUE */

        default: 
            erg+= WTO("lastof(1)",a); 
            break;
        };
    ENDR("lastof");
    }

INT freeall_speicherposition;
INT freeall_speichersize;
OP *freeall_speicher; /* global variable for callocobject/freeall */

INT speicher_anfang()
/* AK 231001 */
    {
    INT erg = OK;
    freeall_speicher=(OP *)SYM_MALLOC(SPEICHERSIZE * sizeof(OP));
    SYMCHECK( (freeall_speicher == NULL), "speicher_anfang:no mem");
    freeall_speicherposition = -1;
    freeall_speichersize=SPEICHERSIZE;
    ENDR("speicher_anfang");
    }

INT speicher_ende() 
/* AK 231001 */
    {
    INT i;
    for (i=freeall_speicherposition;i>=0L;i--) /* AK 161091 */
                {
                SYM_free(freeall_speicher[i]); /* AK 161091 */
                }
    SYM_FREE(freeall_speicher); /* AK 161091 */
    return OK;
    }


INT freeall_magma(a) OP a;
{
    if (not EMPTYP(a)) 
        freeself(a); 
    SYM_FREE(a);
    return OK;
}

INT freeall(a) OP a;
/* AK 101286 */ /* AK 280689 V1.0 */ /* AK 071289 V1.1 */
/* AK 270291 V1.2 */ /* AK 050891 V1.3 */
    { 
    INT erg = OK;

    COP("freeall(1)",a);

    if (not EMPTYP(a)) 
        erg += freeself(a); 

    if (freeall_speicherposition+1  == freeall_speichersize) /* AK 231001 */
        {
        freeall_speicher = (OP *) 
            SYM_realloc(freeall_speicher,
                (freeall_speichersize+SPEICHERSIZE)*sizeof(OP));
        SYMCHECK( (freeall_speicher == NULL) ,"freeall:no more memory");
        freeall_speichersize = freeall_speichersize+SPEICHERSIZE;
        }
        freeall_speicher[++freeall_speicherposition] = a;

    ENDR("freeall");
    }


INT freeself(a) OP a;
/* AK 061186 */ /* AK 280689 V1.0 */ /* AK 041289 V1.1 */ /* AK 050891 V1.3 */
/* AK 070498 V2.0 */
    {
    INT erg=OK;
    COP("freeself(1)",a);

    switch(S_O_K(a))
        {
        case EMPTY: 
            break;
#ifdef BINTREETRUE
        case BINTREE : 
            erg += freeself_bintree(a); 
            break;
#endif /* BINTREETRUE */

#ifdef BRUCHTRUE
        case BRUCH : 
            erg += freeself_bruch(a); 
            break;
#endif /* BRUCHTRUE */
#ifdef FFTRUE
        case FF :
            erg += freeself_ff(a); 
            break;
#endif /* FFTRUE */
        case INTEGER : 
            erg += FREESELF_INTEGER(a);
            break;
#ifdef LISTTRUE
        case GRAL: case HOM_SYM: case POW_SYM: case MONOPOLY:
        case POLYNOM: case SCHUR: case SCHUBERT: case ELM_SYM:
        case LIST: case MONOMIAL:
            erg += freeself_list(a); 
            break; 
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT : 
            erg += freeself_longint(a); 
            break; 
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case KRANZTYPUS : 
            erg += freeself_kranztypus(a);
            break;
        case KOSTKA :
        case MATRIX : 
            erg += freeself_matrix(a); 
            break;
        case INTEGERMATRIX: 
            erg += freeself_integermatrix(a); 
            break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM : 
            erg += freeself_monom(a); 
            break;
#endif /* MONOMTRUE */
#ifdef NUMBERTRUE
        case SQ_RADICAL:
        case CYCLOTOMIC: 
            erg += freeself_number(a);
            break;
#endif /* NUMBERTRUE */
#ifdef PARTTRUE
        case AUG_PART : 
        case CHARPARTITION:
        case PARTITION : 
            erg += freeself_partition(a); 
            break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION : 
            erg += freeself_permutation(a);
            break;
#endif /* PERMTRUE */
#ifdef REIHETRUE
        case REIHE : 
            erg += freeself_reihe(a);
            break;
#endif /* REIHETRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION : 
            erg += freeself_skewpartition(a); 
            break;
#endif /* PERMTRUE */
#ifdef CHARTRUE
        case SYMCHAR : 
            erg += freeself_symchar(a); 
            break;
#endif /* CHARTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX : 
            erg += freeself_tableaux(a); 
            break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case HASHTABLE:
            erg += freeself_hashtable(a);
            break;
        case LAURENT: 
            erg += freeself_laurent(a);
            break;
#ifdef KRANZTRUE
        case KRANZ: 
            erg += freeself_kranz(a);
            break;
#endif /* KRANZTRUE */
        case WORD: 
        case QUEUE: 
        case VECTOR: 
            erg += freeself_vector(a);
            break;
        case BITVECTOR:
            erg += freeself_bitvector(a); 
            break;
        case SUBSET:
        case INTEGERVECTOR:
        case COMPOSITION:
            erg += freeself_integervector(a); 
            break;
        case GALOISRING:
            erg += freeself_galois(a); 
            break;
#endif /* VECTORTRUE */
        default: 
            erg +=  WTO("freeself(1)",a); 
            break;
        };
    CTO(EMPTY,"freeself(e1)",a);
    ENDR("freeself");
    }

INT copy(a,b) OP a, b;
/* AK 280689 V1.0 */ /* AK 201289 V1.1 */ /* AK 050891 V1.3 */
    {
    INT erg = OK;
    if (sym_timelimit > 0L)
        check_time();

    if (a == b) return(OK);
    COP("copy(1)",a);
    COP("copy(2)",b);
    FREESELF(b);
 
    switch(S_O_K(a))
        {
        case EMPTY:
            break;
#ifdef BINTREETRUE
        case BINTREE : 
            erg += copy_bintree(a,b);
            break;
#endif /* BINTREETRUE */

#ifdef BRUCHTRUE
        case BRUCH : 
            erg += copy_bruch(a,b);
            break;
#endif /* BRUCHTRUE */

#ifdef FFTRUE
        case FF: 
            erg += copy_ff(a,b);
            break;
#endif /* FFTRUE */

#ifdef INTEGERTRUE
        case INTEGER : 
            COPY_INTEGER(a,b);
            break;    
#endif /* INTEGERTRUE */

#ifdef LISTTRUE
        case POLYNOM: case GRAL: 
        case MONOPOLY:
        case SCHUBERT: case LIST : 
            erg += copy_list(a,b);
            break;
        case SCHUR:
            erg += copy_schur(a,b);
            break;
        case HOMSYM:
            erg += copy_homsym(a,b);
            break;
        case MONOMIAL:
            erg += copy_monomial(a,b);
            break;
        case POWSYM:
            erg += copy_powsym(a,b);
            break;
        case ELMSYM:
            erg += copy_elmsym(a,b);
            break;

#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT : 
            erg += copy_longint(a,b);
            break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case INTEGERMATRIX: 
            erg += copy_integermatrix(a,b);
            break;
        case KRANZTYPUS : 
            erg += copy_kranztypus(a,b);
            break;
        case KOSTKA :
        case MATRIX : 
            erg += copy_matrix(a,b);
            break;
            
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM : 
            erg += copy_monom(a,b);
            break;
#endif /* MONOMTRUE */
#ifdef NUMBERTRUE
        case SQ_RADICAL:
        case CYCLOTOMIC: erg += copy_number(a,b);break;
#endif /* NUMBERTRUE */
#ifdef PARTTRUE
        case AUG_PART :
        case PARTITION : erg += copy_partition(a,b);break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION : erg += copy_permutation(a,b);break;
#endif /* PERMTRUE */
#ifdef REIHETRUE
        case REIHE : erg += copy_reihe(a,b);break;
#endif /* REIHETRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION : erg += copy_skewpartition(a,b);break;
#endif /* SKEWPARTTRUE */
#ifdef CHARTRUE
        case SYMCHAR : erg += copy_symchar(a,b);break;
#endif /* CHARTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX : erg += copy_tableaux(a,b);break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case HASHTABLE:
            erg += copy_hashtable(a,b);
            break;
        case COMPOSITION: 
            erg += copy_composition(a,b);
            break;
        case WORD: 
            erg += copy_word(a,b);
            break;
        case KRANZ: 
            erg += copy_kranz(a,b);
            break;
        case SUBSET:
            erg += copy_subset(a,b);
            break;
        case LAURENT:
            erg += copy_laurent(a,b);
            break;
        case QUEUE:   
            erg += copy_queue(a,b);
            break;
        case VECTOR:   
            erg += copy_vector(a,b);
            break;
        case INTEGERVECTOR:
            erg += copy_integervector(a,b); break;
	case GALOISRING:
            erg += copy_galois(a,b); break;
        case BITVECTOR:
            erg += copy_bitvector(a,b); break;
#endif /* VECTORTRUE */
        default: 
            erg+= WTO("copy(1)",a);
            break;
        };

    ENDR("copy");
    }

INT append_apply(a,b) OP a,b;
/* AK 060901 */
/* a := [a1,...,ak,b1,...,bl] */
{
    INT erg = OK;
    COP("append_apply(1)",a);
    COP("append_apply(2)",b);
    /* a and b may be equal here */
    switch(S_O_K(a))
        {
#ifdef PARTTRUE
        case PARTITION :  
            erg += append_apply_part(a,b);
            break;
#endif /* PARTTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case WORD:
        case QUEUE:
        case COMPOSITION:
        case SUBSET:
        case VECTOR :  
            erg += append_apply_vector(a,b);
            break;
#endif /* VECTORTRUE */
        default: 
            erg+= WTO("append_apply",a); 
            break;
        };
    ENDR("append_apply");
}

INT append(a,b,e) OP a,b,e;
/* AK 280689 V1.0 */ /* AK 221289 V1.1 */
/* AK 190291 V1.2 */ /* AK 090891 V1.3 */
/* e := [a1,...,ak,b1,...,bl] */
/* AK 241006 V3.1 */
    {
    INT erg = OK;
    if (a == e) {
        erg += append_apply(a,b);
        goto endr_ende;
        }
    CE3(a,b,e,append);

    if (EMPTYP(b)) {
        erg += copy(a,e);
        goto endr_ende;
        }
    switch(S_O_K(a))
        {
	case LIST: /* missing */
	    NYI("append with lists");
	    break;
#ifdef PARTTRUE
        case PARTITION :  
	    erg += append_part_part(a,b,e);
            break;
#endif /* PARTTRUE */

#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case WORD:
        case QUEUE:
        case COMPOSITION:
        case SUBSET:
        case VECTOR :  
            erg += append_vector(a,b,e);
            break;
#endif /* VECTORTRUE */
        default: erg+= WTO("append",a); break;
        };
    ENDR("append");
    }


INT scalarp(a) OP a;
/* test ob scalarer datentyp
 Fri Mar  3 12:43:30 MEZ 1989
AK wahr falls INTEGER,LONGINT,BRUCH */
/* AK 280689 V1.0 */ /* AK 221289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("scalarp(1)",a);
    switch(S_O_K(a))
        {
        case BRUCH:
        case INTEGER:
        case LONGINT:
            return(TRUE);
        default:
            return(FALSE);
        }
    ENDR("scalarp");
    }

INT dynamicp(a) OP a;
/* test ob dynamische datenstruktur */
/* Tue Jan 10 07:16:33 MEZ 1989 */
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 050891 V1.3 */
    {
    INT erg = OK;
    COP("dynamicp",a);
    switch (S_O_K(a))
        {
        case GRAL: case HOM_SYM: case POW_SYM: case BINTREE:
        case MONOPOLY: case SCHUR: case SCHUBERT: case LIST:
        case ELM_SYM: case MONOMIAL: case POLYNOM:
            return(TRUE);
        default:
            return(FALSE);
        }
    ENDR("dynamicp");
    }



INT nullp(a) OP a;
/* 290388  aus macro */ /* AK 280689 V1.0 */ /* AK 081289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    EOP("nullp(1)",a);

    switch (S_O_K(a))
        {
#ifdef BRUCHTRUE
        case BRUCH: return(NULLP_BRUCH(a));
#endif /* BRUCHTRUE */
        case INTEGER:  return (NULLP_INTEGER(a)); 
#ifdef FFTRUE
        case FF:  return nullp_ff(a);
#endif /* FFTRUE */
#ifdef GRTRUE
        case GALOISRING:  return nullp_galois(a);
#endif /* GRTRUE */
#ifdef LONGINTTRUE
        case LONGINT: return nullp_longint(a);
#endif /* LONGINTTRUE */
#ifdef CYCLOTRUE
        case CYCLOTOMIC: return nullp_cyclo(a);
#endif /* CYCLOTRUE */
#ifdef MONOPOLYTRUE
        case MONOPOLY: return nullp_monopoly(a); /* AK 290395 */
#endif /* MONOPOLYTRUE */
#ifdef MATRIXTRUE
        case INTEGERMATRIX: 
            return nullp_integermatrix(a); 
        case MATRIX: 
            return nullp_matrix(a);
#endif /* MATRIXTRUE */
#ifdef SQRADTRUE
        case SQ_RADICAL: return nullp_sqrad(a);
#endif /* SQRADTRUE */
#ifdef SCHUBERTTRUE
        case SCHUBERT: return nullp_schubert(a); /* AL 180393 */
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE
        case ELM_SYM: return nullp_elmsym(a);
        case POW_SYM: return nullp_powsym(a);
        case HOM_SYM: return nullp_homsym(a);
        case MONOMIAL: return nullp_monomial(a);
        case SCHUR: return nullp_schur(a);
#endif /* SCHURTRUE */
#ifdef CHARTRUE
        case SYMCHAR: return nullp_symchar(a); /* AK 010692 */
#endif /* CHARTRUE */
#ifdef POLYTRUE
        case POLYNOM: return nullp_polynom(a);
#endif /* POLYTRUE */
#ifdef REIHETRUE
        case REIHE: return nullp_reihe(a);
#endif /* REIHETRUE */
#ifdef VECTORTRUE  /* AK 311091 */
        case INTEGERVECTOR: return nullp_integervector(a);
        case VECTOR: return nullp_vector(a);
        case BITVECTOR: return nullp_bitvector(a);
        case HASHTABLE: return nullp_integer(S_V_I(a,S_V_LI(a)));
#endif /* VECTORTRUE */

        case MONOM: return NULLP(S_MO_K(a));
                
        default:  
            WTO("nullp",a);
        };
    ENDR("nullp");
    }

INT bit(a,i) OP a; INT i;
/* returns the i-th bit of a */
/* in the case of longint with out sign */
/* AK 200902 V2.1 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"bit(1)",a);
    SYMCHECK(i<0,"bit: neg index");
    {
    if (S_O_K(a) == INTEGER)
       {
       INT l;
       if (i>=32) return 0;
       l = S_I_I(a);
       return (l>>i)&1;
       }
    else
       {
       return bit_longint(a,i);
       }
    }
    ENDR("bit");
} 

INT eins_default(a,b) OP a,b;
/* AK 200902 V2.1 */
{
    INT erg = OK;
    erg += m_i_i(1,b);
    cast_apply(S_O_K(a),b);
    ENDR("eins_default");
}

INT eins(a,b) OP a,b;
/* a any object b becomes identity in the object class of a */
/* AK 200902 V2.1 */ /* AK 120804 V3.0 */
/* AK 231106 V3.1 */
{
    INT erg = OK;
    EOP("eins(1)",a);
    switch(S_O_K(a)) {
        case BRUCH: /* AK 120804 */
        case INTEGER:
        case LONGINT: 
            erg += m_i_i(1,b); 
            break;
	case GALOISRING:
	    erg += eins_galois(a,b);
	    break;
        case FF:
            erg += eins_ff(a,b);
            break;
        case MATRIX:
        case INTEGERMATRIX:
            if (S_M_HI(a)==S_M_LI(a)) {
                INT i,j;
                erg += m_lh_m(S_M_L(a),S_M_H(a),b);
                C_O_K(b,S_O_K(a));
                for (i=0;i<S_M_HI(b);i++)
                for (j=0;j<S_M_LI(b);j++)
                    if (i==j) eins(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
                    else null(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
                }
            else
                error("eins:only for quadratic matrices");
            break;    
        case PERMUTATION:
            erg += first_permutation(S_P_L(a),b);
            break;
        case KRANZ: /* AK 120804 */
            {
            INT i;
            COPY(a,b);
            erg += eins(S_KR_G(a),S_KR_G(b));
            for (i=0;i<S_KR_GLI(a);i++)
                eins(S_KR_I(a,i),S_KR_I(b,i));
            }
            break;
	case POLYNOM: /* AK 271005 */
            {
            if (S_L_S(a) != NULL) {
                OP dd=CALLOCOBJECT();
                eins(S_PO_K(a),dd);
                m_scalar_polynom(dd,b);
                FREEALL(dd);
                }
            else {
                 m_scalar_polynom(cons_eins,b);
                 }
            }
            break;
	case MONOPOLY: /* AK 271005 */
            {
            if (S_L_S(a) != NULL) {
                OP dd=CALLOCOBJECT();
                eins(S_PO_K(a),dd);
                m_skn_mp(cons_null,dd,NULL,b);
                FREEALL(dd);
                }
            else {
                 m_skn_mp(cons_null,cons_eins,NULL,b);
                 }
            }
	    break;
        default: 
            erg += eins_default(a,b);
            break;
        }
    ENDR("eins");     
}

INT null_default(a,b) OP a,b;
/* AK 200902 V2.1 */
{
    INT erg = OK;
    erg += m_i_i(0,b);
    cast_apply(S_O_K(a),b);
    ENDR("eins_default");
}


INT null(a,b) OP a,b;
/* a any object b becomes zero in the object class */
/* AK 200902 V2,1 */
{
    INT erg = OK;
    EOP("null(1)",a);
    switch(S_O_K(a)) {
	case GALOISRING:
            erg += null_galois(a,b);
            break;
        case FF:
            erg += null_ff(a,b);
            break;
        case INTEGER:
        case LONGINT:
            erg += m_i_i(0,b);
            break;
        case POLYNOM:
        case SCHUR:
        case HOMSYM:
        case ELMSYM:
        case POWSYM:
        case MONOMIAL:
        case MONOPOLY:
            erg += init(S_O_K(a),b);
            break;
        default: 
            erg += null_default(a,b);
            break;
        }
    ENDR("null");
}  

INT einsp(a) OP a;
/* TRUE if a is unity */
/* 290388  aus macro */ /* AK 280689 V1.0 */ /* AK 081289 V1.1 */
/* AK 250291 V1.2 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT erg = OK;
    COP("einsp",a);
    switch (S_O_K(a)) {


#ifdef BRUCHTRUE
        case BRUCH:  return einsp_bruch(a);
#endif /* BRUCHTRUE */

#ifdef FFTRUE
        case FF:  return einsp_ff(a);
#endif /* FFTRUE */



#ifdef GRTRUE
        case GALOISRING:  return einsp_galois(a);
#endif /* GRTRUE */


        case INTEGER:  return einsp_integer(a);

#ifdef LONGINTTRUE
        case LONGINT:  return einsp_longint(a);
#endif /* LONGINTTRUE */


#ifdef MATRIXTRUE
        case MATRIX: return einsp_matrix(a);
#endif /* MATRIXTRUE */

#ifdef REIHETRUE
        case REIHE: return einsp_reihe(a);
#endif /* REIHETRUE */

#ifdef KRANZTRUE
        case KRANZ:  return einsp_kranz(a);
#endif /* KRANZTRUE */

#ifdef PERMTRUE
        case PERMUTATION:  return einsp_permutation(a);
#endif /* PERMTRUE */

#ifdef POLYTRUE
        case POLYNOM:  return einsp_polynom(a);
        case GRAL:
        case MONOPOLY: return einsp_monopoly(a);
#endif

#ifdef SQRADTRUE
        case SQ_RADICAL: return einsp_sqrad(a);
#endif
#ifdef CYCLOTRUE
        case CYCLOTOMIC: return einsp_cyclotomic(a);
#endif

#ifdef SCHURTRUE
        case ELM_SYM: return einsp_elmsym(a);
        case POW_SYM: return einsp_powsym(a);
        case HOM_SYM: return einsp_homsym(a);
        case MONOMIAL: return einsp_monomial(a);
        case SCHUR: return einsp_schur(a);
#endif /* SCHURTRUE */
#ifdef SCHUBERTTRUE
        case SCHUBERT: return einsp_schubert(a);
#endif /* SCHUBERTTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR:
            return einsp_integervector(a); 
        case VECTOR: return einsp_vector(a); 
#endif
#ifdef CHARTRUE
        case SYMCHAR: return einsp_symchar(a); 
#endif /* CHARTRUE */
        default:  
            WTO("einsp(1)",a);
        };
    ENDR("einsp");
    }

INT negeinsp(a) OP a;
/* AK 181289 V1.1 */ /* AK 250291 V1.2 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    EOP("negeinsp(1)",a);

    switch (S_O_K(a))
        {

#ifdef BRUCHTRUE
        case BRUCH:  
            return(negeinsp_bruch(a));
#endif /* BRUCHTRUE */

#ifdef INTEGERTRUE
        case INTEGER:  
            return(NEGEINSP_INTEGER(a));
#endif /* INTEGERTRUE */

#ifdef LONGINTTRUE
        case LONGINT:  
            return negeinsp_longint(a);
#endif /* LONGINTTRUE */

#ifdef POLYTRUE
        case POLYNOM:  return negeinsp_polynom(a);
#endif

        default:  
            WTO("negeinsp(1)",a);
        };
        ENDR("negeinsp");
    }

INT vexillaryp(a,part) OP a,part;
/* AK 290986 */
/* part ist die Partition zugehoerig zur permutation */
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    switch(S_O_K(a))
        {
#ifdef PERMTRUE
        case PERMUTATION : 
            return vexillaryp_permutation(a,part);
#endif /* PERMTRUE */
        default: 
            WTO("vexillary(1)",a); 
        };
    ENDR("vexillaryp");
    }

INT lastp(a) OP a;
/*  AK 250986 */ /* AK 280689 V1.0 */ /* AK 181289 V1.1 */
/* AK 200691 V1.2 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    EOP("lastp(1)",a);

    switch(S_O_K(a)) {
#ifdef LISTTRUE
        case HOM_SYM : 
        case POW_SYM : 
        case GRAL : 
        case POLYNOM :     
        case MONOPOLY: 
        case SCHUBERT : 
        case SCHUR :  
        case ELM_SYM:
        case MONOMIAL: 
        case LIST : 
            return(lastp_list(a));
#endif /* LISTTRUE */
        default:  
            WTO("lastp(1)",a);
        };
    ENDR("lastp");
    }
    
INT odd(a) OP a;
/* AK 210291 V1.2 */ /* AK 210891 V1.3 */
    {
    return not even(a);
    }

INT even(a) OP a;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210291 V1.2 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    EOP("even(1)",a);
    switch(S_O_K(a))
        {
#ifdef INTEGERTRUE
        case INTEGER : return even_integer(a);
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
        case LONGINT : return even_longint(a);
#endif /* LONGINTTRUE */
#ifdef PARTTRUE
        case PARTITION : return even_partition(a); /* AK 300992 */
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION : return even_permutation(a); /* AK 010692 */
#endif /* PERMTRUE */
        default: WTO("even",a);goto endr_ende;
        };
    ENDR("even");
    }

INT negp(a) OP a;
/* AK 190888 */ /* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
/* AK V2.0 221298 */
/* true if a < 0 */
/* AK 151204 V3.0 */
    {
    INT erg = OK;
    COP("negp",a);
    switch(S_O_K(a))
        {
#ifdef BRUCHTRUE
        case BRUCH : return negp_bruch(a);
#endif /* BRUCHTRUE */
#ifdef INTEGERTRUE
        case INTEGER : return negp_integer(a);
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
        case LONGINT : return negp_longint(a);
#endif /* LONGINTTRUE */
#ifdef POLYTRUE        /* AK V2.0 221298 */
            /* true if all coeffs < 0 */
        case SCHUBERT:
        case GRAL:
        case SCHUR:
        case ELM_SYM:
        case POW_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case MONOPOLY:
        case POLYNOM:
                return negp_polynom(a);
#endif /* POLYTRUE */

        default: WTO("negp",a);goto endr_ende;
        };

    ENDR("negp");
    }

INT posp(a) OP a;
/* AK 190888 */ /* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
/* AK 190298 V2.0 */
/* TRUE if > 0 */
/* changed from >= 0 to >0 041001 AK */
/* AK 151204 V3.0 */
    {
    INT erg = OK;
    COP("posp",a);
    switch(S_O_K(a))
        {
#ifdef BRUCHTRUE
        case BRUCH : return posp_bruch(a) ;
#endif /* BRUCHTRUE */
#ifdef INTEGERTRUE
        case INTEGER : return POSP_INTEGER(a) ;
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
        case LONGINT : return posp_longint(a) ;
#endif /* LONGINTTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case VECTOR : return posp_vector(a) ;
#endif /* VECTORTRUE */
#ifdef POLYTRUE        /* AK V2.0 221298 */
            /* true if all coeffs > 0 */
        case SCHUBERT:
        case GRAL:
        case SCHUR:
        case ELM_SYM:
        case POW_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case MONOPOLY:
        case POLYNOM:
                return posp_polynom(a);
#endif /* POLYTRUE */
        default: 
            erg +=  WTO("posp",a); 
            goto endr_ende;
        };
    ENDR("posp");
    }

INT comp(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 281289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("comp(1)",a);
    COP("comp(2)",b);
    if (EMPTYP(a) && EMPTYP(b)) return(0L);
    else if (EMPTYP(a)) return(-1L);
    else if (EMPTYP(b)) return(1L);
    else switch(S_O_K(a)){
#ifdef BRUCHTRUE
        case BRUCH : return comp_bruch(a,b);
#endif /* BRUCHTRUE */
#ifdef FFTRUE
        case FF :    return comp_ff(a,b);
#endif /* FFTRUE */
#ifdef INTEGERTRUE
        case INTEGER : 
            if (S_O_K(b) == INTEGER)
                return ( S_I_I(a) > S_I_I(b) ? 1L : 
                     S_I_I(a) == S_I_I(b) ? 0L : -1L );
            else
            return comp_integer(a,b);
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
        case LONGINT : return comp_longint(a,b);
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case KRANZTYPUS :return comp_kranztafel(a,b);
        case INTEGERMATRIX: return comp_integermatrix(a,b);
        case MATRIX : return comp_matrix(a,b);
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM :    return comp_monom(a,b);
#endif /* MONOMTRUE */
#ifdef LISTTRUE
        case SCHUBERT:
        case GRAL:
        case SCHUR:
        case ELM_SYM:
        case POW_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case LIST : return comp_list(a,b);
        case POLYNOM:
                return comp_polynom(a,b);
        case MONOPOLY:
                return comp_monopoly(a,b);
#endif /* LISTTRUE */
#ifdef PARTTRUE
        case PARTITION: return comp_partition(a,b);
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION: return comp_permutation(a,b);
#endif /* PERMTRUE */
#ifdef REIHETRUE
        case REIHE: return comp_reihe(a,b);
#endif /* REIHETRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: return comp_skewpartition(a,b);
#endif /* SKEWPARTTRUE */
#ifdef CHARTRUE
        case SYMCHAR: return comp_symchar(a,b);
#endif /* CHARTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX :    /* 060588 */
            return comp_tableaux(a,b);
#endif /* TABLEAUXTRUE */
#ifdef WORDTRUE
        case WORD:
            return comp_word(a,b);
#endif /* WORDTRUE */
#ifdef VECTORTRUE
        case BITVECTOR: /* AK 200395 */
            return comp_bv(a,b);
        case VECTOR: 
            return comp_vector(a,b);
        case INTEGERVECTOR:
        case COMPOSITION: 
        case SUBSET:
            return comp_integervector(a,b);
	case GALOISRING:
		return comp_galois(a,b);
#endif /* VECTORTRUE */
        default: return WTT("comp",a,b);
        }
    ENDR("comp");
    }

INT lt(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
/* AK 161204 V3.0 */
    {
    INT erg = OK;
    COP("lt(1)",a);
    COP("lt(2)",b);
    if (comp(a,b) < 0L) return(TRUE);
    return(FALSE);
    ENDR("lt");
    }

INT eq(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
/* AK 161204 V3.0 */
    {
    INT erg = OK;
    COP("eq(1)",a);
    COP("eq(2)",b);
    switch (S_O_K(a)) {
        case INTEGER: 
            return eq_integer(a,b);
        case PARTITION: 
            return eq_partition(a,b);
        case PERMUTATION: 
            return eq_permutation(a,b);
        case VECTOR: 
            return eq_vector(a,b);
        case CYCLOTOMIC:
            return eq_cyclotomic(a,b);
        case SQ_RADICAL:
            return eq_sqrad(a,b);
        case INTEGERMATRIX:
        case MATRIX:
        case KRANZTYPUS:
            return eq_matrix(a,b); /* AK 110703 */
        case INTEGERVECTOR: /* AK 280804 */
            if (S_O_K(b)==INTEGERVECTOR) 
                return eq_integervector_integervector(a,b);
            else if (comp(a,b) == 0L) return(TRUE);
            else return FALSE;
        default:
            /* AK 051207 if (S_O_K(a) != S_O_K(b)) return FALSE; */	
	    
            if (comp(a,b) == 0L) return(TRUE);
        }
    ENDR("eq");
    }

INT neq(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("neq(1)",a);
    COP("neq(2)",b);
    return not eq(a,b);
    ENDR("neq");
    }

INT gr(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    if (comp(a,b) > 0L) return(TRUE);
    return(FALSE);
    }

INT ge(a,b) OP a,b;
/* AK 260789 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    if (comp(a,b) >= 0L) return(TRUE);
    return(FALSE);
    }

INT gt(a,b) OP a,b;
/* AK 010889 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    if (S_O_K(a) == INTEGER)
        if (S_O_K(b) == INTEGER) return ((S_I_I(a) > S_I_I(b))? TRUE:FALSE);
        
    if (comp(a,b) > 0L) return(TRUE);
    return(FALSE);
    }



INT le(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    if (comp(a,b) > 0L) return(FALSE);
    return(TRUE);
    }

INT listp(a) OP a;
/* AK 030789 V1.0 */ /* AK 160890 V1.1 */ /* AK 060891 V1.3 */
    {
    OBJECTKIND kind = S_O_K(a);
    if (    kind == LIST || 
        kind == POLYNOM || 
        kind == MONOPOLY || 
        kind == GRAL || 
        kind == HOM_SYM || 
        kind == POW_SYM || 
        kind == ELM_SYM || 
        kind == MONOMIAL || 
        kind == SCHUR || 
        kind == SCHUBERT
            ) return(TRUE);
    else return(FALSE);
    }
        
INT factorize(a,b) OP a,b;
/* AK 290304 */
/* decomposition into factors, i.e. a vector of factors */
/* the factors are ordered */
/* AK 281106 V3.1 */
{
    INT erg = OK;
    CE2(a,b,factorize);
    FREESELF(b);
    switch(S_O_K(a))
        {
        case INTEGER: erg+=factorize_integer(a,b); goto endr_ende;
        case LONGINT: NYI("factorize for longint"); goto endr_ende;
        case POLYNOM: NYI("factorize for polynom"); goto endr_ende;
        default: WTO("factorize",a);
        }
    ENDR("factorize");
}

#ifdef INTEGERTRUE
INT factorize_integer(a,b) OP a,b;
/* AK 060690 V1.1 */ /* AK 060891 V1.3 */ /* AK 220998 V2.0 */
/* input: INTEGER object a
   output:INTEGERVECTOR of prim factors in increasing order */
{
    INT erg = OK;
    CTO(INTEGER,"factorize_integer(1)",a);
    
        {
        INT ai = S_I_I(a);
        INT i=2L;
        m_il_v((INT)0,b);
        while (i <= ai) 
            {
            if (ai % i == 0L) {
                INC(b);
                M_I_I(i,S_V_I(b,S_V_LI(b)-1L));
                ai = ai / i; continue; }
            i++;
            }
        }

    ENDR("factorize_integer");
}
#endif /* INTEGERTRUE */


#ifdef BRUCHTRUE
INT invers_apply_integer(a) OP a;
/* AK 140591 V1.2 */ /* AK 060891 V1.3 */
    { 
    INT erg = OK;
    CTO(INTEGER,"invers_apply_integer",a);
    SYMCHECK(S_I_I(a) == 0,"invers_apply_integer:zero");
    if (S_I_I(a) == 1) goto endr_ende;
    if (S_I_I(a) == -1) { 
             M_I_I(-S_I_I(a),a);
             goto endr_ende; }
    erg += m_ioiu_b(1L, S_I_I(a), a);
    ENDR("invers_apply_integer");
    }
#endif /* BRUCHTRUE */

INT addinvers_apply_integer(a) OP a;
/* AK 201289 V1.1 */ /* AK 140591 V1.2 */ /* AK 060891 V1.3 */
    { 
    INT erg = OK;
    CTO(INTEGER,"addinvers_apply_integer",a);
    M_I_I(- S_I_I(a), a);
    ENDR("addinvers_apply_integer");
    }


INT addinvers_integer(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 131289 V1.1 */ /* AK 060891 V1.3 */
    { 
    INT erg = OK;
    CTO(INTEGER,"addinvers_integer(1)",a);
    CTO(EMPTY,"addinvers_integer(2)",b);
    M_I_I(- S_I_I(a), b);
    ENDR("addinvers_integer");
    }

INT inc_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    { 
    INT erg = OK;
    CTO(INTEGER,"inc_integer(1)",a);
    C_I_I(a,S_I_I(a)+1L); 
    ENDR("inc_integer");
    }

INT dec_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    { 
    INT erg = OK;
    CTO(INTEGER,"dec_integer(1)",a);
    C_I_I(a,S_I_I(a)-1L); 
    ENDR("dec_integer");
    }

INT hoch_integer_integer(a,b,c) OP a,b,c;
{
    INT erg = OK;
    INT i;
    OP d;
    CTTO(LONGINT,INTEGER,"hoch_integer_integer(1)",a);
    CTO(INTEGER,"hoch_integer_integer(2)",b);
    CTO(EMPTY,"hoch_integer_integer(3)",c);
    if (NULLP_INTEGER(b)) {
        M_I_I(1,c);
        goto ende;
        }
    if (NEGP_INTEGER(b)) {
        erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),c);
        M_I_I(1,S_B_O(c));
        C_B_I(c,GEKUERZT);
        ADDINVERS_APPLY_INTEGER(b);
        erg += hoch_integer_integer(a,b,S_B_U(c));
        ADDINVERS_APPLY_INTEGER(b);
        goto ende;
        }
    if (EINSP_INTEGER(b)) {
        COPY(a,c);
        goto ende;
        }
    SYMCHECK((S_I_I(b) <= 1), "hoch_integer_integer:(i1)");

    i = S_I_I(b);
    d = CALLOCOBJECT();
    COPY(a,d);
    M_I_I(1,c);
    while(i) {
        if ( i % 2 == 1)
            {
            MULT_APPLY(d,c);
            }
            
        erg += square_apply(d);
        i /=  2;
    }
    
    FREEALL(d);
ende:
    CTTO(INTEGER,LONGINT,"hoch_integer_integer(e3)",c);
    ENDR("hoch_integer_integer");
}

INT hoch_longint_integer(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(LONGINT,"hoch_longint_integer(1)",a);
    CTO(INTEGER,"hoch_longint_integer(2)",b);
    CTO(EMPTY,"hoch_longint_integer(3)",c);
    erg += hoch_integer_integer(a,b,c);
    ENDR("hoch_longint_integer");
}

INT hoch_longint_longint(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(LONGINT,"hoch_longint_longint(1)",a);
    CTO(LONGINT,"hoch_longint_longint(2)",b);
    CTO(EMPTY,"hoch_longint_longint(3)",c);
    NYI("hoch_longint_longint");
    ENDR("hoch_longint_longint");
}

INT hoch_integer_longint(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(INTEGER,"hoch_integer_longint(1)",a);
    CTO(LONGINT,"hoch_integer_longint(2)",b);
    CTO(EMPTY,"hoch_integer_longint(3)",c);
    NYI("hoch_integer_longint");
    ENDR("hoch_integer_longint");
}

INT hoch_default();
INT hoch_bruch_integer(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(BRUCH,"hoch_bruch_integer(1)",a);
    CTO(INTEGER,"hoch_bruch_integer(2)",b);
    CTO(EMPTY,"hoch_bruch_integer(3)",c);
    erg += hoch_default(a,b,c);
    ENDR("hoch_bruch_integer");
}
 
INT hoch_bruch_longint(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(BRUCH,"hoch_bruch_longint(1)",a);
    CTO(LONGINT,"hoch_bruch_longint(2)",b);
    CTO(EMPTY,"hoch_bruch_longint(3)",c);
    erg += hoch_default(a,b,c);
    ENDR("hoch_bruch_longint");
}



INT hoch_integer(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(INTEGER,"hoch_integer(1)",a);
    CTO(EMPTY,"hoch_integer(3)",c);
    if (S_O_K(b) == INTEGER)
        erg += hoch_integer_integer(a,b,c);
    else if (S_O_K(b) == LONGINT) 
         erg += hoch_integer_longint(a,b,c);
    else
         erg += hoch_default(a,b,c);
    ENDR("hoch_integer");
}

INT hoch_longint(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(LONGINT,"hoch_longint(1)",a);
    CTO(EMPTY,"hoch_longint(3)",c);
    if (S_O_K(b) == INTEGER)
        erg += hoch_longint_integer(a,b,c);
    else if (S_O_K(b) == LONGINT)
         erg += hoch_longint_longint(a,b,c);
    else
         erg += hoch_default(a,b,c);
    ENDR("hoch_longint");
}

INT hoch_bruch(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(BRUCH,"hoch_bruch(1)",a);
    CTO(EMPTY,"hoch_bruch(3)",c);
    if (S_O_K(b) == INTEGER)
        erg += hoch_bruch_integer(a,b,c);
    else if (S_O_K(b) == LONGINT)
         erg += hoch_bruch_longint(a,b,c);
    else
         erg += hoch_default(a,b,c);
    ENDR("hoch_bruch");
}

INT mult_integer_integer(a,b,d) OP a,b,d;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    {
    INT l,erg = OK;
    CTO(INTEGER,"mult_integer_integer(1)",a);
    CTO(INTEGER,"mult_integer_integer(2)",b);
    CTO(EMPTY,"mult_integer_integer(3)",d);

    l=INTLOG(a) + INTLOG(b);
    if ( l > 9) 
            {
#ifdef LONGINTTRUE
            OP c= CALLOCOBJECT(); 
            erg += t_int_longint(a,c);
            erg += mult_longint_integer(c,b,d); 
            FREEALL(c); 
#else /* LONGINTTRUE */
            erg += error("mult_integer_integer:no LONGINT");
#endif /* LONGINTTRUE */
            goto endr_ende;
            }

    M_I_I(S_I_I(a)*S_I_I(b),d);
    ENDR("mult_integer_integer");
    }

INT mult_integer_longint(a,b,c) OP a,b,c;
    {
    INT erg = OK;
    CTO(INTEGER,"mult_integer_longint",a);
    CTO(LONGINT,"mult_integer_longint",b);
    CTO(EMPTY,"mult_integer_longint",c);

    erg += mult_longint_integer(b,a,c);

    ENDR("mult_integer_longint");
    }

INT mult_integer_bruch(a,b,c) OP a,b,c;
    {
    INT erg = OK;
    CTO(INTEGER,"mult_integer_bruch",a);
    CTO(BRUCH,"mult_integer_bruch",b);
    CTO(EMPTY,"mult_integer_bruch",c);

    erg += mult_bruch_integer(b,a,c);

    ENDR("mult_integer_bruch");
    }

INT mult_integer(a,b,d) OP a,b,d;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    {
    INT erg=OK;
    CTO(INTEGER,"mult_integer(1)",a);
    CTTO(EMPTY,INTEGER,"mult_integer(3)",d);
    EOP("mult_integer(2)",b);

    if (S_O_K(d)==INTEGER) C_O_K(d,EMPTY);
    switch(S_O_K(b)) {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += mult_bruch_integer(b,a,d);
            goto ende;
#endif /* BRUCHTRUE */

        case INTEGER: 
            erg += mult_integer_integer(a,b,d);
            goto ende;

#ifdef LONGINTTRUE
        case LONGINT: 
            erg += mult_longint_integer(b,a,d);
            goto ende;
#endif /* LONGINTTRUE */

#ifdef MATRIXTRUE
        case KRANZTYPUS :
        case MATRIX:  
            erg += mult_scalar_matrix(a,b,d);
            goto ende;
#endif /* MATRIXTRUE */

#ifdef MONOMTRUE
        case MONOM: 
            erg += mult_integer_monom(a,b,d);
            goto ende;
#endif /* MONOMTRUE */

#ifdef POLYTRUE
        case POW_SYM:
            erg += mult_powsym_scalar(b,a,d);
            goto ende;
        case ELM_SYM:
            erg += mult_elmsym_scalar(b,a,d);
            goto ende;
        case HOM_SYM:
            erg += mult_homsym_scalar(b,a,d);
            goto ende;
        case MONOMIAL:
            erg += mult_monomial_scalar(b,a,d);
            goto ende;
        case SCHUR:
            erg += mult_schur_scalar(b,a,d);
            goto ende;
#ifdef SCHUBERTTRUE
        case SCHUBERT:
            erg += mult_scalar_schubert(a,b,d);
            goto ende;
#endif
        case GRAL:
            erg += mult_scalar_gral(a,b,d);
            goto ende;
        case POLYNOM: 
            erg += mult_scalar_polynom(a,b,d);
            goto ende;
        case MONOPOLY:
            erg += mult_scalar_monopoly(a,b,d);
            goto ende;
#endif /* POLYTRUE */

#ifdef LAURENTTRUE
        case LAURENT:
            {
            OP c = callocobject();
            erg += t_INTEGER_LAURENT(a,c);
            erg += mult_laurent(c,b,d);
            erg += freeall(c);
            }
            goto ende;
#endif /* LAURENTTRUE */
     
#ifdef SQRADTRUE
        case SQ_RADICAL:
            erg += mult_scalar_sqrad(a,b,d);
            goto ende;
#endif /* SQRADDTRUE */

#ifdef CYCLOTRUE
        case CYCLOTOMIC:
            erg += mult_scalar_cyclo(a,b,d);
            goto ende;
#endif /* CYCLOTRUE */

#ifdef CHARTRUE
        case SYMCHAR: 
            erg += mult_scalar_symchar(a,b,d);
            goto ende;
#endif /* CHARTRUE */

#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case VECTOR: 
            erg += mult_scalar_vector(a,b,d);
            goto ende;
#endif /* VECTORTRUE */

#ifdef FFTRUE
        case FF:
            erg += cast_apply_ff(a);
            erg += mult_ff(a,b,d);
            goto ende;
#endif /* FFTRUE */

        case HASHTABLE:
            erg += mult_integer_hashtable(a,b,d);
            goto ende;

        default:
            WTO("mult_integer(2)",b);
            goto ende;
        }
ende:
    ENDR("mult_integer");
    }

INT even_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    { 
    return(S_I_I(a) %2L == 0L); 
    }

INT posp_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    { 
    return(S_I_I(a) >= (INT) 0);
    }

INT negp_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    { 
    return(S_I_I(a) < 0L); 
    }

INT mod_integer_integer(a,b,c) OP a,b,c;
    {
    INT erg = OK;
    CTO(INTEGER,"mod_integer_integer(1)",a);
    CTO(INTEGER,"mod_integer_integer(2)",b);
    CTO(EMPTY,"mod_integer_integer(3)",c);
   
    M_I_I(S_I_I(a) % S_I_I(b),c);
    ENDR("mod_integer");
    }


INT add_integer_integer(a,b,c) OP a,b,c;
/* AK 251001 */
    {
    INT erg = OK,i;
    CTO(INTEGER,"add_integer_integer(1)",a);
    CTO(INTEGER,"add_integer_integer(2)",b);
    CTO(EMPTY,"add_integer_integer(3)",c);

    i = S_I_I(a)+S_I_I(b);
    if (
          ( (S_I_I(a) > 0) && (S_I_I(b) > 0) && (i <= 0) )
          ||
          ( (S_I_I(a) < 0) && (S_I_I(b) < 0) && (i >= 0) )
        )
        {
#ifdef LONGINTTRUE
        OP d;
        d = callocobject();
        erg += t_int_longint(b,d);
        erg += add_longint_integer(d,a,c);
        erg += freeall(d);
#else /* LONGINTTRUE */
        erg += error("add_apply_integer_integer:Overflow no LONGINT");
#endif /* LONGINTTRUE */
        }
    else    {
        M_I_I(i,c);
        }

    ENDR("add_integer_integer");
    }

INT add_integer_longint(a,b,c) OP a,b,c;
/* AK 251001 */
{
    INT erg = OK;
    CTO(INTEGER,"add_integer_longint(1)",a);
    CTO(LONGINT,"add_integer_longint(2)",b);
    CTO(EMPTY,"add_integer_longint(3)",c);

    erg += add_longint_integer(b,a,c);
    ENDR("add_integer_longint");
}

INT add_integer(a,b,c) OP a,b,c;
/* das erste object ist vom typ INTEGER, das ergebnis ist ein leere
object */
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 280291 V1.2 */
/* AK 060891 V1.3 */
    {
    INT erg = OK;
    CTO(INTEGER,"add_integer(1)",a);
    CTO(EMPTY,"add_integer(3)",c);
    EOP("add_integer(2)",b);


    switch(S_O_K(b))
        {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += add_bruch_scalar(b,a,c); 
            goto aiende;
#endif /* BRUCHTRUE */

        case INTEGER: 
            erg += add_integer_integer(a,b,c); 
            goto aiende;

#ifdef LONGINTTRUE
        case LONGINT: 
            erg += add_longint_integer(b,a,c); 
            goto aiende;
#endif  /* LONGINTTRUE */

#ifdef POLYTRUE   /* AK 060891 */
        case POLYNOM: 
            erg += add_scalar_polynom(a,b,c); 
            goto aiende;
#endif /* POLYTRUE */

        case SQ_RADICAL:
            erg += add_scalar_sqrad(a,b,c);
            goto aiende;
        case CYCLOTOMIC:
            erg += add_scalar_cyclo(a,b,c);
            goto aiende;

#ifdef SCHURTRUE /* AK 240102 */
        case SCHUR:
            erg += add_schur(b,a,c);
            goto aiende;
        case HOMSYM:
            erg += add_homsym(b,a,c);
            goto aiende;
        case POWSYM:
            erg += add_powsym(b,a,c);
            goto aiende;
        case ELMSYM:
            erg += add_elmsym(b,a,c);
            goto aiende;
        case MONOMIAL:
            erg += add_monomial(b,a,c);
            goto aiende;
#endif /* SCHURTRUE */
        case MONOPOLY:
            erg += add_scalar_monopoly(a,b,c);
            goto aiende;

        default :
            if (NULLP_INTEGER(a)) 
                COPY(b,c);
            else
                erg += WTO("add_integer(2)",b);
            goto aiende;
        } /* end switch */
aiende:
    ENDR("add_integer");
    }
  
INT eq_integer(a,b) OP a,b;
/* AK 110202 */
{
    INT erg = OK;
    CTO(INTEGER,"eq_integer(1)",a);

    switch(S_O_K(b)) {
        case SQ_RADICAL:
            return FALSE;
        case CYCLOTOMIC:
            return FALSE;
        case EMPTY:
            return FALSE;
         
        default:
            return comp_integer(a,b) == 0;
        }
    
    ENDR("eq_integer");
}

INT comp_integer_integer(a,b) OP a,b;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* AK 281098 V2.0 */
    {
    INT ai = S_I_I(a);
    INT bi = S_I_I(b);
    if (ai == bi) return(0L);
    if (ai > bi) return(1L);
    return(-1L);
    }

INT comp_integer(a,b) OP a,b; 
/* AK 280888 */ /* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* AK 040298 V2.0 */
/* a is of type INTEGER
   type of b is from
        BRUCH, INTEGER, LONGINT, POLYNOM */
    {
    INT erg = OK;
    CTO(INTEGER,"comp_integer(1)",a);

    switch (S_O_K(b))
        {
#ifdef BRUCHTRUE
        case BRUCH: 
             return -1 * comp_bruch_scalar(b,a);
#endif /* BRUCHTRUE */

        case INTEGER:
             return COMP_INTEGER_INTEGER(a,b); 

#ifdef LONGINTTRUE
        case LONGINT: 
             return -1 * comp_longint_integer(b,a);
#endif /* LONGINTTRUE */

#ifdef POLYTRUE
        case POLYNOM: 
             return -1 * comp_polynom_scalar(b,a);
#endif /* POLYTRUE */

        default:
             WTO("comp_integer(2)",b);goto endr_ende;
        }
    ENDR("comp_integer");
    } 



INT quores_integer(a,b,c,d) OP a,b,c,d;
/* AK 280888 */ /* AK 270689 V1.0 */ /* AK 081289 V1.1 */
/* AK 210891 V1.3 */
/* d is always positive */
/* a is integer */
    {
    INT erg = OK;
    CTO(INTEGER,"quores_integer(1)",a);
    CTO(EMPTY,"quores_integer(3)",c);
    CTO(EMPTY,"quores_integer(4)",d);

    switch(S_O_K(b))
        {
        case INTEGER: 
            {
            M_I_I(S_I_I(a) / S_I_I(b), c);
            M_I_I(S_I_I(a) % S_I_I(b), d);
            if ((S_I_I(d) < 0L) && (S_I_I(b) < 0L))
                {
                M_I_I(S_I_I(d)-S_I_I(b),d);
                INC_INTEGER(c);
                }
            if ((S_I_I(d) < 0L) && (S_I_I(b) > 0L))
                {
                M_I_I(S_I_I(d)+S_I_I(b),d);
                DEC_INTEGER(c);
                }
            goto endr_ende;
            }
#ifdef LONGINTTRUE
        case LONGINT:
            {
            if (NULLP_INTEGER(a)) /* AK 020103 */
                {
                M_I_I(0,c);
                M_I_I(0,d);
                }
            else 
                {
                OP e = callocobject(); 
                erg += m_i_longint(S_I_I(a),e);
                erg += quores_longint(e,b,c,d);
                erg += freeall(e);
                }
            goto endr_ende;
            };
#endif /* LONGINTTRUE */
        default: WTT("quores_integer",a,b); goto endr_ende;
        }
    ENDR("quores_integer");
    }

INT nullp_integer(a) OP a;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
/* a is integer */
    { 
    return( (S_I_I(a) == 0L) ? TRUE : FALSE ); 
    }

INT einsp_integer(a) OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
/* a is integer */
    { 
    return ((S_I_I(a) == 1L)?TRUE:FALSE); 
    }

INT negeinsp_integer(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
/* a is integer */
    { 
    return ((S_I_I(a) == -1L)? TRUE : FALSE); 
    }

INT copy_integer(a,c) OP a,c;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    { 
    M_I_I( S_I_I(a),c);
    return OK;
    }
    
#ifdef BRUCHTRUE
INT invers_integer(a,b) OP a,b;
/* AK 031286 */ /* AK 220888 gilt auch bei longint */
/* AK 270689 V1.0 */ /* AK 151289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(INTEGER,"invers_integer(1)",a);
    CTO(EMPTY,"invers_integer(2)",b);
    if (EINSP_INTEGER(a)) 
        {
        M_I_I(1,b);
        goto endr_ende;
        }
    if (NEGEINSP_INTEGER(a)) 
        {
        M_I_I(-1,b);
        goto endr_ende;
        }
    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),b);
    M_I_I(1,S_B_O(b));
    M_I_I(S_I_I(a),S_B_U(b));
    C_B_I(b,GEKUERZT);
    ENDR("invers_integer");
    }
#endif  /* BRUCHTRUE */


INT random_integer(res,para_eins,para_zwei) OP res,para_eins,para_zwei; 
/* AK 150587 */ /* AK 090688 changed */
/* para_eins = lower limit, para_zwei= upper limit */
/* res will be a pseudo random number 
   between lower and upper limit.  */
/* uses the system function rand() */
/* para_eins and para_zwei may be NULL 
              in this case an integer between 0 and 10 */
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* AK 300802 V2.0 */ /* AK 080306 V3.0 */
    {
    INT untergrenze,obergrenze,ires,zi;
    INT erg = OK;
    int rand();

    if (para_eins==NULL) 
        untergrenze=0;
    else if (S_O_K(para_eins) != INTEGER)
        WTO("random_integer(2)",para_eins);
    else untergrenze = S_I_I(para_eins);


    if (para_zwei==NULL) 
        obergrenze=untergrenze + 10;
    else if (S_O_K(para_zwei) != INTEGER)
#ifdef LONGINTTRUE
        {
        if (S_O_K(para_zwei)==LONGINT) /* AK 151092 */
            {
            OP c = callocobject();
            COPY(para_zwei,c);
            if (para_eins != NULL) 
                erg += sub(c,para_eins,c);
            
            if (S_O_K(c) == LONGINT)
                erg += random_longint(res,c);
            else    
                erg += random_integer(res,NULL,c);
                
            if (para_eins != NULL) 
                erg += add_apply(para_eins,res);
            freeall(c);
            goto endr_ende;
            }
        else
#endif /* LONGINTTRUE */
            WTO("random_integer(3)",para_zwei);
#ifdef LONGINTTRUE
        }
#endif /* LONGINTTRUE */
    else obergrenze = S_I_I(para_zwei);

    SYMCHECK(obergrenze < untergrenze,"random_integer: upper limit < lower limit");

    if (obergrenze > untergrenze)
        {
        zi = rand() % (obergrenze - untergrenze);
        ires = untergrenze + zi;
        }
    else
        ires = untergrenze;
    erg += m_i_i(ires,res);
    ENDR("random_integer");
    }

INT tex_integer(a) OP a;
/* AK 101187 */ /* AK 270689 V1.0 */ /* AK 181289 V1.1 */
/* AK 070291 V1.2 prints to texout instead of stdout */
/* AK 210891 V1.3 */
    {
    INT ts = texmath_yn; /* AK 190892 */
    texposition +=  /* AK 210291 */ intlog(a);
    if (S_I_I(a) <0L) texposition++; 
    if (ts == 0L)
    {
        fprintf(texout," $%ld$ ",S_I_I(a)); 
        texposition += 4L;
    }
    else
        fprintf(texout," %ld ",S_I_I(a)); 
    return OK;
    }


INT scan_integer(ergebnis) OP ergebnis;
/* liest ein integerobject ein AK 270787 */
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 080591 V1.2 */
/* AK 210891 V1.3 */
    {
    char c;
    int eingabe;
    INT erg = OK;
    INT numberofmatches;
    CTO(EMPTY,"scan_integer(1)",ergebnis);

sia:
    scan_printeingabe("integerobject ");
    skip_comment();
    numberofmatches = (INT)scanf("%d",&eingabe);
    if (numberofmatches == EOF)  /* AK 220807 */
	{
	error("scan_integer:EOF");
	goto endr_ende;
	}
    if (numberofmatches != (INT)1) 
        {
        while ((c = getchar()) != '\n');
        error("scan_integer:I did not recognize a number");
        goto sia;
        }
    M_I_I((INT)eingabe,ergebnis);
    ENDR("scan_integer");
    }

INT skip_integer(t)  char *t;
/* AK 300998 */
{
    INT erg = OK;
    char *oldt = t;

    while (*t == ' ') t++;
    if (*t == '-') t++;
    if (not SYM_isdigit(*t))
        {
        error("skip_integer:not a INTEGER");
        erg = -10;
        goto endr_ende;
        }
    while (SYM_isdigit(*t)) t++;
    return (INT)(t-oldt);
    ENDR("skip_integer");
}

INT sscan_integer(t,a) OP a; char *t;
/* AK 301293 */
{
    long i;
    sscanf(t,"%ld",&i);
    m_i_i((INT)i,a);
    return OK;
}

INT objectread_integer(filename,obj) FILE *filename; OP obj;
/* AK 131086 */ /* AK 270689 V1.0 */ /* AK 181289 V1.1 */
/* AK 020591 V1.2 */ /* AK 210891 V1.3 */
    {
    INT eingabe;
    INT erg = OK;
    COP("objectread_integer(1)",filename);
    fscanf(filename,"%ld",&eingabe); 
    M_I_I(eingabe,obj); 
    ENDR("objectread_integer");
    }

INT objectwrite_integer(filename,obj) FILE *filename; OP obj;
/* AK 131086 */ /* AK 270689 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    { 
    INT erg = OK;
    COP("objectwrite_integer(1)",filename);
    fprintf(filename," %ld %ld\n",(INT)INTEGER,S_I_I(obj)); 
    ENDR("objectwrite_integer");
    }

INT sprint_integer(string,a) char *string; OP a;
/* AK 020295 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    CTO(INTEGER,"sprint_integer(2)",a);
    sprintf(string,"%ld",S_I_I(a)); 
    ENDR("sprint_integer");
    }

INT fprint_integer(f,a) FILE *f; OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* AK 190298 V2.0 */ /* AK 201204 V3.0 */
    {
    INT erg = OK;
    CTO(INTEGER,"fprint_integer",a);
    SYMCHECK(f == NULL,"fprint_integer:NULL file pointer");

    {
    INT l;
    if (f == stdout) 
        { 
        l = intlog(a);
        zeilenposition +=  l;

        if (l < integer_format) 
            {
            /* we need leading blanks */
            l = integer_format-l;
            zeilenposition +=  l;
            while (l--) putchar(' ');
            }
        if (S_I_I(a) < 0) 
            zeilenposition++;  /* for the leading sign */
        }
    fprintf(f,"%ld",S_I_I(a)); 
    if (f == stdout) 
        if (zeilenposition >= row_length)
            { fprintf(f,"\n"); zeilenposition = 0; }

    }
    ENDR("fprint_integer");
    }

INT s_i_i(a) OP a;
/* to be faster, use the macro S_I_I */
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
/* AK 201204 V3.0 */
    { 
    INT erg = OK;
    CTO(INTEGER,"s_i_i",a);
    return a->ob_self.ob_INT; 
    ENDR("s_i_i");
    }

INT c_i_i(a,b) OP a;INT b;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(INTEGER,"c_i_i",a);
    a->ob_self.ob_INT=b;
        ENDR("c_i_i");
    }

INT m_i_i(a,b) INT a;OP b;
/* AK 270689 V1.0 AK 181289 V1.1 AK 110291 V1.2 AK 060891 V1.3 */
    {  
    INT erg=OK;
    COP("m_i_i",b);
    FREESELF(b);
    C_O_K(b,INTEGER); 
    C_I_I(b,a); 
    ENDR("m_i_i");
    }

INT freeself_integer(a) OP a;
/* AK 270689 V1.0 AK 181289 V1.1 AK 210891 V1.3 */
    { 
    C_O_K(a,EMPTY); 
    return(OK); 
    }

INT test_integer()
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    OP a=callocobject();
    OP b=callocobject();
    OP c=callocobject();
    INT erg;

    m_i_i(5L,a);
    printf("test_integer:m_i_i(5L,a)\n"); 
    debugprint_object(a);
    C_I_I(a,7L);
    printf("test_integer:c_i_i(a,7L)\n"); 
    debugprint_object(a);
    printf("test_integer:fprint_integer(stdout,a)\n"); 
    fprint_integer(stdout,a);
    printf("\n");
    printf("test_integer:tex_integer(a)\n"); 
    tex_integer(a);
    printf("\n");
    printf("test_integer:copy_integer(a,b)\n"); 
    copy_integer(a,b);
    printf("b=");
    println(b);
    printf("test_integer:comp_integer_integer(a,b)\n");
    erg=comp_integer_integer(a,b);
    printf("%ld\n",erg);
    printf("test_integer:binom(a=5L,b=4L,c)\n");
    m_i_i(5L,a); 
    m_i_i(4L,b); 
    binom(a,b,c); 
    println(c);
    freeall(a);
    freeall(b);
    freeall(c);
    return(OK);
    }

#ifdef POLYTRUE 
INT add_apply_scalar_polynom(a,b) OP a,b;
/* AK 110990 V1.1 */ /* AK 270291 V1.2 */ /* AK 080891 V1.3 */
/* AK 260298 V2.0 */
/* input: a = INTEGER or 
              BRUCH or 
              LONGINT */
{
    INT erg = OK;
    OP c;
    CE2A(a,b,add_apply_scalar_polynom);
    CTO(POLYNOM,"add_apply_scalar_polynom(2)",b);

    c = callocobject();
    erg += m_scalar_polynom(a,c);
    erg += insert(c,b,add_koeff,comp_monomvector_monomvector);

    ENDR("add_apply_scalar_polynom");
}
#endif /* POLYTRUE */

INT add_apply_integer(a,b) OP a,b;
/* AK 120390 V1.1 */ /* AK 080891 V1.3 */
/* AK 260298 V2.0 */
{
    INT erg=OK;
    OP d;
    CTO(INTEGER,"add_apply_integer(1)",a);

    switch(S_O_K(b)) {
#ifdef BRUCHTRUE 
        case BRUCH:  
            erg += add_apply_scalar_bruch(a,b);
            break;
#endif /* BRUCHTRUE */

        case INTEGER: 
            erg += add_apply_integer_integer(a,b);
            break;

#ifdef LONGINTTRUE 
        case LONGINT: 
            erg += add_apply_integer_longint(a,b);
            break;
#endif /* LONGINTTRUE */

#ifdef SCHURTRUE
        case SCHUR:
            d = callocobject();
            erg += m_scalar_schur(a,d);
            insert(d,b,add_koeff,comp_monomschur);
            break;
#endif /* SCHURTRUE */

#ifdef POLYTRUE
        case SCHUBERT:
        case POLYNOM:
            erg += add_apply_scalar_polynom(a,b);
            break;
#endif /* POLYTRUE */

        default: 
            {
            OP c;
            c = callocobject();
            *c = *b;
            C_O_K(b,EMPTY);
            erg += add_integer(a,c,b);
            erg += freeall(c); 
            }
            break;
        }
    ENDR("add_apply_integer");
}    


#ifdef MATRIXTRUE
INT mult_apply_integer_matrix(a,b) OP a,b;
/* b = b* a */ /* AK 220390 V1.1 */ /* AK 250291 V1.2 */
/* AK 080891 V1.3 */
/* AK 260298 V2.0 */
    {
    OP z = S_M_S(b);
    INT i = S_M_HI(b)*S_M_LI(b);
    INT erg = OK;
    CTO(INTEGER,"mult_apply_integer_matrix(1)",a);
    CTO(MATRIX,"mult_apply_integer_matrix(2)",b);

    for(;i>0L;i--,z++) 
        MULT_APPLY_INTEGER(a,z);

    ENDR("mult_apply_integer_matrix");
    }
#endif /* MATRIXTRUE */


INT mult_apply_integer(a,b) OP a,b;
/* b = b* a */ /* AK 201289 V1.1 */ /* AK 250291 V1.2 */
/* AK 210891 V1.3 */
/* AK 260298 V2.0 */
{
    INT erg = OK;
    EOP("mult_apply_integer(2)",b);
    CTO(INTEGER,"mult_apply_integer(1)",a);

    switch(S_O_K(b)) {
#ifdef BRUCHTRUE
        case BRUCH:
            erg += mult_apply_integer_bruch(a,b);
            break;
#endif /* BRUCHTRUE */

        case INTEGER:
            erg += mult_apply_integer_integer(a,b);
            break;

#ifdef LONGINTTRUE
        case LONGINT:
            erg += mult_apply_integer_longint(a,b);
            break;
#endif /* LONGINTTRUE */

#ifdef MATRIXTRUE
        case KRANZTYPUS :
        case MATRIX:
            erg += mult_apply_integer_matrix(a,b);
            break;
#endif /* MATRIXTRUE */

#ifdef CHARTRUE
        case SYMCHAR:
            erg += mult_apply_scalar_symchar(a,b);
             break;
#endif /* CHARTRUE */

#ifdef POLYTRUE
        case MONOM:
            erg += mult_apply_integer_monom(a,b);
            break;
        case SCHUR:
        case POW_SYM:
        case ELM_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case SCHUBERT:
        case GRAL:
        case POLYNOM:
        case MONOPOLY:
            erg += mult_apply_integer_polynom(a,b);
            break;
#endif /* POLYTRUE */

#ifdef NUMBERTRUE
        case SQ_RADICAL:
            erg +=  mult_apply_scalar_sqrad(a,b);
            break;
        case CYCLOTOMIC:
            erg += mult_apply_scalar_cyclo(a,b);
            break;
#endif /* NUMBERTRUE */

#ifdef VECTORTRUE 
        case INTEGERVECTOR:
        case COMPOSITION:
        case WORD:
        case VECTOR:
            erg += mult_apply_scalar_vector(a,b);
            break;
        case HASHTABLE:
            erg += mult_apply_integer_hashtable(a,b);
            break;

#endif /* VECTORTRUE */
        default: 
            if (S_I_I(a) == (INT)1) { }
            else if (S_I_I(a) == (INT)-1)
                erg += addinvers_apply(b);
            else
                erg += WTO("mult_apply_integer: wrong second type",b);
        }
    ENDR("mult_apply_integer");
}

INT square_apply_integer(a) OP a;
/* AK 271101 */
/* a = a * a */
{
    INT erg = OK;
    INT i;
    CTO(INTEGER,"square_apply_integer(1)",a);
    i = S_I_I(a);
    if (i<0) i = -i;

    if (i < 46340) /* sqrt(2^31 */
        {
        M_I_I(S_I_I(a) * S_I_I(a),a);
        }
    else{
        OP c;
        c = CALLOCOBJECT();
        *c = *a;
        C_O_K(a,EMPTY);
        t_int_longint(c,a);
        erg += mult_apply_integer_longint(c,a);
        FREEALL(c);
        }
    ENDR("square_apply_integer");
}

INT mult_apply_integer_integer(a,b) OP a,b;
/* AK 201289 V1.1 */ /* AK 250291 V1.2 */
/* AK 210891 V1.3 */
/* AK 270298 V2.0 */
{ 
    INT erg = OK;
    CTO(INTEGER,"mult_apply_integer_integer(1)",a);
    CTO(INTEGER,"mult_apply_integer_integer(2)",b);

    if ( 
        (S_I_I(a) < 46300) && (S_I_I(a) > -46300)
        &&
        (S_I_I(b) < 46300) && (S_I_I(b) > -46300)
        )  
        M_I_I(S_I_I(a)*S_I_I(b),b); 
    else
        {
        if ( (INTLOG(a) + INTLOG(b)) > 9L )
            {
            if (S_I_I(a)==0) M_I_I(0,b);
            else if (S_I_I(b)!=0)
                 {
                 erg += t_int_longint(b,b);
                 erg += mult_apply_integer_longint(a,b);
                 }
            }
        else 
            M_I_I(S_I_I(a)*S_I_I(b),b); 
        }
    ENDR("mult_apply_integer_integer");
}



INT add_apply_integer_integer(a,b) OP a,b;
/* AK 120390 V1.1 */ /* AK 250291 V1.2 */ /* AK 210891 V1.3 */
/* AK 270298 V2.0 */
/* AK 050902 V2.1 */
{
    INT erg = OK;
    INT i;
    CTO(INTEGER,"add_apply_integer_integer(1)",a);
    CTO(INTEGER,"add_apply_integer_integer(2)",b);
 
    i = S_I_I(a)+S_I_I(b);
    if (
          ( (S_I_I(a) > 0) && (S_I_I(b) > 0) && (i <= 0) )
          ||
          ( (S_I_I(a) < 0) && (S_I_I(b) < 0) && (i >= 0) )
        )
    /* we have to change to longint arithmetic */
        {
#ifdef LONGINTTRUE
        OP c;
        c = CALLOCOBJECT();
        erg += t_int_longint(b,c);
        FREESELF(b);
        *b = *c;
        C_O_K(c,EMPTY);
        FREEALL(c);
        erg += add_apply_integer_longint(a,b);
#else /* LONGINTTRUE */
        erg += error("add_apply_integer_integer:Overflow no LONGINT");
#endif /* LONGINTTRUE */
        }
    else    
        C_I_I(b,i);
        
    ENDR("add_apply_integer_integer");
}

INT intlog_int(ai) INT ai;
/* number of digits of an int */
/* AK 201204 V3.0 */
    {
    if (ai < 0L) ai = -ai;
    if (ai >= 1000000000L) return(10L);
    if (ai >= 100000000L) return(9L);
    if (ai >= 10000000L) return(8L);
    if (ai >= 1000000L) return(7L);
    if (ai >= 100000L) return(6L);
    if (ai >= 10000L) return(5L);
    if (ai >= 1000L) return(4L);
    if (ai >= 100L) return(3L);
    if (ai >= 10L) return(2L);
    return(1L);
    }

INT intlog(a) OP a;
/* number of digits of an integer object */ 
/* AK 150290 V1.1 */ /* AK 250291 V1.2 */
/* AK 210891 V1.3 */ /* AK 201204 V3.0 */
    {
    INT erg = OK;
    CTTO(LONGINT,INTEGER,"intlog(1)",a);
    if (S_O_K(a) == INTEGER) 
    {
    INT ai;
    ai = S_I_I(a);
    if (ai < 0L) ai = -ai;
    if (ai >= 1000000000L) return(10L);
    if (ai >= 100000000L) return(9L);
    if (ai >= 10000000L) return(8L);
    if (ai >= 1000000L) return(7L);
    if (ai >= 100000L) return(6L);
    if (ai >= 10000L) return(5L);
    if (ai >= 1000L) return(4L);
    if (ai >= 100L) return(3L);
    if (ai >= 10L) return(2L);
    return(1L);
    }
    else if (S_O_K(a) == LONGINT)
	{
	return intlog_longint(a);
        }
    ENDR("intlog");
    }

INT init(kind,a) OBJECTKIND kind; OP a;
/* AK 300588 */ /* AK 030789 V1.0 */ /* AK 060390 V1.1 */ /* AK 250291 V1.2 */
/* AK 050891 V1.3 */
    {
    INT erg=OK;
    COP("init(2)",a);
    FREESELF(a);

    switch (kind) {
        case EMPTY:
                break;
#ifdef BINTREETRUE
        case BINTREE: erg +=  init_bintree(a); break;
#endif /* BINTREETRUE */
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += b_ou_b(callocobject(),callocobject(),a);
            break;
#endif /* BRUCHTRUE */
        case INTEGER: 
            M_I_I(0,a); /* AK 050902 */
            break;
#ifdef KRANZTRUE
        case KRANZ:  erg+= init_kranz(a);
            break;
#endif /* KRANZTRUE */
#ifdef LONGINTTRUE
        case LONGINT: erg += init_longint(a); break;
#endif /* LONGINTTRUE */
#ifdef MONOMTRUE
        case MONOM: 
            erg += b_sk_mo(callocobject(),callocobject(),a);
            break;
#endif /* MONOMMTRUE */
#ifdef NUMBERTRUE 
        case CYCLOTOMIC: 
            erg += init_cyclo(a);
            break;
        case SQ_RADICAL:
            /* MD */
            erg += init_sqrad(a);
            break;
#endif /* NUMBERTRUE */
#ifdef PARTTRUE
        case PARTITION: 
            erg+= b_ks_pa(VECTOR,callocobject(),a);break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION: 
            erg+=b_ks_p(VECTOR,callocobject(),a);break;
#endif /* PERMTRUE */
#ifdef REIHETRUE
        case REIHE: erg+=init_reihe(a);break;
#endif /* REIHETRUE */
#ifdef LISTTRUE
        case SCHUR:
            erg += init_schur(a);
            break;
        case HOMSYM:
            erg += init_homsym(a);
            break;

        case GRAL: case POW_SYM:  case MONOPOLY:
        case POLYNOM: case ELM_SYM: case MONOMIAL: case SCHUBERT: 
        case LIST: 
            erg += b_sn_l(NULL,NULL,a);
            C_O_K(a,kind); 
            break;
#endif /* LISTTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX:
            erg+=b_us_t(callocobject(),callocobject(),a); break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE  
        case BITVECTOR:
            erg += m_il_bv((INT)0,a);break;
        case INTEGERVECTOR:
        case WORD: 
        case VECTOR: 
        case COMPOSITION: 
        case SUBSET:
            erg += m_il_v((INT)0,a);
            C_O_K(a,kind);
            break;
        case QUEUE:
            erg += init_queue(a);
            break;
        case HASHTABLE:
            erg += init_hashtable(a);
            break;
#endif /* VECTORTRUE */
        default: 
            fprintf(stderr,"kind = %ld\n",(INT) kind);
            return error("init:wrong kind");
        }
    
    CTO(kind,"init(e2)",a);
    ENDR("init");
}

INT next_apply(obj) OP obj;
/* AK 300997 */
    {
    INT erg = OK;
    EOP("next_apply(1)",obj);
    switch(S_O_K(obj))
        {
#ifdef FFTRUE
        case FF: /* AK 290304  */
            erg = next_apply_ff(obj);
            if (erg == ERROR)
                goto endr_ende;
            return (erg == LAST_FF ? FALSE : TRUE );
#endif /* FFTRUE */



#ifdef PARTTRUE
        case SUBSET: /* AK 280901 */
            return((next_apply_subset(obj)
                == 
                LASTSUBSET)?
                        FALSE : TRUE);
        case COMPOSITION:
            return((next_apply_composition(obj)
                == 
                LASTCOMP)?
                        FALSE : TRUE);
        case PARTITION: 
            return((next_apply_partition(obj) 
                == 
                LASTPARTITION)?
                        FALSE : TRUE);
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION:  /* AK 280901 */
            if (S_P_K(obj) == VECTOR)
                return (next_apply_permutation(obj) == LASTPERMUTATION)?  FALSE : TRUE;
            else if (S_P_K(obj) == BAR) /* AK 120902 */
                return (next_apply_bar(obj) == LASTPERMUTATION)?  FALSE : TRUE;
            else 
                {
                error("wrong kind of permutation in next_apply");
                goto endr_ende;
                }
#endif /* PERMTRUE */
        default: 
            erg+= WTO("next_apply(1)",obj);
            break;
        }
    ENDR("next_apply");
    }

INT next(von,nach) OP von, nach;
/* AK 220488 */ /* AK 030789 V1.0 */ /* AK 081289 V1.1 */ /* AK 250291 V1.2 */
/* AK 050891 V1.3 */
    {
    INT erg = OK;

    EOP("next",von);
    /* nicht CE2 wg. return value */
    if (check_equal_2(von,nach,next,&erg) == EQUAL)
                return erg;

    switch(S_O_K(von))
        {
#ifdef FFTRUE
        case FF: /* AK 170194 */
            erg = next_ff(von,nach);
            if (erg == ERROR)
                goto endr_ende;
            return (erg == LAST_FF ? FALSE : TRUE );
#endif /* FFTRUE */
#ifdef PARTTRUE
        case PARTITION: {
            return((next_partition(von,nach) 
                == 
                LASTPARTITION)?
                        FALSE : TRUE);
            }
        case COMPOSITION: {
            return((next_composition(von,nach) 
                == 
                LASTCOMP)?
                        FALSE : TRUE);
            }
        case SUBSET: {
            return((next_subset(von,nach) 
                == 
                LASTSUBSET)?
                        FALSE : TRUE);
            }
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION: {
            if (S_P_K(von) == BAR)
            return((next_bar(von,nach) == LASTPERMUTATION)?
                FALSE : TRUE);
            else if (S_P_K(von) == VECTOR)
            return((next_permutation(von,nach) == LASTPERMUTATION)?
                FALSE : TRUE);
            else
                return error("next: wrong kind of permutation");
            }
#endif /* PERMTRUE */
        default: erg+= WTO("next(1)",von);
            break;
        }
    ENDR("next");
    }

OP find (a,b) OP a,b;
/* return NULL if a not in b */
/* AK 251103 */
{
    INT erg =OK;
    if (VECTORP(b)) return find_vector(a,b);
    WTO("find(2)",b);
    ENDO("find");
}


INT insert(a,c,eh,cf) OP a,c; INT (*eh)(),(*cf)();
/* AK 221286*/ /* AK 030789 V1.0 */ /* AK 221289 V1.1 */ /* AK 250291 V1.2 */
/* AK 060891 V1.3 */
/* inserts a into c */
/* AK 060498 V2.0 */
    {
    INT erg = OK;
    if (a == NULL) 
        {
        erg += error("insert:first == NULL");
        goto endr_ende;
        }
    if (a == c) 
        {
        erg += error("insert:first == ERGEBNIS");
        goto endr_ende;
        }
    if (EMPTYP(a))  
        {
        erg += freeall(a);
        goto endr_ende;
        }
        

    switch(S_O_K(c))
        {
#ifdef VECTORTRUE
        case HASHTABLE:
            erg = insert_hashtable(a,c, eh,cf,hash);
            goto endr_ende;
#endif

#ifdef BINTREETRUE
        case BINTREE: 
            erg = insert_bintree(a,c, eh,cf);
            switch (erg) {
                case INSERTOK:
                case INSERTEQ:
                    return erg;
                    }
            goto endr_ende;
#endif /* BINTREETRUE */

#ifdef LISTTRUE
        case LIST: 
            erg += insert_list(a,c,eh,cf);
            goto endr_ende;
#endif /* LISTTRUE */

        case MONOPOLY: 
        case SCHUR: 
        case SCHUBERT: 
        case POW_SYM: 
        case HOM_SYM: 
        case GRAL: 
        case POLYNOM: 
        case ELM_SYM:
        case MONOMIAL:
#ifdef LISTTRUE
            if (cf == NULL)
                cf= comp_monomvector_monomvector;
            if (eh == NULL)
                eh = add_koeff;
            erg += insert_list(a,c, eh,cf);
            goto endr_ende;
#endif /* LISTTRUE */

        default:
            ;
        };

    switch(S_O_K(a))
        {
#ifdef POLYTRUE
        case GRAL: 
        case HOM_SYM: 
        case POW_SYM: 
        case MONOPOLY:
        case SCHUBERT: 
        case SCHUR: 
        case POLYNOM: 
        case ELM_SYM:
        case MONOMIAL:
            if (cf == NULL)
                cf= comp_monomvector_monomvector;
            if (eh == NULL)
                eh = add_koeff;
            erg += insert_list(a,c, eh,cf);
            goto endr_ende;
#endif /* POLYTRUE */
        default: 
            erg += WTT("insert(1,2)",a,c); 
            goto endr_ende;
        };
    ENDR("insert");
    }


INT first(kind,res,para_eins) OBJECTKIND kind; OP res,para_eins;
/* AK 270788 */ /* AK 030789 V1.0 */ /* AK 060390 V1.1 */ /* AK 200691 V1.2 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    CE2(res,para_eins,first);
    if (not EMPTYP(res)) 
        erg += freeself(res);
    switch (kind)
        {
#ifdef PERMTRUE
        case PERMUTATION:  erg += first_permutation(para_eins,res);
            break; 
#endif /* PERMTRUE */
#ifdef PARTTRUE
        case PARTITION:  erg += first_partition(para_eins,res);
            break; 
#endif /* PARTTRUE */
        default: return error("first:wrong kind");
        };
    ENDR("first");
    }

INT b_ks_o(kind,self,object) OBJECTKIND kind; OBJECTSELF self; OP object;
/* build_kind_self_object */ /* AK 061086 */
/* erzeugt ein object der art kind (z.B. VECTOR)
und einen pointer auf self, das eigentliche
object (z.B. struct vector) 270787/ */
/* AK 270689 V1.0 */ /* AK 060390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("b_ks_o",object);
    FREESELF(object);
    C_O_K(object,kind); 
    C_O_S(object,self); 
    ENDR("b_ks_o");
    }


/* must be with offset */ INT (*check_time_co)();


INT check_time()
{ 
    static INT l_callocobject;
    if (check_time_co != NULL)
        {
        (*check_time_co)();
        }
    runtime(&l_callocobject);
    if (l_callocobject > sym_timelimit)
        {
        fprintf(stderr,"SYMMETRICA stopped due to timelimit\n");
        exit(ERROR_TIMELIMIT);
        }
    return OK;
}

OP callocobject_magma()
{
    OP res;
    res = (OP) SYM_MALLOC(sizeof(struct object));
    C_O_K(res,EMPTY);
    return res;
}

OP callocobject()
/* erzeugt den speicherplatz fuer ein object 270787 */
/* AK 270689 V1.0 */ /* AK 170190 V1.1 */ /* AK 060891 V1.3 */
    {
#ifdef SYMMAGMA
    return callocobject_magma();
#else
    OP c;
    if (sym_timelimit > 0L)
        check_time();

    if (freeall_speicherposition >= 0L) /* AK 111091 */
        {
        c = freeall_speicher[freeall_speicherposition--];
        }
    else
        c = (OP) SYM_MALLOC(sizeof(struct object));

    if (c == NULL) 
        error("callocobject:NULL object");


    C_O_K(c,EMPTY);
    return c;
#endif
    }

OP callocobject_fast()
/* AK 141101 */
    {
    OP c;
    c = (OP) SYM_MALLOC(sizeof(struct object));
    C_O_K(c,EMPTY);
    return c;
    }

OBJECTSELF s_o_s(a) OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060891 V1.3 */
    {
    if (a==NULL) 
        {
        error("s_o_s:object == NULL");
        }
    return(a->ob_self);
    }

OBJECTKIND s_o_k(a) OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    if (a==NULL) {return((OBJECTKIND) error("s_o_k:object == NULL"));}
    return(a->ob_kind);
    }

INT c_o_k(a,b) OP a; OBJECTKIND b;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("c_o_k",a);
    a->ob_kind = b;
    ENDR("c_o_k");
    }

INT c_o_s(a,b) OP a; OBJECTSELF b;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("c_o_s",a);
    a->ob_self = b; 
    ENDR("c_o_s");
    }

INT emptyp(a) OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    { 
    return(s_o_k(a) == EMPTY); 
    }

INT test_callocobject()
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    OP a = callocobject();
    printf("test_callocobject: sizeof(OP)=%d\n",sizeof(a));
    printf("test_callocobject: sizeof(*OP)=%d\n",sizeof(*a));
    printf("test_callocobject: sizeof(struct object)=%d\n",sizeof(struct object));
    if (a==NULL) {
        printf("test_callocobject: NULL-object");return(OK);
        }
    printf("test_callocobject: a=%ld\n",(INT)a);
    printf("test_callocobject: a->ob_kind=%ld\n",(INT) (a->ob_kind));
    printf("test_callocobject: a->ob_self.ob_INT=%ld\n",
                        (a->ob_self).ob_INT);
    SYM_free(a);
    return(OK);
    }

INT debugprint_object(a) OP a;
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    if (a==NULL) {
    fprintf(stderr,"debugprint_object: NULL-object");return(OK);}
    fprintf(stderr,"debugprint_object: a=%ld\n",(INT)a);
    fprintf(stderr,"debugprint_object: kind=%ld\n",(INT)a->ob_kind);
    fprintf(stderr,"debugprint_object: self.INT=%ld\n",a->ob_self.ob_INT);
    return(OK);
    }

INT test_object()
/* AK 270689 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    OP a=callocobject();
    OBJECTSELF d;
    printf("test von callocobject()\n");
    test_callocobject();
    printf("\nobject vor c_o_k()\n");
    debugprint_object(a);
    c_o_k(a,(OBJECTKIND)5);
    printf("\nobject nach c_o_k(a,5)\n");
    debugprint_object(a);
    d.ob_INT = 12345L;
    c_o_s(a,d);
    printf("\nobject nach c_o_s(a,12345L)\n");
    debugprint_object(a);
    SYM_free(a);
    return(OK);
    }


#ifdef SKEWPARTTRUE
OP s_spa_g(a) OP a;
/* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    { 
    OBJECTSELF b; 
    INT erg = OK;
    CTO(SKEWPARTITION,"s_spa_g",a);
    b = s_o_s(a); 
    return b.ob_skewpartition->spa_gross; 
    ENDO("s_spa_g");
    }

INT c_spa_g(a,b) OP a,b;
/* AK 280789 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    { 
    OBJECTSELF c;
    c=s_o_s(a);
    c.ob_skewpartition->spa_gross=b;
    return(OK); 
    }

OP s_spa_k(a) OP a;
/* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_skewpartition->spa_klein); 
    }

INT c_spa_k(a,b) OP a,b;
/* AK 280789 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
{ 
    OBJECTSELF c;
    c=s_o_s(a);
    c.ob_skewpartition->spa_klein=b;
    return(OK);
}

OP s_spa_gi(a,i) OP a; INT i;
/* AK 260789 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    { return(s_pa_i(s_spa_g(a),i)); }

OP s_spa_ki(a,i) OP a; INT i;
/* AK 260789 V1.1 */ /* AK 210891 V1.3 */
    { return(s_pa_i(s_spa_k(a),i)); }

INT s_spa_gii(a,i) OP a; INT i;
/* AK 260789 V1.1 */
/* AK 210891 V1.3 */
    { return(s_pa_ii(s_spa_g(a),i)); }

INT s_spa_gli(a) OP a;
/* AK 260789 V1.1 */ /* AK 210891 V1.3 */
    { return(s_pa_li(s_spa_g(a))); }

INT s_spa_kii(a,i) OP a; INT i;
/* AK 260789 V1.1 */ /* AK 210891 V1.3 */
    { return(s_pa_ii(s_spa_k(a),i)); }

INT s_spa_kli(a) OP a; 
/* AK 260789 V1.1 */ /* AK 210891 V1.3 */
    { return(s_pa_li(s_spa_k(a))); }
#endif

INT comp_skewpartition(a,b) OP a,b;
{
    INT erg=OK;
    INT res=0;
    CTO(SKEWPARTITION,"comp_skewpartition(1)",a);
    CTO(ANYTYPE,"comp_skewpartition(2)",b);

    if (S_O_K(b) == SKEWPARTITION) 
        res= comp_skewpartition_skewpartition(a,b);
    else 
        WTO("comp_partition(2)",b);
    return res;
    ENDR("comp_skewpartition");
}

INT comp_skewpartition_skewpartition(a,b) OP a,b;
{
    INT erg=OK;
    CTO(SKEWPARTITION,"comp_skewpartition_skewpartition(1)",a);
    CTO(SKEWPARTITION,"comp_skewpartition_skewpartition(2)",b);
    erg = comp(S_SPA_G(a), S_SPA_G(b));
    if (erg != 0)
        return erg;
    return comp(S_SPA_K(a), S_SPA_K(b));
    ENDR("comp_skewpartition_skewpartition");
}

INT lastof_skewpartition(a,b) OP a,b;
/* AK 280789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
#ifdef SKEWPARTTRUE
    return(lastof(S_SPA_G(a),b));
#else
    return error("lastof_skewpartition:SKEWPARTITION not available");
#endif
    }

#ifdef SKEWPARTTRUE
INT length_skewpartition(a,b) OP a,b;
/* AK 280789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
{
    return length(S_SPA_G(a),b);
}

INT hash_skewpartition(a) OP a;
/* AK 201201 */
{
    INT erg = OK;
    CTO(SKEWPARTITION,"hash_skewpartition(1)",a);
    return hash_partition(S_SPA_G(a)) + 11 * hash_partition(S_SPA_K(a));
    ENDR("hash_skewpartition");
}

INT freeself_skewpartition(a) OP a;
/* AK 280789 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(SKEWPARTITION,"freeself_skewpartition(1)",a);

    FREEALL(S_SPA_G(a)); 
    FREEALL(S_SPA_K(a));
    SYM_free(S_O_S(a).ob_skewpartition); 
    C_O_K(a,EMPTY);
    ENDR("freeself_skewpartition");
    }

INT copy_skewpartition(a,b) OP a,b;
/* AK 280789 V1.1 */ /* AK 140891 V1.3 */
    {
    INT erg = OK;
    CTO(SKEWPARTITION,"copy_skewpartition(1)",a);
    CTO(EMPTY,"copy_skewpartition(2)",b);

    erg += b_gk_spa(callocobject(),callocobject(),b);
    copy_partition(S_SPA_G(a),S_SPA_G(b)); 
    copy_partition(S_SPA_K(a),S_SPA_K(b)); 

    ENDR("copy_skewpartition");
    }

INT weight_skewpartition(a,b) OP a,b;
/* AK 020488 */ /* AK 060390 V1.1 */ /* AK 020591 V1.2 */
/* AK 210891 V1.3 */
    {
    OP c=callocobject(), d=callocobject(); 
    weight(S_SPA_G(a),c); 
    weight(s_spa_k(a),d); 
    sub(c,d,b);
    freeall(c);
    freeall(d); 
    return(OK);
    }

INT objectread_skewpartition(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 020591 V1.2 */
/* AK 210891 V1.3 */
    {
    b_gk_spa(callocobject(),callocobject(),a);
    objectread(f,S_SPA_G(a));
    objectread(f,s_spa_k(a));
    return OK;
    }

INT objectwrite_skewpartition(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    COP("objectwrite_skewpartition(1)",f);
    fprintf(f, "%ld ", (INT)SKEWPARTITION);
    erg += objectwrite(f,S_SPA_G(a));
    erg += objectwrite(f,s_spa_k(a));
    ENDR("objectwrite_skewpartition");
    }

INT dimension_skewpartition(a,b) OP a,b;
/* dimension der dartsellung */
/* AK 020890 V1.1 */ /* AK 210891 V1.3 */
{
    OP c = callocobject();
    part_part_skewschur(S_SPA_G(a),S_SPA_K(a),c);
    dimension(c,b);
    freeall(c);
    return OK;
}


INT starpart(a,b,c) OP a,b,c;
/* 020488 AK implementiert staroperation aus REWH */
/* bsp 123 * 222 -> 222345/222 */
/* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT i,letztes;
    OP glength = callocobject(); 
    OP klength = callocobject(); 

    b_gk_spa(callocobject(),callocobject(),c);
    add(S_PA_L(a),S_PA_L(b),glength);
    length(a,klength);
    b_kl_pa(VECTOR,glength,S_SPA_G(c));
    b_kl_pa(VECTOR,klength,S_SPA_K(c));
    
    letztes = S_PA_II(b,S_PA_LI(b)-1);
    for (i=0L;i<S_PA_LI(a);i++) M_I_I(letztes,s_spa_ki(c,i));
    for (i=0L;i<S_PA_LI(b);i++)
        M_I_I(S_PA_II(b,i),s_spa_gi(c,i));
    for (i=0L;i<S_PA_LI(a);i++)
        M_I_I(S_PA_II(a,i)+letztes,s_spa_gi(c,i+S_PA_LI(b)));
    return OK;
    }


INT ferrers_skewpartition(a) OP a; 
{
    return error("ferrers_skewpartition: not yet implemented");
}
#endif /* SKEWPARTTRUE */

#ifdef SKEWPARTTRUE
INT fprint_skewpartition(f,a) OP a; FILE *f;
/* AK 280789 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK; /* AK 150192 */
    erg += fprint(f,S_SPA_G(a));
    fprintf(f," / ");
    erg += fprint(f,s_spa_k(a));
    return erg; /* AK 150192 */
    }

INT sprint_skewpartition(t,s) char *t; OP s;
{
    INT erg = OK;
    CTO(SKEWPARTITION,"sprint_skewpartition(2)",s);
    sprint_partition(t,S_SPA_G(s));
    sprintf(t+strlen(t),"-");
    sprint_partition(t+strlen(t),S_SPA_K(s));
    ENDR("sprint_skewpartition");
}



INT scan_skewpartition(a) OP a;
/* 020488 AK */ /* AK 010889 V1.1 */ /* AK 210891 V1.3 */
    {
    b_gk_spa(callocobject(),callocobject(),a);
    scan_printeingabe("input of a skewpartiton, the big partition");
    scan(PARTITION,S_SPA_G(a));
    scan_printeingabe("input of a skewpartiton, the small partition");
    scan(PARTITION,s_spa_k(a));
    return(OK);
    }


static struct skewpartition * callocskewpartition()
/* 020488 AK erste prozedur beim einfuehren eines neuen datentyps */
/* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    struct  skewpartition *erg
    = (struct skewpartition *) SYM_calloc(1,sizeof(struct skewpartition));
    if (erg == NULL) error("erg == NULL in callocskewpartition()");
    return(erg);
    }

INT skewpartitionp(a) OP a;
/* AK V2.0 040398 */
/* TRUE if a skewpartition */
{
    if (S_O_K(a) != SKEWPARTITION)
        return FALSE;
    if (not partitionp(S_SPA_G(a)))
        return FALSE;
    if (not partitionp(S_SPA_K(a)))
        return FALSE;
    return TRUE;
}

INT m_gk_spa(gross,klein,res)  OP gross,klein,res;
/* AK 110790 V1.1 */ /* AK 140891 V1.3 */
/* AK V2.0 090298 */
/* input:    two PARTITION objects gross, klein
   output:    SKEWPARTITION res = gross/klein
*/
    {
    INT erg = OK;
    CTO(PARTITION,"m_gk_spa",gross);
    CTO(PARTITION,"m_gk_spa",klein);
    CE3(gross,klein,res,m_gk_spa);
    erg +=  b_gk_spa(callocobject(),callocobject(),res);
    erg += copy_partition(gross,S_SPA_G(res));
    erg += copy_partition(klein,S_SPA_K(res));
    ENDR("m_gk_spa");
    }

INT b_gk_spa(gross,klein,ergebnis)  OP gross,klein,ergebnis;
/* AK 020488 */
/* AK 181289 V1.1 */ /* AK 140891 V1.3 */
/* AK 040398 V2.0 */
    {
    OBJECTSELF d;

    if (ergebnis==NULL)
        return ERROR;

    d.ob_skewpartition = callocskewpartition();
    b_ks_o(SKEWPARTITION, d, ergebnis);

    c_spa_g(ergebnis,gross); /*change_skewpartition_gross*/
    c_spa_k(ergebnis,klein); /*change_skewpartition_klein*/
    return(OK);
    }
#endif  /* SKEWPARTTRUE */

#ifdef WORDTRUE
INT test_word()
/* AK 030892 */
{
    OP c = callocobject();
    OP b = callocobject();
    OP a = callocobject();
    printf("random_word(30,b):");
    m_i_i(30L,a); random_word(a,b); println(b);
    printf("content(b,c):");
    content(b,c); println(c);
    freeall(a);
    freeall(b);
    freeall(c);
    return OK;
}
#endif /* WORDTRUE */

#ifdef WORDTRUE
INT charge_word(a,b) OP a,b;
/* AK 151196 */
{
    OP c,d,e,f;
    INT erg = OK,i,r=0,j,oj;
    c = callocobject();
    erg += content_word(a,c);
    if (einsp(c)) goto aaa;
    if (not decreasingp_vector(c))
        {
        erg += fprint(stderr,a);
        erg += fprint(stderr,c);
        erg += error("charge_word:not decreasing content of the word");
        goto endr_ende;
        }
    /* decompose into standard words */
    d = callocobject();
    e = callocobject();
    f = callocobject();
    erg += m_v_pa(c,d);
    erg += conjugate(d,d); 
    erg += copy(a,c);
    erg += m_i_i(0,b);
    for (i=S_PA_LI(d)-1;i>=0;i--) /* number of subwords */
        {
        r = 1;
        m_il_w(S_PA_II(d,i),e); /* the subword */
ccc:
        j=S_W_LI(c)-1;
ddd:
        if (S_W_II(c,j) == r) { r++; M_I_I(-S_W_II(c,j),S_W_I(c,j)); }
        j--;
        if (r == S_W_LI(e) +1) goto bbb; /* one word finished */
        if (j == -1) goto ccc; else goto ddd;
bbb:
        for (j=0,r=0;j<S_W_LI(c);j++)
            if (S_W_II(c,j) < 0) 
                {
                M_I_I(-S_W_II(c,j),S_W_I(e,r));
                r++;
                M_I_I(0,S_W_I(c,j));
                }
        erg += charge_word(e,f);
        erg += add_apply(f,b);
        }
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    goto eee;
aaa:
    oj = S_V_LI(c);
    for (i=1;i<= S_V_LI(c);i++)
        {
        for (j=0;j<S_W_LI(a);j++)
            if (S_W_II(a,j) == i) 
                {
                if (j > oj) r++;
                M_I_I(r,S_V_I(c,j));
                oj = j;
                }
        }
    erg += sum(c,b);
eee:
    erg += freeall(c);
    ENDR("charge_word");
}

INT random_word(a,b) OP a,b;
/* AK 030892 */
/* a random word of length a and entries between 1 and 2 * length */
{
    OP c;
    INT erg = OK, i;
    CTO(INTEGER,"random_word(1)",a);
    c = CALLOCOBJECT();
    M_I_I(S_I_I(a)+S_I_I(a),c);
    erg += m_l_w(a,b);
    for (i=0L;i<S_W_LI(b);i++)
        erg += random_integer(S_W_I(b,i),cons_eins,c);
    FREEALL(c);
    ENDR("random_word");
}
#endif /* WORDTRUE */

#ifdef WORDTRUE
INT S_a_rofword(w,a,r) OP w,a,r;
/* 220488 */ /* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    OP i=callocobject(); 
    if (ge(a,r)) { fprintln(stderr,a); fprintln(stderr,r);
        error("a >= r in S_a_rofword"); }

    copy(r,i);
    do {    dec(i); S_rofword(w,i); } while( ge(i,a) );
    freeall(i);
    return(OK);
    }



INT S_rofword(w,r) OP w,r;
/* 210488 */ /* AK 160890 V1.1 */
/* liefert TRUE solange ein r-index > 0 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    OP m=callocobject(); 
    OP index=callocobject(); 

    erg += maxrindexword(w,r,index,m);
    if (S_I_I(m) <= 0L) return(FALSE);
    M_I_I(S_I_I(r)-1L,S_W_I(w,S_I_I(index)));
    erg += freeall(m); 
    erg += freeall(index); 
    return(TRUE);
    }



INT content_word(a,b) OP a,b;
/* AK 300792 */
    {
    INT erg=OK,m,i;
    CTTO(VECTOR,WORD,"content_word(1)",a);
    CTO(EMPTY,"content_word(2)",b);
    
    
    m=0L;
    for (i=0L;i<S_W_LI(a);i++)
        if (S_W_II(a,i)>m)
            m=S_W_II(a,i);
    /* m is max */
    erg += m_il_nv(m,b);
    for (i=0L;i<S_W_LI(a);i++)
        {
        if (S_W_II(a,i) < 1L) 
            {
            erg += freeself(b);
            return error("content_word: wrong word content");
            }
        INC_INTEGER(S_V_I(b,S_W_II(a,i)-1L));
        }
    ENDR("content_word");
    }



INT R_roftableaux(w,r) OP w,r;
/* 250488 */ /* AK 160890 V1.1 */
/* AK 210891 V1.3 */
/* der umriss wird nicht gebraucht */
    {
    INT j,i,k;

    i=s_t_hi(w)-S_I_I(r)+1L; /* die zeilenummer in die gewechselt wird */
    for (j=0L;j<s_t_li(w);j++)
        if (EMPTYP(s_t_ij(w,i,j))) break;
    if (j==s_t_li(w))     { inc(w); i=i+1L; };
    /* j ist die spaltennummer in die gewechselt wird */
    
    for (k=0L;k<s_t_li(w);k++) if (EMPTYP(s_t_ij(w,i-1L,k))) break;
    k = k-1L;
    /* k ist die spaltennummer aus der gewechselt wird */

    M_I_I(s_t_iji(w,i-1L,k),s_t_ij(w,i,j));
    freeself(s_t_ij(w,i-1L,k));return(OK);
    }



INT starttableaux(t,s) OP t,s;
/* berechnet das Tableaux T_0 aus MD */
/* 250488 */ /* AK 160890 V1.1 */
/* AK 210891 V1.3 */
    {
    OP in = callocobject();
    OP m = callocobject();
    OP l = callocobject();
    OP h = callocobject();
    
    INT i,j,k;

    m_us_t(callocobject(),callocobject(),s);
    content(t,in); max(in,m);

    /* ist der maximale eintrag in  content */
    copy(s_v_l(in),h); copy(m,l);
    m_lh_m(l,h,S_T_S(s));
    for (i=S_I_I(h)-1L,k=0L;i>=0L;i--,k++)
        for (j=s_v_ii(in,k)-1L;j>=0L;j--)
            M_I_I(k+1L,s_t_ij(s,i,j));

    freeall(in);
    SYM_free(m);
    return OK;
    }

INT rm_rindex(word,r) OP word,r;
/* 250488 */ /* AK 160890 V1.1 */
/* AK 210891 V1.3 */
    {
    while(S_rofword(word,r))
        {
        };
    return(OK);
}

    


static INT coroutine250488(i,word,tableaux) INT i; OP word,tableaux;
/* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    OP rindex=callocobject(); 
    OP umriss;
    INT erg=OK;
    M_I_I(i,rindex);
    while(S_rofword(word,rindex))
        erg += R_roftableaux(tableaux,rindex);
        /* simultane operation auf tableaux */


    if (i>2) 
        erg += coroutine250488(i-1L,word,tableaux);

    umriss = callocobject();  /* AK 100688 den umriss ausrechnen */
    erg+= m_matrix_umriss(S_T_S(tableaux), S_T_U(tableaux));

    erg += freeall(rindex);
    return erg;
    }



INT m_tableaux_tableauxpair(tab,ergtab_eins,s) OP tab,ergtab_eins,s; 
/* AK 160890 V1.1 */ /* AK 210891 V1.3 */
    {
    OP w = callocobject(); 

    INT i,j,l;
    INT index;

    wordoftableaux(tab,w);
    starttableaux(tab,s);
    l = s_t_hi(s);
    for(i=2L;i<=l;i++)
        coroutine250488(i,w,s);
    copy(tab,ergtab_eins);
    index=0L;
    for (i=s_t_hi(ergtab_eins)-1L;i>=0L;i--)
        for (j=s_t_li(ergtab_eins)-1L;j>=0L;j--)
            if (not EMPTYP(s_t_ij(ergtab_eins,i,j)))
                {
                M_I_I(S_W_II(w,index),s_t_ij(ergtab_eins,i,j));
                index++;
                };
    freeall(w);
    return OK;
    }



INT maxrindexword(w,r,index,erg) OP w,r,erg,index;
    /*210488*/ /* AK 160890 V1.1 */
    /* berechnet den maximalen wert der r-indices */
    /* er wird an der stelle index erreicht */
/* AK 210891 V1.3 */
    {
    INT i;
    OP zw_eins=callocobject(); 
    OP stelle=callocobject(); 

    M_I_I(-1000000L,erg);
    M_I_I(0L,index);
    for(i=0L;i<s_w_li(w);i++)
        {
        M_I_I(i,stelle);
        rindexword(w,r,stelle,zw_eins);
        if (gr(zw_eins,erg)) {copy(zw_eins,erg);M_I_I(i,index);};
        };
    freeall(zw_eins); freeall(stelle);return(OK);
    }



INT latticepword(w) OP w;
/* 210488 */ /* AK 160890 V1.1 */
/* AK 210891 V1.3 */
    {
    OP m = callocobject(); 
    OP null = callocobject(); 
    OP stelle = callocobject(); 
    OP r = callocobject(); 
    OP erg = callocobject(); 
    INT i,j,a=FALSE;

    max(w,m);
    M_I_I(0L,null);
    for (i=2L;i<=S_I_I(m);i++)
        for(j=0L;j<s_w_li(w);j++)
            {
            M_I_I(i,r); M_I_I(j,stelle); rindexword(w,r,stelle,erg);
            if (gr(erg,null)) goto lwende;
            };
    a = TRUE;
    lwende:
    freeall(null); freeall(r); freeall(erg); freeall(stelle);
    return(a);
    }



INT rindexword(w,r,stelle,erg) OP w,r,stelle,erg;
/* 210488 */ /* AK 020290 V1.1 */
/* AK 210891 V1.3 */
    {
    OP zw_eins= callocobject(); 
    OP zw_zwei= callocobject(); 
    if (S_I_I(r) <= 1) error("zu diesem r ist r-index nicht definiert");
    dec(r);
    rindexword_sub(w,r,stelle,zw_eins);
    inc(r);
    rindexword_sub(w,r,stelle,zw_zwei);
    sub(zw_zwei,zw_eins,erg);
    freeall(zw_eins);
    freeall(zw_zwei);
    return OK;
    }



INT rindexword_sub(w,r,stelle,erg) OP w,r,stelle,erg;
/* 210488 */ /* AK 020290 V1.1 */
/* AK 210891 V1.3 */
    {
    INT i,z=0L;
    if (ge(stelle,s_w_l(w))) { error("so lang ist das wort nicht"); };
    for(i=0L;i<=S_I_I(stelle);i++)
        if (S_W_II(w,i) == S_I_I(r)) z++;
    M_I_I(z,erg);
    return(OK);
    }



INT sscan_word(t,a) char *t; OP a;
{
    INT erg = OK;
    COP("sscan_word(1)",t);
    erg += sscan_integervector(t,a);
    C_O_K(a,WORD);
    ENDR("sscan_word");
}

INT scan_word(ergebnis) OP ergebnis;
/* AK 020290 V1.1 */ /* AK 210891 V1.3 */
    {
    OP l = callocobject();
    INT i,erg=OK;
    CTO(EMPTY,"scan_word(1)",ergebnis);
    
    erg += scan_printeingabe("length of the word ");
    erg += scan(INTEGER,l);

    erg += b_l_w(l,ergebnis);
    for (i=0L;i < S_I_I(l); erg += scan(INTEGER,S_W_I(ergebnis,i++)));
    ENDR("scan_word");
    }

    

OP s_w_s(a) OP a;
/* AK 260789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    return(s_v_s(a));
    }

OP s_w_l(a) OP a;
/* AK 260789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    return(s_v_l(a));
    }

INT s_w_li(a) OP a;
/* AK 260789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    return(s_v_li(a));
    }

OP s_w_i(a,i) OP a;INT i;
/* AK 260789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    return(s_v_i(a,i));
    }

INT s_w_ii(a,i) OP a;INT i;
/* AK 260789 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    return(s_v_ii(a,i));
    }
#endif /* WORDTRUE */

INT cast_apply_integer(a) OP a;
/* AK a is a object which should become a INTEGER */
{
    INT erg = OK,err;
    COP("cast_apply_integer(1)",a);

    switch(S_O_K(a)) {
        case INTEGER: break;
#ifdef LONGINTTRUE
        case LONGINT: erg += t_longint_int(a,a);
            if (S_O_K(a) != INTEGER)
                erg+= error("cast_apply_integer: LONGINT too big");
            break;
#endif
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += kuerzen(a); 
            if (S_O_K(a) == BRUCH)
                {
                erg+= 
            error("cast_apply_integer: BRUCH with nenner != 1");
                break; 
                }
            erg += cast_apply_integer(a);
            break;
#endif
        default:
            err = error("cast_apply_integer: cannot cast to INTEGER");
            if (err==ERROR_EXPLAIN)
                {
                fprintf(stderr,"I tried to convert:");
                fprintln(stderr,a);
                }
            erg += ERROR;
        }
    CTO(INTEGER,"cast_apply_integer(e1)",a);
    ENDR("cast_apply_integer");
}



INT cast_apply(k,a) OBJECTKIND k; OP a;
/* AK 140293 */
/* to cast into correct datatype */
{
    INT erg = OK;
    COP("cast_apply(1)",a);

    if (k == S_O_K(a))
        goto cae;
    switch (k) {
#ifdef FFTRUE
        case FF:
            erg += cast_apply_ff(a); break;
#endif /* FFTRUE */
#ifdef BRUCHTRUE
        case BRUCH:
            erg += cast_apply_bruch(a) ; break;
#endif /* BRUCHTRUE */
        case INTEGER:
            erg += cast_apply_integer(a); break;
#ifdef MATRIXTRUE
        case MATRIX:
            erg += cast_apply_matrix(a); break;
#endif
        case MONOM:
            erg += cast_apply_monom(a); break;
#ifdef PARTTRUE
        case PARTITION:
            erg += cast_apply_part(a); break;
#endif
#ifdef PERMTRUE
        case PERMUTATION:
            erg += cast_apply_perm(a); break;
        case BARPERM:
            erg += cast_apply_barperm(a); break;
#endif
#ifdef SCHURTRUE
        case ELMSYM:
            erg += cast_apply_elmsym(a); break;
        case SCHUR:
            erg += cast_apply_schur(a); break;
        case POWSYM:
            erg += cast_apply_powsym(a); break;
        case HOMSYM:
            erg += cast_apply_homsym(a); break;
        case MONOMIAL:
            erg += cast_apply_monomial(a); break;
#endif
#ifdef MONOPOLYTRUE
        case MONOPOLY:
            erg += cast_apply_monopoly(a);
            break;
#endif
#ifdef POLYTRUE
        case POLYNOM:
            erg += cast_apply_polynom(a); break;
#endif
#ifdef SCHUBERTTRUE
        case SCHUBERT:
            erg += cast_apply_schubert(a); break;
#endif
#ifdef TABLEAUXTRUE
        case TABLEAUX:
            erg += cast_apply_tableaux(a); break;
#endif
        default:
            erg += printobjectkind(a);
            erg += print_type(k);
            erg += error("cast_apply:can not cast from first kind into second kind");
    }
cae:
    ENDR("cast_apply");
}

OP select_i(a,b) OP a,b;
/* AK 180294 */
{
    INT erg = OK;
    CTO(INTEGER,"select_i",b);
    switch(S_O_K(a)) {
        case INTEGERVECTOR:
        case VECTOR: return s_v_i(a,S_I_I(b));
        case PERMUTATION: return s_p_i(a,S_I_I(b));
        case PARTITION: return s_pa_i(a,S_I_I(b));
        }
    WTO("select_i",a);
    ENDO("select_i");
}



/*
Additionne 2 polynomes de Laurent.
La composante 0 de vc1 est plus grande que la composante 0 de vc2 
*/

static INT q_add_ord(vc1,vc2,res) OP vc1,vc2,res;
{
  INT delta,lg_vc1,lg_vc2,i;

  lg_vc1=S_LA_LI(vc1);
  lg_vc2=S_LA_LI(vc2);
  delta=S_LA_II(vc1,0L)-S_LA_II(vc2,0L);
  if(lg_vc2>=lg_vc1+delta)
    m_il_nla(lg_vc2,res);
  else
    m_il_nla(lg_vc1+delta,res);
  M_I_I(S_LA_II(vc2,0L),S_LA_I(res,0L));

  for(i=1L;i<lg_vc2;i++)
    M_I_I(S_LA_II(vc2,i),S_LA_I(res,i));
  for(i=1L;i<lg_vc1;i++)
    M_I_I(S_LA_II(res,i+delta)+S_LA_II(vc1,i),S_LA_I(res,i+delta));
  return OK;
}

/*
Additionne 2 polynomes de Laurent
*/

INT add_laurent(vc1,vc2,res) OP vc1,vc2,res;
{
    INT erg = OK;
    CTO(LAURENT,"add_laurent(1)",vc1);
    
    if (S_O_K(vc2) == INTEGER)
        {
        OP c = callocobject();
        t_INTEGER_LAURENT(vc2,c);
        add_laurent(vc1,c,res);
        freeall(c);
        return OK;
        }
    else if (S_O_K(vc2) != LAURENT)
        {
        WTO("add_laurent",vc2);
        goto endr_ende;
        }

    if(S_LA_II(vc1,0L)<S_LA_II(vc2,0L))
        q_add_ord(vc2,vc1,res);
    else
        q_add_ord(vc1,vc2,res);
    return OK;
    ENDR("add_laurent");
}


INT add_apply_laurent(a,b) OP a,b;
{
    OP c;
    INT erg = OK;
    CTO(LAURENT,"add_apply_laurent(1)",a);
    c=callocobject();
    erg += add_laurent(a,b,c);
    erg += freeself(b);
    c_o_s(b,S_O_S(c));
    C_O_K(c,EMPTY);
    erg += freeall(c);
    ENDR("add_apply_laurent");
}

/*
Produit de 2 polynomes de Laurent
*/

INT mult_laurent(vc1,vc2,res) OP vc1,vc2,res;
{
  INT lg_vc1,lg_vc2,i,j;
    INT erg = OK;

  if (S_O_K(vc2) == INTEGER)
    {
    OP c = callocobject();
    t_INTEGER_LAURENT(vc2,c);
     mult_laurent(vc1,c,res);
    freeall(c);
    return OK;
    }
  else if (S_O_K(vc2) == BRUCH)
    {
    copy(vc2,res);
    mult(vc1,S_B_O(vc2),S_B_O(res));
    kuerzen(res);
    return OK;
    }
  else if (S_O_K(vc2) != LAURENT)
    {
    WTO("mult_laurent",vc2);
    goto endr_ende;
    }
  lg_vc1=S_LA_LI(vc1);
  lg_vc2=S_LA_LI(vc2);
  m_il_nla(lg_vc1+lg_vc2-2L,res);
  M_I_I(S_LA_II(vc1,0L)+S_LA_II(vc2,0L),S_LA_I(res,0L));
  for(i=1L;i<lg_vc1;i++)
    if(S_LA_II(vc1,i)!=0L)
      for(j=i;j<i+lg_vc2-1L;j++)
        M_I_I(S_LA_II(res,j)+(S_LA_II(vc1,i)*S_LA_II(vc2,j-i+1L)),S_LA_I(res,j));
  return(OK);
    ENDR("mult_laurent");
}

/*
Normalise the Laurent's polynom:
For example [2, 0, 0, 3, 4, 0, 7] becomes [4, 3, 4]
returns 0 if the polynom is null, 1 if not
*/
INT normal_laurent(vc) OP vc;
{
    /* CC 290396 */
    /*Normalise Laurent polynom. For example, [2,0,0,3,5] becomes [4,3,5]*/

    INT tp,tmp,lg_vc,i,lg_w;
    OP w;
    INT erg = OK;

    tp=0L;
    lg_vc= S_LA_LI(vc);
    for(i=1L;i<lg_vc;i++)
        {
        if(S_LA_II(vc,i)!=0L) break;
        else tp++;
        }
    if(i>=lg_vc)
        {
        erg += m_il_nla(2L,vc);
        goto endr_ende;
        }
    tmp=0L;
    for(i=lg_vc-1L;i>0L;i--)
    {
        if(S_LA_II(vc,i)!=0L) break;
        else tmp++;
    }
    w=callocobject();
    lg_w=lg_vc-tmp-tp;
    erg += m_il_la(lg_w,w);
        M_I_I(S_LA_II(vc,0L)+tp,S_LA_I(w,0L));
    for(i=1L;i<lg_w;i++)
        M_I_I(S_LA_II(vc,i+tp),S_LA_I(w,i));
    erg += freeself(vc);
    *vc = *w;
    C_O_K(w,EMPTY); /* AK 300197 */
    freeall(w);
    ENDR("normal_laurent");
}


INT scan_laurent(ergebnis) OP ergebnis;
{
/* CC 010496 */
  INT l,erg=OK;
  INT i;
  erg += printeingabe("length of vector ");
  scanf("%ld",&l);
  if(l<2L)
  {
    erg+= m_il_nla(2L,ergebnis);
    return OK;
  }
  erg+=m_il_la(l,ergebnis);
  for(i=0L;i<l;erg += scan(INTEGER,S_V_I(ergebnis,i++)));
  return OK;
}


INT t_LAURENT_OBJ(vc,mp) OP vc,mp;
{
/*CC 290496*/
/*
transforms an object vc of type LAURENT into an object mp of type MONOPOLY
or into a BRUCH or into an INTEGER 
*/
    OP oben,unten,mn,sf;
    INT erg = OK;
    INT i;

    CTO(LAURENT,"t_LAURENT_OBJ",vc);

        erg += normal_laurent(vc);
        if(S_LA_LI(vc)==2L&&S_LA_II(vc,0L)==0L)
    {
        erg += m_i_i(S_LA_II(vc,1L),mp);
        goto endr_ende;
    }
    sf=callocobject();
    if(S_LA_II(vc,0L)>=0L)
    {
        erg += init(MONOPOLY,mp);
        for(i=1L;i<S_LA_LI(vc);i++)
        {
            if(S_LA_II(vc,i)!=0L)
            {
                mn=callocobject();
                M_I_I(S_LA_II(vc,0L)+i-1L,sf);
                erg += m_sk_mo(sf,S_LA_I(vc,i),mn);
                insert(mn,mp,add_koeff,NULL);
            }
        }
    }
    else
    {
        unten=callocobject();
        init(MONOPOLY,unten);
        M_I_I(-S_LA_II(vc,0L),sf);
        mn=callocobject();
        erg += m_sk_mo(sf,cons_eins,mn);
        insert(mn,unten,add_koeff,NULL);
        oben=callocobject();
        if(S_LA_LI(vc)==2L)
            M_I_I(S_LA_II(vc,1L),oben);
        else
        {
            erg += init(MONOPOLY,oben);
            M_I_I(0L,sf);
            for(i=1L;i<S_LA_LI(vc);i++)
            {
                if(S_LA_II(vc,i)!=0L)
                {
                    mn=callocobject();
                    erg += m_sk_mo(sf,S_LA_I(vc,i),mn);
                    insert(mn,oben,add_koeff,NULL);
                }
                erg += inc(sf);
            }
        }
        erg += b_ou_b(oben,unten,mp);
    }
    erg += freeall(sf);
    ENDR("t_LAURENT_OBJ");
}



INT t_MONOPOLY_LAURENT(mp,vc) OP mp,vc;
{
/* CC 010496 */
    OP dg,z;
    INT dgi,deb,lg_vc,tmp;

    if(S_O_K(mp)!=MONOPOLY)
        return error("t_MONOPOLY_LAURENT: wrong first type");
    if(nullp_monopoly(mp))
    {
        m_il_nla(2L,vc);
        return OK;
    }
    dg=callocobject();
    degree_monopoly(mp,dg);
    dgi=S_I_I(dg);
    deb=S_I_I(S_PO_S(mp));
    lg_vc=dgi-deb+2L;
    m_il_nla(lg_vc,vc);
    M_I_I(deb,S_LA_I(vc,0L));
    z=mp;
    while(z!=NULL)
    {
        tmp=S_I_I(S_PO_S(z));
        copy(S_PO_K(z),S_LA_I(vc,tmp-deb+1L));
        z=S_L_N(z);
    }
    freeall(dg);return OK;
}


INT t_POLYNOM_LAURENT(po,vc) OP po,vc;
{
    /*CC 010496*/
    OP dg,z;
    INT dgi,deb,lg_vc,tmp;
    INT erg = OK;

    CTO(POLYNOM,"t_POLYNOM_LAURENT",po);


    /*CC 30/07/96*/
    if(has_one_variable(po)==FALSE) 
        {
        erg += error("t_POLYNOM_LAURENT: the first polynomial has more than pne variable");
        goto endr_ende;
        }

    if(nullp_polynom(po))
        {
        erg += m_il_nla(2L,vc);
        goto endr_ende;
        }
    dg=callocobject();
    erg += degree_polynom(po,dg);
    dgi=S_I_I(dg);
    deb=S_PO_SII(po,0L);
    lg_vc=dgi-deb+2L;
    erg += m_il_nla(lg_vc,vc);
    M_I_I(deb,S_LA_I(vc,0L));
    z=po;
    while(z!=NULL)
        {
        tmp=S_PO_SII(z,0L);
        copy(S_PO_K(z),S_LA_I(vc,tmp-deb+1L));
        z=S_L_N(z);
        }
    erg += freeall(dg);
    ENDR("t_POLYNOM_LAURENT");
}

INT t_INTEGER_LAURENT(n,vc) OP n,vc;
{
    if((S_O_K(n)!=INTEGER)&&(S_O_K(n)!=LONGINT))
        return error("t_INTEGER_LAURENT: first argument not an integer");
    m_il_nla(2L,vc);
    copy(n,S_LA_I(vc,1L));
    return(OK);
}


/*
transforms an object of type MONOPOLY or POLYNOM or INTEGER or
BRUCH into an object of type LAURENT
*/

INT t_OBJ_LAURENT(obj,vc) OP obj,vc;
{
    switch(S_O_K(obj))
    {
        case MONOPOLY:
            return t_MONOPOLY_LAURENT(obj,vc);
        case POLYNOM:
            return t_POLYNOM_LAURENT(obj,vc);
        case INTEGER:
            return t_INTEGER_LAURENT(obj,vc);
        case BRUCH:
            return t_BRUCH_LAURENT(obj,vc);
        default:
            return error("t_OBJ_LAURENT: wrong first type");        }
}

INT invers_laurent(lau, res) OP lau,res;
{
    INT erg = OK;
    CTO(LAURENT,"invers_laurent(1)",lau);
    erg += t_LAURENT_OBJ(lau,res);
    erg += invers(res,res);
/*
    erg += b_ou_b(callocobject(),callocobject(),res);
    M_I_I((INT)1,S_B_O(res));
    erg += copy(lau,S_B_U(res));
    C_B_I(res,GEKUERZT);
*/
    ENDR("invers_laurent");
}

INT addinvers_apply_laurent(lau) OP lau;
{
    INT i;
    INT erg  = OK;
    CTO(LAURENT,"addinvers_apply_laurent(1)",lau);
    for (i=1;i<S_LA_LI(lau);i++)
        erg += addinvers_apply(S_LA_I(lau,i));
    ENDR("addinvers_apply_laurent");
}

INT t_BRUCH_LAURENT(br,vc) OP br,vc;
/*CC 030196*/
{
    OP oo,uu,vc1,v,z,hh,u;
    INT i;

    krz(br);
    if(S_O_K(br) != BRUCH)
        return t_OBJ_LAURENT(br,vc);
    oo=S_B_O(br); uu=S_B_U(br);
    if(S_O_K(uu)==INTEGER || S_O_K(uu)==LONGINT)
    {
        vc1=callocobject();
        t_OBJ_LAURENT(oo,vc);
        copy(vc,vc1);
        for(i=1L;i<S_LA_LI(vc);i++)
            div(S_LA_I(vc1,i),uu,S_LA_I(vc,i));
        freeall(vc1); return OK;
    }
    if(S_O_K(uu)==POLYNOM)
    {
            if(has_one_variable(uu)==FALSE) return FALSE;
        u=callocobject(); init(MONOPOLY,u);
        z=uu;
        while(z!=NULL)
            {
                        hh=callocobject();
                        m_sk_mo(S_V_I(S_PO_S(z),0L),S_PO_K(z),hh);
                        insert(hh,u,add_koeff,NULL);
                    z=S_PO_N(z);
            }
        copy(u,uu); freeall(u);
    }
    if(S_O_K(uu)== MONOPOLY)
    {
        v=callocobject();
        t_MONOPOLY_LAURENT(uu,v);
        if(S_LA_LI(v) >2L)
        {
            freeall(v);
            return error("t_BRUCH_LAURENT: don't succeed in converting into Laurent polynomial");
        }
        t_OBJ_LAURENT(oo,vc); 
        vc1=callocobject();
        copy(vc,vc1);
        sub(S_LA_I(vc1,0L),S_LA_I(v,0L),S_LA_I(vc,0L));
        for(i=1L;i<S_LA_LI(vc);i++)
                        div(S_LA_I(vc1,i),S_LA_I(v,1L),S_LA_I(vc,i));
                freeall(vc1); 
        freeall(v); 
        return OK;
    }
    return OK;
}




INT unrank_subset(b,c,d) OP b,c,d;
/* AK 241006 V3.1 */
{
    INT k = S_I_I(b);
    INT i; 
    INT erg = OK;
    OP p ,oi,h,r;

    CE3(b,c,d,unrank_subset);

    CALLOCOBJECT4(p,oi,h,r);
    erg += copy(c,r);
    erg += m_l_v(b,d);
    for (i=k;i>=1;i--)
        {
        erg += m_i_i(i-1,p);
        erg += m_i_i(i,oi);
        do {
        erg += inc(p);
        erg += binom(p,oi,h);
        } while (ge(r,h));
        erg += dec(p);
        erg += binom(p,oi,h);
        erg += sub(r,h,r);
        erg += m_i_i(S_I_I(p)+1,S_V_I(d,i-1));
        }

    FREEALL4(p,oi,h,r);
    ENDR("unrank_subset");
}


INT unrank_k_subset(OP number, OP n, OP k, OP set)
/* die menge ist k-teilmenge von 1...n */
/* sortierung ist lexikographisch */
/* AK 241006 V3.1 */
{
INT erg =OK;
	OP h,b;
	INT i;
	// printf("number= "); print(number); printf(" n = ");print(n); printf(" k= ");println(k);

	if (S_O_K(set)!= VECTOR) m_l_v(k,set);
	else if (S_V_LI(set)!= S_I_I(k)) m_l_v(k,set);

	if (S_I_I(k)==S_I_I(n)) { 
		for(i=0;i<S_V_LI(set);i++) M_I_I(i+1,S_V_I(set,i));
		}
	else if (S_I_I(k)==1) { M_I_I(S_I_I(number)+1, S_V_I(set,0)); }
	else if (S_I_I(n)==1) { M_I_I(1, S_V_I(set,0)); }
	else
	{
		/* das erste element ist 1 falls number < (n-1 over k-1) */
		CALLOCOBJECT2(h,b);
		DEC_INTEGER(k);DEC_INTEGER(n); 
		if (S_I_I(n) <BINOMLIMIT)
			binom_small(n,k,b);
		else
			binom(n,k,b);
		INC_INTEGER(n); INC_INTEGER(k);
		// printf("binom = ");println(b);
		if (LT(number,b)) {
			DEC_INTEGER(n);DEC_INTEGER(k);
			unrank_k_subset(number,n,k,h);
			INC_INTEGER(n);INC_INTEGER(k);
			M_I_I(1,S_V_I(set,0));
			for(i=0;i<S_V_LI(h);i++)
				M_I_I(S_V_II(h,i)+1, S_V_I(set,i+1));
			}
		else {
		     DEC_INTEGER(n);
		     sub(number,b,h);
		     unrank_k_subset(h,n,k,set);
		     INC_INTEGER(n);
		     for(i=0;i<S_V_LI(set);i++)
			INC_INTEGER(S_V_I(set,i));
		     }
		FREEALL2(h,b);
	// println(set);
	}
ENDR("unrank_k_subset");
}

INT rank_k_subset(OP set, OP n, OP number)
/* AK 241006 V3.1 */
{
	INT erg = OK;
	CTTO(VECTOR,INTEGERVECTOR,"rank_k_subset(1)",set);
	CTO(INTEGER,"rank_k_subset(2)",n);
	{
	INT i;
	if (S_I_I(n)==1) M_I_I(0,number);
	else if (S_V_LI(set)==1) M_I_I(S_V_II(set,0)-1, number);
	else {
		OP h = CALLOCOBJECT();
		if (S_V_II(set,0) == 1) {
			OP sp=S_V_S(set);
			DEC_INTEGER(n);
			DEC_INTEGER(S_V_L(set));
			C_V_S(set,sp+1);
			for (i=0;i<S_V_LI(set);i++) DEC_INTEGER(S_V_I(set,i));
			rank_k_subset(set,n,number);
			for (i=0;i<S_V_LI(set);i++) INC_INTEGER(S_V_I(set,i));
			C_V_S(set,sp);
			INC_INTEGER(S_V_L(set));
			INC_INTEGER(n);
		 	}
		else    {
			DEC_INTEGER(n);DEC_INTEGER(S_V_L(set));
			if (S_I_I(n) <BINOMLIMIT)
				binom_small(n,S_V_L(set),h);
			else
				binom(n,S_V_L(set),h);
			INC_INTEGER(S_V_L(set));
			for (i=0;i<S_V_LI(set);i++) DEC_INTEGER(S_V_I(set,i));
			rank_k_subset(set,n,number);
			for (i=0;i<S_V_LI(set);i++) INC_INTEGER(S_V_I(set,i));
			INC_INTEGER(n);
			ADD_APPLY(h,number);
			}
		FREEALL(h);
		}
	}
	CTTO(INTEGER,LONGINT,"rank_k_subset(3e)",number);
	ENDR("rank_k_subset");
}



INT makevectorofsubsets(a,b,c) OP a,b,c;
/* AK 040204 */
/* b-subsets of a a-set */
{
    INT erg = OK;
    {
    OP d=callocobject();
    INT i;
    erg += binom(a,b,d); b_l_v(d,c);
    first_subset(a,b,S_V_I(c,0));
    for (i=0;i<S_V_LI(c)-1;i++) next_subset(S_V_I(c,i),S_V_I(c,i+1));
    }
    ENDR("makevectorofsubsets");
}



INT words_jn=0;
INT point(a,b,c) OP a,b,c;
/* a is a permutation pi
c = pi(b) */
{ COPY(S_P_I(a,S_I_I(b)-1),c); }

INT hashv(OP v) { INT erg = OK; return HASH(S_V_I(v,0)); ENDR("hashv"); }
INT eqv(OP a,OP b) { INT erg = OK;return EQ(S_V_I(a,0),S_V_I(b,0));ENDR("eqv");}
INT orbit_words(erz,root,res,f,sv) OP erz,root,res; INT (*f)(); OP sv;
{ words_jn=1; orbit(erz,root,res,f,sv); words_jn=0; }



static orbit_max_size = -1;
INT orbit_set_max_size(INT s)
/* sets a limit on the orbit size */
/* -1 = no limit */
/* AK 080306 V3.0 */
{ orbit_max_size=s; return OK; }

INT orbit(erz,root,res,f,sv) OP erz,root,res; INT (*f)(); OP sv;
/* bahn von root unter den erzeuger = res */
/* gruppen operation ist die funktion f */
/* sv wird vector von schreier erzeugern */
/* res ist die bahn = vector von objecten vom typ wie root */
/* sv kann NULL sein */
/* AK 080306 V3.0 */
{
    INT erg =OK;
    INT anz=0;
    OP cand,z,ares,fop,h,z1;INT i;
    OP perm;

    if (erz == sv) { 
       z=CALLOCOBJECT(); 
       COPY(erz,z); 
       erg += orbit(z,root,res,f,sv);
       FREEALL(z); 
       goto endr_ende;
       }

    cand=CALLOCOBJECT();

    h = CALLOCOBJECT(); init(HASHTABLE,h);  


    if (sv != NULL) erg += m_il_v(0,sv); /* vector of schreier generators */


    init(QUEUE,cand);
    z = CALLOCOBJECT(); erg += m_il_v(2,z); 
    COPY(root,S_V_I(z,0)); 
    if (sv != NULL) {
       if (words_jn==0)
          erg += eins(S_V_I(erz,0),S_V_I(z,1)); 
       else
          erg += m_il_v(0,S_V_I(z,1)); /* empty word at first position */
       }
    
    z1=CALLOCOBJECT();
    COPY(z,z1); 
    insert_hashtable(z1,h,NULL,NULL,hashv); 
    push(z,cand);

    z=pop(cand);
    while (z!=NULL)
    {
    for (i=0;i<S_V_LI(erz);i++)
        {
        INT in;OP z2;
        ares = CALLOCOBJECT();
        erg += m_il_v(2,ares);
        (*f)(S_V_I(erz,i),S_V_I(z,0),S_V_I(ares,0));
        z2 = find_hashtable(ares,h,eqv,hashv);
        if (z2 == NULL)
            {
            if (sv != NULL) {
                if (words_jn==0)
                    MULT(S_V_I(erz,i),S_V_I(z,1),S_V_I(ares,1));
                else
                    {
                    COPY(S_V_I(z,1),S_V_I(ares,1)); 
                    INC(S_V_I(ares,1));
                    M_I_I(i+1,S_V_I(S_V_I(ares,1),S_V_LI(S_V_I(ares,1))-1));
                    }
                }
    
            z1=CALLOCOBJECT();
            COPY(ares,z1); 
	    anz++;
            insert_hashtable(z1,h,NULL,NULL,hashv);
            push(ares,cand);
	    if ( (orbit_max_size != -1) && (anz > orbit_max_size) ) 
			goto end; 
            }
        else
            {
            OP perm,inv;
            if (sv != NULL) {
		    CALLOCOBJECT2(perm,inv);
                    if (words_jn==0) {
                        MULT(S_V_I(erz,i),S_V_I(z,1),perm);
                        INVERS(S_V_I(z2,1),inv);
                        MULT_APPLY(inv,perm);
                        }
                    else            {
                        INT ii,jj;
                        m_il_v(S_V_LI(S_V_I(z,1))+1+S_V_LI(S_V_I(z2,1)),perm);
                        for (ii=0;ii<S_V_LI(S_V_I(z,1));ii++) 
                            M_I_I(S_V_II(S_V_I(z,1),ii),S_V_I(perm,ii));
                        M_I_I(i+1,S_V_I(perm,ii));ii++;
                        for (jj=S_V_LI(S_V_I(z2,1))-1;jj>=0;ii++,jj--) 
                            M_I_I(-S_V_II(S_V_I(z2,1),jj),S_V_I(perm,ii));
                        }
    
                    in = index_vector(perm,sv);
                    if (in == -1) {
                         INC(sv); 
                         COPY(perm, S_V_I(sv,S_V_LI(sv)-1)); 
                                 /* add the new schreier generator */
                         }
                    FREEALL2(inv,perm);
                    }
            FREEALL(ares);
            }
        }
    FREEALL(z);
    z = pop(cand);
    }
   
end: 
    erg += m_il_v(WEIGHT_HASHTABLE(h),res); 
    i=0;
    FORALL(z,h,{COPY(S_V_I(z,0),S_V_I(res,i)); i++; });
    FREEALL2(h,cand);
    ENDR("orbit");
}





static all_orbits_trace=0;
static INT (*all_orbits_rankf)()=NULL;
INT all_orbits_set_trace() { all_orbits_trace=1; }
INT all_orbits_unset_trace() { all_orbits_trace=0; }
INT all_orbits_set_rankf(f) INT (*f)(); { all_orbits_rankf=f; }
INT all_orbits_unset_rankf()  { all_orbits_rankf=NULL; }

INT all_orbits(X,erz,bahnen,no,f) OP X,erz,bahnen,no; INT (*f)();
/* berechnet alle bahnen von erz auf der menge X
   die menge X wird sortiert
   in bahnen steht danach die bahnnr beginnend mit 1 
   die anzahl der bahnen ist in no 
*/
{
   INT erg = OK;
   CTO(VECTOR,"all_orbits(1)",X);
   CTO(VECTOR,"all_orbits(2)",erz);
   {
   INT nextbahn=0;  // naechste unverbrauchte element
   INT bahnnr=1;
   OP c;

   // ein test ob identität bei den erzeugern 
   // das kostet zeit
   {
   INT i;
   for (i=0;i<S_V_LI(erz);i++)
       {
       if (EINSP(S_V_I(erz,i))) 
		{
		OP cerz=CALLOCOBJECT();
		delete_entry_vector(erz,i,cerz);
nni:
		for (;i<S_V_LI(cerz);i++)
			if (EINSP(S_V_I(cerz,i))) 
				{ delete_entry_vector(cerz,i,cerz);
	                          goto nni;
				}
		all_orbits(X,cerz,bahnen,no,f);
		FREEALL(cerz);
		goto endr_ende;
		}
       }
   }


   // bei den erzeugern ist keine id dabei
   erg += qsort_vector(X);
   erg += m_l_nv(S_V_L(X),bahnen);

   c = CALLOCOBJECT();
nn:
   if (all_orbits_trace) printf("orbit number %d\n",bahnnr);
   erg += orbit(erz,S_V_I(X,nextbahn), c, f, NULL);


   if (all_orbits_rankf != NULL) // mit rankfunktion suchen in X
	{
	OP ra = CALLOCOBJECT();
	INT rai,j;
	for (j=0;j<S_V_LI(c);j++)
		{
		(*all_orbits_rankf)(S_V_I(c,j),ra);
		rai=S_I_I(ra);
/*
		if (rai==312) 
			{
			printf("orbit number %d nextbahn %d\n",bahnnr,nextbahn);
			println(S_V_I(X,nextbahn));
			println(S_V_I(c,j));
			}
*/
		if (S_V_II(bahnen,rai)!= 0) error("all_orbits:rank function error");
/*
		if (neq(S_V_I(c,j),S_V_I(X,rai))) {
			printf("rai=%d\n",rai);
			println(S_V_I(c,j));
			println(S_V_I(X,rai));
			error("all_orbits:diff elements");
			}
*/
		M_I_I(bahnnr,S_V_I(bahnen,rai));
		}
        nextbahn=-1;
	for (j=0;j<S_V_LI(bahnen);j++)
		if (S_V_II(bahnen,j)==0) { nextbahn=j; break; }
	FREEALL(ra);
	}
   else
   {
	   INT j,k=0;
	   erg += qsort_vector(c);
	   nextbahn=-1;
	   for (j=0;j<S_V_LI(c);j++)
	       {
	       while (  (S_V_II(bahnen,k) > 0)  // dies sind elemente zu anderen bahnen  AK290607
			||
			(NEQ(S_V_I(c,j),S_V_I(X,k)))
			) 
		   {
		   if (S_V_II(bahnen,k)==0) nextbahn=k; 
				/* nextbahn next element from X not in known orbit */
		   k++;
		   }
	       M_I_I(bahnnr,S_V_I(bahnen,k));
	       }
	   while (k<S_V_LI(X)) 
	       { 
	       if (S_V_II(bahnen,k)==0) { nextbahn=k; break; }
	       k++; 
	       }
   }

   bahnnr++; 
   FREESELF(c);
   if (nextbahn != -1) goto nn;

   FREEALL(c);
   if (no != NULL) m_i_i(bahnnr-1,no);
   }
   CTO(VECTOR,"all_orbits(3-e)",bahnen);
   ENDR("all_orbits");
}
