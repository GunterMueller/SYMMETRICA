
#include "def.h"
#include "macro.h"

static INT ausgabe_koeff();
static INT write_polynom();




/* global variables for output */
    INT zeilenposition;
    INT texposition;
    INT texmath_yn; /* 1 in mathmode */ /* 0 not in mathmode */
    INT scanoutput_yn; /* 1 no output */ /* 0 bitte output */
    INT row_length = 70; 
    INT tex_row_length = 70; 
    INT integer_format = 0; /* no format */

INT print_type(a) OBJECTKIND a;
/* AK 280294 */
/* AK 240398 V2.0 */
{
    OP b;
    INT erg = OK;

    b = CALLOCOBJECT();
    C_O_K(b,a);
    erg += printobjectkind(b);
    C_O_K(b,EMPTY);
    FREEALL(b);

    ENDR("print_type");
}

INT printobjectkind(a) OP a;
/* AK 270689 V1.0 */ /* AK 020290 V1.1 */ /* AK 130891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    if (a == NULL) 
        {
        fprintf(stderr,"object is NULL object\n");
        goto endr_ende; 
        }
    fprintf(stderr,"kind of object is ");
    
    switch(S_O_K(a))
        {
    case AUG_PART: fprintf(stderr,"augpart\n");break;
    case BARPERM: fprintf(stderr,"barred permutation\n");break;
    case BINTREE: fprintf(stderr,"bintree\n");break;
    case BITVECTOR: fprintf(stderr,"bitvector\n");break;
    case BRUCH: fprintf(stderr,"bruch\n");break;
    case CHARPARTITION: fprintf(stderr,"internal type charpartition\n");break;
    case COMPOSITION: fprintf(stderr,"composition\n");break;
    case CYCLOTOMIC: fprintf(stderr,"cyclotomic\n");break;
    case ELM_SYM: fprintf(stderr,"elementary symmetric function\n");break;
    case FF: fprintf(stderr,"finite field element\n");break;
	case GALOISRING: fprintf(stderr,"galois ring element\n");break;
    case GRAL: fprintf(stderr,"groupalgebra\n");break;
    case HOM_SYM: fprintf(stderr,"complete symmetric function\n");break;
    case INTEGER: fprintf(stderr,"integer\n");break;
    case KOSTKA: fprintf(stderr,"kostka\n");break;
    case KRANZ: fprintf(stderr,"kranz\n");break;
    case KRANZTYPUS: fprintf(stderr,"kranztypus\n");break;
        case LAURENT: fprintf(stderr,"laurent\n");break;
    case LIST: fprintf(stderr,"list\n");break;
    case LONGINT: fprintf(stderr,"longint\n");break;
    case INTEGERMATRIX: fprintf(stderr,"integermatrix\n");break;
    case MATRIX: fprintf(stderr,"matrix\n");break;
    case MONOM: fprintf(stderr,"monom\n");break;
    case MONOMIAL: fprintf(stderr,"monomial symmetric function\n");break;
    case MONOPOLY: fprintf(stderr,"monopoly\n");break;
    case PARTITION: fprintf(stderr,"partition\n");break;
    case PERMUTATION: fprintf(stderr,"permutation\n");break;
    case POLYNOM: fprintf(stderr,"polynom\n");break;
    case POW_SYM: fprintf(stderr,"powersum symmetric function\n");break;
    case REIHE: fprintf(stderr,"power-series\n");break;
    case SCHUR: fprintf(stderr,"schur-polynom\n");break;
    case SCHUBERT: fprintf(stderr,"schubert-polynom\n");break;
    case SKEWPARTITION: fprintf(stderr,"skewpartition\n");break;
    case SQ_RADICAL: fprintf(stderr,"square-radical\n");break;
    case SUBSET: fprintf(stderr,"subset\n");break;
    case SYMCHAR: fprintf(stderr,"symchar\n");break;
    case TABLEAUX: fprintf(stderr,"tableaux\n");break;
    case VECTOR: fprintf(stderr,"vector\n");break;
    case WORD: fprintf(stderr,"word\n");break;
    case HASHTABLE: fprintf(stderr,"hashtable\n");break;
    case INTEGERVECTOR: fprintf(stderr,"integervector\n");break;
    case (OBJECTKIND) 0: fprintf(stderr,"empty-object\n");break;
    default: fprintf(stderr," %ld ",S_O_K(a));
        fprintf(stderr,"unknown\n");
        break;
        };
    ENDR("printobjectkind");
    }

INT ferrers(obj) OP obj;
/* AK 290986 */ /* AK 010889 V1.0 */ /* AK 020290 V1.1 */
/* AK 130891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    COP("ferrers(1)",obj);

    switch(S_O_K(obj)) {
#ifdef PARTTRUE
        case PARTITION: erg +=  ferrers_partition(obj); break;
#endif /* PARTTRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: erg +=  ferrers_skewpartition(obj); break;
#endif /* SKEWPARTTRUE */
        default:  
            erg += WTO("ferrers",obj); break;
        }
    ENDR("ferrers");
    }


INT scan_printeingabe(text) char *text;
/* AK 250194 */
/* AK 240398 V2.0 */
    {
    extern INT scanoutput_yn; /* 1 no output */ /* 0 bitte output */
    if (scanoutput_yn == (INT) 0)
        return printeingabe(text);
    return OK;
    }

INT printeingabe(text) char *text;
/* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 070291 V1.2 prints to stderr instead to stdout , returns OK */
/* AK 130891 V1.3 */
/* AK 240398 V2.0 */
    { 
    fprintf(stderr,"%s\n",text); 
    return OK;
    }

INT sprint(string, obj) char *string; OP obj;
/* AK 020195 */
/* to get length of string use strlen */
/* AK 240398 V2.0 */
{
    INT erg = OK;
    COP("sprint(2)",obj);
    COP("sprint(1)",string);

    switch(S_O_K(obj))
        {
#ifdef FFTRUE
        case FF:
            erg+= sprint_ff(string,obj);
            goto spe;
#endif
        case INTEGER: 
            erg+= sprint_integer(string,obj);
            goto spe;
#ifdef LONGINTTRUE
        case LONGINT: 
            erg+= sprint_longint(string,obj);
            goto spe;
#endif /* LONGINTTRUE */
#ifdef PARTTRUE
        case SKEWPARTITION: 
            erg+= sprint_skewpartition(string,obj);
            goto spe;
        case PARTITION: 
            erg+= sprint_partition(string,obj);
            goto spe;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION:
            erg+= sprint_permutation(string,obj);
            goto spe;
#endif /* PERMTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR: 
            erg+= sprint_integervector(string,obj);
            goto spe;
        case VECTOR: 
            erg+= sprint_vector(string,obj);
            goto spe;
#endif /* VECTORTRUE */

        default: 
            WTO("sprint(1)",obj); 
            goto spe;
        }
spe:
    ENDR("sprint");
}

INT fprint(of,obj) FILE    *of; OP obj;
/* AK 211186 */ /* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 050891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    COP("fprint(1)",of);
    COP("fprint(2)",obj);

    switch(S_O_K(obj))
        {
#ifdef PARTTRUE
        case AUG_PART: 
        case PARTITION:  erg += fprint_partition(of,obj);break;
#endif /* PARTTRUE */
#ifdef BINTREETRUE
        case BINTREE:  erg += fprint_bintree(of,obj);break;
#endif /* BINTREETRUE */
#ifdef BRUCHTRUE
        case BRUCH:  erg += fprint_bruch(of,obj);break;
#endif /* BRUCHTRUE */
#ifdef FFTRUE
        case FF:  erg += fprint_ff(of,obj);break;
#endif /* FFTRUE */
#ifdef INTEGERTRUE
        case INTEGER:  erg += fprint_integer(of,obj);break;
#endif /* INTEGERTRUE */
#ifdef LISTTRUE
        case ELM_SYM: case MONOMIAL: case HOM_SYM: case POW_SYM:
        case GRAL: case MONOPOLY: case POLYNOM: case SCHUBERT:
        case SCHUR: case LIST:  
            erg += fprint_list(of,obj);break;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT:  erg += fprint_longint(of,obj);break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case KOSTKA:
        case KRANZTYPUS:
        case INTEGERMATRIX:
        case MATRIX:  erg += fprint_matrix(of,obj);break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM:  erg += fprint_monom(of,obj);break;
#endif /* MONOMTRUE */
#ifdef PERMTRUE
        case PERMUTATION:  erg += fprint_permutation(of,obj);
                break;
#endif /* PERMTRUE */
#ifdef REIHETRUE
        case REIHE:  erg += fprint_reihe(of,obj);
                break;
#endif /* REIHETRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: /*020488 */
             erg += fprint_skewpartition(of,obj);break;
#endif /* SKEWPARTTRUE */
#ifdef CHARTRUE
        case SYMCHAR: /*110488 */
             erg += fprint_symchar(of,obj);break;
#endif /* CHARTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX: /*020488 */
             erg += fprint_tableaux(of,obj);break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case QUEUE:
             erg += fprint_queue(of,obj);break;
        case HASHTABLE:
             erg += fprint_hashtable(of,obj);break;
        case COMPOSITION:
        case SUBSET:
        case WORD:
        case KRANZ:
        case INTEGERVECTOR:
        case GALOISRING:
        case LAURENT:
        case VECTOR:    erg += fprint_vector(of,obj);break;
        case BITVECTOR:    erg += fprint_bitvector(of,obj);break;
#endif /* VECTORTRUE */
#ifdef    NUMBERTRUE
        case SQ_RADICAL:
        case CYCLOTOMIC:  erg += fprint_number(of,obj);break;
#endif /* NUMBERTRUE */
        case 0:     
            fprintf(of,"#");
            /* AK 310889 */
            if (of == stdout) 
                zeilenposition++;
             break;
        default: erg += WTO("fprint",obj); 
            break;
        };

    ENDR("fprint");
    }

INT display(obj) OP obj;
/* AK 271087 */ /* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 130891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    COP("display(1)",obj);

    switch(S_O_K(obj))
        {
#ifdef SCHUBERTTRUE
        case SCHUBERT: 
            erg += display_schubert(obj);
            break;
#endif /* SCHUBERTTRUE */
        default: 
            erg += WTO("display(1)",obj);
            break;
        };
    ENDR("display");
    }
 
INT fprintln(f,obj) FILE *f; OP obj;
/* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 130891 V1.3 */ /* AK 240398 V2.0 */
/* AK 201204 V3.0 */
    {
    INT erg = OK;
    COP("fprintln(1)",f);
    COP("fprintln(2)",obj);

    erg += fprint(f,obj); 
    putc('\n',f);
    if (f == stdout) zeilenposition = 0;
    ENDR("fprintln");
    }

INT check_zeilenposition(f) FILE *f;
/* AK 201204 */
    {
    if (f==stdout) {
        /* printf("(zp=%d)",zeilenposition); */
        if (zeilenposition > row_length) { putchar('\n'); zeilenposition=0; }
        }
    return OK;
    }



INT print(obj) OP obj;
/* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 130891 V1.3 */ /* AK 240398 V2.0 */ 
/* AK 201204 V3.0 */
    {
    INT erg = OK;
    COP("print(1)",obj);
    erg += check_zeilenposition(stdout);
    erg += fprint(stdout,obj);
    ENDR("print");
    }



INT println(obj) OP obj;
/* AK 270689 V1.0 */ /* AK 020290 V1.1 */
/* AK 130891 V1.3 */
/* AK 240398 V2.0 */
{
    INT erg = OK;
    COP("println(1)",obj);
    erg += print(obj); 
    putchar('\n'); zeilenposition = 0;
    ENDR("println");
}


INT skip_comment()
/* AK 240398 V2.0 */
{
    int i;
/* here we insert code to implement comments *//* AK 210395 */
sa:
    i = getc(stdin);
    if (i == EOF)
        return error("scan:EOF encountered");
    else if (i==' ') goto sa;
    else if (i=='\t') goto sa;
    else if (i=='#') /* comments til the end of line */
        {
        while ((i=getc(stdin)) != '\n');
        goto sa;
        }
    else ungetc(i,stdin);
    return OK;
}


INT scan(kind,obj) OBJECTKIND kind; OP obj;
/* AK 270787 */ /* AK 280689 V1.0 */ /* AK 020290 V1.1 */ /* AK 050891 V1.3 */
/* AK 240298 V2.0 */
{
    INT erg = OK;
    COP("scan(2)",obj);

    if (not EMPTYP(obj)) 
        erg += freeself(obj);

    switch(kind)
        {
#ifdef BRUCHTRUE
        case BRUCH: erg += scan_bruch(obj); break;
        case INTEGERBRUCH: erg += scan_integerbruch(obj); break;
#endif /* BRUCHTRUE */
#ifdef CYCLOTRUE
        case CYCLOTOMIC: erg += scan_cyclo(obj); break;
#endif /* CYCLOTRUE */
#ifdef ELMSYMTRUE
        case ELM_SYM: erg += scan_elmsym(obj); break;
#endif /* ELMSYMTRUE */
#ifdef GRALTRUE
        case GRAL: erg += scan_gral(obj); break;
#endif /* GRALTRUE */
#ifdef FFTRUE
        case FF: erg += scan_ff(obj); break;
#endif /* FFTRUE */
#ifdef HOMSYMTRUE
        case HOM_SYM: erg += scan_homsym(obj); break;
#endif /* HOMSYMTRUE */
#ifdef INTEGERTRUE
        case INTEGER: erg += scan_integer(obj); break;
#endif /* INTEGERTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR: erg += scan_integervector(obj); break;
#endif /* VECTORTRUE */
#ifdef MATRIXTRUE
        case INTEGERMATRIX: erg += scan_integermatrix(obj); break;
#endif /* MATRIXTRUE */
#ifdef KOSTKATRUE
        case KOSTKA: erg += scan_kostka(obj); break;
#endif /* KOSTKATRUE */
#ifdef KRANZTRUE
        case KRANZ: erg += scan_kranz(obj); break;
#endif /* KRANZTRUE */
#ifdef LAURENTTRUE
                case LAURENT: erg += scan_laurent(obj); break;
#endif /* LAURENTTRUE */
#ifdef LISTTRUE
        case LIST: erg += scan_list(obj,(OBJECTKIND)0); break;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT: erg += scan_longint(obj); break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case KRANZTYPUS:
            erg += scan_matrix(obj);
            C_O_K(obj,KRANZTYPUS);
            break;
        case MATRIX: erg += scan_matrix(obj); break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM: erg += scan_monom(obj); break;
#endif /* MONOMTRUE */
#ifdef MONOMIALTRUE
        case MONOMIAL: erg += scan_monomial(obj); break;
#endif /* MONOMIALTRUE */
#ifdef MONOPOLYTRUE
        case MONOPOLY: erg += scan_monopoly(obj); break;
#endif /* MONOPOLYTRUE */
#ifdef PARTTRUE
        case REVERSEPARTITION: erg += scan_reversepartition(obj); 
            break;
        case EXPONENTPARTITION: erg += scan_exponentpartition(obj); 
            break;
        case PARTITION: erg += scan_partition(obj); break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case BARPERM:    erg += scan_bar(obj); break;
        case PERMUTATION: erg += scan_permutation(obj); break;
#endif /* PERMTRUE */
#ifdef POLYTRUE
        case FASTPOLYNOM: erg += scan_fastpolynom(obj); break;
        case POLYNOM: erg += scan_polynom(obj); break;
#endif /* POLYTRUE */
#ifdef POWSYMTRUE
        case POW_SYM: erg += scan_powsym(obj); break;
#endif /* POWSYMTRUE */
#ifdef REIHETRUE
        case REIHE: erg += scan_reihe(obj); break;
#endif /* REIHETRUE */
#ifdef SCHUBERTTRUE
        case SCHUBERT: erg += scan_schubert(obj); break;
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE
        case SCHUR: erg += scan_schur(obj); break;
#endif /* SCHURTRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: erg += scan_skewpartition(obj); break;
#endif /* SKEWPARTTRUE */
#ifdef SQRADTRUE
        case SQ_RADICAL: erg += scan_sqrad(obj); break;
#endif /* SQRADTRUE */
#ifdef CHARTRUE
        case SYMCHAR: erg += scan_symchar(obj); break;
#endif /* CHARTRUE */
#ifdef TABLEAUXTRUE
        case PARTTABLEAUX: 
            erg += scan_parttableaux(obj); 
            break;
        case SKEWTABLEAUX: 
            erg += scan_skewtableaux(obj); 
            break;
        case TABLEAUX: 
            erg += scan_tableaux(obj); 
            break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case VECTOR: 
            erg += scan_vector(obj); break;
        case BITVECTOR: 
            erg += scan_bitvector(obj); break;
        case PERMUTATIONVECTOR: 
            erg += scan_permvector(obj); break;
#endif /* VECTORTRUE */
#ifdef WORDTRUE
        case WORD: erg += scan_word(obj); break;
#endif /* WORDTRUE */
        default:
            {
            fprintf(stderr,"kind = %ld\n",kind);
            erg += error("scan:wrong type");
            goto endr_ende;
            }
        };
    ENDR("scan");
    }

INT skip(t,kind) char *t; OBJECTKIND kind;
/* AK 300998 */
/* return >= 0 gives the offset in t after the given object */
    {
    INT erg = OK;
    COP("skip(1)",t);

    switch(kind)
        {
        case INTEGER:
            {
            erg = skip_integer(t);
            if (erg >= 0) return erg;
            }
        default:
            {
            fprintf(stderr,"kind = %ld\n",kind);
            erg += error("skip:wrong type");
            goto endr_ende;
            }
        }
    ENDR("skip");
    }

INT sscan(t,kind,obj) char *t; OBJECTKIND kind; OP obj;
/* AK 301293 */
    {
    INT erg = OK;
    COP("sscan(1)",t);
    COP("sscan(3)",obj);

    if (not EMPTYP(obj)) 
        erg += freeself(obj);
    switch(kind)
        {
#ifdef INTEGERTRUE
        case INTEGER: erg += sscan_integer(t,obj); break;
#endif /* INTEGERTRUE */
#ifdef VECTORTRUE
        case BITVECTOR: erg += sscan_bitvector(t,obj); break;
        case INTEGERVECTOR: erg += sscan_integervector(t,obj); break;
        case PERMUTATIONVECTOR: erg += sscan_permvector(t,obj); break;
#endif /* VECTORTRUE */
#ifdef LONGINTTRUE
        case LONGINT: erg += sscan_longint(t,obj); break;
#endif /* LONGINTTRUE */
#ifdef PARTTRUE
        case PARTITION: 
            erg += sscan_partition(t,obj); 
            break;
        case REVERSEPARTITION: 
            erg += sscan_reversepartition(t,obj); 
            break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case BARPERM: erg += sscan_bar(t,obj); break;
        case PERMUTATION: erg += sscan_permutation(t,obj); break;
#endif /* PERMTRUE */
#ifdef SCHURTRUE
        case ELMSYM: erg += sscan_elmsym(t,obj); break;
        case HOMSYM: erg += sscan_homsym(t,obj); break;
        case SCHUR: erg += sscan_schur(t,obj); break;
#endif /* SCHURTRUE */
#ifdef WORDTRUE
        case WORD: erg += sscan_word(t,obj); break;
#endif /* WORDTRUE */


        default:
            {
            fprintf(stderr,"kind = %ld\n",kind);
            error("sscan:wrong type");
            return(ERROR);
            }
        };
    ENDR("sscan");
    }

OBJECTKIND scanobjectkind()
/* routine zum einlesen des objecttyps 160787 */
/* AK 280689 V1.0 */ /* AK 020290 V1.1 */
/* AK 070291 V1.2 works with stderr instead of stdin */
/* AK 130891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg;
    INT i = 0L;
    
    printeingabe("enter kind of object");
    /* hier sind neue objecttypen einzufuegen */
    
#ifdef INTEGERTRUE
    fprintf(stderr,"integer     [1]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* INTEGERTRUE */
#ifdef VECTORTRUE
    fprintf(stderr,"vector      [2]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* VECTORTRUE */
#ifdef PARTTRUE
    fprintf(stderr,"partition   [3]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* PARTTRUE */
#ifdef BRUCHTRUE
    fprintf(stderr,"bruch       [4]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* BRUCHTRUE */
#ifdef PERMTRUE
    fprintf(stderr,"permutation [6]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* PERMTRUE */
#ifdef SKEWPARTTRUE
    fprintf(stderr,"skewpart    [7]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* SKEWPARTTRUE */
#ifdef TABLEAUXTRUE
    fprintf(stderr,"tableaux    [8]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* TABLEAUXTRUE */
#ifdef POLYTRUE
    fprintf(stderr,"polynom     [9]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* POLYTRUE */
#ifdef SCHURTRUE
    fprintf(stderr,"schurfunk  [10]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* SCHURTRUE */
#ifdef MATRIXTRUE
    fprintf(stderr,"matrix     [11]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* MATRIXTRUE */
#ifdef HOMSYMTRUE
    fprintf(stderr,"homsym     [13]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* HOMSYMTRUE */
#ifdef SCHUBERTTRUE
    fprintf(stderr,"schubert   [14]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* SCHUBERTTRUE */
#ifdef KOSTKATRUE
    fprintf(stderr,"kostka     [16]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* KOSTKATRUE */
#ifdef CHARTRUE
    fprintf(stderr,"symchar    [18]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* CHARTRUE */
#ifdef WORDTRUE
    fprintf(stderr,"word       [19]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* WORDTRUE */
#ifdef LISTTRUE
    fprintf(stderr,"list       [20]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
    fprintf(stderr,"longint    [22]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* LONGINTTRUE */
#ifdef POWSYMTRUE
    fprintf(stderr,"powersum   [28]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* POWSYMTRUE */
#ifdef MONOMIALTRUE
    fprintf(stderr,"mon. sym.  [29]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* MONOMIALTRUE */
#ifdef GRALTRUE
    fprintf(stderr,"groupalg.  [32]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* GRALTRUE */
#ifdef ELMSYMTRUE
    fprintf(stderr,"elm. sym.  [33]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* ELMSYMTRUE */
#ifdef FFTRUE
    fprintf(stderr,"fin. field [35]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* FFTRUE */
#ifdef REIHETRUE
    fprintf(stderr,"reihe      [36]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* REIHETRUE */
#ifdef CYCLOTRUE
    fprintf(stderr,"cyclotomic [41]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* CYCLOTRUE */
#ifdef MONOPOLYTRUE
    fprintf(stderr,"monopoly   [42]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* MONOPOLYTRUE */
#ifdef SQRADTRUE
    fprintf(stderr,"radical    [43]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* SQRADTRUE */
    fprintf(stderr,"bitvector  [44]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#ifdef LAURENTTRUE
    fprintf(stderr,"laurent    [45]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;
#endif /* LAURENTTRUE */
    fprintf(stderr,"barperm    [46]"); 
    if (i++ == 4L)fprintf(stderr,"\n"),i=0L;

    fprintf(stderr,"\nwhat kind:? ");
    scanf("%ld",&erg);
    if (erg == 46) erg = BARPERM;
    return (OBJECTKIND)erg;
    }

INT objectread(f,obj) FILE *f; OP obj;
/* AK 131086 */ /* AK 280689 V1.0 */ /* AK 160190 V1.1 */ /* AK 020591 V1.2 */
/* AK 090891 V1.3 */
/* AK 240398 V2.0 */
    {
    OBJECTKIND kind;
    INT c,erg=OK,i;
    COP("objectread(1)",f);
    COP("objectread(2)",obj);

    FREESELF(obj);
    i=fscanf(f,"%ld",&c);
    SYMCHECK(i!=1,"objectread:could not read datatype");
    kind = (OBJECTKIND)c;
    switch(kind)
        {
        case (OBJECTKIND)0:    
            break;
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += objectread_bruch(f,obj);
            break;
#endif /* BRUCHTRUE */
#ifdef FFTRUE
        case FF: 
            erg += objectread_ff(f,obj);
            break;
#endif /* FFTRUE */
#ifdef INTEGERTRUE
        case INTEGER: 
            erg += objectread_integer(f,obj);
            break;
#endif /* INTEGERTRUE */
#ifdef LISTTRUE
        case GRAL: case HOM_SYM: case POW_SYM: case MONOMIAL:
        case ELM_SYM: case SCHUR: case MONOPOLY: case POLYNOM:
        case SCHUBERT: case LIST:     
            erg += objectread_list(f,obj);
            C_O_K(obj,kind); 
            break;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT: 
            erg += objectread_longint(f,obj);
            break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case MATRIX: 
            erg += objectread_matrix(f,obj);
            break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM: 
            erg += objectread_monom(f,obj);
            break;
#endif /* MONOMTRUE */
#ifdef    NUMBERTRUE
        case SQ_RADICAL: 
            erg += OBJECTREAD_SQRAD(f,obj);
            break;
        case CYCLOTOMIC: 
            erg += OBJECTREAD_CYCLO(f,obj);
            break;
#endif /* NUMBERTRUE */
#ifdef PARTTRUE
        case PARTITION: 
            erg += objectread_partition(f,obj);
            break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION: 
            erg += objectread_permutation(f,obj);
            break;
#endif /* PERMTRUE */
#ifdef CHARTRUE
        case SYMCHAR: 
            erg += objectread_symchar(f,obj);
            break;
#endif /* CHARTRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: 
            erg += objectread_skewpartition(f,obj);
            break;
#endif /* SKEWPARTTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX: 
            erg += objectread_tableaux(f,obj); 
            break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case HASHTABLE:
	   erg += objectread_hashtable(f,obj);
	   break;
        case COMPOSITION:
        case INTEGERVECTOR:
        case VECTOR: 
	case GALOISRING:
            erg += objectread_vector(f,obj); 
            C_O_K(obj,c);
            break;
        case BITVECTOR: 
            erg += objectread_bv(f,obj); 
            break;
#endif /* VECTORTRUE */
        default:  
            fprintf(stderr,"kind = %ld\n",kind);
            erg += error("objectread:wrong type"); 
            goto oe;
        };
oe:
    ENDR("objectread");
    }

INT objectwrite(f,obj) FILE *f; OP obj;
/* AK 131086 */ /* AK 280689 V1.0 */ /* AK 160190 V1.1 */
/* AK 090891 V1.3 */
/* AK 240398 V2.0 */
    {
    INT erg = OK;
    COP("objectwrite(1)",f);
    COP("objectwrite(2)",obj);

    switch(S_O_K(obj))
        {
        case 0: fprintf(f," %ld ",0L); return(OK);
#ifdef BRUCHTRUE
        case BRUCH: erg += objectwrite_bruch(f,obj);break;
#endif /* BRUCHTRUE */
#ifdef FFTRUE
        case FF: erg += objectwrite_ff(f,obj);break;
#endif /* FFTRUE */
#ifdef INTEGERTRUE
        case INTEGER: erg += objectwrite_integer(f,obj);break;
#endif /* INTEGERTRUE */
#ifdef LISTTRUE
        case GRAL: case HOM_SYM: case POW_SYM:
        case ELM_SYM: case MONOMIAL: case SCHUR: case MONOPOLY:
        case POLYNOM: case SCHUBERT: case LIST: 
            erg += objectwrite_list(f,obj);
            break;
#endif /* LISTTRUE */
#ifdef LONGINTTRUE
        case LONGINT: erg += objectwrite_longint(f,obj);break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
        case KRANZTYPUS: /* AK 220492 */
        case MATRIX:  erg += objectwrite_matrix(f,obj);break;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM: erg += objectwrite_monom(f,obj);break;
#endif /* MONOMTRUE */
#ifdef    NUMBERTRUE
        case SQ_RADICAL:
        case CYCLOTOMIC: erg += objectwrite_number(f,obj);break;
#endif /* NUMBERTRUE */
#ifdef PARTTRUE
        case PARTITION: erg += objectwrite_partition(f,obj);break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION:erg += objectwrite_permutation(f,obj);break;
#endif /* PERMTRUE */
#ifdef CHARTRUE
        case SYMCHAR:erg += objectwrite_symchar(f,obj);break;
#endif /* CHARTRUE */
#ifdef SKEWPARTTRUE
        case SKEWPARTITION: erg += objectwrite_skewpartition(f,obj);
                break;
#endif /* SKEWPARTTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX: erg += objectwrite_tableaux(f,obj);break;
#endif /* TABLEAUXTRUE */
#ifdef VECTORTRUE
        case HASHTABLE:
	   erg += objectwrite_hashtable(f,obj);
	   break;
        case INTEGERVECTOR:
        case COMPOSITION:
	case GALOISRING:
        case VECTOR: erg += objectwrite_vector(f,obj);break;
        case BITVECTOR: erg += objectwrite_bv(f,obj); break;
#endif
        default:
            {
            printobjectkind(obj);
            return error("objectwrite:wrong type");
            }
        };
    ENDR("objectwrite");
    }


INT tex(obj) OP obj;
/* tex-output of the object obj */
/* AK 101187 */ /* AK 060789 V1.0 */ /* AK 020290 V1.1 */
/* AK 300791 V1.3 */    
/* AK 260298 V2.0 */
    {
    INT erg = OK;
    /* es folgen zwei sonderfaelle */
    EOP("tex(1)",obj);

    switch(S_O_K(obj))
        {
#ifdef BRUCHTRUE
        case BRUCH: erg +=  tex_bruch(obj);break;
#endif /* BRUCHTRUE */
#ifdef CYCLOTRUE
        case CYCLOTOMIC: erg += tex_cyclo(obj); break;
#endif /* CYCLOTRUE */
#ifdef INTEGERTRUE
        case INTEGER: erg +=  tex_integer(obj);break;
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
        case LONGINT: erg +=  tex_longint(obj); break;
#endif /* LONGINTTRUE */
#ifdef MONOPOLYTRUE
        case MONOPOLY: erg +=  tex_monopoly(obj); break;
#endif /* MONOPOLYTRUE */
#ifdef SCHUBERTTRUE
        case SCHUBERT: erg +=  tex_schubert(obj); break;
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE
        case MONOMIAL:
        case POW_SYM:
        case ELM_SYM:
        case HOM_SYM:
        case SCHUR:erg +=  tex_schur(obj); break;
#endif /* SCHURTRUE */
#ifdef CHARTRUE
        case SYMCHAR: erg += tex_symchar(obj); break;
#endif /* CHARTRUE */
        case GRAL:
#ifdef LISTTRUE
        case LIST: erg += tex_list(obj);break;
#endif /* LISTTRUE */
#ifdef MATRIXTRUE
        case KOSTKA:
        case MATRIX: erg += tex_matrix(obj);break;
            
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
        case MONOM: erg += tex_monom(obj);break;
#endif /* MONOMTRUE */
#ifdef PARTTRUE
        case PARTITION: erg+= tex_partition(obj);break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
        case PERMUTATION: erg+= tex_permutation(obj);break;
#endif /* PERMTRUE */
#ifdef POLYTRUE
        case POLYNOM: erg+= tex_polynom(obj);break;
#endif /* POLYTRUE */
#ifdef TABLEAUXTRUE
        case TABLEAUX: erg+= tex_tableaux(obj);break;
#endif /* TABLEAUXTRUE */
#ifdef SQRADTRUE
        case SQ_RADICAL: erg += tex_sqrad(obj);break;
#endif /* SQRADTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case SUBSET:
        case HASHTABLE:
        case COMPOSITION:
        case VECTOR:
            erg += tex_vector(obj);
            break;
#endif /* VECTORTRUE */
        default:
            WTO("tex",obj);
            break;
        };
    ENDR("tex");
    }


#ifdef MATRIXTRUE 
#ifdef POLYTRUE
INT latex_glm_dar(M) OP    M;
/* RH */
/* AK 280192 output to texout */
/* AK 240398 V2.0 */
{
    INT    i;
    INT    j;
    INT    k;
    INT    var = 1L;

    OP     moddy    =    callocobject();    
    OP     rest    =    callocobject();    
    OP    vier    =    callocobject();

    if(S_M_LI(M) >= 10) var = 1L;
    M_I_I(var,vier);
    ganzdiv(S_M_L(M),vier,moddy);
    mult(moddy,vier,vier);
    sub(S_M_L(M),vier,rest);

    if(S_I_I(moddy) != 0L)
    {
    fprintf(texout,"$$\n");
    fprintf(texout,"\\left[\n");
    for(i=0L;i<S_I_I(moddy);++i)
    {
            if(i != 0L)    
            {
                fprintf(texout,"$$\n");
                fprintf(texout,"\\left.\n");
            }
            fprintf(texout,"\\begin{array}{l");
            for(j=1L;j<var;++j) fprintf(texout,"|l");
            fprintf(texout,"}\n");
            for(j=0L;j<S_M_HI(M);++j)
            {
                for(k=0L;k<var;++k)
                {
                    write_polynom(S_M_IJ(M,j,var*i+k));
                    if(k != var-1L) fprintf(texout," & ");
                    else 
                            if(j != S_M_HI(M)-1L) 
                                fprintf(texout,"\\\\\\hline\n");
                            else    
                                fprintf(texout,"\\\\\n");
                }
            }
            fprintf(texout,"\\end{array}\n");
            if(i < S_I_I(moddy)-1L)
            {
            fprintf(texout,"\\right.\n");
            fprintf(texout,"$$\n");
            }
            else
            if(i < S_I_I(moddy))
            {
                if(S_I_I(rest) != 0L)
                {
                    fprintf(texout,"\\right.\n");
                    fprintf(texout,"$$\n");
                }
                else
                {
                    fprintf(texout,"\\right]\n");
                    fprintf(texout,"$$\n");
                }
            }
    }
    }
    if(S_I_I(rest) != 0L)
    {
    fprintf(texout,"\n\\bigskip\n");
    fprintf(texout,"$$\n");
    if(S_I_I(moddy) != 0)
        fprintf(texout,"\\left.\n");
    else
        fprintf(texout,"\\left[\n");
    fprintf(texout,"\\begin{array}{l");
    for(j=1L;j<S_I_I(rest)-1L;++j)
        fprintf(texout,"|l");
    fprintf(texout,"|l}\n");
    for(j=0L;j<S_M_HI(M);++j)
    {
        for(k=0L;k<S_I_I(rest);++k)
        {
            write_polynom(S_M_IJ(M,j,var*S_I_I(moddy)+k));
            if(k != S_I_I(rest)-1L) fprintf(texout," & ");
            else 
                if(j != S_M_HI(M)-1L) fprintf(texout,"\\\\\\hline\n");
                else    fprintf(texout,"\\\\\n");
        }
    }
    fprintf(texout,"\\end{array}\n");
    fprintf(texout,"\\right]\n");
    fprintf(texout,"$$\n");
    }

    freeall(moddy);
    freeall(rest);
    freeall(vier);
    return OK;
}
#endif /* POLYTRUE */
#endif /* MATRIXTRUE */

#ifdef POLYTRUE
static INT write_polynom(poly) OP    poly;
/* AK 280192 output to texout */
/* AK 240398 V2.0 */
{
    INT    k,l;
    OP    z = poly;

    while(z != NULL)
    {
        if(!nullp(s_po_k(z)) && !emptyp(s_po_k(z)))    
        {
            ausgabe_koeff(s_po_k(z));
            for(k=0L;k<S_M_HI(s_po_s(z));++k)
            {
                for(l=0L;l<S_M_LI(s_po_s(z));++l)
                    if(S_M_IJI(s_po_s(z),k,l) > 0L)

                        if(S_M_IJI(s_po_s(z),k,l) == 1L)
                            fprintf(texout,"x_{%ld %ld} ",k+1L,l+1L);
                        else
                            fprintf(texout,"x_{%ld %ld}^{%ld} ",k+1L,l+1L,S_M_IJI(s_po_s(z),k,l));
            }
            if(S_PO_N(z) != NULL)    
            {
                fprintf(texout,"+");
            }
        }
        z = S_PO_N(z);
    }
    return OK;
}
#endif /* POLYTRUE */

static INT ausgabe_koeff(k) OP    k;
/* AK 280192 output to texout */
/* AK 240398 V2.0 */
{
            switch(S_O_K(k))
            { 
                case INTEGER: 
                {
                    if(S_I_I(k) == 1L)
                        break;

                    if(S_I_I(k) == -1L)
                    {
                        fprintf(texout,"-");
                        break;
                    }
                    print(k);
                    break;
                }
#ifdef BRUCHTRUE
                case BRUCH: 
                {
                    kuerzen(k);
                    fprintf(texout,"\\frac{");
                    ausgabe_koeff(S_B_O(k));
                    fprintf(texout,"}{");
                    ausgabe_koeff(S_B_U(k));
                    fprintf(texout,"}");
                    break;
                }
#endif /* BRUCHTRUE */
#ifdef NUMBERTRUE
                case SQ_RADICAL: 
                {
                    OP    ptr = S_N_S(k);
                    while(ptr != NULL)
                    {
                    fprintf(texout,"\\sqrt{");
                    ausgabe_koeff(S_PO_S(ptr));
                    fprintf(texout,"}");
                    ptr = S_L_N(ptr);
                    }
                    break;
                }
#endif /* NUMBERTRUE */
                default:
                {
                printobjectkind(k);
                error("unknown type of coefficient !!!\n");
                break;
                }
            }
return OK;
}

