/* SYMMETRICA perm.c */
#include "def.h"
#include "macro.h"

static struct permutation * callocpermutation();
/* static INT free_permutation(); */
static INT co_div_040989();
static INT co040989();
static INT mem_counter_perm;
static OP old_kranz_tafel; /* speichert letzte kranztafel */
static INT co_120194();
static INT co_120194_1();
static INT co_co();
static INT co_co_2();
#define CPT(typ,text,a) CTO(PERMUTATION,text,a);if (S_P_K(a) != typ) \
fprintf(stderr,\
"wrong typ of permutation in %s\n typ should be %ld and it was %ld\n "\
,text,typ,S_O_K(a));
#define CPTT(typ,typ2,text,a) CTO(PERMUTATION,text,a);if \
((S_P_K(a) != typ)&&(S_P_K(a) != typ2)) \
fprintf(stderr,\
"wrong typ of permutation in %s\n typ should be %ld or %ld and it was %ld\n "\
,text,typ,typ2,S_O_K(a));


#ifdef PERMTRUE
INT unrank_permutation(a,b) OP a,b;
/* AK 140597 */
/* AK 151104 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGER, LONGINT, "unrank_permutation(1)",a);
    {
    OP c,d;
    /* get the degree */
    CALLOCOBJECT2(c,d);
    M_I_I((INT)1, d);
again:
    erg += fakul(d,c); 
    if (lt(c,a) ) { INC(c); goto again; }
    DEC(c);
    erg += unrank_degree_permutation(a,c,b);
    FREEALL2(c,d);
    }
    ENDR("unrank_permutation");
}

INT unrank_degree_permutation(a,c,b) OP a,c,b;
/* AK 200597 */
/* AK 151104 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"unrank_degree_permutation(1)",a);
    CTO(INTEGER,"unrank_degree_permutation(2)",c);
    {
    INT i;
    OP d,e,f,g;
    CALLOCOBJECT4(d,e,f,g);

    erg += m_l_v(c,d);
    COPY(c,e);
    COPY(a,g);
    for (i=0;i<S_V_LI(d);i++)
        {
        DEC(e); 
        erg += fakul(e,f);
        erg += quores(g,f,S_V_I(d,i),g);
        }
    FREEALL3(e,f,g);
    erg += lehmercode(d,b);
    FREEALL(d);
    }
    ENDR("unrank_degree_permutation");
}

INT rank_permutation(a,b) OP a,b;
/* AK 160295 */
/* a and b may be equal */
/* result is integer >= 0 */
/* AK 151104 V3.0 */

{
    INT erg = OK;
    CTO(PERMUTATION,"rank_permutation",a);
    CPT(VECTOR,"rank_permutation",a);
    {
    OP f,c,d;
    INT i,j;
    CALLOCOBJECT3(c,d,f);
    erg += lehmercode(a,f);
    erg += m_i_i(0L,b);
    for (i=0,j=S_P_LI(a);i<S_P_LI(a);j--,i++)
        {
        erg += m_i_i(j-1,d);
        erg += fakul(d,c);
        MULT_APPLY(S_V_I(f,i),c);
        ADD_APPLY(c,b);
        }
    erg += t_longint_int(b,b);
    FREEALL3(c,d,f);
    }
    ENDR("rank_permutation");
}
      
INT perm_anfang()
/* AK 100893 */
/* AK 110804 V3.0 */
    {
    INT erg = OK;
    {
    old_kranz_tafel=CALLOCOBJECT();
    mem_counter_perm=0L;
    }
    ENDR("perm_anfang");
    }

static OP next_perm_v = NULL;
static OP zykeltyp_perm_v = NULL;
INT perm_ende()
/* AK 100893 */
    {
    INT erg = OK;
    erg += freeall(old_kranz_tafel);
    if (mem_counter_perm != 0L)
        {
        fprintf(stderr,"mem_counter_perm = %ld\n",mem_counter_perm);
        erg += error("permutation memory not freed");
        }
    if (next_perm_v != NULL)
        {
        erg += freeall(next_perm_v);
        next_perm_v = NULL;
        }
    if (zykeltyp_perm_v != NULL)
        {
        erg += freeall(zykeltyp_perm_v);
        zykeltyp_perm_v = NULL;
        }
    return erg;
    }

INT even_permutation(a) OP a;
/* AK 010692 */
    {
    INT erg;
    OP c;
    c = callocobject();
    numberof_inversionen(a,c);
    erg = even(c);
    freeall(c);
    return erg;
    }
#endif /* PERMTRUE */

INT permutationp(a) OP a;
/* AK 150891 V1.3 */
    {
    if (S_O_K(a) != PERMUTATION) return FALSE;
    else return TRUE;
    }

#ifdef PERMTRUE
#ifdef MATRIXTRUE

INT diagramm_permutation(perm,mat) OP perm,mat;
/* 0 at the position i,perm[i] */ 
/* else empty object */
/* AK 010988 */ /* AK 170889 V1.1 */ /* AK 150891 V1.3 */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CPT(VECTOR,"diagramm_permutation(1)",perm);
    CE2(perm,mat,diagramm_permutation);

        {
        INT i,j;
        OP l,h;

        l=CALLOCOBJECT();
        h=CALLOCOBJECT();

        COPY_INTEGER(S_P_L(perm),h);
        COPY_INTEGER(S_P_L(perm),l);
        erg += b_lh_m(l,h,mat);
    
        /* but the  0  at the right position */
        for (i=0L, j= S_P_LI(perm)-1;i<S_P_LI(perm);i++,j--)
            M_I_I(0,S_M_IJ(mat,j,S_P_II(perm,i)-1));

        }
    CTO(MATRIX,"diagramm_permutation(2e)",mat);
    ENDR("diagramm_permutation");
}
#endif /* MATRIXTRUE */

#ifdef TABLEAUXTRUE
INT red_dia_perm(p,e) OP p,e;
/* ein allgemeines tableau zu der perm */
/* AK 010988 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,k,m;

    diagramm_permutation(p,e);
    for (j=0L;j<S_M_LI(e); j++)
    {
        k=j+1;
        for (i=S_M_HI(e)-1;i>=0 ; i--)
        {
            if (EMPTYP(S_M_IJ(e,i,j)))
            {
                M_I_I(k,S_M_IJ(e,i,j)) ;
                k++;
            }
            else if (S_M_IJI(e,i,j) == -1L) freeself(S_M_IJ(e,i,j));
            else if (S_M_IJI(e,i,j) == 0L)
            {
                freeself(S_M_IJ(e,i,j));
                for (m=j+1; m<S_M_LI(e);m++)
                    M_I_I(-1L,S_M_IJ(e,i,m));
                for (m=i-1; m>=0 ; m--)
                    if (not EMPTYP(S_M_IJ(e,m,j)))
                        if (S_M_IJI(e,m,j) == -1L)
                            freeself(S_M_IJ(e,m,j));
                break;
            }
            else return error("red_dia_perm:wrong content");
        }
    }
    return(OK);
}



INT first_tab_perm(a,c) OP a,c;
/* AK 010988 */ /* das erste tableau */ /* AK 151289 V1.1 */
/* AK 150891 V1.3 */
{
    OP b;
    INT erg = OK;
    CTO(PERMUTATION,"first_tab_perm(1)",a);
    b = callocobject();
    erg += red_dia_perm(a,b);
    erg += fill_left_down_matrix(b);
    erg += m_matrix_tableaux(b,c);
    ENDR("first_tab_perm");
}
#endif /* TABLEAUXTRUE */

INT fill_left_down_matrix(b) OP b;
/* AK 060988 */
/* schiebt inhalt einer matrix nach links, dann nach unten,
sofern dieser inhalt integer zahlen */
/* AK 051289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,k,l,m;
    for (i=S_M_HI(b)-1; i>=0L; i--)
    {
        k=0L;
        for (j=0L;j<S_M_LI(b); j++)
            if (not EMPTYP(S_M_IJ(b,i,j)))
            {
                m=S_M_IJI(b,i,j);
                /* der zu verschiebende eintrag */
                /* k ist die spalte in der der
                        eintrag hinkommt */
                freeself(S_M_IJ(b,i,j));
                for (l=S_M_HI(b)-1; l>=0L; l--)
                    if (EMPTYP(S_M_IJ(b,l,k))) break;
                /* l ist die zeile in der der
                        eintrag hinkommt */
                M_I_I(m,S_M_IJ(b,l,k));
                k++;
            }

    }
    return(OK);
}


#ifdef POLYTRUE
INT divideddiff_rz(rzt,poly,ergebnis) OP    rzt, poly, ergebnis;
/* 270887 zur berechnung des ergebnis des operators  delta bei
anwendung auf das polynom poly */
/* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i = 0 ;
    INT erg = OK;
    CTO(POLYNOM,"divideddiff_rz",poly);
    CE3(rzt,poly,ergebnis,divideddiff_rz);

    erg += copy_polynom(poly,ergebnis);

    if (EMPTYP(rzt)) 
        goto endr_ende;

    while (i < S_V_LI(rzt))
    { 
        erg += divideddifference(S_V_I(rzt,i),ergebnis,ergebnis);
        i++; 
    };
    ENDR("divideddiff_rz");
}


INT max_divideddiff(n,poly,e) OP n,poly,e;
/* applies the maximal permutation */
/* AK 180291 V1.2 */ /* AK 150891 V1.3 */
{
    OP p = callocobject();
    INT erg=OK; 

    if ((erg=last_permutation(n,p)) != OK) goto md1;
    if ((erg=divideddiff_permutation(p,poly,e)) != OK) goto md1;
    md1:
    freeall(p);
    return erg;
}


INT divideddiff_permutation(perm,poly,c) OP     perm,poly,c;
/* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150591 V1.2 */
/* AK 150891 V1.3 */
{
    OP rzt;
    INT erg = OK;

    CTO(PERMUTATION,"divideddiff_permutation",perm);

    rzt = callocobject();
    erg += rz_perm(perm,rzt); 
    erg += divideddiff_rz(rzt,poly,c);
    erg += freeall(rzt); 
    ENDR("divideddiff_permutation");
}

INT divideddiff_lc(lc,poly,c) OP     lc,poly,c;
/* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK; /* AK 020392 */
    OP    rzt;
    CTTO(INTEGERVECTOR,VECTOR,"divideddiff_lc(1)",lc);
    CTO(POLYNOM,"divideddiff_lc(2)",poly);

    rzt = callocobject();
    erg += rz_lehmercode(lc,rzt); 
    erg += divideddiff_rz(rzt,poly,c);
    erg += freeall(rzt); 
    ENDR("divideddiff_lc");
}

INT divdiff(a,b,c) OP a,b,c;
/* AK 180393 */
{
    INT erg = OK;    
    COP("divdiff(1)",a);
    COP("divdiff(2)",b);
    COP("divdiff(3)",c);
    CE3(a,b,c,divdiff);

    switch(S_O_K(a))
        {
        case INTEGER:
            switch(S_O_K(b))
                {
                case POLYNOM:
                    erg += divideddifference(a,b,c);
                    break;
#ifdef SCHUBERTTRUE
                case SCHUBERT:
                    erg += divdiff_schubert(a,b,c);
                    break;
#endif
                default:
                    erg += WTT("divdiff",a,b);
                    break;
                };
            break;
        case PERMUTATION:
            if (S_P_K(a) == VECTOR)
            {
            switch(S_O_K(b))
    
                {
                case POLYNOM:
                    erg += divideddiff_permutation(a,b,c);
                    break;
#ifdef SCHUBERTTRUE
                case SCHUBERT:
                    erg += divdiff_perm_schubert(a,b,c);
                    break;
#endif
                default:
                    erg += WTT("divdiff",a,b);
                    break;
                };
            break;
            }
            if (S_P_K(a) == BAR)
            {
            switch(S_O_K(b))
    
                {
                case POLYNOM:
                    erg += divdiff_bar(a,b,c);
                    break;
                };
            break;
            }
        default:
            erg += WTT("divdiff",a,b);
            break;
        }
    ENDR("divdiff");
}



INT divideddifference(i,poly,c) OP i,poly,c;
/* AK 270887
zur berechnung des ergebnis des operators  delta_i bei
anwendung auf das polynom poly */
/* AK 110789 V1.0 */ /* AK 151289 V1.1 */ /* AK 150891 V1.3 */
{

    OP     zeiger, zwischen;
    INT     index,j,k, expo1, expo2 ,erg = OK;

    CTO(INTEGER,"divideddifference(1)",i);
    CTO(POLYNOM,"divideddifference(2)",poly);
    index = S_I_I(i) -1L;
    SYMCHECK(index < 0, "divideddifference:index < 1");
    CE3(i,poly,c,divideddifference);
        
    
    init(POLYNOM,c);
        
    if (EMPTYP(poly)) 
        goto rr;
    if (S_L_S(poly) == NULL) /* AK 040392 */
        {
        erg +=  copy(poly,c);
        goto rr;
        }

    zwischen = callocobject();
    zeiger = poly;
    while (zeiger != NULL)
    {
        if (S_L_S(zeiger) == NULL)
        {
            error("divideddifference:self == NULL");
            erg += ERROR;
            goto rr;
        }
        if (not VECTORP(S_PO_S(zeiger))) 
        { 
            printobjectkind(S_PO_S(zeiger));
            error("kind != VECTOR in divideddifference");
            erg += ERROR;
            goto rr;
        };

        if (S_I_I(i) == S_PO_SLI(zeiger))
        /* operiert auf letzten exponenten */
        { 
            erg += inc(S_PO_S(zeiger));
            M_I_I(0L,S_PO_SI(zeiger,S_I_I(i))); 
        }
        else if (S_I_I(i) > S_PO_SLI(zeiger)) goto dividedend;
        expo1 = S_PO_SII(zeiger,index);
        expo2 = S_PO_SII(zeiger,index + 1L);
        if (expo1 > expo2)
        {
            for (j=expo1-1L,k=expo2 ;j>= expo2; j--,k++)
            { 
            erg += b_skn_po(callocobject(),callocobject(),NULL,zwischen);
            erg += copy(S_PO_S(zeiger),S_PO_S(zwischen));
            erg += copy(S_PO_K(zeiger),S_PO_K(zwischen));
            M_I_I(j,S_PO_SI(zwischen,index));
            M_I_I(k,S_PO_SI(zwischen,index+1L));
            erg += add_apply(zwischen,c);
            erg += freeself(zwischen);
            };
        }
        else if (expo1 < expo2)
        {
            for (j=expo2-1L,k=expo1 ;j>= expo1; j--,k++)
            {
            erg += b_skn_po(callocobject(),callocobject(),NULL,zwischen);
            COPY(S_PO_S(zeiger),S_PO_S(zwischen));
            erg += addinvers(S_PO_K(zeiger),S_PO_K(zwischen));
            M_I_I(j,S_PO_SI(zwischen,index));
            M_I_I(k,S_PO_SI(zwischen,index+1));
            erg += add_apply(zwischen,c);
            erg += freeself(zwischen);
            }
        };
dividedend:
        zeiger = S_PO_N(zeiger);
    };
    FREEALL(zwischen); 
rr:
    ENDR("divideddifference");
}
#endif /* POLYTRUE */

#endif /* PERMTRUE */

#ifdef KRANZTRUE

OP s_kr_g(a) OP a; 
/* select_kranz_grobpermutation */
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
/* AK 110804 V3.0 */
{ 
    INT erg = OK;
    CTO(KRANZ,"s_kr_g(1)",a);
    {
    return(s_v_i(a,0L)); 
    }
    ENDO("s_kr_g");
}

OP s_kr_v(a) OP a;
/* select_kranz_vector */ 
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(s_v_i(a,1L)); 
}

INT c_kr_g(a,b) OP a,b; 
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(c_v_i(a,0L,b)); 
}

INT c_kr_v(a,b) OP a,b; 
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(c_v_i(a,1L,b)); 
}

OP s_kr_i(a,i) OP a; INT i; 
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(s_v_i(s_kr_v(a),i)); 
}

INT s_kr_gli(a) OP a; 
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(s_p_li(s_kr_g(a))); 
}

OP s_kr_gi(a,i) OP a;  INT i;
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
/* AK 200804 V3.0 */
{ 
    INT erg = OK;
    CTO(KRANZ,"s_kr_gi(1)",a);
    SYMCHECK(i<0,"s_kr_gi(2)<0");
    {
    return s_p_i(s_kr_g(a),i); 
    }
    ENDO("s_kr_gi");
}


OP s_kr_gl(a) OP a;
/* AK 170889 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(s_p_l(s_kr_g(a))); 
}

INT init_kranz(a) OP a;
/* AK Fri Jan 27 12:29:38 MEZ 1989 */ 
/* AK 150891 V1.3 */
/* AK 110804 V3.0 */
{ 
    init(VECTOR,a); 
    m_il_v(2L,a); 
    C_O_K(a,KRANZ); 
    return(OK); 
}

INT b_perm_vector_kranz(p,v,a) OP p,v,a;
/* dies initialisiert eine kranz product struktur */
/* ein vector aus 2 teilen
    wobei der erste eintrag ein eine permutation aus der s_n
    der zweite eintrag ein vector von n eintraegen
    */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK;
    CTO(PERMUTATION,"b_perm_vector_kranz(1)",p);
    CTO(VECTOR,"b_perm_vector_kranz(2)",v);
    {
    erg += init(KRANZ,a); 
    c_kr_g(a,p); 
    c_kr_v(a,v); 
    }
    ENDR("b_perm_vector_kranz");
}

INT random_kranz(gn,vn,a) OP gn,vn,a;
/* random element of kranz produkt */
/* AK 120804 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"random_kranz(1)",gn);
    SYMCHECK(S_I_I(gn)<1,"random_kranz(1)<1");
    CTO(INTEGER,"random_kranz(2)",vn);
    SYMCHECK(S_I_I(vn)<1,"random_kranz(2)<1");
    CE3(gn,vn,a,random_kranz);
    {
    INT i;
    erg += init_kranz(a);
    erg += random_permutation(gn,S_KR_G(a));
    erg += m_l_v(gn,S_KR_V(a));
    for (i=0;i<S_I_I(gn);i++)
        erg += random_permutation(vn,S_KR_I(a,i));
    }
    ENDR("random_kranz");
}

INT scan_kranz(a) OP a;
/* AK 151289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i;
    INT erg = OK;
    CTO(EMPTY,"scan_kranz(1)",a);
    init(KRANZ,a);

    printeingabe("input of the elment of the wreath product of two");
    printeingabe("symmetric groups");
    printeingabe("input of the base permutation");
    scan(PERMUTATION,s_kr_g(a));
    erg += m_il_v(s_kr_gli(a),s_kr_v(a));
    for (i=0L;i<s_kr_gli(a);i++)
    {
        printf("input of the %ld. permutation permuted by the base permutation\n",i+1L);
        scan(PERMUTATION,s_kr_i(a,i));
    }
    ENDR("scan_kranz");
}

INT mult_kranz_kranz(a,b,c) OP a,b,c;
/* AK Fri Jan 27 14:13:14 MEZ 1989 */
/* multipliziert zwei elemente eines kranzprodukts */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
/* AK 120804 V3.0 */
{
    INT erg = OK; 
    CTO(KRANZ,"mult_kranz_kranz(1)",a);
    CTO(KRANZ,"mult_kranz_kranz(2)",b);
    CTO(EMPTY,"mult_kranz_kranz(3)",c);
    {
    erg += init(KRANZ,c);
    MULT(S_KR_G(a),S_KR_G(b),S_KR_G(c));
    /* grobperm. werden normal multipliziert */
    erg += operate_perm_vector(S_KR_G(b),S_KR_V(a),S_KR_V(c));
    erg += mult(S_KR_V(c),S_KR_V(b),S_KR_V(c));
    }
    ENDR("mult_kranz_kranz");
}

INT invers_kranz(a,b) OP a,b;
/* AK 030902 */
/* AK 120804 V3.0 */
{
    INT erg = OK;
    CTO(KRANZ,"invers_kranz(1)",a);
    CTO(EMPTY,"invers_kranz(2)",b);
    {
    INT i;
    erg += init(KRANZ,b);
    erg += invers_permutation(s_kr_g(a),s_kr_g(b));
    erg += m_il_v(s_kr_gli(a), s_kr_v(b));
    for (i=0;i<s_kr_gli(a);i++)
        erg += invers(s_kr_i(a,i),s_kr_i(b,i));
    erg += operate_perm_vector(s_kr_g(b),s_kr_v(b),s_kr_v(b));
    }
    ENDR("invers_kranz");
}

INT einsp_kranz(a) OP a;
/* AK 030902 */
/* AK 200804 V3.0 */
{
    INT erg = OK;
    CTO(KRANZ,"einsp_kranz(1)",a);
    {
    INT i;
    if (not einsp_permutation(S_KR_G(a))) return FALSE;
    for (i=0;i<S_KR_GLI(a);i++) 
        {
        if (not einsp(S_KR_I(a,i))) return FALSE;
        }
    return TRUE;
    }
    ENDR("einsp_kranz");
}

INT freeself_kranz(a) OP a;
/* AK 030902 */
{
    INT erg = OK;
    CTO(KRANZ,"freeself_kranz(1)",a);
    C_O_K(a,VECTOR);
    erg += freeself_vector(a);
    ENDR("freeself_kranz");
}

INT first_kranztypus(w,parts,c) OP w,parts,c;
/* AK 310889 */
/* kranztypus ist ein vector mit zwei eintraegen.
der erste eintrag eine komposition 
der zweite eintrag ist eine vector mit partitionen als 
komponeten.
*/
/* AK 181289 V1.1 */ /* AK 120691 V1.2 */ /* AK 150891 V1.3 */
{
    INT erg = OK;
    CTO(INTEGER,"first_kranztypus(1)",w);
    CTO(INTEGER,"first_kranztypus(2)",parts);
    CE3(w,parts,c,first_kranztypus);
    {
    INT i;
    OP a;

    erg += m_il_v(2L,c);
    erg += first_composition(w,parts,S_V_I(c,0L));
    erg += m_il_v(S_I_I(parts),S_V_I(c,1L));
    for (i=0L;i<S_I_I(parts);i++)
        {
        a =S_V_I(S_V_I(c,1L),i);
        if (not EMPTYP(a))
            erg += freeself(a);
        if (S_V_II(S_V_I(c,0L),i) > 0L)
            erg += first_partition(S_V_I(S_V_I(c,0L),i),a);
        }
    }
    ENDR("first_kranztypus");
}

INT next_kranztypus(alt,c) OP alt,c;
/* AK 310889 */
/* kranztypus ist ein vector mit zwei eintraegen.
der erste eintrag eine komposition 
der zweite eintrag ist eine vector mit partitionen als 
komponenten.
return TRUE falls ok
       FALSE falls letzter typus    
*/
/* AK 181289 V1.1 */ /* AK 130691 V1.2 */ /* AK 150891 V1.3 */
{
    INT i,j,l    ;
    OP a;
    OP b;
    if (alt != c) copy(alt,c);

    b = S_V_I(c,0L); /* die composition */
    l = S_V_LI(b); /* anzahl teile der composition */
    for (i=l-1;i>=0L;i--)
    {
        a = S_V_I(S_V_I(c,1L),i); /* partition */
        if (not EMPTYP(a))
            if (next(a,a)) goto nk310889;
    }
    if (i < 0L) if (next(b,b) == FALSE) return(FALSE);
nk310889:
    for (j=i+1; j < l; j++)
    {
        a = S_V_I(S_V_I(c,1L),j);
        if (not EMPTYP(a))
            freeself(a);
        if (S_V_II(b,j) > 0L) first_partition(S_V_I(b,j),a);
    }
    return(TRUE);
}
#endif /* KRANZTRUE */

INT makevectorof_kranztypus(w,parts,c) OP w,parts,c;
/* AK 310889 */ /* AK 181289 V1.1 */ /* AK 120691 V1.2 */ /* AK 150891 V1.3 */
{
    INT erg = ERROR;
#ifdef KRANZTRUE
    erg =OK;
    CTO(INTEGER,"makevectorof_kranztypus(1)",w);
    CTO(INTEGER,"makevectorof_kranztypus(2)",parts);
    CE3(w,parts,c,makevectorof_kranztypus);
    {
    OP a = callocobject();
    INT i=0L;
    erg += m_il_v(1L,c);
    erg += first_kranztypus(w,parts,a); /* ergebnis ist vector */
    COPY(a,S_V_I(c,0L));
    while (next_kranztypus(a,a)) 
        {
        INC(c);
        i++;
        COPY(a,S_V_I(c,i));
        }
    FREEALL(a);
    }
#endif
    ENDR("makevectorof_kranztypus");
}

INT kranztypus_to_matrix(a,b) OP a,b;
/* AK 010989 */
/* kranztypus als matrix */
/* b wird eine matrix */
/* kranztypus ist ein vector mit zwei eintraegen.
der erste eintrag eine komposition 
der zweite eintrag ist eine vector mit partitionen als 
komponeten. */
/* AK 081289 V1.1 */ /* AK 120691 V1.2 */ /* AK 150891 V1.3 */
/* AK 050902 V2.0 */
{
    INT erg = OK;
#ifdef KRANZTRUE
    CTO(VECTOR,"kranztypus_to_matrix(1)",a);
    SYMCHECK(S_V_LI(a)!=2,"kranztypus_to_matrix(1):wrong length of vector");
    CTO(COMPOSITION,"kranztypus_to_matrix(1.0)",S_V_I(a,0));
    CTO(VECTOR,"kranztypus_to_matrix(1.1)",S_V_I(a,1));
    CE2(a,b,kranztypus_to_matrix);
    {
    INT z,s,i,j;
    OP summe = callocobject();
    OP h1,h2;
    /* z = Anzahl der zeilen */
    /* s = Anzahl der spalten */
        
    s = S_V_LI(S_V_I(a,0L));
    sum(S_V_I(a,0L),summe);/* composition ist vector */
    z = S_I_I(summe);
    FREEALL(summe); 
    m_ilih_nm(s,z,b); 
    C_O_K(b,KRANZTYPUS);
    for (i=0L;i<s;i++)
    {
        h1 = S_V_I(a,0L); /* composition */
        if (S_V_II(h1,i) > 0L) {
            h2 = S_V_I(S_V_I(a,1L),i) ; /* i-te partition */
            for (j=0L;j<S_PA_LI(h2);j++)
                INC(S_M_IJ(b,S_PA_II(h2,j) -1L,i));
        }
    }
    }
#endif
    ENDR("kranztypus_to_matrix");
}

INT matrix_to_kranztypus(a,b) OP a,b;
/* AK 010989 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,s;
    OP h;
#ifdef KRANZTRUE
    if (not EMPTYP(b)) 
        freeself(b);

    m_il_v(2L,b);
    m_il_v(S_M_LI(a),S_V_I(b,1L));
    m_il_v(S_M_LI(a),S_V_I(b,0L));
    C_O_K(S_V_I(b,0L),COMPOSITION);
    for (j=0L;j<S_M_LI(a);j++)
    {
        s = 0L;
        for (i=0L;i<S_M_HI(a);i++)
            s = s + S_M_IJI(a,i,j)*(i+1L);
        /* s ist das gewicht */
        if (s > 0L) {
            h = S_V_I(S_V_I(b,1L),j);
            /* h ist die partition */
            b_ks_pa(EXPONENT,callocobject(),h);
            m_il_integervector(S_M_HI(a),S_PA_S(h));
            for (i=0L;i<S_M_HI(a);i++)
                M_I_I(S_M_IJI(a,i,j),S_PA_I(h,i));
            t_EXPONENT_VECTOR(h,h);
        }
        M_I_I(s,S_V_I(S_V_I(b,0L),j));
    }
#endif
    return(OK);
}

#ifdef KRANZTRUE
INT kranztypus_kranztypus_monom(a,b,c) OP a,b,c;
/* AK 010989 */
/* der erste kranztypus ist das F_lambda
der zweite eine klasse von der gleichen uneigentlichen partition 
das ergebnis ist ein monom induziert durch eine typus-matrix 
*/
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i;
    OP a1=S_V_I(a,0L);
    OP a2=S_V_I(a,1L),b2=S_V_I(b,1L);
    OP erg = callocobject();
    OP h1 = callocobject();
    
    if (not EMPTYP(c)) 
        freeself(c);
    b_skn_po(callocobject(),callocobject(),NULL,c);
    M_I_I(1L,S_PO_K(c));

    for (i=0L;i<S_V_LI(a1);i++)
    {
        if (S_V_II(a1,i) > 0L) {
            if (not EMPTYP(h1)) 
                if (S_O_K(h1) != INTEGER) freeself(h1);
            charvalue(S_V_I(a2,i),S_V_I(b2,i),erg,NULL);
            mult(erg,S_PO_K(c),h1);
            ordcen(S_V_I(b2,i),erg);
            div(h1,erg,S_PO_K(c));
        }
    }
    freeall(erg);
    freeall(h1);
    if (not nullp(S_PO_K(c)))
        kranztypus_to_matrix(b,S_PO_S(c));
    else freeself(c); /* polynom == list */
    return(OK);
}

INT kranztypus_charakteristik(a,b) OP a,b;
/* AK 010989 */ /* aus einem kranztypus wird F_lambda berechnet */
/* AK 181289 V1.1 */ /* AK 120691 V1.2 */ /* AK 150891 V1.3 */
{
    OP c,d;
    INT i;
    if (S_O_K(a) == KRANZTYPUS) {
        c = callocobject();
        matrix_to_kranztypus(a,c);
        kranztypus_charakteristik(c,b);
        freeall(c); 
        return(OK);
        }
/* a ist ein vektor */
    c = callocobject();
    copy(a,c);
    if (not EMPTYP(b)) 
        freeself(b);

    for (i=0L; i<S_V_LI(S_V_I(a,0L)); i++)
        if (S_V_II(S_V_I(a,0L),i) > 0L)
            first_partition(S_V_I(S_V_I(a,0L),i),
                S_V_I(S_V_I(c,1L),i));

    do {
        d = callocobject();
        kranztypus_kranztypus_monom(a,c,d);
        if (not EMPTYP(d)) 
            insert(d,b,NULL,NULL); 
        else 
            freeall(d);
    } while (
        next_kranztypus(c,c) && 
        eq( S_V_I(c,0L),S_V_I(a,0L))
        );

    freeall(c);
    return(OK);
}

INT charakteristik_to_ypolynom(a,b,grad,ct) OP a,b,grad,ct;
/* AK 040989 */
/* A ist charakteristik, b wird ypolynom */
/* grad ist der grad der symmetrischen gruppe G in GwrS_n*/
/* ct ist chartafel von S_n */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    OP z = a;
    OP c;
    OP partv = callocobject();

    makevectorofpart(grad,partv);
    if (not EMPTYP(b)) 
        freeself(b);

    while (z != NULL)
    {
         c = callocobject();
        matrix_monom_ypolynom(z,c,grad,partv,ct);
         insert(c,b,NULL,NULL);
        z = S_PO_N(z);
    }
    freeall(partv);
    return(OK);
}

INT matrix_monom_ypolynom(a,b,grad,partv,ct) OP a,b,grad,partv,ct;
/* AK 040989 */
/* eingabe a ist ein monom mit matrix kranztypus
ausgabe b ist ein gleiches polynom in den y variablen */
/* grad ist der grad der symmetrischen gruppe G in GwrS_n*/
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j;
    OP m=S_PO_S(a); /* matrix */
    OP c = callocobject();
    INT erg = OK;
    FREESELF(b);
    M_I_I(1L,b);
    for (i= 0L;i<S_M_HI(m); i++)
        for (j=0L;j<S_M_LI(m) ; j++)
        {
            if (S_M_IJI(m,i,j) > 0L) {
                s_x_nu_to_ypolynom(m,grad,i,j,c,partv,ct);
                MULT_APPLY(c,b);
            }
        }
    MULT_APPLY(S_PO_K(a),b);
    freeall(c);
    ENDR("matrix_monom_ypolynom");
}

INT s_x_nu_to_ypolynom(m,grad,i,j,c,partv,ct) INT i,j; OP m,grad,c,partv,ct;
/* AK 040989 */ /* ein einzelne transformation */ /* m ist die matrix */
/* c wird polynom */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i1,j1,i2;
        OP h1,h2,h3,d,f;
        INT erg = OK;
    h1 = callocobject();
    h2 = callocobject();
    h3 = callocobject();
    d = callocobject();
    f = callocobject();

    init(POLYNOM,c);
        
    erg += fakul(grad,f);
    for (i2=0L;i2<S_V_LI(partv);i2++)
    {
        COPY(S_M_IJ(ct,j,i2),h2);
        /* equiv zu
    charvalue_tafel_part(S_V_I(partv,j),S_V_I(partv,i2),h2,ct,partv);
        */
        if (nullp(h2)) continue;
        erg += ordcon(S_V_I(partv,i2),h1);
        FREESELF(d);
        erg += b_skn_po(callocobject(),callocobject(),NULL,d);
        erg += div(h1,f,h3);
        MULT(h3,h2,S_PO_K(d));
        erg += m_ilih_m(S_M_LI(m),S_M_HI(m),S_PO_S(d));
        C_O_K(S_PO_S(d),KRANZTYPUS);
        for (i1=0L;i1<S_M_HI(m);i1++)
            for (j1=0L;j1<S_M_LI(m);j1++)
                M_I_I(0L,S_M_IJ(S_PO_S(d),i1,j1));
        M_I_I(1L,S_M_IJ(S_PO_S(d),i,i2));
        erg += add_apply(d,c);
    }

    erg += hoch(c,S_M_IJ(m,i,j),c);

    FREEALL(f);
    FREEALL(d);
    FREEALL(h2); 
    FREEALL(h3); 
    FREEALL(h1);

    ENDR("s_x_nu_to_ypolynom");
}

INT kranztafel(a,b,kt,d,h) OP a,b,kt,d,h;
/* a,b sind integer werte
kt wird die charaktertafel von s_b wr s_a
d wird der vektor der ordnung der konjugiertenklassen
h wird der vektor der label der konjugiertenklassen */
/* AK 181289 V1.1 */ /* AK 050391 V1.2 */ /* AK 150891 V1.3 */
{
    OP c,e,f,h1,ct,m;
    INT i;
    INT erg = OK;

    CTO(INTEGER,"kranztafel(1)",a);
    CTO(INTEGER,"kranztafel(2)",b);
    SYMCHECK(S_I_I(a) < 1,"kranztafel: a < 1");
    SYMCHECK(S_I_I(b) < 1,"kranztafel: b < 1");

    if (S_O_K(old_kranz_tafel) == VECTOR) /* AK 170893 */
    {
    if (S_V_II(old_kranz_tafel,0L) == S_I_I(a))
    if (S_V_II(old_kranz_tafel,1L) == S_I_I(b))
        {
        erg += copy(S_V_I(old_kranz_tafel,2L),kt);
        erg += copy(S_V_I(old_kranz_tafel,3L),d);
        erg += copy(S_V_I(old_kranz_tafel,4L),h);
        goto kt_ende;
        }
    }
    else
        erg += m_il_v(5L,old_kranz_tafel);

    c=callocobject(); e=callocobject(); f=callocobject(); 
    h1=callocobject(); ct=callocobject(); m=callocobject();


    if (not EMPTYP(kt)) 
        erg += freeself(kt);
    if (not EMPTYP(d)) 
        erg += freeself(d);
    if (not EMPTYP(h)) 
        erg += freeself(h);

    erg += makevectorofpart(b,f);
    erg += makevectorof_kranztypus(a,S_V_L(f),c);
    erg += m_il_v(S_V_LI(c),h);
    for(i = 0L; i<S_V_LI(c);i++) {
        erg += kranztypus_to_matrix(S_V_I(c,i),S_V_I(h,i)); 
    }
    
    erg += sort(h);

    erg += chartafel(b,ct);

    erg += m_ilih_m(S_V_LI(c),S_V_LI(c),kt);
    for(i = 0L; i<S_V_LI(h);i++) {
        erg += kranztypus_charakteristik(S_V_I(h,i),d);
        erg += charakteristik_to_ypolynom(d,e,b,ct);
        erg += co040989(e,kt,h,i);
        }

    erg += freeall(e); 
    erg += freeall(ct); 
    erg += freeall(c);

    erg += fakul(a,d);
    erg += fakul(b,m);
    erg += hoch(m,a,m);
    erg += mult_apply(d,m);
    erg += mult_apply(m,kt);

    erg += freeself(d);
    erg += m_il_v(S_V_LI(h),d);
    for(i = 0L; i<S_V_LI(h);i++) {
        erg += typusorder(S_V_I(h,i),b,a,S_V_I(d,i),f); 
    }

    erg += co_div_040989(kt,d);
    erg += freeall(f); 
    erg += freeall(h1); 
    erg += freeall(m);

    erg += copy(a,S_V_I(old_kranz_tafel,0L));
    erg += copy(b,S_V_I(old_kranz_tafel,1L));
    erg += copy(kt,S_V_I(old_kranz_tafel,2L));
    erg += copy(d,S_V_I(old_kranz_tafel,3L));
    erg += copy(h,S_V_I(old_kranz_tafel,4L));
kt_ende:
    ENDR("kranztafel");
}

INT latex_kranztafel(h,g,d) OP h,d,g;
/* AK 051289 V1.1 */
/* g ist matrix der charakterwerte
   d ist vector der ordnung der konjugiertenklassen
   h ist vector der label der konjugiertenklassen */
/* AK 070291 V1.2 texout for output */ /* AK 150891 V1.3 */
    {
    INT i,j,j1,i1;
    for (i=0L;i<S_V_LI(h); i++) {
        fprintf(texout,"$ %ld$ ",i+1L);
        tex(S_V_I(h,i));
        tex(S_V_I(d,i));
        fprintf(texout,"\n\n\\smallskip\n");
        }
    for (i=0L;i<S_M_HI(g);i+=15L)
        for (j=0L;j<S_M_LI(g);j+=15L)
        {
            fprintf(texout,"\n\\begin{tabular}{|c||");
            for (j1=j;(j1<S_M_LI(g))&&(j1<j+15L);j1++) fprintf(texout,"c|");
            fprintf(texout,"}\n  \\hline \n & ");
            for (j1=j;(j1<S_M_LI(g))&&(j1<j+15L);j1++) {
                fprintf(texout,"%ld",j1+1L);
                if ((j1+1 <j+15L) &&(j1+1 <S_M_LI(g))) fprintf(texout,"&"); 
            }
            fprintf(texout,"\n \\\\ \\hline \\hline");
            for (i1=i;(i1<S_M_HI(g))&&(i1<i+15L);i1++)
            {
                fprintf(texout,"\n %ld&",i1+1L);
                for (j1=j;(j1<S_M_LI(g))&&(j1<j+15L);j1++)
                { 
                    tex(S_M_IJ(g,i1,j1));
                    if ((j1+1 <j+15L) &&(j1+1 <S_M_LI(g))) fprintf(texout,"&"); 
                }
                fprintf(texout,"\n \\\\ \\hline");
            }
            fprintf(texout,"\n\\end{tabular} ");
        }
    return(OK);
    }

static INT co_div_040989(a,d) OP a,d;
/* AK dividiert die spalten durch den ersten eintrag */
/* d vector der klassenordnungen */
/* AK 081289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j;
    OP z;
    INT erg = OK;
    z = S_M_S(a);
    for (i=0L;i<S_M_HI(a);i++)
    for (j=0L;j<S_M_LI(a);j++)
    {
        erg += ganzdiv(z,S_V_I(d,j),z);
        z++;
    }
    return erg;
}


static INT co040989(a,b,c,i) OP a,b,c; INT i;
/* a ist ypoly, b ist matrix, c vector von matrixtypus, i ist zeile in Matrix */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i2=0L;
    OP z = a;
    OP m,ll;
    while ( z != NULL)
    {
        m = S_PO_S(z);
        while (NEQ(m,S_V_I(c,i2)))  { 
            ll = S_M_IJ(b,i,i2);
            if (not EMPTYP(ll))
                if (S_O_K(ll) != INTEGER) freeself(ll);
            M_I_I(0L,ll);
            i2++;
            if (i2 >= S_V_LI(c)) 
                {
                fprintf(stderr,"m=");
                fprintln(stderr,m);
                fprintf(stderr,"a=");
                fprintln(stderr,a);
                fprintf(stderr,"c=");
                fprintln(stderr,c);
                error("co040989: not found");    
                }
            }
        /* i2 ist jetzt der index */
        copy(S_PO_K(z),S_M_IJ(b,i,i2));
        i2++;
        z = S_PO_N(z);
    }
    z = S_M_IJ(b,i,i2);
    while(i2 < S_M_LI(b))  { 
        if(not EMPTYP(z)) if (S_O_K(z) != INTEGER) freeself(z);
        M_I_I(0L,z);
        i2++;z++;
    }
    return(OK);
}

INT typusorder(a,ggrad,ngrad,b,vec) OP b,a,ggrad,ngrad,vec;
/* ordnung der konjugiertenklasse mit typus==MATRIX
ggrad ist grad der symmetrischen gruppe G */
/* ngrad ist grad der symmetrischen gruppe S_n */
/* vec ist vector der partition von G */
/* result is b */
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j;
    OP f = callocobject();
    OP h = callocobject();
    OP p;
    OP k = callocobject();
    OP h1 = callocobject();
    OP h2 = callocobject();
    OP gorder = callocobject();
    INT erg = OK; /* AK 090692 */
    erg += fakul(ggrad,gorder);
    erg += hoch(gorder,ngrad,h2);
    erg += fakul(ngrad,h);
    MULT(h2,h,f);
    p = S_V_I(vec,0L);

    if (not EMPTYP(b)) 
            erg += freeself(b);
    M_I_I(1L,b);
    for (j=0L;j<S_M_LI(a);j++)
    {
        erg += ordcon(p,h);
        for (i=0L;i<S_M_HI(a);i++)
            if (S_M_IJI(a,i,j) != 0L) {
                FREESELF(k);
                FREESELF(h2);
                FREESELF(h1);
                M_I_I(i+1,k);
                MULT(gorder,k,h2);
                erg += div(h,h2,h1);
                erg += hoch(h1,S_M_IJ(a,i,j),k);
                erg += fakul(S_M_IJ(a,i,j),h1);
                erg += div(k,h1,h2);
                MULT_APPLY(h2,b);
            }
         p++; /* p is now next partition  */
    }
    MULT_APPLY(f,b);
    erg += freeall(f); erg += freeall(k); 
    erg += freeall(h1); erg += freeall(h);
    erg += freeall(gorder);erg += freeall(h2);
    ENDR("typusorder");
}
/* ende des teiles fuer das kranzprodukt */
#endif /* KRANZTRUE */


INT numberof_shufflepermutation(mx,n) OP mx,n;
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
#ifdef SHUFFLETRUE
    INT i;
    OP a=callocobject();
    OP b=callocobject();
    i=0L;
    first_permutation(n,b);
    do    { 
        copy(b,a); 
        i++; 
    }    while    (next_shufflepermutation(mx,a,b) != LASTSHUFFLE);

    freeall(b); 
    freeall(a); 
    return(i);
#else /* SHUFFLETRUE */
    return error("numberof_shufflepermutation:SHUFFLE not defined");
#endif /* SHUFFLETRUE */
}

INT next_shufflevector(mx,a,b) OP a,b; OP mx;
/* bsp 34555 --> 44555
       33344 --> 00444 */
/* AK 260789 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
#ifdef SHUFFLETRUE

    INT k,i;
    INT grenze = S_V_LI(a)-S_I_I(mx);
    copy(a,b);
    for (i=grenze-1L;i>=0L;i--)
        if (S_V_II(b,i) == 0L)
        { 
            M_I_I(1L,S_V_I(b,i));
            return(OK); 
        };
    for (i=1L;i<grenze;i++) /* i=1 statt i=0 */
        if (S_V_II(b,i) > S_V_II(b,i-1L)) break;

    k=i-1;
    if (eq(S_V_I(b,k),mx)) 
        return(LASTSHUFFLE);

    inc(S_V_I(b,k));
    for (i=k-1;i>=0L;i--) 
        M_I_I(0L,S_V_I(b,i));
    return OK;
#else /* SHUFFLETRUE */
    return error("next_shufflevector:SHUFFLE not defined");
#endif /* SHUFFLETRUE */
}

INT next_shufflepermutation(mx,perm,erg) OP mx,perm,erg;
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
#ifdef SHUFFLETRUE
    INT e;
    OP a=callocobject();
    OP b=callocobject();
    lehmercode(perm,a);
    e = next_shufflevector(mx,a,b);
    if (e != LASTSHUFFLE) 
        lehmercode(b,erg);
    freeall(a); 
    freeall(b); 
    return(e);
#else /* SHUFFLETRUE */
    return error("next_shufflepermutation:SHUFFLE not defined");
#endif /* SHUFFLETRUE */
}

#ifdef PERMTRUE
INT test_perm()
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();

    printf("test_perm:scan(a)");
    scan(PERMUTATION,a);
    println(a);
    printf("test_perm:copy(a,b)");
    copy(a,b);
    println(b);
    printf("test_perm:mult(a,b,b)");
    mult(a,b,b);
    println(b);
    printf("test_perm:invers(b,a)");
    invers(b,a);
    println(a);
    printf("test_perm:even(b)");
    if (even(b))
        printeingabe("is even");
    else
        printeingabe("is not even");
    printf("test_perm:inc(a)");
    inc(a);
    println(a);
    printf("test_perm:UD_permutation(a,b)");
    UD_permutation(a,b);
    println(b);
    printf("test_perm:random_permutation(134L,b)");
    m_i_i(134L,a);
    random_permutation(a,b);
    println(b);
    printf("test_perm:makevectoroftranspositions(5L,c)");
    m_i_i(5L,a);
    makevectoroftranspositions(a,c);
    println(c);

    freeall(a);
    freeall(b);
    freeall(c);
    return(OK);
}

INT tex_lc(perm) OP perm;
/* AK 101187 */ /* AK 100789 V1.0 */ /* AK 181289 V1.1 */
/* AK 070291 V1.2 prints to texout instead of stdout */ /* AK 150891 V1.3 */
{
    INT i;
    if (S_V_LI(perm)<10L)
    { 
        fprintf(texout,"\\ $"); 
        texposition += 2L;
        for (i=0L;i<S_V_LI(perm);i++)
        { 
            fprintf(texout,"%ld",S_V_II(perm,i)); 
            texposition ++; 
        }
        fprintf(texout,"$\\ "); 
        texposition += 3L;
    }
    else    { 
        fprintf(texout,"\\ $("); 
        texposition += 4L;
        for (i=0L;i<S_V_LI(perm);i++)
        { 
            fprintf(texout,"%ld",S_V_II(perm,i));
            if (i != S_V_LI(perm)-1L) fprintf(texout,",");
            texposition += 3L; 
        }
        fprintf(texout,")$\\ "); 
        texposition += 3L;
    };
    if (texposition >60L)
    { 
        fprintf(texout,"\n"); 
        texposition = 0L; 
    }
    return(OK);
}

INT tex_permutation(perm) OP perm;
/* AK 101187 */ /* AK 100789 V1.0 */ /* AK 181289 V1.1 */
/* AK 070291 V1.2 prints to texout instead of stdout */ /* AK 150891 V1.3 */
{
    INT i;
    if (S_P_LI(perm)<10L)
    { 
        fprintf(texout,"\\ $"); 
        texposition += 3L;
        for (i=0L;i<S_P_LI(perm);i++)
        { 
            fprintf(texout,"%ld",S_P_II(perm,i)); 
            texposition += 1L; 
        }
        fprintf(texout,"$\\ "); 
        texposition += 3L;
    }
    else    { 
        fprintf(texout,"\\ $(");
        for (i=0L;i<S_P_LI(perm);i++)
        { 
            texposition += 3L; 
            fprintf(texout,"%ld",S_P_II(perm,i));
            if (i != S_P_LI(perm)-1L) fprintf(texout,",");
        }
        fprintf(texout,")$\\ "); 
        texposition += 3;
    };

    if (texposition > 60L)
    { 
        fprintf(texout,"\n"); 
        texposition = 0L; 
    }
    return(OK);
}

INT tex_rz(obj) OP obj;
/* AK 101187 */ /* AK 100789 V1.0 */ /* AK 181289 V1.1 */
/* AK 070291 V1.2 prints to texout instead of stdout */ /* AK 150891 V1.3 */
{
    INT i;
    INT erg = OK;
    CTO(VECTOR,"tex_rz(1)",obj);

    fprintf(texout,"\\ $");
    for (i=0L;i<S_V_LI(obj);i++)
        fprintf(texout,"\\sigma_{%ld}\\ ",S_V_II(obj,i));
    fprintf(texout,"$\\ ");
    ENDR("tex_rz");
}


INT m_perm_paareperm(a,b) OP a,b;
/* 140488 */
/* diese routine berechnet die induzierte permutation in n ueber 2
oder anders gesprochen:
berechnet die operation von pi aus S_n auf der identitaet 
in S_(n ueber 2) */
/* AK 170789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
/* AK 180598 V2.0 */
{
    OP c;
    INT i,j,ni,nj,e=1L,z=1L;
    INT erg = OK;

    CPT(VECTOR,"m_perm_paareperm",a);
    CE2(a,b,m_perm_paareperm);

    c = callocobject();

    erg += binom(S_P_L(a),cons_zwei,c);
    /* c ist jetzt die laenge der ergebnis permutation */
    /* c = n ueber 2 */
    erg += b_ks_p(VECTOR,callocobject(),b);
    erg += b_l_v(c,S_P_S(b));
    /* die permutation ist nun initialisiert */


    z=0L;
    for(i=0L;i<S_P_LI(a);i++)
        for(j=i+1;j<S_P_LI(a);j++)
        {
            ni = S_P_II(a,i); nj = S_P_II(a,j);
            if (ni>nj) { e=ni; ni=nj; nj=e; };
            /* ni < nj ist ergebnis der permutation */
            /* nun nur noch den index bestimmen */
            /* der ist e */
            e = (nj-ni-1L)+((S_P_LI(a)+S_P_LI(a)-ni)*(ni-1L))/2L ;
            /* e ist der index des neuen paars speicher */
            M_I_I(e+1L,S_P_I(b,z)); 
            z++; 
        };
    ENDR("m_perm_paareperm");
}

INT eq_permutation(a,b) OP a,b;
/* AK 120104 */
{
    INT erg = OK;
    CTO(PERMUTATION,"eq_permutation(1)",a);
    CTO(PERMUTATION,"eq_permutation(2)",b);
    if (S_P_K(a) == S_P_K(b))
        {
        switch (S_P_K(a))
            {
            case ZYKEL:
            case VECTOR:
                return eq_integervector_integervector(S_P_S(a),S_P_S(b));
            default:
                return EQ(S_P_S(a),S_P_S(b));
            }
        }
    else
        {
        fprintf(stderr,"kind a = %ld\nkind b = %ld\n", S_P_K(a), S_P_K(b));
        debugprint(b);
        return error("eq_permutation:different kinds of permutations");
        }
    ENDR("eq_permutation");
}


INT comp_permutation(a,b) OP a, b;
/* AK 130587 als gr*/ /* AK 060488 als comp*/
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */
/* AK 070891 V1.3 comp_vector */
/* AK 050898 V2.0 */
{
    INT erg = OK;
    CTO(PERMUTATION,"comp_permutation(1)",a);
    CTO(PERMUTATION,"comp_permutation(2)",b);
    if (S_P_K(a) == S_P_K(b))
        return comp(S_P_S(a),S_P_S(b));
    else
        {
        fprintf(stderr,"kind a = %ld\nkind b = %ld\n", S_P_K(a), S_P_K(b));
        debugprint(b);
        return error("comp_permutation:different kinds of permutations");
        }
    ENDR("comp_permutation");
}


INT first_lehmercode(l,res) OP l, res;
/* l beleibt erhalten */
/* AK 040487 */ /* firstlemercode = 0000...0000 */
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i;
    INT erg = OK;
    CTO(INTEGER,"first_lehmercode(1)",l);
    erg += m_il_v(S_I_I(l),res);
    for (i=0L;i<S_V_LI(res);i++) M_I_I(0L,S_V_I(res,i));
    ENDR("first_lehmercode");
}

INT last_lehmercode(l,res) OP l, res;
/* 270887 */ /* lastlehmercode = 0123...n-1 */
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j;
    INT erg = OK;

    CTO(INTEGER,"last_lehmercode",l);
    j=S_I_I(l)-1;
    erg += m_il_v(S_I_I(l),res);
    for (i=0L;i<S_I_I(l);i++,j--) 
        M_I_I(j,S_V_I(res,i));
    ENDR("last_lehmercode");
}

INT first_permutation(l,res) OP l, res;
/* AK 040487 */ /* l bleibt erhalten */
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
/* ohne lehmercode AK 291091 */
/* AK 050898 V2.0 */
/* parameter may be equal */
{
    INT i,erg=OK,li;
    CTO(INTEGER,"first_permutation",l);
    li = S_I_I(l);
    erg += m_il_p(li,res);
    for(i=0L;i<li;i++) M_I_I(i+1L,S_P_I(res,i));
    C_O_K(S_P_S(res),INTEGERVECTOR);
    ENDR("first_permutation");
}


INT next_permutation_lex(start,next) OP start,next;
/* AK 160591 V1.2 */ /* AK 150891 V1.3 */
{ /* Fischer Krause */
    INT r,s,i,j,erg;
    if (check_equal_2(start,next,next_permutation_lex,&erg) == EQUAL)
                goto fe;
    copy(start,next);
    for (r=S_P_LI(next)-2L;r>=0;r--)
        if (S_P_II(next,r) < S_P_II(next,r+1L)) break;
    if (r == -1L) 
        {
        erg = LASTPERMUTATION;
        goto fe;
        }
    for (s=0L; s<S_P_LI(next)-r-1; s++)
        if (S_P_II(next,r) > S_P_II(next,r+s+1L) ) break;
    swap(S_P_I(next,r),S_P_I(next,r+s));
    for (i=r+1,j=S_P_LI(next)-1;i<j;i++,j--)
        swap(S_P_I(next,i),S_P_I(next,j));
    erg = OK;
fe:
    return erg;
}


INT next_permutation(a,b) OP a,b;
/* AK 280901 */
/* parameter may be equal */
{
    INT erg = OK;
    CTO(PERMUTATION,"next_permutation(1)",a);
    erg += copy(a,b);
    return next_apply_permutation(b);
    ENDR("next_permutation");
}


INT next_apply_permutation(a) OP a;
/* AK 280901 */
/* lex next permutation */
{
    INT i,j,k,erg = OK;
    CPT(VECTOR,"next_apply_permutation(1)",a);
    if (next_perm_v == NULL) {
        next_perm_v = CALLOCOBJECT();
        m_il_nv(S_P_LI(a)+1,next_perm_v); 
        }
    if (S_V_LI(next_perm_v) < (S_P_LI(a)+1) ) {
        i = S_V_LI(next_perm_v);
        inc_vector_co(next_perm_v,S_P_LI(a) - S_V_LI(next_perm_v) + 5);
        for (;i<S_V_LI(next_perm_v);i++) M_I_I(0,S_V_I(next_perm_v,i));
        }

    /* hilfsvector ist initialisiert */
    for (i=0,j=S_P_LI(a)-1;j>=0;j--)
        {
        M_I_I(1,S_V_I(next_perm_v,S_P_II(a,j)));
        if (S_P_II(a,j) > i)  i = S_P_II(a,j); 
        else {
            /* schauen was hinkommt */
            for (k=S_P_II(a,j)+1;k<S_V_LI(next_perm_v);k++)
                if (S_V_II(next_perm_v,k)==1) { 
                     M_I_I(k,S_P_I(a,j)); 
                     M_I_I(0,S_V_I(next_perm_v,k));
                     break;
                     }
            /* increasing filling for the remaining part */
            for (k=0,j++;j<S_P_LI(a);k++)
                if (S_V_II(next_perm_v,k) == 1) { 
                    M_I_I(0,S_V_I(next_perm_v,k));
                    M_I_I(k,S_P_I(a,j)); j++; }
            return OK;
            }
        }
    for (i=0;i<S_V_LI(next_perm_v);i++)
        M_I_I(0,S_V_I(next_perm_v,i));
    return LASTPERMUTATION;
    ENDR("next_permutation_apply");
}



INT next_lehmercode(start,n) OP start,n;
/* erzeugt den lexikographisch naechsten l.c. */
/* 040487 */ /* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j;
    copy(start,n);
    for (i=S_V_LI(n)-1L,j=0L;i>=0L;i--,j++)
    {
        if (S_V_II(n,i) < j)
            return(inc(S_V_I(n,i)));
        else C_I_I(S_V_I(n,i),0L);
    };
    freeself(n); 
    return(LASTLEHMERCODE);
}


#ifdef PARTTRUE
INT vexillaryp_permutation(perm,part) OP perm,part;
/* AK 290986 */
/* AK 031187 vergleiche hierzu kapitel 5.0 der diplomarbeit
dort wird das kriterium fuer den test auf vexillary beschrieben */
/* in part der sortierte lehmercode von perm zurueck gegeben AK 110488 */
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg;
    OP zwischen = callocobject();
    OP zwei = callocobject();
    OP a = callocobject(),b= callocobject(),c = callocobject();
    OP d;

    if (part == NULL) d = callocobject();
    else    d = part;

    invers_permutation(perm,a);
    lehmercode_permutation(a,b);
    m_v_pa(b,zwischen);freeall(b);
    lehmercode_permutation(perm,c);
    m_v_pa(c,d);freeall(c);
    conjugate(d,zwei);
    erg = eq(zwischen,zwei);
    if (d != part) freeall(d);
    freeall(zwischen);
    freeall(zwei);
    freeall(a);
    return(erg);
}
#endif /* PARTTRUE */



INT lehmercode_permutation(perm,vec) OP perm, vec;
/* AK 221087 diese procedure berechnet zur permutation perm = [p1,....,pn]
 den zugehoerigen lehmercode vec [v1,...,vn] */
/* AK 100789 V1.0 */ /* AK 111289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,k;
    INT erg = OK;
    CTO(PERMUTATION,"lehmercode_permutation(1)",perm);

    if (S_P_K(perm) == ZYKEL) /* AK 291091 */
        erg += t_ZYKEL_VECTOR(perm,perm);
    else if (S_P_K(perm) == BAR)
        {
        erg += lehmercode_bar(perm,vec);
        goto aa;
        }

    erg += m_il_v(S_P_LI(perm),vec);
    /* erzeugt ein Vectorobject */
    for(i=0L;i<S_P_LI(perm);i++)
    {
        k=0L;
        for(j=i+1L;j<S_P_LI(perm);j++)
            if (S_P_II(perm,j) < S_P_II(perm,i)) k++;
        /* k ist die anzahl der permutationselemente
                rechts von pi, die kleiner sind */
        M_I_I(k,(S_V_S(vec)+i));
        /* k wird an der richtigen stelle im
                vector notiert */
    };
aa:
    ENDR("lehmercode_permutation");
}


INT lehmercode_vector(vec,b) OP vec, b;
/* AK 221087 diese procedure berechnet aus dem lehmercode vec = [v1,....,vn]
die zugehoerige permutation b [e1,...,en] */
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,k;
    INT erg = OK; /* AK 131093 */
    OP self,liste;
    if (not VECTORP(vec))
        {
        erg = ERROR;
        goto lc_ende;
        }


    k=(INT)0;
    for (j=S_V_LI(vec)-1L,i=(INT)0; j>=(INT)0; j--,i++)
        {
        if (not INTEGERP(S_V_I(vec,j))) /* AK 131093 */
            {
            erg = ERROR;
            goto lc_ende;
            }
        if (S_V_II(vec,j) < (INT)0)
            {
            erg = ERROR;
            goto lc_ende;
            }
        if (S_V_II(vec,j) > i) /* entry to big */
            {
            if (S_V_II(vec,j)-i > k) k = S_V_II(vec,j)-i;
            }
        }

    if (k > (INT)0) /* to increase vector */
        {
        self = callocobject();
        liste = callocobject();
        erg += m_il_nv(k,self);
        erg += append(vec,self,liste);
        erg += lehmercode_vector(liste,b);
        erg += freeall(self);
        erg += freeall(liste); 
        goto lc_ende;
        }

    self = CALLOCOBJECT();
    liste = CALLOCOBJECT();

    erg += m_il_integervector(S_V_LI(vec),self);
    erg += m_il_integervector(S_V_LI(vec),liste);
    /* initialisierung zweier vektoren fuer
        eine Liste und fuer die zu berechnende Permutation */
    for(i=(INT)0;i<S_V_LI(liste);i++) M_I_I(i+1L,(S_V_I(liste,i)));
    /* liste ist jetzt ein vector [1,2,3,....,n] */
    for(i=(INT)0;i<S_V_LI(vec);i++)
    {
        k=S_V_II(vec,i);
        /* k ist ist das i-te Element aus vec, also vi */
        M_I_I(S_V_II(liste,k),S_V_I(self,i));
        /* daher ist ei = k-te Element aus der aktuellen Liste*/
        for (j=k;j<(S_V_LI(vec)-1L)-i;j++)
            /* in der liste wird das k-te Element gestrichen.
            und von rechts aufgefuellt */
            C_I_I(S_V_I(liste,j),S_V_II(liste,j+1L));
    };
    FREEALL(liste);
    erg += b_ks_p(VECTOR,self,b);
    C_O_K(S_P_S(b),INTEGERVECTOR);
lc_ende:
    ENDR("lehmercode_vector");
}

INT signum_permutation(perm,b) OP perm, b;
/* AK 240102 */
/* AK 220704 V3.0 */
{
    INT erg = OK;
    CPT(VECTOR,"signum_permutation(1)",perm);
    CTTO(INTEGER,EMPTY,"signum_permutation(2)",b);
        {
        INT i,j,res = 1;
        for (i=0;i<S_P_LI(perm);i++)
        for (j=i+1;j<S_P_LI(perm);j++)
            if ((S_P_II(perm,j) - S_P_II(perm,i )) < 0) res *= (-1);
        M_I_I(res,b);
        }
    CTO(INTEGER,"signum_permutation(2e)",b);
    ENDR("signum_permutation");
}



INT numberof_inversionen(a,b) OP a,b;
/* b becomes number of inversions in a */
/* AK 250889 V1.1 */ /* AK 150891 V1.3 */
/* AK 220704 V3.0 */
{
    INT erg = OK;
    CPTT(VECTOR,ZYKEL,"numberof_inversionen(1)",a);
    {
    OP c;
    c = CALLOCOBJECT();
    erg += lehmercode_permutation(a,c); /*result is a vector */
    erg += sum(c,b); 
    FREEALL(c);
    }
    ENDR("numberof_inversionen");
}

INT lehmercode2_permutation(perm,vec) OP perm,vec;
/* zweites verfahren */ /*AK  070488 */ /* ist langsamer */
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,j,k;
    copy_vector(S_P_S(perm),vec);
    for (i=(INT)0;i<S_V_LI(vec);)
    {
        k = S_V_II(vec,i)-1L;
        M_I_I(k,S_V_I(vec,i));
        i++;
        for (j=i;j<S_V_LI(vec);j++)
            if (S_V_II(vec,j)>k)
                M_I_I(S_V_II(vec,j)-1L,S_V_I(vec,j));
    };
    return(OK);
}


INT invers_permutation(perm,b) OP perm,b;
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,erg = OK;
    OP self;

    CTO(PERMUTATION,"invers_permutation(1)",perm);
    CTO(EMPTY,"invers_permutation(2)",b);

    if (S_P_K(perm) == BAR)
        {
        erg += invers_bar(perm,b);
        goto ee;
        }
    if (S_P_K(perm) != VECTOR) /* AK 010692 */
        return error("invers_perm: wrong perm type");

/* now the input is OK */

    self = callocobject();
    erg += m_il_integervector(S_P_LI(perm),self);
    for (    i=(INT)0;i<S_V_LI(self); i++)
        M_I_I(i+1L,S_V_I(self,S_P_II(perm,i)-1L));
    erg += b_ks_p(VECTOR,self,b);
ee:
    ENDR("invers_permutation");
}



static struct permutation * callocpermutation()
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    struct permutation *
    b = (struct permutation *)
        SYM_MALLOC((int)1 * sizeof(struct permutation));
    if (b == NULL) 
        error("callocpermutation:no mem");
    mem_counter_perm++;
    return b;
}

INT m_il_p(l,p) INT l; OP p;
/* AK 200691 V1.2 */ /* AK 060891 V1.3 */
/* AK 100902 V2.1 */
{
    INT erg =OK;
    SYMCHECK(l<0,"m_il_p:l<0");
    erg += b_ks_p(VECTOR,callocobject(),p) ;
    erg += m_il_integervector(l,S_P_S(p)) ;
    ENDR("m_il_p");
}

INT m_l_p(l,p) OP l,p;
/* AK 100902 V2.1 */
/* generates a permutation object with empty entries */
{
    INT erg =OK;
    CTO(INTEGER,"m_l_p(1)",l);
    SYMCHECK(S_I_I(l)<0,"m_il_p:l<0");
    erg += b_ks_p(VECTOR,CALLOCOBJECT(),p) ;
    erg += m_il_integervector(S_I_I(l),S_P_S(p)) ;   
    ENDR("m_l_p");
}

INT m_ks_p(kind,self,p) OBJECTKIND    kind; OP self,p;
/* AK 210690 V1.1 */ /* AK 130691 V1.2 */ /* AK 060891 V1.3 */
{
    INT erg = OK;
    COP("m_ks_p(3)",p);

    if (self == p) {
        OP sc;
        sc = CALLOCOBJECT();
        COPY(self,sc);
        erg += b_ks_p(kind,sc,p);
        }
    else {
        erg += b_ks_p(kind,callocobject(),p) ;
        COPY(self,S_P_S(p));
        }

    ENDR("m_ks_p");
}

INT b_ks_p(kind,self,p) OBJECTKIND    kind; OP self,p;
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 130691 V1.2 */ 
/* AK 060891 V1.3 */
{
    OBJECTSELF b;
    INT erg = OK;
    COP("b_ks_p(3)",p);

    b.ob_permutation = callocpermutation();
    erg += b_ks_o(PERMUTATION, b,p);
    C_P_S(p,self); 
    C_P_K(p,kind); 
    ENDR("b_ks_p");
}

INT scan_permutation_cycle(a) OP a;
/* AK 010692 */
{
    INT erg = OK;
    CTO(EMPTY,"scan_permutation_cycle(1)",a);
    erg += b_ks_p(ZYKEL,callocobject(),a);
    erg += printeingabe("input of a permutation in cycle notation");
    erg += scan(INTEGERVECTOR,S_P_S(a));
    ENDR("scan_permutation_cycle");
}

INT strong_check_permutationp(a) OP a;
/* AK 030594 */
{
    OP h;
    INT i;

    if (a == NULL)
        return FALSE;
    if (S_O_K(a) != PERMUTATION)
        return FALSE;
    if     (
       (S_P_K(a) == ZYKEL)
        ||
       (S_P_K(a) == VECTOR)
        )
        {
        if (S_P_S(a) == NULL)
            return FALSE;
        if (
        (S_O_K(S_P_S(a)) != INTEGERVECTOR) &&
         (S_O_K(S_P_S(a)) != VECTOR) )
            return FALSE;
        for (i=0;i<S_P_LI(a);i++) /* AK 181203 */
            {
            if (S_P_II(a,i)<1) return FALSE;
            if (S_P_II(a,i)>S_P_LI(a) ) return FALSE;
            }
        h = callocobject(); 
        m_il_v(S_P_LI(a),h);
        for (i=(INT)0;i<S_V_LI(h);i++)
            M_I_I(i+(INT)1, S_V_I(h,i));
        for (i=(INT)0;i<S_V_LI(h);i++)
            M_I_I((INT)0, S_V_I(h,S_P_II(a,i) -(INT)1));
            
        i = nullp(h);
        freeall(h);
        return i;
        }
    return FALSE;
}

INT scan_permutation(a) OP a;
/* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 040391 V1.2 */
/* AK 060891 V1.3 */
{
    INT erg=OK;
    CTO(EMPTY,"scan_permutation(1)",a);
spa:
    erg = OK;
    erg += b_ks_p(VECTOR,callocobject(),a);
    erg += printeingabe("input of a permutation in list notation");
    erg += scan(INTEGERVECTOR,S_P_S(a));
    if (not strong_check_permutationp(a))
        {
        fprintln(stderr,a);
        printeingabe("wrong input, please enter a permutation");
        goto spa;
        }
    ENDR("scan_permutation");
}


INT mult_apply_permutation(a,b) OP a,b;
/* AK 051198 V2.0 */
/* b = ab */
/* AK 221104 V3.0 */
{
    INT erg = OK;
    CTO(PERMUTATION,"mult_apply_permutation(1)",a);
    {
    OP c;
    c = CALLOCOBJECT();
    erg += swap(b,c);
    erg += mult_permutation(a,c,b);
    FREEALL(c);
    }
    ENDR("mult_apply_permutation");
}

INT mult_permutation(a,b,c) OP a,b,c;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK; 
    CTO(PERMUTATION,"mult_permutation(1)",a);
    CTO(PERMUTATION,"mult_permutation(2)",b);
    CTO(EMPTY,"mult_permutation(3)",c);
    {
    INT i;
    OP d = NULL; /* AK 270493 */

    if ((S_P_K(a) == BAR) && (S_P_K(b) == BAR))
        {
        erg += mult_bar_bar(a,b,c);
        goto endr_ende;
        }
    if ((S_P_K(a) != VECTOR) || (S_P_K(b) != VECTOR)) /* AK 210192 */
        return error("mult_permutation:only for VECTOR type");

    if (S_P_LI(a) < S_P_LI(b)) /* AK 270493 */
        {
        d = callocobject();
        erg += m_il_p(S_P_LI(b),d);
        for (i=(INT)0;i<S_P_LI(a);i++)
            M_I_I(S_P_II(a,i),S_P_I(d,i));
        for (;i<S_P_LI(d);i++)
            M_I_I(i+1L,S_P_I(d,i));
        a = d;
        }
    else  if (S_P_LI(a) > S_P_LI(b)) /* AK 270493 */
        {
        d = callocobject();
        erg += m_il_p(S_P_LI(a),d);
        for (i=(INT)0;i<S_P_LI(b);i++)
            M_I_I(S_P_II(b,i),S_P_I(d,i));
        for (;i<S_P_LI(d);i++)
            M_I_I(i+1L,S_P_I(d,i));
        b = d;
        }
    erg += copy_permutation(b,c);
    for (i=(INT)0;i<S_P_LI(c);i++)
        M_I_I(S_P_II(a,S_P_II(b,i)-1L),S_P_I(c,i));

    if (d != NULL)
        erg += freeall(d);
    }
    ENDR("mult_permutation");
}

INT copy_permutation(a,b) OP a,b;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 210291 V1.2 */ 
/* AK 150891 V1.3 */
{
    INT erg; /* 210291 */
    erg = b_ks_p(S_P_K(a),callocobject(),b);
    erg += m_il_integervector(S_P_LI(a),S_P_S(b));
    if (erg != OK)
        return erg;
    if (memcpy( (char *) S_V_S(S_P_S(b)), (char *) S_V_S(S_P_S(a)),
        (int) (S_P_LI(a) * sizeof(struct object)))  == NULL)  

        return ERROR;
    else 
        return OK;
}


INT length_permutation(a,b) OP a,b;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 140891 V1.3 */
{
    return copy(S_P_L(a),b); 
}
INT sprint_permutation(t,a) char *t; OP a;
/* AK 120598 V2.0 */
{
    INT erg = OK;
    COP("sprint_permutation(1)",t);
    CTO(PERMUTATION,"sprint_permutation(2)",a);

    if (S_P_K(a) == VECTOR)
        erg += sprint(t,S_P_S(a));
    else
        {
        erg += error("fprint_permutation:wrong type of permutation");
        }
    ENDR("sprint_permutation");
}

INT fprint_permutation(f,a) OP a; FILE *f;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
/* AK 280192 for other types of permutation */
{
    INT erg = OK;
    INT i,j;
    if (
        (S_P_K(a) == VECTOR) 
        || 
        (S_P_K(a) == BAR) 
        ||
        (S_P_K(a) == BITREC)
       )
    {
    erg += fprint(f,S_P_S(a));
    }
    else if (
        (S_P_K(a) == ZYKEL)
        ||
        (S_P_K(a) == BARCYCLE) 
        )
    {
    j = S_P_II(a,(INT)0);
    fprintf(f,"("); 
    if (f == stdout) 
        zeilenposition++;
    for (i=(INT)0;i<s_p_li(a);i++)
        {
        if (S_P_II(a,i) < j) /* new cycle */
            {
            fprintf(f,")("); 
            if (f == stdout) 
                zeilenposition+=2L;
            j = S_P_II(a,i);
            }
        else    if (i != (INT)0) 
            {
            fprintf(f,","); 
            if (f == stdout) 
                zeilenposition++;
            }
        erg += fprint(f,S_P_I(a,i));
        }
    fprintf(f,")"); 
    if (f == stdout) 
        zeilenposition++;
    }
    else
    {
    erg += error("fprint_permutation:wrong type of permutation");
    }
    return erg;
}



INT dec_permutation(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK;
    CTO(PERMUTATION,"dec_permutation(1)",a);
    erg += dec_integervector(S_P_S(a));
    ENDR("dec_permutation");
}




INT inc_permutation(perm) OP perm;
/* AK 171187
nur fuer listendarstellung realisiert die Einbettung S_n ---> S_{n+1} */
/* am anfang eine 1 dazu */ 
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 140891 V1.3 */
{
    INT i;
    INT erg = OK;
    CTO(PERMUTATION,"inc_permutation(1)",perm);
    if (S_P_K(perm) != VECTOR) 
        return  error("inc_permutation:wrong kind");
    erg += inc(S_P_S(perm));
    for(i=S_P_LI(perm)-1L;i>(INT)0;i--)
        M_I_I(S_P_II(perm,i-1L)+1L,S_P_I(perm,i));
    M_I_I(1L,S_P_I(perm,(INT)0));
    ENDR("inc_permutation");
}



INT last_permutation(l,ree) OP l, ree;
/* AK 101187 */ /* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 140891 V1.3 */
{
    OP zwerg;
    INT erg=OK;
    CTO(INTEGER,"last_permutation(1)",l);
    zwerg = callocobject();
    erg += last_lehmercode(l,zwerg);
    erg += lehmercode(zwerg,ree);
    FREEALL(zwerg);
    ENDR("last_permutation");
}


INT rz_perm(perm,c) OP perm,c;
/* AK 050198 V2.0 */
/* computes a reduced decomposition of a permutation */
/* AK 270887 */ /* AK 070789 V1.0 */ 
/* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg=OK; /* 260292 */
    OP lc;
    CTO(PERMUTATION,"rz_perm(1)",perm);
    lc = callocobject();

    erg += lehmercode_permutation(perm,lc);
    erg += rz_lehmercode(lc,c);
    erg += freeall(lc);
    ENDR("rz_perm");
}

INT rz_lehmercode(lc,b) OP lc,b;
/* AK 241087
bildet die reduzierte zerlegung des lehmercodes lc
bsp lc = 321200  dann ist ergebnis 32132354
vgl verfahren 1 in diplomarbeit */
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT     i = S_V_LI(lc),    /* laufvariable durch l.c. */
    k ,        /* laufvariable durch ergebnis */
    j,erg = OK;
    OP    zw;

    CTO(VECTOR,"rz_lehmercode(1)",lc);
    COP("rz_lehmercode(2)",b);

    zw = callocobject();
    erg += sum(lc,zw); 
    if (NULLP(zw)) 
        {
        erg += m_il_integervector((INT)0,b);
        erg += freeall(zw);
        goto ende;
        }
    k = S_I_I(zw);
    erg += b_l_v(zw,b);
    /* die laenge der reduzierten zerlegung ist die summe des lehmercodes */
    while (i-- > (INT)0)
        if (S_V_II(lc,i) > (INT)0)
            for (j=(INT)0;j<S_V_II(lc,i);j++)
            {
                --k;
                if    (k < (INT)0) /* AK 271087 */
                    return(error("rzoflc:k < 0"));

                M_I_I(i+1+j,S_V_I(b,k));
            };
ende:
    ENDR("rz_lehmercode");
}

INT random_permutation(ln,b) OP ln, b;
/* AK 150587 */ /* nijnhuis kap 8 */ /* AK 070789 V1.0 */
/* an dieser stelle wird float verwandt */
/* AK 181289 V1.1 */
/* rand() gibt auf verschiedenen rechnern zufallszahlen in unter
schiedlichen bereichen */ /* AK 150891 V1.3 */
/* AK 150296 FMD */
/* AK 110804 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"random_permutation(1)",ln);
    SYMCHECK(S_I_I(ln)<1,"random_permutation(1)<1");
    {
    INT i,l,merk;
    INT integerlength;
    float zw;
    int rand();

    integerlength = S_I_I(ln);
    erg += first_permutation(ln,b);
    for (i=(INT)0;i<integerlength;i++)
    {
        zw  = (float) (rand() % 32767) /32767.0;
        l = i + (int)(zw * (integerlength-i));
        merk = S_P_II(b,l);
        M_I_I(S_P_II(b,i),S_P_I(b,l));
        M_I_I(merk,S_P_I(b,i));
    }
    }
    ENDR("random_permutation");
}
#endif /* PERMTRUE */


OP s_p_s(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_permutation->p_self); 
}

OBJECTKIND s_p_k(a) OP a; 
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a);
    return(c.ob_permutation->p_kind); 
}

OP s_p_i(a,i) OP a; INT i; 
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    return(s_v_i(s_p_s(a),i)); 
}

INT s_p_ii(a,i) OP a; INT i; 
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 070891 V1.3 */
{ 
    if (a == NULL) 
        return error("s_p_ii: a == NULL");
    if (not permutationp(a)) 
        return error("s_p_ii: a not permutation");
    if (i >= s_p_li(a)) 
        return error("s_p_ii: i to big");
    return(s_v_ii(s_p_s(a),i)); 
}

OP s_p_l(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 070891 V1.3 */
{ 
    return(s_v_l(s_p_s(a))); 
}

INT s_p_li(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    if (a == NULL) 
        return error("s_p_li: a == NULL");
    if (not permutationp(a)) 
        return error("s_p_li: a not permutation");
    return(s_v_li(s_p_s(a))); 
}

INT c_p_k(a,b) OP a; OBJECTKIND b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    OBJECTSELF c; 
    if (a == NULL) /* AK 040292 */
        return error("c_p_k:NULL object");
    if (s_o_k(a) != PERMUTATION) /* AK 040292 */
        return error("c_p_k:no PERMUTATION");
    if ( /* AK 040292 */
        (b != VECTOR)&&
        (b != ZYKEL) )
        return error("c_p_k:wrong kind");

    c = s_o_s(a); 
    c.ob_permutation->p_kind = b; 
    return(OK); 
}

INT c_p_s(a,b) OP a,b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_permutation->p_self = b; 
    return(OK); 
}

#ifdef PERMTRUE
INT elementarp_permutation(a,b) OP a,b;
/* AK 210889 */ /* AK 230889 */
/* true falls sich die beiden perm durch eine elementartransposition 
multipliziert von rechts unterscheiden */
/* AK 250889 V1.1 */ /* AK 150891 V1.3 */
{
    INT i;
    for (i=(INT)0;i<S_P_LI(a);i++)
    {
        if (S_P_II(b,i) != S_P_II(a,i)) break;
    }
    if (i == S_P_LI(a)) return(FALSE); /* zwei gleiche permutationen */
    if (i == S_P_LI(a)-1L)  {
        fprintln(stderr,a);
        fprintln(stderr,b);
        return error("elementarp: error in permutation");
    }
    if (S_P_II(a,i) != S_P_II(b,i+1L)) return(FALSE);
    if (S_P_II(b,i) != S_P_II(a,i+1L)) return(FALSE); /* keine elementar 
                                transposition */
    for(i += 2; i<S_P_LI(a);i++)
        if (S_P_II(b,i) != S_P_II(a,i)) return(FALSE);
    return(TRUE);

}


INT objectread_permutation(filename,perm) OP perm; FILE *filename;
/* AK 291086 */ /* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i;
    OBJECTKIND kind;
    INT erg = OK;
    COP("objectread_permutation(1)",filename);
    CTO(EMPTY,"objectwrite_permutation(2)",perm);

    erg += b_ks_p((OBJECTKIND)0, callocobject(),perm);
    fscanf(filename,"%ld",&i); kind = (OBJECTKIND)i;
    C_P_K(perm,kind);
    erg += objectread(filename,S_P_S(perm));
    ENDR("objectread_permutation");
}



INT objectwrite_permutation(filename,perm) FILE *filename; OP perm;
/* AK 291086 */ /* AK 100789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK;
    COP("objectwrite_permutation(1)",filename);
    CTO(PERMUTATION,"objectwrite_permutation(2)",perm);

    fprintf(filename,"%ld\n",(INT)PERMUTATION);
    fprintf(filename,"%ld\n",(INT)S_P_K(perm));
    erg += objectwrite(filename,S_P_S(perm));
    ENDR("objectwrite_permutation");
}

INT zykeltyp(a,b) OP a,b;
/* AK 170789 V1.0 *//* AK 181289 V1.1 *//* AK 180691 V1.2 *//* AK 150891 V1.3 *//* AK 050898 V2.0 */
{
    INT erg = OK;
    
    CE2(a,b,zykeltyp);
    CPT(VECTOR,"zykeltyp",a);
    erg += zykeltyp_permutation(a,b);
    ENDR("zykeltyp");
}



#ifdef PARTTRUE
	INT zykeltyp_permutation_pre190202(a,b) OP a,b;
/* AK 120488 */ /* AK 170789 V1.0 */ /* AK 181289 V1.1 */ /* AK 180691 V1.2 */ 
/* AK 150891 V1.3 */
{
    INT i,zykellength,alt,n;
    INT erg = OK; /* AK 221191 */
    OP self;
    CPT(VECTOR,"zykeltyp_permutation(1)",a);

    self=callocobject();

    erg += copy_integervector(S_P_S(a),self);
    for (i=(INT)0;i<S_V_LI(self);i++)
        if (S_V_II(self,i) != (INT)0) /* noch nicht im zykel */
        { 
            zykellength=1L;
            alt=i;
            while (S_V_II(self,alt) != (i+1L))
            { 
                n = S_V_II(self,alt)-1L;
                M_I_I((INT)0,S_V_I(self,alt));
                alt = n; 
                zykellength++; 
            };
            M_I_I((INT)0,S_V_I(self,alt));
            M_I_I(zykellength,S_V_I(self,i));
        };
    erg += m_v_pa(self,b);
    erg += freeall(self);
    ENDR("zykeltyp_permutation");
}

INT zykeltyp_permutation(a,b) OP a,b;
/* AK 190202 */
{
    INT i,zykellength,alt,n,l=0;
    INT erg = OK; 
    OP self;
    CPT(VECTOR,"zykeltyp_permutation(1)",a);
    CTO(EMPTY,"zykeltyp_permutation(2)",b);

    if (zykeltyp_perm_v == NULL) 
        {
        zykeltyp_perm_v = CALLOCOBJECT();
        erg += m_il_nv(2,zykeltyp_perm_v);
        }
    
 
    self=zykeltyp_perm_v;
 
    
    for (i=(INT)0;i<S_P_LI(a);i++)
        if (S_P_II(a,i) > 0) /* noch nicht im zykel */
        {
            zykellength=1L;
            alt=i;
            while (S_P_II(a,alt) != (i+1))
            {
                n = S_P_II(a,alt)-1;
                ADDINVERS_APPLY_INTEGER(S_P_I(a,alt));
                alt = n;
                zykellength++;
            };
            ADDINVERS_APPLY_INTEGER(S_P_I(a,alt));
            M_I_I(zykellength,S_V_I(self,l));
            l++;
            if (l >= S_V_LI(self)) inc_vector_co(self,10);
        };

    for (i=(INT)0;i<S_P_LI(a);i++) ADDINVERS_APPLY_INTEGER(S_P_I(a,i));
    n = S_V_LI(self);
    C_I_I(S_V_L(self),l);
    erg += m_v_pa(self,b);
    C_I_I(S_V_L(self),n);
    
    ENDR("zykeltyp_permutation");
}




INT m_part_perm(a,b) OP a,b;
/* erzeugt aus zykeltyp permutation */
/* AK 120488 */ /* AK 170789 V1.0 */ /* AK 181289 V1.1 */ /* AK 130691 V1.2 */
/* AK 070891 V1.3 */ /* AK 050898 V2.0 */
/* AK 021106 V3.1 */
{
    INT i,j,k; /* die adresse in der perm. b */
    INT erg = OK; /* AK 221191 */
    OP l;

    CE2(a,b,m_part_perm);
    CTO(PARTITION,"m_part_perm(1)",a);

    l=callocobject();

    if (S_PA_K(a) == EXPONENT) {
        /* AK 151189 */
        erg += t_EXPONENT_VECTOR(a,l);
        erg += m_part_perm(l,b);
        erg += freeall(l);
        goto endr_ende;
    }
    else if (S_PA_K(a) == VECTOR)
    {
        erg += weight(a,l);
        erg += b_ks_p(VECTOR,callocobject(),b);
        erg += b_l_v(l,S_P_S(b));
        k=0;
        for (i=0;i<S_PA_LI(a);i++)
        {
            /* k ist naechste frei stelle */
            M_I_I(k+1L,S_P_I(b,k+S_PA_II(a,i)-1L));
            for (j=1L;j<S_PA_II(a,i);j++)
            M_I_I(j+k+1L,S_P_I(b,k+j-1L));
            k=k+S_PA_II(a,i);
        }
    }
    else
    {
        erg += error("m_part_perm(1): wrong type of partition");
    }
    ENDR("m_part_perm");
}
#endif /* PARTTRUE */



INT zykeltyp_hoch_n(a,b,c) OP a,b,c;
/* AK 160988 */
/* a ist zykeltyp b ist integer c wird der zykeltyp nach b-maligen
anwenden einer permutation vom typ a */
/* AK 170789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150891 V1.3 */
{
    INT i,k;
    if (S_O_K(a) != PARTITION)
        return(error("zykeltyp_hoch_n:S_O_K(a) != PARTITION"));
    if (S_O_K(b) != INTEGER)
        return(error("zykeltyp_hoch_n:S_O_K(b) != INTEGER"));
    if (S_PA_K(a) == VECTOR)
        {
        OP d = callocobject();
        i = OK;
        i += t_VECTOR_EXPONENT(a,d);
        i += zykeltyp_hoch_n(d,b,c);
        i += freeall(d);
        return(i);
        }
    copy(a,c);
    /* nun nachschauen ob ggt von b und den einzelnen 
    zykellaengen > 1, dann zerfaellt dieser zykel naemlich */

    for (i=(INT)0; i<S_PA_LI(a); i++)
        if (S_PA_II(a,i) > (INT)0) {
            k = ggt_i(S_I_I(b),i+1L);
            if (k>1L) { 
                M_I_I(    (
                    (S_PA_II(c,((i+1L)/k -1L)))
                    +
                    (k * S_PA_II(c,i) )
                    ),
                    S_PA_I(c,  (i+1L)/k -1L)
                    );
                M_I_I((INT)0,S_PA_I(c,i));
            };
        };
    return(OK);
}
#endif /* PERMTRUE */

INT t_VECTOR_ZYKEL(a,b) OP a,b; /* AK 291091 */
    {
    return t_vperm_zperm(a,b);
    }

INT t_vperm_zperm(a,b) OP a,b;
    /* aus einer vector-permutation
    eine zykel-permutation */
    /* folgende darstellung des zykel
    zuerst der zykel mit groessten kleinsten element
    usw als letztes der zykel mit der 1
    */
    /* bsp (1256)(387)(49) als
    [4,9,3,8,7,1,2,5,6] */
/* AK 050390 V1.1 */ /* AK 080891 V1.3 */
    {
    INT i,erg =OK;
    INT schreibindex;
    INT leseindex,altleseindex;
    INT startindex=(INT)0,startwert;
    INT ergindex = S_P_LI(a)-1;
        /* der freie index am rechten ende */
    OP c;
    CE2(a,b,t_vperm_zperm);

    c= callocobject(); 
    erg += copy(a,c);
    erg += copy(a,b);
    C_P_K(b,ZYKEL);
m_vperm_zperm_again:    
    for (i=startindex;i<S_P_LI(c);i++)
        if (S_P_II(c,i) != (INT)0) break;
    if (i == S_P_LI(a)) 
            {
            erg += freeall(c);
            goto endr_ende;
                /* der algorithmus ist fertig wenn
                der hilfsvector c=000...0000 */
            }

    /* ist der erste index mit eintrag != 0 in c 
    d.h. noch in keinem zykel */

    schreibindex=(INT)0;
    startwert = i+1;    /* der wert mit dem der zykel startet */
    leseindex = i;
m_vperm_zperm_next:
        M_I_I(leseindex+1L,S_P_I(b,schreibindex));
        schreibindex++;
        /* zykelelement wurde geschreiben */
    altleseindex=leseindex;
    leseindex = S_P_II(a,leseindex)-1;
    M_I_I((INT)0,S_P_I(c,altleseindex));
    if (leseindex+1 == startwert) { 
        /* der zykel ist zu ende */
        /* der zykel muss nach rechts geschoben werden */
        do 
            {
            schreibindex--;
            M_I_I(S_P_II(b,schreibindex),S_P_I(b,ergindex));
            ergindex--;
            }
        while (schreibindex > (INT)0);
        goto m_vperm_zperm_again;    
        };
    goto m_vperm_zperm_next;
    ENDR("t_vperm_zperm");
    }

INT t_ZYKEL_VECTOR(a,b) OP a,b; /* AK 291091 */
    {
    return t_zperm_vperm(a,b);
    }

INT t_zperm_vperm(a,b) OP a,b;
/* AK 050390 V1.1 */ /* AK 080891 V1.3 */
    {
    INT index = (INT)0;
    INT startwert, schreibindex;
    INT erg = OK; /* AK 291091 */
    CE2(a,b,t_zperm_vperm);
    copy(a,b);
    C_P_K(b,VECTOR);
m_zperm_vperm_again:
    startwert = S_P_II(a,index); /* zykelanfang */
    index++;
    schreibindex = startwert-1;
    
    if (index < S_P_LI(a)) /* AK 210597 */
    while  (S_P_II(a,index) > startwert)
        {
        M_I_I(S_P_II(a,index), S_P_I(b,schreibindex));
        schreibindex = S_P_II(a,index) - 1;
        index++;
        if (index == S_P_LI(a)) break;
        };

    /* wir sind am zykelende */
    /* index ist anfang naechster zykel */
    M_I_I(startwert, S_P_I(b,schreibindex));
    if (index != S_P_LI(a)) goto m_zperm_vperm_again;
    /* ende der permutation */
    ENDR("t_zperm_vperm");
    }

#ifdef MATRIXTRUE
#ifdef PERMTRUE
INT permutation_matrix(a,b) OP a,b;
{
    return perm_matrix(a,b);
}


INT perm_matrix(a,b) OP a,b;
/* AK 181289 permutationsmatrix (0,1) zu einer permutation */
/* AK 181289 V1.1 */ 
/* AK 150891 V1.3 */
/* FM 210296 */
/* AK 220498 V2.0 */
/* AK 261103 for barred permutations */
/* input: PERMUTATION
   output: 01 matrix b_ij = 1 if a(j) = i */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CPTT(BAR,VECTOR,"perm_matrix(1)",a);
    CE2(a,b,perm_matrix);
        {
        INT i,j;
        erg += m_ilih_m(S_P_LI(a),S_P_LI(a),b);
        for (i=0; i<S_P_LI(a); i++)
            for (j=0; j<S_P_LI(a); j++)
                if (S_P_II(a,j) == i+1L) M_I_I(1,S_M_IJ(b,i,j));
                else if (S_P_II(a,j) == -(i+1)) M_I_I(-1,S_M_IJ(b,i,j));
                else M_I_I(0,S_M_IJ(b,i,j));
        }
    ENDR("perm_matrix");
}

INT perm_matrix_p(a) OP a;
/* true if a is a permutation matrix */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"perm_matrix_p(1)",a);
    {
    INT i,j,e;
    if (S_M_HI(a) != S_M_LI(a)) return FALSE;
    for (i=0;i<S_M_HI(a);i++)
        {
        e=0;
        for (j=0;j<S_M_LI(a);j++)
            {
            if (NULLP(S_M_IJ(a,i,j))) continue;
            else if ((e==0) && EINSP(S_M_IJ(a,i,j))) e++;
            else return FALSE;
            }
        if (e==0) return FALSE;
        }
    /* now we know each row has one 1 */
    /* now check the columns */
    for (j=0;j<S_M_LI(a);j++)
        {
        e=0;
        for (i=0;i<S_M_HI(a);i++)
            {
            if (NULLP(S_M_IJ(a,i,j))) continue;
            else if ((e==0) && EINSP(S_M_IJ(a,i,j))) e++;
            else return FALSE;
            }
        if (e==0) return FALSE;
        }
    return TRUE;
    }
    ENDR("perm_matrix_p");
}

#endif /* PERMTRUE */
#endif /* MATRIXTRUE */

#ifdef PERMTRUE
INT einsp_permutation(a) OP a;
/* test auf identitaet */ /* AK 221289 V1.1 */ /* AK 150891 V1.3 */
{
    INT erg = OK;
    CTO(PERMUTATION,"einsp_permutation(1)",a);
    {
    INT i,j;
    if (S_P_K(a) == VECTOR) {
        for (i=S_P_LI(a) -1;i>=0;i--)
            if (S_P_II(a,i) != (i+1L)) return(FALSE);
        return(TRUE);
        }
    else if (S_P_K(a) == ZYKEL) {
        for (j=1,i=S_P_LI(a) -1;i>=0;i--,j++)
            if (S_P_II(a,i) != j ) return(FALSE);
        return(TRUE);
        } 
    else if (S_P_K(a) == BAR) {
        for (j=S_P_LI(a),i=S_P_LI(a) -1;i>=0;i--,j--)
            if (S_P_II(a,i) != j ) return(FALSE);
        return(TRUE);
        } 
    else {
        WTO("einsp_permutation(1.typ)",a);
        }
    }
    ENDR("einsp_permutation");
}



INT comp_lex_perm(a,b) OP a,b;
/* AK 070390 V1.1 */ /* AK 150891 V1.3 */
/* AK 020902 V2.0 */
    {
    return COMP(S_P_S(a),S_P_S(b));
    }



#ifdef POLYTRUE

INT operate_gral_polynom(a,b,c) OP a,b,c;
/* a is GRAL, b is POLYNOM, c becomes POLYNOM */
/* AK 200891 V1.3 */
{
    OP z,d;
    INT erg = OK;
    CTO(GRAL,"operate_gral_polynom(1)",a);
    CTO(POLYNOM,"operate_gral_polynom(2)",b);
    if (S_L_S(b) == NULL) /* AK 141092 */
        return copy(b,c);
    erg += init(POLYNOM,c);
    z = a;
    d = callocobject();
    while (z != NULL)
        {
        erg += operate_perm_polynom(S_PO_S(z),b,d);
        erg += mult_apply(S_PO_K(z),d);
        erg += add_apply(d,c);
        z = S_PO_N(z);
        }
    erg += freeall(d);
    ENDR("operate_gral_polynom");
}


INT operate_perm_polynom(a,b,c) OP a,b,c;
/* a is PERMUTATION, b is POLYNOM, c becomes POLYNOM */
/* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(PERMUTATION,"operate_perm_polynom(1)",a);
    SYMCHECK((S_P_K(a) != VECTOR)&&(S_P_K(a) != BAR),
             "operate_perm_polynom(1) only for VECTOR or BAR permutations");
    CTO(POLYNOM,"operate_perm_polynom(2)",b);
    CE3(a,b,c,operate_perm_polynom);
    {
    OP z,d,aa;
    INT j = 1;
    if (S_L_S(b) == NULL)  /* AK 141092 */
        {
        erg += copy(b,c);
        goto endr_ende;
        }
    erg += init(POLYNOM,c);

    if (S_P_K(a) == VECTOR) aa = a;
    else {  /* Barred permutation */
        INT i;
        aa = CALLOCOBJECT();
        COPY (a,aa);C_P_K(aa,VECTOR);
        for (i=0;i<S_P_LI(aa);i++)
            if (S_P_II(aa,i) < 0) { j*=-1; M_I_I(-S_P_II(aa,i),S_P_I(aa,i)); }
        }
      

    FORALL(z,b,
        {
        d = callocobject();
        erg += b_sk_mo(callocobject(),callocobject(),d);
        if (j == -1) ADDINVERS(S_MO_K(z),S_MO_K(d));
        else COPY(S_MO_K(z),S_MO_K(d));

        while (S_P_LI(a) > S_MO_SLI(z)) /* AK 230192 */
            {
            INC(S_MO_S(z));
            ;M_I_I(0,S_MO_SI(z,S_MO_SLI(z)-1L));
            }
        erg += operate_perm_vector(aa,S_MO_S(z),S_MO_S(d));
        insert(d,c,add_koeff,NULL);
        });
    if (a != aa) FREEALL(aa);
    }
    CTO(POLYNOM,"operate_perm_polynom(3-e)",c);
    ENDR("operate_perm_polynom");
}

#endif /* POLYTRUE */



INT operate_perm_zeilenmatrix(perm,b,c) OP perm,b,c;
{
    OP v;
    INT i,j;
    INT erg = OK;
    CTO(PERMUTATION,"operate_perm_zeilenmatrix(1)",perm);
    CTO(MATRIX,"operate_perm_zeilenmatrix(2)",b);

    v = callocobject();    
    erg += m_l_v(S_M_H(b), v);
    for (i=0;i<S_V_LI(v);i++)
        erg += select_row(b,i,S_V_I(v,i));
    println(v);
    erg += operate_perm_vector(perm,v,v);
    erg += m_lh_m(S_M_L(b), S_M_H(b), c);
    println(v);
    for (i=0;i<S_V_LI(v);i++)
        for (j=0;j<S_M_LI(b);j++)
            erg += copy(S_V_I(S_V_I(v,i),j) , S_M_IJ(c,i,j) );
    ENDR("operate_perm_zeilenmatrix");
}

INT operate_perm_vector(perm,b,c) OP perm,b,c;
/* AK Fri Jan 27 14:08:25 MEZ 1989 */
/* operates by permuting entries in the vector */
/* AK 030789 V1.0 */ /* AK 020290 V1.1 */ /* AK 150891 V1.3 */
/* AK 120804 V3.0 */
    {
    INT erg = OK; 
    CTO(PERMUTATION,"operate_perm_vector",perm);
    SYMCHECK(not VECTORP(b),"operate_perm_vector(2): not a vector object");
    SYMCHECK(S_P_LI(perm) > S_V_LI(b),"operate_perm_vector:perm too big");
    CE3( perm,b,c, operate_perm_vector);
    {
    INT i;
    if (S_P_LI(perm) < S_V_LI(b)) /* AK 230192 */
        {
        OP d = callocobject();
        erg += m_il_p(S_V_LI(b),d);
        for (i=0;i<S_P_LI(perm);i++)
            erg += m_i_i(S_P_II(perm,i),S_P_I(d,i));
        for(;i<S_P_LI(d);i++)
            erg += m_i_i(i+1L,S_P_I(d,i));
        erg += operate_perm_vector(d,b,c);
        FREEALL(d);
        }
    else{
        erg += m_il_v(S_V_LI(b),c); 
        C_O_K(c,S_O_K(b));
        for (i=0;i<S_V_LI(c);i++)
            COPY (S_V_I(b,i),S_V_I(c,S_P_II(perm,i) -1) );
        }
    }
    ENDR("operate_perm_vector");
    }

#define FREE_PERMUTATION(a) SYM_free((char *) a)

INT freeself_permutation(a) OP a;
/* AK 110488 */ /* AK 070789 V1.0 */ /* AK 260690 V1.1 */
/* AK 120391 V1.2 */ /* AK 150891 V1.3 */
/* AK 271098 V2.0 */
{
    /* it works for INTEGER-Vectors */
    OBJECTSELF d;
    INT erg = OK;
    CTO(PERMUTATION,"freeself_permutation(1)",a);

    FREEALL(S_P_S(a));
    d = S_O_S(a); 
    FREE_PERMUTATION(d.ob_permutation); 
    mem_counter_perm--;
    C_O_K(a,EMPTY);
    ENDR("freeself_permutation");
}


INT UD_permutation(a,b) OP a,b;
/* computes Up-Down-sequence of a permutation */
/* AK 010890 V1.1 */ /* AK 150891 V1.3 */
/* AK 280598 V2.0 */
{
    INT i,erg=OK;

    CPT(VECTOR,"UD_permutation",a);
    CE2(a,b,UD_permutation);
    erg += m_il_v(S_P_LI(a)-1L,b);
    for (i=0;i+1L < S_P_LI(a);i++)
        if (S_P_II(a,i) < S_P_II(a,i+1)) 
            M_I_I(1L,S_V_I(b,i));
        else  
            M_I_I((INT)0,S_V_I(b,i));
    ENDR("UD_permutation");
}

INT comp_permutation_pol(as,bs) OP as,bs;
/* comparision of permutations of may be different degrees:
   eq if identity on remaining part */
/* AK 200891 V1.3 */
{
    INT erg,i;
    OP c;
    erg=1L;
    if (S_P_LI(bs) > S_P_LI(as)) {c=bs;bs=as;as=c;erg= -1L;}
    /* as ist laenger als bs */
    for (i=(INT)0; i<S_P_LI(as); i++)
        {
        if (i < S_P_LI(bs))
            {
            if (S_P_II(as,i) > S_P_II(bs,i)) return erg*1L;
            if (S_P_II(as,i) < S_P_II(bs,i)) return erg*-1L;
            }
        else {
            if (S_P_II(as,i) < i+1) return erg*-1L;
            if (S_P_II(as,i) > i+1) return erg*1L;
            }
        }
    return (INT)0;
}

INT gengroup(vec) OP vec;
/* NiS 220191 V1.3 */
/* input: VECTOR of group elements
   output: VECTOR of all elements in the generated group */
{
    INT found=0,i,j,k,newfound=1,veclen;
    INT erg = OK;
    OP a,c,h,z,z1;
    CTO(VECTOR,"gengroup(1)",vec);

    CALLOCOBJECT3(a,c,h);init(HASHTABLE,h);
    for (i=0;i<S_V_LI(vec);i++) { OP d=CALLOCOBJECT();
                                  COPY(S_V_I(vec,i),d);
                                  insert(d,h,NULL,NULL); }
    veclen=S_V_LI(vec);

    while(newfound != 0)
    {
#ifdef UNDEF
        for(i=0; i < veclen; i++)
            for(j=0; j < veclen; j++)
            {
                OP z;
                FREESELF(c);
                MULT(S_V_I(vec,i),S_V_I(vec,j),c);
                newfound=1;
                z = find_vector(c,vec);
                if(z == NULL)
                { INC(vec); COPY(c,S_V_I(vec,veclen++)); }
                else newfound=0;
            }
#endif
cc:
         for(i=0; i < veclen; i++)
         {
         FORALL(z,h, {
                FREESELF(c);
                MULT(S_V_I(vec,i),z,c);newfound=1;
                z1 = find_hashtable(c,h,NULL,NULL);
                if(z1 == NULL) { insert(c,h,NULL,NULL);c=CALLOCOBJECT();goto cc;}
                else newfound=0;
                     } );
         }
    } 
    t_HASHTABLE_VECTOR(h,vec);
    FREEALL3(a,c,h);
    ENDR("gengroup");
}
#endif /* PERMTRUE */

/*******************************************************************
 *  if(pfact(permutation)) continue;                             *
 *******************************************************************/
INT pfact(a) OP a;
/* AL 250791 V1.3 */
{
    INT x, i;
        x=(INT)0;
        for(i=(INT)0;i<S_P_LI(a)-1L;i++)
            {
        if(x < S_P_II(a,i)) x=S_P_II(a,i); 
        if((i+1L)==x) { return(TRUE); break;}
            }
        return(FALSE);
}


INT makevectoroftranspositions(a,b) OP a,b;
/* b becomes VECTOR of all transpositions */
/* AK 250791 V1.3 */
{
    INT i,j,k,erg=OK;
    CTO(INTEGER,"makevectoroftranspositions(1)",a);

    erg += m_il_v((S_I_I(a) * (S_I_I(a)-1L))/2L, b);
    for (i=(INT)0;i<S_V_LI(b);i++)
        {
        erg += first_permutation(a,S_V_I(b,i));
        }
    k=(INT)0; /* index in vector b */
    for (i=(INT)0;i<S_I_I(a);i++)
        for (j=i+1L;j<S_I_I(a);j++)
            {
            M_I_I(j+1,S_P_I(S_V_I(b,k),i));
            M_I_I(i+1,S_P_I(S_V_I(b,k),j));
            k++;
            }
    ENDR("makevectoroftranspositions");
}

INT first_perm_n_invers(a,b,c) OP a,b,c;
/* AK 250892 */
/* a,b,c may be equal */
{
    OP d;
    INT i,bi=S_I_I(b);
    INT erg = OK;
    CTO(INTEGER,"first_perm_n_invers",a);
    CTO(INTEGER,"first_perm_n_invers",b);
    d = callocobject();
    erg += m_l_nv(a,d);
    for(i=(INT)0;i<S_V_LI(d);i++)
        if (S_V_LI(d)-1L-i < bi)
            {
            erg += m_i_i(S_V_LI(d)-1L-i, S_V_I(d,i) );
            bi = bi - (S_V_LI(d)-1L-i); /*  BUG ( were missing */
            }
        else    {
            erg += m_i_i(bi,S_V_I(d,i));
            bi = (INT)0;
            break;
            }
    if (bi > (INT)0)    
        {
        erg += freeall(d);
        erg += error("first_perm_n_invers: number of invers too big");
        goto endr_ende;
        }
        
    erg += lehmercode_vector(d,c);
    erg += freeall(d);
    ENDR("first_perm_n_invers");
}

INT next_perm_invers(a,b) OP a,b;
/* next perm with a given number of inversions */
/* a and b may be equal */
{
    INT erg = OK;
    CPT(VECTOR,"next_perm_invers(1)",a);
    {
    OP c = callocobject();
    INT i,j,s,k;
    erg += lehmercode(a,c);
    s =(INT)0;
    for (j=(INT)0,i= S_V_LI(c)-1L; i>= (INT)0; i--,j++)
        {
        s += S_V_II(c,i);
        if ((S_V_II(c,i) < j))  break;
        }
    if (i < (INT)0) {
        freeall(c);
        return LAST_PERMUTATION;
        }
    for (j=i-1L;j>=(INT)0;j--) 
        if (S_V_II(c,j) > (INT)0) break;
    if (j < (INT)0) {
        freeall(c);
        return LAST_PERMUTATION;
        }

    /* an j wird um eins erniedrigt */
    /* rest wird aufgefuellt */
    m_i_i(S_V_II(c,j) -1L, S_V_I(c,j));
    s++;

    for (i=j+1L,k=S_V_LI(c)-1L-i; i<S_V_LI(c); i++,k--)
        if (s >= k) {
            m_i_i(k,S_V_I(c,i)); s -= k; 
            }
        else {
            m_i_i(s,S_V_I(c,i)); s = (INT)0;
            }

    erg += lehmercode_vector(c,b);
    FREEALL(c);
    return erg;
    }
    ENDR("next_perm_invers");
}

#ifdef PERMTRUE
INT make_nzykel(n,r) OP n,r;
/* AK 051198 V2.0 */
/* n and r may be equal */
{
    INT i,erg=OK;
    CTO(INTEGER,"make_nzykel",n);
    erg += m_il_p(S_I_I(n),r);
    for (i=(INT)0;i<S_P_LI(r);i++)
        M_I_I(i+2L,S_P_I(r,i));
    M_I_I(1L,S_P_I(r,i-1));
    ENDR("make_nzykel");
}



INT make_n_id(n,r) OP n,r;
{
    INT i,erg=OK;
    erg += m_il_p(S_I_I(n),r);
    for (i=(INT)0;i<S_P_LI(r);i++)
        erg += m_i_i(i+1L,S_P_I(r,i));
    return erg;
}



INT m_INTEGER_elmtrans(i,r) OP i,r;
{
    return m_INT_elmtrans(S_I_I(i),r);
}

INT m_INT_elmtrans(i,r) INT i; OP r;
/* builds the elementary transposition (i,i+1) in S_{i+1} */
{
    OP c,d;
    INT erg = OK;
    c = callocobject();
    d = callocobject();
    erg += m_i_i(i,d);
    erg += m_i_i(i+1L,c);
    erg += make_n_kelmtrans(c,d,r);
    erg += freeall(c);
    erg += freeall(d);
    return erg;
}

INT make_n_kelmtrans(n,k,r) OP n,k,r;
/* n degree of permutation */
/* elementary transposition (k,k+1) */
/* AK 210804 V3.0 */
{
    INT erg=OK;
    CTO(INTEGER,"make_n_kelmtrans(1)",n);
    SYMCHECK(S_I_I(n)<2,"make_n_kelmtrans(1)<2");
    CTO(INTEGER,"make_n_kelmtrans(2)",k);
    SYMCHECK(S_I_I(k)<1,"make_n_kelmtrans(2)<1");
    SYMCHECK(S_I_I(k)>=S_I_I(n),"make_n_kelmtrans(2)>=n");
    {
    INT i;
    erg += m_il_p(S_I_I(n),r);
    for (i=0;i<S_P_LI(r);i++)
        M_I_I(i+1,S_P_I(r,i));
    M_I_I(S_I_I(k)+1, S_P_I(r,S_I_I(k)-1));
    M_I_I(S_I_I(k), S_P_I(r,S_I_I(k)));
    }
    ENDR("make_n_kelmtrans");
}



INT maxorder_young(a,b) OP a,b;
/* AK 070693 */
/* a is a partition, b becomes the length of the maximum permutation 
in the corresponding young group */
{
    INT i,erg=OK;    
    OP c;
    if (S_O_K(a) != PARTITION)
        return ERROR;
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    c = callocobject();
    erg += m_i_i((INT)0,b);
    for (i=(INT)0;i<S_PA_LI(a);i++)
        {
        erg += binom(S_PA_I(a,i),cons_zwei,c);
        erg += add_apply(c,b);
        }
    erg += freeall(c);
    if (erg != OK)
        EDC("maxorder_young");
    return erg;
}
#endif /* PERMTRUE */
#ifdef PERMTRUE
#ifdef PARTTRUE
INT next_shuffle_part(part,a,b) OP part,a,b;
/* AK 090693 */
/* next shuffle permutation according to part shape */
/* to be improved */
/* return TRUE / FALSE */
{
    INT e,i,j,k;
    OP c = a;
    if (a == b)
        {
        c = callocobject();
        *c = *a;
        C_O_K(a,EMPTY);
        e = next_shuffle_part(part,c,b);
        freeall(c);
        return e;
        }
    again:
    e = next(c,b);
    if (e == FALSE) 
        return e;
    /* now check of correct shape */
    j=(INT)0; /* durchlauf permutation */
    for (i=(INT)0;i<S_PA_LI(part);i++)
        {
        for (k=1L,j++; k<S_PA_II(part,i); k++,j++)
            if (S_P_II(b,j) < S_P_II(b,j-1))
                {
                c = b;
                goto again;
            }
        }
    return TRUE;
}
#endif /* PARTTRUE */

INT m_perm_rz_set(a,b) OP a,b;
/* AK 120194 */
/* enter a permutation a, 
   output vector of all reduced decompositions */
{
    OP d;
    INT erg = OK;
    CE2(a,b,m_perm_rz_set);
    CPT(VECTOR,"m_perm_rz_set(1)",a);

    d = CALLOCOBJECT();
    erg += numberof_inversionen(a,d);
    erg += co_120194(a,b,S_I_I(d),S_I_I(d));
    FREEALL(d);
    ENDR("m_perm_rz_set");
}

static INT co_120194(a,b,k,l) OP a,b; INT k,l;
{
    int i=(INT)0,j;
    OP c,d;
    INT erg = OK;

    if (k == 0)
        {
        erg += m_il_v(1L,b) ;
        erg += m_il_v(l,S_V_I(b,(INT)0)) ;
        goto eee;
        }
    c = callocobject();
    d = callocobject();
    erg += m_il_v((INT)0,b);
    for (i=1L;i<S_P_LI(a);i++)
        {
        if (S_P_II(a,i-1) > S_P_II(a,i))
            {
            erg += copy(a,c);
        erg += swap(S_P_I(c,i-1),S_P_I(c,i));
            erg += co_120194(c,d,k-1,l);
            for (j=(INT)0;j<S_V_LI(d);j++)
                {
                /* inc(S_V_I(d,j)); */
                erg += m_i_i(i,
                    S_V_I(    S_V_I(d,j),    /* S_V_LI(S_V_I(d,j)) */ k-1L)
                    );
                }
            erg += append(b,d,b);
            if (k==1) break;
            }
        }
    erg += freeall(c);
    erg += freeall(d);
eee:
    return erg;    
}

INT m_perm_rz_number(a,b) OP a,b;
/* AK 120194 */
/* enter a permutation a, 
   output number of all reduced decompositions */
{
    INT erg = OK;
    OP d;
    if (check_equal_2(a,b,m_perm_rz_number,&erg) == EQUAL)
                goto endr_ende;
    CPT(VECTOR,"m_perm_rz_number",a);
    d = callocobject();
    erg += numberof_inversionen(a,d);
    erg += co_120194_1(a,b,S_I_I(d),S_I_I(d));
    erg += freeall(d);
    ENDR("m_perm_rz_number");
}

static INT co_120194_1(a,b,k,l) OP a,b; INT k,l;
{
    int i=(INT)0;
    INT erg = OK;
    OP c,d;

    if (k == 0)
        {
        erg += m_i_i(1L,b) ;
        goto endr_ende;
        }
    c = callocobject();
    d = callocobject();
    erg += m_i_i((INT)0,b);
    for (i=1L;i<S_P_LI(a);i++)
        {
        if (S_P_II(a,i-1) > S_P_II(a,i))
            {
            erg += copy(a,c);
        erg += swap(S_P_I(c,i-1),S_P_I(c,i));
            erg += co_120194_1(c,d,k-1,l);
            erg += add_apply(d,b);
            if (k==1) break;
            }
        }
 
    erg += freeall(c);
    erg += freeall(d);
    ENDR("internal routine:    co_120194_1");
}

INT cast_apply_perm(a) OP a;
/* AK 280294 */
{
    INT erg = OK;
    EOP("cast_apply_perm(1)",a);
    switch(S_O_K(a))
        {
        case VECTOR:
            erg += m_ks_p(VECTOR,a,a);
            break;
        default:
            printobjectkind(a);
            erg += WTO("cast_apply_perm",a);
            break;
        }
    ENDR("cast_apply_perm");
}

INT sscan_permutation(t,a) OP a; char *t;
/* AK 050194 to read permutation from string
        format [1,2,3,..]
*/
{
    INT erg = OK;
    COP("sscan_permutation(1)",t);
    CTO(EMPTY,"sscan_permutation(2)",a);

    erg += b_ks_p(VECTOR,callocobject(),a);
    erg += sscan(t,INTEGERVECTOR,S_P_S(a));
    ENDR("sscan_permutation");
}

INT makevectorofperm(a,b) OP a,b;
/* input INTEGER object a
   output VECTOR object of length a! with permutations in 
          order of next */

/* AK 220702 */
{
    INT i;
    INT erg = OK;
    OP c;
    CTO(INTEGER,"makevectorofperm(1)",a);
    CE2(a,b,makevectorofperm);
    c = CALLOCOBJECT();
    erg += fakul(a,c);
    erg += m_l_v(c,b);
    erg += first_permutation(a,c);
    i=0;
    do {
        erg += copy_permutation(c,S_V_I(b,i));
        i++;
        } while (next_apply(c));
    FREEALL(c);
    ENDR("makevectorofperm");
}

INT bruhat_comp_perm(a,b) OP a,b;
/* compares according to the strong bruhat order*/
/* 1 if a>b 
   0 if a=b 
  -1 if a<b 
NONCOMPARABLE else */
{
        INT erg,erg2;
        erg = bru_comp(a,b);
        erg2 = bru_comp(b,a);
        if ((erg == TRUE) && (erg2 == TRUE)) return (INT) 0;
        if (erg == TRUE) return (INT ) 1;
        if ((erg == FALSE) && (erg2 == FALSE)) return NONCOMPARABLE;
        return (INT) -1;
}

/*  =TRUE  if a>=c  in the Bruhat order  ADD condition when c not long enough  */
INT bru_comp(a,c)   OP a,c;
{
        INT i,j,k,x,y1,y2;
        k=S_P_LI(a);
        y1=S_P_II(a,(INT)0);
        y2=S_P_II(a,k-1);
        if(  S_P_II(c,(INT)0) > y1 ) return (FALSE);

        if(  k < S_P_LI(c) ) {
                for (j=k;j<S_P_LI(c);j++)
                        if (j!=S_P_II(c,j)-1) return FALSE;
                }
        if(  (S_P_LI(c) == k) && (S_P_II(c,k-1) < y2)) return (FALSE);


        if (S_P_LI(c) < k) k = S_P_LI(c);

        for(i=0L;i<k;i++)  {
                x=0L;
                for(j=0L;j<k;j++){
                        if (  S_P_II(a,j) >i ) x++;
                        if (  S_P_II(c,j) >i ) x--;
                        if (x<0)  return (FALSE);
                }
        }

        return (TRUE);
}

INT t_VECTOR_BITREC(a,bitperm) OP a,bitperm;
/* AK 200195 */
{
    OP c,d,b;
    INT i,erg=OK;
    CTO(PERMUTATION,"t_VECTOR_BITREC(1)",a);
    c = callocobject();
    d = callocobject();
    b = callocobject();
    m_i_i(S_P_LI(a)+1,b);
    m_i_i(3,c);
    binom(b,c,d);
    freeall(c);
    m_il_nbv(S_I_I(d),b);
    fastrectr(a,d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        co_co_2(S_P_L(a),S_V_I(d,i),b);
        }
    b_ks_p(BITREC,b,bitperm);
    freeall(d);
    ENDR("t_VECTOR_BITREC");
    
}


INT fastrectr(a,v)  OP a,v;
/* AL 1094 */
{
        OP b,u;
        INT i,k,x,y,z,iv,i1;
        b=callocobject();
        u=callocobject();

        invers(a,b);
        init(VECTOR,v);
        m_il_v(3L,u);
        iv=0L;
        for(i=0L;i<S_P_LI(a)-1L;i++)
        {
                if( S_P_II(a,i)>S_P_II(a,i+1))
                {
                        z= S_P_II(a,i);
                        x=S_P_II(a,i+1);
                        for (k=z;k>=x;k--)
                        {
                                                                             
    if  ( S_P_II(b,k-1) >= i+2 && S_P_II(b,k) <=i+1)
                                {
                                        y=0;
                                        for(i1=0;i1<=i;i1++) {
                                                if( S_P_II(a,i1) <k) y++;
                                        }
                                        M_I_I(y,S_V_I(u,0L));
                                        M_I_I(i+1-y,S_V_I(u,1L));
                                        M_I_I(k-y,S_V_I(u,2L));
                                        inc(v);
                                        copy(u,S_V_I(v,iv));
                                        iv++;
                                }
                        }
                }
        }
        freeall(b);
        freeall(u);
    return OK;
}

INT makevectorofrect_permutation(a,b) OP a,b;
/* AK 130195 */
{
    OP c;
    INT erg = OK,i;
    CTO(INTEGER,"makevectorofrect_permutation(1)",a);
    c = callocobject();
    erg += makevectorofrect_lehmercode(a,c);
    erg += m_il_v(S_V_LI(c),b);
    for (i=0;i<S_V_LI(b);i++)
        {
        erg += lehmercode(S_V_I(c,i),S_V_I(b,i));
        erg += freeself(S_V_I(c,i));
        }
    erg += freeall(c);
    ENDR("makevectorofrect_permutation");
}

INT makevectorofrect_lehmercode(a,b) OP a,b;
/* AK 130195 */
{
    INT erg = OK,i,j;
    CTO(INTEGER,"makevectorofrect(1)",a);
    if (S_I_I(a) < (INT)0) erg = ERROR;
    else if (S_I_I(a) == (INT)0) erg += m_il_v((INT)0,b);
    else    {
        erg += m_il_v((INT)1,b);
        erg += m_l_nv(a,S_V_I(b,(INT)0));
        C_O_K(S_V_I(b,0),INTEGERVECTOR);
    
    for (i=1;i<S_I_I(a);i++)
        {
        for (j=S_V_LI(b)-1;j>0;j--)
            {
            if (S_V_II(S_V_I(b,j),S_I_I(a)-i) > 0)
                {
            erg += inc(b);
            erg += copy(S_V_I(b,j),S_V_I(b,S_V_LI(b)-1));
            C_O_K(S_V_I(b,S_V_LI(b)-1),INTEGERVECTOR);
              erg += m_i_i(S_V_II(S_V_I(b,j),S_I_I(a)-i)
            ,S_V_I(S_V_I(b,S_V_LI(b)-1),S_I_I(a)-1-i)); 
                }
            }
        for (j=1L;j<=i;j++)
            { 
            erg += inc(b);
            erg += m_l_nv(a,S_V_I(b,S_V_LI(b)-1));
            C_O_K(S_V_I(b,S_V_LI(b)-1),INTEGERVECTOR);
            erg += m_i_i(j,S_V_I(S_V_I(b,S_V_LI(b)-1),S_I_I(a)-i-1)); 
            }
        }

        }
    ENDR("makevectorofrect");
}

static INT co_co(n,bigr,vec) OP bigr,vec,n;
/* input bigr and vector which is to be manipulated */
/* n the degree of s_n */
/* insert ones in one block */
{
    INT r2,r1,r0,og;
    INT x,k,i,j,length_of_cell;
    r2 = S_V_II(bigr,2);
    r1 = S_V_II(bigr,1);
    r0 = S_V_II(bigr,0);
    length_of_cell = S_I_I(n)-r1-r0;

    k=S_I_I(n); x=r0 + r1;
    og = x*(x-1)*(3*k-2*x+1)/6; /* start of block */

    for (i=0;i<r1;i++)
        {
        for (j=0;j<r2;j++)
            /*
            m_i_i(1,S_V_I(vec,og+i*length_of_cell+j));
            */
            {
            k = og+i*length_of_cell+j;
            SET_BV_I(vec,k);
            }
        }
    return OK;
}

static INT co_co_2(n,bigr,vec) OP bigr,vec,n;
/* input bigr and vector which is to be manipulated */
/* n the degree of s_n */
/* insert ones in all blocks */
{
    INT i;
    INT erg = OK;
    OP c;
    CTO(INTEGER,"co_co_2(1)",n);
    c = callocobject();
    copy(bigr,c);
    for (i=S_V_II(c,1);i>=1;i--)
        {
        co_co(n,c,vec);
        dec(S_V_I(c,1));
        }
    copy(bigr,c);
    for (i=S_V_II(c,2);i>1;i--)
        {
        inc(S_V_I(c,0));
        dec(S_V_I(c,2));
        co_co(n,c,vec);
        }
    freeall(c);
    ENDR("internal routine:co_co_2");
}

INT order_permutation(a,b) OP a,b;
/* AK 210802 */
/* order of permutation */
/* result is in b
   b is minimal integer with a^b = id
*/
/* AK V3.1 031106 */
/* a and b may be equal */
{
    INT erg = OK;
    CTO(PERMUTATION,"order_permutation(1)",a);
    {
    OP part;
    INT i;
    part = CALLOCOBJECT();
    zykeltyp(a,part);
    copy(S_PA_I(part,0),b);
    for (i=1;i<S_PA_LI(part);i++) erg += kgv(S_PA_I(part,i),b,b);
    FREEALL(part);
    }
    ENDR("order_permutation");
}

    

INT rz_Dn(v,r) OP v,r;
/* AK 290296 */
/* rz in coxeter gruppe Dn */
{
    INT i,j,ii,jj,k,erg=OK;
    OP vc;
    OP rn;
    CTO(PERMUTATION,"rz_Dn",v);
    for (i=0;i<S_P_LI(v);i++)
        if (S_P_II(v,i) <= 0)  goto realdn;
    /* ist eigentlich s_n permutation */
    C_P_K(v,VECTOR);
    erg += rz_perm(v,r);
    C_P_K(v,BAR);
    goto endr_ende;
realdn:
    m_il_v((INT)0,r);
    vc = callocobject(); 
    rn = callocobject(); 
    erg += copy(v,vc);
realdn_again:
    /* es muss zwei - geben */
    for (j=i+1;j<S_P_LI(vc);j++)
        if (S_P_II(vc,j) <= (INT)0)  break;
    if (j == S_P_LI(vc))
        error("rz_Dn:perm not in Dn");
    erg += m_il_v(i+j,rn);
    k=0;
    m_i_i(-1,S_V_I(rn,k));
    k++;
    for (jj=2;jj<=j;jj++)
        m_i_i(jj,S_V_I(rn,k++));
    for (ii=1;ii<=i;ii++)
        m_i_i(ii,S_V_I(rn,k++));
    i = S_P_II(vc,i);
    j = S_P_II(vc,j);
    for (ii=S_P_LI(vc)-1,jj=ii;ii>=0;ii--)
        {
        if (S_P_II(vc,ii) != i) 
        if (S_P_II(vc,ii) != j) 
            {
            M_I_I(S_P_II(vc,ii),S_P_I(vc,jj));
            jj--;
            }
        }
    M_I_I(-i,S_P_I(vc,1));
    M_I_I(-j,S_P_I(vc,0));
    append(rn,r,r);
    for (i=0;i<S_P_LI(vc);i++)
        if (S_P_II(vc,i) <= 0)  goto realdn_again;
    C_P_K(vc,VECTOR);
    erg += rz_perm(vc,rn);
    C_P_K(v,BAR);
    erg += append(rn,r,r);
    
    
    erg += freeall(vc);
    erg += freeall(rn);
    ENDR("rz_Dn");
}



INT vorgaenger_bruhat(a,b) OP a,b; { return vorgaenger_bruhat_weak(a,b); }

INT vorgaenger_bruhat_weak(a,b) OP a,b;
/* weak bruhat oder, only elementary transpositions */
{
    INT i,l,h;
    OP z;
    INT erg = OK;
    CPT(VECTOR,"vorgaenger_bruhat_weak(1)",a);
    CE2(a,b,vorgaenger_bruhat_weak);
    for (l=0,i=1;i<S_P_LI(a);i++)
        if (S_P_II(a,i) < S_P_II(a,i-1)) l++;
    /* l ist the number of decreases */
    erg += m_il_v(l,b);
    for (l=0,i=1;i<S_P_LI(a);i++)
        if (S_P_II(a,i) < S_P_II(a,i-1)) {
            z = S_V_I(b,l);
            copy_permutation(a,z);
            h = S_P_II(z,i);
            M_I_I(S_P_II(z,i-1),S_P_I(z,i));
            M_I_I(h,S_P_I(z,i-1));
            l++;
            }
    ENDR("vorgaenger_bruhat_weak");
}

INT vorgaenger_bruhat_strong(a,b) OP a,b;
/* strong bruhat oder, all transpositions */
/* AK 230702 */
{
    INT erg = OK;
    CPT(VECTOR,"vorgaenger_bruhat_strong(1)",a);
    CE2(a,b,vorgaenger_bruhat_strong);
    {
    INT i;
    erg += m_il_v(0,b);
    for (i=0;i<S_P_LI(a);i++)
        {
        INT wi = S_P_II(a,i);
        /* to the right and smaller */
        INT rightmin=0;
        INT j;
        for (j=i+1;j<S_P_LI(a);j++)
            {
            INT wj = S_P_II(a,j);
            if ((wj < wi) && (wj > rightmin))
                 {
                 OP perm_in_result;
                 INC(b);
                 perm_in_result =  S_V_I(b,S_V_LI(b)-1);
                 copy_permutation(a,perm_in_result);
                 M_I_I(wj,S_P_I(perm_in_result,i));
                 M_I_I(wi,S_P_I(perm_in_result,j));
                 rightmin = wj;
                 }
            }
        }
    }
    ENDR("vorgaenger_bruhat_strong");
}       

#define BRUHAT_IDEAL_CO(a,b,func)\
    {\
    INT i,j,k;\
    OP c,d,e,z,f;\
    c = CALLOCOBJECT();\
    d = CALLOCOBJECT();\
    e = CALLOCOBJECT();\
    erg += numberof_inversionen(a,c); \
    INC(c);\
    erg += b_l_v(c,b);\
    erg += m_o_v(a,S_V_I(b,0));\
    for (i=0;i<S_V_LI(b)-1;i++)\
        {\
        erg += init(BINTREE,d);\
        for (j=0;j<S_V_LI(S_V_I(b,i));j++)\
            {\
            z = S_V_I(S_V_I(b,i),j);\
            erg += (*func)(z,e);\
            for(k=0;k<S_V_LI(e);k++)\
                {\
                f = CALLOCOBJECT();\
                SWAP(f,S_V_I(e,k));\
                insert(f,d,NULL,NULL);\
                }\
            }\
        erg += t_BINTREE_VECTOR(d,S_V_I(b,i+1));\
        }\
    FREEALL(d);\
    FREEALL(e);\
    }

INT bruhat_ideal(a,b) OP a,b; { return bruhat_ideal_weak(a,b); }

INT bruhat_ideal_weak(a,b) OP a,b;
/* input: PERMUTATION object
   output: VECTOR object, i-th entry = i-th level in bruhat ideal */
/* weak bruhat oder, only elementary transpositions */
{
    INT erg = OK;
    CPT(VECTOR,"bruhat_ideal_weak(1)",a);
    CE2(a,b,bruhat_ideal_weak);
    BRUHAT_IDEAL_CO(a,b,vorgaenger_bruhat_weak);
    ENDR("bruhat_ideal_weak");
}

INT bruhat_ideal_strong(a,b) OP a,b;
/* input: PERMUTATION object
   output: VECTOR object, i-th entry = i-th level in bruhat ideal */
/* strong bruhat oder, all transpositions */
/* AK 230702 */
{
    INT erg = OK;
    CPT(VECTOR,"bruhat_ideal(1)",a);
    CE2(a,b,bruhat_ideal);
    BRUHAT_IDEAL_CO(a,b,vorgaenger_bruhat_strong);
    ENDR("bruhat_ideal");
} 


INT bruhat_rank_function(a,b) OP a,b;
{
    INT erg = OK;
    OP d;
    INT i;
    CPT(VECTOR,"bruhat_rank_function(1)",a);
    d = callocobject();
    bruhat_ideal(a,d);
    m_il_v(S_V_LI(d),b);
    for(i=0;i<S_V_LI(d);i++)
        M_I_I(
            S_V_LI(S_V_I(d,i)),
            S_V_I(b,i)
            );
    erg += freeall(d);
    ENDR("bruhat_rank_function");
}

#define BRUHAT_INTERVAL_CO(a,b,c,func)\
    if (EQ(a,b)) {\
        erg += m_il_v(1,c);\
	erg += m_o_v(a,S_V_I(c,0));\
        goto ende;\
        }\
    {\
    OP d,e,f,z;\
    INT i,j,k;\
    e = CALLOCOBJECT();\
    d = CALLOCOBJECT();\
    erg += numberof_inversionen(a,d);\
    erg += numberof_inversionen(b,e);\
    if (le(d,e)) { \
        FREEALL(e);\
        FREEALL(d);\
	m_il_v(0,c); \
	goto ende; \
	}\
    erg += m_il_v(S_I_I(d)-S_I_I(e)+1,c);\
    erg += m_o_v(a,S_V_I(c,0));\
    for (i=0;i<S_V_LI(c)-1;i++)\
        {\
        erg += init(BINTREE,d);\
        for (j=0;j<S_V_LI(S_V_I(c,i));j++)\
            {\
            z = S_V_I(S_V_I(c,i),j);\
            erg += (*func)(z,e);\
            for(k=0;k<S_V_LI(e);k++)\
                {\
                f = CALLOCOBJECT();\
                SWAP(f,S_V_I(e,k));\
                insert(f,d,NULL,NULL);\
                }\
            }\
        erg += t_BINTREE_VECTOR(d,S_V_I(c,i+1));\
        }                                                     \
\
    /* ideal til level of b */\
\
    /* starting from bottom removing items */\
    \
    for (j=0;j<S_V_LI(S_V_I(c,i));j++)\
	{\
	z = S_V_I(S_V_I(c,i),j);\
	if (NEQ(z,b)) delete_entry_vector(S_V_I(c,i),j--,S_V_I(c,i));\
        }\
\
    if (S_V_LI(S_V_I(c,i))== 0) {\
        FREEALL(e);\
        FREEALL(d);\
	m_il_v(0,c); \
	goto ende; \
        }\
\
    /* check backward */\
    i--;\
    for (;i>0;i--)\
    for (j=0;j<S_V_LI(S_V_I(c,i));j++)\
	{\
	z = S_V_I(S_V_I(c,i),j);\
        erg += (*func)(z,e);\
        for(k=0;k<S_V_LI(e);k++)\
            {\
            if (index_vector(S_V_I(e,k),S_V_I(c,i+1)) != -1) goto next;\
            }\
        /* the entry z does not belong to the ideal */\
        delete_entry_vector(S_V_I(c,i),j--,S_V_I(c,i)); \
next:   ;\
        }\
    \
    FREEALL(e);\
    FREEALL(d);\
    }\
ende:;

INT bruhat_interval_weak(a,b,c) OP a,b,c;
/* weak bruhat ideal between a and b
*/
/* weak = differ by elementary transpositions */
{
    INT erg = OK;
    CPT(VECTOR,"bruhat_interval_weak(1)",a);
    CPT(VECTOR,"bruhat_interval_weak(2)",b);
    BRUHAT_INTERVAL_CO(a,b,c,vorgaenger_bruhat_weak);
    ENDR("bruhat_interval_weak");
}

INT bruhat_interval_strong(a,b,c) OP a,b,c;
/* strong bruhat ideal between a and b
*/
/* strong = differ by any transpositions */
{
    INT erg = OK;
    CPT(VECTOR,"bruhat_interval_strong(1)",a);
    CPT(VECTOR,"bruhat_interval_strong(2)",b);
    BRUHAT_INTERVAL_CO(a,b,c,vorgaenger_bruhat_strong);
    ENDR("bruhat_interval_strong");
} 



INT inversion_matrix_perm(p,e) OP p,e;
/* AK 180598 V2.0 */
/* p and e may be equal */
{
    INT i,j,k,m;
    INT erg = OK;
    erg += diagramm_permutation(p,e);
    for (j=(INT)0;j<S_M_LI(e); j++)
                {
                k=j+1L;
                for (i=S_M_HI(e)-1L;i>=(INT)0 ; i--)
                        {
                        if (EMPTYP(S_M_IJ(e,i,j)))
                                {
                                erg += m_i_i(1L,S_M_IJ(e,i,j)) ;
                                k++;
                                }
                        else if (S_M_IJI(e,i,j) == -1L)
                                erg += m_i_i((INT)0,S_M_IJ(e,i,j));
                        else if (S_M_IJI(e,i,j) == (INT)0){
                                erg += m_i_i((INT)0,S_M_IJ(e,i,j));
                                for (m=j+1L; m<S_M_LI(e);m++)
                                        erg += m_i_i(-1L,S_M_IJ(e,i,m));
                                for (m=i-1L; m>=(INT)0 ; m--)
                                        if (not EMPTYP(S_M_IJ(e,m,j))) {
                                                if (S_M_IJI(e,m,j) == -1L)
                                                    erg += m_i_i((INT)0,S_M_IJ(e,m,j)
);
                                                }
                                        else m_i_i((INT)0,S_M_IJ(e,m,j));

                                break;
                                }
                        else error("inversion_matrix_perm:wrong content");
                        }
                }
	ENDR("inversion_matrix_perm");
}

#endif /* PERMTRUE */

