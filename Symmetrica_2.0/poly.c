/* file: poly.c */
#include "def.h"
#include "macro.h"

struct monom * callocmonom();

INT mem_counter_monom=0;

static int tex_poly_var = LETTERS;
static int tex_poly_first_var_index = (INT)0;
/* static INT monom_speicher_ende(); */


#ifdef POLYTRUE
INT get_tex_polynom_parameter(a) INT a; /* AK 090395 */
{
    INT erg = OK;
    switch(a)
    {
    case VARTYP: 
        return tex_poly_var;
    case FIRSTVARINDEX: 
        return tex_poly_first_var_index;
    default:
        erg += error("get_tex_polynom:wrong parameter");
        goto endr_ende;
    }
    ENDR("get_tex_polynom_parameter");
}


INT set_tex_polynom_parameter(i,a) INT i,a; /* AK 090395 */
{
    INT erg =OK;
    switch(i)
    {
    case FIRSTVARINDEX:
        tex_poly_first_var_index = a;
        break;
    case VARTYP:
        if (a == LETTERS)
            tex_poly_var = LETTERS;
        else if (a == NUMERICAL)
            tex_poly_var = NUMERICAL;
        else
            {
            erg += error("set_tex_polynom:VARTYP:wrong parameter");
            goto endr_ende;
            }
        break;
    default:
        erg+= error("set_tex_polynom:wrong parameter");
        goto endr_ende;
    }
    ENDR("set_tex_polynom_parameter");
}


INT monom_release()
/* AK 100893 */
    {
    INT erg = OK;
    return erg;
    }


INT eval_polynom(poly,vec,res) OP poly,vec,res;
/* AK 310588 */
/* ein polynom wird ausgewertet indem der vector
vec eingesetzt wird
bsp     poly:= 2 [3,0,1]
    vec:= [4,4,5]
    res = 2 * 4^3 * 5 = 640 [0,0,0] */
/* AK 110789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
/* AK 220904 V3.0 */
{
    INT erg=OK;
    CTO(POLYNOM,"eval_polynom(1)",poly);
    CTTO(VECTOR,INTEGERVECTOR,"eval_polynom(2)",vec);
    CE3(poly,vec,res,eval_polynom);
    {
    OP zeiger = poly,monom,z;
    OP speicher;
    INT i,l;

    if (NULLP(poly)) 
        {
        init(POLYNOM,res);
        goto endr_ende;
        }

    if (scalarp(poly))
        {
        erg += m_scalar_polynom(poly,res);
        goto endr_ende;
        }


    speicher = callocobject();
    m_il_v(10,speicher); 
    for (i=0;i<10;i++) m_il_v(S_V_LI(vec),S_V_I(speicher,i));

    // c = callocobject();
    while (zeiger != NULL)
    {
        monom = callocobject(); 
        erg += m_skn_po(S_PO_S(zeiger),S_PO_K(zeiger),NULL,monom);
        if (not VECTORP(S_PO_S(zeiger)))
        { 
            printobjectkind(S_PO_S(zeiger));
            return error("eval_polynom:self != VECTOR "); 
        }
        for (i=(INT)0;i<S_PO_SLI(zeiger); i++)
        {
            if (i >= S_V_LI(vec)) goto evalpoly3;
            /* i ist < S_V_LI(vec) */
            if (not EMPTYP(S_V_I(vec,i)))
            if (S_PO_SII(zeiger,i) != (INT)0)
                { 
            if (S_PO_SII(zeiger,i) != 1L)
                {
                if (S_PO_SII(zeiger,i) >= S_V_LI(speicher))
                    {
                    l = S_V_LI(speicher);
                    inc_vector_co(speicher,
                      S_PO_SII(zeiger,i)-S_V_LI(speicher)+1);
                    for (;l<S_V_LI(speicher);l++)
                      m_il_v(S_V_LI(vec),S_V_I(speicher,l));
                    }

                z = S_V_I(S_V_I(speicher,S_PO_SII(zeiger,i)),i);
                if (EMPTYP(z))
                  erg += hoch(S_V_I(vec,i),S_PO_SI(zeiger,i),z);
                MULT_APPLY(z,S_PO_K(monom)); 
                }
            else /* AK 040892 */
                MULT_APPLY(S_V_I(vec,i),S_PO_K(monom)); 
                }
            M_I_I((INT)0,S_PO_SI(monom,i)); 
        };
evalpoly3:
        insert(monom,res,add_koeff,comp_monomvector_monomvector); 
        zeiger = S_PO_N(zeiger);
    }
    if (nullp(res))
        erg += m_i_i(0,res);
    else if (S_PO_N(res) == NULL) /* AK 311091 */
        if (nullp(S_PO_S(res))) /* scalar as result */
            {
            OP c = CALLOCOBJECT();
            SWAP(S_PO_K(res),c);
            FREESELF(res);
            SWAP(c,res);
            FREEALL(c);
            }
    FREEALL(speicher);
    }
    ENDR("eval_polynom");
}
#endif /* POLYTRUE */




#ifdef MONOMTRUE
/* global as used in the macro B_SK_MO */
INT monom_speicherindex=-1; /* AK 301001 */
INT monom_speichersize=0; /* AK 301001 */
struct monom **monom_speicher=NULL; /* AK 301001 */

INT monom_anfang()
/* AK 100893 */
    {
    ANFANG_MEMMANAGER(monom_speicher,monom_speicherindex,
                      monom_speichersize,mem_counter_monom);
    return OK;
    }

struct monom * callocmonom()
/* AK 230688 */ /* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg =OK;
    struct monom *c; 
    CALLOC_MEMMANAGER(struct monom, 
                      monom_speicher, 
                      monom_speicherindex,
                      mem_counter_monom,
                      c);
    return c;
    ENDTYP("callocmonom",struct monom *);
}

INT freemonom(v) struct monom *v;
/* AK 231001 */
{
    INT erg = OK;
    FREE_MEMMANAGER(struct monom *, 
                    monom_speicher,
                    monom_speicherindex,
                    monom_speichersize,
                    mem_counter_monom,
                    v);
    ENDR("freemonom");
}
 
INT monom_ende()
/* AK 230101 */
{
    INT erg = OK;
    ENDE_MEMMANAGER(monom_speicher,
                    monom_speicherindex,
                    monom_speichersize,
                    mem_counter_monom,"monom_ende:speicher not freed");
    ENDR("monom_speicher_ende");
}


INT m_sk_mo(self,koeff,c) OP self,koeff,c;
/* AK 070690 V1.1 */ /* AK 200891 V1.3 */
/* AK 211106 V3.1 */
{
    INT erg = OK;
    CE3(self,koeff,c,m_sk_mo);
    B_SK_MO(CALLOCOBJECT(),CALLOCOBJECT(),c);
    COPY(self,S_MO_S(c));  
    COPY(koeff,S_MO_K(c));
    ENDR("m_sk_mo");
}



INT b_sk_mo(self,koeff,c) OP self,koeff,c;
/* build_self koeff_monom AK 230688 */
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    OBJECTSELF d;
    INT erg = OK;
    COP("b_sk_mo(3)",c);

    SYMCHECK( ( (self != NULL) && (self == koeff) ) ,"b_sk_mo:identical objects");

    d.ob_monom = callocmonom(); /* AK 161189 */

    erg += b_ks_o(MONOM,d,c);
    C_MO_S(c,self);
    C_MO_K(c,koeff);
    ENDR("b_sk_mo");
}

INT mult_apply_monom(a,b) OP a,b;
/* AK  230999 */
{
    INT erg = OK;    
    CTO(MONOM,"mult_apply_monom(1)",a);

    if (S_O_K(b) == MONOM) {
        erg += add_apply(S_MO_S(a), S_MO_S(b));
        MULT_APPLY(S_MO_K(a), S_MO_K(b));
        }
    else {
        erg += mult(a,b,b);
        }
    ENDR("mult_apply_monom");
}

INT mult_monom(a,b,c) OP a,b,c;
/* AK 230999 */
{
    INT erg = OK;
    CTO(MONOM,"mult_monom(1)",a);
    CTO(EMPTY,"mult_monom(3)",c);

    switch(S_O_K(b))
        {
        case INTEGER:
            erg += copy_monom(a,c);
            erg += mult_apply_integer(b,S_MO_K(c));
            break;
        case BRUCH:
            erg += copy_monom(a,c);
            erg += mult_apply_bruch(b,S_MO_K(c));
            break;
        case LONGINT:
            erg += copy_monom(a,c);
            erg += mult_apply_longint(b,S_MO_K(c));
            break;
        default:
            erg += WTO("mult_monom",b);
        }
    ENDR("mult_monom");
}



INT objectwrite_monom(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    COP("objectwrite_monom(1)",f);
    fprintf(f,"%ld ",(INT)MONOM);
    erg += objectwrite(f,S_MO_K(a)); 
    erg += objectwrite(f,S_MO_S(a)); 
    ENDR("objectwrite_monom");
}



INT objectread_monom(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    COP("objectread_monom(1)",f);
    erg += b_sk_mo(callocobject(),callocobject(),a);
    erg += objectread(f,S_MO_K(a)); 
    erg += objectread(f,S_MO_S(a)); 
    ENDR("objectread_monom");
}



INT scan_monom(c) OP c;
/* AK 230688 */ /* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    OBJECTKIND kind;
    INT erg = OK;
    CTO(EMPTY,"scan_monom(1)",c);

    erg += b_sk_mo(callocobject(),callocobject(),c);
    printeingabe("what kind of monom");
    kind = scanobjectkind();

    erg += scan(kind,S_MO_S(c));
    printeingabe("what kind of coefficent");
    kind = scanobjectkind();
    erg += scan(kind,S_MO_K(c));
    ENDR("scan_monom");
}



INT fprint_monom(f,monom) FILE *f; OP monom;
/* AK 230688 */ /* AK 100789 V1.0 */ /* AK 071289 V1.1 */
/* AK 040391 V1.2 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    COP("fprint_monom(1)",f);
    CTO(MONOM,"fprint_monom(2)",monom);

    if (dynamicp(S_MO_K(monom))) /* AK zum unterscheiden */
        fprintf(f,"(");
    erg += fprint(f,S_MO_K(monom)); 
    if (dynamicp(S_MO_K(monom))) /* AK 240795 */
        fprintf(f,")");
    if (f==stdout)
    {
        if (zeilenposition > row_length) {
            zeilenposition = (INT)0; fprintf(stdout,"\n"); }
        else zeilenposition++;
    }
    fprintf(f," "); 
    erg += fprint(f,S_MO_S(monom));
    if (f==stdout)
    {
        if (zeilenposition > row_length) {
            zeilenposition = (INT)0; 
            fprintf(stdout,"\n"); 
            }
    }
    ENDR("fprint_monom");
}



INT tex_monom(monom) OP monom;
/* AK 230688 */ /* AK 100789 V1.0 */ /* AK 191289 V1.1 */
/* AK 070291 V1.2 tex to texout */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"tex_monom(1)",monom);
    if (POLYNOMP(S_MO_K(monom)))
          fprintf(texout,"(");
    erg += tex(S_MO_K(monom)); 
    fprintf(texout,"\\ ");
    texposition += (INT)2; 
    if (POLYNOMP(S_MO_K(monom))) /* AK 240795 */
          fprintf(texout,")");
    erg += tex(S_MO_S(monom)); 
    ENDR("tex_monom");
}
#endif    /* MONOMTRUE */

#ifdef POLYTRUE
INT m_s_po(self,poly) OP self,poly;
/* AK 120790 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP s;
    COP("m_s_po(2)",poly);
    s = CALLOCOBJECT();
    COPY(self,s);
    erg += b_s_po(s,poly);
    ENDR("m_s_po");
}



INT b_s_po(self,poly) OP self,poly;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
/* AK 210904 V3.0 */
{
    INT erg = OK;
    COP("b_s_po(2)",poly);
    SYMCHECK(self==poly,"b_s_po:two equal parameters");
    {
    erg += b_sn_l(CALLOCOBJECT(),NULL,poly);
    C_O_K(poly,POLYNOM);
    B_SK_MO(self,CALLOCOBJECT(),S_L_S(poly));
    M_I_I(1,S_PO_K(poly));
    }
    ENDR("b_s_po");
}


#endif     /* POLYTRUE */

#ifdef MONOMTRUE
INT freeself_monom(a) OP a;
/* AK 100789 V1.0 */ /* AK 211189 V1.1 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"freeself_monom(1)",a);

    FREEALL(S_MO_S(a)); 
    FREEALL(S_MO_K(a)); 
    FREEMONOM(S_O_S(a).ob_monom); 
    C_O_K(a,EMPTY); 
    ENDR("freeself_monom");
}



INT comp_monom(a,b) OP a,b;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */
/* AK 080390 bei gleichheit von self wird koeff verglichen */ 
/* AK 200891 V1.3 */
{
    INT erg=OK;
    CTO(MONOM,"comp_monom(1)",a);
    CTO(MONOM,"comp_monom(2)",b);
    { 
    INT res;
    res = COMP(S_MO_S(a), S_MO_S(b));
    if (res != 0) 
        return res;
    else
        return COMP(S_MO_K(a),S_MO_K(b));
    }
    ENDR("comp_monom");
}



INT copy_monom(a,b) OP a,b;
/* AK 100789 V1.0 */ /* AK 071289 V1.1 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"copy_monom(1)",a);
    CTO(EMPTY,"copy_monom(2)",b);
    B_SK_MO(CALLOCOBJECT(),CALLOCOBJECT(),b);
    COPY(S_MO_K(a), S_MO_K(b));
    COPY(S_MO_S(a), S_MO_S(b));
    ENDR("copy_monom");
}



OP s_mo_s(a) OP a;
/* select_monom_self */ /* AK 100789 V1.0 */ /* AK 191289 V1.1 */
/* AK 200891 V1.3 */
{
    OBJECTSELF c;
    if (a == NULL) 
        return error("s_mo_s:a == NULL"),(OP)NULL;
    if (S_O_K(a) != MONOM) 
        return error("s_mo_s:a  != MONOM"),(OP)NULL;
    c = s_o_s(a);
    return(c.ob_monom->mo_self);
}

OP s_mo_k(a) OP a;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    OBJECTSELF c;
    if (a == NULL) 
        return error("s_mo_k:a == NULL"),(OP)NULL;
    if (S_O_K(a) != MONOM) 
        return error("s_mo_k:a  != MONOM"),(OP)NULL;
    c = s_o_s(a);
    return(c.ob_monom->mo_koeff);
}

/* the following routines only work with self part which are VECTORobjects */
OP s_mo_sl(a) OP a; 
/* AK 200891 V1.3 */
{
    return s_v_l(s_mo_s(a)); 
}
INT s_mo_sli(a) OP a; 
/* AK 200891 V1.3 */
{
    return s_v_li(s_mo_s(a)); 
}
OP s_mo_si(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
{
    return s_v_i(s_mo_s(a),i); 
}
INT s_mo_sii(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
{
    return s_v_ii(s_mo_s(a),i); 
}


INT s_mo_ki(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    return(s_i_i(s_mo_k(a))); 
}

INT c_mo_s(a,b) OP a,b; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_monom->mo_self = b; 
    return(OK); 
}

INT c_mo_k(a,b) OP a,b; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_monom->mo_koeff = b; 
    return(OK); 
}

INT mult_scalar_monom(a,b,c) OP a,b,c;
/* AK 111188 */
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"mult_scalar_monom(2)",b);
    CTO(EMPTY,"mult_scalar_monom(3)",c);
    B_SK_MO(CALLOCOBJECT(),CALLOCOBJECT(),c);
    COPY(S_MO_S(b),S_MO_S(c)); 
    MULT(S_MO_K(b),a,S_MO_K(c));
    ENDR("mult_scalar_monom");
}

INT mult_integer_monom(a,b,c) OP a,b,c;
/* AK 111188 */
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(INTEGER,"mult_integer_monom(1)",a);
    CTO(MONOM,"mult_integer_monom(2)",b);
    CTO(EMPTY,"mult_integer_monom(3)",c);

    B_SK_MO(CALLOCOBJECT(),CALLOCOBJECT(),c);
    COPY(S_MO_S(b),S_MO_S(c));
    MULT_INTEGER(a,S_MO_K(b),S_MO_K(c));

    ENDR("mult_integer_monom");
}

#endif    /* MONOMTRUE */

#ifdef POLYTRUE 
INT mult_polynom(a,b,d) OP a,b,d;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 150591 V1.2 */
/* AK 080891 V1.3 */
/* CC 210595 fuer die rationnellen Funktionen*/

{
    INT erg = OK;
    OP tp1, tp2;
    CTO(POLYNOM,"mult_polynom(1)",a);
    CTO(EMPTY,"mult_polynom(3)",d);

    if (NULLP(a))
        {
        M_I_I(0,d); 
        goto ende;
        }

    switch(S_O_K(b)) {
    case INTEGER:
    case FF:
    case LONGINT:
        erg+=mult_scalar_polynom(b,a,d);
        break;
#ifdef BRUCHTRUE
    case BRUCH: 
               if((!scalarp(S_B_O(b))) ||(!scalarp(S_B_U(b))))
                {
                        tp1=callocobject();tp2=callocobject();
                        M_I_I(1L,tp1);m_ou_b(a,tp1,tp2);
                        copy(tp2,a);
                        freeall(tp1);freeall(tp2);
                        erg += mult_bruch_bruch(a,b,d);
                }
                else
                        erg+=mult_scalar_polynom(b,a,d);
                break;
#endif /* BRUCHTRUE */
    case POLYNOM: erg+=mult_polynom_polynom(a,b,d);
        break;
#ifdef SCHUBERTTRUE
    case SCHUBERT: 
        erg+=mult_schubert_polynom(b,a,d); /* AK 190690 */
        goto ende;
#endif /* SCHUBERTTRUE */
#ifdef GRALTRUE
    case GRAL:    
        erg += mult_scalar_gral(a,b,d); 
        goto ende;
#endif /* GRALTRUE */
#ifdef SCHURTRUE
    case HOM_SYM:
        erg += mult_homsym_scalar(b,a,d); 
        goto ende; 
    case MONOMIAL:
        erg += mult_monomial_scalar(b,a,d); 
        goto ende; 
    case POW_SYM:
        erg += mult_powsym_scalar(b,a,d); 
        goto ende; 
    case ELM_SYM:
        erg += mult_elmsym_scalar(b,a,d); 
        goto ende; 
    case SCHUR: 
        erg += mult_schur_scalar(b,a,d); 
        goto ende; 
#endif /* SCHURTRUE */
#ifdef MATRIXTRUE
    case MATRIX: 
        erg+=mult_scalar_matrix(a,b,d);
        goto ende;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
    case MONOM: 
        erg += mult_scalar_monom(a,b,d); 
        goto ende;
#endif /* MONOMTRUE */
    case MONOPOLY:
        erg += mult_monopoly_polynom(b,a,d);         
        goto ende;
        
    default: 
        erg += WTO("mult_polynom(2)",b);
    }
ende:
    ENDR("mult_polynom");
}



INT mult_scalar_polynom(a,poly,res) OP a,poly,res;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 150591 V1.2 */ 
/* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(POLYNOM,"mult_scalar_polynom(2)",poly);
    CTO(EMPTY,"mult_scalar_polynom(3)",res);
    MULT_SCALAR_MONOMLIST(a,poly,res);
    ENDR("mult_scalar_polynom");
}

INT mult_polynom_polynom(eins,zwei,c) OP eins, zwei, c;
/* AK 100789 V1.0 */ /* AK 081289 V1.1 */ /* AK 150591 V1.2 */
/* AK 140891 V1.3 */
{
    OP z, ez, zz;
    INT erg = OK;
    CTO(POLYNOM,"mult_polynom_polynom(1)",eins);
    CTO(POLYNOM,"mult_polynom_polynom(2)",zwei);
    CTO(EMPTY,"mult_polynom_polynom(3)",c);

    erg += init_polynom(c);

    if (NULLP(eins)) goto ende;
    if (NULLP(zwei)) goto ende;

    zz = zwei;
    while (zz != NULL)
    {
        z = CALLOCOBJECT();
        erg += copy_list(eins,z); /* eins ist polynom */

        ez = z;
        while (ez != NULL)
        {
            ADD_APPLY( S_PO_S(zz), S_PO_S(ez));
            MULT_APPLY( S_PO_K(zz), S_PO_K(ez));
            ez = S_PO_N(ez);
        };
        INSERT(z,c,add_koeff,comp_monomvector_monomvector);
        zz = S_PO_N(zz);
    };

ende:
    CTO(POLYNOM,"mult_polynom_polynom(e3)",c);
    ENDR("mult_polynom_polynom");
}

INT init_polynom(a) OP a;
/* AK 250102 */
{
    INT erg = OK;
    CTO(EMPTY,"init_polynom(1)",a);
    erg += b_sn_l(NULL,NULL,a);
    C_O_K(a,POLYNOM);
    CTO(POLYNOM,"init_polynom(e1)",a);
    ENDR("init_polynom");
}



INT numberofmonomials(a,n) OP a,n;
/* AK 230999 */
/* only works for positive integer coefficients */
{
    INT erg = OK;
    OP z;

    CTO(POLYNOM,"numberofmonomials",a);
    CE2(a,n,numberofmonomials);

    erg += m_i_i((INT)0,n); /* frees the result automaticaly */
    if (S_L_S(a) == NULL)
        goto ne;
    z = a;
    while (z != NULL)
        {
        if (S_O_K(S_PO_K(z)) == INTEGER)
            {
            if (negp(S_PO_K(z))) { m_i_i(-1L,n); goto ne; }
            else add_apply(S_PO_K(z),n);
            }
        else if (S_O_K(S_PO_K(z)) == LONGINT)
                        {
                        if (negp(S_PO_K(z))) { m_i_i(-1L,n); goto ne; }
                        else add_apply(S_PO_K(z),n);
                        }
        else {
            println(a);
            WTO("numberofmonomials",S_PO_K(z));
            m_i_i(-1L,n);
            goto ne;
            }
        z = S_PO_N(z);
        }
ne:
    ENDR("numberofmonomials");
}

INT numberofvariables(a,n) OP a,n;
/* AK 250692 */
/* n becomes the number of variables of the POLYNOM a */
{
    INT i,erg = OK;
    OP z;

    CTO(POLYNOM,"numberofvariables(1)",a);
    CE2(a,n,numberofvariables);

    M_I_I((INT)0,n); 
    if (S_L_S(a) == NULL)
        goto ne;
    z = a;
    while (z != NULL)
        {
        i = S_PO_SLI(z)-1L;
        while (S_PO_SII(z,i) == (INT)0) 
            i--;
        if (i+1L > S_I_I(n)) 
            M_I_I(i+1L,n);
        z = S_PO_N(z);
        }
ne:
    ENDR("numberofvariables");
}


INT mult_disjunkt_polynom_polynom(a,b,c) OP a, b, c;
/* AK 300889 */
/* die beiden polynome haben disjunkte alphabete */
/* beim c werden die alphabete hintereinandergehaengt */
/* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    OP z, ap, bp;
    OP n,l;
    INT i;
    INT erg = OK;
    CTO(POLYNOM,"mult_disjunkt_polynom_polynom(1)",a);
    CTO(POLYNOM,"mult_disjunkt_polynom_polynom(2)",b);
    CE3(a,b,c,mult_disjunkt_polynom_polynom);

/* first check the number of variables of a */ /* AK 250692 */
    n = callocobject();
    numberofvariables(a,n);

    bp = b;
    l = callocobject();
    while (bp != NULL)
    {
        z = callocobject();
        copy(a,z);

        ap = z;
        while (ap != NULL)
        {
            if (S_PO_SLI(ap) < S_I_I(n))   /* AK 250692 */
                {
                m_il_nv(S_I_I(n),l);
                for (i=(INT)0;i<S_PO_SLI(ap);i++)
                    M_I_I(S_PO_SII(ap,i),S_V_I(l,i));
                append(l,S_PO_S(bp),S_PO_S(ap));
                }
            else
                append(    S_PO_S(ap), S_PO_S(bp), S_PO_S(ap));
            mult(    S_PO_K(ap), S_PO_K(bp), S_PO_K(ap));
            ap = S_PO_N(ap);
        };

        add_apply(z,c);
        freeall(z);

        bp = S_PO_N(bp);
    };
    FREEALL(n);
    FREEALL(l);
    ENDR("mult_disjunkt_polynom_polynom");
}



INT mult_apply_polynom_scalar(a,b) OP a,b;
/* AK 160290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP c;
    CTO(POLYNOM,"mult_apply_polynom_scalar(1)",a);
    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += copy_polynom(a,b);
    erg += mult_apply_scalar_polynom(c,b);
    erg += freeall(c);
    ENDR("mult_apply_polynom_scalar");
}



INT mult_apply_polynom(a,b) OP a,b;
/* AK 140290 V1.1 */ /* AK 140591 V1.2 */ /* AK 220791 V1.3 */
{
    INT erg = OK; /* zuweisung AK091091 */
    CTO(POLYNOM,"mult_apply_polynom(1)",a);
    EOP("mult_apply_polynom(2)",b);
    if (NULLP(b)) 
        goto map_ende;
  
    if (NULLP(a))
        {
        erg += m_i_i((INT)0,b); 
        goto map_ende;
        }

    switch(S_O_K(b)) {
        case BRUCH:
        case LONGINT:
        case INTEGER:  /* a ist scalar, b ist poly */
            erg+= mult_apply_polynom_scalar(a,b); 
            goto map_ende;
        case POLYNOM: 
            erg+= mult_apply_polynom_polynom(a,b); 
            goto map_ende;
        default:
            {
            OP c = callocobject();
            *c = *b; C_O_K(b,EMPTY);
            erg = mult(a,c,b);
            if (erg == ERROR) {
                printobjectkind(c);
                error("mult_apply_polynom:wrong second type");
                }
            freeall(c); 
            goto map_ende;
            }
        }
map_ende:
    ENDR("mult_apply_polynom");
}



INT mult_apply_polynom_polynom(a,b) OP a,b;
/* AK 140290 V1.1 */ /* AK 170591 V1.2 */ /* AK 200891 V1.3 */
{
    OP c;
    INT erg=OK;
    CTO(POLYNOM,"mult_apply_polynom_polynom(1)",a);
    CTO(POLYNOM,"mult_apply_polynom_polynom(2)",b);
    if (NULLP(b)) goto mape;
    if (NULLP(a)) {
        FREESELF(b);
        erg += init_polynom(b);
        goto mape;
        }

    if (S_PO_N(a) == NULL) /* AK 100394 */
        {
        c = b;
        while (c != NULL)
            {
            MULT_APPLY(S_PO_K(a),S_PO_K(c));
            ADD_APPLY(S_PO_S(a),S_PO_S(c)); 
            c = S_PO_N(c);
            }
        goto mape;
        }

    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += mult_polynom_polynom(a,c,b); 
    FREEALL(c);
mape:
    ENDR("mult_apply_polynom_polynom");
}
#endif /* POLYTRUE */

INT mult_apply_scalar_monom(a,b) OP a,b; 
/* AK 150290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"mult_apply_scalar_monom(2)",b);
    MULT_APPLY(a,S_MO_K(b));
    ENDR("mult_apply_scalar_monom");
}

INT mult_apply_integer_monom(a,b) OP a,b;
{
    INT erg = OK;
    CTO(INTEGER,"mult_apply_integer_monom(1)",a);
    CTO(MONOM,"mult_apply_integer_monom(2)",b);
    MULT_APPLY_INTEGER(a,S_MO_K(b));
    ENDR("mult_apply_integer_monom");
}

INT mult_apply_bruch_monom(a,b) OP a,b;
{
    INT erg = OK;
    CTO(BRUCH,"mult_apply_bruch_monom(1)",a);
    CTO(MONOM,"mult_apply_bruch_monom(2)",b);
    MULT_APPLY_BRUCH(a,S_MO_K(b));
    ENDR("mult_apply_bruch_monom");
}



#ifdef POLYTRUE
INT mult_apply_scalar_polynom(a,b) OP a,b;
/* AK 201289 V1.1 */ /* AK 200891 V1.3 */
/* AK 030498 V2.0 */
{
    OP z = b;
    INT erg = OK;
    OBJECTKIND k;
    if (NULLP(a))
        {
        k = S_O_K(b);
        erg += init(k,b);
        goto endr_ende;
        }

    FORALL(z,b,{ MULT_APPLY(a,S_MO_K(z)); });

    ENDR("mult_apply_scalar_polynom");
}

INT mult_apply_integer_polynom(a,b) OP a,b;
/* AK 291001 */
{
    INT erg = OK;
    OBJECTKIND d = S_O_K(b);
    OP z;
    CTO(INTEGER,"mult_apply_integer_polynom(1)",a);

    if (NULLP_INTEGER(a)) {
        erg += init(d,b);
        goto ende;
        }

    FORALL(z,b, {
        MULT_APPLY_INTEGER(a,S_MO_K(z));
        });

ende:
    CTO(d,"mult_apply_integer_polynom(e2)",b);
    ENDR("mult_apply_integer_polynom");
}

INT mult_apply_longint_polynom(a,b) OP a,b;
/* AK 291001 */
{
    INT erg = OK;
    OBJECTKIND d = S_O_K(b);
    OP z;
    CTO(LONGINT,"mult_apply_longint_polynom(1)",a);
 
    if (NULLP_LONGINT(a)) {
        erg += init(d,b);
        goto endr_ende;
        }
    if (S_L_S(b) == NULL) goto endr_ende;
    z = b;
    while (z != NULL)
        {
        MULT_APPLY_LONGINT(a,S_PO_K(z));
        z = S_L_N(z);
        }
 
    ENDR("mult_apply_longint_polynom");
}

INT mult_apply_bruch_polynom(a,b) OP a,b;
/* AK 291001 */
/* AK 090805 */
{
    INT erg = OK;
    OBJECTKIND d = S_O_K(b);
    OP z;
    CTO(BRUCH,"mult_apply_bruch_polynom(1)",a);
 
    if (NULLP_BRUCH(a)) {
        erg += init(d,b);
        goto endr_ende;
        }
    if (S_L_S(b) == NULL) goto endr_ende;
    z = b;
    while (z != NULL)
        {
        MULT_APPLY_BRUCH(a,S_PO_K(z));
        z = S_L_N(z);
        }
 
    ENDR("mult_apply_bruch_polynom");
}

INT mod_monom(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(MONOM,"mod_monom(1)",a);
    CTTO(INTEGER,LONGINT,"mod_monom(2)",b);
    CE3(a,b,c,mod_monom);
    b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),c);
    erg += mod(S_MO_K(a),b,S_MO_K(c));
    COPY(S_MO_S(a),S_MO_S(c));
    ENDR("mod_monom");
}

INT mod_polynom(a,b,c) OP a,b,c;
/* AK 230703 */
/* AK c = a mod b */
/* scalar operation */
{
    INT erg = OK;
    CTO(POLYNOM,"mod_polynom(1)",a);
    CTTO(INTEGER,LONGINT,"mod_polynom(2)",b);
    CE3(a,b,c,mod_polynom);
    {
    OP z,y; INT t=0;
    /* z over a, y over c */
    init_polynom(c);
    if (S_L_S(a) == NULL) goto endr_ende;

    y = c;z=a;
    while (z!=NULL) {
        OP e;
        e = CALLOCOBJECT();
        erg +=mod_monom(S_L_S(z),b,e);
        if (NULLP(S_MO_K(e))) FREEALL(e);
        else {
            if (t==0) { C_L_S(y,e); t=1; }
            else { 
                OP f;
                f = CALLOCOBJECT();
                erg +=b_sn_po(e,NULL,f);
                C_L_N(y,f);y = S_L_N(y);
                }
            }
        z=S_PO_N(z);
        }
    }
    ENDR("mod_polynom");
}





INT scan_polynom(poly) OP poly;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
/* AK 201093: with add_apply */
{
    char antwort[2];
    INT erg = OK;
    OP d;
    CTO(EMPTY,"scan_polynom(1)",poly);

    erg += 
    printeingabe("input of a POLYNOM object as a sum of MONOM objects");
    erg += init(POLYNOM,poly);
    d = callocobject();
spa:
    erg += b_sn_l(callocobject(),NULL,d);
    C_O_K(d,POLYNOM);
    erg += scan(MONOM,S_L_S(d));
    erg += add_apply(d,poly);
spe:
    erg += printeingabe("one more monom  y/n");
    skip_comment(); /* AK 210395 */
    scanf("%s",antwort);
    if (antwort[0]  == 'y')
        goto spa;
    if (antwort[0]  == 'j')
        goto spa;
    if (antwort[0]  != 'n')
        goto spe;
    erg += freeall(d);
    ENDR("scan_polynom");
}



INT scan_fastpolynom(poly) OP poly;
/* AK 211093 */
{
    char antwort[2];
    INT erg = OK;
    OBJECTKIND kind;
    OP d;
    CTO(EMPTY,"scan_fastpolynom(1)",poly);

    erg += 
    printeingabe("input of a POLYNOM object as a sum of MONOM objects");
    printeingabe("what kind of coefficent");
    kind = scanobjectkind();
    erg += init(POLYNOM,poly);
    d = callocobject();
spa:
    erg += b_skn_po(callocobject(),callocobject(),NULL,d);
    printeingabe("enter the exponent vector of the polynom");
    erg += scan(INTEGERVECTOR,S_PO_S(d));
    printeingabe("enter the coefficent of the polynom");
    scan(kind,S_PO_K(d));
    erg += add_apply(d,poly);
spe:
    erg += printeingabe("one more monom  y/n");
    skip_comment(); /* AK 210395 */
    scanf("%s",antwort);
    if (antwort[0]  == 'y')
        goto spa;
    if (antwort[0]  == 'j')
        goto spa;
    if (antwort[0]  != 'n')
        goto spe;
    erg += freeall(d);
    ENDR("scan_fastpolynom");
}
#endif /* POLYTRUE */


#ifdef MONOMTRUE
INT add_monom(a,b,c) OP a,b,c;
/* AK 201289 V1.1 */ /* AK 050891 V1.3 */
{
    INT erg = OK;
    OP h;
    CTO(MONOM,"add_monom(1)",a);
    CTO(EMPTY,"add_monom(3)",c);

    switch (S_O_K(b)) {

#ifdef HOMSYMTRUE
        case HOM_SYM: erg += add_monom_homsym(a,b,c);break;
#endif /* HOMSYMTRUE */

#ifdef SCHURTRUE
        case SCHUR: erg += add_monom_schur(a,b,c);break;
#endif /* SCHURTRUE */

        case MONOM: 
            erg += m_sn_l(a,NULL,c);
            C_O_K(c,POLYNOM);
            ADD_APPLY(b,c);
            break;

        case POLYNOM:
            h = callocobject();
            erg += m_sn_l(a,NULL,h);
            C_O_K(h,POLYNOM);
            erg += add_polynom_polynom(h,b,c);
            FREEALL(h);
            break;

        default: 
            WTO("add_monom(2)",b);
        }
    ENDR("add_monom");
}
#endif /* MONOMTRUE */

#ifdef SCHURTRUE
INT add_monom_schur(a,b,d) OP a,b,d;
/* for all partition typ polynomials */
/* AK 201289 V1.1 */ /* AK 050891 V1.3 */
{ 
    INT erg = OK;
    OP c;
    CTO(MONOM,"add_monom_schur(1)",a);

    c = callocobject(); 
    erg += init(S_O_K(b),c);
    erg += copy_monom(a,S_L_S(c)); 
    erg += add(c,b,d);
    erg += freeall(c);
    ENDR("add_monom_schur");
}
#endif /* SCHURTRUE */

#ifdef MONOMTRUE
INT add_koeff(a,b) OP a,b;
/* eqhandle bei insert bei polynomen, monopoly
addiert die beiden koeffizienten der monome a und b
nach dem monom b */
/* wenn das ergebnis 0 ist wird das ergebnis geloescht */

/* AK 100789 V1.0 */ /* AK 231189 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(MONOM,"add_koeff",a);
    CTO(MONOM,"add_koeff",b);
    
    ADD_APPLY(S_MO_K(a), S_MO_K(b));
    if (NULLP(S_MO_K(b)))
        erg += freeself_monom(b);

    ENDR("add_koeff");
}
#endif    /* MONOMTRUE */

#ifdef POLYTRUE
INT add_scalar_polynom(a,b,c) OP a,b,c;
/* a scalar, b polynom, c empty */
/* AK 060891 V1.3 */
/* AK 060498 V2.0 */
{
    INT erg = OK;
    OP d;
    CTO(POLYNOM,"add_scalar_polynom",b);

    if (nullp(a))
        {
        erg += copy_polynom(b,c);
        goto endr_ende;
        }

    d = callocobject();
    erg += m_scalar_polynom(a,d);
    erg += add_polynom_polynom(d,b,c);
    erg += freeall(d);
    ENDR("add_scalar_polynom");
}

INT add_polynom(a,b,c) OP a,b,c;
/* AK 110789 V1.0 */ /* AK 191289 V1.1 */ /* AK 290591 V1.2 */
/* AK 060891 V1.3 */
/*CC 210595 Fuer die rationnellen Funktionen*/

{
    INT erg = OK;
    OP tp1,tp2;

    CTO(EMPTY,"add_polynom(3)",c);

    if (NULLP(a))
        {
        COPY(b,c);
        goto ende;
        }
    if (NULLP(b))
        {
        COPY(a,c);
        goto ende;
        }

    switch (S_O_K(b))
        {
        case FF: /* AK 290304 */
        case INTEGER:
        case LONGINT:
            erg += add_scalar_polynom(b,a,c); 
            goto ende; /* AK 060891 */
        case BRUCH:
            if((!scalarp(S_B_O(b)))
                   ||(!scalarp(S_B_U(b))))
                   {
                   tp1=callocobject();tp2=callocobject();
                   M_I_I(1L,tp1);m_ou_b(a,tp1,tp2);
                   copy(tp2,a);
                   freeall(tp1);freeall(tp2);
                   erg += add_bruch_bruch(a,b,c);
                   }
            else
                erg += add_scalar_polynom(b,a,c); /* AK 060891 */

            goto ende;
        case GRAL:
        case POLYNOM: 
            erg+= add_polynom_polynom(a,b,c);
            goto ende;
        case MONOPOLY: /* project to the first variable */
                       /* CC */
            erg += t_POLYNOM_MONOPOLY(a,c);
            erg += add_apply_monopoly(b,c);
           
            goto ende;
        default: 
            WTO("add_polynom(2)",b);
            goto ende;
    }
ende:
    ENDR("add_polynom");
}


INT add_polynom_polynom(a,b,c) OP a,b,c;
/* works for all types */
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 290591 V1.2 */
/* AK 050891 V1.3 */
{
    INT erg=OK;
    OP d;
    CTO(EMPTY,"add_polynom_polynom(3)",c);
    
    if (
        (not LISTP(a)) 
        ||
        (not LISTP(b)) 
       )
        erg+= WTT("add_polynom_polynom(1,2)",a,b);
    SYMCHECK(S_O_K(a) != S_O_K(b), "add_polynom_polynom:different object types");
    d = callocobject();
    erg += copy_list(a,d); 
    erg += copy_list(b,c);
    

    insert(d,c,add_koeff,comp_monomvector_monomvector);

    ENDR("add_polynom_polynom");
}

 

INT posp_polynom(a) OP a;
/* AK V2.0 221298 */
/* TRUE if all coeffs > 0 */
/* works also for other list objects */
/* false for empty list */
{
    OP z = a;
    if (S_L_S(a) == NULL) return FALSE;
    while (z != NULL)
        {
        if (not posp(S_PO_K(z)))
            return FALSE;
        z = S_PO_N(z);
        }
    return TRUE;
}



INT negp_polynom(a) OP a;
/* AK V2.0 221298 */
/* TRUE
        if all coeffs < 0 */
/* works also for other list objects */
{
    OP z = a;
    if (S_L_S(a) == NULL) return TRUE;
    while (z != NULL)
        {
        if (not negp(S_PO_K(z))) return FALSE;
        z = S_PO_N(z);
        }
    return TRUE;
}


INT comp_polynom(a,b) OP a,b;
{
    INT erg = OK;
    CTO(POLYNOM,"comp_polynom(1)",a);

    switch (S_O_K(b))
        {
        case INTEGER:
        case LONGINT:
        case BRUCH:
        case FF:
            return comp_polynom_scalar(a,b);
        case POLYNOM:
            if ( (S_L_S(a) == NULL) && (S_L_S(b) == NULL) ) return 0;
            if (S_L_S(a) == NULL)  return -1;
            if (S_L_S(b) == NULL)  return 1;
            /* return comp_list_co(a,b,comp); AK061207 *//* comp but not comp_monomvector */
            return comp_list_co(a,b,comp_monomvector_monomvector);/* comp but not comp_monomvector */
        default:
            WTO("comp_polynom(2)",b);
            break;
        }
    ENDR("comp_polynom");
}

INT comp_polynom_scalar(a,b) OP a,b;
/* AK 030298 */
{
    if (not nullp(S_PO_S(a)))
        return -1;
    if (S_PO_N(a) != NULL)
        return 1;
    return comp(S_PO_K(a),b);
}

#define COMP_MONOMSF(a,b)\
    if (S_PA_LI(S_MO_S(a)) == S_PA_LI(S_MO_S(b)))\
         {\
         INT i,l=S_PA_LI(S_MO_S(b)); OP ap,bp;\
         if (S_PA_LI(S_MO_S(a)) == 0) return 0;\
         ap = S_V_S  (S_PA_S( S_MO_S(a) ));\
         bp =  S_V_S  (S_PA_S( S_MO_S(b) ));\
         for (i=0;i<l;i++,ap++,bp++)\
             if (S_I_I(ap) - S_I_I(bp)) return S_I_I(ap) - S_I_I(bp);\
         return 0;\
         }\
    else if (S_PA_LI(S_MO_S(a)) == 0) return -1;\
    else if (S_PA_LI(S_MO_S(b)) == 0) return 1;\
    else if ( S_PA_LI(S_MO_S(a)) > S_PA_LI(S_MO_S(b)) )\
         {\
         INT i,l=S_PA_LI(S_MO_S(b)); OP ap,bp;\
         ap = S_V_S  (S_PA_S( S_MO_S(a) ));\
         bp =  S_V_S  (S_PA_S( S_MO_S(b) ));\
         for (i=0;i<l;i++,ap++,bp++)\
             if (S_I_I(ap) - S_I_I(bp)) return S_I_I(ap) - S_I_I(bp);\
         return 1;\
         }\
    else {\
         INT i,l=S_PA_LI(S_MO_S(a)); OP ap,bp;\
         ap = S_V_S  (S_PA_S( S_MO_S(a) ));\
         bp =  S_V_S  (S_PA_S( S_MO_S(b) ));\
         for (i=0;i<l;i++,ap++,bp++)\
             if (S_I_I(ap) - S_I_I(bp)) return S_I_I(ap) - S_I_I(bp);\
         return -1;\
         }
        

INT comp_monompowsym(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"comp_monompowsym",a);
    CTO(MONOM,"comp_monompowsym",b);
    CTO(PARTITION,"comp_monompowsym",S_MO_S(a));
    CTO(PARTITION,"comp_monompowsym",S_MO_S(b));
    COMP_MONOMSF(a,b);
    ENDR("comp_monompowsym");
}

INT comp_monomschur(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"comp_monomschur(1)",a);
    CTO(MONOM,"comp_monomschur(2)",b);
    CTO(PARTITION,"comp_monomschur(1)",S_MO_S(a));
    CTO(PARTITION,"comp_monomschur(2)",S_MO_S(b));
    COMP_MONOMSF(a,b);
    ENDR("comp_monomschur");
}

INT eq_monomsymfunc(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"eq_monomsymfunc(1)",a);
    CTO(MONOM,"eq_monomsymfunc(2)",b);
    CTO(PARTITION,"eq_monomsymfunc(1)",S_MO_S(a));
    CTO(PARTITION,"eq_monomsymfunc(2)",S_MO_S(b));
    return eq_partition_partition(S_MO_S(a),S_MO_S(b));
    ENDR("eq_monomsymfunc");
}

INT eq_monomsymfunchash(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"eq_monomsymfunchash(1)",a);
    CTO(MONOM,"eq_monomsymfunchash(2)",b);
    CTO(PARTITION,"eq_monomsymfunchash(1)",S_MO_S(a));
    CTO(PARTITION,"eq_monomsymfunchash(2)",S_MO_S(b));
    return S_PA_HASH(S_MO_S(a)) == S_PA_HASH(S_MO_S(b)) ;
    ENDR("eq_monomsymfunchash");
}



INT comp_monomhomsym(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"comp_monomhomsym",a);
    CTO(MONOM,"comp_monomhomsym",b);
    CTO(PARTITION,"comp_monomhomsym",S_MO_S(a));
    CTO(PARTITION,"comp_monomhomsym",S_MO_S(b));
    COMP_MONOMSF(a,b);
    ENDR("comp_monomhomsym");
}
INT comp_monommonomial(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"comp_monommonomial",a);
    CTO(MONOM,"comp_monommonomial",b);
    CTO(PARTITION,"comp_monommonomial",S_MO_S(a));
    CTO(PARTITION,"comp_monommonomial",S_MO_S(b));
    COMP_MONOMSF(a,b);
    ENDR("comp_monommonomial");
}
INT comp_monomelmsym(a,b) OP a,b;
{
    INT erg = OK;
    CTO(MONOM,"comp_monomelmsym",a);
    CTO(MONOM,"comp_monomelmsym",b);
    CTO(PARTITION,"comp_monomelmsym",S_MO_S(a));
    CTO(PARTITION,"comp_monomelmsym",S_MO_S(b));
    COMP_MONOMSF(a,b);
    ENDR("comp_monomelmsym");
}

INT comp_monomvector_monomvector(a,b) OP a,b;
/* vergleicht zwei monome von vectorform */
/* wenn keine vectorform dann der normale vergleich */
/* AK 100789 V1.0 */ /* AK 081289 V1.1 */ /* vergleich bei polynomen */
/* AK 120391 V1.2 */ /* AK 200891 V1.3 */
{
    INT i,j,erg=OK;
    OP as,bs;



    CTO(MONOM,"comp_monomvector_monomvector",a);
    CTO(MONOM,"comp_monomvector_monomvector",b);
        
    as = S_MO_S(a); 
    bs = S_MO_S(b);

    if (    (S_O_K(as) == PARTITION)
        &&
       (S_O_K(bs)==PARTITION) )
       {
       return comp_partition(as,bs);
       }

    if (    (S_O_K(as) == PERMUTATION)
        &&
        (S_O_K(bs)==PERMUTATION)        )
        /* AK 210690 if schubert polynom */
        /*           or gral */
        {
        erg=1L;
        if (S_P_LI(bs) > S_P_LI(as)) {
            a=bs;
            bs=as;
            as=a;
            erg= -1L;
        }
        /* as ist laenger als bs */
        for (i=(INT)0; i<S_P_LI(as); i++)
            {
            if (i < S_P_LI(bs))
                {
                if (S_P_II(as,i) > S_P_II(bs,i)) return erg*1L;
                if (S_P_II(as,i) < S_P_II(bs,i)) return erg*-1L;
                }
            else {
                if (S_P_II(as,i) < i+1L) return erg*-1L;
                if (S_P_II(as,i) > i+1L) return erg*1L;
                }
            }
        return (INT)0;
        }
    if (    (S_O_K(as) == MATRIX)
        &&
        (S_O_K(bs)==MATRIX)        )
        {
        INT h,l;
        h = (S_M_HI(as) > S_M_HI(bs) ? S_M_HI(as) : S_M_HI(bs));
        l = (S_M_LI(as) > S_M_LI(bs) ? S_M_LI(as) : S_M_LI(bs));
        for (i=(INT)0; i<h; i++)
        for (j=(INT)0; j<l; j++)
            {
            if (
                ( i<S_M_HI(as) )  &&
                ( i<S_M_HI(bs) )  &&
                ( j<S_M_LI(as) )  &&
                ( j<S_M_LI(bs) ) 
               ) 
                if ((erg = COMP(S_M_IJ(as,i,j),S_M_IJ(bs,i,j)))
                    != (INT)0) return erg;
            if (
                ( i>=S_M_HI(as) )  &&
                ( j<S_M_LI(bs) )
               )
                if (not NULLP(S_M_IJ(bs,i,j)))
                    return -1L;
            if (
                ( i>=S_M_HI(bs) )  &&
                ( j<S_M_LI(as) )
               )
                if (not NULLP(S_M_IJ(as,i,j)))
                    return 1L;
            if (
                ( i<S_M_HI(as) )  &&
                ( j>=S_M_LI(bs) )
               )
                if (not NULLP(S_M_IJ(as,i,j)))
                    return 1L;
            if (
                ( i<S_M_HI(bs) )  &&
                ( j>=S_M_LI(as) )
               )
                if (not NULLP(S_M_IJ(bs,i,j)))
                    return -1L;
            }
        return (INT)0;
        }
    if (
        ((S_O_K(as) != VECTOR)&&(S_O_K(as) != INTEGERVECTOR))
        || 
        ((S_O_K(bs) != VECTOR)&&(S_O_K(bs) != INTEGERVECTOR))
        )
            return COMP(as,bs);


    for (i=(INT)0;i<S_V_LI(as);i++)
        {
        if (S_O_K(S_V_I(as,i)) != INTEGER)
        {
        if (S_O_K(S_V_I(as,i)) == LONGINT) {
            C_O_K(as,VECTOR);
            goto ccc;
            }
        fprintln(stderr,as);
        error("comp_monomvector_monomvector:as no INTEGERVECTOR");
        }
        else if (i >= S_V_LI(bs))
            {
            if (S_V_II(as,i) != (INT)0)
                return 1L; 
            }
        else if (S_O_K(S_V_I(bs,i)) != INTEGER)
        {
        if (S_O_K(S_V_I(bs,i)) == LONGINT) {
            C_O_K(bs,VECTOR);
            goto ccc;
            }
        fprintln(stderr,bs);
        error("comp_monomvector_monomvector:bs no INTEGERVECTOR");
        }
        else if ( S_V_II(as,i) > S_V_II(bs,i) )
            return 1L;
        else if ( S_V_II(as,i) < S_V_II(bs,i) )
            return -1L;
        }

    for (j=i;j<S_V_LI(bs);j++)
        {
        /* if (S_O_K(S_V_I(bs,i)) != INTEGER)  error AK 311091 */
        if (S_O_K(S_V_I(bs,j)) != INTEGER) 
        {
        if (S_O_K(S_V_I(bs,j)) == LONGINT) 
            {
            C_O_K(bs,VECTOR);
            goto ccc;
            }
        fprintln(stderr,bs);
        error("comp_monomvector_monomvector:bs no INTEGERVECTOR");
        }
        /* else if (S_V_II(bs,i) != (INT)0 )  error AK 311091 */
        else if (S_V_II(bs,j) != (INT)0 ) 
                        return -1L; 
        }


    return (INT)0;
ccc: /* AK 300195 */ /* vergleich mit longint -- slow */
    for (i=(INT)0;i<S_V_LI(as);i++)
        {
        if (i >= S_V_LI(bs))
            {
            if (not nullp(S_V_I(as,i)))
                return 1L; 
            }
        else if ( gt(S_V_I(as,i),S_V_I(bs,i)) )
            return 1L;
        else if ( lt(S_V_I(as,i),S_V_I(bs,i)) )
            return -1L;
        }

    for (j=i;j<S_V_LI(bs);j++)
        {
        if (not nullp(S_V_I(bs,j)))
                        return -1L; 
        }
    return (INT)0;
    ENDR("comp_monomvector_monomvector");
}
#endif /* POLYTRUE */


#ifdef MONOMTRUE
INT addinvers_monom(a,b) OP a,b;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg=OK;
    CTO(MONOM,"addinvers_monom(1)",a);
    CTO(EMPTY,"addinvers_monom(2)",b);
    B_SK_MO(callocobject(),callocobject(),b);
    COPY(S_MO_S(a),S_MO_S(b));
    ADDINVERS(S_MO_K(a),S_MO_K(b));
    ENDR("addinvers_monom");
}

INT addinvers_apply_monom(a) OP a;
/* AK 201289 V1.1 */ /* AK 200891 V1.3 */
{ 
    INT erg = OK;
    CTO(MONOM,"addinvers_apply_monom(1)",a);
    ADDINVERS_APPLY(S_MO_K(a)); 
    ENDR("addinvers_apply_monom");
}
#endif /* MONOMTRUE */

#ifdef POLYTRUE
INT addinvers_polynom(a,b) OP a,b;
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    return(transformlist(a,b,addinvers)); 
}

INT addinvers_apply_polynom(a) OP a;
/* AK 201289 V1.1 */ /* AK 200891 V1.3 */
{ 
    INT erg = OK;
    OP z;
    CTTO(HASHTABLE,POLYNOM,"addinvers_apply_polynom(1)",a);

    FORALL(z,a, {
        ADDINVERS_APPLY(S_MO_K(z));
        });
 
    ENDR("addinvers_apply_polynom");
}

INT m_skn_po(a,b,c,d) OP a,b,c,d;
/* make_self.koeff.next_polynom */
/* AK 290590 V1.1 */ /* AK 200891 V1.3 */
{
    OP s=NULL,k=NULL,n=NULL;
    INT erg = OK;
    COP("m_skn_po(4)",d);
    if (c != NULL) { 
        n = CALLOCOBJECT(); 
        erg += copy(c,n); 
        }
    if (a != NULL) { 
        s = CALLOCOBJECT(); 
        erg += copy(a,s); 
        }
    if (b != NULL) { 
        k = CALLOCOBJECT(); 
        erg += copy(b,k); 
        }
    erg += b_skn_po(s,k,n,d);
    ENDR("m_skn_po");
}

INT b_skn_po(a,b,c,d) OP a,b,c,d;
/* AK 100789 V1.0 */ /* AK 241189 V1.1 */ /* AK 130891 V1.3 */
{
    INT erg = OK;
    COP("b_skn_po(4)",d);
    erg += b_sn_l(CALLOCOBJECT(),c,d); 
    C_O_K(d,POLYNOM);
    B_SK_MO(a,b,S_L_S(d)); 
    ENDR("b_skn_po");
}


OP s_po_s(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    if (a == NULL) return  
        error("s_po_s: a == NULL"),(OP)NULL;
    if (s_o_k(a) != POLYNOM) return  
        error("s_po_s: not POLYNOM"),(OP)NULL;
    return(s_mo_s(s_l_s(a))); 
}

OP s_po_k(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    if (a == NULL) return  
        error("s_po_k: a == NULL"),(OP)NULL;
    if (s_o_k(a) != POLYNOM) return  
        error("s_po_k: not POLYNOM"),(OP)NULL;
    return s_mo_k(s_l_s(a));
}

OP s_po_n(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    if (a == NULL) return  
        error("s_po_n: a == NULL"),(OP)NULL;
    if (s_o_k(a) != POLYNOM) return  
        error("s_po_n: not POLYNOM"),(OP)NULL;
    return s_l_n(a); 
}

OP s_po_si(a,i) OP a; INT i; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    if (a == NULL) return  
        error("s_po_si: a == NULL"),(OP)NULL;
    if (s_o_k(a) != POLYNOM) return  
        error("s_po_si: not POLYNOM"),(OP)NULL;
    return s_v_i(s_mo_s(s_l_s(a)),i); 
}

OP s_po_sl(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    if (a == NULL) return  
        error("s_po_sl: a == NULL"),(OP)NULL;
    if (s_o_k(a) != POLYNOM) return  
        error("s_po_sl: not POLYNOM"),(OP)NULL;
    return s_v_l(s_mo_s(s_l_s(a))); 
}

INT s_po_ki(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    return(s_mo_ki(s_l_s(a))); 
}

INT s_po_sii(a,i) OP a; INT i; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    return(s_v_ii(s_mo_s(s_l_s(a)),i)); 
}


INT s_po_sli(a) OP a; 
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{ 
    return(s_v_li(s_mo_s(s_l_s(a)))); 
}



INT test_poly()
/* AK 191289 V1.1 */ /* AK 190291 V1.2 */ /* AK 200891 V1.3 */
{
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();

    printf("test_poly:scan(a)"); 
    scan(POLYNOM,a);
    println(a);
    printf("test_poly:copy(a,b)"); 
    copy(a,b); 
    println(b);
    printf("test_poly:mult(a,b,b)"); 
    mult(a,b,b); 
    println(b);
    printf("test_poly:tex(b)"); 
    tex(b); 
    printf("test_poly:add(b,a,a)"); 
    add(b,a,a); 
    println(a);
    printf("test_poly:hoch(b,2L,a)"); 
    hoch(b,cons_zwei,a); 
    println(a);
    printf("test_poly:eval_polynom(a,b,c)");
    m_il_v(2L,b); 
    M_I_I(3L,s_v_i(b,(INT)0)); 
    M_I_I(5L,s_v_i(b,1L));
    printf("b=");
    println(b);
    eval_polynom(a,b,c); 
    println(c);
    printf("test_poly:vander(4L,c)"); 
    M_I_I(4L,b);
    vander(b,c);
    println(c);
    printf("test_poly:numberofvariables(c,b)"); 
    numberofvariables(c,b); 
    println(b);

#ifdef BRUCHTRUE
    freeself(a); freeself(b); freeself(c);
    printf("test_poly:lagrange_polynom([1,7],[5,7],c)"); 
    m_il_v(2L,a);
    m_i_i(1L, s_v_i(a,(INT)0));
    m_i_i(7L, s_v_i(a,1L));

    m_il_v(2L,b);
    m_i_i(5L, s_v_i(b,(INT)0));
    m_i_i(7L, s_v_i(b,1L));

    lagrange_polynom(a,b,c);println(c);
#endif /* BRUCHTRUE */
    printf("test_poly:mult_disjunkt_polynom_polynom(c,c,a)"); 
    mult_disjunkt_polynom_polynom(c,c,a); 
    println(a);


    m_i_i(1L,a); 
    m_scalar_polynom(a,b); 
    if (not einsp(b)) 
        printf("test_poly:ERROR!!:einsp test not successful\n");
    else
        printf("test_poly:einsp test successful\n");

    m_i_i((INT)0,a); 
    m_scalar_polynom(a,b); 
    if (not nullp(b)) 
        printf("test_poly:ERROR!!:nullp test not successful\n");
    else
        printf("test_poly:nullp test successful\n");

    freeall(a);
    freeall(b);
    freeall(c);
    return(OK);
}



INT tex_polynom(poly) OP poly;
/* AK 101187 */ /* zur TeXausgabe eines polynoms */
/* AK 100789 V1.0 */ /* AK 191289 V1.1 */
/* AK 070291 V1.2 tex to texout */ /* AK 200891 V1.3 */
{
    OP zeiger = poly;
    OP z;
    INT i,j;
    INT hbool=1L;
    INT ts = texmath_yn; /* AK 260892 */

    if (ts == (INT)0) 
        {
        texmath_yn = 1L;
        fprintf(texout,"\\ $ ");
        }
    else
        fprintf(texout,"\\ ");
    texposition += 3L;
    if (EMPTYP(poly)) 
        return(OK);
    while (zeiger != NULL)
    {
        hbool = 1L;
        if (not einsp(S_PO_K(zeiger))) 
            {
            if (negeinsp(S_PO_K(zeiger))) /* AK 100892 */
            {
            fprintf(texout," - "); 
            texposition += 3L; 
            }
            else
                {
                if (POLYNOMP(S_PO_K(zeiger)))
                    fprintf(texout,"(");
                if (negp(S_PO_K(zeiger)))
                    {
                    fprintf(texout," - "); 
                    addinvers_apply(S_PO_K(zeiger));
                    tex(S_PO_K(zeiger)); 
                    addinvers_apply(S_PO_K(zeiger));
                    }
                else
                    tex(S_PO_K(zeiger)); 
                hbool=(INT)0; 
                if (POLYNOMP(S_PO_K(zeiger)))
                    fprintf(texout,")");
                }
            }
        /* der koeffizient wird nur geschrieben wenn er ungleich 1 ist*/
        fprintf(texout,"\\ ");
        texposition += 3L;
        if (S_O_K(S_PO_S(zeiger)) == MATRIX) /* AK 031291 */
            {
            z = S_PO_S(zeiger);
            for (i=(INT)0;i<S_M_HI(z);i++)
            for (j=(INT)0;j<S_M_LI(z);j++)
                if (S_M_IJI(z,i,j) >(INT)0)
                {
                hbool=(INT)0;
                if (S_M_IJI(z,i,j) >1L)
                    fprintf(texout," x_{%ld,%ld}^{%ld} ",
                        i,j,S_M_IJI(z,i,j));
                else 
                    fprintf(texout," x_{%ld,%ld} ", i,j);
                texposition += 15L;
                }
            }
        else     {
        for (i= (INT)0 ;i < S_PO_SLI(zeiger); i++)
            if (S_PO_SII(zeiger,i) > (INT)0)
            {
                hbool=(INT)0;
                if (tex_poly_var == NUMERICAL) /* AK 090395 */
            fprintf(texout,"x_{%ld}",i+tex_poly_first_var_index);
                else
            fprintf(texout,"%c",(char)( 'a'+i+tex_poly_first_var_index));
                texposition ++;
                if (S_PO_SII(zeiger,i) != 1L)
                {
                    fprintf(texout,"^{%ld}",S_PO_SII(zeiger,i));
                    texposition += 10L;
                };
            };
            }
        if (hbool == 1L) 
            fprintf(texout,"1");
        fprintf(texout,"\\ ");
        texposition += 3L;
        if (texposition > tex_row_length)
        { 
            fprintf(texout,"\n");
            texposition = (INT)0; 
        }

        zeiger = S_PO_N(zeiger);
        if (zeiger != NULL)
        if (not negp(S_PO_K(zeiger))) /* AK 100892 */
        { 
            fprintf(texout," + "); 
            texposition += 5L; 
        }
    };
    if (ts == (INT)0)
        {
        fprintf(texout,"$ \\ ");
        texmath_yn = (INT)0;
        }
    else 
        fprintf(texout,"\\ ");
    texposition += 2L;
    return(OK);
}



INT copy_polynom(a,b) OP a,b; 
/* AK 091190 V1.1 */ /* AK 190291 V1.2 */ /* AK 200891 V1.3 */
    {
    return(copy_list(a,b));
    }



INT add_apply_polynom_polynom(a,b) OP a,b;
/* AK 091190 V1.1 */ /* AK 190291 V1.2 */ /* AK 200891 V1.3 */
    {
    INT erg = OK;
    OP c;
    CTO(POLYNOM,"add_apply_polynom_polynom(1)",a);
    CTO(POLYNOM,"add_apply_polynom_polynom(2)",b);
    c = callocobject();
    erg += copy_polynom(a,c);
    insert(c,b,add_koeff,comp_monomvector_monomvector);
    ENDR("add_apply_polynom_polynom");
    }


INT add_apply_polynom_scalar(a,b) OP a,b;
/* AK 130891 V1.3 */
{
    OP c;
    INT erg = OK;
    CTO(POLYNOM,"add_apply_polynom_scalar(1)",a);
#ifdef UNDEF /* 170304 removed */
    c = callocobject();
    erg += copy(a,c);
    erg += add(b,c,b); /* error AK 211194 */
    erg += freeall(c);
#endif
    c = callocobject();
    erg += m_scalar_polynom(b,c);
    erg += add(a,c,b);
    erg += freeall(c);
    ENDR("add_apply_polynom_scalar");
}

INT add_apply_polynom(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 190291 V1.2 */
/* AK 130891 V1.3 */
/* AK 030498 V2.0 */
{
    INT erg = OK;
    OP d;
    CTO(POLYNOM,"add_apply_polynom",a);
    if ((EMPTYP(b)) 
        ||  nullp(b) )
        {
        erg += copy_polynom(a,b);
        goto endr_ende;
        }
    switch(S_O_K(b)) {
        case BRUCH:
        case FF:
        case LONGINT:
        case CYCLOTOMIC:
        case SQ_RADICAL:
        case INTEGER: 
            erg += add_apply_polynom_scalar(a,b);break;
        case MONOPOLY: 
            d=callocobject();
            erg += t_POLYNOM_MONOPOLY(a,d);
            erg += add_apply_monopoly(d,b);
            erg += freeall(d);
            break;


        case POLYNOM:  erg += add_apply_polynom_polynom(a,b);break;
#ifdef SCHUBERTTRUE
        case SCHUBERT:  erg += add_apply_polynom_schubert(a,b);break;
#endif /* SCHUBERTTRUE */
        default:
            WTO("add_apply_polynom(2)",b);
            goto endr_ende;
        }
    ENDR("add_apply_polynom");
}
#endif /* POLYTRUE */

#ifdef SCHUBERTTRUE
INT add_apply_polynom_schubert(a,b) OP a,b;
/* AK 190291 V1.2 */ /* AK 200891 V1.3 */
{
    OP c;
    INT erg = OK;
    CTO(POLYNOM,"add_apply_polynom_schubert(1)",a);
    CTO(SCHUBERT,"add_apply_polynom_schubert(2)",b);

    c = callocobject();
    erg += t_POLYNOM_SCHUBERT(a,c);
    erg += add_apply(c,b);
    erg += freeall(c);
    ENDR("add_apply_polynom_schubert");
}

INT gauss_schubert_polynom(a,b,c) OP a,b,c;
/* AK 040190 gausspolynom [a+b \atop b] */
/* mittels schubertpolynome */
/* AK 040190 V1.1 */ /* AK 200891 V1.3 */
/* AK 280199 V2.0 */
/* a,b,c may be equal */
{
    INT i,m;
    OP  vec,perm;
    INT erg = OK;
    CTO(INTEGER,"gauss_schubert_polynom",a);
    CTO(INTEGER,"gauss_schubert_polynom",b);

    vec = callocobject();
    perm = callocobject();

    erg += m_il_v(S_I_I(a)+S_I_I(b)+1L,vec);
    for (i=(INT)0,m=(INT)0;i<S_I_I(b);i++,m++)
        M_I_I((INT)0,S_V_I(vec,m));
    M_I_I(S_I_I(a),S_V_I(vec,m)); m++;
    for (i=(INT)0;i<S_I_I(a);i++,m++)
        M_I_I((INT)0,S_V_I(vec,m));
    /* dies ist der lehmercode */
    erg += lehmercode_vector(vec,perm);
    erg += m_perm_schubert_qpolynom(perm,c);
    FREEALL2(perm,vec);
    ENDR("gauss_schubert_polynom");
}
#endif /* SCHUBERTTRUE */

#ifdef POLYTRUE
INT polya_sub(a,c,b) OP a,b,c;
/* einsetzung */ /* a ist polynom */ /* c ist length of alphabet */
/* b wird ergebnis x_i ----> 1 + q^i */
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */
{
    OP d,e,f;
    OP z;
    INT i;
    INT erg = OK;
    CTO(POLYNOM,"polya_sub(1)",a);
    CTO(INTEGER,"polya_sub(2)",c);

    e=CALLOCOBJECT();
    erg += b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,e);
    erg += m_il_nv(1L,S_PO_S(e));
    M_I_I(1,S_PO_K(e));

    f=CALLOCOBJECT(); COPY(e,f); 
    M_I_I(1L,S_PO_SI(f,0L));
    erg += insert(f,e,add_koeff,comp_monomvector_monomvector);

    d=CALLOCOBJECT(); erg += m_il_v(S_I_I(c),d);
    for (i=0L;i<S_V_LI(d);i++)
        {
        COPY(e,S_V_I(d,i));
        z = S_V_I(d,i);
        while (z != NULL)
            {
            M_I_I(S_PO_SII(z,0L)*(i+1),S_PO_SI(z,0));
            z = S_L_N(z);
            }
        }
    erg += eval_polynom(a,d,b); 
    FREEALL2(d,e);
    ENDR("polya_sub");
}
#endif /* POLYTRUE */

INT unimodalp(a) OP a;
/* AK 080190 */ /* AK 091190 V1.1 */ /* AK 200891 V1.3 */
{
    OP z,k;
    if (EMPTYP(a)) return(FALSE);
    if (S_O_K(a) != POLYNOM) return(FALSE);
    z = S_PO_N(a);
    k = S_PO_K(a);
    while (z != NULL)
        {
        if (lt(S_PO_K(z),k)) break;
        k = S_PO_K(z);
        z = S_PO_N(z);
        }
    if (z == NULL) return(TRUE);
    k = S_PO_K(z);
    z = S_PO_N(z);
    while (z != NULL)
        {
        if (gr(S_PO_K(z),k)) return(FALSE);
        k = S_PO_K(z);
        z = S_PO_N(z);
        }
    return(TRUE);
}

INT degree_polynom(a,b) OP a,b;
/* b becomes the degree, but only if in one variable */
/* AK 300590 V1.1 */ /* AK 190291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z,za=NULL;
    INT erg = OK;
    CTO(POLYNOM,"degree_polynom(1)",a);
    CTO(EMPTY,"degree_polynom(2)",b);
    
   
    z = a;
    while (z != NULL)
        {
        za = z;
        if( (S_O_K(S_PO_S(z)) != VECTOR) &&
            (S_O_K(S_PO_S(z)) != INTEGERVECTOR))         /*CC*/
                {
                        printobjectkind(S_PO_S(z));
                        return error("degree_polynom: not VECTOR");
                }

        if (S_PO_SLI(z) != 1L) 
        return error("degree_polynom: not single variable");
        z = S_PO_N(z);
        }
    /* za has now maximal degree */
    COPY(S_PO_SI(za,0L),b);
    ENDR("degree_polynom");
}

#ifdef POLYTRUE
INT lagrange_polynom(a,b,c) OP a,b,c;
/* a sind die stuetzpunkte VECTOR
   b die werte VECTOR
   c wird das polynom */
/* AK 060690 V1.1 */ /* AK 200891 V1.3 */
{
    INT i,j,erg=OK;
    OP zw,h;

    CTO(VECTOR,"lagrange_polynom(1)",a);
    CTO(VECTOR,"lagrange_polynom(2)",b);
    SYMCHECK(S_V_LI(a) != S_V_LI(b),
             "lagrange_polynom: different vector length");
    CE3(a,b,c,lagrange_polynom);
        
    zw = CALLOCOBJECT();
    h = CALLOCOBJECT();
    for (i=0L; i< S_V_LI(a) ; i++ )
        {
        COPY (S_V_I(b,i), zw);
        for (j = 0L; j < S_V_LI(a); j++)
            if (i != j) {
                erg += sub(S_V_I(a,i),S_V_I(a,j),h);
                erg += div(zw,h,zw); 
                FREESELF(h);
                erg += b_skn_po(
                CALLOCOBJECT(),CALLOCOBJECT(),CALLOCOBJECT(),h);
                erg += b_skn_po(
                CALLOCOBJECT(),CALLOCOBJECT(),NULL,S_PO_N(h));
                erg += m_il_nv(1,S_PO_S(h));
                erg += m_il_v(1,S_PO_S(S_PO_N(h)));
                M_I_I(1,S_PO_SI(S_PO_N(h),0L));
                ADDINVERS(S_V_I(a,j), S_PO_K(h));
                M_I_I(1, S_PO_K(S_PO_N(h)));
                MULT_APPLY(h,zw);
                }
        if (i == 0) SWAP(c,zw);
        else {
            ADD_APPLY(zw,c); 
            FREESELF(zw);
            }
        }
    FREEALL2(zw,h);
    ENDR("lagrange_polynom");
}



INT m_index_monom(i,res) OP i; OP res; 
/* res = x_i */
/* AK 220904 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"m_index_monom(1)",i);
    SYMCHECK(S_I_I(i)<0,"m_index_monom:negative parameter");
    {
    erg += m_iindex_monom(S_I_I(i),res);
    }
    ENDR("m_index_monom");
}

INT m_iindex_monom(i,res) INT i; OP res; 
/* res = x_i */
/* AK 200891 V1.3 */
/* AK 220904 V3.0 */
{
    INT erg = OK;
    SYMCHECK(i<0  ,"m_iindex_monom:index < 0 ");
    {
    erg += m_iindex_iexponent_monom(i,1,res);
    }
    ENDR("m_iindex_monom");
}



INT m_iindex_iexponent_monom(i,ex,res) INT i,ex; OP res;
/* AK 300588 */ 
/* AK 030789 V1.0 */ /* AK 060390 V1.1 */ /* AK 200891 V1.3 */
/* res = x_i^ex */
    {
    INT erg = OK;
    COP("m_iindex_iexponent_monom(3)",res);
    SYMCHECK(i<0  ,"m_iindex_iexponent_monom:index < 0 ");
    {
    erg += b_skn_po(callocobject(),callocobject(),NULL,res);
    erg += m_il_nv(i+1L,S_PO_S(res));
    C_O_K(S_PO_S(res),INTEGERVECTOR);
    M_I_I(1,S_PO_K(res));
    M_I_I(ex,S_PO_SI(res,i));
    }
    ENDR("m_iindex_iexponent_monom");
    }

INT nullp_polynom(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a, { if (not NULLP(S_MO_K(z)) ) return FALSE; } );
    return TRUE;
}

INT nullp_schur(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a, { if (not NULLP(S_MO_K(z)) ) return FALSE; } );
    return TRUE;
}

INT nullp_homsym(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a,
        {
        if (not NULLP(S_MO_K(z)) ) return FALSE;
        } );
    return TRUE;
}

INT nullp_powsym(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a,
        {
        if (not NULLP(S_MO_K(z)) ) return FALSE;
        } );
    return TRUE;
}

INT nullp_monomial(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a,
        {
        if (not NULLP(S_MO_K(z)) ) return FALSE;
        } );
    return TRUE;
}

INT nullp_elmsym(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z;
    FORALL(z,a,
        {
        if (not NULLP(S_MO_K(z)) ) return FALSE;
        } );
    return TRUE;
}







INT negeinsp_polynom(a) OP a;
/* AK 060502 */
{
    OP z = a;
    INT i;
    if (empty_listp(a)) return FALSE;
    if (not negeinsp(S_PO_K(z)) ) return FALSE;
    /* now check whether self == 000000 */
    for (i=(INT)0; i<S_PO_SLI(z); i++)
        if (S_PO_SII(z,i) != (INT)0) return FALSE;
    z = S_PO_N(z);
    if (z != NULL) return FALSE;
    return TRUE;
}


INT einsp_polynom(a) OP a;
/* AK 180291 V1.2 */ /* AK 200891 V1.3 */
{
    OP z = a;
    INT i;
    if (empty_listp(a)) return FALSE;
    if (not einsp(S_PO_K(z)) ) return FALSE;
    /* now check whether self == 000000 */
    for (i=(INT)0; i<S_PO_SLI(z); i++)
        if (S_PO_SII(z,i) != (INT)0) return FALSE;
    z = S_PO_N(z);
    if (z != NULL) return FALSE;
    return TRUE;
}



INT consp_polynom(a) OP a;
{
    INT i;
    OP z = a;
    if (empty_listp(a)) return FALSE;
    for (i=(INT)0; i<S_PO_SLI(z); i++)
        if (S_PO_SII(z,i) != (INT)0) return FALSE;
    z = S_PO_N(z);
    if (z != NULL) return FALSE;
    return TRUE;
}



INT m_scalar_polynom(a,b) OP a,b;
/* AK 180291 V1.2 */ /* AK 060891 V1.3 */
/* AK 271005 V3.1 */
{
    INT erg = OK;
    CE2(a,b,m_scalar_polynom);
    {
    erg += b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,b);
    COPY(a,S_PO_K(b));
    erg += m_il_v(1,S_PO_S(b));
    M_I_I(0,S_PO_SI(b,0));
    C_O_K(S_PO_S(b),INTEGERVECTOR); 
    }
    ENDR("m_scalar_polynom");
}

INT eval_char_polynom(poly,vec,res) OP poly,vec,res;
/* AK 310588 */
/* ein polynom wird ausgewertet indem der vector
vec eingesetzt wird
bsp     poly:= 2 [3,0,1]
    vec:= [4,4,5]
    res = 2 * 4^3 * 5 = 640 [0,0,0] */
/* AK 110789 V1.0 */ /* AK 191289 V1.1 */ /* AK 200891 V1.3 */
{
    OP zeiger = poly,monom,c;
    INT i;
    INT erg=OK;

    if (
        (S_O_K(vec) != VECTOR) &&
        (S_O_K(vec) != INTEGERVECTOR)
       )
    { 
        printobjectkind(vec); 
        return error("eval_char_polynom:vec != VECTOR "); 
    }

    m_i_i((INT)0,res);
    c = callocobject();
    monom = callocobject(); 

    while (zeiger != NULL)
    {
        erg += copy(S_PO_K(zeiger),monom);
        if (
            (S_O_K(S_PO_S(zeiger)) != VECTOR) &&
            (S_O_K(S_PO_S(zeiger)) != INTEGERVECTOR)
           )
        { 
            printobjectkind(S_PO_S(zeiger));
            return error("eval_char_polynom:self != VECTOR "); 
        }
        for (i=(INT)0;i<S_PO_SLI(zeiger); i++)
        {
            if (i >= S_V_LI(vec)) goto evalpoly3;
            /* i ist < S_V_LI(vec) */
            if (not EMPTYP(S_V_I(vec,i)))
            /* if (not nullp (S_PO_SI(zeiger,i))) AK 040892 */
            if (S_PO_SII(zeiger,i) != (INT)0)
                { 
                if (S_PO_SII(zeiger,i) == 1L)
                    mult_apply_integer(S_V_I(vec,i),monom); 
                else if (S_PO_SII(zeiger,i) == 2L)
                    {
                    m_i_i(S_V_II(vec,i)*S_V_II(vec,i),c);
                    mult_apply_integer(c,monom); 
                    }
                else if (S_PO_SII(zeiger,i) == 3L)
                    {
            m_i_i(S_V_II(vec,i)*S_V_II(vec,i)*S_V_II(vec,i),c);
            erg += mult_apply_integer(c,monom); 
                    }
                else if (S_PO_SII(zeiger,i) == 4L)
                    {
    m_i_i(S_V_II(vec,i)*S_V_II(vec,i)*S_V_II(vec,i)*S_V_II(vec,i),c);
    erg += mult_apply_integer(c,monom); 
                    }
                else /* AK 040892 */
                    {
                    erg += hoch(S_V_I(vec,i),S_PO_SI(zeiger,i),c);
                    erg += mult_apply(c,monom); 
                    }
                }
        };
evalpoly3:
    if ( (S_O_K(monom) == INTEGER)
        && (S_O_K(res) == INTEGER) )
        erg += add_apply_integer_integer(monom,res);
    else if (S_O_K(monom) == BRUCH)
        erg += add_apply_bruch(monom,res);
    else
        erg += add_apply(monom,res);
        zeiger = S_PO_N(zeiger);
    }
    erg += freeall(c); 
    erg += freeall(monom); 
    return erg;
}

INT m_vec_poly(a,c) OP a,c;
/* AK 090805 */
/* input vec a
   out polynom c = ... a_i x^i */
{
    INT erg = OK;
    CTO(VECTOR,"m_vec_poly(1)",a);
    CE2(a,c,m_vec_poly);
    {
    INT i;OP z,zz;
    if (i==0) init(POLYNOM,c);
    else if (NULLP(a)) init(POLYNOM,c);
    else
    {
    zz= z = c;
    for (i=0;i<S_V_LI(a);i++)
        {
        if (not NULLP(S_V_I(a,i))) {
            m_iindex_iexponent_monom(0,i,z);
            copy(S_V_I(a,i),S_PO_K(z));
            if (i+1 < S_V_LI(a)) {
                C_L_N(z,CALLOCOBJECT());
                zz = z;
                z = S_L_N(z);
                }
            }
        }
    if (EMPTYP(S_L_N(zz))) {
        FREEALL(S_L_N(zz));
        C_L_N(zz,NULL);
        }
    }
    }
    ENDR("m_vec_poly");
}

INT m_vec_vec_poly(a,b,c) OP a,b,c;
/* AK 310892 */
/* input two integer vectors a,b of same length */
/* output polynom c= ... a_i ^ b_i ... with coeff 1 */
{
    INT erg = OK;
    INT i,maxvar;
    CTO(VECTOR,"m_vec_vec_poly(1)",a);
    CTO(VECTOR,"m_vec_vec_poly(2)",b);
    SYMCHECK (S_V_LI(a) != S_V_LI(b),"m_vec_vec_poly:different lengths");

    maxvar = (INT)0;
    for (i=(INT)0;i<S_V_LI(a);i++)
        {
        if (S_O_K(S_V_I(a,i)) != INTEGER)
            return ERROR;
        if (S_O_K(S_V_I(b,i)) != INTEGER)
            return ERROR;
        if (S_V_II(b,i) < (INT)0)
            return ERROR;
        if (S_V_II(a,i) < (INT)0)
            return ERROR;
        if (S_V_II(a,i) > maxvar) 
            maxvar = S_V_II(a,i);
        }
    /* now the input is OK */
    erg += b_skn_po(callocobject(),callocobject(),NULL,c);
    erg += m_i_i(1L,S_PO_K(c));
    erg += m_il_nv(maxvar+1L,S_PO_S(c));
    for (i=(INT)0;i<S_V_LI(a);i++)
        {
        M_I_I(S_V_II(b,i)+S_PO_SII(c,S_V_II(a,i)),
            S_PO_SI(c,S_V_II(a,i)));
        }
    ENDR("m_vec_vec_poly");
}



INT is_scalar_polynom(a) OP a;
/* AK 290793 */
{
    if (scalarp(a) ) 
        return TRUE;
    if (nullp(S_PO_S(a)) && S_PO_N(a) == NULL)
        return TRUE;
    else
        return FALSE;
}




INT select_coeff_polynom(a,b,c) OP a,b,c;
/* AK 020893 */
/* c becomes the coeff of the exponent vector b in the polynomial a */
{
    OP z;
    INT erg = OK;
    if ((S_O_K(a) != POLYNOM) ||
        (S_O_K(b) != VECTOR))
            return WTT("select_coeff_polynom",a,b);

    z = a;
    while (z != NULL)
        {
        if (comp_numeric_vector(S_PO_S(z), b) == (INT)0)
            {
            erg += copy(S_PO_K(z),c);
             goto s_p_c_ende;
            }
        z = S_L_N(z);
        }
    erg += m_i_i((INT)0,c);
s_p_c_ende:
    return erg;
}



INT random_monom(a) OP a;
/* AK 180893 */
{
    OP b,c;
    INT i,erg = OK;

    b = callocobject();
    c = callocobject();
    erg += random_integer(b,cons_eins,NULL);
    erg += m_l_v(b,c);
    for  (i=(INT)0;i<S_V_LI(c);i++)
        erg += random_integer(S_V_I(c,i),NULL,NULL);
        
    erg += b_skn_po(c,callocobject(),NULL,a);
    erg += random_integer(b,NULL,NULL);
    if ((S_I_I(b) % 3L) == (INT)0)
        erg += random_integer(S_PO_K(a),NULL,NULL);
    if ((S_I_I(b) % 3L) == 1L)
        erg += random_longint(S_PO_K(a),NULL);
    if ((S_I_I(b) % 3L) == 2L)
        {
        erg += b_ou_b(callocobject(),callocobject(),S_PO_K(a));
        erg += random_integer(S_B_O(S_PO_K(a)),NULL,NULL);
        erg += random_integer(S_B_U(S_PO_K(a)),cons_eins,NULL);
        erg += kuerzen(S_PO_K(a));
        }
    erg += freeall(b);
    return erg;
}


INT random_polynom(a) OP a;
/* AK 180893 */
{
    INT erg = OK;
    OP b,c;
    INT i;

    CALLOCOBJECT2(b,c);
    erg += random_integer(b,NULL,NULL);
    init(POLYNOM,a);
    for (i=0;i<=S_I_I(b);i++)
        {
        erg += random_monom(c);
        erg += add_apply(c,a);
        }

    FREEALL2(b,c);
    ENDR("random_polynom");
}



INT symmetricp_i(a,i) OP a; INT i;
/* AK 141293 */
/* true if the POLYNOM object a ist the symmetric in a_i and a_{i+1} */
{
    OP d,c;
    INT erg = OK, res;

    if (i<(INT)0) 
        return error("symmetricp_i: index < 0");
    CTO(POLYNOM,"symmetricp_i",a);

    d = callocobject();
    c = callocobject();
    M_I_I(i+1,c);
    erg += divdiff(c,a,d);
    if (nullp(d))
        res = TRUE;
    else 
        res = FALSE;
    erg += freeall(d);
    erg += freeall(c);
    return res;
    ENDR("symmetricp_i");
}

INT symmetricp(a) OP a;
{
    OP n;
    INT i,res,erg = OK;
    if (MATRIXP(a)) return symmetricp_matrix(a);
    CTO(POLYNOM,"symmetricp",a);
    if (consp_polynom(a))
        return TRUE;
    
    n=callocobject();
    numberofvariables(a,n);
    for (i=(INT)0;i<S_I_I(n)-1L;i++)
        if (symmetricp_i(a,i) == FALSE)
            { res =FALSE; goto se; }
        
    res = TRUE;
    se:
    freeall(n);
    return res;
    ENDR("symmetricp");
}

INT cast_apply_monom(a) OP a;
/* AK 010394 */
{
    INT erg = OK;
    switch(S_O_K(a))
        {
        }
    return erg;
}


INT GaussRecInternal(po, m, n, res) INT po, m, n; OP res;
{ 
    if (n==0L || m==n) 
        {
        M_I_I(S_V_II(res,po)+1, S_V_I(res,po));
        }
        /* inc(S_V_I(res,po)); */
      else { 
        GaussRecInternal(po,m-1,n-1,res); 
        GaussRecInternal(po+n,m-1,n,res); 
        }
    return OK;
}

INT gauss_polynom(m, n, pol) OP m,n,pol;
/* computes the gauss polynomial */
/* SV&AL */
/* AK 201204 V3.0 */ /* AK 161006 V3.1 */
{
    INT erg = OK;
    CTO(INTEGER,"gauss_polynom(1)",m);
    CTO(INTEGER,"gauss_polynom(2)",n);

	    {
	    OP res;
	    INT i;

	    if (S_I_I(m) < S_I_I(n)) {
		m_i_i(0,pol);
		}
	    else     {
		res = CALLOCOBJECT();
		erg += m_il_nv(S_I_I(n)* ( S_I_I(m)-S_I_I(n)  ) + 1 ,res);
		GaussRecInternal(0,S_I_I(m),S_I_I(n),res);
		erg += m_iindex_iexponent_monom(0,0,pol);
		for (i=1;i<S_V_LI(res);i++)
		    {
		    C_PO_N(pol,callocobject());
		    erg += m_iindex_iexponent_monom(0,i,S_PO_N(pol));
		    pol = S_PO_N(pol);
		    erg += m_i_i(S_V_II(res,i),S_PO_K(pol));
		    }
		FREEALL(res);
		}
	    }

    ENDR("gauss_polynom");
}


INT t_LIST_POLYNOM(a,b) OP a,b;
/* AK 250195 */ /* AK 161006 V3.1 */
{
    INT erg = OK;
    OP z,zb;
    CTO(LIST,"t_LIST_POLYNOM(1)",a);
    CE2(a,b,t_LIST_POLYNOM);
                
    z = a;
    erg +=  init(POLYNOM,b);
    zb = b;
    if (S_L_S(z) == NULL)
        goto endr_ende;
    C_L_S(zb,callocobject());
again:
    erg += m_sk_mo(S_L_S(z),cons_eins,S_L_S(zb));
    C_O_K(zb,POLYNOM);
    if (S_L_N(z) != NULL)
        {
        C_L_N(zb,callocobject());
        erg += b_sn_l(callocobject(),NULL,S_L_N(zb));
        zb = S_L_N(zb);
        z = S_L_N(z);
        goto again;
        }

    ENDR("t_LIST_POLYNOM");
}

INT invers_POLYNOM(a,b) OP a ,b;
/* CC */
{
    INT erg = OK;
    CTO(POLYNOM,"invers_POLYNOM(1)",a);
    CTO(EMPTY,"invers_POLYNOM(2)",b);

    erg += m_ou_b(cons_eins,a,b);
    ENDR("invers_POLYNOM");
}



INT maple_polynom(poly) OP poly;
/* AL */
{
    OP zeiger = poly;
    INT i;

    if (EMPTYP(poly))               return(OK);
    while (zeiger != NULL)
    {
        print(S_PO_K(zeiger));
        for (i= 0L ;i < S_PO_SLI(zeiger); i++)
            if (S_PO_SII(zeiger,i) > 0L)
            {
                fprintf(texout,"*x%ld",i+1);
                texposition ++;
                if (S_PO_SII(zeiger,i) != 1L)
                    {
                    fprintf(texout,"^%ld",S_PO_SII(zeiger,i));
                    texposition += 10L;
                    };
            };

        texposition += 1L;
        if (texposition > 70L)
            {
            fprintf(texout,"\n");
            texposition = 0L;
            }

        zeiger = S_PO_N(zeiger);
        if (zeiger != NULL)
            if (not negp(S_PO_K(zeiger)))
                {
                fprintf(texout,"+");
                texposition +=3L;
                }
    };
    return(OK);
}

INT cast_apply_polynom(a) OP a;
/* tries to transform the object a into a POLYNOM object */
/* AK 170206 V3.0 */
{
    INT erg = OK;
    COP("cast_apply_polynom(1)",a);
    switch (S_O_K(a)) {
        case BRUCH:
        case LONGINT:
        case INTEGER:
            erg += m_scalar_polynom(a,a);
            break;
	case MONOPOLY:
	    erg += t_MONOPOLY_POLYNOM(a,a);
	    break;
        default:
            erg += WTO("cast_apply_polynom",a);
            break;
            }
    ENDR("cast_apply_polynom");
}


OP s_lc_poly(OP pol)
/* AK 181203 */
/* pointer auf leading coeff */
{
    INT erg = OK;
    OP z;
    CTO(POLYNOM,"s_lc_poly(1)",pol);
    SYMCHECK (S_L_S(pol)==NULL,"s_lc_poly:null polynom");
    z = S_PO_S(pol);
    SYMCHECK (( S_O_K(z)!= VECTOR )&&(S_O_K(z)!= INTEGERVECTOR),
              "s_lc_poly:wrong type of list self part");
    SYMCHECK (S_V_LI(z)!= 1, "s_lc_poly:not a univariate polynomial");
    z=pol;
    while (S_L_N(z)!=NULL) z=S_L_N(z);
    return S_PO_K(z);
    ENDO("s_lc_poly");
}

INT content_polynom(OP a, OP b)
/* AK 171203 */
{
    OP z;
    INT erg =OK;
    CTO(POLYNOM,"content_polynom(1)",a);
    if (NULLP(a)) { m_i_i(0,b); }
    copy(S_PO_K(a),b);
    FORALL(z,a,{ ggt(b,S_MO_K(z),b); });
    ENDR("content_polynom");
}

INT ggt_field_polynom(OP a, OP b, OP c)
/* AK 170206 */
/* Cohen p.113 */
{
    INT erg = OK;
    CTO(POLYNOM,"ggt_field_polynom(1)",a);
    CTO(POLYNOM,"ggt_field_polynom(2)",b);
    {
    if (NULLP(b)) erg+=copy(a,c);
    else {
        OP q=callocobject();
        OP r=callocobject();
        erg += quores(a,b,q,r); 
        erg += ggt_field_polynom(b,r,c);
	freeall(q);
	freeall(r);
        }
    }
    ENDR("ggt_field_polynom");
}

INT ggt_polynom(OP a, OP b, OP c)
/* AK 171203 */
{
    INT erg = OK;
    CTO(POLYNOM,"ggt_polynom(1)",a);
    CTO(POLYNOM,"ggt_polynom(2)",b);
    {
    OP aa,bb;OP q,r;
    OP ac,bc;
    OP d,z;
    if (NULLP(b))  { erg += copy(a,c); goto endr_ende;}
    aa=CALLOCOBJECT();content_polynom(a,aa);
    bb=CALLOCOBJECT();content_polynom(b,bb);
    d = CALLOCOBJECT();
    ggt(aa,bb,d);
    invers_apply(bb);
    invers_apply(aa);
    ac = CALLOCOBJECT();mult_scalar_polynom(aa,a,ac);FREESELF(aa);
    bc = CALLOCOBJECT();mult_scalar_polynom(bb,b,bc);FREESELF(bb);
    degree_polynom(ac,aa); degree_polynom(bc,bb);
    if (LT(aa,bb)) swap(ac,bc);

    CALLOCOBJECT2(q,r);
bb:
    FREESELF(aa);
    FREESELF(bb);
    degree_polynom(ac,aa); degree_polynom(bc,bb); /* aa >= bb is known */
    sub(aa,bb,aa); inc(aa);
    hoch (s_lc_poly(bc),aa,bb);
    mult_apply(bb,ac);  /* no coeff division necessary  in quores */
    quores(ac,bc,q,r);
    if (NULLP(r))  goto aa;
    FREESELF(q);
    degree_polynom(r,q); if (NULLP(q)) { eins(S_PO_K(r),bc); goto aa; }
    content_polynom(r,q); copy(bc,ac); invers_apply(q);
    FREESELF(bc);
    mult_scalar_polynom(q,r,bc); goto bb;

aa:
    MULT(d,bc,c);
    FREEALL3(d,aa,bb);
    FREEALL4(ac,bc,q,r);
    }
    ENDR("ggt_polynom");
}


INT derivative(OP pol, OP pold)
/* AK 171203 */
{
    INT erg = OK;
    OP z;
    CTO(POLYNOM,"derivative(1)",pol);
    CE2(pol,pold,derivative);
    if (S_L_S(pol)==NULL)
        {
        erg += copy(pol,pold);
        goto endr_ende;
        }
    z = S_PO_S(pol);
    SYMCHECK (S_O_K(z)!= VECTOR, "derivative:wrong type of list self part");
    SYMCHECK (S_V_LI(z)!= 1, "derivative:not a univariate polynomial");
    if (S_V_II(z,0) == 0)
        {
        if (S_PO_N(pol)==NULL) {
            init(POLYNOM,pold);
            goto endr_ende;
            }
        pol = S_PO_N(pol);
        }
    COPY(pol,pold);
    FORALL(z,pold,{
        MULT_APPLY(S_MO_SI(z,0),S_MO_K(z));
        DEC(S_MO_SI(z,0));
        });


    ENDR("derivative");
}

INT horner( OP point, OP vec, OP res)
/* eval polynomial at point */
/* vec[0] constant term */
/* res = vec[0]+point*vec[1]+point^2 *vec[2]+ .. */
/* AK 300607 */
{
        INT erg = OK;
        CTTO(VECTOR,INTEGERVECTOR,"horner(2)",vec);
        CE3(point,vec,res,horner);
        {
        INT i;
        COPY(S_V_I(vec,S_V_LI(vec)-1), res);
        for (i=S_V_LI(vec)-2;i>=0;i--)
                {
                MULT_APPLY(point,res);
                ADD_APPLY(S_V_I(vec,i),res);
                }
        }
        ENDR("horner");
}


#endif /* POLYTRUE */


