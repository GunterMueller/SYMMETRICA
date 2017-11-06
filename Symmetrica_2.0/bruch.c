/* SYMMETRICA source code file: bruch.c */
#include "def.h"
#include "macro.h"

static INT ggt_mp();
static INT lowcf_br();
static INT lowcf_br();


INT kuerzen_yn;
static struct bruch * callocbruch();
static INT freebruch();

static int bruch_speicherindex=-1; /* AK 301001 */
static int bruch_speichersize=0; /* AK 301001 */
static struct bruch **bruch_speicher=NULL; /* AK 301001 */
static INT mem_counter_bruch=0;



#ifdef BRUCHTRUE
INT bruch_anfang()
/* AK 100893 */
    {
    mem_counter_bruch=0;
    return OK;
    }

#define B_OU_B(oben,unten,ergebnis)\
    ( C_O_K(ergebnis,BRUCH),\
      (ergebnis->ob_self).ob_bruch=callocbruch(),\
      C_B_O(ergebnis,oben) ,\
      C_B_U(ergebnis,unten) ,\
      C_B_I(ergebnis,NGEKUERZT) \
    )

INT bruch_ende()
/* AK 100893 */
/* this function is called to clean up data structures concerning BRUCH objects */
/* this function is called from the function ende */
    {
    INT erg = OK;
    if (no_banner != TRUE)
    if (mem_counter_bruch != 0L)
        {
        fprintf(stderr,"mem_counter_bruch = %ld\n",mem_counter_bruch);
        erg += error("bruch memory not freed");
        goto endr_ende;
        }

    if (bruch_speicher!=NULL)
        {
        INT i;
        for (i=0;i<=bruch_speicherindex;i++)
            SYM_free(bruch_speicher[i]);
        SYM_free(bruch_speicher);
        }

    bruch_speicher=NULL;
    bruch_speicherindex=-1;
    bruch_speichersize=0;

    ENDR("bruch_ende");
    }




INT add_bruch_scalar(a,b,c) OP a, b, c;
/* AK 050789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP d;
    CTO(BRUCH,"add_bruch_scalar(1)",a);
    CTO(EMPTY,"add_bruch_scalar(3)",c);

    d = callocobject();
    erg += m_scalar_bruch(b,d);
    erg += add_bruch_bruch(a,d,c); /* hat kuerzen */

    FREEALL(d);
    ENDR("add_bruch_scalar");
}

INT add_bruch_integer(a,b,c) OP a,b,c;
/* AK 251001 */
{
    INT erg = OK;
    OP d;
    CTO(BRUCH,"add_bruch_integer(1)",a);
    CTO(INTEGER,"add_bruch_integer(2)",b);
    CTO(EMPTY,"add_bruch_integer(3)",c);

    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),c);
    d = CALLOCOBJECT();
    MULT_INTEGER(b,S_B_U(a),d);
    ADD(d,S_B_O(a),S_B_O(c));
    FREEALL(d);
    COPY(S_B_U(a),S_B_U(c));
    erg += kuerzen(c);
    ENDR("add_bruch_integer");
}


INT random_bruch(a) OP a;
/* AK 191093 */
{
    INT erg = OK;
    CTO(EMPTY,"random_bruch(1)",a);
rb_again:
    erg += b_ou_b(callocobject(),callocobject(),a); 
        /* a is freed automatically */
    erg += random_integer(S_B_O(a),NULL,NULL);
    erg += random_integer(S_B_U(a),cons_zwei,NULL);
    kuerzen(a);
    if (S_O_K(a) != BRUCH)
        goto rb_again;
    ENDR("random_bruch");
}




INT add_bruch_bruch(a,b,c) OP a, b, c;
/* AK 050789 V1.0 */ /* AK 181289 V1.1 */ /* AK 270291 V1.2 */
/* AK 200891 V1.3 */
{
    OP  zw2;
    INT erg =OK;
    CTO(BRUCH,"add_bruch_bruch(1)",a);
    CTO(BRUCH,"add_bruch_bruch(2)",b);
    CTO(EMPTY,"add_bruch_bruch(3)",c);

    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),c);
    MULT(S_B_U(a),S_B_U(b),S_B_U(c));
    zw2 = CALLOCOBJECT();
    MULT(S_B_O(a), S_B_U(b), S_B_O(c));
    MULT(S_B_U(a), S_B_O(b), zw2);
    ADD_APPLY(zw2,S_B_O(c));

    FREEALL(zw2);
    erg += kuerzen(c);
    ENDR("add_bruch_bruch");
}




INT absolute_bruch(a,b) OP a,b;
/* AK 150393 */
{
    INT erg = OK;
    CTO(BRUCH,"absolute_bruch(1)",a);
    CTO(EMPTY,"absolute_bruch(2)",b);

    erg += b_ou_b(callocobject(),callocobject(),b);
    erg += absolute(S_B_O(a),S_B_O(b));
    erg += absolute(S_B_U(a),S_B_U(b));
    ENDR("absolute_bruch");
}



INT add_bruch(a,b,c) OP a,b,c;
/* AK 310888 */ /* AK 050789 V1.0 */ /* AK 181289 V1.1 */
/* AK 270291 V1.2 */ /* AK 200891 V1.3 */
/*CC 190995 */
{
    INT erg = OK;
    CTO(BRUCH,"add_bruch(1)",a);
    CTO(EMPTY,"add_bruch(3)",c);

    switch(S_O_K(b))
    {
    case INTEGER:
        erg +=  add_bruch_integer(a,b,c);
        goto aiende;

    case LONGINT: 
        erg +=  add_bruch_scalar(a,b,c);
        goto aiende;

    case BRUCH: 
        erg +=  add_bruch_bruch(a,b,c); 
        goto aiende;

#ifdef POLYTRUE
    case LAURENT:
        {
        OP tp2;
        tp2=callocobject();
        erg += m_ou_b(b,cons_eins,tp2);
        erg += kuerzen(tp2);
        erg += add_bruch_bruch(a,tp2,c);
        erg += freeall(tp2);
        }
        break;
/*CC*/
    case MONOPOLY:
        {
        OP tp2=callocobject();
        erg += m_ou_b(b,cons_eins,tp2);
        erg += add_bruch_bruch(a,tp2,c);
        erg += freeall(tp2);
        }
        break;

    case POLYNOM:
/*
        if (has_one_variable(b))
            {
            OP tp2=callocobject();
            erg += m_ou_b(b,cons_eins,tp2);
            erg += kuerzen(tp2);
            erg += add_bruch_bruch(a,tp2,c);
            erg += freeall(tp2);
            }
        else
*/
            erg += add_scalar_polynom(a,b,c);
        goto aiende;
#endif /* POLYTRUE */

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

    case SQ_RADICAL:
        erg += add_scalar_sqrad(a,b,c);
        goto aiende;

    case CYCLOTOMIC:
        erg += add_scalar_cyclo(a,b,c);
        goto aiende;

    default :
        erg += WTO("add_bruch(2)",b);
    };
    erg += kuerzen(c);
aiende:
    ENDR("add_bruch");
}



INT negp_bruch(a) OP a;
/* AK 050789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK 221298 V2.0 */
/* TRUE if a < 0 */
{
    if (negp(S_B_O(a))) {
        if (negp(S_B_U(a))) return(FALSE);
        else return(TRUE);
    }
    else if (NULLP(S_B_O(a))) /* AK 221298 */
        return FALSE;
    /* now S_B_O > 0 */
    if (negp(S_B_U(a))) 
        return(TRUE);
    return(FALSE);
}



INT einsp_bruch(a) OP a;
/* AK 050789 V1.0 */ /* AK 081289 V1.1 */ /* AK 200891 V1.3 */
{
    return EQ(S_B_O(a),S_B_U(a));
}



INT negeinsp_bruch(a) OP a;
/* AK 181289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg;
    CTO(BRUCH,"negeinsp_bruch(1)",a);    
    addinvers_apply(S_B_O(a));
    erg = EQ(S_B_O(a),S_B_U(a));
    addinvers_apply(S_B_O(a));
    return(erg);
    ENDR("negeinsp_bruch");
}



INT nullp_bruch(a) OP a;
/* AK 050789 V1.0 */ /* AK 201289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"nullp_bruch(1)",a);
    return (NULLP(S_B_O(a)));
    ENDR("nullp_bruch");
}





INT addinvers_bruch(a,b) OP a,b;
/* AK 290388*/ /* AK 050789 V1.0 */ /* AK 201289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"addinvers_bruch(1)",a);
    CTO(EMPTY,"addinvers_bruch(2)",b);

    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),b);
    ADDINVERS(S_B_O(a),S_B_O(b));
    COPY(S_B_U(a),S_B_U(b));
    if (NEGP(S_B_O(b)) && NEGP(S_B_U(b))) 
        {
        ADDINVERS_APPLY(S_B_O(b));
        ADDINVERS_APPLY(S_B_U(b));
        }
    C_B_I(b,S_B_I(a));

    ENDR("addinvers_bruch");
}



INT addinvers_apply_bruch(a) OP a;
/* AK 201289 V1.1 */ /* AK 200891 V1.3 */
{ 
    INT erg = OK;
    CTO(BRUCH,"addinvers_apply_bruch(1)",a);
    ADDINVERS_APPLY(S_B_O(a)); 
    if (NEGP(S_B_O(a)) && NEGP(S_B_U(a))) 
        {
        ADDINVERS_APPLY(S_B_O(a));
        ADDINVERS_APPLY(S_B_U(a));
        }
    ENDR("addinvers_apply_bruch");
}




INT invers_apply_bruch(a) OP a;
/* AK 161001 */
{
    INT erg = OK;
    CTO(BRUCH,"invers_apply_bruch(1)",a);
    erg += swap(S_B_O(a),S_B_U(a));
    ENDR("invers_apply_bruch");
}

INT invers_bruch(a,b) OP a,b;
/* AK 031286 */ /* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"invers_bruch(1)",a);
    CTO(EMPTY,"invers_bruch(2)",b);

    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),b);
    COPY(S_B_U(a),S_B_O(b));
    COPY(S_B_O(a),S_B_U(b));
    C_B_I(b,S_B_I(a));

    ENDR("invers_bruch");
}



INT mult_bruch_integer(a,b,c) OP a,b,c;
/* AK 040789 V1.0 */ /* AK 081289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP d;

    CTO(BRUCH,"mult_bruch_integer(1)",a);
    CTO(INTEGER,"mult_bruch_integer(2)",b);
    CTO(EMPTY,"mult_bruch_integer(3)",c);

    if (INTEGRALP(S_B_O(a)) && INTEGRALP(S_B_U(a)) )
        {

        d = CALLOCOBJECT();
        GGT_INTEGER(b,S_B_U(a),d);

        if (EQ(d,S_B_U(a))) {
            GANZDIV(b,d,c);
            MULT_APPLY(S_B_O(a),c);
            FREEALL(d);
            goto ende;
            }

        B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),c);
        GANZDIV(S_B_U(a),d,S_B_U(c));
        GANZDIV_INTEGER(b,d,S_B_O(c));
        FREEALL(d);
        MULT_APPLY(S_B_O(a),S_B_O(c));
        if (NEGP(S_B_O(c)) && NEGP(S_B_U(c)))
            {
            ADDINVERS_APPLY(S_B_O(c));
            ADDINVERS_APPLY(S_B_U(c));
            }
        C_B_I(c,GEKUERZT);
        goto ende;
        }
    /* denominator or nominator not a integer */
    /* AK 060502 */
    COPY(a,c);
    MULT_APPLY(b,S_B_O(c));
    erg += kuerzen(c);

ende:
    CTTTTO(LONGINT,INTEGER,S_O_K(S_B_O(a)),BRUCH,"mult_bruch_integer(e3)",c);
    ENDR("mult_bruch_integer");
}

INT mult_bruch_longint(a,b,c) OP a,b,c;
/* AK 040789 V1.0 */ /* AK 081289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP d;
    
    CTO(BRUCH,"mult_bruch_longint(1)",a);
    CTO(LONGINT,"mult_bruch_longint(2)",b);
    CTO(EMPTY,"mult_bruch_longint(3)",c);
    d = CALLOCOBJECT();
    GGT_LONGINT(b,S_B_U(a),d);
 
    if (EQ(d,S_B_U(a))) {
        GANZDIV(b,d,c);
        MULT_APPLY(S_B_O(a),c);
        FREEALL(d);
        goto endr_ende;
        }
 
    B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),c);
    GANZDIV(S_B_U(a),d,S_B_U(c));
    GANZDIV_LONGINT(b,d,S_B_O(c));
    FREEALL(d);
    MULT_APPLY(S_B_O(a),S_B_O(c));
    if (NEGP(S_B_O(c)) && NEGP(S_B_U(c)))
        {
        ADDINVERS_APPLY(S_B_O(c));
        ADDINVERS_APPLY(S_B_U(c));
        }
    C_B_I(c,GEKUERZT);

    CTTTTO(INTEGER,LONGINT,S_O_K(S_B_O(a)),BRUCH,"mult_bruch_longint(e3)",c);
    ENDR("mult_bruch_longint");
}

INT mult_bruch_bruch(a,b,c) OP a,b,c;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"mult_bruch_bruch(1)",a);
    CTO(BRUCH,"mult_bruch_bruch(2)",b);
    CTTO(EMPTY,BRUCH,"mult_bruch_bruch(3)",c);

    
    if (S_O_K(c) == BRUCH)
        { 
        FREESELF(S_B_O(c)); 
        FREESELF(S_B_U(c)); 
        }
    else
        B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),c);

    if (
       INTEGRALP(S_B_O(a)) && INTEGRALP(S_B_U(a)) 
       && 
       INTEGRALP(S_B_O(b)) && INTEGRALP(S_B_U(b)) 
       )     {
        OP d = CALLOCOBJECT();
        OP e = CALLOCOBJECT();

        GGT(S_B_O(a),S_B_U(b),d); 
        if (not EINSP(d)) {
            GANZDIV(S_B_O(a),d,S_B_O(c));
            GANZDIV(S_B_U(b),d,S_B_U(c));
            }
        else {
            COPY(S_B_O(a),S_B_O(c));
            COPY(S_B_U(b),S_B_U(c));
            }
        FREESELF(d);
        GGT(S_B_U(a),S_B_O(b),d);
        if (not EINSP(d)) {
            GANZDIV(S_B_O(b),d,e);
            MULT_APPLY(e,S_B_O(c));
            }
        else {
            MULT_APPLY(S_B_O(b),S_B_O(c));
            }
        FREESELF(e);
        if (not EINSP(d)) {
            GANZDIV(S_B_U(a),d,e);
            MULT_APPLY(e,S_B_U(c));
            }
        else {
            MULT_APPLY(S_B_U(a),S_B_U(c));
            }
        if (NEGP(S_B_O(c)) && NEGP(S_B_U(c)))
            {
            ADDINVERS_APPLY(S_B_O(c));
            ADDINVERS_APPLY(S_B_U(c));
            }
        C_B_I(c,GEKUERZT);
        FREEALL(e);
        FREEALL(d);
        goto ende;
        }

    MULT(S_B_O(a),S_B_O(b),S_B_O(c));
    MULT(S_B_U(a),S_B_U(b),S_B_U(c));
    erg += kuerzen(c);
ende:
    ENDR("mult_bruch_bruch");
}



INT tex_bruch(a) OP a;
/* AK 070291 V1.2 */ /* AK 300791 V1.3 */ /* AK 200891 V1.3 */
{
    INT erg = OK,merk;
    CTO(BRUCH,"tex_bruch(1)",a);
    merk = texmath_yn;
    if (texmath_yn != (INT)1) 
        {  fprintf(texout,"$"); texmath_yn = (INT)1; }
    fprintf(texout,"{");
    erg += tex(S_B_O(a));
    fprintf(texout," \\over ");
    erg += tex(S_B_U(a));
    fprintf(texout,"}");
    texposition += (INT)10;
    texmath_yn = merk;
    if (texmath_yn != (INT)1)  /* d.h. no math mode any more */
          fprintf(texout,"$");
    ENDR("tex_bruch");
}



INT fprint_bruch(a,b) FILE *a; OP b;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 040391 V1.2 */
/* AK 200891 V1.3 */
{
    extern INT zeilenposition;

    fprint(a,S_B_O(b));
    fprintf(a,"/");
    if (a == stdout)
    {
        if (zeilenposition > 70L)
        {
            zeilenposition = 0L;
            fprintf(a,"\n");
        }
        else
            zeilenposition++;
    }
    fprint(a,S_B_U(b));
    return OK;
}



INT freeself_bruch(bruch) OP bruch;
/* AK 050789 V1.0 */ /* AK 211189 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;

    FREEALL(S_B_O(bruch));
    FREEALL(S_B_U(bruch));

    erg += freebruch(S_O_S(bruch).ob_bruch);
    C_O_K(bruch,EMPTY);
    ENDR("freeself_bruch");
}


INT copy_bruch(von,nach) OP von, nach;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"copy_bruch(1)",von);
    CTO(EMPTY,"copy_bruch(2)",nach);

    B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),nach);
    COPY(S_B_O(von),S_B_O(nach));
    COPY(S_B_U(von),S_B_U(nach));
    C_B_I(nach,S_B_I(von));
    ENDR("copy_bruch");
}



static struct bruch * callocbruch()
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    struct bruch *ergebnis;

    mem_counter_bruch++;


    if (bruch_speicherindex >= 0) /* AK 301001 */
        return bruch_speicher[bruch_speicherindex--];
 


    ergebnis = (struct bruch *) 
        SYM_malloc( sizeof(struct bruch));

    if (ergebnis == NULL) no_memory();

    return ergebnis;
}

static INT freebruch(v) struct bruch *v;
/* AK 231001 */
{
    INT erg = OK;
    if (bruch_speicherindex+1 == bruch_speichersize) {
       if (bruch_speichersize == 0) {
           bruch_speicher = (struct bruch **) SYM_malloc(100 * sizeof(struct bruch *));
           if (bruch_speicher == NULL) {
               erg += error("no memory");
               goto endr_ende;
               }
           bruch_speichersize = 100;
           }
       else {
           bruch_speicher = (struct bruch **) SYM_realloc (bruch_speicher,
               2 * bruch_speichersize * sizeof(struct bruch *));
           if (bruch_speicher == NULL) {
               erg += error("no memory");
               goto endr_ende;
               }
           bruch_speichersize = 2 * bruch_speichersize;
           }
       }

    mem_counter_bruch--;

    bruch_speicher[++bruch_speicherindex] = v;
    ENDR("freebruch");
}
 




INT m_ou_b(oben,unten,ergebnis) OP oben, unten,ergebnis;
/* AK 221190 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),ergebnis);
    COPY(oben, S_B_O(ergebnis));
    COPY(unten, S_B_U(ergebnis));
    CTO(BRUCH,"m_ou_b(3-end)",ergebnis);
    ENDR("m_ou_b");
}



INT b_ou_b(oben,unten,ergebnis) OP oben, unten,ergebnis;
/* AK 050789 V1.0 */ /* AK 071289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OBJECTSELF d;
    if (oben == unten) {
        erg += error("b_ou_b:identical objects");
        goto endr_ende;
        }

    d.ob_bruch = callocbruch();
    erg += b_ks_o(BRUCH, d, ergebnis);
    C_B_O(ergebnis,oben);
    C_B_U(ergebnis,unten);
    C_B_I(ergebnis,NGEKUERZT);
    ENDR("b_ou_b");
}



INT m_ioiu_b(oben,unten,ergebnis) INT oben,unten; OP ergebnis;
/* AK 030389
    ein bruch mit einem integer eintrag im zaehler und einem
    integer eintrag im nenner z.b. oben = 3 unten = 5 --> 3/5 */
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    erg += b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),ergebnis);
    M_I_I(oben,S_B_O(ergebnis));
    M_I_I(unten,S_B_U(ergebnis));
    return erg;
}




INT scan_bruch(a) OP a;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
/* AK 220998 V2.0 */
{
    OBJECTKIND kind;
    INT erg = OK;
    CTO(EMPTY,"scan_bruch(1)",a);

    erg += b_ou_b(callocobject(),callocobject(),a);
    erg += printeingabe("input of a fractional number");
    erg += printeingabe("input of the nominator");
    kind = scanobjectkind();
    erg += scan(kind,S_B_O(a));
    erg += printeingabe("input of the denominator");
    kind = scanobjectkind();
    erg += scan(kind,S_B_U(a));
    erg += kuerzen(a);
    ENDR("scan_bruch");
}

INT scan_integerbruch(a) OP a;
/* AK 220998 V2.0 */
{
    INT erg = OK;
    CTO(EMPTY,"scan_integerbruch(1)",a);

    erg +=b_ou_b(CALLOCOBJECT(),CALLOCOBJECT(),a);
    erg += printeingabe("input of a fraction two INTEGER objects");
    erg += printeingabe("input of the nominator");
    erg += scan(INTEGER,S_B_O(a));
    erg += printeingabe("input of the denominator");
    erg += scan(INTEGER,S_B_U(a));
    CTO(BRUCH,"scan_integerbruch(i)",a);
    erg += kuerzen_integral(a);
    ENDR("scan_integerbruch");
}




OP s_b_o(a) OP a;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{

    OBJECTSELF c;
    INT erg = OK;
    CTO(BRUCH, "s_b_o",a);
    c = s_o_s(a);
    return(c.ob_bruch->b_oben);
    ENDO("s_b_o");
}

OP s_b_u(a) OP a;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{

    OBJECTSELF c;
    INT erg = OK;
    CTO(BRUCH, "s_b_u(1)",a);
    c = s_o_s(a);
    return(c.ob_bruch->b_unten);
    ENDO("s_b_u");
}

INT s_b_i(a) OP a;
/* notiert gekuerzt oder nicht */
{
    INT erg = OK;
    OBJECTSELF c;
    CTO(BRUCH, "s_b_i(1)",a);
    c = s_o_s(a);
    return(c.ob_bruch->b_info);
    ENDR("s_b_i")
}


INT s_b_oi(a) OP a;
/* AK 240789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    return(s_i_i(s_b_o(a)));
}

INT s_b_ui(a) OP a;
/* AK 240789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{
    return(s_i_i(s_b_u(a)));
}

INT c_b_o(a,b) OP a,b;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{

    OBJECTSELF c;
    c = s_o_s(a);

    c.ob_bruch->b_oben = b;
    return(OK);
}

INT c_b_u(a,b) OP a,b;
/* AK 050789 V1.0 */ /* AK 010290 V1.1 */ /* AK 200891 V1.3 */
{

    OBJECTSELF c;
    c = s_o_s(a);

    c.ob_bruch->b_unten = b;
    return(OK);
}



INT posp_bruch(a) OP a;
/* AK 040590 V1.1 */ /* AK 200891 V1.3 */
/* AK 190298 V2.0 */
/* TRUE if >= 0 */
{
    INT erg = OK;
    CTO(BRUCH,"posp_bruch",a);

    if (NULLP(S_B_O(a))) 
            return TRUE; 

    if (posp(S_B_O(a))) {
        if (posp(S_B_U(a))) 
            return TRUE;
        else
            return FALSE;
        }

    if (negp(S_B_U(a))) 
            return TRUE;
    else
            return FALSE;

    ENDR("posp_bruch");
}



INT comp_bruch(a,b) OP a,b;
/* AK 050789 V1.0 */
/* AK 310190 V1.1 */ /* fehler beseitigt von Isabel Klein */ 
/* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"comp_bruch(1)",a);
    if (S_O_K(b) == BRUCH)
        {
        /* a/b < c/d   <==>  ad < cb */
        INT ret;
        OP c,d;
        c = CALLOCOBJECT();
        d = CALLOCOBJECT();
        MULT(S_B_O(a),S_B_U(b),c);
        MULT(S_B_O(b),S_B_U(a),d);
        if     (
            (NEGP(S_B_U(a)) && NEGP(S_B_U(b)))
            || 
            (POSP(S_B_U(a)) && POSP(S_B_U(b)))
            )
            ret = comp(c,d);
        else 
            ret = comp(d,c);
        FREEALL(c); 
        FREEALL(d); 
        return(ret);
        }
    else if (scalarp(b))
        return comp_bruch_scalar(a,b);
    else    
        WTO("comp_bruch(2)",b);
    
    ENDR("comp_bruch");
}



INT comp_bruch_scalar(a,b) OP a,b;
/* AK 050789 V1.0 */ /* AK 310190 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg=0;
    OP c;
    CTO(BRUCH,"comp_bruch_scalar(1)",a);
    c = CALLOCOBJECT();
    MULT(S_B_U(a),b,c);
    erg = COMP(S_B_O(a),c);
    FREEALL(c);
    if (NEGP(S_B_U(a))) erg =  -erg; /* AK 271192 */
    return(erg);
    ENDR("comp_bruch_scalar");
}




INT kuerzen_integer_integer();
INT kuerzen_integer_longint();
INT kuerzen_longint_integer();
INT kuerzen_longint_longint();

INT kuerzen(bruch) OP bruch;
{
    INT erg = OK;
    CTTTO(LONGINT,INTEGER,BRUCH,"kuerzen(1)",bruch);

    if (S_O_K(bruch) != BRUCH) goto ende;
    if (kuerzen_yn == 1L) goto ende; /* d.h. nicht kuerzen */


    if (S_O_K(S_B_O(bruch)) == INTEGER) 
        {
        if (S_O_K(S_B_U(bruch)) == INTEGER) 
            {
            erg += kuerzen_integer_integer(bruch);
            goto ende;
            }
        else if (S_O_K(S_B_U(bruch)) == LONGINT) 
            {
            erg += kuerzen_integer_longint(bruch);
            goto ende;
            }
        else
            goto nf;
        }
    else if (S_O_K(S_B_O(bruch)) == LONGINT)
        {
        if (S_O_K(S_B_U(bruch)) == INTEGER) 
            {
            erg += kuerzen_longint_integer(bruch);
            goto ende;
            }
        else if (S_O_K(S_B_U(bruch)) == LONGINT) 
            {
            erg += kuerzen_longint_longint(bruch);
            goto ende;
            }
        else
            goto nf;
        }
        

nf:
    erg += krz(bruch);
ende:
    ENDR("kuerzen");
}

INT kuerzen_integer_integer(bruch) OP bruch;
{
    INT erg = OK;
    INT ggterg;
    CTO(BRUCH,"kuerzen_integer_integer(1)",bruch);
    CTO(INTEGER,"kuerzen_integer_integer(1-nominator)",S_B_O(bruch));
    CTO(INTEGER,"kuerzen_integer_integer(1-denominator)",S_B_U(bruch));
    if (kuerzen_yn == 1L) { goto ende; /* d.h. nicht kuerzen */ }
    
    if (NULLP_INTEGER(S_B_O(bruch))) {
        freeself_bruch(bruch);
        M_I_I(0,bruch);
        goto ende;
        }

    ggterg = ggt_i(S_B_UI(bruch),S_B_OI(bruch));

    if (ggterg == S_B_UI(bruch)) {
        freeself_bruch(bruch);
        M_I_I(S_B_OI(bruch) / ggterg,bruch);
        goto ende;
        }

    if (-ggterg == S_B_UI(bruch)) {
        freeself_bruch(bruch);
        M_I_I(- S_B_OI(bruch) / ggterg,bruch);
        goto ende;
        }

    if (ggterg != 1) {
        M_I_I(S_B_OI(bruch)/ggterg,S_B_O(bruch));
        M_I_I(S_B_UI(bruch)/ggterg,S_B_U(bruch));
        }
    if (NEGP_INTEGER(S_B_O(bruch)) && NEGP_INTEGER(S_B_U(bruch)))
        {
        ADDINVERS_APPLY_INTEGER(S_B_O(bruch));
        ADDINVERS_APPLY_INTEGER(S_B_U(bruch));
        }
    C_B_I(bruch,GEKUERZT);

ende:
    ENDR("kuerzen_integer_integer");
}

INT kuerzen_integer_longint(bruch) OP bruch;
{
    INT erg = OK;
    OP ggterg;
    CTO(BRUCH,"kuerzen_integer_longint(1)",bruch);
    CTO(INTEGER,"kuerzen_integer_longint(1-nominator)",S_B_O(bruch));
    CTO(LONGINT,"kuerzen_integer_longint(1-denominator)",S_B_U(bruch));
    if (kuerzen_yn == 1L) { goto ende; /* d.h. nicht kuerzen */ }
    
    if (NULLP_INTEGER(S_B_O(bruch))) {
        freeself_bruch(bruch);
        M_I_I(0,bruch);
        goto ende;
        }
    if (EINSP_INTEGER(S_B_O(bruch))) {
        C_B_I(bruch,GEKUERZT);
        goto ende;
        }


    ggterg = CALLOCOBJECT();
    erg += ggt_integer_longint(S_B_O(bruch),S_B_U(bruch),ggterg);
    CTO(INTEGER,"kuerzen_integer_longint(i1)",ggterg);
    if (S_I_I(ggterg) != 1) {
        GANZDIV_APPLY_INTEGER(S_B_O(bruch),ggterg);
        GANZDIV_APPLY_LONGINT(S_B_U(bruch),ggterg);
        }
    FREEALL(ggterg);

    if (S_O_K(S_B_U(bruch)) == INTEGER)
        if (S_B_UI(bruch) == 1) { 
            freeself_bruch(bruch);
            M_I_I(S_B_OI(bruch),bruch); 
            goto ende; }
        else if (S_B_UI(bruch) == -1) { 
            freeself_bruch(bruch);
            M_I_I( - S_B_OI(bruch),bruch); 
            goto ende; }
    if (NEGP(S_B_O(bruch)) && NEGP(S_B_U(bruch)))
        {
        ADDINVERS_APPLY(S_B_O(bruch));
        ADDINVERS_APPLY(S_B_U(bruch));
        }
    C_B_I(bruch,GEKUERZT);

ende:
    CTO(ANYTYPE,"kuerzen_integer_longint(e1)",bruch);
    ENDR("kuerzen_integer_longint");
}

INT kuerzen_longint_integer(bruch) OP bruch;
{
    INT erg = OK;
    OP ggterg;
    CTO(BRUCH,"kuerzen_longint_integer(1)",bruch);
    CTO(LONGINT,"kuerzen_longint_integer(1-nominator)",S_B_O(bruch));
    CTO(INTEGER,"kuerzen_longint_integer(1-denominator)",S_B_U(bruch));
    if (kuerzen_yn == 1L) { goto ende; /* d.h. nicht kuerzen */ }
   
    if (NULLP_LONGINT(S_B_O(bruch))) {
        freeself_bruch(bruch);
        M_I_I(0,bruch);
        goto ende;
        }
 
    ggterg = CALLOCOBJECT();
    erg += ggt_integer_longint(S_B_U(bruch),S_B_O(bruch),ggterg);
    CTO(INTEGER,"kuerzen_integer_longint(i1)",ggterg);
    if (S_I_I(ggterg) != 1)
        {
        GANZDIV_APPLY_INTEGER(S_B_U(bruch),ggterg);
        GANZDIV_APPLY_LONGINT(S_B_O(bruch),ggterg);
        }
    FREEALL(ggterg);
 
    if (S_B_UI(bruch) == 1) {
        if (S_O_K(S_B_O(bruch)) == INTEGER)
            {
            INT wi = S_B_OI(bruch);
            freeself_bruch(bruch);
            M_I_I(wi,bruch);
            }
        else /* LONGINT */
            {
            OP d;
            d  = CALLOCOBJECT();
            SWAP(S_B_O(bruch),d);
            erg += freeself_bruch(bruch);
            SWAP(d,bruch);
            FREEALL(d);
            }
        goto ende; 
        }
    else if (S_B_UI(bruch) == -1) {
        if (S_O_K(S_B_O(bruch)) == INTEGER)
            {
            INT wi = S_B_OI(bruch);
            freeself_bruch(bruch);
            M_I_I(-wi,bruch);
            }
        else /* LONGINT */
            {
            OP d;
            d  = CALLOCOBJECT();
            SWAP(S_B_O(bruch),d);
            erg += freeself_bruch(bruch);
            ADDINVERS_APPLY(d);
            SWAP(d,bruch);
            FREEALL(d);
            }
        goto ende; 
        }
    if (NEGP(S_B_O(bruch)) && NEGP(S_B_U(bruch)))
        {
        ADDINVERS_APPLY(S_B_O(bruch));
        ADDINVERS_APPLY(S_B_U(bruch));
        }
    C_B_I(bruch,GEKUERZT);
ende:
    ENDR("kuerzen_longint_integer");
}

INT kuerzen_longint_longint(bruch) OP bruch;
{
    INT erg = OK;
    OP ggterg;
    CTO(BRUCH,"kuerzen_longint_longint(1)",bruch);
    CTO(LONGINT,"kuerzen_longint_longint(1-nominator)",S_B_O(bruch));
    CTO(LONGINT,"kuerzen_longint_longint(1-denominator)",S_B_U(bruch));
    if (kuerzen_yn == 1L) { goto ende; /* d.h. nicht kuerzen */ }
 
    if (NULLP_LONGINT(S_B_O(bruch))) {
        freeself_bruch(bruch);
        M_I_I(0,bruch);
        goto ende;
        }
 
    ggterg = CALLOCOBJECT();
    erg += ggt_longint_longint(S_B_U(bruch),S_B_O(bruch),ggterg);
    if (not EINSP(ggterg)) {
        GANZDIV_APPLY_LONGINT(S_B_U(bruch),ggterg);
        GANZDIV_APPLY_LONGINT(S_B_O(bruch),ggterg);
        }
    FREEALL(ggterg);
 
    if (S_O_K(S_B_U(bruch))== INTEGER)
    if (S_B_UI(bruch) == 1) {
        if (S_O_K(S_B_O(bruch)) == INTEGER)
            {
            INT wi = S_B_OI(bruch);
            freeself_bruch(bruch);
            M_I_I(wi,bruch);
            }
        else /* LONGINT */
            {
            OP d;
            d  = CALLOCOBJECT();
            SWAP(S_B_O(bruch),d);
            erg += freeself_bruch(bruch);
            SWAP(d,bruch);
            FREEALL(d);
            }
        goto ende;
        }
    else if (S_B_UI(bruch) == -1) {
        if (S_O_K(S_B_O(bruch)) == INTEGER)
            {
            INT wi = S_B_OI(bruch);
            freeself_bruch(bruch);
            M_I_I(-wi,bruch);
            }
        else /* LONGINT */
            {
            OP d;
            d  = CALLOCOBJECT();
            SWAP(S_B_O(bruch),d);
            erg += freeself_bruch(bruch);
            ADDINVERS_APPLY(d);
            SWAP(d,bruch);
            FREEALL(d);
            }
        goto ende;
        }
    if (NEGP(S_B_O(bruch)) && NEGP(S_B_U(bruch)))
        {
        ADDINVERS_APPLY(S_B_O(bruch));
        ADDINVERS_APPLY(S_B_U(bruch));
        }
    C_B_I(bruch,GEKUERZT);
ende:
    ENDR("kuerzen_longint_longint");
}


INT kuerzen_integral(bruch) OP bruch;
/* AK 050789 V1.0 */ /* AK 061289 V1.1 */ /* AK 100791 V1.3 */
/* bruch is a BRUCH object
   with oben and unten both are integral, i.e. INTEGER or LONGINT
*/
{
    return kuerzen(bruch);
}



INT m_scalar_bruch(a,b) OP a,b;
/* AK 210387 macht aus scalar bruch */
/* die integerzahl 5 wird z.B. 5/1 */
/* AK 050789 V1.0 */ /* AK 040590 V1.1 */
/* AK 050789 V1.0 */ /* AK 061289 V1.1 */ /* AK 100791 V1.3 */
{
    return m_ou_b(a,cons_eins,b);
}

#define MAS_B_CO(b)\
    if (S_O_K(S_B_U(b)) == INTEGER)\
    if (S_B_UI(b) == (INT)1)\
        {\
        c = CALLOCOBJECT();\
        SWAP(S_B_O(b),c);\
        FREESELF(b);\
        SWAP(c,b);\
        FREEALL(c);\
        }\
    else if (S_B_UI(b) == (INT)-1)\
        {\
        c = CALLOCOBJECT();\
        SWAP(S_B_O(b),c);\
        FREESELF(b);\
        SWAP(c,b);\
        FREEALL(c);\
        ADDINVERS_APPLY(b);\
        } 

INT mult_apply_scalar_bruch(a,b) OP a,b;
/* AK 150290 V1.1 */ /* AK 100791 V1.3 */
{
    INT erg = OK;
    OP c;
    CTO(BRUCH,"mult_apply_scalar_bruch(2)",b);

    c = CALLOCOBJECT();
    erg += ggt(a,S_B_U(b),c);
    GANZDIV_APPLY(S_B_U(b),c);
    erg += ganzdiv(a,c,c);
    erg += mult_apply(c,S_B_O(b));
    FREEALL(c);
    MAS_B_CO(b); /* check on 1 in denominator */
    /* ist bereits gekuerzt */
    
    ENDR("mult_apply_scalar_bruch");
}

INT mult_apply_integer_bruch(a,b) OP a,b;
/* AK 251001 */
{
    INT erg = OK;
    OP c,d;
    CTO(INTEGER,"mult_apply_integer_bruch(1)",a);
    CTO(BRUCH,"mult_apply_integer_bruch(2)",b);

    if (INTEGRALP(S_B_O(b)) && INTEGRALP(S_B_U(b)))
        {
        c = CALLOCOBJECT();
        GGT_INTEGER(a,S_B_U(b),c);
        GANZDIV_APPLY(S_B_U(b),c);
        d = CALLOCOBJECT();
        GANZDIV(a,c,d);
        MULT_APPLY_INTEGER(d,S_B_O(b));
        FREEALL(c);
        FREEALL(d);
        MAS_B_CO(b); /* check on 1 in denominator */
        /* ist bereits gekuerzt */
        goto ende;
        }
    /* nominator or denominator is not integer */
    /* AK 060502 */
    MULT_APPLY_INTEGER(a,S_B_O(b));
    erg += kuerzen(b);
   
ende:
    ENDR("mult_apply_integer_bruch");
}

INT mult_apply_longint_bruch(a,b) OP a,b;
/* AK 291001 */
{
    INT erg = OK;
    OP c,d;
    CTO(LONGINT,"mult_apply_longint_bruch(1)",a);
    CTO(BRUCH,"mult_apply_longint_bruch(2)",b);
 
    c = CALLOCOBJECT();
    GGT_LONGINT(a,S_B_U(b),c);
    GANZDIV_APPLY(S_B_U(b),c);
    d = CALLOCOBJECT();
    GANZDIV(a,c,d);
    MULT_APPLY(d,S_B_O(b));
    FREEALL(c);
    FREEALL(d);
 
    MAS_B_CO(b); /* check on 1 in denominator */
 
    /* ist bereits gekuerzt */
 
    ENDR("mult_apply_longint_bruch");
}


INT mult_apply_bruch_integer(a,b) OP a,b;
/* AK 251001 */
{
    INT erg = OK;
    OP c,d;
    CTO(BRUCH,"mult_apply_bruch_integer(1)",a);
    CTO(INTEGER,"mult_apply_bruch_integer(2)",b);

    if (NULLP_INTEGER(b)) goto ae;
 
    c = CALLOCOBJECT();
    GGT_INTEGER(b,S_B_U(a),c);
    CTO(INTEGER,"mult_apply_bruch_integer:internal",c);

    if (EQ_INTEGER(c,S_B_U(a)))
        {
        M_I_I(S_I_I(b)/S_I_I(c),b);
        FREEALL(c);
        MULT_APPLY(S_B_O(a),b);
        goto ae;
        }

    
    d = CALLOCOBJECT();
    B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),d);

    GANZDIV(S_B_U(a),c,S_B_U(d));
    M_I_I(S_I_I(b)/S_I_I(c),c);
    MULT_INTEGER(c,S_B_O(a),S_B_O(d));
    if (NEGP(S_B_O(d)) && NEGP(S_B_U(d))) 
        {
        ADDINVERS_APPLY(S_B_O(d));
        ADDINVERS_APPLY(S_B_U(d));
        }
    C_B_I(d,GEKUERZT);
    FREEALL(c);
    SWAP(d,b);
    FREEALL(d);
    
 
 
    C_B_I(b,GEKUERZT);
    /* ist bereits gekuerzt */
ae: 
    ENDR("mult_apply_bruch_integer");
}

INT mult_apply_bruch_longint(a,b) OP a,b;
/* AK 251001 */
{
    INT erg = OK;
    OP c,d;
    CTO(BRUCH,"mult_apply_bruch_longint(1)",a);
    CTO(LONGINT,"mult_apply_bruch_longint(2)",b);
 
    c = CALLOCOBJECT();
    GGT_LONGINT(b,S_B_U(a),c);
 
    if (EQ(c,S_B_U(a)))
        {
        GANZDIV_APPLY(b,c);
        FREEALL(c);
        MULT_APPLY(S_B_O(a),b);
        goto ende;
        }
 
   
    d = CALLOCOBJECT();
    B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),d);
 
    GANZDIV(S_B_U(a),c,S_B_U(d));
    ganzdiv(b,c,c); /* AK 121201 */
    MULT(c,S_B_O(a),S_B_O(d));
    FREEALL(c);
    SWAP(d,b);
    FREEALL(d);
 
 
 
    /* ist bereits gekuerzt */
    C_B_I(b,GEKUERZT);
    if (NEGP(S_B_O(b)) && NEGP(S_B_U(b))) 
        {
        ADDINVERS_APPLY(S_B_O(b));
        ADDINVERS_APPLY(S_B_U(b));
        }
ende:
    ENDR("mult_apply_bruch_longint");
}

INT mult_apply_bruch_bruch(a,b) OP a,b;
/* AK 281001 */
{
    INT erg = OK;
    OP c,d;
    CTO(BRUCH,"mult_apply_bruch_bruch(1)",a);
    CTO(BRUCH,"mult_apply_bruch_bruch(2)",b);
    c = CALLOCOBJECT();
    d = CALLOCOBJECT();
    GGT(S_B_O(a),S_B_U(b),c);
    GANZDIV(S_B_O(a),c,d);
    GANZDIV_APPLY(S_B_U(b),c);

    FREESELF(c);

    GGT(S_B_O(b),S_B_U(a),c);
    GANZDIV_APPLY(S_B_O(b),c);
    MULT_APPLY(d,S_B_O(b));

    FREESELF(d);
    GANZDIV(S_B_U(a),c,d);
    MULT_APPLY(d,S_B_U(b));

    if (EINSP(S_B_U(b))) {
        SWAP(S_B_O(b),c);
        FREESELF(b);
        SWAP(c,b);
        }
    else if (NEGEINSP(S_B_U(b))) {
        SWAP(S_B_O(b),c);
        FREESELF(b);
        ADDINVERS_APPLY(c);
        SWAP(c,b);
        } 

    FREEALL(c);  
    FREEALL(d);  


    CTO(ANYTYPE,"mult_apply_bruch_bruch(e2)",b);
    ENDR("mult_apply_bruch_bruch");
}




INT mult_apply_bruch_scalar(a,b) OP a,b;
/* AK 140290 V1.1 */ /* AK 200891 V1.3 */
/* b = b*a */
{
    INT erg = OK;
    OP c;
    CTO(BRUCH,"mult_apply_bruch_scalar",a);

    c = callocobject();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += copy_bruch(a,b);
    erg += mult_apply_scalar_bruch(c,b); /* hat kuerzen */
    erg += freeall(c);
    ENDR("mult_apply_bruch_scalar");
}



INT add_apply_bruch_bruch_pre261101(a,b) OP a,b;
/* b = b + a */
/* AK 220390 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP c;
    CTO(BRUCH,"add_apply_bruch_bruch(1)",a);
    CTO(BRUCH,"add_apply_bruch_bruch(2)",b);


    SYMCHECK((S_B_I(a) != GEKUERZT),"add_apply_bruch_bruch:(1) not reduced");
    SYMCHECK((S_B_I(b) != GEKUERZT),"add_apply_bruch_bruch:(2) not reduced");

    c = CALLOCOBJECT();

    MULT(S_B_O(a),S_B_U(b),c);
    MULT_APPLY(S_B_U(a), S_B_U(b));
    MULT_APPLY(S_B_U(a), S_B_O(b));
    ADD_APPLY(c,S_B_O(b));
    FREEALL(c);

    if (NULLP(S_B_O(b)) ) {
        FREESELF(b);
        M_I_I(0,b);
        }
    else {
        C_B_I(b,NGEKUERZT);
        KUERZEN(b);
        }
    ENDR("add_apply_bruch_bruch");
}

INT add_apply_bruch_bruch(a,b) OP a,b;
/* b = b + a */
/* AK 220390 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP c,d,e;
    CTO(BRUCH,"add_apply_bruch_bruch(1)",a);
    CTO(BRUCH,"add_apply_bruch_bruch(2)",b);
 
    if (S_B_I(a) != GEKUERZT) goto safe;
    if (S_B_I(b) != GEKUERZT) goto safe;
/*
    SYMCHECK((S_B_I(a) != GEKUERZT),"add_apply_bruch_bruch:(1) not reduced");
    SYMCHECK((S_B_I(b) != GEKUERZT),"add_apply_bruch_bruch:(2) not reduced");
*/
    if (INTEGRALP(S_B_O(a)) && INTEGRALP(S_B_U(a))
        && INTEGRALP(S_B_O(b)) && INTEGRALP(S_B_U(b))   )
        {
 
        c = CALLOCOBJECT();
        GGT(S_B_U(a), S_B_U(b), c);
    
        if (not EINSP(c)) {
            d = CALLOCOBJECT();
            GANZDIV(S_B_U(a),c,d);   /* damit wir der bruch b erweitert */
    
            e = CALLOCOBJECT();
            GANZDIV(S_B_U(b),c,e);   /* dmit wird der bruch a erweitert */
    
            MULT_APPLY(d,S_B_U(b));
            MULT_APPLY(d,S_B_O(b));
            FREESELF(c);
            MULT(S_B_O(a),e,c);
            ADD_APPLY(c,S_B_O(b));
            FREEALL(d);
            FREEALL(e);
            }
        else {
            FREESELF(c);
            MULT(S_B_O(a),S_B_U(b),c);
            MULT_APPLY(S_B_U(a),S_B_O(b));
            ADD_APPLY(c,S_B_O(b));
            MULT_APPLY(S_B_U(a),S_B_U(b));
            }
    
        FREEALL(c);
     
        if (NULLP(S_B_O(b)) ) { FREESELF(b); M_I_I(0,b); }
        else { C_B_I(b,NGEKUERZT); KUERZEN(b); }
        goto ende;
        }
    /* nominator or denominator not integer */
    /* AK 060502 */
safe:
    c = CALLOCOBJECT();
    SWAP(c,b);
    erg += add_bruch_bruch(a,c,b);
    FREEALL(c);
ende:
    ENDR("add_apply_bruch_bruch");
}
 
 




INT add_apply_bruch_scalar(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    OP c;
    CTO(BRUCH,"add_apply_bruch_scalar(1)",a);

    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += add_bruch_scalar(a,c,b);
    FREEALL(c);

    ENDR("add_apply_bruch_scalar");
}

INT add_apply_bruch_integer(a,b) OP a,b;
/* AK 251001 */
{
    INT erg = OK;
    OP c;
    CTO(BRUCH,"add_apply_bruch_integer(1)",a);
    CTO(INTEGER,"add_apply_bruch_integer(2)",b);
 
    c = CALLOCOBJECT();
    MULT_INTEGER(b,S_B_U(a),c);
    

    C_O_K(b,EMPTY);
    B_OU_B(CALLOCOBJECT(),CALLOCOBJECT(),b);

    ADD(c,S_B_O(a),S_B_O(b));
    FREEALL(c);

    COPY(S_B_U(a),S_B_U(b));
    KUERZEN(b);
 
    ENDR("add_apply_bruch_integer");
}


INT add_apply_scalar_bruch(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 050791 V1.3 */
{
    OP c;
    INT erg = OK;
    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += add_bruch_scalar(c,a,b);
    FREEALL(c);
    ENDR("add_apply_scalar_bruch");
}

INT add_apply_integer_bruch(a,b) OP a,b;
/* AK 251001 */
/* not yet optimal, better with ggt */
{
    OP c;
    INT erg = OK;
    CTO(INTEGER,"add_apply_integer_bruch(1)",a);
    CTO(BRUCH,"add_apply_integer_bruch(2)",b);

    c = CALLOCOBJECT();
    MULT_INTEGER(a,S_B_U(b),c);
    ADD_APPLY(c,S_B_O(b));

    FREEALL(c);
    C_B_I(b,NGEKUERZT);
    KUERZEN(b);

    ENDR("add_apply_integer_bruch");
}
 



INT add_apply_bruch(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 190291 V1.2 */ /* AK 050791 V1.3 */
/* a is bruch */
{
    INT erg = OK;
    CTO(BRUCH,"add_apply_bruch(1)",a);

    switch (S_O_K(b)) {
    case BRUCH:
        erg += add_apply_bruch_bruch(a,b);  /* hat kuerzen */
        break;

    case LONGINT:
        erg += add_apply_bruch_scalar(a,b);  /* hat kuerzen */
        break;

    case INTEGER:
        erg += add_apply_bruch_integer(a,b);  /* hat kuerzen */
        break;

    default:
        {
            OP c = callocobject();
            *c = *b;
            C_O_K(b,EMPTY);
            erg += add_bruch(a,c,b); /* hat kuerzen */
            erg += freeall(c);
            break;
        }
    }
    ENDR("add_apply_bruch");
}




INT mult_apply_bruch(a,b) OP a,b;
/* a is BRUCHobject */
/* AK 140290 V1.1 */ /* AK 190291 V1.2 */ /* AK 200891 V1.3 */
{
    OP c;
    INT erg=OK;
    CTO(BRUCH,"mult_apply_bruch(1)",a);

/*CC 260696*/
    if(bruch_not_scalar(a))
        {
        erg += mult_apply(S_B_O(a),b);
        c=callocobject(); 
        erg += copy(b,c); 
        erg += m_ou_b(c,S_B_U(a),b); 
        erg += kuerzen(b);
        erg += freeall(c); 
        goto endr_ende;
        }

                
    switch (S_O_K(b)) {
        case BRUCH: 
            erg += mult_apply(S_B_O(a),S_B_O(b));
            erg += mult_apply(S_B_U(a),S_B_U(b));
            C_B_I(b,NGEKUERZT);
            erg += kuerzen(b);
            break;
    
        case INTEGER:
            erg+= mult_apply_bruch_integer(a,b);
            break;

        case LONGINT:  
            erg+= mult_apply_bruch_longint(a,b);
            break;
    
#ifdef MATRIXTRUE
        case KRANZTYPUS :
        case MATRIX: 
            erg += mult_apply_scalar_matrix(a,b);
            break;
#endif /* MATRIXTRUE */
    
#ifdef MONOMTRUE
        case MONOM: 
            erg += mult_apply_bruch_monom(a,b);
            break;
#endif /* MONOMTRUE */

#ifdef CHARTRUE
        case SYMCHAR:
            erg += mult_apply_scalar_symchar(a,b);
             break;
#endif /* CHARTRUE */

    
#ifdef POLYTRUE
        case SCHUR:
        case POW_SYM:
        case ELM_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case SCHUBERT:
        case GRAL:
        case MONOPOLY:
        case POLYNOM: 
            erg += mult_apply_bruch_polynom(a,b);
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
            erg += mult_apply_bruch_hashtable(a,b);
            break;
 
#endif /* VECTORTRUE */
    
        default:
            c = callocobject();
            erg+=mult(a,b,c);
            erg+=freeself(b);
            *b = *c;
            C_O_K(c,EMPTY);
            erg += freeall(c);
        }
    ENDR("mult_apply_bruch");
}

#endif /* BRUCHTRUE */

#ifdef BRUCHTRUE
INT mult_bruch(a,b,c) OP a,b,c;
/* AK 050789 V1.0 */ /* AK 140290 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"mult_bruch(1)",a);
    CTO(EMPTY,"mult_bruch(3)",c);

    switch( S_O_K(b)) {

    case BRUCH:  
        erg += mult_bruch_bruch(a,b,c);
        break;

#ifdef LONGINTTRUE
    case LONGINT:
        erg += mult_bruch_longint(a,b,c);
        break;
#endif /* LONGINTTRUE */

#ifdef INTEGERTRUE
    case INTEGER: 
        erg += mult_bruch_integer(a,b,c);
        break;
#endif /* INTEGERTRUE */

#ifdef MATRIXTRUE
    case MATRIX: 
        erg += mult_scalar_matrix(a,b,c);
        break;
#endif /* MATRIXTRUE */

#ifdef MONOMTRUE
    case MONOM: 
        erg += mult_scalar_monom(a,b,c);
        break;
#endif /* MONOMTRUE */

    case LAURENT:
        erg += copy(a,c);
        erg += mult(b,S_B_O(c), S_B_O(c));
        break;

#ifdef POLYTRUE
    case POLYNOM: 
        if (
            (has_one_variable(b)) 
            && 
            ((!scalarp(S_B_O(a))) ||(!scalarp(S_B_U(a))))
            )
            {
            OP tp2;
            tp2=callocobject();
            erg += m_ou_b(b,cons_eins,tp2);
            erg += mult_bruch_bruch(a,tp2,c);
            erg += freeall(tp2);
            }
        else
            erg += mult_scalar_polynom(a,b,c);
        goto ende;
    case GRAL:
        erg += mult_scalar_gral(a,b,c);
        goto ende;
#ifdef SCHUBERTTRUE
    case SCHUBERT:
        erg += mult_scalar_schubert(a,b,c);
        goto ende;
#endif
#endif /* POLYTRUE */

#ifdef SQRADTRUE
    case SQ_RADICAL:
        erg += mult_scalar_sqrad(a,b,c);
        goto ende;
#endif /* SQRADTRUE */

#ifdef CYCLOTRUE
    case CYCLOTOMIC:
        erg += mult_scalar_cyclo(a,b,c);
        goto ende;
#endif /* CYCLOTRUE */


#ifdef SCHURTRUE
    case ELM_SYM:
        erg += mult_elmsym_scalar(b,a,c);
        goto ende;
    case HOM_SYM:
        erg += mult_homsym_scalar(b,a,c);
        goto ende;
    case POW_SYM:
        erg += mult_powsym_scalar(b,a,c);
        goto ende;
    case MONOMIAL:
        erg += mult_monomial_scalar(b,a,c);
        goto ende;
    case SCHUR: 
        erg += mult_schur_scalar(b,a,c);
        goto ende;
#endif /* SCHURTRUE */

#ifdef CHARTRUE
    case SYMCHAR: 
        erg += mult_scalar_symchar(a,b,c);
        goto ende;
#endif /* CHARTRUE */

#ifdef VECTORTRUE
    case VECTOR:  
        erg += mult_scalar_vector(a,b,c);
        break;
#endif /* VECTORTRUE */

    default:
        WTO("mult_bruch(2)",b);
        goto ende;
    };
ende:
    ENDR("mult_bruch");
}



INT test_bruch()
/* AK 150290 V1.1 */ /* AK 200891 V1.3 */
{
    OP a= callocobject();
    OP b= callocobject();
    OP c= callocobject();

    printf("test_bruch:scan(a) ");
    scan(BRUCH,a);
    println(a);
    printf("test_bruch:scan(b) ");
    scan(BRUCH,b);
    println(b);
    printf("test_bruch:posp(a) ");
    if (posp(a)) {
        printf(" a ist positiv\n");
    }
    else {
        printf(" a ist nicht positiv\n");
    }
    printf("test_bruch:einsp(a) ");
    if (einsp(a)) {
        printf(" a ist eins\n");
    }
    else {
        printf(" a ist nicht eins\n");
    }

    printf("test_bruch:add(a,b,c) ");
    add(a,b,c);
    println(c);
    printf("test_bruch:mult(a,b,c) ");
    mult(a,b,c);
    println(c);
    printf("test_bruch:kuerzen(c) ");
    kuerzen(c); 
    println(c);
    freeall(a); 
    freeall(b); 
    freeall(c);
    return(OK);
}




INT objectwrite_bruch(f,a) FILE *f; OP a;
/* AK 200690 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(BRUCH,"objectwrite_bruch(2)",a);
    fprintf(f,"%ld\n", (INT)BRUCH);
    erg += objectwrite(f,S_B_O(a));
    erg += objectwrite(f,S_B_U(a)); 
    ENDR("objectwrite_bruch");
}




INT objectread_bruch(f,a) FILE *f; OP a;
/* AK 200690 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    COP("objectread_bruch(1)",f);
    erg += b_ou_b(callocobject(),callocobject(),a);
    erg += objectread(f,S_B_O(a));
    erg += objectread(f,S_B_U(a)); 
    CTO(BRUCH,"objectread_bruch(i)",a);
    erg += kuerzen(a);
    ENDR("objectread_bruch");
}


INT cast_apply_bruch(a) OP a;
/* AK 210294 */
{
    INT erg = OK;
    EOP("cast_apply_bruch(1)",a);
    switch S_O_K(a) {
        case BRUCH:
            break;
        case INTEGER: 
            erg += m_ioiu_b(S_I_I(a), (INT) 1, a);
            break;
        case LONGINT: 
            erg += m_ou_b(a,cons_eins,a);
            break;
        }
    CTO(BRUCH,"cast_apply_bruch(e1)",a);
    ENDR("cast_apply_bruch");
}
#endif /* BRUCHTRUE */



/*
Met dans dg le degre du monopoly mp
*/

INT dg_mp(mp,dg) OP mp,dg;
{
    
    OP z,za=NULL;
    if(not EMPTYP(dg)) freeself(dg);
    z=mp;
    while(z !=NULL)
    {
        za=z;
        z=S_L_N(z);
    }
    copy(S_PO_S(za),dg);
    return(OK);
}


/*
Met dans ld le coefficient du terme maximal  du monopoly mp
*/

INT ldcf_mp(mp,ld) OP mp,ld;
{
    
    OP z,za=NULL;
    if(not EMPTYP(ld)) freeself(ld);
    z=mp;
    while(z !=NULL)
    {
        za=z;
        z=S_L_N(z);
    }
    copy(S_PO_K(za),ld);
    return(OK);
}


INT t_POLYNOM_MONOPOLY(a,b) OP a,b;
/* CC */
/* take only the first variable */
{
    OP z,hh;
    INT erg = OK;
    CTO(POLYNOM,"t_POLYNOM_MONOPOLY(1)",a);
    CE2(a,b,t_POLYNOM_MONOPOLY);

    init(MONOPOLY,b);
    if (not NULLP(a)) {
        z=a;
        while(z!=NULL)
            {
            hh=callocobject();
            erg += m_sk_mo(S_V_I(S_PO_S(z),0L),S_PO_K(z),hh);
            insert(hh,b,add_koeff,NULL);
            z=S_PO_N(z);
            }
        }
    ENDR("t_POLYNOM_MONOPOLY");
}


/*
n est de type INTEGER
po est de type POLYNOM ou MONOPOLY
pg est le pgcd de n et des coefficients de po
Retourne ERROR si le pgcd n'est pas definie
*/

INT gcd_int_po(n,po,pg) OP n,po,pg;
{
    OP z,tmp,k;

    if(not EMPTYP(pg)) freeself(pg);
    z=po;
    if(NULLP(z)){ copy(n,pg);return(OK);}
    tmp=callocobject();
    copy(n,tmp);
    while(z!=NULL)
    {
        k=S_PO_K(z);
        if(S_O_K(k)==BRUCH)
            krz(k);
        if(S_O_K(k)!=INTEGER)
            return ERROR;
        ggt(tmp,k,tmp);
        z=S_L_N(z);
    }
    copy(tmp,pg);
    freeall(tmp);
    return(OK);
}

/*
Calcule le pgcd de a et b qui sont de type quelconque.
Retourne ERROR si le pgcd de a et b n'existe pas
*/

INT pgcd(a,b,c) OP a,b,c;
{
    OP aa,bb,nb;
    if(S_O_K(a)==BRUCH) krz(a);
    if(S_O_K(b)==BRUCH) krz(b);
    if((S_O_K(a)==BRUCH)||(S_O_K(b)==BRUCH))
        return ERROR;
    if((S_O_K(a)==INTEGER)&&(S_O_K(b)==INTEGER))
    {
        ggt(a,b,c);return(OK);
    }
    if(NULLP(a))
    {
        if(has_one_variable(b)==TRUE)
        {
            copy(b,c);return(OK);
        }
        else
            return ERROR;
    }
    if(NULLP(b))
    {
        if(has_one_variable(a)==TRUE)
        {
            copy(a,c);return(OK);
        }
        else
            return ERROR;
    }
    if(scalarp(a))
    {
        copy(a,c);
        return(OK);
    }
    if(scalarp(b))
    {
        copy(b,c);
        return(OK);
    }
    
    if(S_O_K(a)==POLYNOM)
    {
        nb=callocobject();
        numberofvariables(a,nb);
        if(S_I_I(nb)>1L)
        {
            freeall(nb);
            return(ERROR);
        }
        else
        {
            freeall(nb);
            aa=callocobject();
            t_POLYNOM_MONOPOLY(a,aa);
        }
    }    
    else
    {
        aa=callocobject();
        copy(a,aa);
    }

    if(S_O_K(b)==POLYNOM)
    {
        nb=callocobject();
        numberofvariables(b,nb);
        if(S_I_I(nb)>1L)
        {
            freeall(nb);
            return(ERROR);
        }
        else
        {
            freeall(nb);
            bb=callocobject();
            t_POLYNOM_MONOPOLY(b,bb);
        }
    }    
    else
    {
        bb=callocobject();
        copy(b,bb);
    }
    ggt_mp(aa,bb,c);
    freeall(aa);freeall(bb);
    return OK;
}






/*
Lance le pgcd de 2 polynomes non nuls de type MONOPOLY
Computes the gcd of 2 MONOPOLY objects
*/

static INT ggt_mp(a,b,c) OP a,b,c;
{
    OP dg1,dg2;
    INT dgi1,dgi2;
    dg1=callocobject();dg2=callocobject();
    dg_mp(a,dg1); dg_mp(b,dg2);
    dgi1=S_I_I(dg1); dgi2=S_I_I(dg2);
    if(dgi1==0)
        copy(a,c);
    else if(dgi2==0)
        copy(b,c);
    else if(dgi1>dgi2)
        gcd_mp(a,b,c);
    else
        gcd_mp(b,a,c);
    freeall(dg1);freeall(dg2);
    return(OK);
}


/*
Calcule le pgcd de 2 polynomes  de type MONOPOLY a et b
degre(a)>degre(b)>0
Algo d'Euclide non optimise
*/

    
INT gcd_mp_lent(a,b,c) OP a,b,c;
{
    OP aa,bb,qp,rp;
    aa=callocobject(); qp=callocobject(); rp=callocobject(); bb=callocobject();
    copy(a,aa);copy(b,bb);
    while(1)
    {
        quores_monopoly(aa,bb,qp,rp);
        if(nullp_monopoly(rp)) break;
        copy(bb,aa);
        copy(rp,bb);
    }
    copy(bb,c);
    freeall(bb);freeall(aa);
    return OK;
}



/*
Calcule le pgcd de 2 polynomes de type MONOPOLY a et b
degre(a)>degre(b)>0
*/

INT gcd_mp(a,b,c) OP a,b,c;
{
    OP av,nv,ld,dlt,tp,aa,bb,qp,rp;
    INT avi,nvi,dlti;
    INT erg = OK;
    CTO(MONOPOLY,"gcd_mp(1)",a);
    CTO(MONOPOLY,"gcd_mp(2)",b);

    tp=callocobject(); aa=callocobject(); bb=callocobject();
    av=callocobject(); nv=callocobject(); ld=callocobject();
    dlt=callocobject(); qp=callocobject(); rp=callocobject();
    dg_mp(a,av);avi=S_I_I(av);
    dg_mp(b,nv);nvi=S_I_I(nv);
    copy(a,aa);copy(b,bb);
    while(nvi>0)
    {
        dlti=avi-nvi+1;
        M_I_I(dlti,dlt);
        ldcf_mp(b,ld);
        hoch(ld,dlt,tp);
        MULT_APPLY(tp,aa);
        FREESELF(qp);
        FREESELF(rp);
        quores_monopoly(aa,bb,qp,rp);

        if(nullp_monopoly(rp))  break;
        else
        {
            copy(bb,aa);
            copy(rp,bb);
            avi=nvi;
            dg_mp(bb,nv);
            nvi=S_I_I(nv);
        }
    }
    copy(bb,c);
    freeall(tp); freeall(aa);
    freeall(ld); freeall(dlt);
    freeall(bb); freeall(av);
    freeall(nv);
    freeall(qp); /* AK 130297 */
    freeall(rp); /* AK 130297 */
    ENDR("gcd_mp");
}    


/*
mp est de type MONOPOLY.
Renvoie TRUE si mp est une constante 
FALSE sinon
*/

INT mp_is_cst(mp) OP mp;
{
    OP z;
    INT i,boo;
    z=mp;i=0L;boo=0L;
    while(z!=NULL)
    {
        if(i > 0L) return FALSE;
        if(S_I_I(S_PO_S(z))==0L)
            boo=1L;
        z=S_L_N(z);
        i++;
    }
    if(boo==1L) return TRUE;
    else return FALSE;
}

/*Simplifie fc3
renvoie ERROR si fc3 est une fraction rationnelle avec 0 au denominateur
*/

INT bruch_not_scalar(a) OP a;
/*
Returns 1 if a is built with MONOPOLY or POLYNOM object.
Returns 0 if not.
*/
{
        INT tp1,tp2;
        if(S_O_K(S_B_O(a))==MONOPOLY || S_O_K(S_B_O(a))==POLYNOM
                ||S_O_K(S_B_U(a))==MONOPOLY || S_O_K(S_B_U(a))==POLYNOM)
                return 1;
        tp1=tp2=0L;
        if(
             (S_O_K(S_B_O(a))==BRUCH && bruch_not_scalar(S_B_O(a)))
                || 
             (S_O_K(S_B_U(a))==BRUCH && bruch_not_scalar(S_B_U(a))) 
           ) return 1;
        return 0;
}


/*
ma0 est une matrice de polynomes, fractions rationnelles, entiers...
Transforme les types MONOPOLY de ma0
 en type POLYNOM dans ma    
*/

INT t_MA_MONOPOLY_MA_POLYNOM(ma0,ma) OP ma0, ma;
{
    INT i,j;
    OP tp,ttp1,tp1,ttp2,tp2;

    m_ilih_m(S_M_LI(ma0),S_M_HI(ma0),ma);
    for(i=0L;i<S_M_LI(ma0);i++)
        for(j=0L;j<S_M_LI(ma0);j++)
        {
            tp=S_M_IJ(ma0,i,j);
            if(S_O_K(tp)==MONOPOLY)
            {
                tp=callocobject();
                t_MONOPOLY_POLYNOM(S_M_IJ(ma0,i,j),tp);
                copy(tp,S_M_IJ(ma,i,j));
                freeall(tp);
            }
            else if (S_O_K(tp)==BRUCH)
            {
                tp1=S_B_O(tp); ttp1=callocobject();
                if(S_O_K(tp1)==MONOPOLY)
                {
                    t_MONOPOLY_POLYNOM(tp1,ttp1);
                }
                else copy(tp1,ttp1);
                tp2=S_B_U(tp); ttp2=callocobject();
                if(S_O_K(tp2)==MONOPOLY)
                {
                    t_MONOPOLY_POLYNOM(tp2,ttp2);
                }
                else copy(tp2,ttp2);
                b_ou_b(ttp1,ttp2,S_M_IJ(ma,i,j));
            }
            else copy(tp,S_M_IJ(ma,i,j));
        }
    return OK;
}

/*
met 0 a la place de empty_list dans la matrice ma
*/

INT en_forme(ma) OP ma;
{
    INT i,j;
    INT erg = OK;
    CTO(MATRIX,"en_forme(1)",ma);

    for(i=0L;i<S_M_LI(ma);i++)
        for(j=0L;j<S_M_LI(ma);j++)
            if(EMPTYP(S_M_IJ(ma,i,j)))
                M_I_I(0L,S_M_IJ(ma,i,j));
            else if (empty_listp(S_M_IJ(ma,i,j)))
                erg += m_i_i(0L,S_M_IJ(ma,i,j));
            else if (NULLP(S_M_IJ(ma,i,j)))
                erg += m_i_i(0L,S_M_IJ(ma,i,j));
    ENDR("en_forme");
}



INT krz(fc3) OP fc3;
{
    OP oo,uu,pg,tp,r,dgu,dgo,dgpg=NULL,tpu,tpo,tmp;
    INT erg = OK;

    if(S_O_K(fc3)!=BRUCH) return OK;

    oo=S_B_O(fc3); 
    uu=S_B_U(fc3);

    SYMCHECK(NULLP(uu)," krz:zero nominator");

    if(NULLP(oo))
    {
        FREESELF(fc3);
        M_I_I(0L,fc3);
        goto endr_ende;
    }

    if(
        ((S_O_K(oo)==INTEGER)||(S_O_K(oo) == LONGINT))
        &&
        ((S_O_K(uu)==INTEGER)||(S_O_K(uu) == LONGINT))
      )
    {
        erg += kuerzen_integral(fc3);
        goto endr_ende;
    }

/* CC  28/09/95*/
    if(S_O_K(oo)==BRUCH) krz(oo);
    if(S_O_K(uu)==BRUCH) krz(uu);
    if((S_O_K(oo)==BRUCH)||(S_O_K(uu)==BRUCH))
    {
        tp=callocobject();
        if(S_O_K(uu)==BRUCH)
            m_ou_b(S_B_U(uu),S_B_O(uu),tp);
        else
            m_ou_b(cons_eins,uu,tp);
        kuerzen(tp);
        mult_apply(oo,tp);
        copy(tp,fc3);
        freeall(tp);
        return(krz(fc3));
    }        

    if(scalarp(uu))
    {
        tp=callocobject();
        div(oo,uu,tp);
        copy(tp,fc3);
        freeall(tp);
        sp_br(fc3);
        return(OK);
    }
    if(scalarp(oo))
    {
        tp=callocobject();
        div(uu,oo,tp);

/*CC 28/09/95*/
        if(S_O_K(tp)==BRUCH)
            m_ou_b(S_B_U(tp),S_B_O(tp),fc3);
        else
            m_ou_b(cons_eins,tp,fc3);
        sp_br(fc3);
        freeall(tp);

        return(OK);
    }
    if (S_O_K(uu) == LAURENT)
        {
        tpo=callocobject();
        tp=callocobject();
        copy(oo,tp);
        t_LAURENT_OBJ(uu,tpo);
        m_ou_b(tp,tpo,fc3);
        freeall(tpo);
        freeall(tp);
        krz(fc3);
        return(OK);
        }

    if (S_O_K(oo) == LAURENT)
        {
        tpo=callocobject();
        tp=callocobject();
        copy(uu,tp);
        t_LAURENT_OBJ(oo,tpo);
        m_ou_b(tpo,tp,fc3);
        freeall(tpo);
        freeall(tp);
        krz(fc3);
        return(OK);
        }

    pg=callocobject();
    if(pgcd(oo,uu,pg)==ERROR) return ERROR;

/*CC 28/09/95*/
    if(scalarp(pg))
    {
        sp_br(fc3);
        freeall(pg);
        return(OK);
    }
    if(S_O_K(pg)==MONOPOLY)
    {
        dgpg=callocobject();
        degree_monopoly(pg,dgpg);
        if(nullp(dgpg))
        {
            sp_br(fc3);
            freeall(pg);
            freeall(dgpg);
            return(OK);
        }
    }
    if(S_O_K(pg)==POLYNOM)
    {
        dgpg=callocobject();
        degree_polynom(pg,dgpg);
        if(NULLP(dgpg)==TRUE)
        {
            sp_br(fc3);
            freeall(dgpg);
            freeall(pg);
            return OK;
        }
    }

    tpu=callocobject();
    if(S_O_K(uu)==POLYNOM)
        t_POLYNOM_MONOPOLY(uu,tpu);
    else
        copy(uu,tpu);
    tpo=callocobject();
    if(S_O_K(oo)==POLYNOM)
        t_POLYNOM_MONOPOLY(oo,tpo);
    else
        copy(oo,tpo);

    dgu=callocobject();
    degree_monopoly(tpu,dgu);
    if(S_I_I(dgu)==S_I_I(dgpg))
    {
        freeself(fc3);
        r=callocobject(); 
        tmp=callocobject();
        quores_monopoly(tpo,tpu,tmp,r);
        copy(tmp,fc3);

        freeall(tmp);    
        freeall(r);freeall(pg);
        freeall(tpo);freeall(tpu);
        freeall(dgu);freeall(dgpg);
        return(OK);
    }
    
    dgo=callocobject();
    degree_monopoly(tpo,dgo);
    if(S_I_I(dgo)==S_I_I(dgpg))
    {
        r=callocobject(); 
        tmp=callocobject();
        quores_monopoly(tpu,tpo,tmp,r);

        div(cons_eins,tmp,fc3);
        C_B_I(fc3,GEKUERZT);

        freeall(r);freeall(pg);freeall(tmp);
        freeall(dgu);freeall(dgo);freeall(dgpg);
        freeall(tpu);freeall(tpo);
        return(OK);
    }
    r=callocobject();
    FREESELF(oo);
    quores_monopoly(tpo,pg,oo,r);
    FREESELF(uu);
    FREESELF(r);
    quores_monopoly(tpu,pg,uu,r);

/*CC 28/09/95*/
    sp_br(fc3);

    freeall(r);freeall(dgo);freeall(dgu);freeall(dgpg);
    freeall(tpo);freeall(tpu);freeall(pg);
    ENDR("internal routine:krz");
}

/*
CC 28/09/95
If br is a bruch with monopoly or polynom in the numerator or denominator.
Try to remove bruch in the numerator and denominator
*/
INT sp_br(br) OP br;
{
    OP cf,tp1,tp2;
    if(S_O_K(br)!=BRUCH)return OK;
    if((S_O_K(S_B_O(br))!=MONOPOLY && S_O_K(S_B_O(br))!=POLYNOM)
    ||(S_O_K(S_B_U(br))!=MONOPOLY && S_O_K(S_B_U(br))!=POLYNOM))
            {
            C_B_I(br,GEKUERZT);
            return OK;
            }
    cf=callocobject();
    lowcf_br(br,cf);
    if(comp(cons_eins,cf)!=0L)
    {
        tp1=callocobject();tp2=callocobject();
        div(S_B_O(br),cf,tp1);
        div(S_B_U(br),cf,tp2);
        m_ou_b(tp1,tp2,br); 
        freeall(tp1);freeall(tp2);
    }
    freeall(cf);
    C_B_I(br,GEKUERZT);
    return OK;
}

/*
CC 28/09/95
mp is a polynom or a monopoly with scalar coefficient.
cf will be the smallest coefficient different from 0 in mp.
*/

static INT lowcf_mp(mp,cf) OP mp,cf;
{
        OP z;
        INT boo;
        if(not EMPTYP(cf)) freeself(cf);
        z=mp;
        boo=0L;
        while(z!=NULL)
        {
                if(NULLP(S_PO_K(z))==FALSE)
                {
                        if(boo==0L)
                        {
                                copy(S_PO_K(z),cf);

                                boo=1L;
                        }
                        else if(lt(S_PO_K(z),cf)==TRUE)
                        {
                                copy(S_PO_K(z),cf);
                        }
                }
                z=S_L_N(z);
        }
        return OK;
}

/*
CC 28/09/95
br is a bruch with monopoly or polynom in the numerator or denominator.
cf will be the smallest coefficient different from 0 in br.
*/

static INT lowcf_br(br,cf) OP br,cf;
{
    OP cf1,cf2;
    INT erg = OK;
    CTO(BRUCH,"lowcf_br(1)",br);
    cf1=callocobject();
    cf2=callocobject();
    erg += lowcf_mp(S_B_O(br),cf1);
    erg += lowcf_mp(S_B_U(br),cf2);
    if(lt(cf1,cf2)==TRUE)
        erg += copy(cf1,cf);
    else
        erg += copy(cf2,cf);
    FREEALL(cf1);
    FREEALL(cf2);
    ENDR("internal func: lowcf_br");
}

