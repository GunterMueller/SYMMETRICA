
/* SYMMETRICA sb.c */
#include "def.h"
#include "macro.h"

#ifdef SCHUBERTTRUE
static INT algorithmus2();
static INT algorithmus3();
static INT algorithmus4();
static INT algorithmus5();
static INT algorithmus6();
static INT pol_sch_alg01();
static INT co_L9();
#endif /* SCHUBERTTRUE */

#ifdef SCHUBERTTRUE

INT cast_apply_schubert(a) OP a;
/* tries to transform the object a into a SCHUBERT object */
/* AK 170207 V3.0 */
{
    INT erg = OK;
    COP("cast_apply_schubert(1)",a);
    switch (S_O_K(a)) {
        case BRUCH:
        case LONGINT:
        case INTEGER:
            erg += m_scalar_schubert(a,a);
            break;
        default:
            erg += WTO("cast_apply_schubert",a);
            break;
            }
    ENDR("cast_apply_schubert");
}

INT m_scalar_schubert(a,b) OP a,b;
/* AK 141099 */
/* input scalar = INTGEER, BRUCH, LONGINT,... the type is not checked */
/* output schubert polynomial labeled by identy perm */
{
    INT erg = OK;
    CE2(a,b,m_scalar_schubert);
    erg += b_skn_sch(callocobject(),callocobject(),NULL,b);
    erg += first_permutation(cons_zwei,S_SCH_S(b));
    COPY(a,S_SCH_K(b));
    ENDR("m_scalar_schubert");
}

INT maxdegree_schubert(a,b) OP a,b;
/* AK 231194 */
/* AK 190598 V2.0 */
/* b: maximal degree of the permutations 
    labelling the schubert polynomials  (INTEGER object) */
{
    OP z;
    INT erg = OK;
    CTO(SCHUBERT,"maxdegree_schubert",a);
    CE2(a,b,maxdegree_schubert);
    erg += m_i_i((INT)0,b);
    z = a;
    while((z != NULL)&&(S_SCH_S(z) != NULL))
        {
        if (S_SCH_SLI(z) > S_I_I(b))
            M_I_I(S_SCH_SLI(z),b);
        z = S_SCH_N(z);
        }
    ENDR("maxdegree_schubert");
}

INT einsp_schubert(a) OP a;
/* AK 200691 V1.2 */ /* AK 200891 V1.3 */
{
    if (einsp(S_SCH_S(a)))
        if (einsp(S_SCH_K(a)))
            if (S_SCH_N(a) == NULL) return TRUE;
    return FALSE;
}
#endif /* SCHUBERTTRUE */


INT schubertp(a) OP a;
/* AK 200891 V1.3 */
{
    if (s_o_k(a) == SCHUBERT) return TRUE;
    else return FALSE;
}

#ifdef SCHUBERTTRUE
INT m_lehmer_schubert_qpolynom(a,b) OP a,b;
/* AK 131097 */
{
    INT erg = OK; /* AK 191191 */
    OP p;
    CTTO(INTEGERVECTOR,VECTOR,"m_lehmer_schubert_qpolynom(1)",a);
    
    p = CALLOCOBJECT();
    erg += lehmercode(a,p);
    erg += m_perm_schubert_qpolynom(p,b);
    FREEALL(p);
    ENDR("m_lehmer_schubert_qpolynom");
}

INT m_lehmer_schubert_monom_summe(a,b) OP a,b;
/* AK 061288 */ /* AK 240789 V1.0 */ /* AK 190690 V1.1 */ /* AK 090891 V1.3 */
/* AK 190598 V2.0 */
/* a and b may be equal */
{
    INT erg = OK; /* AK 191191 */
    OP p;
    CTTO(VECTOR,INTEGERVECTOR,"m_lehmer_schubert_monom_summe(1)",a);

    p = callocobject();
    erg += lehmercode(a,p);
    erg += m_perm_schubert_monom_summe(p,b);
    erg += freeall(p);
    ENDR("m_lehmer_schubert_monom_summe");
}


#endif /* SCHUBERTTRUE */

INT m_perm_schubert_monom_summe(perm,res) OP perm,res;
/* Eingabe: PERMUTATION als label des Schubertpolynoms */
/* Ausgabe: POLYNOM */
/* 020588 */ /* AK 240789 V1.0 */ /* AK 120790 V1.1 */ /* AK 090891 V1.3 */
{
    OP vorfaktor;
    INT erg = ERROR;
    /* das monom, mit dem das ergebnis einer einzelnen
        rekursion multipliziert werden muss */
    /* beim start = [0,0,0,0,....,0] */
#ifdef SCHUBERTTRUE
    erg = OK;
    CTO(PERMUTATION,"m_perm_schubert_monom_summe(1)",perm);
    CE2(perm,res,m_perm_schubert_monom_summe);
        
    if (einsp(perm)) /* AK 191191 */
        {
        erg += m_scalar_polynom(cons_eins,res);
        goto endr_ende;
        }

    vorfaktor = CALLOCOBJECT();
    erg += m_il_nv(S_P_LI(perm),vorfaktor);
    C_O_K(vorfaktor,INTEGERVECTOR);
    /* vorfaktor ist nun initialisiert */
    erg += algorithmus2(vorfaktor,0L,S_P_LI(perm)-1L,perm,res);
    /* die rekursion wird aufgerufen */
    FREEALL(vorfaktor);
#endif /* SCHUBERTTRUE */
    ENDR("m_perm_schubert_monom_summe");
}


#ifdef SCHUBERTTRUE
INT m_perm_schubert_qpolynom(perm,res) OP perm,res;
/* 020588 */ /* AK 240789 V1.0 */ /* AK 040190 V1.1 */ /* AK 090891 V1.3 */
{
    INT erg = OK;
    INT w,i;
    OP c;
    CTO(PERMUTATION,"m_perm_schubert_qpolynom(1)",perm);
    c = callocobject();
    erg += lehmercode(perm,c);
    w = 0;
    for (i=0;i<S_V_LI(c);i++)
        w += S_V_II(c,i) * (i+1);
    erg += m_il_nv(  w , c);
    if (w == (INT)0)
        erg += m_skn_po(cons_null,cons_eins,NULL,res);
    else
        {
        erg += algorithmus4(0L,0L,S_P_LI(perm)-1L,perm,c);
        for (i=0;i<S_V_LI(c);i++)
            if (gt(S_V_I(c,i) ,cons_null) )
                {
                erg += b_skn_po(callocobject(),callocobject(),NULL,res);
                erg += copy(S_V_I(c,i) ,S_PO_K(res));
                erg += m_il_v((INT)1, S_PO_S(res));
                M_I_I(i,S_PO_SI(res,(INT)0));
                i++;
                break;
                }
        for (;i<S_V_LI(c)-1;i++)
            if (gt(S_V_I(c,i) ,cons_null) )
                {
                C_L_N(res,callocobject());
                erg += b_skn_po(callocobject(),callocobject(),NULL,S_L_N(res));
                res = S_L_N(res);
                erg += copy(S_V_I(c,i) ,S_PO_K(res));
                erg += m_il_v((INT)1, S_PO_S(res));
                M_I_I(i,S_PO_SI(res,(INT)0));
                }
        if (i<S_V_LI(c))
        if (gt(S_V_I(c,i) ,cons_null) )
            {
            C_L_N(res,callocobject());
            erg += b_skn_po(callocobject(),callocobject(),NULL,S_L_N(res));
            res = S_L_N(res);
            erg += copy(S_V_I(c,i) ,S_PO_K(res));
            erg += m_il_v((INT)1, S_PO_S(res));
            M_I_I(i,S_PO_SI(res,(INT)0));
            }
        }

    erg += freeall(c);
    ENDR("m_perm_schubert_qpolynom");
}



INT m_perm_schubert_dimension(perm,res) OP perm,res;
/* 020588 */ /* AK 240789 V1.0 */ /* AK 120790 V1.1 */ /* AK 090891 V1.3 */
/* AK 260198 V2.0 */
/* 
   input: labeling permutation
   output: number of terms = evaluation a_i = 1
*/
{
    INT erg = OK;
    CTO(PERMUTATION,"m_perm_schubert_dimension(1)",perm);
    CE2(perm,res,m_perm_schubert_dimension);
    M_I_I(0,res);
    erg += algorithmus3(0,perm,res);
    ENDR("m_perm_schubert_dimension");
}




INT t_POLYNOM_SCHUBERT(pol,sch) OP pol,sch;
/* AK 240789 V1.0 */ /* AK 131290 V1.1 */
/* AK 150291 V1.2 */ /* AK 090891 V1.3 */
/* AK 260198 V2.0 */
/*     input: polynom
    output: same in the base of schubert polynomials
*/
{
    OP p; /* wird copie des polynoms */
    INT erg = OK;
    if (S_O_K(pol) == MONOM) /* AK 240999 */
        {
        p = callocobject();
        erg += m_sn_l(pol,NULL,p);
        C_O_K(p,POLYNOM);
        erg += freeself(sch);
        goto nn;
        }
    CTO(POLYNOM,"t_POLYNOM_SCHUBERT",pol);
    CE2(pol,sch,t_POLYNOM_SCHUBERT);
    if (EMPTYP(pol))
        goto endr_ende;
    if (nullp(pol))
        {
        erg += m_scalar_schubert(cons_null,sch);
        goto endr_ende;
        }

    p = callocobject();
    erg += copy_polynom(pol,p);
nn:
    erg += pol_sch_alg01(p,sch);
    erg += freeall(p);
    ENDR("t_POLYNOM_SCHUBERT");
}



static INT pol_sch_alg01 (p,s) OP p,s;
/* AK 240789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    OP l,res,schub;
    INT i,j;
    INT erg = OK;

pol_sch_alg01l2:
    CTO( POLYNOM,"pol_sch_alg01",p);
    l = callocobject();
    res = callocobject();
    schub = callocobject();

    copy(S_PO_S(p),l);
    if (
        (S_O_K(l) != VECTOR) && (S_O_K(l) != INTEGERVECTOR)
       )
    {
        debugprint(l);
        erg +=  error("pol_sch_alg01: not vectortype in p");
        goto endr_ende;
    }

pol_sch_alg01l1:
    for (i=0L,j=S_V_LI(l)-1L;i<S_V_LI(l);i++,j--)
        if(S_V_II(l,i) > j)
        {
            inc_vector(l);
            M_I_I(0L,S_V_I(l,S_V_LI(l)-1L));
            goto pol_sch_alg01l1;
        }
    /* nun ist l ein lehmercode */

    erg += b_skn_sch(callocobject(),callocobject(),NULL,schub);
    erg += copy(S_PO_K(p),S_SCH_K(schub));
    erg += lehmercode(l,S_SCH_S(schub));



    if (not EMPTYP(res))
        erg += freeself(res);
    erg += m_lehmer_schubert_monom_summe(l,res);
    erg += mult_apply(S_PO_K(p),res);
    erg += sub(p,res,p);
    insert(schub,s,NULL,comp_monomvector_monomvector);
    erg += freeall(res);
    erg += freeall(l);
    if (not EMPTYP(p))
        if (not empty_listp(p)) goto pol_sch_alg01l2;
    ENDR("internal:pol_sch_alg01");
}


static INT algorithmus2(vorfaktor,alphabetindex,stufe,perm,res)
    OP vorfaktor; /* ist ein monom, d.h. vector */
/* bsp [0,1,0] == b^2 */
/* damit wird das ergebnis dieser rekursion 
        multipliziert und in res eingefuegt */
    INT alphabetindex;
/* ist der start des alphabets a==0 */
/* d.h. wird nur noch im alphabet b,c,d, ..
        gerechnet so ist dies =1 */
    INT stufe; /* der exponent des Vorfaktors */
    OP perm; /* die permutation zu der berechnet wird */
    OP res; /* das globale ergebnis */
/* AK 020588 */ /* AK 081188 */ /* AK 240789 V1.0 */ /* AK 201189 V1.1 */
/* AK 090891 V1.3 */
{
    INT i,erg=OK;
    CTO(PERMUTATION,"algorithmus2(1)",perm);
    CTTO(VECTOR,INTEGERVECTOR,"algorithmus2(2)",vorfaktor);
    if (S_V_LI(vorfaktor) == 0L)
        return error("algorithmus2:vorfaktor == 0");

    if (S_P_LI(perm) == 2L)
    /* ende des algorithmus */
    {
        OP monom = callocobject();
        b_skn_po(callocobject(),callocobject(),NULL,monom);
        M_I_I(1L,S_PO_K(monom));
        copy(vorfaktor,S_PO_S(monom));
        /* das monom ist nun fertig initialisiert */

        if (S_P_II(perm,0L) == 2L)
            INC(S_PO_SI(monom,alphabetindex));
        /* der vorfaktor wird noch mit dem i-ten
            buchstaben multipliziert falls perm = [2,1] */
        insert(monom,res,add_koeff,comp_monomvector_monomvector);
        /* einfuegen des ergebnis in das globale ergebnis */
        return OK;
    }


    if (S_P_II(perm,0L) == S_P_LI(perm)) /* nun die rekursion */
    {
        OP neuperm = callocobject();
        OP neufaktor = callocobject();

        b_ks_p(VECTOR,callocobject(),neuperm);
        m_il_v(S_P_LI(perm)-1L,S_P_S(neuperm));
        for(i=0L;i<S_P_LI(neuperm);i++)
            M_I_I(S_P_II(perm,i+1L),S_P_I(neuperm,i));
        /* es wurde die permutation um das erste element
        welches das groesste war gekuerzt, hier wurde
        ausgenutzt 
        z.B X_634215 = a^6 X_34215(b,c,d,e,f)
        diese multiplikation folgt nun
        */

        copy_integervector(vorfaktor,neufaktor);
        M_I_I(stufe,S_V_I(neufaktor,alphabetindex));
        algorithmus2(    neufaktor,alphabetindex+1,
            S_P_LI(neuperm)-1,neuperm,res);
        FREEALL(neufaktor);
        FREEALL(neuperm);
        return OK;
    }
    else    {    /* falls keine rekursion im alphabet */
        INT maximal = S_P_LI(perm)+1L;
        OP neuperm = callocobject();
        for (i=1L;i<S_P_LI(perm);i++)
            if (    (S_P_II(perm,i) < maximal)&&
                (S_P_II(perm,i) > S_P_II(perm,0L)))
            {
            copy(perm,neuperm);
            maximal = S_P_II(perm,i);
            M_I_I(S_P_II(perm,0L),S_P_I(neuperm,i));
            M_I_I(S_P_II(perm,i),S_P_I(neuperm,0L));

            algorithmus2(vorfaktor,alphabetindex,
                    stufe-1L,neuperm,res);
            };
        freeall(neuperm);
        return OK;
    }
    ENDR("algorithmus2");
}



static INT algorithmus4(exponent,alphabetindex,stufe,perm,result)
    INT exponent; /* exponent zur q-specialisierung */
    /* bsp [0,1,0] == b^2 */
    INT alphabetindex; /* ist der startdes alphabets a==0 */
    INT stufe; /* der exponent des Vorfaktors */
    OP perm; /* die permutation zu der berechnet wird */
    OP result;
/* AK 020588 */ /* AK 240789 V1.0 */
/* AK 170190 V1.1 */ /* aendern monom nicht mehr integer sondern vector */
/* AK 090891 V1.3 */
{
    if (S_P_LI(perm) == 2L)    /* ende des algorithmus */
    {
        if (S_P_II(perm,0L) == 2L)
            inc(S_V_I(result,exponent+alphabetindex));
        else
            inc(S_V_I(result,exponent));
        return OK;
    }

    if (S_P_II(perm,0L) == S_P_LI(perm)) /* nun die rekursion */
    {
        INT i;
        DEC_INTEGER(S_P_L(perm));
        for(i=0L;i<S_P_LI(perm);i++)
            M_I_I(S_P_II(perm,i+1L),S_P_I(perm,i));
        algorithmus4(exponent + stufe*alphabetindex ,alphabetindex+1L,
            S_P_LI(perm)-1L,perm,result);
        for(i=S_P_LI(perm);i>0;i--)
            M_I_I(S_P_II(perm,i-1),S_P_I(perm,i));
        INC_INTEGER(S_P_L(perm));
        M_I_I(S_P_LI(perm),S_P_I(perm,(INT)0));
        return OK;
    }
    else    {
        INT i;
        INT maximal = S_P_LI(perm)+1L;
        for (i=1L;i<S_P_LI(perm);i++)
            if (    (S_P_II(perm,i) < maximal)&&
                (S_P_II(perm,i) > S_P_II(perm,0L)))
            {
                /*
                OP neuperm = callocobject();
                copy_permutation(perm,neuperm);
                maximal = S_P_II(perm,i);
                M_I_I(S_P_II(perm,0L),S_P_I(neuperm,i));
                M_I_I(S_P_II(perm,i),S_P_I(neuperm,0L));

                algorithmus4(exponent,alphabetindex,
                    stufe-1L,neuperm,result);
                freeall(neuperm);
                */
                maximal = S_P_II(perm,i);
                M_I_I(S_P_II(perm,0L),S_P_I(perm,i));
                M_I_I(maximal,S_P_I(perm,0L));
                algorithmus4(exponent,alphabetindex,
                    stufe-1L,perm,result);
                M_I_I(S_P_II(perm,i),S_P_I(perm,0L));
                                M_I_I(maximal,S_P_I(perm,i));
            };
        return(OK);
    }
}




static INT algorithmus3(alphabetindex,perm,result)
    INT alphabetindex; /* ist der startdes alphabets a==0 */
    OP perm; /* di epermutation zu der berechnet wird */
    OP result;
/* AK 020588 */
/* AK 240789 V1.0 */ /* AK 191190 V1.1 */
/* AK 090891 V1.3 */
{
    if (S_P_LI(perm) == 2L)    /* ende des algorithmus */
        return inc(result);

    if (S_P_II(perm,0L) == S_P_LI(perm)) /* nun die rekursion */
    {
        OP neuperm = callocobject();
        INT i;

        b_ks_p(VECTOR,callocobject(),neuperm);
        m_il_v(S_P_LI(perm)-1L,S_P_S(neuperm));
        for(i=0L;i<S_P_LI(neuperm);i++)
            M_I_I(S_P_II(perm,i+1L),S_P_I(neuperm,i));
        algorithmus3(alphabetindex+1L,neuperm,result);
        freeall(neuperm);
        return(OK);
    }
    else    {
        INT i;
        INT maximal = S_P_LI(perm)+1L;
        for (i=1L;i<S_P_LI(perm);i++)
            if (    (S_P_II(perm,i) < maximal)&&
                (S_P_II(perm,i) > S_P_II(perm,0L)))
            {
                OP neuperm = callocobject();
                copy(perm,neuperm);
                maximal = S_P_II(perm,i);
                M_I_I(S_P_II(perm,0L),S_P_I(neuperm,i));
                M_I_I(S_P_II(perm,i),S_P_I(neuperm,0L));

                algorithmus3(alphabetindex,neuperm,result);
                freeall(neuperm);
            };
        return(OK);
    }
}







INT all_ppoly(a,c,b) OP a,b,c;
/* AK 201189 V1.1 */ /* AK 090891 V1.3 */
{
    /* a is PARTITION, c is INTEGER-limit , b becomes result */

    INT i,j,k;
    OP w = callocobject();
    for (i=0L;i<=S_I_I(c);i++)
    {
        OP d = callocobject();
        OP e = callocobject(); /* becomes permutation with lehmercode d */
        OP f = callocobject(); /* becomes q specialisation */
        OP g = callocobject();
        m_il_v(i+S_PA_LI(a)+s_pa_ii(a,S_PA_LI(a)-1L),d);
        for (j=0L;j<i;j++) M_I_I(0L,S_V_I(d,j));
        for (k=0L;k<S_PA_LI(a);k++,j++) copy(s_pa_i(a,k),S_V_I(d,j));

        for (k=0L;k<s_pa_ii(a,S_PA_LI(a)-1L);k++,j++)  M_I_I(0L,S_V_I(d,j));
        println(d);
        lehmercode(d,e);
        println(e);
        m_perm_schubert_qpolynom(e,f);
        b_skn_po(callocobject(),f,NULL,g);
        ;
        m_il_v(1L,S_PO_S(g));
        M_I_I(i,S_PO_SI(g,0L));
        println(g);
        add(g,b,b);
        freeall(g);
        freeall(e);
        freeall(d);
    }
    weight(a,w);
    println(b);
    for (i=0L;i<=S_I_I(w);i++)
    {
        OP p = callocobject();
        OP q = callocobject();
        b_skn_po(callocobject(),callocobject(),NULL,p);
        b_skn_po(callocobject(),callocobject(),NULL,S_PO_K(p));
        M_I_I(1L,S_PO_K(S_PO_K(p)));
        M_I_I(0L,S_PO_S(S_PO_K(p)));
        m_il_v(1L,S_PO_S(p));
        M_I_I(0L,S_PO_SI(p,0L));
        println(p);
        b_skn_po(callocobject(),callocobject(),NULL,q);
        b_skn_po(callocobject(),callocobject(),NULL,S_PO_K(q));
        M_I_I(-1L,S_PO_K(S_PO_K(q)));
        M_I_I(i,S_PO_S(S_PO_K(q)));
        m_il_v(1L,S_PO_S(q));
        M_I_I(1L,S_PO_SI(q,0L));
        println(q);
        add(p,q,q);
        println(q);
        mult(q,b,b);
        println(b);
    }
    return(OK);
}




INT tex_schubert(poly) OP poly;
/* AK 101187 */ /* AK 240789 V1.0 */ /* AK 191190 V1.1 */
/* AK 070291 V1.2 prints to texout */ /* AK 090891 V1.3 */
{
    OP zeiger = poly;

    fprintf(texout,"\\ ");
    if (EMPTYP(poly)) return(OK);
    while (zeiger != NULL)
    {
        if (not einsp (S_SCH_K(zeiger)))
            /* der koeffizient wird nur geschrieben wenn er
            ungleich 1 ist */
            tex(S_SCH_K(zeiger));
        fprintf(texout,"\\ $X_{ ");
        fprint(texout,S_SCH_S(zeiger));
        fprintf(texout," } $\\ ");
        zeiger = S_SCH_N(zeiger);
        if (zeiger != NULL)
            if (not negp(S_SCH_K(zeiger))) /* AK 100892 */
            {
                fprintf(texout," $+$ ");
                texposition += 5L;
            }
        texposition += 15L;
        if (texposition >70L)
        {
            fprintf(texout,"\n");
            texposition = 0L;
        }
    };
    fprintf(texout,"\\ ");
    texposition += 3L;
    return(OK);
}




INT add_schubert_schubert(a,b,c) OP a,b,c;
/* AK 191190 V1.1 */ /* AK 090891 V1.3 */
{
    INT erg;
    OP d = callocobject();
    if (not EMPTYP(c))
        freeself(c);
    copy_list(a,d);
    copy_list(b,c);

    erg = insert(d,c,add_koeff,comp_monomvector_monomvector);

    return(erg);
}

INT add_schubert(a,b,c) OP a,b,c;
/* AK 080102 */
{
    INT erg = OK;
    CTO(SCHUBERT,"add_schubert(1)",a);
    CTO(EMPTY,"add_schubert(3)",c);
    switch (S_O_K(b)) 
        {
        case SCHUBERT: erg += add_schubert_schubert(a,b,c);
                       goto ende;
        default:
             WTO("add_schubert(2)",b);
             goto ende;
        }
ende:
    ENDR("add_schubert");
}





INT m_skn_sch(self,koeff,n,ergebnis) OP self,koeff,n,ergebnis;
/* AK 110789 V1.0 */ /* AK 191190 V1.1 */ /* AK 090891 V1.3 */
{
    INT erg = OK;
    COP("m_skn_sch(4)",ergebnis);
    erg += m_skn_po(self,koeff,n,ergebnis);
    C_O_K(ergebnis,SCHUBERT);
    ENDR("m_skn_sch");
}




INT b_skn_sch(self,koeff,n,ergebnis) OP self,koeff,n,ergebnis;
/* AK 110789 V1.0 */ /* AK 191190 V1.1 */ /* AK 090891 V1.3 */
{
    if (ergebnis == NULL)
        return(ERROR);
    b_skn_po(self,koeff,n,ergebnis);
    C_O_K(ergebnis,SCHUBERT);
    return(OK);
}

#endif /* SCHUBERTTRUE */

#ifdef SCHUBERTTRUE
INT scan_schubert(ergebnis) OP ergebnis;
/* AK 110789 V1.0 */ /* AK 191190 V1.1 */ /* AK 090891 V1.3 */
{
    char antwort[2];
    OBJECTKIND kind;
    INT erg = OK;

    CTO(EMPTY,"scan_schubert(1)",ergebnis);
    erg += b_skn_sch( callocobject(), callocobject(), 
        callocobject(), ergebnis);
    erg += printeingabe("input of Schubert-monom as permutation");
    erg += scan(PERMUTATION,S_SCH_S(ergebnis));
    erg += printeingabe("input kind of coeff");
    kind = scanobjectkind();
    erg += scan(kind,S_SCH_K(ergebnis));
    erg += printeingabe("one more monom y/n");
    scanf("%s",antwort);
    if (antwort[0]  == 'y')     
        erg += scan(SCHUBERT,S_SCH_N(ergebnis));
    else {
        C_O_K(S_SCH_N(ergebnis),EMPTY);
        erg += freeall(S_SCH_N(ergebnis));
        erg += c_sch_n(ergebnis,NULL);
        }
    ENDR("scan_schubert");
}



INT m_perm_sch(a,b) OP a,b;
/* AK 231194 */
{
    INT erg = OK;
    CTO(PERMUTATION,"m_perm_sch",a);
    erg += b_skn_sch(callocobject(),callocobject(),NULL,b);
    erg += copy(a,S_SCH_S(b));
    M_I_I((INT)1,S_SCH_K(b));
    ENDR("m_perm_sch");
}

OP s_sch_s(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_s:a == NULL"), (OP) NULL;
    if (not schubertp(a)) return 
    error("s_sch_s:a != SCHUBERT"), (OP) NULL;
    return(s_mo_s(s_l_s(a)));
}

OP s_sch_k(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_k:a == NULL"), (OP) NULL;
    if (not schubertp(a)) return 
    error("s_sch_k:a != SCHUBERT"), (OP) NULL;
    return(s_mo_k(s_l_s(a)));
}

OP s_sch_n(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_n:a == NULL"), (OP) NULL;
    if (not schubertp(a)) return 
    error("s_sch_n:a != SCHUBERT"), (OP) NULL;
    return(s_l_n(a));
}

OP s_sch_si(a,i) OP a; INT i;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_si:a == NULL"), (OP) NULL;
    if (not schubertp(a)) return 
    error("s_sch_si:a != SCHUBERT"), (OP) NULL;
    return s_p_i(s_sch_s(a),i);
}

OP s_sch_sl(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_sl:a == NULL"), (OP) NULL;
    if (not schubertp(a)) return 
    error("s_sch_sl:a != SCHUBERT"), (OP) NULL;
    return s_p_l(s_sch_s(a));
}

INT s_sch_ki(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_ki:a == NULL");
    if (not schubertp(a)) return error("s_sch_ki:a != SCHUBERT");
    return s_i_i(s_sch_k(a));
}

INT s_sch_sii(a,i) OP a; INT i;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) return error("s_sch_sii:a == NULL");
    if (not schubertp(a)) return error("s_sch_sii:a != SCHUBERT");
    return s_p_ii(s_sch_s(a),i);
}


INT s_sch_sli(a) OP a;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    if (a == NULL) 
        return error("s_sch_sli:a == NULL");
    if (not schubertp(a)) 
        return error("s_sch_sli:a != SCHUBERT");
    return s_p_li(s_sch_s(a));
}

INT c_sch_n(a,b) OP a,b;
/* AK 110789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    OBJECTSELF c;
    if (a == NULL) 
        return error("c_sch_n:a == NULL");
    c = s_o_s(a);
    c.ob_list->l_next = b;
    return OK;
}




INT display_schubert(a) OP a;
/* AK 240789 V1.0 */ /* AK 131290 V1.1 */ /* AK 090891 V1.3 */
{
    return(println(a));
}



INT test_schubert()
/* AK 200891 V1.3 */
{
    OP a = callocobject();
    OP b = callocobject();

    printf("test_schubert:scan(PERMUTATION)\n");
    scan(PERMUTATION,a);
    println(a);
    printf("test_schubert:m_perm_schubert_monom_summe(a,b)\n");
    m_perm_schubert_monom_summe(a,b);
    println(b);
    printf("test_schubert:scan(POLYNOM)\n");
    scan(POLYNOM,a);
    println(a);
    printf("test_schubert:t_POLYNOM_SCHUBERT(a,b)\n");
    t_POLYNOM_SCHUBERT(a,b);
    println(b);
    printf("test_schubert:tex(b)\n");
    tex(b);
    printf("test_schubert:scan(SCHUBERT,a)\n");
    scan(SCHUBERT,a);
    println(a);
    printf("test_schubert:hoch(a,2L,b)\n");
    hoch(a,cons_zwei,b);
    println(b);
    printf("test_schubert:einsp(b)\n");
    if (not einsp(b))
        printeingabe("not eins");
    else
        printeingabe("is eins");

    freeall(a);
    freeall(b);
    return(OK);
}




INT print_schubert_difference(b,c) OP b,c;
/* druckt in spezieller weise aus
b ist ein einzelnes Schubertpolynom, c ist eine summe von Schubertpolynomen
gedruckt werden nur die stellen die verschieden in den permutationen */
/* AK 200690 */
/* AK 200891 V1.3 */
{
    OP x;
    INT i;
    x = c;
    while ( x != NULL) {
        print(S_SCH_K(b));
        printf(" [");
        for (i=0L;(i < S_SCH_SLI(x))&&
            (i <S_SCH_SLI(b)) ; i++ )
        {
            if (S_SCH_SII(x,i)==S_SCH_SII(b,i)) printf(".,");
            else printf("%ld,",S_SCH_SII(b,i));
            zeilenposition += 2L;
        }
        printf("]\n");
        print(S_SCH_K(x));
        printf(" [");
        for (i=0L;(i < S_SCH_SLI(x))&&
            (i <S_SCH_SLI(b)) ; i++ )
        {
            if (S_SCH_SII(x,i)==S_SCH_SII(b,i)) printf(".,");
            else printf("%ld,",S_SCH_SII(x,i));
            zeilenposition = 0L;
        }
        printf("]\n\n");
        x = S_SCH_N(x);
    }
    return OK;
}




INT t_SCHUBERT_POLYNOM(a,b) OP a,b;
/* AK 210690 V1.1 */ /* AK 210291 V1.2 */ /* AK 090891 V1.3 */
{
    OP z=a;
    OP c;

    INT erg = OK;
    CTO(SCHUBERT,"t_SCHUBERT_POLYNOM(1)",a);
    CE2(a,b,t_SCHUBERT_POLYNOM);

    c = CALLOCOBJECT();
    init(POLYNOM,b);
      
    while(z != NULL) {
        erg += m_perm_schubert_monom_summe(S_SCH_S(z),c);
        MULT_APPLY(S_SCH_K(z),c); /* missing in V1.1 */
        ADD_APPLY(c,b);
        z = S_SCH_N(z);
    }
    FREEALL(c);
    ENDR("t_SCHUBERT_POLYNOM");
}

INT t_SCHUBERT_SCHUR(a,b) OP a,b;
{
    OP z,s;
    INT erg = OK;
    
    CTO(SCHUBERT,"t_SCHUBERT_SCHUR(1)",a);
    erg += init(SCHUR,b);
    FORALL(z,a,{
        s = CALLOCOBJECT();init(SCHUR,s);
        newtrans(S_MO_S(z),s);
        MULT_APPLY(S_MO_K(z),s);
        insert(s,b,add_koeff,comp_monomschur);
        });
    ENDR("t_SCHUBERT_SCHUR");
}




INT mult_scalar_schubert(von,nach,ergebnis) OP von, nach, ergebnis;
/* AK 230402 */
{
    INT erg = OK;
    CTO(SCHUBERT,"mult_scalar_schubert(2)",nach);
    CTO(EMPTY,"mult_scalar_schubert(3)",ergebnis);

    if ((NULLP(von))|| (NULLP(nach)))
        {
        erg +=  m_i_i(0,ergebnis); 
        goto endr_ende;
        }

    erg += trans2formlist(von,nach,ergebnis,mult);
    ENDR("mult_scalar_schubert");
}


INT mult_schubert_schubert(a,b,c) OP a,b,c;
/* AK 210690 V1.1 */ /* AK 090891 V1.3 */
{
    INT erg = OK;
    OP d;
    CTO(SCHUBERT,"mult_schubert_schubert(1)",a);
    CTO(SCHUBERT,"mult_schubert_schubert(2)",b);
    CTO(EMPTY,"mult_schubert_schubert(3)",c);

    if (S_SCH_SLI(a) > S_SCH_SLI(b)) {
        d=a;
        a=b;
        b=d;
    }
    d=callocobject();
    erg += t_SCHUBERT_POLYNOM(a,d);
    erg += mult(d,b,c);
    erg += freeall(d);
    ENDR("mult_schubert_schubert");
}

INT outerproduct_schubert(a,b,c) OP a,b,c;
/* a PERM b PERM c wird SCHUBERT */
{
    INT erg = OK;
    OP d,e;
    CTO(PERMUTATION,"outerproduct_schubert(1)",a);
    CTO(PERMUTATION,"outerproduct_schubert(2)",b);
    d=callocobject();
    e=callocobject();
    erg += m_perm_sch(a,d);
    erg += m_perm_sch(b,e);
    erg += mult(d,e,c);
    erg += freeall(d);
    erg += freeall(e);
    ENDR("outerproduct_schubert");
}

INT mult_schubert_variable (a,i,r) OP a,i,r;
/* a ist schubert polynom
   i ist INTEGER, index der variable *
   r wird result */
/* AK 190690 V1.1 */ /* AK 090891 V1.3 */
{
    OP z,ss,c;
    INT erg = OK;
    INT ii = S_I_I(i);  /* variablennumerierung beginnt mit 0 */
    INT j;
    INT grenzelinks,grenzerechts;

    CE3(a,i,r,mult_schubert_variable);
    init(SCHUBERT,r);
    
    
    z = a;
    while (z != NULL)
    {
        ss = S_SCH_S(z);
        if (S_P_II(ss,S_P_LI(ss)-1L) != S_P_LI(ss) ) {
            inc(S_P_S(ss));
            M_I_I(S_P_LI(ss), S_P_I(ss,S_P_LI(ss)-1L) );
        }
        while (ii+1L >= S_P_LI(ss))
        {
            inc(S_P_S(ss));
            M_I_I(S_P_LI(ss), S_P_I(ss,S_P_LI(ss)-1L) );
        }
        grenzelinks=0L;
        grenzerechts=S_P_LI(ss)+1L;
        for (j=ii-1L;j>=0L; j--)
        {
            if (
                (S_P_II(ss,j) < S_P_II(ss,ii) )
                &&
                (S_P_II(ss,j) > grenzelinks )
                )
            {
                /* nach links tauschen */
                c = callocobject();
                b_skn_sch(callocobject(),callocobject(),
                    NULL,c);
                addinvers(S_SCH_K(z),S_SCH_K(c));
                copy(ss,S_SCH_S(c));
                m_i_i(S_P_II(ss,j), S_SCH_SI(c,ii));
                m_i_i(S_P_II(ss,ii), S_SCH_SI(c,j));
                insert(c,r,add_koeff,
                    comp_monomvector_monomvector);
                grenzelinks = S_P_II(ss,j);
            }
        }
        for (j=ii+1L; j <S_P_LI(ss); j++)
        {
            if (
                (S_P_II(ss,j) > S_P_II(ss,ii) )
                &&
                (S_P_II(ss,j) < grenzerechts )
                )
            {
                /* nach rechts tauschen */
                c = callocobject();
                b_skn_sch(callocobject(),callocobject(),
                    NULL,c);
                copy(S_SCH_K(z),S_SCH_K(c));
                copy_permutation(ss,S_SCH_S(c));
                M_I_I(S_P_II(ss,j), S_SCH_SI(c,ii));
                M_I_I(S_P_II(ss,ii), S_SCH_SI(c,j));
                insert(c,r,add_koeff,
                    comp_monomvector_monomvector);
                grenzerechts = S_P_II(ss,j);
            }
        }

        z = S_SCH_N(z);
    }
    ENDR("mult_schubert_variable");
}




INT mult_schubert_monom(a,b,c) OP a,b,c;
/* a ist SCHUBERT b ist MONOM eines POLYNOMS c wird ergebnis */
/* AK 190690 V1.1 */ /* AK 090891 V1.3 */
{
    OP e=callocobject();
    INT i,j;
    copy(a,c);
    for (i=0L; i<S_MO_SLI(b); i++)
        for (j=0L; j<S_MO_SII(b,i); j++)
        {
            M_I_I(i,e);
            mult_schubert_variable(c,e,c);
        }

    mult_apply(S_MO_K(b),c);
    freeall(e);
    return OK;
}




INT mult_schubert_polynom(a,b,c) OP a,b,c;
/* a ist SCHUBERT b ist POLYNOM c wird SCHUBERT */
/* AK 190690 V1.1 */ /* AK 090891 V1.3 */
{
    OP d,z = b;
    INT erg = OK;
    CTO(SCHUBERT,"mult_schubert_polynom(1)",a);
    CTO(POLYNOM,"mult_schubert_polynom(2)",b);
    CTO(EMPTY,"mult_schubert_polynom(3)",c);
    
    erg += b_sn_l(NULL,NULL,c);
    C_O_K(c,SCHUBERT);
    while (z != NULL)
    {
        d = callocobject();
        mult_schubert_monom(a,S_L_S(z),d);
        insert(d,c,add_koeff,comp_monomvector_monomvector);
        z = S_PO_N(z);
    }
    ENDR("mult_schubert_polynom");
}




INT t_PERMUTATION_SCHUBERT(a,b) OP a,b;
/* AK 200891 V1.3 */
{
    if (not EMPTYP(b))
        freeself(b);
    b_skn_sch(callocobject(),callocobject(),NULL,b);
    M_I_I(1L,S_SCH_K(b));
    copy_permutation(a,S_SCH_S(b));
    return OK;
}




INT add_apply_schubert_schubert(a,b) OP a,b;
/* AK 200891 V1.3 */
{
    OP c = callocobject();
    copy_list(a,c);
    return(insert(c,b,add_koeff,comp_monomvector_monomvector));
}



INT add_apply_schubert(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 210291 V1.2 */ /* AK 090891 V1.3 */
{
    INT erg = OK;
    EOP("add_apply_schubert(2)",b);
    CTO(SCHUBERT,"add_apply_schubert(1)",a);


    switch(S_O_K(b)) 
        {
        case SCHUBERT:
            erg +=  add_apply_schubert_schubert(a,b);
            break;
        default:
            erg += add_apply_default(a,b);
            break;
        }
   ENDR("add_apply_schubert");
}





INT println_schub_lehmer(a) OP a;
/* AK 070691 V1.2 */ /* AK 200891 V1.3 */
{
    OP z,b;
    INT erg = OK;
    CTO(SCHUBERT,"println_schub_lehmer(1)",a);
    z=a;
    b = callocobject();
    while (z != NULL)
    {
        erg += print(S_SCH_K(z));
        erg += lehmercode(S_SCH_S(z),b);
        erg += print(b);
        if (S_SCH_N(z) != NULL)
            if (not negp(S_SCH_K(S_SCH_N(z)))) {
                printf(" + "); zeilenposition += 3L; 
                }
        z = S_SCH_N(z);
    }
    erg += freeall(b);
    printf("\n");zeilenposition = 0L;
    ENDR("println_schub_lehmer");
}




INT m_i_schubert(a,b) INT a; OP b;
/* changes a INT into a SCHUBERTpolynomial with this INT as 
koeffizent and labeled by the identity perm */
/* AK 181290 V1.1 */ /* AK 090891 V1.3 */
{
    b_skn_sch(callocobject(),callocobject(),NULL,b);
    M_I_I(a,S_SCH_K(b));
    b_ks_p(VECTOR,callocobject(),S_SCH_S(b));
    m_il_v(2L,S_P_S(S_SCH_S(b)));
    M_I_I(1L,S_P_I(S_SCH_S(b),0L));
    M_I_I(2L,S_P_I(S_SCH_S(b),1L));
    return OK;
}




INT invers_polynom(a,b) OP a,b;
/* AK 281290 V1.1 */ /* AK 090891 V1.3 */
{
    INT i,j,erg=OK;
    OP c = callocobject();
    if (not EMPTYP(b))
        erg += freeself(b);
    erg += m_i_schubert(1L,b);
    erg += t_SCHUBERT_POLYNOM(b,b);
    for (i=0L; i< S_P_LI(a); i++)
        for (j=i+1; j< S_P_LI(a); j++)
        {
            if ( S_P_II(a,j) < S_P_II(a,i) )
            {
                erg += co_L9(i,j,c);
                erg += mult_apply(c,b);
                erg += freeself(c);
            }
        }

    erg += freeall(c);
    return erg;
}




static INT co_L9(i,j,c) INT i,j; OP c;
/* computes x_i - x_j */
/* AK 200891 V1.3 */
{
    OP d = callocobject();
    if (not EMPTYP(c)) 
        freeself(c);
    m_iindex_monom(i,c);
    m_iindex_monom(j,d);
    addinvers_apply(d);
    add_apply(d,c);
    freeall(d);
    return OK;
}



INT nullp_schubert(a) OP a;
/* AL 180393 */
{
    OP z = a;
    if (EMPTYP(a)) /* AK 091194 */
        return TRUE;
    if (empty_listp(a))
        return TRUE;
    while (z != NULL)
    {
        if (not nullp(S_SCH_K(z)) )
            return FALSE;
        z = S_SCH_N(z);
    }
    return TRUE;
}



INT dimension_schubert(sb,res)  OP sb,res;
/* AL 180393 */
{
    OP  z,a;
    INT erg = OK;

    CTO(SCHUBERT,"dimension_schubert(1)",sb);
    CE2(sb,res,dimension_schubert);

    z=callocobject();
    a=callocobject();
    M_I_I(0L,res);
    z=sb;
    while(z !=NULL) {
        erg += m_perm_schubert_dimension(S_SCH_S(z),a);
        erg += mult_apply(S_SCH_K(z),a);
        z=S_SCH_N(z);
        erg += add_apply(a,res);
    }

    erg += freeall(a);
    ENDR("dimension_schubert");
}

INT qdimension_schubert(sb,res)  OP sb,res;
/* AL 180393 */
{
    OP  z,a;
    INT erg = OK;
    CTO(SCHUBERT,"qdimension_schubert(1)",sb);
    CTO(EMPTY,"qdimension_schubert(2)",res);

    z=callocobject();
    a=callocobject();
    M_I_I(0L,res);
    z=sb;
    while(z !=NULL) {
        erg += m_perm_schubert_qpolynom(S_SCH_S(z),a);
        erg += mult_apply(S_SCH_K(z),a); 
        z=S_SCH_N(z);
        erg += add_apply(a,res);
    }

    erg += freeall(a);
    ENDR("qdimension_schubert");
}

INT divdiff_schubert(a,schub,res)  OP a,schub,res;
/* AL 180393 */
{
    OP a1,e,f;    
    INT x,y;
    INT erg = OK;
    CTO(INTEGER,"divdiff_schubert(1)",a);
    CTO(SCHUBERT,"divdiff_schubert(2)",schub);
        
    a1=callocobject();
    f=callocobject();
    e=callocobject();


    M_I_I(S_I_I(a)-1L,a1);
    erg += init(SCHUBERT,res);

    if (S_L_S(schub) == NULL)
        {
        erg += copy(schub,res);
        goto ende;
        }
    while(schub!=NULL)
    { 
        copy(S_SCH_S(schub),e); 
        x=S_P_II(e,S_I_I(a)-1L);
        y=S_P_II(e,S_I_I(a));

        if(x>y){ 
            M_I_I(x,S_P_I(e,S_I_I(a)));
            M_I_I(y,S_P_I(e,S_I_I(a)-1L));

            erg += m_skn_sch(e,S_SCH_K(schub),NULL,f);
            erg += add_apply(f,res);
        }

        schub=S_SCH_N(schub);

    } 
ende:
    erg += freeall(f);
    erg += freeall(e);
    erg += freeall(a1);
    ENDR("divdiff_schubert");
}


INT divdiff_perm_schubert(perm,sb,res)  OP perm,sb,res;
/* AL 180393 */
{
    OP red,f;
    INT i,erg = OK;
    CTO(PERMUTATION,"divdiff_perm_schubert(1)",perm);
    CTO(SCHUBERT,"divdiff_perm_schubert(2)",sb);

    red=callocobject();
    f=callocobject();
    erg += rz_perm(perm,red);
    erg += copy(sb,res);

    for(i=0L;i<S_V_LI(red);i++)
    { 
        erg += divdiff_schubert(S_V_I(red,i), res,f);
        erg += copy(f,res);
    }
    erg += freeall(red);
    erg += freeall(f);
    ENDR("divdiff_perm_schubert");
}



INT tex_2schubert_monom_summe(b) OP b;
{
    OP z = b;
    INT i,j,k;
    INT erg = OK;
    CTO(POLYNOM,"tex_2schubert_monom_summe",b);
    while (z != NULL)
        {
        tex (S_PO_K(z));
        for (i=0L,k=0,j=0;i<S_PO_SLI(z);i++)
            {
            
            if (S_PO_SII(z,i) == (INT)1)
                {
                fprintf(texout,"$ (x_%ld - y_%ld) $ ",j,k-j);
                texposition += (INT)10;
                }
            else
            if (S_PO_SII(z,i) > (INT)1)
                {
                fprintf(texout,"$ (x_%ld - y_%ld)^%ld $ ",j,k-j,S_PO_SII(z,i));
                texposition += (INT)10;
                }

            if (k == j) { k++;j=(INT)0; }
            else j++;
/*
            if (j == 0) { k++;j=k; }
            else j--;
*/
            }
        z = S_PO_N(z);
        if (texposition >(INT)70)
        {
            fprintf(texout,"\n");
            texposition = 0L;
        }
        if (z != NULL)
            fprintf(texout," $+$ ");
        }

    ENDR("tex_2schubert_monom_summe");
}


INT m_perm_2schubert_monom_summe(perm,res) OP perm,res;
/* Eingabe: PERMUTATION als label des Schubertpolynoms */
/* Ausgabe: POLYNOM */
/* 020588 */ /* AK 240789 V1.0 */ /* AK 120790 V1.1 */ /* AK 090891 V1.3 */
{
    OP vorfaktor;
    /* das monom, mit dem das ergebnis einer einzelnen
        rekursion multipliziert werden muss */
    /* beim start = [0,0,0,0,....,0] */
    INT i;
    INT erg = OK;
    CTO(PERMUTATION,"m_perm_2schubert_monom_summe",perm);
    if (einsp(perm)) /* AK 191191 */
        return m_scalar_polynom(cons_eins,res);
    if (not EMPTYP(res))
        erg += freeself(res);
    vorfaktor = callocobject();
    erg += m_il_v((S_P_LI(perm)*(S_P_LI(perm)-1))/2,vorfaktor);
    for (i=0L;i<S_V_LI(vorfaktor);i++)
        M_I_I(1L,S_V_I(vorfaktor,i));
    /* vorfaktor ist nun initialisiert */
    erg += algorithmus5(vorfaktor,0L,S_P_LI(perm)-1L,perm,res);
    /* die rekursion wird aufgerufen */
    erg += freeall(vorfaktor);
    ENDR("m_perm_2schubert_monom_summe");
}

static INT algorithmus5(vorfaktor,alphabetindex,stufe,perm,res)
    OP vorfaktor; /* ist ein monom, d.h. vector */
/* bsp [0,1,0] == b^2 */
/* damit wird das ergebnis dieser rekursion 
        multipliziert und in res eingefuegt */
    INT alphabetindex;
/* ist der start des alphabets a==0 */
/* d.h. wird nur noch im alphabet b,c,d, ..
        gerechnet so ist dies =1 */
    INT stufe; /* der exponent des Vorfaktors */
    OP perm; /* die permutation zu der berechnet wird */
    OP res; /* das globale ergebnis */
/* AK 020588 */ /* AK 081188 */ /* AK 240789 V1.0 */ /* AK 201189 V1.1 */
/* AK 090891 V1.3 */
{
    INT i,j,k;
    if (S_O_K(perm) != PERMUTATION)
        return error("algorithmus5:no PERMUTATION");
    if (S_O_K(vorfaktor) != VECTOR)
        return error("algorithmus5:no VECTOR");
    if (S_V_LI(vorfaktor) == 0L)
        return error("algorithmus5:vorfaktor == 0");
    if (S_P_LI(perm) == 2L)
    /* ende des algorithmus */
    {
        OP monom = callocobject();
        b_skn_po(callocobject(),callocobject(),NULL,monom);
        M_I_I(1L,S_PO_K(monom));
        if (S_P_II(perm,0L) == 1L)
            {
            j =  ((1+alphabetindex) * alphabetindex)  / 2;
            M_I_I(0L,S_V_I(vorfaktor,j + alphabetindex));
            }
        copy(vorfaktor,S_PO_S(monom));
        /* das monom ist nun fertig initialisiert */

        /* der vorfaktor wird noch mit dem i-ten
            buchstaben multipliziert falls perm = [2,1] */
        insert(monom,res,add_koeff,comp_monomvector_monomvector);
        /* einfuegen des ergebnis in das globale ergebnis */
        return OK;
    }


    if (S_P_II(perm,0L) == S_P_LI(perm)) /* nun die rekursion */
    {
        OP neuperm = callocobject();
        OP neufaktor = callocobject();

        b_ks_p(VECTOR,callocobject(),neuperm);
        m_il_v(S_P_LI(perm)-1L,S_P_S(neuperm));
        for(i=0L;i<S_P_LI(neuperm);i++)
            M_I_I(S_P_II(perm,i+1L),S_P_I(neuperm,i));
        /* es wurde die permutation um das erste element
        welches das groesste war gekuerzt, hier wurde
        ausgenutzt 
        z.B X_634215 = a^6 X_34215(b,c,d,e,f)
        diese multiplikation folgt nun
        */

        copy_vector(vorfaktor,neufaktor);
        /* M_I_I(stufe,S_V_I(neufaktor,alphabetindex)); */
        algorithmus5(    neufaktor,alphabetindex+1L,
            S_P_LI(neuperm)-1,neuperm,res);
        freeall(neufaktor);
        freeall(neuperm);
        return OK;
    }
    else    {    /* falls keine rekursion im alphabet */
        INT maximal = S_P_LI(perm)+1L;
        OP neuperm = callocobject();
        OP neufaktor = callocobject();
        for (i=1L;i<S_P_LI(perm);i++)
            if (    (S_P_II(perm,i) < maximal)&&
                (S_P_II(perm,i) > S_P_II(perm,0L)))
            {
            copy(perm,neuperm);
            copy(vorfaktor,neufaktor);
            maximal = S_P_II(perm,i);
            M_I_I(S_P_II(perm,0L),S_P_I(neuperm,i));
            M_I_I(S_P_II(perm,i),S_P_I(neuperm,0L));
            /* 
            M_I_I(1L,S_V_I(neufaktor,S_P_II(perm,0L)-1+alphabetindex));
            */
            k = alphabetindex + S_P_II(perm,0L) - 1L;
            j =  ((1+k) * k)  / 2;
            M_I_I(0L,S_V_I(neufaktor,j + alphabetindex));
            

/*            print(S_P_I(perm,0L));print(neufaktor);println(neuperm); */

            algorithmus5(neufaktor,alphabetindex,
                    stufe-1L,neuperm,res);
            };
        freeall(neuperm);
        freeall(neufaktor);
        return OK;
    }
}

INT exchange_alphabets(a,b) OP a,b;
/* AK 101194 */
/* eingabe ein polynom mit matrix self teil in zwei zeilen
   = ergebnis von t_2SCHUBERT_POLYNOM */
/* ergbnis tausch der beiden zeilen der matrix */
{
    OP z,d;
    init(POLYNOM,b);
    z = a;
    while (z != NULL)
        {
        d = callocobject();
        m_skn_po(S_PO_S(z),S_PO_K(z),NULL,d);
        change_row_ij(S_PO_S(d),0L,1L);
        insert(d,b,NULL,NULL);
        z = S_PO_N(z);
        }
    return OK;
}

INT eval_2schubert(a,vec,b) OP a,b,vec;
/* AK 101194 */
/* eingabe ein double schubert polynom a (d.h. kodiert in einem vektor)
   und ein vektor vec mit den ersetzungen fuer y_i 
   ergebnis ist b */
{
    OP z,c,d,e,f;
    INT i,j,k;
    z = a;
    init ( POLYNOM, b);
    if (nullp(a))
        return OK;
    c = callocobject();
    d = callocobject();
    e = callocobject();
    while (z != NULL)
        {
        f = callocobject();
        m_i_i(1L,f);
        for (i=0L,j=0L,k=0L;i<S_PO_SLI(z);i++) 
            {
            if (S_PO_SII(z,i) != 0L) 
                {
                add(S_PO_SL(z), S_PO_SL(z), c);
                ganzsquareroot(c,c); /* c is size of self part */
                b_skn_po(callocobject(), callocobject(), NULL, d);
                M_I_I(1L,S_PO_K(d));
                m_l_nv(c,S_PO_S(d));
                M_I_I(1L,S_PO_SI(d,k));
                sub(d,S_V_I(vec,j-k),d);
                hoch(d,S_PO_SI(z,i),d);
                mult_apply(d,f);
                }
            if (j == k) { k = 0L; j++ ; }
            else k++;
            }
        z = S_PO_N(z);
        insert(f,b,NULL,NULL);
        }
    freeall(c);
    freeall(d);
    freeall(e);
    return OK;
}

INT t_2SCHUBERT_POLYNOM(a,b) OP a,b;
/* AK 101194 */
{
    OP z,c,d,e,f;
    INT i,j,k;
    z = a;
    init ( POLYNOM, b);
    c = callocobject();
    d = callocobject();
    e = callocobject();
    while (z != NULL)
        {
        f = callocobject();
        m_i_i(1L,f);
        for (i=0L,j=0L,k=0L;i<S_PO_SLI(z);i++) 
            {
            if (S_PO_SII(z,i) != 0L) 
                {
                add(S_PO_SL(z), S_PO_SL(z), c);
                ganzsquareroot(c,c); /* c is size of matrix */
                b_skn_po(callocobject(), callocobject(), NULL, d);
                M_I_I(1L,S_PO_K(d));
                m_lh_nm(c,cons_zwei,S_PO_S(d));
                M_I_I(1L,S_PO_SIJ(d,0L,k));
                b_skn_po(callocobject(), callocobject(), NULL, e);
                M_I_I(1L,S_PO_K(e));
                m_lh_nm(c,cons_zwei,S_PO_S(e));
                M_I_I(1L,S_PO_SIJ(e,1L,j-k));
                sub(d,e,d);
                hoch(d,S_PO_SI(z,i),d);
                mult_apply(d,f);
                }
            if (j == k) { k = 0L; j++ ; }
            else k++;
            }
        z = S_PO_N(z);
        insert(f,b,NULL,NULL);
        }
    freeall(c);
    freeall(d);
    freeall(e);
    return OK;
}




INT m_perm_2schubert_operating_monom_summe(perm,perm2,res2) OP perm,perm2,res2;
/* Eingabe: PERMUTATION als label des Schubertpolynoms */
/* Ausgabe: POLYNOM */
/* 020588 */ /* AK 240789 V1.0 */ /* AK 120790 V1.1 */ /* AK 090891 V1.3 */
{
    OP vorfaktor;
    OP res,vec;
    INT i,erg = OK;
    CTO(PERMUTATION,"m_perm_2schubert_operating_monom_summe(1)",perm);
    CTO(PERMUTATION,"m_perm_2schubert_operating_monom_summe(2)",perm2);

    init(POLYNOM,res2);
    if (einsp(perm)) /* AK 191191 */
        {
        erg += m_scalar_polynom(cons_eins,res2);
        goto ee;
        }

    res = callocobject();
    init(POLYNOM,res);
    vorfaktor = callocobject();
    m_il_integervector((S_P_LI(perm)*(S_P_LI(perm)-1))/2,vorfaktor);
    
    for (i=0L;i<S_V_LI(vorfaktor);i++)
        M_I_I(1,S_V_I(vorfaktor,i));
    /* vorfaktor ist nun initialisiert */
    algorithmus6(perm2,vorfaktor,0L,S_P_LI(perm)-1L,perm,res);
    /* die rekursion wird aufgerufen */
    freeall(vorfaktor);
    /* vorfaktor wird freigegeben  ==> kein speicher bedarf */

    if (nullp(res))
        {
        FREEALL(res);
        goto ee;
        }
    vec = callocobject();
    m_il_v(S_P_LI(perm2),vec);
    for (i=0;i<S_V_LI(vec);i++)
        m_iindex_monom(S_P_II(perm2,i)-1,S_V_I(vec,i));
    eval_2schubert(res,vec,res2);
    FREEALL(vec);
    FREEALL(res);
ee:
    ENDR("m_perm_2schubert_operating_monom_summe");
}

static INT algorithmus6(perm2,vorfaktor,alphabetindex,stufe,perm,res)
    OP vorfaktor; /* ist ein monom, d.h. vector */
/* bsp [0,1,0] == b^2 */
/* damit wird das ergebnis dieser rekursion 
        multipliziert und in res eingefuegt */
    INT alphabetindex;
/* ist der start des alphabets a==0 */
/* d.h. wird nur noch im alphabet b,c,d, ..
        gerechnet so ist dies =1 */
    INT stufe; /* der exponent des Vorfaktors */
    OP perm; /* die permutation zu der berechnet wird */
    OP perm2,res; /* das globale ergebnis */
/* AK 020588 */ /* AK 081188 */ /* AK 240789 V1.0 */ /* AK 201189 V1.1 */
/* AK 090891 V1.3 */
{
    INT i,j,k;
    if (S_O_K(perm) != PERMUTATION)
        return error("algorithmus6:no PERMUTATION");
    if (! VECTORP(vorfaktor))
        return error("algorithmus6:no VECTOR");
    if (S_V_LI(vorfaktor) == 0L)
        return error("algorithmus6:vorfaktor == 0");
    if (S_P_LI(perm) == 2L)
    /* ende des algorithmus */
    {
        OP monom;
        if (S_P_II(perm,0L) == 1L)
            {
            j =  ((1+alphabetindex) * alphabetindex)  / 2;
            M_I_I(0L,S_V_I(vorfaktor,j + alphabetindex));
            }

        for (i=0,j=1,k=1; i<S_V_LI(vorfaktor);i++)
            {
            if ((S_P_II(perm2,k-j) == j)  &&
                (S_V_II(vorfaktor,i) != 0L) )
                {
                return OK;
                }
            if (j==k) { j=1;k++; }
            else j++;
            }
        monom = callocobject();
        b_skn_po(callocobject(),callocobject(),NULL,monom);
        M_I_I(1L,S_PO_K(monom));
        copy(vorfaktor,S_PO_S(monom));
        insert(monom,res,add_koeff,comp_monomvector_monomvector);
        /* einfuegen des ergebnis in das globale ergebnis */
        return OK;
    }


    if (S_P_II(perm,0L) == S_P_LI(perm)) /* nun die rekursion */
    {
        OP neuperm = callocobject();
        OP neufaktor = callocobject();

        b_ks_p(VECTOR,callocobject(),neuperm);
        m_il_v(S_P_LI(perm)-1L,S_P_S(neuperm));
        for(i=0L;i<S_P_LI(neuperm);i++)
            M_I_I(S_P_II(perm,i+1L),S_P_I(neuperm,i));
        /* es wurde die permutation um das erste element
        welches das groesste war gekuerzt, hier wurde
        ausgenutzt 
        z.B X_634215 = a^6 X_34215(b,c,d,e,f)
        diese multiplikation folgt nun
        */

        copy_integervector(vorfaktor,neufaktor);
        /* M_I_I(stufe,S_V_I(neufaktor,alphabetindex)); */
        algorithmus6(    perm2,neufaktor,alphabetindex+1L,
            S_P_LI(neuperm)-1,neuperm,res);
        freeall(neufaktor);
        freeall(neuperm);
        return OK;
    }
    else    {    /* falls keine rekursion im alphabet */
        INT maximal = S_P_LI(perm)+1L;
        OP neuperm = callocobject();
        OP neufaktor = callocobject();
        for (i=1L;i<S_P_LI(perm);i++)
            if (    (S_P_II(perm,i) < maximal)&&
                (S_P_II(perm,i) > S_P_II(perm,0L)))
            {
            copy(perm,neuperm);
            copy(vorfaktor,neufaktor);
            maximal = S_P_II(perm,i);
            M_I_I(S_P_II(perm,0L),S_P_I(neuperm,i));
            M_I_I(S_P_II(perm,i),S_P_I(neuperm,0L));
            k = alphabetindex + S_P_II(perm,0L) - 1L;
            j =  ((1+k) * k)  / 2;
            M_I_I(0L,S_V_I(neufaktor,j + alphabetindex));
            

            algorithmus6(perm2,neufaktor,alphabetindex,
                    stufe-1L,neuperm,res);
            };
        freeall(neuperm);
        freeall(neufaktor);
        return OK;
    }
}

INT scalarproduct_schubert(a,b,c) OP a,b,c;
/* AK 231194 */
{
    OP d,e;
    INT erg = OK;
    CTO(SCHUBERT,"scalarproduct_schubert",a);
    CTO(SCHUBERT,"scalarproduct_schubert",b);
    d = callocobject();
    e = callocobject();
    erg += maxdegree_schubert(a,d);
    erg += maxdegree_schubert(b,e);
    if (gt(e,d)) erg += copy(e,d);
    erg += mult(a,b,e);
    erg += last_permutation(d,d);
    erg += divdiff(d,e,c);
    erg += freeall(d);
    erg += freeall(e);
    ENDR("scalarproduct_schubert");
}

#endif /* SCHUBERTTRUE */
