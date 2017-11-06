/* file bar.c symmetrica */
#include "def.h"
#include "macro.h"

#ifdef PERMTRUE
INT cast_apply_barperm(a) OP a;
/* AK 280294 */
{
    INT erg = OK;
    EOP("cast_apply_barperm(1)",a);
    switch(S_O_K(a))
        {
        case VECTOR:
            erg += m_ks_p(VECTOR,a,a);
            C_P_K(a,BAR);
            break;
        case PERMUTATION:
            if (S_P_K(a) == BAR)
                break;
            else if (S_P_K(a) == VECTOR)
                {
                C_P_K(a,BAR);
                break;
                }
        default:
            printobjectkind(a);
            erg += WTO("cast_apply_barperm",a);
            break;
        }
    ENDR("cast_apply_barperm");
}

INT invers_bar(a,b) OP a,b;
{
    INT i,erg =OK,j;
    CH2D(a,b);
    erg += b_ks_p(VECTOR,callocobject(),b);
    erg += absolute(S_P_S(a),S_P_S(b));
    erg += invers(b,b);
    for (i=0L;i<S_P_LI(a);i++)
        if (S_P_II(a,i) < 0) 
            {
            j = (S_P_II(a,i)+1)* (-1);
            M_I_I(S_P_II(b,j) * -1, S_P_I(b,j));
            }
    C_P_K(b,BAR);
    ENDR("invers_bar");
}

INT new_divdiff_bar(a,b,c) OP a,b,c;
{
    OP d;
    INT erg = OK;
    CTO(PERMUTATION,"new_divdiff_bar(1)",a);
    d = callocobject();
    erg += rz(a,d);
    erg += new_divideddiff_rz_bar(d,b,c);
    erg += freeall(d);
    ENDR("new_divdiff_bar");

}
INT divdiff_bar(a,b,c) OP a,b,c;
{
    OP d;
    INT erg = OK;
    CTO(PERMUTATION,"divdiff_bar(1)",a);
    d = callocobject();
    erg += rz(a,d);
    erg += divideddiff_rz_bar(d,b,c);
    erg += freeall(d);
    ENDR("divdiff_bar");

}

INT new_divideddiff_rz_bar(rzt,poly,c) OP    rzt, poly, c;
/* AK 020392 */
/* rzt is reduced decomposition of barred permutation */
{
    INT i = 0 ;
    INT erg = OK;
    erg += copy (poly,c);
    if (EMPTYP(rzt)) 
        goto endr_ende;
    while (i < S_V_LI(rzt))
    { 
        erg += new_divideddifference_bar(S_V_I(rzt,i),c,c);
        i++; 
    };
    ENDR("new_divideddiff_rz_bar");
}

INT divideddiff_rz_bar(rzt,poly,c) OP    rzt, poly, c;
/* AK 020392 */
/* rzt is reduced decomposition of barred permutation */
{
    INT i = 0 ;
    INT erg = OK;
    erg += copy (poly,c);
    if (EMPTYP(rzt)) 
        goto endr_ende;
    while (i < S_V_LI(rzt))
    { 
        erg += divideddifference_bar(S_V_I(rzt,i),c,c);
        i++; 
    };
    ENDR("divideddiff_rz_bar");
}

#ifdef POLYTRUE
INT divideddifference_bar(i,poly,c) OP i,poly,c;
{

    OP     zeiger = poly, zwischen;
    INT     index = S_I_I(i) -1L, j,k, expo1, expo2 ,erg = OK;

    if (EMPTYP(poly)) return(OK);
    zwischen = callocobject();
    if (poly == c)
    { 
        *zwischen = *c;
        C_O_K(c,0);
        erg += divideddifference_bar(i,zwischen,c);
        erg += freeall(zwischen); 
        return erg;
    };
    init(POLYNOM,c);
        
    if (index < 0L) /* symplectic */
        {
        index++;
        copy(poly,zwischen);
        zeiger =zwischen;
        while (zeiger != NULL)
            {
            if (S_L_S(zeiger) != NULL) {
            if (S_PO_SLI(zeiger) >= -index)
            if (S_PO_SII(zeiger,-index -1) % 2L == 1L)
                addinvers(S_PO_K(zeiger),S_PO_K(zeiger));
            }
            zeiger = S_PO_N(zeiger);
            }
        sub(poly,zwischen,c);
        zeiger =c;
        while (zeiger != NULL)
            {
            if (S_L_S(zeiger) != NULL) {
            if (S_PO_SLI(zeiger) >= -index)
                {
                dec(S_PO_SI(zeiger,-index-1L));
                div(S_PO_K(zeiger),cons_zwei,S_PO_K(zeiger));
                }
            }
            zeiger = S_PO_N(zeiger);
            }
        freeall(zwischen);
        return OK;
        }


    while (zeiger != NULL)
    {
        if (S_L_S(zeiger) !=  NULL) 
        {
        if (S_O_K(S_PO_S(zeiger)) != VECTOR)
        { 
            printobjectkind(S_PO_S(zeiger));
            error("kind != VECTOR in divideddifference_bar");
            return(ERROR);
        };

        if (S_I_I(i) == S_PO_SLI(zeiger))
        /* operiert auf letzten exponenten */
        { 
            inc(S_PO_S(zeiger));
            M_I_I(0L,S_PO_SI(zeiger,S_I_I(i))); 
        }
        else if (S_I_I(i) > S_PO_SLI(zeiger)) goto dividedend;
        expo1 = S_PO_SII(zeiger,index);
        expo2 = S_PO_SII(zeiger,index + 1L);
        if (expo1 > expo2)
        {
            for (j=expo1-1L,k=expo2 ;j>= expo2; j--,k++)
            { 
            b_skn_po(callocobject(),callocobject(),NULL,zwischen);
            copy(S_PO_S(zeiger),S_PO_S(zwischen));
            copy(S_PO_K(zeiger),S_PO_K(zwischen));
            M_I_I(j,S_PO_SI(zwischen,index));
            M_I_I(k,S_PO_SI(zwischen,index+1L));
            add_apply(zwischen,c);
            freeself(zwischen);
            };
        }
        else if (expo1 < expo2)
        {
            for (j=expo2-1L,k=expo1 ;j>= expo1; j--,k++)
            {
            b_skn_po(callocobject(),callocobject(),NULL,zwischen);
            copy(S_PO_S(zeiger),S_PO_S(zwischen));
            addinvers(S_PO_K(zeiger),S_PO_K(zwischen));
            M_I_I(j,S_PO_SI(zwischen,index));
            M_I_I(k,S_PO_SI(zwischen,index+1));
            add_apply(zwischen,c);
            freeself(zwischen);
            }
        };
        }
dividedend:
        zeiger = S_PO_N(zeiger);
    };
    freeall(zwischen); 
    return(OK);
}
#endif /* POLYTRUE */

INT rz_bar(a,b) OP a,b;
/* AK 050995 */
{
    INT erg = OK;
    OP c;
    CTO(PERMUTATION,"rz_bar(1)",a);

    c = callocobject();
    erg += lehmercode(a,c);
    erg += rz_lehmercode_bar(c,b);
    erg += freeall(c);
    ENDR("rz_bar");
}

INT rz_lehmercode_bar(a,b) OP a,b;
/* AK 020392 */
{
    OP e,f,g;
    INT i,j,k;
    INT erg = OK;
    CTO(VECTOR,"rz_lehmercode_bar(1)",a);

    g = callocobject();
    e = S_V_I(a,0L);
    f = S_V_I(a,1L);
    erg += sum(f,g);
    j=0L;
    for (i=0L;i<S_V_LI(e);i++)
        j += S_V_II(e,i)*(i+1L);
    j += S_I_I(g); /* j is the length of reduced decomposition */
    erg += m_il_v(j,b);
    if (j == 0L) goto ende;
    j=0L; /* position in rc */
    for (i=0L;i<S_V_LI(e);i++)
        if (S_V_II(e,i) == 1L)
            {
            for (k=i+1L;k>1L;k--,j++)
                erg += m_i_i(k-1L,S_V_I(b,j));
            erg += m_i_i(-1L,S_V_I(b,j++));
            }
    /* now the rc for the lehmercode in f */
    erg += rz_lehmercode(f,g);
    for (i=0L;i<S_V_LI(g);i++,j++)
        erg += m_i_i(S_V_II(g,i),S_V_I(b,j));
ende:
    erg += freeall(g);
    ENDR("rz_lehmercode_bar");
}

INT sscan_bar(t,a) OP a; char *t;
/* AK 050194 to read permutation from string
        format [1,2,3,..]
*/
{
    INT erg = OK;
    COP("sscan_bar(1)",t);
    CTO(EMPTY,"sscan_bar(2)",a);
    erg += b_ks_p(VECTOR,callocobject(),a);
    erg += sscan(t,INTEGERVECTOR,S_P_S(a));
    C_P_K(a,BAR);
    ENDR("sscan_permutation");
}

INT scan_bar(b) OP b;
/* AK 230695 */
{
    INT erg=OK;
    CTO(EMPTY,"scan_bar(1)",b);
spa:
    erg = OK;
    erg += b_ks_p(VECTOR,callocobject(),b);
    erg += printeingabe("input of a barred permutation in list notation");
    erg += scan(INTEGERVECTOR,S_P_S(b));
    C_P_K(b,BAR);
    if (not strong_check_barp(b))
        {
        fprintln(stderr,b);
        printeingabe("wrong input, please enter a barred permutation");
        goto spa;
        }
    ENDR("scan_bar");
}

INT strong_check_barp(a) OP a;
/* AK 230695 */
{
    OP h;
    INT i,SYM_abs();

    if (a == NULL)
        return FALSE;
    if (S_O_K(a) != PERMUTATION)
        return FALSE;
    if      (
       (S_P_K(a) == BARCYCLE)
            ||
       (S_P_K(a) == BAR)
            )
        {
        if (S_P_S(a) == NULL)
            return FALSE;
        if (
            (S_O_K(S_P_S(a)) != INTEGERVECTOR) 
             &&
             (S_O_K(S_P_S(a)) != VECTOR) 
           )                       
            return FALSE;
        h = callocobject();
        m_il_v(S_P_LI(a),h);
        for (i=0L;i<S_V_LI(h);i++)
            M_I_I(i+(INT)1, S_V_I(h,i));
        for (i=0L;i<S_V_LI(h);i++)
            M_I_I((INT)0, S_V_I(h,SYM_abs(S_P_II(a,i)) -(INT)1));
        i = nullp(h);
        freeall(h);
        return i;
        }
    return FALSE;
}


INT first_bar(a,b) OP a,b;
/* AK 230695 */
{
    INT erg = OK;
    CTO(INTEGER,"first_bar",a);
    CE2(a,b,first_bar);
    erg += first_permutation(a,b);
    C_P_K(b,BAR);
    ENDR("first_bar");
}

INT max_bar(a,b) OP a,b;
/* AK 060995 */
/* barred perm with maiximal reduced length */
{
    INT i,erg = OK;
    CTO(INTEGER,"max_bar",a);
    if (check_equal_2(a,b,max_bar,&erg) == EQUAL)
                return erg;
    erg += first_bar(a,b);
    for (i=0;i<S_P_LI(b);i++)
        M_I_I(S_P_II(b,i) * (-1) , S_P_I(b,i));
    C_P_K(b,BAR);
    ENDR("max_bar");
}


INT ordcon_bar(a,b) OP a,b;
/* AK 260292 */
{
    OP c;
    INT erg = OK;
    CTTO(KRANZTYPUS,MATRIX,"ordcon_bar(1)",a);
    c = callocobject();
    erg += hoch(cons_zwei,S_M_H(a),b);
    erg += fakul(S_M_H(a),c);
    erg += mult_apply(c,b);
    erg += ordcen_bar(a,c);
    erg += div(b,c,b);
    erg += freeall(c);
    ENDR("ordcon_bar");
}

INT ordcen_bar(a,b) OP a,b;
/* AK 260292 */
{
    INT i,j;
    INT erg = OK;
    OP c;
    CTTO(KRANZTYPUS,MATRIX,"ordcen_bar(1)",a);
    c = callocobject();
    erg += m_i_i(1L,b);
    for (i=0L;i<S_M_HI(a);i++)
    for (j=0L;j<S_M_LI(a);j++)
        {
        erg += fakul(S_M_IJ(a,i,j),c); 
        erg += mult_apply(c,b);
        erg += m_i_i((i+1L) * 2L,c); 
        erg += hoch(c,S_M_IJ(a,i,j),c);
        erg += mult_apply(c,b);
        }
    erg += freeall(c);
    ENDR("ordcen_bar");
}

INT makevectorof_class_rep_bar(a,b) OP a,b;
/* AK 260292 */
{
    INT i,erg=OK;
    OP c;
    CTO(INTEGER,"makevectorof_class_rep_bar(1)",a);
    c = callocobject();
    
    erg += makevectorof_class_bar(a,c);
    erg += m_il_v(S_V_LI(c),b);
    for (i=0L;i<S_V_LI(c);i++)
        erg += class_rep_bar(S_V_I(c,i),S_V_I(b,i));
    erg += freeall(c);
    ENDR("makevectorof_class_rep_bar");
}

INT makevectorof_class_bar(a,b) OP a,b;
/* AK 260292 */
{
    INT i,erg=OK;
    OP c;
    CTO(INTEGER,"makevectorof_class_bar(1)",a);
    c = callocobject();

    erg += makevectorof_kranztypus(a,cons_zwei,c);
    erg += m_il_v(S_V_LI(c),b);
    for (i=0L;i<S_V_LI(b);i++)
        erg += kranztypus_to_matrix(S_V_I(c,i),S_V_I(b,i));
    erg += freeall(c);
    erg += sort(b); /* AK 130592 */
    ENDR("makevectorof_class_bar");
}

INT class_rep_bar(a,b) OP a,b;
/* AK 260292 */
{
    INT i,j,k=0L,l;
    m_il_p(S_M_HI(a),b);
    C_P_K(b,BAR);
    for (i=0L;i<S_M_HI(a);i++)
        {
        for (j=0L;j<S_M_IJI(a,i,0L);j++)
            {
            for (l=0L;l<=i;l++)
                {
                m_i_i(k+2L,S_P_I(b,k));
                k++;
                }
            m_i_i(-(k-i),S_P_I(b,k-1L)); /* damit ist ein i+1 Zykel
                            mit -
                            fertig */
            }
        for (j=0L;j<S_M_IJI(a,i,1L);j++)
            {
            for (l=0L;l<=i;l++)
                {
                m_i_i(k+2L,S_P_I(b,k));
                k++;
                }
            m_i_i(k-i,S_P_I(b,k-1L)); /* damit ist ein i+1 Zykel 
                            fertig */
            }
        }
    return OK;
}


INT class_bar(a,b) OP a,b;
/* AK 260292 */
{
    INT i,j,k,m,n;
    INT erg = OK;
    OP c;
    CTO(PERMUTATION,"class_bar(1)",a);
    c = callocobject();
    erg += m_ilih_nm(2L,S_P_LI(a),b);
    erg += t_BAR_BARCYCLE(a,c);
    m = ((S_P_II(c,0L) < 0L) ? -S_P_II(c,0L) : S_P_II(c,0L) );
    j=0L;n=0L;
    for (i=0L;i<S_P_LI(c);i++)
        {
        k = ((S_P_II(c,i) < 0L) ? -S_P_II(c,i) : S_P_II(c,i) );
        /* wert ohne vorzeichen */
        if (k < m) /* d.h. hier geht ein neuer Zykel los */
            {
            /* j ist laenge, n anzahl minus */
            INC_INTEGER (S_M_IJ(b,j-1L,n%2L));
            m = ((S_P_II(c,i) < 0L) ? -S_P_II(c,i) : S_P_II(c,i) );
            /* m ist der wert am zykel anfang */
            j = 1L;
            n = ((S_P_II(c,i) < 0L) ? 1L : 0L );
            }
        else    {
            j++; /* der zykel geht weiter */
            if (S_P_II(c,i) < 0L)  n ++; /* noch ein minus */
            }
        }
    INC_INTEGER (S_M_IJ(b,j-1L,n%2L));
    erg += freeall(c);
    ENDR("class_bar");
}

INT t_BARCYCLE_BAR(a,b) OP a,b;
/* AK 260292 */
{
    INT i,j;
    INT erg = OK;
    OP c;
    CTO(PERMUTATION,"t_BARCYCLE_BAR",a);
    CE2(a,b,t_BARCYCLE_BAR);

    c = callocobject();
    erg += copy_permutation(a,c);
    for (i=0L;i<S_P_LI(c); i++)
        if (S_P_II(c,i) < 0L) M_I_I(-S_P_II(c,i), S_P_I(c,i));
    C_P_K(c,ZYKEL);
    erg += t_zperm_vperm(c,b);
    C_P_K(b,BAR);
    for (i=0L;i<S_P_LI(a); i++)
        if (S_P_II(a,i) < 0L)
            for (j=0L;j<S_P_LI(b); j++)
                if (S_P_II(b,j) == - S_P_II(a,i))
                    {
                    M_I_I(-S_P_II(b,j), S_P_I(b,j));
                    break;
                    }
    erg += freeall(c);
    ENDR("t_BARCYCLE_BAR");
}

INT t_BAR_BARCYCLE(a,b) OP a,b;
/* AK 260292 */
{
    INT i,j;
    OP c = callocobject();
    copy(a,c);
    for (i=0L;i<S_P_LI(c); i++)
        if (S_P_II(c,i) < 0L) M_I_I(-S_P_II(c,i), S_P_I(c,i));
    C_P_K(c,VECTOR);
    t_vperm_zperm(c,b);
    C_P_K(b,BARCYCLE);
    for (i=0L;i<S_P_LI(a); i++)
        if (S_P_II(a,i) < 0L)
            for (j=0L;j<S_P_LI(b); j++)
                if (S_P_II(b,j) == - S_P_II(a,i))
                    {
                    M_I_I(-S_P_II(b,j), S_P_I(b,j));
                    break;
                    }
    freeall(c);
    return OK;
}

INT mult_bar_bar(a,b,c) OP a,b,c;
/* AK 250292 */
{
    INT i;
    INT erg = OK;
    CTO(PERMUTATION,"mult_bar_bar(1)",a);
    CTO(PERMUTATION,"mult_bar_bar(2)",b);
    SYMCHECK( S_P_LI(a) != S_P_LI(b) ,
        "mult_bar_bar: different lengths");

    erg += m_il_p(S_P_LI(a),c);
    C_P_K(c,BAR);
    for (i=0L;i<S_P_LI(c);i++)
    {
    if (S_P_II(b,i) < 0L) 
        {
        /* if (S_P_II(a, - S_P_II(b,i) -1L)  > 0L) */
            erg += m_i_i(- S_P_II(a,- S_P_II(b,i)-1L), S_P_I(c,i));
        /* else
            erg += m_i_i(- S_P_II(a,- S_P_II(b,i)-1L), S_P_I(c,i));*/
        }
    else
        erg += m_i_i(S_P_II(a,S_P_II(b,i)-1L), S_P_I(c,i));

    }
    ENDR("mult_bar_bar");
}

INT random_bar(n,b) OP n,b;
/* AK 250292 */
{
    OP a,c;
    INT i,erg = OK;
    CTO(INTEGER,"random_bar(1)",n);
    CTO(EMPTY,"random_bar(2)",b);

    a = callocobject();
    c = callocobject();
    erg += m_il_v(2L,a);
    erg += m_l_nv(n,S_V_I(a,0L));
    erg += random_permutation(n,c);
    erg += lehmercode(c,S_V_I(a,1L));
    for (i=0L;i<S_I_I(n);i++)
        {
        erg += random_integer(c,NULL,NULL);
        if (oddp(c)) 
            erg += m_i_i(1L,S_V_I(S_V_I(a,0L),i));
        }
    erg += lehmercode_vector_bar(a,b);
    erg += freeall(c);
    erg += freeall(a);
    ENDR("random_bar");
}

INT length_bar(a,b) OP a,b;
/* AK 250292 */
{
    OP c,d;
    INT i,erg = OK;
    CTO(PERMUTATION,"length_bar(1)",a);
    CTO(EMPTY,"length_bar(2)",b);
    c = callocobject();
    d = callocobject();
    erg += lehmercode_bar(a,c);
    erg += sum(S_V_I(c,1L),b);
    for(i=0L;i<S_P_LI(a);i++)
        {
        if (S_V_II(S_V_I(c,0L),i) == 1L)
            {
            erg += m_i_i(i+1L,d);
            erg += add_apply(d,b);
            }
        }
    erg += freeall(c);
    erg += freeall(d);
    ENDR("length_bar");
}

INT lehmercode_bar(a,b) OP a,b;
/* AK 250292 */
{
    INT i,j;
    INT erg = OK;
    CTO(PERMUTATION,"lehmercode_bar(1)",a);
    SYMCHECK(S_P_K(a) != BAR,"lehmercode_bar(1):no barred permutation");

    m_il_v(2L,b);
    m_l_nv(S_P_L(a),S_V_I(b,0L));
    m_l_nv(S_P_L(a),S_V_I(b,1L));
    for (i=0L;i<S_P_LI(a);i++)
        {
        if (S_P_II(a,i) < 0L) 
            m_i_i(1L,S_V_I(S_V_I(b,0L),-S_P_II(a,i) -1L));
        for (j=i+1L;j<S_P_LI(a);j++)
            if (S_P_II(a,j) < S_P_II(a,i))
                inc(S_V_I(S_V_I(b,1L),i));
        }
    ENDR("lehmercode_bar");
}


INT next_apply_bar(a) OP a;
/* AK 120902 V2.1 */ 
{
    return next_bar(a,a);
}
INT next_bar(a,b) OP a,b;
/* AK 230695 */
/* AK 120902 V2.1 */
/* a and b may be equal */
{
    INT erg,i;
    OP c,d;
    c = callocobject();
    d = callocobject();
    lehmercode_bar(a,c);
    m_il_v(2L,d);
    erg = next_lehmercode(S_V_I(c,1L),S_V_I(d,1L));
    if (erg != LASTLEHMERCODE)
        {
        copy(S_V_I(c,0L),S_V_I(d,0L));
        goto bb;
        }
    /* now next distribution of minus */
    copy(S_V_I(c,0L),S_V_I(d,0L));
    erg = 0;
    for (i=0;i<S_V_LI(S_V_I(d,0L));i++)
        if (S_V_II(S_V_I(d,0L),i) == 1) erg++;
    /* erg == gewicht */
    if (erg == S_P_LI(a))
        {
        erg = LASTPERMUTATION;
        goto aa;
        }
    first_lehmercode(S_P_L(a),S_V_I(d,1L));
    /* now vector of minus */
    for (i=1;i<S_V_LI(S_V_I(d,0L));i++)
         if ((S_V_II(S_V_I(d,0L),i) == 0) &&
            (S_V_II(S_V_I(d,0L),i-1) == 1) )
            {
            M_I_I(1,S_V_I(S_V_I(d,0L),i));
            M_I_I(0,S_V_I(S_V_I(d,0L),i-1));
            goto bb;
            }
    /* now all the minus are on the right end */
    for (i=0;i<= erg;i++)
         M_I_I(1,S_V_I(S_V_I(d,0L),i));
    for (;i<S_P_LI(a);i++)
         M_I_I(0,S_V_I(S_V_I(d,0L),i));
        
bb:
    lehmercode_vector_bar(d,b);
    erg = OK;
    
aa:
    freeall(c);
    freeall(d);
    return erg;
}


INT lehmercode_vector_bar(a,b) OP a,b;
/* AK 250292 */
{
    INT i,j,k;
    OP self,liste,vec;
    k= S_V_LI(S_V_I(a,0L));

    self = callocobject();
    liste = callocobject();

    m_il_v(k,self);
    m_il_v(k,liste);
    /* initialisierung zweier vektoren fuer
        eine Liste und fuer die zu berechnende Permutation */
    j=0L;
    for(i=k-1L;i>=0L;i--)
        {
        if (S_V_II(S_V_I(a,0L),i) == 1L)
            m_i_i(-i-1L,S_V_I(liste,j++));
        }
    for(i=0L;i<k;i++)
        {
        if (S_V_II(S_V_I(a,0L),i) == 0L)
            m_i_i(i+1L,S_V_I(liste,j++));
        }
    /* liste ist jetzt ein vector [..neg..pos..] */
    vec = S_V_I(a,1L);
    for(i=0L;i<S_V_LI(vec);i++)
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
    freeall(liste);

    b_ks_p(BAR,self,b);
    /* bildung einer Permutation aus dem vector */
    return(OK);
}

#ifdef POLYTRUE

INT new_divideddifference_bar(i,poly,c) OP i,poly,c;
{
    divideddifference_bar(i,poly,c);
/*    if (S_I_I(i) > 0) 
        addinvers(c,c); */
    return OK;
}

INT scalarproduct_bar_schubert(a,b,g) OP a,b,g;
{
    INT erg = OK;
    OP c,d,e,f;
    CTO(PERMUTATION,"scalarproduct_bar_schubert(1)",a);
    CTO(SCHUBERT,"scalarproduct_bar_schubert(2)",b);

    c = callocobject();
    d = callocobject();
    e = callocobject();
    f = callocobject();
    erg += max_bar(S_P_L(a),c);
    erg += mult(b,c,d);
    erg += m_bar_schubert(a,e);
    erg += m_bar_schubert(d,f);
    erg += mult(f,e,e);
    erg += divdiff(c,e,g);
    erg += freeall(c);
    erg += freeall(d);
    erg += freeall(e);
    erg += freeall(f);
    ENDR("scalarproduct_bar_schubert");
}

INT starting_bar_schubert(n,res) OP n,res;
{
    OP a,b,c,y,e,d;
    INT i;
    FILE *fp;
    char s[100];

    sprintf(s,"startbarschubert%ld",S_I_I(n));
    fp = fopen(s,"r");
    if (fp != NULL)
        {
        objectread(fp,res);
        fclose(fp);
        return OK;
        }

    a=callocobject();y=callocobject();e=callocobject();
    b=callocobject();
    c=callocobject();d=callocobject();


    m_i_staircase(n,c);
    m_part_qelm(c,b);

    compute_elmsym_with_alphabet(b,n,res);
    b_skn_po(callocobject(),callocobject(),NULL,d);
    if (((S_I_I(n)*(S_I_I(n)-1))/2)%2 == 0) 
            m_i_i(1L,S_PO_K(d));
    else
            m_i_i(-1L,S_PO_K(d));
    m_il_v(S_I_I(n),S_PO_S(d));
    for (i=0;i<S_PO_SLI(d);i++)
        M_I_I(S_I_I(n)-1-i, S_PO_SI(d,i));
    mult_apply(d,res);

    freeall(a);
    freeall(b);
    freeall(e);
    freeall(c);freeall(d);freeall(y);
    fp = fopen(s,"w");
    if (fp != NULL)
        objectwrite(fp,res);
    fclose(fp);
    return OK;
}

INT m_bar_schubert(bar,res) OP bar,res;
{
    OP a,b,c,y,e,d;
    INT erg = OK;
    CTO(PERMUTATION,"m_bar_schubert(1)",bar);


    CE2(bar,res,m_bar_schubert);

    a=callocobject();y=callocobject();e=callocobject();
    b=callocobject();
    c=callocobject();d=callocobject();

    erg += starting_bar_schubert(S_P_L(bar),c);


    erg += max_bar(S_P_L(bar),e);
    erg += mult(bar,e,b); 

    erg += freeself(res);
    erg += new_divdiff_bar(b,c,res);

    erg += freeall(a);
    erg += freeall(b);
    erg += freeall(e);
    erg += freeall(c);
    erg += freeall(d);
    erg += freeall(y);
    ENDR("m_bar_schubert");
}

#endif /* POLYTRUE */

INT t_bar_doubleperm(a,b) OP a,b;
{
    INT i,k;
    b_ks_p(VECTOR,callocobject(),b);
    m_il_v(S_P_LI(a)*2,S_P_S(b));
    for (i=0,k=S_P_LI(b)-1; i<S_P_LI(a);i++,k--)
        {
        if (S_P_II(a,i) < 0)
            {
            M_I_I(S_P_II(a,i)+S_P_LI(a)+1, S_P_I(b,i));
            M_I_I(-S_P_II(a,i)+S_P_LI(a), S_P_I(b,k));
            }
        else
            {
                        M_I_I(S_P_II(a,i)+S_P_LI(a), S_P_I(b,i));
                        M_I_I(-S_P_II(a,i)+S_P_LI(a)+1, S_P_I(b,k));
            }
        }
    return OK;
}

INT bar_rectr(a,v) OP a,v;
/* input double perm output rectr */
/* half of rectr of s_2n */
{
OP  b,u; INT i,k,x,y,z,iv,i1;
                   b=callocobject();u=callocobject();
 invers(a,b);    init(VECTOR,v);m_il_v(3L,u);iv=0L;
 for(i=0L;i<S_P_LI(a)-1L;i++)
   {if( S_P_II(a,i)>S_P_II(a,i+1))
     {z= S_P_II(a,i); x=S_P_II(a,i+1);
       for (k=z;k>=x;k--)
        {if  ( S_P_II(b,k-1) >= i+2 && S_P_II(b,k) <=i+1)
          {y=0; for(i1=0;i1<=i;i1++) { if( S_P_II(a,i1) <k) y++;}
             if( (k+1L+i < S_P_LI(a)) ||( (k+1L+i== S_P_LI(a)) && (i+1<=k)) )
               { M_I_I(y,S_V_I(u,0L)); M_I_I(i+1-y,S_V_I(u,1L));
                    M_I_I(k-y,S_V_I(u,2L));
                       inc(v);copy(u,S_V_I(v,iv)); iv++; }  }}} }
                                     freeall(b);freeall(u);
    return OK;
}

INT comp_bigr_perm(u,perm)  OP u,perm;
/* compare bigrassmannian (= vector of length 3 ) with permutation */
/* returns TRUE if u <= perm in bruhat order FALSE else */
/* works for s_n */
{  INT i,x,r0,r1,r2;
        r0=S_V_II(u,0L);r1=S_V_II(u,1L);r2=S_V_II(u,2L); x=0L;
  for(i=0L;i<r0+r1;i++)  { if (S_P_II(perm,i) >r0+r2 ) x++; }
      if(x< r1) return (FALSE); else return (TRUE);
}

/*   rectrices  de Sn sur 3 composantes; renvoie 1 si  u <= v , 0 sinon */
INT comp_bigr_bigr(u,v)  OP u,v;
/* compares according bruhat */
/* returns 1 if u <= v */
/* works for s_n */
{ if (S_V_II(u,0L)< S_V_II(v,0L) ) return 0L;
  if (S_V_II(u,1L)>S_V_II(v,1L)) return 0L;
  if (S_V_II(u,2L)>S_V_II(v,2L)) return 0L;
  if (S_V_II(u,0L)+ S_V_II(u,1L)+S_V_II(u,2L) >S_V_II(v,0L)+S_V_II(v,1L)+S_V_II(v,2L) ) return 0L;
 return 1L;
}

#endif /* PERMTRUE */
