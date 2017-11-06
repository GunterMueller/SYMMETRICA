/* nc.c SYMMETRICA source code */
#include "def.h"
#include "macro.h"

static INT m_nc_sym();
static INT m_nc_alt();

/* PF 060292 */ /* PF 040692 */
/***********************************************************************/
/*                                                                     */
/*    Diese Routine berechnet den Vektor der Konjugiertenklassen       */
/*    der An.                                                          */
/*    Rueckgabewert: OK oder error                                     */
/*                                                                     */
/***********************************************************************/

INT ak_make_alt_classes(n,res)
    OP n;        /* Gewicht der Partitionen */
    OP res;        /* Vektor der Konjugiertenklassen der An */
    {
    OP par;        /* Partition von n */
    OP per;     /* Permutation */ 
    OP sgn;     /* Signum der Permutation */ 
    OP l;        /* Anzahl der verschiedenen Konjugiertenklassen der An */
    INT i=0L;
    INT erg=OK;

    INT alt_dimension();    /* Hilfsroutinen */
    INT split();


    CTO(INTEGER,"ak_make_alt_classes(1)",n);

    FREESELF(res);

    /*** Test auf Ganzzahligkeit von n ************************************/

    SYMCHECK (S_I_I(n) <= 0, "ak_make_alt_classes : n <= 0");
    
    /*** Speicherplatzreservierung fuer die Objekte ***********************/

    par=callocobject();
    per=callocobject();
    sgn=callocobject();
    l=callocobject();

    /*** Berechnung des Partitionenvektors (eigentlich eine Matrix) *********/

    erg += alt_dimension(n,l);
    erg += m_il_v(S_I_I(l),res);
    erg += first_partition(n,par);
    do    {
        erg += m_part_perm(par,per);
        erg += signum(per,sgn);
        if(S_I_I(sgn) == 1L)
            {
            if(split(n,par)==1L)
                {
                m_il_v(2L,S_V_I(res,i));
                erg += copy(par,S_V_I(S_V_I(res,i),0L));
                erg += m_i_i(0L,S_V_I(S_V_I(res,i),1L));
                i++;
                m_il_v(2L,S_V_I(res,i));
                erg += copy(par,S_V_I(S_V_I(res,i),0L));
                erg += m_i_i(1L,S_V_I(S_V_I(res,i),1L));
                }
            else    {
                erg += copy(par,S_V_I(res,i));
                }
            i++;
            }
        }
    while(next(par,par));

    /*** Speicherplatzfreigabe *********************************************/

    erg += freeall(par);
    erg += freeall(per);
    erg += freeall(sgn);
    erg += freeall(l);

    /*** Rueckkehr in die aufrufende Routine *******************************/

    ENDR("ak_make_alt_classes");
} /* Ende von make_alt_classes */

INT ak_make_alt_partitions(n,res)
    OP n;        /* Gewicht der Partitionen */
    OP res;        /* Vektor der irred. Darst. der An */
    {
    OP par;        /* Partition von n */
    OP conpar;     /* konjugierte Partition */ 
    OP l;        /* Anzahl der verschiedenen irred. Darst. der An */
    INT i=0L,j;
    INT erg=OK;

    INT alt_dimension();    /* Hilfsroutinen */
    INT part_comp();


    /*** Test auf Ganzzahligkeit von n ************************************/

    CTO(INTEGER,"ak_make_alt_partitions",n);
    if (S_I_I(n) <= 0L)
        {
        error("ak_make_alt_partitions : n <= 0");
        return ERROR;
        }
    
    /*** Speicherplatzreservierung fuer die Objekte **********************/

    par=callocobject();
    conpar=callocobject();
    l=callocobject();

    /*** Berechnung des Partitionenvektors (eigentlich eine Matrix) *******/

    erg += alt_dimension(n,l);
    erg += m_il_v(S_I_I(l),res);
    erg += first_partition(n,par);
    do    {
        erg += conjugate(par,conpar);
        j=part_comp(par,conpar);
        if(j==0L)
                /* zerfaellt */
                {
                erg += m_il_v(2L,S_V_I(res,i));
                erg += copy(par,S_V_I(S_V_I(res,i),0L));
                erg += m_i_i(0L,S_V_I(S_V_I(res,i),1L));
                i++;
                erg += m_il_v(2L,S_V_I(res,i));
                erg += copy(par,S_V_I(S_V_I(res,i),0L));
                erg += m_i_i(1L,S_V_I(S_V_I(res,i),1L));
                i++;
                }
        else if (j>0L)    {
                /* zerfaellt nicht */
                erg += copy(par,S_V_I(res,i));
                i++;
                }
        }
    while(next_apply(par));

    /*** Speicherplatzfreigabe *********************************************/
    FREEALL3(par,conpar,l);
    /*** Rueckkehr in die aufrufende Routine *******************************/

    ENDR("ak_make_alt_partitions");
}

INT scan_gl_nc(a,b) OP a,b;
/* AK 100692 */
{
    OBJECTKIND k;
    INT i,erg = OK;
    OP c;
    CTO(EMPTY,"scan_gl_nc(2)",b);

    c = callocobject();
    erg += printeingabe("input of a character");
    erg += printeingabe("grouplabel = "); println(a);
    erg += m_il_v(2L,b); copy(a,S_NC_GL(b));
    erg += printeingabe("type of charactervalues");
    k = scanobjectkind();
    erg += m_gl_cl(a,c);
    erg += m_il_v(S_V_LI(c),S_NC_C(b));
    for (i=0L;i<S_V_LI(c);i++)
        {
        erg += println(S_V_I(c,i));
        erg += scan(k,S_V_I(S_NC_C(b),i));
        }
    erg += freeall(c);
    ENDR("scan_gl_nc");
}

#ifdef CHARTRUE
INT reduce_nc(a,b) OP a,b;
{
    OP c,d;
    INT i, erg=OK;
    CTO(VECTOR,"reduce_nc(1)",a);
    c =callocobject();
    d =callocobject();
    erg += m_gl_il(S_NC_GL(a),c);
    erg += copy(a,b);
    for (i=0L;i<S_V_LI(c);i++)
        {
        erg += m_gl_nc(S_NC_GL(a),S_V_I(c,i),d);
        erg += scalarproduct_nc(d,a,S_V_I(S_NC_C(b),i));
        }
    FREEALL2(c,d);
    ENDR("reduce_nc");
}



INT scalarproduct_nc(a,b,c) OP a,b,c;
{
    OP d,e;
    INT erg = OK;

    d = callocobject();
    e = callocobject();
    erg += mult(S_NC_C(a),S_NC_C(b),d);
    erg += m_gl_co(S_NC_GL(a),e);
    erg += mult_apply(e,d);
    erg += sum(d,e);
    erg += m_gl_go(S_NC_GL(a),d);
    erg += div(e,d,c);
    erg += freeall(e);
    erg += freeall(d);
    return erg;
}
#endif /* CHARTRUE */
INT m_gl_go(a,b) OP a,b;
/* grouporder */
{
    INT erg;
    if (SYM_GL(a))
        return fakul(S_GL_SYM_A(a),b);
    if (ALT_GL(a))
        {
        erg = fakul(S_GL_ALT_A(a),b);
        if (not einsp(b)) /* sonderfall a1 */
            erg += ganzdiv(b,cons_zwei,b);
        return erg;
        }
    if (CYCLIC_GL(a)) /* AK 291092 */
        return copy(S_GL_CYCLIC_A(a),b);
#ifdef KRANZTRUE
    if (KRANZ_GL(a))
        {
        return grouporder_kranz(a,b);
        }
#endif /* KRANZTRUE */
    return error("can not compute grouporder");
}

#ifdef CHARTRUE
INT m_gl_il(a,b) OP a,b;
/* AK 090692 */
/* labeles of irreducible characters */
{
    INT erg = OK;
    INT i;
    CE2(a,b,m_gl_il);


    if (CYCLIC_GL(a)) /* AK 300695 */
        {
        erg += m_l_v(S_GL_CYCLIC_A(a), b);
        for (i=0;i<S_V_LI(b);i++)
            M_I_I(i,S_V_I(b,i));
        goto ende;
        }
    else if (SYM_GL(a))
        {
        erg += makevectorofpart(S_GL_SYM_A(a),b);
        goto ende;
        }
    else if (ALT_GL(a))
        {
        erg += ak_make_alt_partitions(S_GL_ALT_A(a),b);
        goto ende;
        }
#ifdef KRANZTRUE
    else if (KRANZ_GL(a))
        {
        erg += m_vcl_kranz(a,b);
        goto ende;
        }
#endif /* KRANZTRUE */
    else 
        erg += error("can not compute irr labeling");
ende:
    ENDR("m_gl_il");
}



INT m_gl_nc(a,b,c) OP a,b,c;
/* AK 090692 */
{
    OP d;
    INT erg = OK,i;
    if (SYM_GL(a))
        {
        if (S_O_K(b) == PARTITION)
            return m_nc_sym(b,c);
        if (S_O_K(b) == INTEGER)
            {
            d = callocobject();
            erg += m_gl_il(a,d);
            erg += m_nc_sym(S_V_I(d,S_I_I(b)),c);
            erg += freeall(d);
            return erg;
            }
        }
    if (ALT_GL(a))
        {
        if ((S_O_K(b) == PARTITION) /* no splitting rep */
            ||
            (S_O_K(b) == VECTOR) /* splitting */ )
            return m_nc_alt(a,b,c);
        if (S_O_K(b) == INTEGER)
            {
            d = callocobject();
            erg += m_gl_il(a,d);
            erg += m_nc_alt(a,S_V_I(d,S_I_I(b)),c);
            erg += freeall(d);
            return erg;
            }
        }
#ifdef KRANZTRUE
    if (KRANZ_GL(a))
        {
        if (S_O_K(b) == INTEGER)
            return m_nc_kranz(a,b,c);
        if ( (S_O_K(b) == MATRIX) ||
             (S_O_K(b) == KRANZTYPUS)) 
            {
            d = callocobject();
            erg += m_gl_il(a,d);
            for(i=0L;i<S_V_LI(d);i++)
                if (eq(b,S_V_I(d,i)))
                    {m_i_i(i,d);break;}
            erg += m_nc_kranz(a,d,c);
            erg += freeall(d);
            return erg;
            }
        }
#endif /* KRANZTRUE */
    println(a); println(b);
    return error("can not compute irr char");
}
#endif /* CHARTRUE */

INT m_gl_cl(a,b) OP a,b;
    /* make group label class label */
{
    INT erg = OK,i;

    CE2(a,b,m_gl_cl);

        if (CYCLIC_GL(a)) /* AK 300695 */
                {
                erg += m_l_v(S_GL_CYCLIC_A(a), b);
                for (i=0;i<S_V_LI(b);i++)
                        M_I_I(i,S_V_I(b,i));
                return erg;
                }
#ifdef PARTTRUE
    else if (SYM_GL(a))
        return makevectorofpart(S_GL_SYM_A(a),b);
    else if (ALT_GL(a))
        return ak_make_alt_classes(S_GL_ALT_A(a),b);
#endif /* PARTTRUE */
#ifdef KRANZTRUE
    else if (KRANZ_GL(a))
        return m_vcl_kranz(a,b);
#endif /* KRANZTRUE */
    else 
        erg += error("can not compute class labeling");
    ENDR("m_gl_cl");
}

INT m_gl_ge_cl(a,b,c) OP a,b,c;
/* AK 190202 */
/* enter group label a and group element b, get class label */
{
    INT erg = OK;
    CTO(VECTOR,"m_gl_ge_cl(1)",a);
    if (SYM_GL(a))
        {
        CTO(PERMUTATION,"m_gl_ge_cl(2)",b);
        erg += zykeltyp(b,c);
        goto ende;
        }
    else if (ALT_GL(a))
        {
        OP d;
        CTO(PERMUTATION,"m_gl_ge_cl(2)",b);
        d = CALLOCOBJECT();
        erg += zykeltyp(b,d);
        if (split(S_GL_ALT_A(a),d) ) {
            m_il_v(2,c);
            SWAP(d,S_V_I(c,0));
            M_I_I(which_part(b),S_V_I(c,1));
            }
        else 
            SWAP(c,d);
        FREEALL(d);
        goto ende;
        }
    else {
        NYI("m_gl_ge_cl");
        }
ende:
    ENDR("m_gl_ge_cl");
}

INT m_gl_co(a,b) OP a,b;
/* class order */
{
    OP c,d;
    INT i,erg=OK;
    CE2(a,b,m_gl_co);
                                           
    if (CYCLIC_GL(a)) /* AK 300695 */
        {
        erg += m_l_v(S_GL_CYCLIC_A(a), b);
        for (i=0;i<S_V_LI(b);i++)
            M_I_I((INT)1,S_V_I(b,i));
        return erg;
        }
    else if (SYM_GL(a))
        {
        c = callocobject();
        erg += m_gl_cl(a,c);
        erg += m_l_v(S_V_L(c),b);
        for (i=0L;i<S_V_LI(b);i++)
            {
            erg += ordcon(S_V_I(c,i),S_V_I(b,i));
            }
        erg += freeall(c);
        return erg;
        }
    else if (ALT_GL(a))
        {
        c = callocobject();
        erg += m_gl_cl(a,c);
        erg += m_l_v(S_V_L(c),b);
        for (i=0L;i<S_V_LI(b);i++)
            {
            if (S_O_K(S_V_I(c,i)) == PARTITION)
                erg += ordcon(S_V_I(c,i),S_V_I(b,i));
            else /* is a splitting class */
                {
                erg += ordcon(S_V_I(S_V_I(c,i),0L),S_V_I(b,i));
                erg += div(S_V_I(b,i),cons_zwei,S_V_I(b,i));
                }
            }
        erg += freeall(c);
        return erg;
        }
#ifdef KRANZTRUE
    else if (KRANZ_GL(a))
        {
        c = callocobject();
        d = callocobject();
        erg += m_gl_cl(a,c);
        erg += m_gl_cl(S_GL_KRANZ_GLA(a),d); /* labeling of classes
                    for the first group */
        erg += m_l_v(S_V_L(c),b);
        for (i=0L;i<S_V_LI(b);i++)
            {
            erg += typusorder(S_V_I(c,i),
                S_GL_KRANZ_A(a),S_GL_KRANZ_B(a),
                S_V_I(b,i),d);
            }
        erg += freeall(d);
        erg += freeall(c);
        return erg;
        }
#endif /* KRANZTRUE */
    else 
        erg += error("can not compute class order");
    ENDR("m_gl_co");
}

INT m_gl_cr(a,b) OP a,b;
/* class rep */
/* b will be a vector object of length = number of classes */
{
    OP c;
    INT i,j,erg=OK;
    CE2 (a,b,m_gl_cr);
                
    if (CYCLIC_GL(a))
        {
        erg += m_l_v(S_GL_CYCLIC_A(a),b);
        for (i=0;i<S_V_LI(b);i++)
            {
            erg += m_il_p(S_V_LI(b),S_V_I(b,i));
            for(j=0;j<S_P_LI(S_V_I(b,i));j++)
                erg += m_i_i((1+j+i) % S_V_LI(b),
                    S_P_I(S_V_I(b,i),j));
            }
        goto endr_ende;
        }
    if (SYM_GL(a))
        {
        c = callocobject();
        erg += m_gl_cl(a,c);
        erg += m_l_v(S_V_L(c),b);
        for (i=0L;i<S_V_LI(b);i++)
            {
            erg += m_part_perm(S_V_I(c,i),S_V_I(b,i));
            }
        erg += freeall(c);
        goto endr_ende;
        }
#ifdef MATRIXTRUE
    if (ALT_GL(a))
        {
        c = callocobject();
        erg += makealtclassreps(S_GL_ALT_A(a),c,b);
        erg += freeall(c);
        goto endr_ende;
        }
#endif /* MATRIXTRUE */
    if (GLNQ_GL(a))
        {
        erg += class_label_glnq(S_GL_GLNQ_N(a),S_GL_GLNQ_Q(a),b);
        goto endr_ende;
        }
    error("can not compute class reps");
    ENDR("m_gl_cr");
}

#ifdef CHARTRUE
INT m_gl_chartafel(a,b) OP a,b;
/* AK 080306 */
{
    INT erg = OK;
    if (SYM_GL(a))
        erg += chartafel(S_GL_SYM_A(a),b);
    else if (ALT_GL(a))
        erg += an_tafel(S_GL_SYM_A(a),b);
    else if (CYCLIC_GL(a))
        erg += cyclic_tafel(S_GL_CYCLIC_A(a),b);
#ifdef KRANZTRUE
    else if (KRANZ_GL(a))
        {
        OP c=callocobject();
        OP d=callocobject();
        erg += kranztafel(S_GL_KRANZ_B(a),S_GL_KRANZ_A(a),b,c,d);
        erg += freeall(c);
        erg += freeall(d);
        }
#endif /* KRANZTRUE */
    else 
	{
	erg += error("can not compute character table");
	}
    ENDR("m_gl_chartafel");
}
#endif /* CHARTRUE */

INT cyclic_tafel(a,b) OP a,b;
{
    INT erg = OK,i,j;
    OP c;
    CTO(INTEGER,"cyclic_tafel",a);
    CE2(a,b,cyclic_tafel);
                
    c = callocobject();
    erg += m_lh_m(a,a,b);
    for (i=0;i<S_M_HI(b);i++)
    for (j=0;j<S_M_LI(b);j++)
        {
        m_i_i(i * j,c);
        make_index_coeff_power_cyclo(a,cons_eins,c,S_M_IJ(b,i,j));
        }
    freeall(c);
    ENDR("cyclic_tafel");
}


#ifdef KRANZTRUE
INT m_vec_grad_nc_hyp(v,g,c) OP v,g,c;
/* v is vector with char values 
   g is degree of hyperoktaeder group
   c becomes character
*/
{
    OP d;
    INT erg = OK;
    CTO(VECTOR,"m_vec_grad_nc_hyp(1)",v);
    d = callocobject();
    erg += m_i_i(2L,d);
    erg += m_il_v(2L,c);
    erg += m_gl_symkranz(d,g,S_V_I(c,0L));
    erg += copy(v,S_V_I(c,1L));
    erg += freeall(d);
    ENDR("m_vec_grad_nc_hyp");
}



INT class_rep_kranz(a,b) OP a,b;
/* a is matrix labeling of Sm wr Sn class
   b becomes representing element of the class */
{
    return error("class_rep_kranz:not yet implemented");
}



INT reduce_nc_kranz(a,b) OP a,b;
{
    OP c ,d,e,f,g;
    INT erg = OK;
    CTO(VECTOR,"reduce_nc_kranz(1)",a);
    c = callocobject();
    d = callocobject(); 
    e = callocobject();
    f = callocobject();
    g = callocobject();
    erg += m_i_i(0L,d);
    erg += m_vco_kranz(S_NC_GL(a),f);
    erg += grouporder_kranz(S_NC_GL(a),g);
    erg += copy(a,b);
    for (;lt(d,S_V_L(S_V_I(b,1L)));inc(d))
    {
        erg += m_nc_kranz(S_NC_GL(a),d,c);
        erg += mult_nc_kranz(c,a,e);
        erg += mult(S_V_I(e,1L),f,c);
        erg += div(c,g,c);
        erg += sum(c,S_V_I(S_NC_C(b),S_I_I(d)));
    }
    erg += freeall(c); 
    erg += freeall(d); 
    erg += freeall(e); 
    erg += freeall(f); 
    erg += freeall(g);
    ENDR("reduce_nc_kranz");
}



INT mult_nc_kranz(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(VECTOR,"mult_nc_kranz(1)",a);
    CTO(VECTOR,"mult_nc_kranz(2)",b);
    if (neq(S_NC_GL(a),S_NC_GL(b))) 
        error("mult_nc_kranz:different groups");
    erg += copy(a,c);
    erg += mult(S_NC_C(a),S_NC_C(b),S_NC_C(c));
    ENDR("mult_nc_kranz");
}



INT grouporder_kranz(l,a) OP l,a;
{
    OP zz,z;
    INT erg = OK;
    CTO(VECTOR,"grouporder_kranz(1)",l);
    z = callocobject();
    zz = callocobject();
    erg += fakul(S_GL_KRANZ_B(l),z);
    erg += fakul(S_GL_KRANZ_A(l),zz);
    erg += hoch(zz,S_GL_KRANZ_B(l),a);
    erg += mult_apply(z,a);
    erg += freeall(z); 
    erg += freeall(zz);
    ENDR("grouporder_kranz");
}



INT scan_nc_kranz(a) OP a;
{
    OP b,c,l,d;
    OBJECTKIND k;
    INT i;
    INT erg = OK;
    CTO(EMPTY,"scan_nc_kranz(1)",a);
    b = callocobject();
    c = callocobject();
    l = callocobject();
    d = callocobject();
    erg += scan(INTEGER,b);
    erg += scan(INTEGER,c);
    erg += m_gl_symkranz(b,c,l);
    erg += numberof_class_kranz(l,d);
    erg += k=scanobjectkind();
    erg += m_il_v(2L,a);
    erg += copy(l,S_V_I(a,0L));
    erg += m_l_v(d,S_V_I(a,1L));
    for (i=0L;i<S_I_I(d);i++)
        erg += scan(k,S_V_I(S_V_I(a,1L),i));
    erg += freeall(b);
    erg += freeall(c);
    erg += freeall(l);
    erg += freeall(d);
    ENDR("scan_nc_kranz");
}



INT m_vcl_kranz(l,a) OP l,a;
/* AK 050692 */
/* computes the class labeling of a wreath product
   of two symm groups. l is the corresponding group label */
/* a becomes vector of matrices */
{
    OP za,zb;
    OP f,c,h;
    INT j;
    za = S_V_I(S_V_I(S_V_I(l,1L),1L),1L);
    zb = S_V_I(S_V_I(S_V_I(l,1L),0L),1L);
/* zb wr za */
    f = callocobject();
    c = callocobject();
    h = callocobject();
    makevectorofpart(zb,f);
    makevectorof_kranztypus(za,S_V_L(f),c);
    m_il_v(S_V_LI(c),a);
    for(j = 0L; j<S_V_LI(c);j++) {
        kranztypus_to_matrix(S_V_I(c,j),S_V_I(a,j)); 
    }
    sort(a);
    freeall(f); freeall(h); freeall(c);
    return OK;
}
#endif /* KRANZTRUE */

#ifdef KRANZTRUE
INT m_vco_kranz(l,a) OP l,a;
/* vector of class orders of a wreath product of two symm
    groups */
{
    OP za,zb;
    OP f,c,h;
    INT j;
    za = S_V_I(S_V_I(S_V_I(l,1L),1L),1L);
    zb = S_V_I(S_V_I(S_V_I(l,1L),0L),1L);
/* zb wr za */
    f = callocobject();
    c = callocobject();
    h = callocobject();
    makevectorofpart(zb,f);
    makevectorof_kranztypus(za,S_V_L(f),c);
    m_il_v(S_V_LI(c),h);
    for(j = 0L; j<S_V_LI(c);j++) {
        kranztypus_to_matrix(S_V_I(c,j),S_V_I(h,j)); 
        }
    
    sort(h); 
    m_l_v(S_V_L(h),a);
    for(j = 0L; j<S_V_LI(c);j++) {
        typusorder(S_V_I(h,j), zb, za, S_V_I(a,j), f);
        }
    freeall(f); freeall(c); freeall(h);
    return OK;
}



INT numberof_class_kranz(l,a) OP l,a;
{
    INT erg = OK;
    OP za,zb;
    OP f,c;
    za = S_V_I(S_V_I(S_V_I(l,1L),1L),1L);
    zb = S_V_I(S_V_I(S_V_I(l,1L),0L),1L);
/* zb wr za */
    f = callocobject();
    c = callocobject();
    erg += makevectorofpart(zb,f);
    erg += makevectorof_kranztypus(za,S_V_L(f),c);
    erg += copy(S_V_L(c),a);
    erg += freeall(f);
    erg += freeall(c);
    return erg;
}



INT order_class_kranz(l,i,a) OP l,i,a;
{
    OP za,zb;
    OP f,c,h;
    INT j;
    INT erg = OK;
    za = S_V_I(S_V_I(S_V_I(l,1L),1L),1L);
    zb = S_V_I(S_V_I(S_V_I(l,1L),0L),1L);
/* zb wr za */
    f = callocobject();
    c = callocobject();
    h = callocobject();
    erg += makevectorofpart(zb,f);
    erg += makevectorof_kranztypus(za,S_V_L(f),c);
    erg += m_il_v(S_V_LI(c),h);
    for(j = 0L; j<S_V_LI(c);j++) {
        erg += kranztypus_to_matrix(S_V_I(c,j),S_V_I(h,j)); 
    }
    
    erg += sort(h);
    erg += typusorder(S_V_I(h,S_I_I(i)), zb, za, a, f);
    erg += freeall(f); 
    erg += freeall(c); 
    erg += freeall(h);
    return erg;
}



INT m_nc_kranz(l,i,b) OP l,i,b;
/* l is group label
   i is integer which selects the i-th ireducible character
   b becomes character
*/
{
    OP c , ll ;
    OP d,e;
    OP za,zb;
    INT erg = OK;
    c = callocobject();
    ll = callocobject(); 

    erg += m_il_v(2L,b);
    erg += copy(l,S_V_I(b,0L));

        d = callocobject();
        e = callocobject();
        za = S_V_I(S_V_I(S_V_I(l,1L),1L),1L);
        zb = S_V_I(S_V_I(S_V_I(l,1L),0L),1L);
        /* zb wr za */
        erg += kranztafel(za,zb,c,d,e);
        erg += copy(l,ll);
        
    if (ge(i,S_M_H(c))) error("m_nc_kranz: wrong index");
    erg += select_row(c,S_I_I(i),S_V_I(b,1L));

        erg += freeall(d);
        erg += freeall(e);
        erg += freeall(ll);
        erg += freeall(c);
        
    return erg;
}



INT m_gl_symkranz(a,b,c) OP a,b,c;
/* make group label for kranzprodukt of two sym groups 
  c = s_a wr s_b */
/* AK 050692 */
{
    m_il_v(2L,c); 
    m_i_i(3L,S_V_I(c,0L));  /* 3 == Kranzprodukt */
    m_il_v(2L,S_V_I(c,1L)); 
    m_gl_sym(a,S_V_I(S_V_I(c,1L),0L));
    m_gl_sym(b,S_V_I(S_V_I(c,1L),1L));
    return OK;
}

INT m_gl_glnq(n,q,c) OP n,q,c;
/* AK 300304 */
{
    m_il_v(2L,c);
    m_i_i(5L,S_V_I(c,0L));  /* 5 == GL(n,q) */
    m_il_v(2L,S_V_I(c,1L));
    m_i_i(n,S_V_I(S_V_I(c,1L),0L));
    m_i_i(q,S_V_I(S_V_I(c,1L),1L));
    return OK;
}



INT m_gl_hyp(a,b) OP a,b;
/* make group-label for hyperoctaeder */ /* AK 050692 */
{
    return m_gl_symkranz(cons_zwei,a,b);
}
#endif /* KRANZTRUE */

INT m_gl_cyclic(a,b) OP a,b;
/* make group-label for cyclic */ /* AK 291092 */
{
    INT erg = OK;
    CTO(INTEGER,"m_gl_cyclic(1)",a);
    erg += m_il_v(2L,b); 
    erg += m_i_i(4L,S_V_I(b,0L)); /* 4 == cyclic group */
    erg += copy(a,S_V_I(b,1L));
    ENDR("m_gl_cyclic");
}

INT m_gl_alt(a,b) OP a,b;
/* make group-label for alt */ /* AK 050692 */
/* a and b may be equal */
{
    INT erg = OK,i;
    CTO(INTEGER,"m_gl_alt(1)",a);
    i = S_I_I(a);
    erg += m_il_v(2L,b); 
    M_I_I(2L,S_V_I(b,0L)); /* 2 == alternating group */
    M_I_I(i,S_V_I(b,1L));
    ENDR("m_gl_alt");
}

INT m_gl_sym(a,b) OP a,b;
/* make group-label for sym */ /* AK 050692 */
{
    INT erg = OK;
    erg += m_il_v(2L,b); 
    erg += m_i_i(1L,S_V_I(b,0L)); /* 1 == symmetric group */
    erg += copy(a,S_V_I(b,1L));
    return erg;
}

#ifdef CHARTRUE
static INT m_nc_alt(c,b,a) OP c,b,a;
/* b is part or vec in case of splitting rep */
/* c is group label of thew alternating group */
/* the result is an irreducible character */
{
    OP d = callocobject();
    OP e = callocobject();
    INT erg = OK;
    INT i;
    erg += m_gl_cr(c,d); /* class reps */
    erg += m_gl_cl(c,e); /* class labels */
    erg += m_il_v(2L,a);
    erg += copy(c , S_V_I(a,0L));
    erg += m_il_v(S_V_LI(d), S_V_I(a,1L)); /* structure of new charater */
    for (i=0L;i < S_V_LI(d); i++)
        {
        if (S_O_K(b) == PARTITION) /* not splitting rep */
            a_charvalue(b,S_V_I(d,i),S_V_I(S_V_I(a,1L),i));
        else if (S_O_K(b) == VECTOR) /* splitting rep */
            {
            if (S_O_K(S_V_I(e,i)) == VECTOR) /* splitting class */
                {
                    if (nullp(S_V_I(b,1L))) /* irrep part+ */
                        a_charvalue(S_V_I(b,0L),S_V_I(d,i),S_V_I(S_V_I(a,1L),i));
                    else /* compute values for part+ on exchanged classes */
                        {
                        if (nullp(S_V_I(S_V_I(e,i),1L))) /* class+ */
                            a_charvalue(S_V_I(b,0L),S_V_I(d,i+1L),S_V_I(S_V_I(a,1L),i));
                        else /* class- */
                            a_charvalue(S_V_I(b,0L),S_V_I(d,i-1L),S_V_I(S_V_I(a,1L),i));
                        }
                }
            else
                a_charvalue(S_V_I(b,0L),S_V_I(d,i),S_V_I(S_V_I(a,1L),i));
            }
        }
    freeall(d);
    freeall(e);
    return erg;
}



static INT m_nc_sym(b,a) OP b,a;
/* b is partition 
   a becomes irred char */
{
    OP c = callocobject();
    INT erg = OK;

    erg += m_il_v(2L,a); 
    erg += m_il_v(2L,S_V_I(a,0L));
    erg += weight(b,c);
    erg += m_gl_sym(c,S_V_I(a,0L));
    erg += m_part_sc(b,c);
    erg += copy(S_SC_W(c),S_V_I(a,1L));
    erg += freeall(c);
    return erg;
}
#endif /* CHARTRUE */

/* Ab hier bis ende PF */
/* PF 050292 */ /* PF 040692 */
/***********************************************************************/
/*                                                                     */
/*    Diese Routine berechnet zwei Vektoren.                           */
/*    1.Vektor:     Partition der Konjugiertenklassen der An (class)      */
/*    2.Vektor:  Standardrepraesentanten dieser Klassen (reps)         */
/*    Rueckgabewert: OK oder error                                     */
/*                                                                     */
/***********************************************************************/

#ifdef MATRIXTRUE
INT makealtclassreps(n,class,reps)
    OP     n,class,reps;
    {
    OP    matrix;        /* Partitionen der Klassen */
    OP    trans;        /* (12) */
    INT    i,j;
    INT erg=OK;

    FREESELF2(class,reps);


    /*** Test auf Ganzzahligkeit von n ************************************/

    if (S_O_K(n) != INTEGER)
        {
        error("makealtclassreps : n is no INTEGER.");
        return ERROR;
        }
    if (S_I_I(n) <= 0L)
        {
        error("makealtclassreps : n is negativ.");
        return ERROR;
        }
    
/*** Speicherplatzreservierung ****************************************/

    matrix=callocobject();
    trans=callocobject();

/*** Berechnung der beiden Vektoren *************************************/

    erg += make_alt_classes(n,matrix);
    erg += m_il_nv(S_M_LI(matrix),class);
    erg += m_il_nv(S_M_LI(matrix),reps);
    for(i=0L;i<s_v_li(class);i++)
        {
        erg += copy(S_M_IJ(matrix,0L,i),S_V_I(class,i));
        erg += std_perm(S_V_I(class,i),S_V_I(reps,i));
        if(S_M_IJI(matrix,1L,i)==1L)
            {
            erg += m_il_p(S_I_I(n),trans);
            erg += m_i_i(2L,S_P_I(trans,0L));
            erg += m_i_i(1L,S_P_I(trans,1L));
            for(j=2L;j<S_I_I(n);j++)
                erg += m_i_i(j+1L,S_P_I(trans,j));
            erg += mult(trans,S_V_I(reps,i),S_V_I(reps,i));
            erg += mult(S_V_I(reps,i),trans,S_V_I(reps,i));
            }
        }

    FREEALL2(matrix,trans);
    ENDR("makealtclassreps");
    } 
#endif /* MATRIXTRUE */

/* PF 040692 */
/***********************************************************************/
/*                                                                     */
/*    Diese Routine vergleicht zwei Partitionen a und b bezueglich     */
/*    der lexikographischen Ordnung.                                   */
/*    Rueckgabewert:    0L,  falls a=b                                 */
/*                      <0L, falls a<b                                 */
/*                      >0L, falls a>b                                 */
/*                                                                     */
/***********************************************************************/

INT part_comp(a,b)
    OP a,b;
    {
    OP    l;
    INT i;
    
    l=callocobject();
    
    if (S_PA_LI(a) > S_PA_LI(b))
        m_i_i(S_PA_LI(b),l);
    else
        m_i_i(S_PA_LI(a),l);
    i=0L;
    do     i++;
    while(i<S_I_I(l) && S_PA_II(a,S_PA_LI(a)-i)==S_PA_II(b,S_PA_LI(b)-i));
    if(S_PA_II(a,S_PA_LI(a)-i)<S_PA_II(b,S_PA_LI(b)-i))
        {
        freeall(l);
        return -1L;
        }
    if(S_PA_II(a,S_PA_LI(a)-i)>S_PA_II(b,S_PA_LI(b)-i))
        {
        freeall(l);
          return 1L;    
        }
    freeall(l);
    return 0L;
    }

/**************************************************************************/
/*    Diese Routine berechnet zu einer Partition die Standardpermutation    */
/*    in umgekehrter Reihenfolge wie m_part_perm().            */
/*    Rueckgabewert: OK oder error.                      */
/**************************************************************************/

#ifdef PERMTRUE
INT std_perm(a,b) OP a,b;
/* erzeugt aus zykeltyp standardpermutation */
{
    INT i,j,k; /* die adresse in der perm. b */
    OP l;

    l=callocobject();

    weight(a,l);
    if (not EMPTYP(b))
        freeself(b);
    b_ks_p(VECTOR,callocobject(),b);
    b_l_v(l,S_P_S(b));
    C_O_K(S_P_S(b),INTEGERVECTOR);
    k=0L;
    for (i=S_PA_LI(a)-1L;i>=0L;i--)
    {
        /* k ist naechste frei stelle */
        M_I_I(k+1L,S_P_I(b,k+S_PA_II(a,i)-1L));
        for (j=1L;j<S_PA_II(a,i);j++)
            M_I_I(j+k+1L,S_P_I(b,k+j-1L));
        k=k+S_PA_II(a,i);
    };
    return(OK);
}
#endif /* PERMTRUE */

/* PF 250292 */
/***************************************************************************/ 
/*                                                                         */
/*   Diese Routine berechnet den Charakterwert einer irreduziblen          */
/*   Darstellung (rep) auf der Konjugiertenklasse (part) der An.           */
/*   Rueckgabewert:   OK oder error                                        */
/*                                                                         */
/***************************************************************************/

#ifdef MATRIXTRUE
INT a_charvalue_co(rep,part,res,index)
    OP rep;        /* Partition der irreduziblen Darstellung der An     */
    OP part;    /* Partition der Konjugiertenklasse oder Permutation */
    OP res;         /* Beginn: leer; Ende: Charakterwert                 */
    INT index;     /* 0 or 1  to switch between to different irreducibles */
    {    
    OP conrep;    /* konjugierte Partition zu rep */
    OP newpart;    /* Zykelpartition,falls part Permutation ist */ 
    OP h_part;    /* Hakenpartition zu rep */ 
    OP sgn;        /* Signum zu part */ 

    INT erg=OK;    /* Rueckgabewert */

    CTO(PARTITION,"a_charvalue(1)",rep);
    CTTO(PERMUTATION,PARTITION,"a_charvalue(2)",part);

    FREESELF(res);

    /*** newpart wird Partition der Konjugiertenklasse, ***/
    /*** part wird Permutation daraus. ***/

    newpart = CALLOCOBJECT(); 
    if (S_O_K(part) == PERMUTATION)
        erg += zykeltyp_permutation(part,newpart); 
    else
        {
        erg += copy(part,newpart);
        erg += m_part_perm(newpart,part);
        }

    /*** Test, ob part tatsaechlich in der An liegt ***/


    sgn = CALLOCOBJECT(); 
    erg += signum_permutation(part,sgn);
    if (S_I_I(sgn) == -1L)
        {
        erg += error("a_charvalue: odd permutation ");
        goto acv_ende3;
        }

    /*** Test, ob rep und newpart Partitionen der gleichen Zahl n sind ***/
    { INT wi,wj;
      PARTITION_WEIGHT(rep,wi);
      PARTITION_WEIGHT(newpart,wj);
      if (wi != wj) {
        error("a_charvalue: disagree in partition weights"); 
        goto acv_ende2;
        }
    }

    /*** Falls rep nicht selbstassoziiert ist, kann der Charakterwert ***/
    /*** wie bei der Sn (Murnaghan-Nakayama) berechnet werden. ***/

    conrep = CALLOCOBJECT(); 
    erg += conjugate_partition(rep,conrep);
    if(NEQ(rep,conrep))
        {
        erg += charvalue(rep,newpart,res,NULL);
        goto acv_ende1;
        }
    
    /*** Falls rep selbstassoziiert ist ***/

    h_part = CALLOCOBJECT(); 
    erg += hook_part(rep,h_part);

    /*** und falls part nicht die Hakenpartition von rep ist, bzw eine ***/
    /*** Permutation aus der entsprechenden Konjugiertenklasse, wird ***/
    /*** der Charakterwert der Sn halbiert. ***/

    if(NEQ(h_part,newpart))
        {
        erg += charvalue(rep,newpart,res,NULL);
        erg += half_apply(res);
        goto acv_ende;
        }
    
    /* und falls part doch die Hakenpartition ist, bzw. Permutation */
    /* daraus, wird der Charakterwert der zerfallenden Darstellung */
    /* auf der zerfallenden Konjugiertenklasse berechnet. */

    erg += wert((which_part(part) + index)%2,newpart,res);
    
acv_ende:    
    FREEALL(h_part);
acv_ende1:
    FREEALL(conrep);
acv_ende2:
acv_ende3:
    FREEALL2(newpart,sgn);
    ENDR("a_charvalue");
    }
#endif /* MATRIXTRUE */

INT a_charvalue(rep,part,res) OP rep,part,res;
{
    return a_charvalue_co(rep,part,res,0);
}

/* PF 120292 */
/***********************************************************************/
/*                                                                     */
/*    Diese Routine entscheidet, ob die Permutation per einer ueber    */
/*    der An zerfallenden Konjugiertenklasse im ersten oder zweiten    */
/*    Teil dieser Klasse liegt.                                        */
/*    Rueckgabewert: 0L, falls per im ersten Teil liegt                */
/*                   1L, sonst                                         */
/*                                                                     */
/***********************************************************************/

#ifdef MATRIXTRUE
INT which_part(per)
    OP per;        /* Permutation einer zerfallenden Klasse */
    {
    OP typ;            /* Zykelpartition von per */
    OP std;            /* Konjugator zu per */
    OP sgn;            /* Signum von std */
    OP check;        /* Hilfsvektor der Laenge n */
    OP std_first;     /* Hilfsmatrix zur Konstruktion von std */
    INT alt,neu,i,j,k,l;
    INT erg = OK;

    CTO(PERMUTATION,"which_part(1)",per);
    CALLOCOBJECT5(std,typ,std_first,check,sgn);

    zykeltyp_permutation(per,typ);
    m_ilih_nm(S_PA_LI(typ),2L,std_first);
    for(i=0L;i<S_PA_LI(typ);i++)
        M_I_I(S_PA_II(typ,i),S_M_IJ(std_first,0L,i));
    m_il_nv(S_P_LI(per),check); 
    m_il_p(S_P_LI(per),std); 

    k= -1L;
    for(i=0L;i<S_PA_LI(typ);i++)
        {
        do k++;
        while(S_V_II(check,k)==1L);
        alt=k;
        M_I_I(1L,S_V_I(check,k));
        j=0L;
        do    {
            j++;
            neu=S_P_II(per,alt);
            alt=neu-1L;
            M_I_I(1L,S_V_I(check,alt));
            }
        while(neu!=k+1L);
        l= -1L;
        do    l++;
        while(S_M_IJI(std_first,0L,l)!=j);

        M_I_I(k,S_M_IJ(std_first,1L,l));
        }

    /* Belegung des Konjugators */
            
    k=0L;
    for(i=S_PA_LI(typ)-1L;i>=0L;i--)
        {
        M_I_I(S_M_IJI(std_first,1L,i)+1,S_P_I(std,k));
        k++;
        l=S_M_IJI(std_first,1L,i);
        for(j=0L;j<S_M_IJI(std_first,0L,i)-1L;j++)
            {
            M_I_I(S_P_II(per,l),S_P_I(std,k));
            l=S_P_II(per,l)-1L;
            k++;
            }
        }
    
    signum(std,sgn);
    i = S_I_I(sgn);
    FREEALL5(std,typ,std_first,check,sgn);
    if(i==1) return 0;
    else if(i==-1) return 1;

    SYMCHECK(1,"which_part:should never be here");
    ENDR("which_part");
    }


/* PF 060292 */ /* PF 040692 */ /* PF 100692 */
/***********************************************************************/
/*                                                                     */
/*    Diese Routine berechnet den Vektor der irreduziblen Dar-         */
/*    stellungen der An.                                               */
/*    Rueckgabewert: OK oder error                                     */
/*                                                                     */
/***********************************************************************/

INT make_alt_partitions(n,res)
    OP n;        /* Gewicht der Partitionen */
    OP res;        /* Vektor der irred. Darst. der An */
    {
    OP par;        /* Partition von n */
    OP conpar;     /* konjugierte Partition */ 
    OP l;        /* Anzahl der verschiedenen irred. Darst. der An */
    INT i=0L;
    INT erg=OK;

    INT alt_dimension();    /* Hilfsroutinen */
    INT part_comp();

    if (not EMPTYP(res))
        erg +=  freeself(res);

    /*** Test auf Ganzzahligkeit von n ************************************/

    if (S_O_K(n) != INTEGER)
        {
        error("make_alt_partitions : n is no INTEGER.");
        return ERROR;
        }
    if (S_I_I(n) <= 0L)
        {
        error("make_alt_partitions : n is negativ.");
        return ERROR;
        }

    /*** Speicherplatzreservierung fuer die Objekte **********************/

    conpar=callocobject();
    l=callocobject();
    par=callocobject();

    /*** Berechnung des Partitionenvektors (eigentlich eine Matrix) *******/

    erg += alt_dimension(n,l);
    erg += m_ilih_nm(S_I_I(l),2L,res);
    erg += first_partition(n,par);
    do    {
        erg += conjugate(par,conpar);
        if(part_comp(par,conpar)>=0L)
            {
            erg += copy(par,S_M_IJ(res,0L,i));
            if(part_comp(par,conpar)==0L && S_I_I(n)!=1L)
                {
                i++;
                erg += copy(par,S_M_IJ(res,0L,i));
                erg += m_i_i(1L,S_M_IJ(res,1L,i));
                }
            i++;
            }
        }
    while(next(par,par));

/*** Speicherplatzfreigabe *********************************************/

    erg += freeall(par);
    erg += freeall(conpar);
    erg += freeall(l);

/*** Rueckkehr in die aufrufende Routine *******************************/

    if (erg != OK)
        {
        error("make_alt_partitions : error during computation.");
        return ERROR;
        }
    return OK;
    }/* Ende von make_alt_partitions */
#endif /* MATRIXTRUE */

/* PF 060292 */ /* PF 040692 */ 
/***********************************************************************/
/*                                                                     */
/*    Diese Routine berechnet den Vektor der Konjugiertenklassen       */
/*    der An.                                                          */
/*    Rueckgabewert: OK oder error                                     */
/*                                                                     */
/***********************************************************************/

#ifdef MATRIXTRUE
INT make_alt_classes(n,res)
    OP n;        /* Gewicht der Partitionen */
    OP res;        /* Vektor der Konjugiertenklassen der An */
    {
    OP par;        /* Partition von n */
    OP per;     /* Permutation */ 
    OP sgn;     /* Signum der Permutation */ 
    OP l;        /* Anzahl der verschiedenen Konjugiertenklassen der An */
    INT i=0L;
    INT erg=OK;

    INT alt_dimension();    /* Hilfsroutinen */
    INT split();

    CTO(INTEGER,"make_alt_classes(1)",n);

    FREESELF(res);

    /*** Test auf Ganzzahligkeit von n ************************************/

    SYMCHECK (S_I_I(n) <= 0,"make_alt_classes : n <=0");
    /*** Speicherplatzreservierung fuer die Objekte ***********************/

    par=callocobject();
    per=callocobject();
    sgn=callocobject();
    l=callocobject();

    /*** Berechnung des Partitionenvektors (eigentlich eine Matrix) *********/

    erg += alt_dimension(n,l);
    erg += m_ilih_nm(S_I_I(l),2L,res);
    erg += first_partition(n,par);
    do    {
        erg += m_part_perm(par,per);
        erg += signum(per,sgn);
        if(S_I_I(sgn) == 1L)
            {
            erg += copy(par,S_M_IJ(res,0L,i));
            if(split(n,par)==1L)
                {
                i++;
                erg += copy(par,S_M_IJ(res,0L,i));
                erg += m_i_i(1L,S_M_IJ(res,1L,i));
                }
            i++;
            }
        }
    while(next(par,par));

/*** Speicherplatzfreigabe *********************************************/

    erg += freeall(par);
    erg += freeall(per);
    erg += freeall(sgn);
    erg += freeall(l);

/*** Rueckkehr in die aufrufende Routine *******************************/

    ENDR("make_alt_classes");
} /* Ende von make_alt_classes */
#endif /* MATRIXTRUE */

/* PF 040692 */ /* PF 100692 */
/**********************************************************************/
/*                                                                    */
/*    Diese Routine berechnet die Dimension der Charaktertafel der    */
/*    An, d.h. die Anzahl der gewoehnlichen irreduziblen Darstel-     */
/*    lungen der An.                                                  */
/*    Rueckgabewert: OK oder error                                     */
/*                                                                    */
/**********************************************************************/

INT alt_dimension(n,res)
    OP n,res;
    {
    OP par;        /* Partition von n */
    OP conpar;     /* konjugierte Partition */ 
    INT erg=OK;
    INT part_comp();    /* Hilfsroutine */

    CTO(INTEGER,"alt_dimension(1)",n);


    FREESELF(res);

    /*** Test auf Ganzzahligkeit von n ************************************/

    SYMCHECK(S_I_I(n) <= 0,"alt_dimension : n <= 0");
    
    /*** Speicherplatzreservierung ****************************************/

    par=callocobject();
    conpar=callocobject();

    /*** Berechnung der Anzahl irreduzibler Darstellungen der An ***********/

    erg += m_i_i(0L,res);
    erg += first_partition(n,par);
    do    {
        erg += conjugate(par,conpar);
        if(part_comp(par,conpar)>=0L)
            {
            erg += inc(res);
            if(part_comp(par,conpar)==0L && S_I_I(n)!=1L)
                erg += inc(res);
            }
        }
    while(next(par,par));

    /*** Speicherplatzfreigabe ********************************************/

    erg += freeall(par);
    erg += freeall(conpar);

    /*** Rueckkehr in die aufrufende Routine *******************************/

    ENDR("alt_dimension");
} /* Ende von alt_dimension */



/* PF 040692 */ /* PF 100692 */
/*****************************************************************************/
/*    DIESE ROUTINE UEBERPRUEFT, OB DIE KONJUGIERTENKLASSE PAR UEBER     */
/*    DER An ZERFAELLT.                            */
/*    RUECKGABEWERT:    1    FALLS DIE KLASSE ZERFAELLT,          */
/*                    0    SONST.             */
/*****************************************************************************/

INT split(n,par) OP    n,par;
    {
    INT    i;

    OP    v;
    OP    w;

    /*** Spezialfall n=1 ***/

    if (S_I_I(n) == 1L)
        return 0L;

    w=callocobject();
    v=callocobject();

    m_l_nv(n,v);
    for(i=0L;i<S_PA_LI(par);i++)
        {
        if (S_PA_II(par,i)%2 == 0L)
            {
            freeall(w);
            freeall(v);
            return 0L;
            }
        m_i_i(1L,w);
        add(S_V_I(v,S_PA_II(par,i)-1L),w,S_V_I(v,S_PA_II(par,i)-1L));
        }
    for(i=0L;i<S_I_I(n);i++)
        if (S_I_I(S_V_I(v,i)) > 1L)
            {
            freeall(w);
            freeall(v);
            return 0L;
            }
    freeall(w);
    freeall(v);
    return 1L;
    }
/* PF 070592 *//* PF 010692 */ /* AK 020692 */
/****************************************************************************/
/*                                        */
/*  Diese Routine berechnet die Charaktertafel der alternierenden Gruppe    */
/*  An fuer eine beliebige natuerliche Zahl n.            */
/*    VERSION 1.2     PF040592                    */
/****************************************************************************/

#ifdef MATRIXTRUE
INT an_tafel(n,tafel) OP    n,tafel;
{
    OP    v_part;            /* Vektor der Partitionen von n */
    OP    par;            /* Partition von n */
    OP    conpar;            /* assoziierte Partition zu par */
    OP    per;    /* Permutation aus der Konjugiertenklasse (par) */
    OP    sgn;        /* Signum der Permutation per */
    OP    split_class;    /* Hakenpartition h(par), 
                falls par selbstassoziiert */
    OP    info_pa;/* Infovektor fuer die irreduziblen Darstellungen */
    OP    info_cc;    /* Infovektor fuer die Konjugiertenklassen */
    OP    hilf;        /* Hilfsobjekt zum Umspeichern */

    INT    i,j;    /* Zaehlvariable zum Durchlauf der Infovektoren */
    INT    l=0L;    /* Groesse der Charaktertafel der An */
    INT    zeile,spalte;    /* Indexvariable bei der Belegung der Charaktertafel */
    INT erg=OK;        /* Rueckgabewert */



    /*** Test auf Ganzzahligkeit von n ************************************/
    CTO(INTEGER,"an_tafel",n);
    CE2(n,tafel,an_tafel);

    if (S_I_I(n) <= 0L)
        {
        erg += error("an_tafel : n is negativ.");
        goto endr_ende;
        }
    
    /*** Die Charaktertafel der A1, und die der A2 ist [1] ****************/

    if ((S_I_I(n) == 2L) || (S_I_I(n) == 1L))
        {
        erg +=  m_ilih_m(1L,1L,tafel); /* AK 120692 */
        erg += m_i_i(1L,S_M_IJ(tafel,0L,0L));
        goto endr_ende;
        }

    C1R(n,"an_tafel",tafel);

    /*** Speicherplatzreservierung der Objekte ****************************/

    v_part = callocobject();
    conpar = callocobject();
    par = callocobject();
    per = callocobject();
    sgn = callocobject();
    hilf = callocobject();
    split_class = callocobject();
    info_cc = callocobject();
    info_pa = callocobject();

    /*** Initialisierung der Zahl 2 und des Partitionsvektors *************/

    erg +=  makevectorofpart(n,v_part);

    /*** Initialisierung der Infovektoren als Nullvektoren ****************/

    erg +=  m_il_nv(S_V_LI(v_part),info_pa);
    erg +=  copy(info_pa,info_cc);

/*** Belegung der Infovektoren ****************************************/
/*** Durchlaufe die Partitionen von n mit par. ***/

    i = 0L;
    erg += first_partition(n,par);
    do
        {
/*** Falls die Konjugiertenklasse (par) in der An liegt, wird in ***/
/*** info_cc an der entsprechenden Stelle eine 1 eingetragen.    ***/

        erg +=  m_part_perm(par,per);
        erg +=  signum(per,sgn);
        if (S_I_I(sgn) == 1L)
            {
            erg +=  m_i_i(1L,S_V_I(info_cc,i));
            l++;
            }

/*** Falls par selbstassoziiert ist, wird in info_pa fuer diese   ***/
/*** Partition und in info_cc fuer die zugehoerige Hakenpartition ***/
/*** eine 2 eingetragen.                                          ***/

        erg +=  conjugate(par,conpar);
        if (comp(par,conpar) == 0L)
            {
            erg +=  m_i_i(2L,S_V_I(info_pa,i));
            erg +=  hook_part(par,split_class);
            erg +=  m_i_i(2L,S_V_I(info_cc,indexofpart(split_class)));
            l++;
            }

/*** Falls par lexikographisch groesser als die dazu assoziierte ***/
/*** Partition ist, erhaelt info_pa den Eintrag 1.               ***/

        else
            if (S_V_II(info_pa,indexofpart(conpar)) == 0L)
                erg +=  m_i_i(1L,S_V_I(info_pa,i));

        i++;
        }
    while(next_apply(par));

/***********************************************************************/
/*** Initialisierung der Charaktertafel als Nullmatrix *****************/

    erg +=  m_ilih_m(l,l,tafel);

/*** Belegung der Charaktertafel ***************************************/ 

    zeile = 0L;
    spalte = 0L;

/*** Durchlaufe den Infovektor der irreduziblen Darstellungen  mit i ***/

    for(i=0L;i<S_V_LI(info_pa);i++)
        {
/*** Im Falle einer nicht zerfallenden irreduziblen Darstellung  ***/
/*** erstelle die dazugehoerige Zeile der Charaktertafel.        ***/

        if(S_V_II(info_pa,i)==1L)
            {
    /*** Durchlaufe den Infovektor der Konjugiertenklassen mit j. ***/

            for(j=0L;j<S_V_LI(info_cc);j++)
                {
        /*** Liegt die Konjugiertenklasse in der An, berechne ***/
        /*** den entsprechenden Charakterwert der Sn.         ***/

                if(S_V_II(info_cc,j)>0L)
                    {
                    erg +=  charvalue(S_V_I(v_part,i),
                          S_V_I(v_part,j),
                          S_M_IJ(tafel,zeile,spalte),
                          NULL);
                    spalte++;

                    if(S_V_II(info_cc,j)==2L)
                        {
                    erg +=  copy(S_M_IJ(tafel,zeile,spalte-1L),
                             S_M_IJ(tafel,zeile,spalte));
                        spalte++;
                        }
                    }
                }
            zeile++;
            spalte = 0L;
            }
        
        /*** Im Falle einer zerfallenden irreduziblen Darstellung ***/
        /*** muessen zwei Zeilen in der Charaktertafel berechnet  ***/
        /*** werden.                                              ***/

        if(S_V_II(info_pa,i)==2L)
            {
            erg +=  hook_part(S_V_I(v_part,i),split_class);

    /*** Durchlaufe den Infovektor der Konjugiertenklassen mit j. ***/

            for(j=0L;j<S_V_LI(info_cc);j++)
                {
    /*** Zerfaellt die Konjugiertenklasse nicht, berechne  ***/
    /*** den entsprechenden Charakterwert der Sn, teile    ***/
    /*** ihn durch zwei und trage ihn in beiden Zeilen ein.***/

                if(S_V_II(info_cc,j)==1L)
                    {
        erg +=  charvalue(S_V_I(v_part,i), S_V_I(v_part,j), hilf, NULL);
        erg +=  div(hilf,cons_zwei,S_M_IJ(tafel,zeile,spalte));
        erg +=  copy(S_M_IJ(tafel,zeile,spalte),
                     S_M_IJ(tafel,zeile+1L,spalte));
                    spalte++;
                    }
                /*** Falls die Konjugiertenklasse jedoch zerfaellt, ***/

                if(S_V_II(info_cc,j)==2L)
                    {
        /*** und es sich um die zugehoerige Hakenpartition ***/
        /*** handelt, so berechne die entsprechenden zwei  ***/
        /*** Charakterwerte und trage sie ueber Kreuz in   ***/
        /*** die Charaktertafel ein.                       ***/

            if(eq(split_class,S_V_I(v_part,j)))
                        {
                erg +=  wert(0L,S_V_I(v_part,j),
                        S_M_IJ(tafel,zeile,spalte));
                erg +=  copy(S_M_IJ(tafel,zeile,spalte),
                    S_M_IJ(tafel,zeile+1L,spalte+1L));
                erg +=  wert(1L,S_V_I(v_part,j), 
                    S_M_IJ(tafel,zeile,spalte+1L));
                erg +=  copy(S_M_IJ(tafel,zeile,spalte+1L),
                    S_M_IJ(tafel,zeile+1L,spalte));
                        }
        /*** Handelt es sich nicht um die zugehoerige Haken- ***/
        /*** partition, so berechne wieder den halben Wert   ***/
        /*** des Charakters der Sn und trage diesen viermal  ***/
        /*** in die Charaktertafel ein.                      ***/

                    else
                        {
            erg +=  charvalue(S_V_I(v_part,i), 
                    S_V_I(v_part,j), hilf, NULL);
            erg +=  div(hilf,cons_zwei,S_M_IJ(tafel,zeile,spalte));
            COPY(S_M_IJ(tafel,zeile,spalte), S_M_IJ(tafel,zeile+1L,spalte));
            COPY(S_M_IJ(tafel,zeile,spalte), S_M_IJ(tafel,zeile+1L,spalte+1L));
            COPY(S_M_IJ(tafel,zeile,spalte), S_M_IJ(tafel,zeile,spalte+1L));
                        }
                        
                    spalte = spalte+2L;
                    }
                }
            zeile = zeile+2L;
            spalte = 0L;
            }
        }
/************************************************************************/

    /*** Speicherplatzfreigabe ***/

    erg +=  freeall(v_part);
    erg +=  freeall(conpar);
    erg +=  freeall(par);
    erg +=  freeall(per);
    erg +=  freeall(sgn);
    erg +=  freeall(hilf);
    erg +=  freeall(split_class);
    erg +=  freeall(info_cc);
    erg +=  freeall(info_pa);

    /*** Rueckkehr in die aufrufende Routine *******************************/

    S1R(n,"an_tafel",tafel);
    ENDR("an_tafel");
}/*** Ende von an_tafel ***/
#endif /* MATRIXTRUE */

/*****************************************************************************/
/*    Routine zur Berechnung des Charakterwertes auf der zerfallenden      */
/*    Konjugiertenklasse (split_class) , den die zugehoerige irreduzible   */
/*    Darstellung liefert. Der Wert wird in res zurueckgegeben.         */
/*    Der Index gibt an, welcher der beiden konjugierten Werte berechnet   */
/*    Rueckgabewert:    OK oder error                         */
/*****************************************************************************/
/* PF 200891 V1.3 */ /* PF 070592 */ /* PF 110992 */

#ifdef CHARTRUE
INT wert(index,split_class,res) OP    split_class,res; INT    index;
    {
    INT    i;
    OP    expo,    term_eins,    term_zwei;
    OP    n;
    INT erg=OK;
    CTO(PARTITION,"wert(2)",split_class);

    expo = callocobject();
    term_eins = callocobject();
    term_zwei = callocobject();
    n = callocobject();

    erg += weight(split_class,n);
    erg += copy(n,expo);
    erg += sub(expo,S_PA_L(split_class),term_eins);
    C_I_I(expo,S_I_I(term_eins)/2L);
    C_I_I(term_eins,-1L);
    erg += hoch(term_eins,expo,term_eins);


    C_I_I(expo,1L);
    for(i=0L;i<S_PA_LI(split_class);i++)
        erg += mult_apply(S_PA_I(split_class,i),expo);
    erg += mult_apply(term_eins,expo);
    erg += squareroot(expo,term_zwei);

    if (index == 0L)
        erg += add(term_eins,term_zwei,res);
    else
        erg += sub(term_eins,term_zwei,res);
    erg += div(res,cons_zwei,res);


    erg += freeall(expo);
    erg += freeall(term_eins);
    erg += freeall(term_zwei);
    erg += freeall(n);

    ENDR("wert");
    }
#endif /* CHARTRUE */

/*****************************************************************************/
/*    DIESE ROUTINE BERECHNET ZU EINER SELBSTASSOZIIERTEN PARTITION PAR DIE */
/*    PARTITION, DIE AUS DEN HAKENLAENGEN VON PAR BESTEHT.              */
/*****************************************************************************/

#ifdef PARTTRUE
INT hook_part(par,res) OP    par,res;
/* PF 070592 */
    {
    INT    i,j;
    INT    elementwert;
    OP    element;
    OP    v,hilfsvector;
    INT erg = OK;
    CTO(PARTITION,"hook_part(1)",par);

    if (not EMPTYP(res))
        freeself(res);

    element=callocobject();
    v=callocobject();
    hilfsvector=callocobject();


    elementwert = S_PA_II(par,S_PA_LI(par)-1L);
    elementwert = 2L *elementwert - 1L;
    erg +=  m_i_i(elementwert,element);
    erg +=  m_o_v(element,v);
    j = 2L;
    for (i=S_PA_LI(par)-2L; i>=0L; i--)
        {
        elementwert = S_PA_II(par,i);
        elementwert = 2L *(elementwert-j) + 1L;
        if (elementwert > 0L)
            {
            erg +=  c_i_i(element,elementwert);
            erg +=  append(v,element,hilfsvector);
            erg +=  copy(hilfsvector,v);
            }
        j++;
        }

    erg +=  m_v_pa(v,res);

    erg +=  freeall(v);
    erg +=  freeall(element);
    erg +=  freeall(hilfsvector);

    ENDR("hook_part");
    }
#endif /* PARTTRUE */

#ifdef PERMTRUE
INT m_gl_first(a,b) OP a,b;
/* AK 291092 */
{
if (CYCLIC_GL(a))
    return first_permutation(S_GL_CYCLIC_A(a),b);
if (SYM_GL(a))
    return first_permutation(S_GL_SYM_A(a),b);
if (ALT_GL(a))
    return first_permutation(S_GL_ALT_A(a),b);
return error("m_gl_first: can not handle group label");
}

INT m_gl_next(a,b,c) OP a,b,c;
/* AK 291092 */
/* loop over all group elements */
{
    OP d;
    INT erg,i,j;
    if (b == c) 
        {
         d = callocobject();
        *d = *c;
        C_O_K(c,EMPTY);
        erg = m_gl_next(a,d,c);
        freeall(d);
        return erg;
        }
    if (SYM_GL(a))
        {
        return next(b,c);  
        }
    if (ALT_GL(a))
        {
        erg = next(b,c);
        if (erg == FALSE) 
            return erg; /* d.h. b war letzte permutation */
        while (oddp(c))
            {
            erg = next_apply(c);
            if (erg == FALSE) /* es gibt kein permutation aus an
                         nach der permutation b */
                {
                copy(b,c);
                return FALSE;
                }
            }
        return TRUE;
        }
    if (CYCLIC_GL(a))
        {
        if (S_P_II(b,0L) == S_P_LI(b))
            return FALSE; /* war die letzte */
        copy(b,c);
        for (i=1L,j=0L;i<S_P_LI(c); i++,j++)
            M_I_I(S_P_II(b,i),S_P_I(c,j));
        M_I_I(S_P_II(b,0L),S_P_I(c,j));
        return TRUE;
        }
    return error("m_gl_next: can not handle group label");
}
#endif /* PERMTRUE */


static INT companion_matrix(p,m) OP p,m;
/* the characteristic polynom of the companion matrix 
   is the polynom p */
{
    INT erg = OK,i;
    OP d,z,nu;
    d = CALLOCOBJECT();
    nu = CALLOCOBJECT();
    degree_polynom(p,d);
    m_lh_m(d,d,m);
    null(S_PO_K(p),nu);
    
    FORALL(z,m,{ copy(nu,z); });
    for (i=1;i<S_M_HI(m);i++) eins(S_PO_K(p),S_M_IJ(m,i,i-1));
    FORALL(z,p,{
               i = S_MO_SII(z,0);
               if (i < S_M_LI(m))
                   addinvers(S_MO_K(z),S_M_IJ(m,i,S_M_LI(m)-1)); 
               });
    FREEALL2(nu,d);
    ENDR("companion_matrix");
}

static INT all_irred_companion(n,q,v) OP n,q,v;
{
   INT erg = OK;
   CTO(INTEGER,"all_irred_companion(1)",n);
   SYMCHECK(S_I_I(n)<1,"all_irred_companion:degree < 1");
   CTO(INTEGER,"all_irred_companion(2)",q);
   SYMCHECK(prime_power_p(q)==FALSE,"all_irred_companion(2): no prime power");
   {
#ifdef FFTRUE
   if (einsp(n) )
      {
      OP ff=callocobject();INT i;
      first_ff_given_q(q,ff);/* Nul*/ 
      m_il_v(S_I_I(q)-1,v);
      for (i=0;i<S_V_LI(v);i++) {
          next(ff,ff);
          m_lh_m(n,n,S_V_I(v,i));
          copy(ff,S_M_IJ(S_V_I(v,i),0,0));
          }
      FREEALL(ff);
      }
   else {
        OP p;INT i;
        p = CALLOCOBJECT();
        all_irred_polynomials(n,q,p);
        m_il_v(S_V_LI(p),v);
        for (i=0;i<S_V_LI(v);i++)
            companion_matrix(S_V_I(p,i),S_V_I(v,i));
        FREEALL(p);
        }
#endif
   }
   ENDR("all_irred_companion");
}

static INT J_matrix(n,q,m) OP n,q,m;
{
    INT j; OP y;
    m_lh_m(n,n,m);
    FORALL(y,m,{ null_ff_given_q(q,y); });
    for (j=0;j<S_M_HI(m);j++) eins_ff_given_q(q,S_M_IJ(m,j,j));
    for (j=1;j<S_M_HI(m);j++) eins_ff_given_q(q,S_M_IJ(m,j,j-1));
}

static INT all_blocks(n,q,v) OP n,q,v;
/* alle füllungen eines blocks der grösse n */
{
    OP d,z,y;INT i,j;
    INT erg = OK;
    d = CALLOCOBJECT();
    m_il_v(0,v);
    alle_teiler(n,d);

    for (i=0;i<S_V_LI(d);i++) {
        /* if (EINSP(S_V_I(d,i))) {
            inc(v); z = S_V_I(v,S_V_LI(v)-1);
            J_matrix(n,q,z);
            }
        else 
        if (EQ(n,S_V_I(d,i))) {
            OP yy;
            yy=CALLOCOBJECT();
            all_irred_companion(n,q,yy);
            append(yy,v,v);
            FREEALL(yy);
            }
        else */ {
            OP teil= callocobject();
            OP v2= callocobject();
            OP j2= callocobject();
            ganzdiv(n,S_V_I(d,i),teil);
            all_irred_companion(teil,q,v2);
            J_matrix(S_V_I(d,i),q,j2);
            
            
            
            FORALL(z,v2, {kronecker_product(j2,z,z); });
            
            
            append(v2,v,v);
            FREEALL3(j2,teil,v2);
            }

        }
    FREEALL(d);
    ENDR("all_blocks");
}

INT class_label_glnq(n,q,v) OP n,q,v;
{
    INT erg = OK;
    C2R(n,q,"class_label_glnq",v);
    erg += class_label_glnq_co(n,q,v,NULL);
    S2R(n,q,"class_label_glnq",v);
    ENDR("class_label_glnq");
}

INT class_label_glnq_co(n,q,v,pav) OP n,q,v;OP pav;
{
	OP pa,cm;INT i,erg=OK,j,k;
	CALLOCOBJECT2(pa,cm);
	m_l_v(n,cm);
	for (i=0;i<S_V_LI(cm);i++)
	    {
	    m_i_i(1+i,pa); all_blocks(pa,q,S_V_I(cm,i)); 
	    }

	m_il_v(0,v);
	if (pav != NULL) m_il_v(0,pav);
	first_partition(n,pa);
	do {
	   OP vc= callocobject();
	   OP uc= callocobject();
	   OP f= callocobject();
	   m_l_v(S_PA_L(pa),vc);
	   m_l_nv(S_PA_L(pa),uc);
	   for (i=0;i<S_V_LI(vc);i++) M_I_I(S_V_LI(S_V_I(cm,S_PA_II(pa,i)-1)), S_V_I(vc,i));
	   /* vc enthaält die anzahl der möglichen block einträge */
	   
	again:
	   m_lh_m(n,n,f);
	   for (i=0;i<S_M_HI(f);i++)
	   for (j=0;j<S_M_LI(f);j++) null_ff_given_q(q,S_M_IJ(f,i,j));
	   for (i=0,j=0;i<S_PA_LI(pa);i++)
	       {
	       INT ii,jj;
	       OP z = S_V_I(cm,S_PA_II(pa,i)-1); /* von hier wird der block geholt*/
	       for (ii=0;ii<S_PA_II(pa,i);ii++)
	       for (jj=0;jj<S_PA_II(pa,i);jj++)  copy(S_M_IJ(S_V_I(z,S_V_II(uc,i)),ii,jj), 
						      S_M_IJ(f,j+ii,j+jj));
	       j+=S_PA_II(pa,i);
	       }
	   inc(v); SWAP(f,S_V_I(v,S_V_LI(v)-1));
	   if (pav != NULL) { inc(pav); copy(pa,S_V_I(pav,S_V_LI(pav)-1));}

	/* compute next label */
	    for (i=S_V_LI(uc)-1;i>=0;i--)
		if ( S_V_II(uc,i) < S_V_II(vc,i)-1) {
		   if (i==0) { incr: inc(S_V_I(uc,i)); 
			       for (j=i+1;j<S_V_LI(uc); j++) m_i_i(0,S_V_I(uc,j)); 
			       goto again; }
		   else if (S_PA_II(pa,i) > S_PA_II(pa,i-1)) goto incr;
		   else if (S_V_II(uc,i) < S_V_II(uc,i-1) ) goto incr;
		   else continue;
		   }
	  
	/* keine weitere klasse */ 
	  FREEALL3(f,uc,vc);
	  } while(next_apply(pa));
	FREEALL2(pa,cm);
	ENDR("class_label_glnq");
}


/* for the computation of c_ijk with group labels */
/* AK 080306 */

/* berechnung c_ijk mit gl */

INT class_rep(OP gl, OP cl, OP res)
/* AK 080306 */
/* input group label gl 
         class label cl
   output representing element */
{	
	INT erg = OK;
	if (SYM_GL(gl)) 
		erg += m_part_perm(cl,res);
	else if (ALT_GL(gl)) {
		if (S_O_K(cl) == PARTITION)
			erg += m_part_perm(cl,res);
		else if (S_O_K(cl)==VECTOR)
			{
			erg += std_perm(S_V_I(cl,0),res);
			if (S_V_II(cl,1)==1) {
				OP trans=callocobject();
				make_n_kelmtrans(S_P_L(res),cons_eins,trans);
				mult(res,trans,res);
				mult(trans,res,res);
				freeall(trans);
				}
			}
		else
			error("class_rep(1): wrong cl for alternating group");
		}
	else
		NYI("class_rep");
	ENDR("class_rep");
}

INT class_label(OP gl, OP ge, OP res)
/* AK 080306 */
/* gl is grouplabel 
   ge is a group element
   res becomes the corresponding class label */
{
	return m_gl_ge_cl(gl,ge,res);
}

INT compute_gl_charvalue(OP gl, OP il, OP cl, OP res)
/* computes value of the irreducible character il
     on the class cl */
{
	INT erg = OK;
        if (SYM_GL(gl))
                erg += charvalue(il,cl,res,NULL);
        else if (ALT_GL(gl)) {
		OP h=callocobject();
		class_rep(gl,cl,h);
		if (S_O_K(il) == VECTOR) 
			erg += a_charvalue_co(S_V_I(il,0),h,res,S_V_II(il,1));
		else
			erg += a_charvalue_co(il,h,res,0);
		freeall(h);
                }
        else
                NYI("compute_gl_charvalue");
        ENDR("compute_gl_charvalue");
}

INT compute_gl_il_dimension(OP gl, OP il, OP res)
{
        INT erg = OK;
        if (SYM_GL(gl))
                erg += dimension(il,res);
        else if (ALT_GL(gl)) {
		if (S_O_K(il) == VECTOR)
			{
			erg += dimension(S_V_S(il),res);
			erg += half_apply(res);
			}
                else
			erg += dimension(il,res);
                }
        else
                NYI("compute_gl_il_dimension");
        ENDR("compute_gl_il_dimension");
}

INT compute_gl_cl_classorder(OP gl, OP cl, OP res)
{
        INT erg = OK;
        if (SYM_GL(gl))
                erg += ordcon(cl,res);
        else if (ALT_GL(gl)) {
                if (S_O_K(cl) == VECTOR)
                        {
                        erg += ordcon(S_V_S(cl),res);
                        erg += half_apply(res);
                        }
                else
                        erg += ordcon(cl,res);
                }
        else
                NYI("compute_gl_cl_classorder");
        ENDR("compute_gl_cl_classorder");
}


INT compute_gl_c_ijk(OP gl, OP i, OP j, OP k, OP res)
/* AK 080306 */
/* gl is grouplabel 
   i,j,k  are class labels of this group label
   res will be the result */
{
	INT erg = OK;
	if (SYM_GL(gl)) 
		c_ijk_sn(i,j,k,res);
	else {
		/* we use the formula of curtis reiner */
		OP il,h,ki,h1,h2,h3;
		INT l;
		CALLOCOBJECT3(il,h,ki);
		CALLOCOBJECT3(h1,h2,h3);
	
		m_i_i(0,res);
		/* ki is the class containing the inverse element */
		class_rep(gl,k,h1); invers(h1,h1); class_label(gl,h1,ki);

		m_gl_il(gl,il); 
		for (l=0;l<S_V_LI(il);l++) /* over all irreducible characters */
			{
			compute_gl_charvalue(gl,S_V_I(il,l),i,h1);
			compute_gl_charvalue(gl,S_V_I(il,l),j,h2);
			compute_gl_charvalue(gl,S_V_I(il,l),ki,h3);
			mult(h1,h2,h);mult_apply(h3,h);
			compute_gl_il_dimension(gl,S_V_I(il,l),h1);
			div(h,h1,h);
			add_apply(h,res);
			}

		/* class orders */
		compute_gl_cl_classorder(gl,i,h1); mult_apply(h1,res);
		compute_gl_cl_classorder(gl,j,h1); mult_apply(h1,res);
		/* divide by group order */
		m_gl_go(gl,h1); div(res,h1,res);
		FREEALL3(il,h,ki);
		FREEALL3(h1,h2,h3);
		
	     }
	ENDR("compute_gl_c_ijk");
}


