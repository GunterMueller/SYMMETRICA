/* file boe.c */
#include "def.h"
#include "macro.h"

static INT op_transpo_tab();
static INT vander_gen();

/* AK 180791 berechnung der specht darstellung
Wilhelm Specht: Mathematische Zeitschrift 39 (1935) 696-711 */

#ifdef TABLEAUXTRUE
INT makevectorofspecht_poly(a,d) OP a,d;
/* AK 210703 */
/* computes the vector of all specht polynomials
   for a given shape,
   i.e. basis of ordinary specht modul */
{
    INT erg =OK,i;
    CTTO(PARTITION,SKEWPARTITION,"makevectorofspecht_poly(1)",a);
    {
    OP e = CALLOCOBJECT();
    erg += makevectorofSYT(a,e);
    erg += m_il_v(S_V_LI(e),d);
    for (i=0L;i<S_V_LI(d); i++)
        erg += specht_poly(S_V_I(e,i),S_V_I(d,i)); 
    /* d is vector of specht poly */
    FREEALL(e);
    }
    ENDR("makevectorofspecht_poly");
}

INT specht_dg(a,b,c) OP a,b,c;
/* a partition fuer irr. darstellung
   b permutation 
   c wird die darstellung */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
{
    INT erg = OK;
    CTTO(PARTITION,SKEWPARTITION,"specht_dg(1)",a);
    CTO(PERMUTATION,"specht_dg(2)",b);
    CE3(a,b,c,specht_dg);
    {
    OP d,f, e;
    INT i,j;
    CALLOCOBJECT3(d,e,f);

    erg += makevectorofspecht_poly(a,d);
    /* d is vector of specht poly */
    erg += m_ilih_nm(S_V_LI(d),S_V_LI(d),c);

    for (i=0L;i<S_V_LI(d); i++)
        {
        erg += operate_perm_polynom(b,S_V_I(d,i),e);
        /* e ist das geaenderte specht polynom, welches nun in der
           basis geschrieben werden muss */
aaa:
        if (not NULLP(e)) 
            for (j=0L;j<S_V_LI(d); j++)
                if (EQ(S_PO_S(e),S_PO_S(S_V_I(d,j))))
                    {
                    CLEVER_COPY(S_PO_K(e),S_M_IJ(c,j,i));
                    FREESELF(f);
                    MULT(S_PO_K(e),S_V_I(d,j),f);
                    erg += sub_apply(f,e); /* e = e -f */
                    goto aaa;
                    }
        }
    FREEALL3(d,e,f);
    }
    ENDR("specht_dg");
}
#endif /* TABLEAUXTRUE */

#ifdef MATRIXTRUE
static INT vander_gen(a,b) OP a,b;
/* a ist monom, d.h. vector von integer als self
   b wird die vandermonde, wie sie bei specht definiert wird */
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* a and b may be equal */
/* AK 100902 V2.1 */
{
    INT erg = OK;
    CTO(MONOM,"local:vander_gen(1)",a);
    CTO(VECTOR,"local:vander_gen(1.self)",S_MO_S(a));
    {
    OP c,d;
    INT i,j,k;

    c=CALLOCOBJECT();
    d=CALLOCOBJECT();
    k=0L;
    for (i=0L;i<S_MO_SLI(a);i++)
        if (not NULLP(S_MO_SI(a,i))) k++;

    erg += m_ilih_m(k,k,c);
    for (i=0L;i<S_M_HI(c);i++)
        {
        for (k=0L;k<S_MO_SLI(a);k++)
            if (not NULLP(S_MO_SI(a,k))) break;
        for (j=0L;j<S_M_HI(c);j++)
            {
            erg += b_skn_po(CALLOCOBJECT(),
                            CALLOCOBJECT(),
                            NULL,
                            S_M_IJ(c,i,j));
            erg +=   m_l_nv(S_MO_SL(a),
                            S_PO_S(S_M_IJ(c,i,j)));
            COPY(S_MO_K(a),S_PO_K(S_M_IJ(c,i,j)));
            M_I_I(i+S_MO_SII(a,k)-1L,S_PO_SI(S_M_IJ(c,i,j),k));
            k++;
            for (;k<S_MO_SLI(a);k++)
                if (not NULLP(S_MO_SI(a,k))) break;
            }
        }

    erg += det_mat_imm(c,b);
    FREEALL2(c,d);
    }
    ENDR("local:vander_gen");
}
#endif /* MATRIXTRUE */

#ifdef TABLEAUXTRUE
INT specht_poly(a,b) OP a,b;
/* AK 200891 V1.3 */
/* AK 011098 V2.0 */
/* a and b may be equal */
/* a TABLEAUX object
   b will be POLYNOM object */
{
    INT erg = OK;
    CTO(TABLEAUX,"specht_poly(1)",a);
    CE2(a,b,specht_poly);
    {
    OP c,d,e,f;
    INT i,j,diff=0;




    c = CALLOCOBJECT();
    /* minimal entry must be 1 *//* AK 140703 */
    min_tableaux(a,c);
    if (S_O_K(c) != INTEGER) 
        {
        debugprint(c);
        error("specht_poly:non integer entries in the tableau");
        FREEALL(c); goto endr_ende;
        }
    if (S_I_I(c) != 1)
        {
        diff = S_I_I(c)-1;
        FREESELF(c);
        }
    d = CALLOCOBJECT();
    e = CALLOCOBJECT();
    f = CALLOCOBJECT();
    erg += conjugate(S_T_U(a),c);
    erg += weight(c,f);
    erg += b_skn_po(callocobject(),callocobject(),NULL,b);
    erg += m_l_nv(f,S_PO_S(b));
    M_I_I(1,S_PO_K(b));

    if (S_O_K(S_T_U(a)) == PARTITION) 
        {
        for (i=0L; i<S_PA_LI(c); i++)
            {
            erg += b_sk_mo(callocobject(),callocobject(),d);
            erg += m_l_nv(f,S_MO_S(d));
            M_I_I(1L,S_MO_K(d));
            for (j=0L;j<S_PA_II(c,i);j++)
                M_I_I(1L,S_MO_SI(d,
                    S_T_IJI(a,j,S_PA_LI(c)-1L-i)-1L) - diff);
            
            erg += vander_gen(d,e); /* e ist poly auch falls 1*/
            MULT_APPLY(e,b);
            }
        }
    else if (S_O_K(S_T_U(a)) == SKEWPARTITION) 
        {
        for (i=0L; i<S_SPA_GLI(c); i++)
            {
            erg += b_sk_mo(callocobject(),callocobject(),d);
            erg += m_l_nv(f,S_MO_S(d));
            M_I_I(1L,S_MO_K(d));
            for (j=spaltenanfang(a,i);j<=spaltenende(a,i);j++)
                {
                M_I_I(1+spaltenanfang(a,i),
                       S_MO_SI(d,S_T_IJI(a,j,i)-1L) - diff);
                }
            
            erg += vander_gen(d,e); /* e ist poly auch falls 1*/
            MULT_APPLY(e,b);
            }
        }
    FREEALL4(c,d,e,f);
    }
    ENDR("specht_poly");
}
#endif /* TABLEAUXTRUE */

/****************************************************************************/
/*                                                                          */
/*    Name: alt_sdg_trafo()                        */
/*  Diese Routine transformiert die seminormale Matrix D der irreduziblen   */
/*  Darstellung [part] der Sn, wenn part selbstassoziiert ist, so dass      */
/*  sie in zwei Bloecke entlang der Hauptdiagonale reduziert wird. Diese    */
/*  Bloecke sind dann die seminormalen Matrizen zu den irreduziblen Dar-    */
/*  stellungen [part]+ und [part]- der An, in die die Darstellung [part]    */
/*  zerfaellt.                                                              */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 130892 */

#ifdef MATRIXTRUE

INT alt_sdg_trafo(part,D)
  OP  part;        /* Partition der Darstellung           */
  OP  D;          /* Beginn: seminormale Matrix zu [part]     */
              /* Ende: seminormale Matrix zu [part] in Block- */
              /*     gestalt                 */
  {
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  v_sgn;        /* Vorzeichenvektor fuer die Tableaux-Permuta-   */
              /* tionen                     */
  OP  mat1;        /* Block oben links der darstellenden Matrix,   */
              /* wenn part = part'               */
  OP  mat2;        /* Block unten rechts der darstellenden Matrix, */
              /* wenn part = part'               */
  OP  psi,          /* Tableaufunktionswerte             */
    psii,psij;
  OP  tab;        /* Vektor der Standardtableaux zu part       */
  OP  n;          /* Gewicht von part               */
  OP  zwei;        /* INTEGER-Objekt 2L               */
  OP  eins;        /* INTEGER-Objekt -1L               */
  OP  im;          /* Imaginaere Einheit i             */
  OP  hilf;
  INT  i,j;
  INT  dim;        /* Dimension der Matrix ueber der Sn       */
  INT erg = OK;      /* Variable zum Ablaufcheck           */

  INT  make_tab_signs();  /* Routine zur Berechnung der Vorzeichen der  */
              /* Permutationen, die das 1.Standardtableau in  */
              /* die anderen ueberfuehren            */
  INT make_all_st_tabs(); /* Routine zur Berechnung der Standardtableaux  */
              /* in LLS-Ordnung                */

    CTO(PARTITION,"alt_sdg_trafo(1)",part);
    CTO(MATRIX,"alt_sdg_trafo(2)",D);

  /*** Test, ob die Partition part selbstassoziiert ist *******************/

  conpar = callocobject();
  erg += conjugate(part,conpar);
  if(part_comp(part,conpar) != 0L)
    {
    erg += freeall(conpar);
    error("alt_sdg_trafo : partition is not selfassociated ");
    return erg;
    }

  /*** Falls die Partition part selbstassoziiert ist, wird die darstel- ***/
  /*** lende Matrix der Sn so transformiert, dass sie in zwei inaequi-  ***/
  /*** valente seminormale Darstellungen zerfaelllt.                 ***/

  n = callocobject();
  tab = callocobject();
  v_sgn = callocobject();
  mat1 = callocobject();
  mat2 = callocobject();
  hilf = callocobject();
  zwei = callocobject();
  eins = callocobject();
  im = callocobject();

  erg += make_all_st_tabs(part,tab);
  erg += make_tab_signs(part,v_sgn);
  dim = S_V_LI(v_sgn);
  erg += weight(part,n);
  erg += m_ilih_m(dim, dim,mat1);
  erg += copy(mat1,mat2);
  M_I_I(2L,zwei);
  M_I_I(-1L,eins);
  erg += squareroot(eins,im);

  psi = callocobject();
  psii = callocobject();
  psij = callocobject();

  for(i=0L;i<dim;i++)
    for(j=i+1L;j<dim;j++)
      if(!(nullp(S_M_IJ(D,i,j))))
        {
        erg += tab_funk(n,part,S_V_I(tab,i),psii);
        erg += tab_funk(n,part,S_V_I(tab,j),psij);
        erg += div(psii,psij,psi);
        erg += squareroot(psi,psi);
        erg += mult_apply(psi,S_M_IJ(D,i,j));
        erg += invers(psi,psi);
        erg += mult_apply(psi,S_M_IJ(D,j,i));
        }

  /*** Berechnung der transformierten Matrix der An ***********************/

  /*** Berechnung der Matrix im reellen Fall ***/
  if(S_V_II(v_sgn,dim-1) == 1L)
    for(i=0L;i<dim/2L;i++)
      for(j=0L;j<dim/2L;j++)
        {
        /*** Berechnung des Blockes links oben ***/
        erg += copy(S_M_IJ(D,dim-i-1,dim-j-1),
              S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,i),S_M_IJ(D,i,dim-j-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,dim-i-1,j),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,i,j),hilf);
        erg += mult_apply(S_V_I(v_sgn,i),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += div(S_M_IJ(mat1,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat1,i,j));

        /*** Berechnung des Blockes rechts unten ***/
        erg += copy(S_M_IJ(D,dim/2-i-1,dim/2-j-1),
              S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-i-1),
              S_M_IJ(D,dim/2+i,dim/2-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),
              S_M_IJ(D,dim/2-i-1,dim/2+j),hilf);
        erg += mult_apply(eins,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),S_M_IJ(D,dim/2+i,
              dim/2+j),hilf);
        erg += mult_apply(S_V_I(v_sgn,dim/2-i-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += div(S_M_IJ(mat2,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat2,i,j));
        }

  /*** Berechnung der Matrix im komplexen Fall ***/
  if(S_V_II(v_sgn,dim-1) == -1L)
    for(i=0L;i<dim/2L;i++)
      for(j=0L;j<dim/2L;j++)
        {
        /*** Berechnung des Blockes links oben ***/
        erg += copy(S_M_IJ(D,dim-i-1,dim-j-1),
              S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,i),S_M_IJ(D,i,dim-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,dim-i-1,j),hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,i,j),hilf);
        erg += mult_apply(S_V_I(v_sgn,i),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += div(S_M_IJ(mat1,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat1,i,j));

        /*** Berechnung des Blockes rechts unten ***/
        erg += copy(S_M_IJ(D,dim/2-i-1,dim/2-j-1),
              S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-i-1),
              S_M_IJ(D,dim/2+i,dim/2-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),
              S_M_IJ(D,dim/2-i-1,dim/2+j),hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),S_M_IJ(D,dim/2+i,
              dim/2+j),hilf);
        erg += mult_apply(S_V_I(v_sgn,dim/2-i-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += div(S_M_IJ(mat2,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat2,i,j));
        }

  /*** Belegung der transformierten Matrix ********************************/

  erg += freeself(D);
  erg += m_ilih_nm(dim,dim,D);
  for(i=0;i<dim/2L;i++)
    for(j=0;j<dim/2L;j++)
      {
      erg += copy(S_M_IJ(mat1,i,j),S_M_IJ(D,i,j));
      erg += copy(S_M_IJ(mat2,i,j), S_M_IJ(D,dim/2L+i,dim/2L+j));
      }

  for(i=0L;i<dim;i++)
    for(j=i+1L;j<dim;j++)
      if(!(nullp(S_M_IJ(D,i,j))))
        {
        erg += tab_funk(n,part,S_V_I(tab,i),psii);
        erg += tab_funk(n,part,S_V_I(tab,j),psij);
        erg += div(psij,psii,psi);
        erg += squareroot(psi,psi);
        erg += mult_apply(psi,S_M_IJ(D,i,j));
        erg += invers(psi,psi);
        erg += mult_apply(psi,S_M_IJ(D,j,i));
        }
    

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(v_sgn); erg += freeall(conpar); erg += freeall(mat1);
  erg += freeall(mat2); erg += freeall(hilf); erg += freeall(zwei);
  erg += freeall(eins); erg += freeall(im); erg += freeall(psij);
  erg += freeall(psii); erg += freeall(psi); erg += freeall(tab);
  erg += freeall(n);

  /*** Rueckkehr in die aufrufende Routine ********************************/

    ENDR("alt_sdg_trafo");
  } /* Ende von alt_sdg_trafo */
#endif /* MATRIXTRUE */
/****************************************************************************/
/*                                                                          */
/*  Name: alt_odg_trafo()                          */
/*  Diese Routine transformiert die orthogonale Matrix D der irreduziblen   */
/*  Darstellung [part] der Sn, wenn part selbstassoziiert ist, so dass      */
/*  sie in zwei Bloecke entlang der Hauptdiagonale reduziert wird. Diese    */
/*  Bloecke sind dann die unitaeren Matrizen zu den irreduziblen Darstel-   */
/*  lungen [part]+ und [part]- der An, in die die Darstellung [part]        */
/*  zerfaellt.                                                              */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 130892 */

#ifdef MATRIXTRUE
INT alt_odg_trafo(part,D)
  OP  part;        /* Partition der Darstellung           */  
  OP  D;          /* Beginn: orthogonale Matrix zu [part]     */
              /* Ende: unitaere Matrix zu [part] in Blockge-  */
              /*       stalt                   */
  {
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  v_sgn;        /* Vorzeichenvektor fuer die Tableaux-Permuta-  */
              /* tionen                     */
  OP  mat1;        /* Block oben links der darstellenden Matrix,   */
              /* wenn part = part'               */
  OP  mat2;        /* Block unten rechts der darstellenden Matrix, */
              /* wenn part = part'               */
  OP  zwei;        /* INTEGER-Objekt 2L               */
  OP  eins;        /* INTEGER-Objekt -1L               */
  OP  im;          /* Imaginaere Einheit i             */
  OP  hilf;        /* Hilfsvariable                */
  INT  i,j;
  INT dim;        /* Dimension von D                 */
  INT erg = OK;      /* Variable zum Ablaufcheck           */

  INT  make_tab_signs();  /* Routine zur Berechnung der Vorzeichen der   */
              /* Permutationen, die das 1. Tableau in die   */
              /* anderen ueberfuehren.            */

  /*** Test, ob die Partition part selbstassoziiert ist *******************/

  conpar = callocobject();
  erg += conjugate(part,conpar);
  if(part_comp(part,conpar) != 0L)
    {
    erg += freeall(conpar);
    error("trafo_check : partition is not selfassociated ");
    return erg;
    }

  /*** Falls die Partition part selbstassoziiert ist, wird die darstel- ***/
  /*** lende Matrix der Sn so transformiert, dass sie in zwei inaequi-  ***/
  /*** valente unitaere Darstellungen zerfaelllt.                    ***/


  v_sgn = callocobject();
  mat1 = callocobject();
  mat2 = callocobject();
  hilf = callocobject();
  zwei = callocobject();
  eins = callocobject();
  im = callocobject();

  erg += make_tab_signs(part,v_sgn);
  dim = S_V_LI(v_sgn);
  erg += m_ilih_m(dim, dim,mat1);
  erg += copy(mat1,mat2);
  M_I_I(2L,zwei);
  M_I_I(-1L,eins);
  erg += squareroot(eins,im);

  /*** Berechnung der transformierten Matrix der An ***********************/

  /*** Berechnung der Matrix im reellen Fall ***/
  if(S_V_II(v_sgn,dim-1) == 1L)
    for(i=0L;i<dim/2L;i++)
      for(j=0L;j<dim/2L;j++)
        {
        /*** Berechnung des Blockes links oben ***/
        erg += copy(S_M_IJ(D,dim-i-1,dim-j-1),
              S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,i),S_M_IJ(D,i,dim-j-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,dim-i-1,j),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,i,j),hilf);
        erg += mult_apply(S_V_I(v_sgn,i),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += div(S_M_IJ(mat1,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat1,i,j));

        /*** Berechnung des Blockes rechts unten ***/
        erg += copy(S_M_IJ(D,dim/2-i-1,dim/2-j-1),
              S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-i-1),
              S_M_IJ(D,dim/2+i,dim/2-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),
              S_M_IJ(D,dim/2-i-1,dim/2+j),hilf);
        erg += mult_apply(eins,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),S_M_IJ(D,dim/2+i,
              dim/2+j),hilf);
        erg += mult_apply(S_V_I(v_sgn,dim/2-i-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += div(S_M_IJ(mat2,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat2,i,j));
        }

  /*** Berechnung der Matrix im komplexen Fall ***/
  if(S_V_II(v_sgn,dim-1) == -1L)
    for(i=0L;i<dim/2L;i++)
      for(j=0L;j<dim/2L;j++)
        {
        /*** Berechnung des Blockes links oben ***/
        erg += copy(S_M_IJ(D,dim-i-1,dim-j-1),
              S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,i),S_M_IJ(D,i,dim-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,dim-i-1,j),hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += mult(S_V_I(v_sgn,j),S_M_IJ(D,i,j),hilf);
        erg += mult_apply(S_V_I(v_sgn,i),hilf);
        erg += add_apply(hilf,S_M_IJ(mat1,i,j));
        erg += div(S_M_IJ(mat1,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat1,i,j));

        /*** Berechnung des Blockes rechts unten ***/
        erg += copy(S_M_IJ(D,dim/2-i-1,dim/2-j-1),
              S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-i-1),
              S_M_IJ(D,dim/2+i,dim/2-j-1),hilf);
        erg += mult_apply(eins,hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),
              S_M_IJ(D,dim/2-i-1,dim/2+j),hilf);
        erg += mult_apply(im,hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += mult(S_V_I(v_sgn,dim/2-j-1),S_M_IJ(D,dim/2+i,
              dim/2+j),hilf);
        erg += mult_apply(S_V_I(v_sgn,dim/2-i-1),hilf);
        erg += add_apply(hilf,S_M_IJ(mat2,i,j));
        erg += div(S_M_IJ(mat2,i,j),zwei,hilf);
        erg += copy(hilf,S_M_IJ(mat2,i,j));
        }

  /*** Belegung der transformierten Matrix ********************************/

  erg += freeself(D);
  erg += m_ilih_nm(dim,dim,D);
  for(i=0;i<dim/2L;i++)
    for(j=0;j<dim/2L;j++)
      erg += copy(S_M_IJ(mat1,i,j),S_M_IJ(D,i,j));
  for(i=0;i<dim/2L;i++)
    for(j=0;j<dim/2L;j++)
      erg += copy(S_M_IJ(mat2,i,j),
          S_M_IJ(D,dim/2L+i,dim/2L+j));
    

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(v_sgn);
  erg += freeall(conpar);
  erg += freeall(mat1);
  erg += freeall(mat2);
  erg += freeall(hilf);
  erg += freeall(zwei);
  erg += freeall(eins);
  erg += freeall(im);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("alt_odg_trafo : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von alt_odg_trafo */


#endif /* MTRIXTRUE */
/****************************************************************************/
/*                                      */
/*  Name: an_rz_perm()                            */
/*  Diese Routine berechnet die Zerlegung einer beliebigen Permutation      */
/*  per der An in erzeugende Elemente des Erzeugendensystems (12)(r-1,r),   */
/*  2<r<=n.                                                                 */
/*  Rueckgabewert: OK oder error.                                           */
/*                                      */
/****************************************************************************/
/* PF 220992 */
#ifdef PERMTRUE
INT an_rz_perm(per,res)
  OP   per;      /* Permutation der An                 */
  OP  res;      /* Vektor von INTEGER-Werten, der angibt, welche   */
            /* erzeugenden Elemente von rechts nach links      */
            /* aneinander multipliziert werden muessen, so dass */
            /* die Permutation per entsteht.                */
  {
  OP  rz;        /* Zerlegungsvektor von per in Elementartransposi-  */
            /* tionen                       */
  OP  sig;      /* Signum von per                   */
  INT i,j,k,l;
  INT erg = OK;    /* Variable zum Ablaufcheck              */

  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Test, ob per in der An liegt ***************************************/

  sig = callocobject();
  erg += signum(per,sig);
  if(S_I_I(sig) == -1L)
    {
    erg += freeall(sig);
    error("an_rz_perm : permutation not in An");
    return erg;
    }

  /*** Berechnung der reduzierten Zerlegung von per in Elementartrans-  ***/
  /*** positionen.                                                   ***/

  rz = callocobject();
  erg += rz_perm(per,rz);
  l = S_V_LI(rz);

  /*** Berechnung der Anzahl der erzeugenden Elemente ueber der An ********/

  k = l;
  for(i=0;i<k;i+=2)
    {
    if(S_V_II(rz,i) == 1L)
      l--;
    if((S_V_II(rz,i) == 2L) && (S_V_II(rz,i+1) > 2L))
      l++;
    }

  /*** Berechnung der benoetigten Permutationen (12)(r-1,r) ***************/

  erg += m_il_nv(l,res);
  j = 0L;
  for(i=0;i<k;i+=2)
    {
    if(S_V_II(rz,i) == 1L)
      {
      M_I_I(S_V_II(rz,i+1)-1L,S_V_I(res,j));
      j++;
      }
    if(S_V_II(rz,i) == 2L)
      {
      M_I_I(1L,S_V_I(res,j));
      j++;
      M_I_I(1L,S_V_I(res,j));
      j++;
      if(S_V_II(rz,i+1) > 2L)
        {
        M_I_I(S_V_II(rz,i+1)-1L,S_V_I(res,j));
        j++;
        }
      }  
    if(S_V_II(rz,i) > 2L)
      {
      M_I_I(S_V_II(rz,i)-1L,S_V_I(res,j));
      j++;
      M_I_I(S_V_II(rz,i+1)-1L,S_V_I(res,j));
      j++;
      }
    }

  /*** Speichenplatzfreigabe **********************************************/

  erg += freeall(rz);
  erg += freeall(sig);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("an_rz_perm : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von an_rz_perm */
#endif /* PERMTRUE */
/****************************************************************************/
/*                                                                          */
/*  Name: an_trafo_odg()                          */
/*  Diese Routine berechnet die darstellende unitaere Matrix einer          */
/*  Permutation perm in der Darstellung zu einer Partition part, einge-     */
/*  schraenkt auf die An durch Transformation der darstellenden Matrix      */
/*  ueber der Sn.                                                           */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 140992 */

#ifdef MATRIXTRUE
INT an_trafo_odg(part,perm,D)
  OP  part;        /* Vektor, der die Darstellung beschreibt:     */
              /*     1. Komponente : Partition            */
              /*     2. Komponente : 0L oder 1L           */
  OP  perm;        /* Darzustellende Permutation           */
  OP  D;          /* Ende: unitaere Matrix zu [part](perm)     */
  {
  OP  n;          /* Gewicht von part                */
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  dim;        /* Dimension der Matrix ueber der Sn       */
  OP  sig;              /* Signum von perm                 */
  INT  i;
  INT erg = OK;      /* Variable zum Ablaufcheck           */
  
  INT  alt_odg_trafo();  /* Routine zur Transformation einer zerfallen-  */
              /* den Darstellung                 */
  INT trafo_check();    /* Routine zum Testen der Anordnung der Bloecke */
              /* nach der Transformation             */


    CTO(VECTOR,"an_trafo_odg(1)",part);
    CTO(PERMUTATION,"an_trafo_odg(2)",perm);
    CTO(PARTITION,"an_trafo_odg(1.1)",S_V_I(part,0));
    CTO(INTEGER,"an_trafo_odg(1.2)",S_V_I(part,1));
 

  if (not EMPTYP(D)) 
    erg += freeself(D);

  /*** Test, ob perm in der An liegt **************************************/

  sig = callocobject();
  erg += signum(perm,sig);
  if(S_I_I(sig) == -1L)
    {
    erg += freeall(sig);
    error("an_trafo_odg : permutation not in An");
    return erg;
    }

  /*** Test, ob Laenge von perm mit dem Gewicht von part uebereinstimmt ***/

  n = callocobject();
  erg += weight(S_V_I(part,0L),n);
  if(S_I_I(n) != S_P_LI(perm))
    {
    erg += freeall(sig);
    erg += freeall(n);
    error("an_trafo_odg : permutation and partition don't agree");
    return erg;
    }

  /*** Falls n = 1 oder n = 2, wird D = (1) zurueckgegeben. ***************/

  if((S_P_LI(perm) == 1L) || (S_P_LI(perm) == 2L))
    {
    erg += m_ilih_m(1L,1L,D);
    M_I_I(1L,S_M_IJ(D,0L,0L));
    erg += freeall(sig);
    erg += freeall(n);
    return erg;
    }

  /*** Berechnung der Matrix **********************************************/

  /*** Falls die Partition part nicht selbstassoziiert ist, ist die ***/
  /*** darstellende Matrix gleich der Matrix fuer die Sn.           ***/

  erg += odg(S_V_I(part,0L),perm,D);
  conpar = callocobject();
  erg += conjugate(S_V_I(part,0L),conpar);
  if(part_comp(S_V_I(part,0L),conpar) != 0L)
    {
    erg += freeall(sig);
    erg += freeall(n);
    erg += freeall(conpar);
    return erg;
    }

  /*** Falls die Partition part selbstassoziiert ist, wird die dar- ***/
  /*** stellende Matrix der Sn so transformiert, dass sie in zwei   ***/
  /*** inaequivalente unitaere Darstellungen zerfaellt.             ***/

  erg += alt_odg_trafo(S_V_I(part,0L),D);

  /*** Dann wird mit Hilfe einer Test-Routine nachgeprueft, in      ***/
  /*** welchem der beiden Bloecke die gesuchte Matrixdarstellung    ***/
  /*** steht. Die uebrigen Teile der Matrix werden geloescht.       ***/

  dim = callocobject();
  M_I_I(S_M_LI(D),dim);
  if(trafo_check(S_V_I(part,0L)) == S_V_II(part,1L))
    for(i=0L;i<S_I_I(dim)/2L;i++)
      {
      erg += delete_row_matrix(D,S_M_LI(D)-1L,D);
      erg += delete_column_matrix(D,S_M_LI(D)-1L,D);
      }
  else
    for(i=0L;i<S_I_I(dim)/2L;i++)
      {
      erg += delete_row_matrix(D,0L,D);
      erg += delete_column_matrix(D,0L,D);
      }

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(dim);
  erg += freeall(conpar);
  erg += freeall(sig);
  erg += freeall(n);

  /*** Rueckkehr in die aufrufende Routine ********************************/

    ENDR("an_trafo_odg");
  } /* Ende von an_trafo_odg */


#endif /* MATRIXTRUE */
/****************************************************************************/
/*                                                                          */
/*  Name: an_trafo_sdg()                          */
/*  Diese Routine berechnet die darstellende seminormale Matrix einer       */
/*  Permutation perm in der Darstellung zu einer Partition part, einge-     */
/*  schraenkt auf die An durch Transformation der darstellenden Matrix      */
/*  ueber der Sn.                                                           */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 140992 */

INT an_trafo_sdg(part,perm,D) OP part,perm,D;
/* AK 220704 V3.0 */
          /* part Vektor, der die Darstellung beschreibt:     */
              /*     1. Komponente : Partition            */
              /*     2. Komponente : 0L oder 1L           */
          /* perm Darzustellende Permutation           */
            /* D  Ende: seminormale Matrix zu [part](perm)   */
  {
    INT erg = OK;
    CTO(VECTOR,"an_trafo_sdg(1)",part);
    CTO(PERMUTATION,"an_trafo_sdg(2)",perm);
    CTO(PARTITION,"an_trafo_sdg(1.1)",S_V_I(part,0));
    CTO(INTEGER,"an_trafo_sdg(1.2)",S_V_I(part,1));
    {
#ifdef DGTRUE
  OP  n;          /* Gewicht von part                */
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  dim;        /* Dimension der Matrix ueber der Sn       */
  OP  sig;              /* Signum von perm                 */
  INT  i;
  
  INT  alt_sdg_trafo();  /* Routine zur Transformation einer zerfallen-  */
              /* den Darstellung                 */
  INT trafo_check();    /* Routine zum Testen der Anordnung der Bloecke */
              /* nach der Transformation             */


    FREESELF(D);

  /*** Test, ob perm in der An liegt **************************************/

  sig = callocobject();
  erg += signum(perm,sig);
  if(S_I_I(sig) == -1L)
    {
    FREEALL(sig);
    error("an_trafo_sdg : permutation not in An");
    goto endr_ende;
    }

  /*** Test, ob Laenge von perm mit dem Gewicht von part uebereinstimmt ***/

  n = callocobject();
  erg += weight(S_V_I(part,0L),n);
  if(S_I_I(n) != S_P_LI(perm))
    {
    FREEALL2(sig,n);
    error("an_trafo_sdg : permutation and partition don't agree");
    goto endr_ende;
    }

  /*** Falls n = 1 oder n = 2, wird D = (1) zurueckgegeben. ***************/

  if((S_P_LI(perm) == 1L) || (S_P_LI(perm) == 2L))
    {
    erg += m_ilih_m(1L,1L,D);
    M_I_I(1L,S_M_IJ(D,0L,0L));
    erg += freeall(sig);
    erg += freeall(n);
    return erg;
    }

  /*** Berechnung der Matrix **********************************************/

  /*** Falls die Partition part nicht selbstassoziiert ist, ist die ***/
  /*** darstellende Matrix gleich der Matrix fuer die Sn.           ***/

  erg += sdg(S_V_I(part,0L),perm,D);
  conpar = callocobject();
  erg += conjugate(S_V_I(part,0L),conpar);
  if(part_comp(S_V_I(part,0L),conpar) != 0L)
    {
    erg += freeall(conpar);
    erg += freeall(sig);
    erg += freeall(n);
    return erg;
    }

  /*** Falls die Partition part selbstassoziiert ist, wird die dar- ***/
  /*** stellende Matrix der Sn so transformiert, dass sie in zwei   ***/
  /*** inaequivalente unitaere Darstellungen zerfaellt.             ***/

  erg += alt_sdg_trafo(S_V_I(part,0L),D);

  /*** Dann wird mit Hilfe einer Test-Routine nachgeprueft, in      ***/
  /*** welchem der beiden Bloecke die gesuchte Matrixdarstellung    ***/
  /*** steht. Die uebrigen Teile der Matrix werden geloescht.       ***/

  dim = callocobject();
  M_I_I(S_M_LI(D),dim);
  if(trafo_check(S_V_I(part,0L)) == S_V_II(part,1L))
    for(i=0L;i<S_I_I(dim)/2L;i++)
      {
      erg += delete_row_matrix(D,S_M_LI(D)-1L,D);
      erg += delete_column_matrix(D,S_M_LI(D)-1L,D);
      }
  else
    for(i=0L;i<S_I_I(dim)/2L;i++)
      {
      erg += delete_row_matrix(D,0L,D);
      erg += delete_column_matrix(D,0L,D);
      }

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(dim);
  erg += freeall(conpar);
  erg += freeall(sig);
  erg += freeall(n);

  /*** Rueckkehr in die aufrufende Routine ********************************/
#endif
    }
    ENDR("an_trafo_sdg");
  } /* Ende von an_trafo_sdg */


/****************************************************************************/
/*                                      */
/*  Name: gen_mat()                              */
/*  Diese Routine berechnet die darstellende unitaere Matrix ueber der      */
/*  An des erzeugenden Elements (12)(index+1L,index+2L) zur irreduzib-      */
/*  len Darstellung [part]+ oder [part]-. Dabei bestimmt die Zahl ref,      */
/*  welcher Block der Matrix berechnet wird, die sonst durch Trans-         */
/*  formation der darstellenden Matrix ueber der Sn entstehen wuerde.       */
/*  Rueckgabewert: OK oder error.                                           */
/*                                      */
/****************************************************************************/
/* PF 280992 */

#ifdef MATRIXTRUE
INT gen_mat(part,index,ref,res)
  OP  part;        /* selbstassoziierte Partition           */
  INT index;        /* Nummer der erzeugenden Permutation, deren   */
              /* darstellende Matrix berechnet werden soll   */
  INT ref;        /* INTEGER-Wert: 0L, falls der Block links oben */
              /*          berechnet werden soll,       */
              /*         1L, sonst.               */
  OP  res;        /* Ende: darstellende Matrix von [part]+ bzw.   */
              /* [part]- der Permutation (12)(index+1,index+2)*/
  {
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  h_part;        /* Hakenpartition zu part             */
  OP  tab;        /* Vektor der Standardtableaux zu part       */
  OP  sig;        /* Vorzeichenvektor der Permutationen zu den   */
              /* Standardtableaux zu part           */
  OP  vgl_tab;      /* Tableau (index+1,index+2)*Standardtableau   */
  OP  dist1;        /* Axialdistanz von index+1 und index+2     */
  OP  dist2;        /* Axialdistanz von 1 und 2           */
  OP  n;          /* Grad der An                   */
  OP  eins;        /* INTEGER 1L                   */
  OP  zwei;        /* INTEGER 2L                   */
  OP  im;          /* komlpexe Einheit -i               */
  OP  exp;        /* Vorfaktor bei der Belegung           */
  INT  i,j,k,l;
  INT  fac;        /* Faktor bei der Indizierung           */
  INT  erg = OK;      /* Variable zum Ablaufcheck           */

  INT make_all_st_tabs();  /* Routine zur Berechnung der Standardtableaux   */
              /* zu part                     */
  INT  get_index();    /* Routine zur Bestimmung des Index eines Tab-  */
              /* leaus im Tableauvektor             */

    CTO(PARTITION,"gen_mat(1)",part);
    SYMCHECK((ref != 1) && (ref != 0),"gen_mat:wrong value par2");

  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Test, ob ref = 0L oder 1L ******************************************/

  if((ref != 0L) && (ref != 1L))
    {
    error("gen_mat : wrong reference INTEGER ");
    return erg;
    }

  /*** Test, ob index < n-1 ***********************************************/

  n = callocobject();
  erg += weight(part,n);
  if(S_I_I(n) - 2L < index)
    {
    erg += freeall(n);
    error("gen_mat : index of generating element too big ");
    return erg;
    }

  /*** Test, ob die Partition part selbstassoziiert ist *******************/

  conpar = callocobject();
  erg += conjugate(part,conpar);
  if(part_comp(part,conpar) != 0L)
    {
    erg += freeall(n);
    erg += freeall(conpar);
    error("gen_mat : partition is not selfassociated ");
    return erg;
    }

  /*** Falls part = (2,1) oder part = (2,2), sind die Matrizen eindi-   ***/
  /*** mensional und koennen direkt angegeben werden.                 ***/

  if((S_I_I(n) == 3L) || (S_I_I(n) == 4L))
    {
    h_part = callocobject();
    erg += hook_part(part,h_part);
    erg += m_ilih_m(1L,1L,res);
    if(index == 1L)
      erg += wert(ref,h_part,S_M_IJ(res,0L,0L));
    else
      M_I_I(1L,S_M_IJ(res,0L,0L));
    erg += freeall(conpar);
    erg += freeall(h_part);
    erg += freeall(n);
    return erg;
    }

  /*** Zunaechst berechnen wir die Standardtableaux zur Partition part  ***/
  /*** und den Vorzeichenvetor der Permutationen, die das erste         ***/
  /*** Standardtableau in das i-te ueberfuehren.                        ***/

  tab = callocobject();
  sig = callocobject();
  erg += make_all_st_tabs(part,tab);
  erg += make_tab_signs(part,sig);

  /*** Belegung der darstellenden Matrix von (1 2)(index+1,index+2) *******/

  vgl_tab = callocobject();
  dist1 = callocobject();
  dist2 = callocobject();
  eins = callocobject();
  zwei = callocobject();
  im = callocobject();
  exp = callocobject();

  M_I_I(1L,eins);
  M_I_I(2L,zwei);
  erg += addinvers(eins,im);
  erg += squareroot(im,im);
  erg += addinvers_apply(im);
  l = S_V_LI(tab)/2L;
  fac = ref*l;
  erg += m_ilih_nm(l,l,res);
  for(i=0L;i<l;i++)
    {
      /*** Belegung der Hauptdiagonale der Matrix ***/
    erg += get_ax_dist(S_V_I(tab,fac+i),index+1,index+2,dist1);
    erg += invers(dist1,S_M_IJ(res,i,i));
    erg += get_ax_dist(S_V_I(tab,fac+i),1,2,dist2);
    erg += mult_apply(dist2,S_M_IJ(res,i,i));

      /*** Belegung der Nichtdiagonalelemente innerhalb des Blockes ***/
    erg += op_transpo_tab(index+1L,S_V_I(tab,fac+i),vgl_tab);
    k = get_index(vgl_tab,tab);
    if(k != -1L)
      {
      if(((fac==0L) && (k<l)) || ((fac==l) && (k>=l)))
        j = k-fac;
      else
        j = S_V_LI(tab)-k-1-fac;
      erg += invers(dist1,S_M_IJ(res,i,j));
      erg += hoch(S_M_IJ(res,i,j),zwei,S_M_IJ(res,i,j));
      erg += addinvers_apply(S_M_IJ(res,i,j));
      erg += add_apply(eins,S_M_IJ(res,i,j));
      erg += squareroot(S_M_IJ(res,i,j),S_M_IJ(res,i,j));
      erg += mult_apply(dist2,S_M_IJ(res,i,j));
      if(!(((fac==0L) && (k<l)) || ((fac==l) && (k>=l))))
        {
        erg += add(eins,S_V_I(sig,S_V_LI(sig)-1L),exp);
        erg += hoch(zwei,exp,exp);
        erg += hoch(im,exp,exp);
        erg += mult_apply(S_V_I(sig,fac+i),exp);
        if(ref == 0L)
          erg += addinvers_apply(exp);
        erg += mult_apply(exp,S_M_IJ(res,i,j));
        }
      }
    }
  
  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(conpar);
  erg += freeall(tab);
  erg += freeall(n);
  erg += freeall(vgl_tab);
  erg += freeall(dist1);
  erg += freeall(dist2);
  erg += freeall(eins);
  erg += freeall(zwei);
  erg += freeall(im);
  erg += freeall(exp);

  /*** Rueckkehr in die aufrufende Routine ********************************/

    ENDR("gen_mat");
  } /* Ende von gen_mat */
#endif /* MATRIXTRUE */

/****************************************************************************/
/*                                      */
/*  Name: gen_smat()                            */
/*  Diese Routine berechnet die darstellende seminormale Matrix ueber      */
/*  der An des erzeugenden Elements (12)(index+1L,index+2L) zur irre-      */
/*  duziblen Darstellung [part]+ oder [part]-. Dabei bestimmt die Zahl     */
/*  ref welcher Block der Matrix berechnet wird, die sonst durch Trans-    */
/*  formation der darstellenden Matrix ueber der Sn entstehen wuerde.      */
/*  Rueckgabewert: OK oder error.                                          */
/*                                      */
/****************************************************************************/
/* PF 280992 */

INT gen_smat(part,index,ref,res)
  OP  part;        /* selbstassoziierte Partition           */
  INT index;        /* Nummer der erzeugenden Permutation, deren   */
              /* darstellende Matrix berechnet werden soll   */
  INT ref;        /* INTEGER-Wert: 0L, falls der Block links oben */
              /*          berechnet werden soll,       */
              /*         1L, sonst.               */
  OP  res;        /* Ende: darstellende Matrix von [part]+ bzw.   */
              /* [part]- der Permutation (12)(index+1,index+2)*/
  {
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  h_part;        /* Hakenpartition zu part             */
  OP  tab;        /* Vektor der Standardtableaux zu part       */
  OP  sig;        /* Vorzeichenvektor der Permutationen zu den   */
              /* Standardtableaux zu part           */
  OP  vgl_tab;      /* Tableau (index+1,index+2)*Standardtableau   */
  OP  dist1;        /* Axialdistanz von index+1 und index+2     */
  OP  dist2;        /* Axialdistanz von 1 und 2           */
  OP  n;          /* Grad der An                   */
  OP  eins;        /* INTEGER 1L                   */
  OP  zwei;        /* INTEGER 2L                   */
  OP  im;          /* komlpexe Einheit -i               */
  OP  exp;        /* Vorfaktor bei der Belegung           */
  OP  psi,        /* Tableaufunktionswerte             */
    psii,psij;  
  INT  i,j,k,l;
  INT  fac;        /* Faktor bei der Indizierung           */
  INT  erg = OK;      /* Variable zum Ablaufcheck           */

  INT make_all_st_tabs();  /* Routine zur Berechnung der Standardtableaux  */
              /* zu part                     */
  INT  get_index();    /* Routine zur Bestimmung des Index eines Tab-  */
              /* leaus im Tableauvektor             */

  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Test, ob ref = 0L oder 1L ******************************************/

  if((ref != 0L) && (ref != 1L))
    {
    error("gen_smat : wrong reference INTEGER ");
    return erg;
    }

  /*** Test, ob index < n-1 ***********************************************/

  n = callocobject();
  erg += weight(part,n);
  if(S_I_I(n) - 2L < index)
    {
    erg += freeall(n);
    error("gen_smat : index of generating element too big ");
    return erg;
    }

  /*** Test, ob die Partition part selbstassoziiert ist *******************/

  conpar = callocobject();
  erg += conjugate(part,conpar);
  if(part_comp(part,conpar) != 0L)
    {
    erg += freeall(n);
    erg += freeall(conpar);
    error("gen_smat : partition is not selfassociated ");
    return erg;
    }

  /*** Falls part = (2,1) oder part = (2,2), sind die Matrizen eindi-   ***/
  /*** mensional und koennen direkt angegeben werden.                 ***/

  n = callocobject();
  erg += weight(part,n);
  if((S_I_I(n) == 3L) || (S_I_I(n) == 4L))
    {
    h_part = callocobject();
    erg += hook_part(part,h_part);
    erg += m_ilih_m(1L,1L,res);
    if(index == 1L)
      erg += wert(ref,h_part,S_M_IJ(res,0L,0L));
    else
      M_I_I(1L,S_M_IJ(res,0L,0L));
    erg += freeall(conpar);
    erg += freeall(h_part);
    erg += freeall(n);
    return erg;
    }

  /*** Zunaechst berechnen wir die Standardtableaux zur Partition part  ***/
  /*** und den Vorzeichenvetor der Permutationen, die das erste         ***/
  /*** Standardtableau in das i-te ueberfuehren.                        ***/

  tab = callocobject();
  sig = callocobject();
  erg += make_all_st_tabs(part,tab);
  erg += make_tab_signs(part,sig);

  /*** Belegung der darstellenden Matrix von (1 2)(index+1,index+2) *******/

  vgl_tab = callocobject();
  dist1 = callocobject();
  dist2 = callocobject();
  eins = callocobject();
  zwei = callocobject();
  im = callocobject();
  exp = callocobject();
  psii = callocobject();
  psij = callocobject();
  psi = callocobject();

  M_I_I(1L,eins);
  M_I_I(2L,zwei);
  erg += addinvers(eins,im);
  erg += squareroot(im,im);
  erg += addinvers_apply(im);
  l = S_V_LI(tab)/2L;
  fac = ref*l;
  erg += m_ilih_nm(l,l,res);
  for(i=0L;i<l;i++)
    {
      /*** Belegung der Hauptdiagonale der Matrix ***/
    erg += get_ax_dist(S_V_I(tab,fac+i),index+1,index+2,dist1);
    erg += invers(dist1,S_M_IJ(res,i,i));
    erg += get_ax_dist(S_V_I(tab,fac+i),1,2,dist2);
    erg += mult_apply(dist2,S_M_IJ(res,i,i));

      /*** Belegung der Nichtdiagonalelemente innerhalb des Blockes ***/
    erg += op_transpo_tab(index+1L,S_V_I(tab,fac+i),vgl_tab);
    k = get_index(vgl_tab,tab);
    if(k != -1L)
      {
      if(((fac==0L) && (k<l)) || ((fac==l) && (k>=l)))
        j = k-fac;
      else
        j = S_V_LI(tab)-k-1-fac;
      erg += invers(dist1,S_M_IJ(res,i,j));
      erg += hoch(S_M_IJ(res,i,j),zwei,S_M_IJ(res,i,j));
      erg += addinvers_apply(S_M_IJ(res,i,j));
      erg += add_apply(eins,S_M_IJ(res,i,j));
      erg += squareroot(S_M_IJ(res,i,j),S_M_IJ(res,i,j));
      erg += mult_apply(dist2,S_M_IJ(res,i,j));
      if(!(((fac==0L) && (k<l)) || ((fac==l) && (k>=l))))
        {
        erg += add(eins,S_V_I(sig,S_V_LI(sig)-1L),exp);
        erg += hoch(zwei,exp,exp);
        erg += hoch(im,exp,exp);
        erg += mult_apply(S_V_I(sig,fac+i),exp);
        if(ref ==0L)
          erg += addinvers_apply(exp);
        erg += mult_apply(exp,S_M_IJ(res,i,j));
        }
      erg += tab_funk(n,part,S_V_I(tab,fac+i),psii);
      erg += tab_funk(n,part,S_V_I(tab,fac+j),psij);
      erg += div(psij,psii,psi);
      erg += squareroot(psi,psi);
      erg += mult_apply(psi,S_M_IJ(res,i,j));
      }
    }
  
  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(conpar);
  erg += freeall(tab);
  erg += freeall(n);
  erg += freeall(vgl_tab);
  erg += freeall(dist1);
  erg += freeall(dist2);
  erg += freeall(eins);
  erg += freeall(zwei);
  erg += freeall(im);
  erg += freeall(exp);
  erg += freeall(psii);
  erg += freeall(psij);
  erg += freeall(psi);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("gen_smat : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von gen_smat */


/****************************************************************************/
/*                                      */
/*  Name: get_ax_dist()                            */
/*   Diese Routine berechnet die Axialdistanz der Punkte r und s im          */
/*  Standardtableau tab.                                                    */
/*  Rueckgabewert: OK oder error.                                           */
/*                                      */
/****************************************************************************/
/* PF 071092 */

INT get_ax_dist(tab,r,s,res) OP tab,res; INT r,s;
/* tab Standardtableau                 */
/* r,s Zahlen zwischen denen die Axialdistanz berechnet werden soll. */
/* res: Axialdistanz von r und s in tab     */
  {
  OP  s1;          /* Positionsvektor [i,j], falls tab(i,j) = r   */
  OP  s2;          /* Positionsvektor [k,l], falls tab(k,l) = s   */
  INT erg = OK;      /* Variable zum Ablaufcheck           */


  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Berechnung der Positionen (i,j) und (k,l), an denen r bzw. s in  ***/
  /*** tab stehen.                                                      ***/

  s1 = callocobject();
  s2 = callocobject();
  erg += get_position(tab,r,s1);
  erg += get_position(tab,s,s2);

  /*** Berechnung der Axialdistanz ****************************************/

  M_I_I(S_V_II(s2,0L)-S_V_II(s2,1L)+S_V_II(s1,1L)-S_V_II(s1,0L),res);

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(s1);
  erg += freeall(s2);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    EDC("get_ax_dist");
  return erg;
  } /* Ende von get_ax_dist */

/****************************************************************************/
/*                                      */
/*  Name: get_position()                          */
/*   Diese Routine berechnet die Position des Zahl r in dem Standard-        */
/*  tableau tab und schreibt sie in den Vektor res = [i,j] der Laenge 2.    */
/*  Rueckgabewert: 0L, falls r gefunden wurde,                */
/*            -1L, sonst.                        */
/*                                      */
/****************************************************************************/
/* PF 071092 */

INT get_position(tab,r,res) OP tab, res; INT r;
          /* tab Standardtableau                 */
            /* i Zahl die gesucht werden soll         */
          /* res Positionsvektor [i,j], falls tab(i,j) = r   */
  {
  INT  erg = OK;      /* Variable zum Ablaufcheck           */
  INT i,j;

  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Suche der Zahl r im Standardtableau tab ****************************/

  erg += m_il_v(2L,res);
  for(i=0L;i<S_T_HI(tab);i++) /* HI statt LI AK 090693 */
    for(j=0L;j<S_T_LI(tab);j++) /* LI statt HI  AK 090693 */
      if((!EMPTYP(S_T_IJ(tab,i,j))) && (S_T_IJI(tab,i,j) == r))
        {
        M_I_I(i,S_V_I(res,0L));
        M_I_I(j,S_V_I(res,1L));
        if (erg != OK)
          EDC("get_position");
        return 0L;
        }

  /*** Falls r nicht im Standardtableau tab steht, wird -1 zurueckgege- ***/
  /*** ben.                                ***/

  return -1L;

  } /* Ende von get_position */

/****************************************************************************/
/*                                      */
/*  Name: op_transpo_tab()                          */
/*  Diese Routine wendet die Permutation (transpo, transpo+1) auf das       */
/*  Standardtableau tab an und gibt das resultierende Tableau in res        */
/*  zurueck.                                  */
/*  Rueckgabewert: OK oder error                        */
/*                                      */
/****************************************************************************/
/* PF 071092 */

static INT op_transpo_tab(transpo,tab,res)
  INT  transpo;      /* Zahl, die die Transposition           */
              /* (transpo,transpo+1) beschreibt.         */
  OP  tab;        /* Standardtableau                 */
  OP  res;        /* Ende: Tableau (transpo,transpo+1)*tab     */
  {
  INT i,j;
  INT erg = OK;      /* Variable zum Ablaufcheck           */

  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Vertauschen der Eintraege transpo und transpo+1 in tab *************/

  erg += copy(tab,res);
  for(i=0L;i<S_T_LI(res);i++)
    for(j=0L;j<S_T_HI(res);j++)
      {
      if(!EMPTYP(S_T_IJ(res,i,j)))
      if((S_T_IJI(res,i,j)==transpo) || (S_T_IJI(res,i,j)==transpo+1))
        {
        if(S_T_IJI(res,i,j)==transpo) 
          erg += inc(S_T_IJ(res,i,j));
        else
          erg += dec(S_T_IJ(res,i,j));
        }
      }

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("op_transpo_tab : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von op_transpo_tab */


/****************************************************************************/
/*                                      */
/*  Name: get_index()                            */
/*  Routine zur Berechnung der Stelle einer Elements tab in einem Vektor    */
/*  vector.                                       */
/*  Rueckgabewert:  index, falls tab in vector vorkommt,            */
/*      -1     sonst                             */
/*                                      */
/****************************************************************************/
/* PF 200891 V1.3 */

INT get_index(tab,vector) OP  tab,vector;
  {
  INT  i;

  for(i=0;i<S_V_LI(vector);i++)
    if (comp(tab,S_V_I(vector,i)) == 0)
      return i;
  return -1;
  } /* Ende von get_index */

    

/****************************************************************************/
/*                                                                          */
/*  Name: make_all_st_tabs()                        */
/*  Diese Routine berechnet alle Standard-Young-Tableaux zu einer Partition */
/*  par, geordnet in LLS-ordnung.                                           */
/*  Rueckgabewert: 0L oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 120892 */

INT make_all_st_tabs(par,res)
  OP   par;      /* Partition                     */
  OP  res;      /* Ende: Vektor von Standard-Young-Tableaux geord-  */
            /*      net in LLS-Ordnung              */
  {
  OP  n;        /* Gewicht von par                   */
  OP  new_par;    /* neue Partition von n-1               */
  OP  tab;      /* Tableau                       */
  OP  hilf;      /* Hilfsvektor beim Umspeichern           */
  OP  zw;        /* Zwischenergebnis bei der Rekursion         */
  OP  eins;      /* INTEGER-Object 1L                 */
  OP  mat;      /* Matrix als self-part eines Tableau's       */
  OP   ta;        /* Tableau als einkomponentiger Vektor        */
  INT i,j,k;    
  INT erg = 0L;    /* Variable zum Ablaufcheck             */
  CTO(PARTITION,"make_all_st_tabs(1)",par);


  if (not EMPTYP(res)) 
    erg += freeself(res);

  eins = callocobject();
  tab = callocobject();

  M_I_I(1L,eins);

  /*** Falls par = (1), existiert nur ein einziges Tableau T = 1 . ********/

  if((S_PA_LI(par) == 1) && (S_PA_II(par,0) == 1))
    {
    mat = callocobject();
    erg += m_ilih_m(1,1,mat);
    erg += copy(eins,S_M_IJ(mat,0,0));

    erg += m_us_t(par,mat,tab);
    erg += m_o_v(tab,res);

    erg += freeall(mat);
    erg += freeall(eins);
    erg += freeall(tab);
    return OK;
    }

  /*** Falls par != (1) , werden die Tableaux rekursiv erzeugt ************/

  n = callocobject();
  zw = callocobject();
  new_par = callocobject();
  hilf = callocobject();
  ta = callocobject();

  erg += weight(par,n);
  erg += init(VECTOR,res);

  /*** Durchlaufe die Zeilen des Young-Diagramms zu par ...  ***/
  for(i=S_PA_LI(par)-1;i>0;i--)
  /*** ... und pruefe, ob die Zahl n in dieser Zeile auftreten kann. ***/
    if(S_PA_II(par,i) > S_PA_II(par,i-1))
      {
      /*** Berechne die Partition, die entsteht, wenn n aus dem ***/
      /*** Tableau entfernt wird und erzeuge alle moeglichen    ***/
      /*** Tableaux zu dieser Partition, fuege die Zahl n an    ***/
      /*** entsprechender Stelle wieder ein und haenge alle so  ***/
      /*** gefundenen Tableaux an den Ergebnisvektor an.        ***/

      erg += copy(par,new_par);
      erg += sub(S_PA_I(new_par,i),eins,S_PA_I(new_par,i));
      erg += make_all_st_tabs(new_par,zw);
      for(j=0;j<S_V_LI(zw);j++)
        {
        erg += copy(S_V_I(zw,j),tab);
        erg += inc(S_T_S(tab));
        erg += copy(n,S_M_IJ(S_T_S(tab),S_PA_LI(par)-1L-i,
             S_PA_II(new_par,i)));
        erg += copy(par,S_T_U(tab));
        erg += m_o_v(tab,ta);
        erg += append_vector(res,ta,hilf);
        erg += copy(hilf,res);
        erg += freeself(hilf);
        }
      }
  
  /*** Erzeuge schliesslich die Tableaux mit der Zahl n in der letzten  ***/
  /*** Zeile.                               ***/

  k = 0;
  erg += copy(par,new_par);
  erg += sub(S_PA_I(new_par,0),eins,S_PA_I(new_par,0));

  /*** Falls die letzte Zeile nur Laenge 1 hat ***/
  if(S_PA_II(new_par,0) == 0L)
    {
    erg += m_il_v(S_PA_LI(par)-1L,hilf);
    for(j=S_PA_LI(par)-1L;j>0;j--)
      erg += copy(S_PA_I(par,j),S_V_I(hilf,j-1));
    erg += m_v_pa(hilf,new_par);
    k++;
    }
  erg += make_all_st_tabs(new_par,zw);
  for(j=0;j<S_V_LI(zw);j++)
    {
    erg += copy(S_V_I(zw,j),tab);
    erg += inc(S_T_S(tab));
    if(k==0L)
      {
      erg += copy(n,S_M_IJ(S_T_S(tab),S_PA_LI(par)-1L,
           S_PA_II(new_par,0)));
      erg += copy(par,S_T_U(tab));
      }
    else
      {
      erg += copy(n,S_M_IJ(S_T_S(tab),S_PA_LI(par)-1L,0));
      erg += copy(par,S_T_U(tab));
      }
    erg += m_o_v(tab,ta);
    erg += append_vector(res,ta,hilf);
    erg += copy(hilf,res);
    }

  /*** Speicherfreigabe ***************************************************/

  erg += freeall(zw);
  erg += freeall(new_par);
  erg += freeall(eins);
  erg += freeall(tab);
  erg += freeall(ta);

  /*** Rueckkehr in die aufrufende Routine ********************************/

    ENDR("make_all_st_tabs");
  } /* Ende von make_all_st_tabs */


/****************************************************************************/
/*                                                                          */
/*  Name: make_tab_signs()                          */
/*  Diese Routine berechnet einen Vorzeichenvektor der Permutationen        */
/*  pi_1, ... , pi_f, wobei f die Anzahl der Standard-Young-Tableaux        */
/*  zu einer gegebenen Partition par ist, und pi_i die Permutation, die     */
/*  das erste Tableau T_1 in das i-te Tableau ueberfuehrt. Die Tableaux     */
/*  sind dabei in LLS-Ordnung geordnet.                    */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 130892 */

INT make_tab_signs(par,res)
  OP  par;        /* Partition des Umrisses der Tableaux       */
  OP  res;        /* Am Ende: Vorzeichenvektor           */
  {
  OP  pi;          /* Permutation                   */
  OP  mat;        /* Tableau                     */
  OP   conpar;        /* zu par konjugierte Partition         */
  OP  n;          /* Gewicht der Partition par           */
  INT  i,j,k,l;
  INT erg = OK;      /* Variable zum Ablaufcheck           */

  INT make_all_st_tabs(); /* Routine zur Berechnung der Standardtableaux  */


  if (not EMPTYP(res)) 
    erg += freeself(res);
  
  /*** Speicherplatzreservierung ******************************************/

  pi = callocobject();
  conpar = callocobject();
  mat = callocobject();
  n = callocobject();

  /*** Berechnung der Standard-Young-Tableaux, der konjugierten Parti-  ***/
  /*** tion und des Gewichts von par, sowie Initialisierung von pi.     ***/

  erg += make_all_st_tabs(par,res);
  erg += conjugate(par,conpar);
  erg += weight(par,n);
  erg += m_il_p(S_I_I(n),pi);

  /*** Berechnung des Vorzeichenvektors ***********************************/

  /*** Durchlaufe alle Tableaux zu par ... ***/
  for(i=0L;i<S_V_LI(res);i++)
    {
    /*** ... und belege die Permutation pi, die das erste Tableau ***/
    /*** in das i-te ueberfuehrt. ***/
    erg += copy(S_T_S(S_V_I(res,i)),mat);
    l = 0L;
    for(j=0L;j<S_PA_LI(conpar);j++)
      for(k=0L;k<S_PA_II(conpar,S_PA_LI(conpar)-j-1L);k++)
        {
        erg += copy(S_M_IJ(mat,k,j),S_P_I(pi,l));
        l++;
        }
    /*** Berechne schliesslich das Vorzeichen von pi. ***/
    erg += signum(pi,S_V_I(res,i));
    }

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(pi);
  erg += freeall(conpar);
  erg += freeall(mat);
  erg += freeall(n);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("make_tab_signs : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von make_tab_signs */

/****************************************************************************/
/*                                      */
/*  Name: tab_funk()                            */
/*  Diese Routine berechnet den Wert der Tableaufunktion f"ur ein           */
/*  Standardtableau tab zu einer Partition part von n und gibt ihn in       */
/*  res zurueck. Die Tableaufunktion ist dabei definiert wie in "Substi-    */
/*  tutional Analysis", Kapitel 26, von D.E. Rutherford.          */
/*  Rueckgabewert: OK oder error                                            */
/*                                      */
/****************************************************************************/
/* PF 091092 */

INT tab_funk(n,part,tab,res)
  OP  n;        /* INTEGER-Object                   */
  OP  part;      /* Partition von n                   */
  OP  tab;      /* Standard-Young-Tableau zu part           */
  OP  res;      /* Ende: Wert der Tableaufunktion von tab       */
  {
  OP  eins;      /* INTEGER-Object 1L                 */
  OP  wert;      /* Axialdistanz in tab                 */
  OP  phi;      /* Faktor                       */
  OP  pos;      /* Positionsvektor fuer den Eintrag n in tab     */
  OP  rec_n,      /* Hilfsvariablen fuer die Rekursion         */
    rec_part,
    rec_tab;
  INT  i;
  INT  erg = OK;    /* Variable zum Ablaufcheck             */


  if (not EMPTYP(res)) 
    erg += freeself(res);

  /*** Abbruchbedingung fuer die Rekursion ********************************/

  if(S_I_I(n) == 1L)
    {
    M_I_I(1L,res);
    return erg;
    }

  /*** Falls n>1, wird der Faktor phi berechnet. **************************/

  phi = callocobject();
  pos = callocobject();
  M_I_I(1L,phi);
  erg += get_position(tab,S_I_I(n),pos);
  if(!(S_V_II(pos,0L) == 0L))
    {
    eins = callocobject();
    wert = callocobject();
    M_I_I(1L,eins);
    for(i=0L;i<S_V_II(pos,0L);i++)
      {
      M_I_I(S_V_II(pos,0L)-S_V_II(pos,1L)-i+
            S_PA_II(part,S_PA_LI(part)-i-1L)-1L,wert);
      erg += invers(wert,wert);
      erg += add_apply(eins,wert);
      erg += mult_apply(wert,phi);
      }
    erg += freeall(eins);
    erg += freeall(wert);
    }

  /*** Rekursion **********************************************************/

  rec_tab = callocobject();
  rec_part = callocobject();
  rec_n = callocobject();
  erg += copy(tab,rec_tab);
  erg += copy(part,rec_part);
  erg += copy(n,rec_n);
  erg += dec(rec_n);
  if(S_PA_II(part,S_PA_LI(part)-S_V_II(pos,0L)-1L) == 1L)
    {
    for(i=0L;i<S_PA_LI(part)-1L;i++)
      erg += copy(S_PA_I(rec_part,i+1L),S_PA_I(rec_part,i));
    erg += dec(rec_part);
    }
  else
    erg += dec(S_PA_I(rec_part,S_PA_LI(part)-S_V_II(pos,0L)-1L));
  erg += freeself(S_T_IJ(rec_tab,S_V_II(pos,0L),S_V_II(pos,1L)));
  erg += tab_funk(rec_n,rec_part,rec_tab,res);
  erg += mult_apply(phi,res);

  /*** Speicherplatzfreigabe **********************************************/

  erg += freeall(phi);
  erg += freeall(pos);
  erg += freeall(rec_n);
  erg += freeall(rec_part);
  erg += freeall(rec_tab);

  /*** Rueckkehr in die aufrufende Routine ********************************/

  if (erg != OK)
    {
    error("tab_funk : error during computation.");
    return ERROR;
    }
  return OK;
  } /* Ende von tab_funk */

/****************************************************************************/
/*                                                                          */
/*  Name: trafo_check()                            */
/*  Diese Routine ueberprueft, wie die Anordnung der irreduziblen           */
/*  Darstellungen [part]+ und [part]- , als irreduzible Bestandteile        */
/*  der Darstellung [part] eingeschraenkt auf die An, beschaffen ist,       */
/*  wenn man die darstellenden orthogonalen Matrizen der Sn mit den von     */
/*  B.M. Puttaswamaiah (1963) hergeleiteten Transformationsmatrizen         */
/*  auf Blockgestalt transformiert.                                         */
/*  Rueckgabewert:  0L, falls [part]+ der erste Block ist                   */
/*                  1L, sonst.                                              */
/*                                                                          */
/****************************************************************************/
/* PF 110992 */

INT trafo_check(part)
  OP  part;        /* Partition der Darstellung           */  
  {
  OP  v_sgn;        /* Vorzeichenvektor fuer die Tableaux-Permuta-  */
              /* tionen                     */
  OP  conpar;        /* konjugierte Partition zu part         */
  OP  dim;        /* Dimension der Matrix ueber der Sn       */
  OP  haken;        /* Hakenpartition zu part             */
  OP  ch;          /* Charakterwert von [part]+ auf (haken)+     */
  OP  std;        /* Standardpermutation zu haken         */
  OP  D;          /* Darstellende Matrix von [part](std)       */
  OP  spur;        /* Spur des oberen linken Blockes         */
  OP  zwei;        /* INTEGER-Objekt 2L               */
  OP  eins;        /* INTEGER-Objekt -1L               */
  OP  im;          /* Imaginaere Einheit i             */
  OP  hilf;        /* Hilfsvariable                */
  INT  i;

  INT  make_tab_signs();  /* Routine zur Berechnung des Vorzeichenvektors */
              /* der Tableaupermutationen            */

  /*** Test, ob die Partition part selbstassoziiert ist *******************/

  conpar = callocobject();
  conjugate(part,conpar);
  if(part_comp(part,conpar) != 0L)
    {
    freeall(conpar);
    error("trafo_check : partition is not selfassociated ");
    return 0L;
    }

  /*** Berechnung des Charakterwertes der von [part]+ auf der Konju-    ***/
  /*** giertenklasse der Hakenpartition (h(part))+                 ***/

  haken = callocobject();
  ch = callocobject();
  hilf = callocobject();
  hook_part(part,haken);
  wert(0L,haken,ch);

  /*** Berechnung der Spur des linken oberen Blockes, der entstehen    ***/
  /*** wuerde, wenn man die darstellende Matrix der Standardpermutation ***/
  /*** aus (h(part)) durch die Transformationsmatrix auf Blockgestalt   ***/
  /*** transformieren wuerde.                                    ***/

  v_sgn = callocobject();
  dim = callocobject();
  spur = callocobject();
  std = callocobject();
  D = callocobject();
  zwei = callocobject();
  eins = callocobject();
  im = callocobject();

  make_tab_signs(part,v_sgn);
  M_I_I(S_V_LI(v_sgn),dim);
  std_perm(haken,std);
  
  odg(part,std,D);

  M_I_I(0L,spur);

  /*** Berechnung der Spur im reellen Fall ***/
  if(S_V_II(v_sgn,S_I_I(dim)-1) == 1L)
    for(i=0L;i<(S_I_I(dim))/2L;i++)
      {
      add_apply(S_M_IJ(D,S_I_I(dim)-i-1,S_I_I(dim)-i-1), spur);
      add_apply(S_M_IJ(D,i,i), spur);
      mult(S_V_I(v_sgn,i),S_M_IJ(D,i,S_I_I(dim)-i-1),hilf);
      add_apply(hilf,spur);
      mult(S_V_I(v_sgn,i),S_M_IJ(D,S_I_I(dim)-i-1,i),hilf);
      add_apply(hilf,spur);
      }

  /*** Berechnung der Spur im komplexen Fall ***/
  M_I_I(-1L,eins);
  squareroot(eins,im);
  if(S_V_II(v_sgn,S_I_I(dim)-1) == -1L)
    for(i=0L;i<(S_I_I(dim))/2L;i++)
      {
      add_apply(S_M_IJ(D,S_I_I(dim)-i-1,S_I_I(dim)-i-1), spur);
      add_apply(S_M_IJ(D,i,i), spur);
      mult(S_V_I(v_sgn,i),S_M_IJ(D,i,S_I_I(dim)-i-1),hilf);
      mult_apply(eins,hilf);
      mult_apply(im,hilf);
      add_apply(hilf,spur);
      mult(S_V_I(v_sgn,i),S_M_IJ(D,S_I_I(dim)-i-1,i),hilf);
      mult_apply(im,hilf);
      add_apply(hilf,spur);
      }

  M_I_I(2L,zwei);
  div(spur,zwei,hilf);
  copy(hilf,spur);

  /*** Speicherplatzfreigabe **********************************************/

  freeall(v_sgn);
  freeall(dim);
  freeall(hilf);
  freeall(zwei);
  freeall(eins);
  freeall(im);
  freeall(haken);
  freeall(std);
  freeall(D);
  freeall(conpar);

  /*** Der Vergleich der beiden Werte gibt den gewuenschten Aufschluss  ***/
  /*** ueber die Blockstruktur der tranformierten Matrizen.             ***/

  if(comp(S_N_S(spur),S_N_S(ch)) == 0L)
    {
    freeall(ch);
    freeall(spur);
    return 0L;
    }
  else
    {
    freeall(ch);
    freeall(spur);
    return 1L;
    }

  } /* Ende von trafo_check */

/****************************************************************************/
/*                                                                          */
/* Name: an_odg()               */
/*  Diese Routine berechnet die darstellende unitaere Matrix einer          */
/*  Permutation perm in der Darstellung zu einer Partition part, einge-     */
/*  schraenkt auf die An durch direkte Belegung.                            */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 280992 */ /* PF 130593 */


INT an_odg(part,perm,D)
 OP part;   /* Vektor, der die Darstellung beschreibt:    */
      /*   1. Komponente : Partition         */
      /*   2. Komponente : 0L oder 1L        */
 OP perm;   /* Darzustellende Permutation       */
 OP D;    /* Ende: unitaere Matrix zu [part](perm)    */
 {
 OP conpar;   /* konjugierte Partition zu part      */
 OP  sig;   /* Signum von perm          */
 OP  n;    /* Gewicht von part         */
 OP rz;    /* Zerlegungsvektor von perm in erzeugende Elemente */
      /* der An            */
 OP mat;   /* Vektor der darstellenden Matrizen der erzeugen-  */
      /* den Elemente der An         */
 OP  dim;   /* Dimension von D */

 INT i,l;
 INT erg = OK;  /* Variable zum Ablaufcheck       */
 
 INT an_rz_perm(); /* Routine zur Zerlegung von perm in erzeugende  */
      /* Elemente (12)(r-1,r) der An       */
 INT trafo_check(); /* Routine zum Testen der Anordnung der Bloecke  */
      /* durch die Transformation       */
 INT gen_mat();  /* Routine zur Berechnung der darstellenden Matri- */
      /* zen der erzeugenden Elemente       */

 if (not EMPTYP(D)) 
  erg += freeself(D);

 /*** Test, ob perm in der An liegt **************************************/

 sig = callocobject();
 erg += signum(perm,sig);
 if(S_I_I(sig) == -1L)
  {
  erg += freeall(sig);
  error("an_odg : permutation not in An");
  return erg;
  }

 /*** Test, ob Laenge von perm mit dem Gewicht von part uebereinstimmt ***/

 n = callocobject();
 erg += weight(S_V_I(part,0L),n);
 if(S_I_I(n) != S_P_LI(perm))
  {
  erg += freeall(sig);
  erg += freeall(n);
  error("an_odg : permutation and partition don't agree");
  return erg;
  }

 /*** Falls n = 1 oder n = 2, wird D = (1) zurueckgegeben. ***************/

 if((S_P_LI(perm) == 1L) || (S_P_LI(perm) == 2L))
  {
  erg += m_ilih_m(1L,1L,D);
  M_I_I(1L,S_M_IJ(D,0L,0L));
  erg += freeall(sig);
  erg += freeall(n);
  return erg;
  }

 /*** Berechnung der Matrix **********************************************/

 /*** Falls es sich um die Identitaet handelt, wird die Einheitsmatrix ***/
 /*** ausgegeben.                ***/

 if(einsp(perm))
  {
  dim = callocobject();
  erg += dimension_partition(S_V_I(part,0L),dim);
  erg += m_ilih_nm(S_I_I(dim),S_I_I(dim),D);
  for(i=0;i<S_I_I(dim);i++)
   erg += C_I_I(S_M_IJ(D,i,i),1L);
  return erg;
  }

 /*** Falls die Partition part nicht selbstassoziiert ist, ist die ***/
 /*** darstellende Matrix gleich der Matrix fuer die Sn.           ***/

 conpar = callocobject();
 erg += conjugate(S_V_I(part,0L),conpar);
 if(part_comp(S_V_I(part,0L),conpar) != 0L)
  {
  erg += odg(S_V_I(part,0L),perm,D);
  erg += freeall(sig);
  erg += freeall(conpar);
  erg += freeall(n);
  return erg;
  }

 /*** Falls die Partition part selbstassoziiert ist, werden zu-    ***/
 /*** naechst die darstellenden Matrizen der erzeugenden Elemente  ***/
 /*** berechnet. Dabei wird mit Hilfe einer Testroutine nachge-    ***/
 /*** prueft, welche Standardtableaux zur Belegung herangezogen    ***/
 /*** werden muessen.                                              ***/

 mat = callocobject();
 erg += m_il_v(S_P_LI(perm)-2L,mat);
 if(trafo_check(S_V_I(part,0L)) == S_V_II(part,1L))
  for(i=1L;i<S_P_LI(perm)-1;i++)
   erg += gen_mat(S_V_I(part,0L),i,0L,S_V_I(mat,i-1L));
 else
  for(i=1L;i<S_P_LI(perm)-1;i++)
   erg += gen_mat(S_V_I(part,0L),i,1L,S_V_I(mat,i-1L));

 /*** Dann wird die Permutation perm in die erzeugenden Elemente   ***/
 /*** zerlegt, und die entsprechenden Matrizen miteinander multi-  ***/
 /*** ziert.                                                       ***/

 rz = callocobject();
 erg += an_rz_perm(perm,rz);
 l = S_V_LI(rz);
 erg += copy(S_V_I(mat,S_V_II(rz,l-1L)-1L),D);
 for(i=l-2L;i>=0L;i--)
  erg += mult_apply(S_V_I(mat,S_V_II(rz,i)-1L),D);

 /*** Speicherplatzfreigabe **********************************************/

 erg += freeall(sig);
 erg += freeall(conpar);
 erg += freeall(rz);
 erg += freeall(mat);
 erg += freeall(n);

 /*** Rueckkehr in die aufrufende Routine ********************************/

 if (erg != OK)
  EDC("an_odg");
 return erg;
 } /* Ende von an_odg */

/****************************************************************************/
/****************************************************************************/

/****************************************************************************/
/*                                                                          */
/* Name: an_sdg()               */
/*  Diese Routine berechnet die darstellende seminormale Matrix einer       */
/*  Permutation perm in der Darstellung zu einer Partition part, einge-     */
/*  schraenkt auf die An durch direkte Belegung.                            */
/*  Rueckgabewert: OK oder error.                                           */
/*                                                                          */
/****************************************************************************/
/* PF 280992 */ /* PF 130593 */

INT an_sdg(part,perm,D) OP part,perm,D;
/* PF 1993 */
/* AK 220704 V3.0 */
   /* part Vektor, der die Darstellung beschreibt:    */
   /*   1. Komponente : Partition         */
   /*   2. Komponente : 0L oder 1L        */
   /* perm Darzustellende Permutation       */
   /* D result is seminormale Matrix zu [part](perm)   */
{
    INT erg = OK;
    {
#ifdef DGTRUE 
    OP conpar;   /* konjugierte Partition zu part      */
    OP  sig;   /* Signum von perm          */
    OP  n;    /* Gewicht von part         */
    OP rz;    /* Zerlegungsvektor von perm in erzeugende Elemente */
         /* der An            */
    OP mat;   /* Vektor der darstellenden Matrizen der erzeugen- */
      /* den Elemente der An         */
    OP dim;   /* Dimension von D */

    INT i,l;
 
    INT an_rz_perm(); /* Routine zur Zerlegung von perm in erzeugende  */
      /* Elemente (12)(r-1,r) der An       */
    INT trafo_check(); /* Routine zum Testen der Anordnung der Bloecke  */
      /* durch die Transformation       */
    INT gen_smat();  /* Routine zur Berechnung der darstellenden Matri- */
      /* zen der erzeugenden Elemente       */

    FREESELF(D);

 /*** Test, ob perm in der An liegt **************************************/

    sig = callocobject();
    erg += signum(perm,sig);
    if(S_I_I(sig) == -1L)
     {
     FREEALL(sig);
     erg += error("an_sdg : permutation not in An");
     goto endr_ende;
     }

 /*** Test, ob Laenge von perm mit dem Gewicht von part uebereinstimmt ***/

    n = callocobject();
    erg += weight(S_V_I(part,0L),n);
    if(S_I_I(n) != S_P_LI(perm))
     {
     FREEALL2(sig,n);
     erg += error("an_sdg : permutation and partition don't agree");
     goto endr_ende;
     }

 /*** Falls n = 1 oder n = 2, wird D = (1) zurueckgegeben. ***************/

    if((S_P_LI(perm) == 1L) || (S_P_LI(perm) == 2L))
     {
     erg += m_ilih_m(1L,1L,D);
     M_I_I(1L,S_M_IJ(D,0L,0L));
     FREEALL2(sig,n);
     goto endr_ende;
     }

 /*** Berechnung der Matrix **********************************************/

 /*** Falls es sich um die Identitaet handelt, wird die Einheitsmatrix ***/
 /*** ausgegeben.                ***/

    if(einsp(perm))
     {
     dim = callocobject();
     erg += dimension_partition(S_V_I(part,0L),dim);
     erg += m_lh_nm(dim,dim,D);
     for(i=0;i<S_I_I(dim);i++) C_I_I(S_M_IJ(D,i,i),1);
     FREEALL3(dim,sig,n);
     goto endr_ende;
     }

 /*** Falls die Partition part nicht selbstassoziiert ist, ist die ***/
 /*** darstellende Matrix gleich der Matrix fuer die Sn.           ***/

    conpar = callocobject();
    erg += conjugate(S_V_I(part,0L),conpar);
    if(part_comp(S_V_I(part,0L),conpar) != 0L)
     {
     erg += sdg(S_V_I(part,0L),perm,D);
     FREEALL3(sig,n,conpar);
     goto endr_ende;
     }

    /*** Falls die Partition part selbstassoziiert ist, werden zu-    ***/
    /*** naechst die darstellenden Matrizen der erzeugenden Elemente  ***/
    /*** berechnet. Dabei wird mit Hilfe einer Testroutine nachge-    ***/
    /*** prueft, welche Standardtableaux zur Belegung herangezogen    ***/
    /*** werden muessen.                                              ***/

    mat = callocobject();
    erg += m_il_v(S_P_LI(perm)-2L,mat);
    if(trafo_check(S_V_I(part,0L)) == S_V_II(part,1L))
     for(i=1L;i<S_P_LI(perm)-1;i++)
      erg += gen_smat(S_V_I(part,0L),i,0L,S_V_I(mat,i-1L));
    else
     for(i=1L;i<S_P_LI(perm)-1;i++)
      erg += gen_smat(S_V_I(part,0L),i,1L,S_V_I(mat,i-1L));
   
    /*** Dann wird die Permutation perm in die erzeugenden Elemente   ***/
    /*** zerlegt, und die entsprechenden Matrizen miteinander multi-  ***/
    /*** ziert.                                                       ***/

    rz = callocobject();
    erg += an_rz_perm(perm,rz);
    l = S_V_LI(rz);
    erg += copy(S_V_I(mat,S_V_II(rz,l-1L)-1L),D);
    for(i=l-2L;i>=0L;i--)
     erg += mult_apply(S_V_I(mat,S_V_II(rz,i)-1L),D);

    FREEALL5(sig,conpar,rz,mat,n);
#endif
    }
    ENDR("an_sdg");
}


