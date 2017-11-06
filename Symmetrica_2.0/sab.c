/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Programm zur Berechnung einer symmetrieangepassten Zerlegung        */
/* eines durch eine Matrix gegebenen Operators M.                      */
/* Dieser Operator habe die symmetrien einer endlichen                 */
/* Permutationsgruppe G. Es wird die symmetrieangepasste Basis         */
/* in der Matrix B berechnet und der Basiswechsel durchgefuehrt.       */
/* Nach dem Programmlauf steht in M ein Vektor von Matrizen,           */
/* die die Diagonalbloecke widerspiegeln. Im Vektor vf stehen deren    */
/* Vielfachheiten.                               */
/*                                                                     */
/* Written by: Ralf Hager September 1991                               */
/*                                                                     */
/***********************************************************************/
/***********************************************************************/

#include"def.h"
#include"macro.h"


#define SAB_get_index index_vector /* AK 010393 */
#define war_schon_da(a,b) ((index_vector(a,b) == -1L ) ? 1L : 0L)

INT glm_get_BV();
INT bilde_htupel();
INT werte_Polynom_aus();
INT bestimme_D();
INT glm_sab();
INT _homtest();
INT bestimme_zufallsmatrizen();
INT glm_B_W();
INT reell_gram_schmidt();
INT B_W();
INT vec_mat_mult();
static INT _bdg();
static INT _xdg();
static INT glmn_B_W();
static INT get_poly_self();
static INT copy_V_in_B();
static INT get_vectors();
static INT get_BV();
static INT add_to_PROJ();
static INT    mhochexpo();
static INT TP();
static INT    get_nr_of_tupel();
static INT     lls_vgl();
static INT     ti_eq_tk();
static INT     get_axial_distance();
static INT     ti_eq_transpo_tk();
static INT     get_main_diag();
static INT D_calc();
static INT D_row_calc();
static INT transponiere();
static INT get_T();
static INT get_Q_perm();
static INT get_H_perm();
static INT cut_col_row();
static INT     ziffern_existieren();
static INT Pcut_col_row();
static INT createP();
static INT     lex_vgl();
static INT sortieren();
static INT zuweisen();
static INT _del();
static INT _ins();
static INT _kt();
static INT get_col();
static INT get_row();
static INT Pziffern_existieren();
static INT alpha_beta_tabs();
static INT get_submatrix();
static INT _sab();
/***********************************************************************/
/*                                                                     */
/* Routine:     sab                                                    */
/* Diese Routine ruft zunaechst _sab auf, wo die Basis B berechnet     */
/* wird. Im Unterprogramm B_W wird dann der Basiswechsel durchgefuehrt.*/
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef SABTRUE
INT sab(D_i,D,basis,M,sn_dim) OP      D_i,D,basis,M,sn_dim;
{
    OP      sym_dim;
    INT erg = OK;
    CTO(VECTOR,"sab(2)",D);

    sym_dim = callocobject();

    erg += _sab(D_i,D,basis,sym_dim,sn_dim);
    erg += B_W(basis,M,sym_dim,sn_dim);

    erg += freeall(sym_dim);
    ENDR("sab");
}
#endif /* SABTRUE */


/***********************************************************************/
/*                                                                     */
/* Routine:     _sab                                                   */
/* Die symmetrieangepasste Basis wird berechnet und in B abgespeichert.*/
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef SABTRUE
static INT _sab(D_i,D,basis,sym_dim,sn_dim) OP      D_i, D, basis, sym_dim,  sn_dim;
{
        INT     i;
        INT     j;
        INT     k;
        INT     l;
        INT     s;
        INT     merk    =       0L;

        OP      count   =       callocobject();
        OP      G       =       callocobject();
        OP      N       =       callocobject();
        OP      f_D     =       callocobject();
        OP      irr_dim =       callocobject();
        OP      faktor  =       callocobject();
        OP      dim     =       callocobject();
        OP      PROJ    =       callocobject();
        OP      V;
        OP      X;

        m_i_i(0L,count);
        m_i_i(0L,dim);
        m_i_i(S_V_LI(D),G);
        m_i_i(S_P_LI(S_V_I(D,0L)),f_D);
        m_i_i(S_V_LI(D_i),N);
        m_lh_nm(f_D,f_D,basis);
        m_l_nv(N,sym_dim);
        m_l_nv(N,sn_dim);
        m_lh_nm(f_D,f_D,PROJ);

        for(i=0L;i<S_I_I(N);++i)
        {
                for(l=0;l<S_I_I(f_D);++l)
                        for(s=0;s<S_I_I(f_D);++s)
                                m_i_i(0L,S_M_IJ(PROJ,l,s));

                m_i_i(S_V_LI(S_V_I(S_V_I(D_i,i),0L)),irr_dim);
                for(j=0L;j<S_I_I(G);++j)
                {
                        copy(S_V_I(S_V_I(S_V_I(D_i,i),j),0L),faktor);
                        if(!nullp(faktor)) 
                                add_to_PROJ(PROJ,faktor,S_V_I(D,j));
                }
                copy(count,dim);
                get_BV(PROJ,basis,count);
                sub(count,dim,dim);
                merk+= S_I_I(dim)*S_I_I(irr_dim);
                if(S_I_I(dim) != 0L)
                {
                        V = callocobject();
                        m_i_i(S_I_I(dim),S_V_I(sym_dim,i));
                        m_i_i(S_I_I(irr_dim),S_V_I(sn_dim,i));
                        get_vectors(basis,count,dim,V);
                        copy_V_in_B(V,basis,count,dim);
                        for(k=1L;k<S_I_I(irr_dim);++k)
                        {
                                for(l=0;l<S_I_I(f_D);++l)
                                        for(s=0;s<S_I_I(f_D);++s)
                                                m_i_i(0L,S_M_IJ(PROJ,l,s));
                                for(j=0L;j<S_I_I(G);++j)
                                {       
                                        copy(S_V_I(S_V_I(S_V_I(D_i,i),j),k),
                                             faktor);
                                        if(!nullp(faktor)) 
                                        {
                                                add_to_PROJ(PROJ,
                                                            faktor,
                                                            S_V_I(D,j));
                                        }
                                }
                                copy(G,faktor);
                                div(irr_dim,faktor,faktor);
                                mult_apply(faktor,PROJ); /* AK 020692 statt mult */
                                
                                X = callocobject();
                                mult(PROJ,V,X);
                                m_i_i(S_I_I(count)+S_I_I(dim),count);
                                copy_V_in_B(X,basis,count,dim);
                                freeall(X);
                        }
                        freeall(V);
                }
        }
        freeall(count); 
    freeall(dim); 
    freeall(G); 
    freeall(N);
        freeall(f_D); 
    freeall(irr_dim); 
    freeall(faktor); 
    freeall(PROJ);
    return OK;
}
#endif /* SABTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     add_to_PROJ                                            */
/* Zur Projektormatrix PROJ wird d_1i(pi^-1)D(pi) dazuaddiert.         */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT add_to_PROJ(PROJ,d,D) OP      PROJ, d, D;
{
        INT     i;

        for(i=0L;i<S_P_LI(D);++i)
                add_apply( d, S_M_IJ(PROJ,S_P_II(D,i)-1L,i));
    return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:     get_BV                                                 */
/* Aus der Projektormatrix PROJ werden die linear unabhaengigen        */
/* Vektoren durch ein Gaussverfahren herausgesucht.                    */
/* In count wird deren Anzahl abgespeichert. Sie werden in B           */
/* uebertragen.                                                        */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT get_BV(PROJ,basis,count) OP      PROJ; OP      basis; OP      count;
{
        INT     i;
        INT     j;
        INT     k;
        INT     l;
        INT     s;
        INT     f_D;

        OP      Proj    =       callocobject();
        OP      val     =       callocobject();
        OP      faktor  =       callocobject();

        copy(PROJ,Proj);
        f_D = S_M_LI(basis);
        k = 0L;
        for(i=0L;i<f_D;++i)
        {
                for(j=k;j<f_D;++j)
                {
                        if(!nullp(S_M_IJ(Proj,j,i)))
                        {
                        for(l=0L;l<f_D;++l)
                                copy(S_M_IJ(PROJ,l,i),
                                     S_M_IJ(basis,l,S_I_I(count)));
                                m_i_i(S_I_I(count)+1L,count);
                                if(j != k)
                                        for(l=0L;l<f_D;++l)
                                                swap(S_M_IJ(Proj,k,l),
                                                     S_M_IJ(Proj,j,l));
                                for(l=k+1L;l<f_D;++l)
                                        if(!nullp(S_M_IJ(Proj,l,i)))
                                        {
                                                div(S_M_IJ(Proj,l,i),
                                                    S_M_IJ(Proj,k,i),
                                                    faktor);
                                                for(s=i;s<f_D;++s)
                                                {
                                                        mult(faktor,
                                                             S_M_IJ(Proj,k,s),
                                                             val);
                                                        sub(S_M_IJ(Proj,l,s),
                                                            val,
                                                            S_M_IJ(Proj,l,s));
                                                }
                                        }
                        }
                }
                k++;
        }

        freeall(Proj);
        freeall(val);
        freeall(faktor);
    return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   get_vectors                                              */  
/* Holt aus basis dim Vektoren und speichert sie in V ab.              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef MATRIXTRUE
static INT get_vectors(basis,count,dim,V) OP      basis, count, dim, V;
{
        INT     i;
        INT     j;

        m_lh_nm(dim,S_M_L(basis),V);

        for(i=0L;i<S_M_LI(basis);++i)
                for(j=0L;j<S_I_I(dim);++j)
                        copy(S_M_IJ(basis,i,S_I_I(count)-S_I_I(dim)+j),
                             S_M_IJ(V,i,j));

    return OK;
}
#endif /* MATRIXTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:   copy_V_in_B                                              */
/* V wird auf basis kopiert an die Stelle count -dim bis count-1L      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT copy_V_in_B(V,basis,count,dim) OP      V,basis,count,dim;
{
    INT     i;
    INT     j;

    for(i=0L;i<S_M_HI(V);++i)
        for(j=0L;j<S_M_LI(V);++j)
            copy(S_M_IJ(V,i,j),
                 S_M_IJ(basis,i,S_I_I(count)-S_I_I(dim)+j));
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   gram_schmidt                                             */
/* Nach dem Gram-Schmidtschen-Orthonormalisierungsverfahren wird eine  */
/* Matrix, bestehend aus l.u. Vektoren orthonormalisiert.              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef MATRIXTRUE
INT gram_schmidt(a) OP      a;
{
        INT     i;
        INT     j;
        INT     k;

        OP      r       =       callocobject();
        OP      h       =       callocobject();
        OP      n       =       callocobject();
        OP      p       =       callocobject();
        OP      s       =       callocobject();

        m_lh_nm(S_M_H(a),S_M_L(a),r);
        m_i_i(S_M_HI(a),n);
        m_i_i(S_M_LI(a),p);

        for(k=0L;k<S_I_I(p);++k)
        {
                for(j=0L;j<k;++j)
                {
                        m_i_i(0L,S_M_IJ(r,j,k));
                        for(i=0L;i<S_I_I(n);++i)
                        {
                                mult(S_M_IJ(a,i,j),S_M_IJ(a,i,k),h);
                                add_apply(h,S_M_IJ(r,j,k));
                        }
                        for(i=0L;i<S_I_I(n);++i)
                        {
                                mult(S_M_IJ(r,j,k),S_M_IJ(a,i,j),h);
                                sub(S_M_IJ(a,i,k),h,S_M_IJ(a,i,k));
                        }
                }
                m_i_i(0L,s);
                for(i=0L;i<S_I_I(n);++i)
                {
                        complex_conjugate(S_M_IJ(a,i,k),h);
                        mult_apply(S_M_IJ(a,i,k),h); /* AK 020692 statt mult */
                        add_apply(h,s); /* AK 010692 statt add */
                }
                squareroot(s,S_M_IJ(r,k,k));
                for(i=0L;i<S_I_I(n);++i)
                        div(S_M_IJ(a,i,k),S_M_IJ(r,k,k),S_M_IJ(a,i,k));
        }

        freeall(r);
        freeall(h);
        freeall(n);
        freeall(p);
        freeall(s);
    return OK;
}
#endif /* MATRIXTRUE */



/***********************************************************************/
/*                                                                     */
/* Routine:   group_gen                                                */
/* Ausgehend von einem Erzeugendensystem S von Permutationen           */
/* wir die Gruppe G erzeugt und in D abgespeichert. In SMat sind die   */
/* darstellenden irreduziblen Matrizen abgespeichert. Mit ihnen        */
/* werden die irreduziblen Matrixdarstellungen saemtlicher             */
/* Gruppenelemente erzeugt  und in Di abgespeichert.                   */
/* Der Algorithmus ist eine vereinfachte Version des Dimino-Algorithmus*/
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT group_gen(S,SMat,D,Di) OP      S,SMat,D,Di;
{
        INT     i;
        INT     j;
        INT     k;

        OP      irr_dim         =       callocobject();
        OP      hperm           =       callocobject();
        OP      hvek            =       callocobject();
        OP      besucht         =       callocobject();

        m_il_v(S_V_LI(S)+1L,D);
        m_il_nv(S_P_LI(S_V_I(S,0L)),S_V_I(D,0L));
        first_permutation(S_P_L(S_V_I(S,0L)),S_V_I(D,0L));
        for(i=1L;i<S_V_LI(D);++i)       
        copy(S_V_I(S,i-1L),S_V_I(D,i));
        m_l_v(S_V_L(SMat),Di);
        for(i=0L;i<S_V_LI(SMat);++i)
        {
                m_il_v(S_V_LI(S_V_I(SMat,i))+1L,S_V_I(Di,i));
                m_i_i(S_M_LI(S_V_I(S_V_I(SMat,i),0L)),irr_dim);
                m_l_nv(irr_dim,S_V_I(S_V_I(Di,i),0L));
                m_i_i(1L,S_V_I(S_V_I(S_V_I(Di,i),0L),0L));
                for(j=1L;j<S_V_LI(S_V_I(Di,i));++j)
                {
                        m_i_i(S_M_LI(S_V_I(S_V_I(SMat,i),0L)),irr_dim);
                        m_l_v(irr_dim,S_V_I(S_V_I(Di,i),j));
                        for(k=0L;k<S_I_I(irr_dim);++k)
                                copy(S_M_IJ(S_V_I(S_V_I(SMat,i),j-1L),0L,k),
                                     S_V_I(S_V_I(S_V_I(Di,i),j),k));
                }                               
        }

        for(i=0L;i<S_V_LI(D);++i)
        {
                for(j=0L;j<S_V_LI(S);++j)
                {
                        mult(S_V_I(D,i),S_V_I(S,j),hperm);
                        if(war_schon_da(hperm,D) != 0L)
                        {
                                inc(D);
                                copy(hperm,S_V_I(D,S_V_LI(D)-1L));
                                for(k=0L;k<S_V_LI(Di);++k)
                                {
                                        inc(S_V_I(Di,k));
                                        m_l_nv(S_M_L(S_V_I(S_V_I(SMat,k),0L)),
                                               hvek);
                                        vec_mat_mult(S_V_I(S_V_I(Di,k),i),
                                                     S_V_I(S_V_I(SMat,k),j),
                             hvek);
                                        copy(hvek,
                                             S_V_I(S_V_I(Di,k),
                                                   S_V_LI(S_V_I(Di,k))-1L));
                                }
                        }
                }
        }

        m_l_nv(S_V_L(D),besucht);
        for(i=0L;i<S_V_LI(D);++i)
        {
                m_i_i(1L,S_V_I(besucht,i));
                invers(S_V_I(D,i),hperm);
                k = SAB_get_index(hperm,D);
                if(k>=0L && k != i && S_V_II(besucht,k) == 0L)
                {
                        m_i_i(1L,S_V_I(besucht,k));
                        for(j=0L;j<S_V_LI(Di);++j)
                                swap(S_V_I(S_V_I(Di,j),i),
                                     S_V_I(S_V_I(Di,j),k));
                }
        }

        freeall(irr_dim);
        freeall(hperm);
        freeall(hvek);
        freeall(besucht);
    return OK;
}

#ifdef UNDEF
/***********************************************************************/
/*                                                                     */
/* Routine:   SAB_get_index                                            */
/* Hilfsroutine bei der Konstruktion der Gruppe.                       */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     SAB_get_index(hperm,D) OP      hperm; OP      D;
{
        INT     i;

        for(i=0L;i< S_V_LI(D);++i)
                if(comp(hperm,S_V_I(D,i)) == 0) return(i);
        return(-1);
}
#endif /* UNDEF */

/***********************************************************************/
/*                                                                     */
/* Routine:   vec_mat_mult                                             */
/* Hilfsroutine bei der Konstruktion der Gruppe.                       */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT vec_mat_mult(vec,mat,hvek) OP      vec,mat,hvek;
{
        INT     i;
        INT     j;

        OP      z       =       callocobject();

        for(i=0L;i<S_V_LI(vec);++i)
        {
                for(j=0L;j<S_V_LI(vec);++j)
                {
                        mult(s_v_i(vec,j),S_M_IJ(mat,j,i),z);
                        add_apply(z,S_V_I(hvek,i)); /* AK 010692 statt add */
                }
        }

        freeall(z);
    return OK;
}

#ifdef UNDEF
/***********************************************************************/
/*                                                                     */
/* Routine:   war_schon_da                                             */
/* Hilfsroutine bei der Konstruktion der Gruppe.                       */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

war_schon_da(hperm,D) OP      hperm,D;
{
        INT     i;

        for(i=0L;i< S_V_LI(D);++i)
                if(comp(hperm,S_V_I(D,i)) == 0) return(0L);
        return(1);
}
#endif

/***********************************************************************/
/*                                                                     */
/* Routine:   B_W                                                      */
/* Der Basiswechsel von M wird durchgefuerht. Dazu wird zunaechst die  */
/* Inverse Matrix basis^-1 von basis bestimmt. Anschliessend wird die          */
/* Matrixmultiplikation durchgefuehrt, unter Beruecksichtigung         */
/* der Vielfachheiten der vorkommenden Darstellungen.                  */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
#ifdef SABTRUE
INT B_W(basis,M,sym_dim,sn_dim) OP      M,basis,sym_dim,sn_dim;
{
        INT     i,j,k,l,s;

        OP      B_1     =       callocobject();
        OP      erg     =     callocobject();
        OP      mneu     =     callocobject();
        OP      count   =       callocobject();
    OP    Mneu    =    callocobject();
    OP    r    =    callocobject();
    OP    vf    =    callocobject();

        invers(basis,B_1);

        m_i_i(0L,count);
        for(s=0L;s<S_V_LI(sym_dim);++s)
                if(S_V_II(sym_dim,s) != 0L)
            inc(count);
    m_l_v(count,vf);
        m_i_i(0L,count);
        for(s=0L;s<S_V_LI(sym_dim);++s)
                if(S_V_II(sym_dim,s) != 0L)
        {
            copy(S_V_I(sn_dim,s),S_V_I(vf,S_I_I(count)));
            inc(count);
        }
    m_l_v(count,Mneu);
        m_i_i(0L,count);
    for(i=0L;i<S_V_LI(sym_dim);++i)
                if(S_V_II(sym_dim,i) != 0L)
        {
            m_lh_m(S_V_I(sym_dim,i),S_V_I(sym_dim,i),S_V_I(Mneu,S_I_I(count)));
            inc(count);
        }
        m_i_i(0L,count);
        m_i_i(0L,r);
        for(s=0L;s<S_V_LI(sym_dim);++s)
        {
                if(S_V_II(sym_dim,s) != 0L)
                {
                        for(i=S_I_I(count);
                            i<S_I_I(count)+S_V_II(sym_dim,s);
                            ++i)
                        {
                                for(j=S_I_I(count);
                                    j<S_I_I(count)+S_V_II(sym_dim,s);
                                    ++j)
                                {
                                        m_i_i(0L,mneu);
                                        for(k=0;k<S_M_LI(basis);++k)
                                        {
                                                for(l=0L;l<S_M_LI(basis);++l)
                                                {
                                                if(!nullp(S_M_IJ(B_1,i,k)) && 
                                                   !nullp(S_M_IJ(basis,l,j)) && 
                                                   !nullp(S_M_IJ(M,k,l)))
                                                   {

                                                   mult(S_M_IJ(B_1,i,k),
                                                        S_M_IJ(basis,l,j),
                                                        erg);
                                                   mult(erg,
                                                        S_M_IJ(M,k,l),
                                                        erg);
                           add_apply(erg,mneu);
                                                   }
                                                }
                                        }
                    copy(mneu,S_M_IJ(S_V_I(Mneu,S_I_I(r)),i-S_I_I(count),j-S_I_I(count)));
                                }
                        }
            inc(r);
                }
                mult(S_V_I(sym_dim,s),S_V_I(sn_dim,s),erg);
        add_apply(erg,count);
        }
    copy(Mneu,M);
    copy(vf,sn_dim);


    freeall(B_1);
    freeall(count);
    freeall(erg);
    freeall(mneu);
    freeall(Mneu);
    freeall(r);
    freeall(vf);
    return OK;
}
#endif /* SABTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:   sab_input                                                    */
/* Von der standardeingabe werden folgende Strukturen eingelesen:      */
/* --------------------------------------------------------------      */
/* Anzahl der Erzeuger von G          |       orderS                   */
/* Erzeuger von G                     |       S                        */
/* Anzahl irred. Darstellungen        |       anz_irr                  */
/* Darstellende Matrizen fuer diese   |       SMat                     */
/* Zu zerlegender Operator M          |       M                        */
/* --------------------------------------------------------------      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT sab_input(S,SMat,M) OP      S; OP      SMat; OP      M;
{
    INT     i;
    INT     j;

    OP      orderS  =       callocobject();
    OP      anz_irr =       callocobject();

        scan(INTEGER,orderS);
        m_l_v(orderS,S);
        for(i=0L;i<S_I_I(orderS);++i)
                scan(PERMUTATION,S_V_I(S,i));
        scan(INTEGER,anz_irr);

        m_l_v(anz_irr,SMat);
        for(i=0L;i<S_I_I(anz_irr);++i)
        {
                m_l_v(orderS,S_V_I(SMat,i));
                for(j=0;j<S_I_I(orderS);++j)
                        scan(MATRIX,S_V_I(S_V_I(SMat,i),j));
        }
        scan(MATRIX,M);

        freeall(orderS);
        freeall(anz_irr);
    return OK;
}

/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Programm zur Berechnung  der natuerlichen Matrixdarstellung von S_n */
/*                                                                     */
/* Written by: Ralf Hager September 1991                               */
/*                                                                     */
/***********************************************************************/
/***********************************************************************/


/***********************************************************************/
/*                                                                     */
/* Routine:     bdg                                                    */
/* Gibt zu gegebener Partition part und Permutation perm die           */
/* zugehoerige irreduzible Matrixdarstellung in D zurueck.             */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT bdg(part,perm,D) OP      part; OP      perm; OP      D;
{
    INT     i,j;
    OP t,P,_D;
    INT erg = OK;

    CTO(PARTITION,"bdg(1)",part);
    CTO(PERMUTATION,"bdg(2)",perm);
    CE3(part,perm,D,bdg);

    t  = CALLOCOBJECT();
    P  = CALLOCOBJECT();
    _D = CALLOCOBJECT();

    _bdg(part,perm,_D,t,P,-1L);          
         /* Matrix _D wird als Vektor von Vektoren berechnet. 
            Es ist auch der Aufruf mit var ungleich -1L erlaubt,
            dann wird die var-te Zeile der darstellenden Matrix
            berechnet. */

    erg += m_ilih_m(S_V_LI(_D),S_V_LI(_D),D);   
         /* Der Vektor von Vektoren wird auf eine Matrix kopiert. */

    for(i=0L;i<S_V_LI(_D);++i)
        for(j=0L;j<S_M_LI(_D);++j)
            COPY(S_V_I(S_V_I(_D,i),j),
                S_M_IJ(D,i,j));

    FREEALL3(t,P,_D);
    ENDR("bdg");
}



/***********************************************************************/
/*                                                                     */
/* Routine:     _bdg                                                   */
/* Gibt zu gegebener Partition part und Permutation perm die           */
/* zugehoerige irreduzible Matrixdarstellung in D zurueck.             */
/* (D ist aber Vektor von Vektoren.)                                   */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT _bdg(part,perm,D,t,P,var) OP  part,perm,D,t,P; INT     var;
{
        INT     i;
        INT     j;
    INT    lex_vgl();

        OP p_inv     = callocobject();   /* inverse Permutatione perm        */
        OP tpart     = callocobject();   /* transponierte Partition von part */
        OP beta      = callocobject();   /* Inhalt der Tableaux              */
        OP Tt        = callocobject();   /* Tableau mit transponiertem Umriss*/

        if(emptyp(t))
        {
                m_il_v(S_P_LI(perm),beta);
                for(i=0L;i<S_V_LI(beta);++i) 
                        m_i_i(1L,S_V_I(beta,i));
             /* Konstruktion der standardtableaux */
                alpha_beta_tabs(part,beta,t);        
             /* Lex. aufst. Sortieren der Tabs    */
                sortieren(0L,S_V_LI(t)-1L,t,lex_vgl);     
             /* Struktur der Horizontal-
                permutationen wird gebildet       */
                createP(P,S_P_L(perm),part,t);       
        }
        conjugate(part,tpart);
        m_il_v(S_PA_LI(tpart),Tt);
        for(i=S_PA_LI(tpart)-1L;i>=0L;--i) 
                m_il_v(S_PA_II(tpart,i),
                       S_V_I(Tt,S_PA_LI(tpart)-1L-i));

        invers(perm,p_inv); invers(perm,perm);
        m_il_v(S_V_LI(t),D);
        if(var == -1L) /* Gesamte Matrix berechnen */
        {
                for(i=0;i<S_V_LI(t);++i) 
                {
                        m_il_v(S_V_LI(t),S_V_I(D,i));
                        for(j=0L;j<S_V_LI(D);++j)
                             m_i_i(0L,S_V_I(S_V_I(D,i),j));
            /* Die i-te Zeile der darstellenden Matrix wird 
               bestimmt */
                        D_calc(t,S_V_I(D,i),P,perm,p_inv,1L,i,i,i,Tt); 
                }
        }
        else  /*  NUR die var-te Zeile berechnen */
        {
                if(var < S_V_LI(D) && var >= 0L)
                {
                        for(j=0L;j<S_V_LI(D);++j)m_i_i(0L,S_V_I(D,j));
                        D_calc(t,D,P,perm,p_inv,1L,var,var,var,Tt);
                }
                else    return error("wrong linenr. !!!\n");
        }
        invers(perm,perm);

        freeall(p_inv);
        freeall(tpart);
        freeall(Tt);
        freeall(beta);
    return OK;
}
#endif /* DGTRUE */
/***********************************************************************/
/*                                                                     */
/* Routine:     alpha_beta_tabs                                        */
/* Programm zur Berechnung der Standardtableaux mit vorgegebenem       */
/* Umriss alpha und Inhalt beta.                                       */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef TABLEAUXTRUE
static INT alpha_beta_tabs(alpha,beta,t)           OP  alpha,beta,t;
{
    OP      n       = callocobject();
    OP      h       = callocobject();
    OP      ou      = callocobject();
    OP      um      = callocobject();
    OP      tou     = callocobject();
    OP      ziel    = callocobject();
    OP      dim     = callocobject();
    OP      tab     = callocobject();

    INT     i;
    INT     j;
    INT     ct = 0L;

/*
    kostka_zahl(alpha,beta,dim); 
*/
    kostka_number(beta,alpha,dim); 
    m_l_v(dim,t);
    conjugate(alpha,h);


    m_il_v(S_PA_LI(alpha)+1L,ou);
    m_il_v(S_PA_LI(h)+1L,tou);
    m_il_v(S_PA_LI(h)+1L,ziel);


    for(i=1L;i<=S_PA_LI(alpha);++i)
            m_i_i(S_PA_II(alpha,S_PA_LI(alpha)-i),S_V_I(ou,i));

    for(i=1L;i<=S_PA_LI(h);++i)
            m_i_i(S_PA_II(h,S_PA_LI(h)-i),S_V_I(tou,i));

    m_il_v(S_V_LI(tou),tab);
    for(i=1L;i<S_V_LI(tou);++i)
            m_il_v(S_V_II(tou,i)+1L,S_V_I(tab,i));

    for(i=1L;i<S_V_LI(tou);++i)
            for(j=0L;j<=S_V_II(tou,i);++j)
                    m_i_i(0L,S_V_I(S_V_I(tab,i),j));

    for(i=0L;i<S_I_I(dim);++i)
            {
            m_il_v(S_V_LI(ou)-1L,S_V_I(t,i));
            for(j=0L;j<S_V_LI(ou)-1L;++j)
                    m_il_v(S_V_II(ou,j+1L),S_V_I(S_V_I(t,i),j));
            }
    copy(tou,um);
    for(i=1L;i<S_V_LI(tou);++i)
            m_i_i(S_V_II(um,1L)+i-1L-S_V_II(um,i),S_V_I(ziel,i));
    m_i_i(-1L,S_V_I(um,0L));
    for(i=0L;i<S_V_LI(um)-1L;++i)
            m_i_i(S_V_II(um,1L)+i,S_V_I(um,i+1L));

    m_i_i(0L,n);
    m_i_i(0L,S_V_I(ziel,0L));
    m_i_i(0L,S_V_I(ou,0L));
    m_i_i(0L,S_V_I(tou,0L));

    for(i=0L;i<S_V_LI(tou);++i) 
    add_apply(S_V_I(tou,i),n); /* AK 010692 statt add */

/* Rekursive Konstruktionsroutine */

    _kt(n,t,tab,um,ziel,ou,tou,0L,0L,1L,&ct,
        beta,S_V_II(beta,0L));


    freeall(ou);
    freeall(um);
    freeall(tou);
    freeall(ziel);
    freeall(h);
    freeall(n);
    freeall(dim);
    freeall(tab);
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     _kt                                                    */
/* Rekursive Konstruktionsroutine zur Berechnung der                   */
/* Standardtableaux mit vorgegebenem                                   */
/* Umriss alpha und Inhalt beta.                                       */
/* Zum Algorithmus  siehe [KO07], (S.8)                                */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT _kt(n,t,tab,um,ziel,ou,tou,k,i,st,ct,beta,nr)
    OP      n; OP      t; OP      tab; OP      um; OP      ziel;
    OP      ou; OP      tou; INT     k; INT     i; INT     st;
    INT     *ct; OP      beta; INT     nr;
{
        INT             l;

        if(i==nr)     
                {
                if(st==S_V_LI(beta))
                        {
                        zuweisen(t,tab,ou,*ct); 
                        (*ct)++;
                        }
                else    _kt(n,t,tab,um,ziel,ou,tou,0L,0L,st+1L,ct,
                            beta,S_V_II(beta,st));
                }
        else 
                for(l=k+1L;l<=S_V_II(ou,1L);++l)
                {
                        if(((S_V_II(um,l)-1L) > (S_V_II(um,l-1L)))&&
                           (S_V_II(um,l) > S_V_II(ziel,l)))
                        {
                                m_i_i(S_V_II(um,l)-1L,S_V_I(um,l));
                                _ins(S_V_I(tab,l),st);
                                _kt(n,t,tab,um,ziel,ou,tou,l,i+1L,st,ct,
                                    beta,nr);
                                _del(S_V_I(tab,l));
                                m_i_i(S_V_II(um,l)+1L,S_V_I(um,l));
                        }
                }
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     _ins                                                   */
/* Hilfsroutine bei der Tableauberechnung                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT _ins(line,z) OP     line; INT    z;
{
        INT     i;

        for(i=1L;i<S_V_LI(line);++i)
                if(S_V_II(line,i)==0L)
                        {
                        m_i_i(z,S_V_I(line,i));
                        break;
                        }
    return OK;
}
/***********************************************************************/
/*                                                                     */
/* Routine:     _del                                                   */
/* Hilfsroutine bei der Tableauberechnung                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT _del(line) OP      line;
{
    INT     i;

    for(i=S_V_LI(line)-1L;i>=1L;--i)
        if(S_V_II(line,i)!=0L)
            {
            m_i_i(0L,S_V_I(line,i));
            break;
            }
    return OK;
}
/***********************************************************************/
/*                                                                     */
/* Routine:     _zuweisen                                              */
/* Hilfsroutine bei der Tableauberechnung                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT zuweisen(t,tab,ou,ind)
    OP      t; OP      tab; OP      ou; INT     ind;
{
        INT     i;
        INT     j;

        for(i=0;i<S_V_LI(ou)-1L;++i)
                for(j=0;j<S_V_II(ou,i+1L);++j)
                        m_i_i(S_V_II(S_V_I(tab,j+1L),i+1L),
                              S_V_I(S_V_I(S_V_I(t,ind),i),j));
    return OK;
}
#endif /* TABLEAUXTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     _sortieren                                             */
/* Sortiert einen Vektor t von Strukturen bei gegebener                */
/* Vergleichsfunktion _vgl nach dem Algorithmus QUICKSORT              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT sortieren(anf,end,t,_vgl)           
    INT     anf; INT     end; OP      t; INT    (*_vgl)();
{
        INT     laenge;
        INT     ind;
        INT     i;
        INT     l;
        INT     r;
        OP      mitte = callocobject();


        laenge = end - anf + 1L;

        if(laenge >= 2L)
                {
                copy(S_V_I(t,anf),mitte);
                ind     = -1L;
                i = anf + 1L;

                while((i<=end)&&(ind == -1L))
                {
                if((*_vgl)(mitte,S_V_I(t,i)) == -1L) ind = i;
                else
                {
                        if((*_vgl)(mitte,S_V_I(t,i)) == 1L) ind = anf;
                        else    ++i;
                }
                if(ind > -1L)
                        {
                        l = anf;
                        r = end;
                        copy(S_V_I(t,ind),mitte);
                        do
                                {
                                swap(S_V_I(t,l),S_V_I(t,r));
                                while((*_vgl)(S_V_I(t,l),mitte) == -1L) 
                                        ++l;
                                while((*_vgl)(S_V_I(t,r),mitte) >=  0L) 
                                        --r;
                                }
                        while(l <= r);
                        sortieren(anf,l-1L,t,_vgl);
                        sortieren(l,end,t,_vgl);
                        }
                }
                }
    freeall(mitte); /* AK 010692 */
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     lex_vgl                                                */
/* lexikographisch aufsteigender Vergleich  zweier Operanden           */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT     lex_vgl(a,b) OP      a; OP      b;
{
        INT     i;
        INT     j;

        for(i=0L;i<S_V_LI(a);++i)
        {
                for(j=0L;j<S_V_LI(S_V_I(a,i));++j)
                        if(S_V_II(S_V_I(a,i),j) != S_V_II(S_V_I(b,i),j))
                        {
                                if(S_V_II(S_V_I(a,i),j) > S_V_II(S_V_I(b,i),j))
                                {
                                        return(1L);
                                }
                                if(S_V_II(S_V_I(a,i),j) < S_V_II(S_V_I(b,i),j))
                                {
                                        return(-1L);
                                }
                        }
        }
        return(0L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     createP                                                */
/* Erstellen der Stuktur P aus Horizontalpermutationen                 */
/* nach dem depth-first-search-Verfahren                               */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT createP(P,n,part,t)     
        /* Die Struktur P, bestehend aus Horizontalpermutationen
           wird gebildet. */
    OP      P; OP      n; OP      part; OP      t;
{
        OP      HP;
        OP      neu;
        OP      v     = callocobject();
        OP      tpart = callocobject();

        INT     i;
        INT     j;

        m_il_v(S_V_LI(t),P);
        m_il_v(20L,v);
        conjugate(part,tpart);

        for(i=0L;i<S_V_LI(t);++i)
        {
                for(j=i+1L;j<S_V_LI(t);++j)
                {
                        if( Pziffern_existieren(
                            S_V_I(t,i),S_V_I(t,j),v,tpart) == 0L)
                        {
                        HP = S_V_I(P,i);
                        if (emptyp(HP)) m_il_v(1L,HP);
                        else inc(HP);
                        neu = S_V_I(HP,S_V_LI(HP)-1L);
                        m_il_v(2L,neu);
                        m_i_i(j,S_V_I(neu,0L));
                        b_ks_p(VECTOR,callocobject(),S_V_I(neu,1L));
                        m_il_v(S_I_I(n),S_P_S(S_V_I(neu,1L)));
                        get_H_perm(S_V_I(t,i),S_V_I(t,j),S_V_I(neu,1L));
                        }
                }
        }
        freeall(v);
        freeall(tpart);
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     Pziffern_existieren                                    */
/* Prueft, ob in zwei Tableaux zwei Ziffern gemeinsam in einer         */
/* Zeile und Spalte vorkommen                                          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT     Pziffern_existieren(t_i,t_j,v,tpart) OP t_i,t_j,v,tpart;
{
        static INT      i;
        static INT      j;
        static INT      k;
        static INT      tl;
        static OP zt_i,zv;

        for(i=0L,tl=S_PA_LI(tpart)-1L;i<S_V_LI(S_V_I(t_i,0L));++i,tl--)
        {
                if(i < S_V_LI(S_V_I(t_i,1L)))
                {
                        for(j=0L;j<S_V_LI(t_i);++j)
                        {
                                for(k=0,zv=S_V_S(v),zt_i=S_V_S(t_i);
                                    k<S_PA_II(tpart,tl);
                                    ++k,zt_i++,zv++)
                                        m_i_i(S_V_II(zt_i,i),zv);
                                        if(Pcut_col_row(
                                           v,S_PA_II(tpart,tl) ,
                                           S_V_I(t_j,j)) >= 2L)
                                        return(1L);
                        }
                }
                else    return(0L);
        }
        return(0L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     Pcut_col_row                                           */
/* Bildet den Schnitt einer Zeile und einer Spalte zweier Tabelaux.    */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT Pcut_col_row(col,l_col,row) 
        OP      col; INT     l_col; OP      row;
{
        static INT      erg;
        static INT      i;
        static INT      j;
        static OP       zi,zj;

        erg = 0L;
        for(i=0L,zi = S_V_S(col);i<l_col;++i,zi++)
                for(j=0L,zj = S_V_S(row);j<S_V_LI(row);++j,zj++)
                        if(S_I_I(zi) == S_I_I(zj))      
                                {
                                erg++;
                                if(erg>1L) return(erg);
                                }
        return(erg);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     ziffern_existieren (Variante mit transponiertem Tabl.) */
/* Prueft, ob in zwei Tableaux zwei Ziffern gemeinsam in einer         */
/* Zeile und Spalte vorkommen                                          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     ziffern_existieren(Tt,t_j) OP      Tt; OP      t_j;
{
        static INT      i;
        static INT      j;

        for(i=0L;i<S_V_LI(Tt);++i)
                for(j=0L;j<S_V_LI(t_j);++j)
                        if(S_V_LI(S_V_I(Tt,i))>0L)
                        {
                                if(cut_col_row(
                                   S_V_I(Tt,i),
                                   S_V_I(t_j,j)) >= 2L)
                                        return(1L);
                        }
                        else    return(0L);
        return(0L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     cut_col_row    (Variante mit transponiertem Tabl.)     */
/* Bildet den Schnitt einer Zeile und einer Spalte zweier Tabelaux.    */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT cut_col_row(col,row) OP      col; OP      row;
{
        static INT      erg;
        static INT      i;
        static INT      j;
        static OP       zi,zj;

        erg = 0L;
        for(i=0L,zi = S_V_S(col);i<S_V_LI(col);++i,zi++)
                for(j=0L,zj = S_V_S(row);j<S_V_LI(row);++j,zj++)
                        if(S_I_I(zi) == S_I_I(zj))      
                        {
                                erg++;
                                if(erg>1L)      return(erg);
                        }
        return(erg);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     get_H_perm                                             */
/* Gibt die Horizontalpermutation zwischen zwei Tableaux zurueck.      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT get_H_perm(t_i,t_j,perm) OP      t_i; OP      t_j; OP      perm;
{
    INT     i;
    INT     j;

    INT     sp;

    for(i=0L;i<S_V_LI(t_i);++i)
        {
        for(j=0L;j<S_V_LI(S_V_I(t_i,i));++j)
            {
            sp = get_col(t_i,S_V_II(S_V_I(t_j,i),j));
            m_i_i(S_V_II(S_V_I(t_j,i),j),
                  S_P_I(perm,S_V_II(S_V_I(t_j,i),sp)-1L));
            }
    }
    return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:     get_H_perm                                             */
/* Gibt die Vertikalpermutation zwischen zwei Tableaux zurueck.        */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT get_Q_perm(T,t_i,perm) OP      T,t_i,perm;
{
        INT     i;
        INT     j;
        INT     row;

        for(i=0L;i<S_V_LI(t_i);++i)
        {
                for(j=0L;j<S_V_LI(S_V_I(t_i,i));++j)
                {
                        row = get_row(t_i,S_V_II(S_V_I(T,i),j));
                        m_i_i(S_V_II(S_V_I(T,i),j),
                              S_P_I(perm,S_V_II(S_V_I(T,row),j)-1L));
                }
        }
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     get_T                                                  */
/* Gibt das Tableau T:= perm*t_i zurueck.                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT get_T(T,t_i,perm) OP      T; OP      t_i; OP      perm;
{
    INT     i;
    INT     j;

    for(i=0L;i<S_V_LI(t_i);++i)
        for(j=0L;j<S_V_LI(S_V_I(t_i,i));++j)    
            m_i_i(S_P_II(perm,S_V_II(S_V_I(t_i,i),j)-1L),
                  S_V_I(S_V_I(T,i),j));
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     transponiere (fuer Vektoren von Vektoren)              */
/* Transponiert das Tableaux T in Tt                                   */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT transponiere(T,Tt) OP      T; OP      Tt;
{
    static INT      i;
    static INT      j;

    for(i=0L;i<S_V_LI(T);++i)
        for(j=0;j<S_V_LI(S_V_I(T,i));++j)
            m_i_i(
                S_V_II(S_V_I(T,i),j),
                S_V_I(S_V_I(Tt,j),i));
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     get_col                                                */
/* Gibt die Spaltennr. an, in der zahl in tab vorkommt.                */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT     get_col(tab,zahl) OP      tab; INT     zahl;
{
    INT     i;
    INT     j;
    INT erg = OK;

    for(i=0L;i<S_V_LI(tab);++i)
        for(j=0L;j<S_V_LI(S_V_I(tab,i));++j)
            if(S_V_II(S_V_I(tab,i),j) == zahl) 
                return(j);
    SYMCHECK(1,"should never be here");
    ENDR("sab.c:get_col");
}

/***********************************************************************/
/*                                                                     */
/* Routine:     get_row                                                */
/* Gibt die Zeilennr. an, in der zahl in tab vorkommt.                 */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
static INT     get_row(tab,zahl) OP      tab; INT     zahl;
{
    INT     i,j,erg=OK;

    for(i=0L;i<S_V_LI(tab);++i)
        {
        for(j=0L;j<S_V_LI(S_V_I(tab,i));++j)
            {
            if(S_V_II(S_V_I(tab,i),j) == zahl) return(i);
            }
        }
    SYMCHECK(1,"should never be here");
    ENDR("get_row");
}

/***********************************************************************/
/*                                                                     */
/* Routine:     D_row_calc                                             */
/* Berechnet den Beitrag eines Tableaux T_i^(m) zur Zeile i            */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef PERMTRUE
static INT D_row_calc(T,t,sgn,D_row,n,Tt) OP T,t,D_row,Tt; INT sgn,n;
{
    INT     i;
    INT erg = OK;
    OP z,p1;
    CTO(VECTOR,"D_row_calc(2)",t);

    z = callocobject();
    p1 = callocobject();

    erg += b_ks_p(VECTOR,callocobject(),p1);
    erg += m_il_v(n,S_P_S(p1));

    for(i=0L;i<S_V_LI(t);++i)
        if(ziffern_existieren(Tt,S_V_I(t,i)) == 0L)
            {
            erg += get_Q_perm(T,S_V_I(t,i),p1);
            erg += signum_permutation(p1,z);
            m_i_i(S_V_II(D_row,i)+sgn*S_I_I(z),S_V_I(D_row,i));
            }
        
    erg += freeall(p1);
    erg += freeall(z);
    ENDR("internal:SAB1");
}


/***********************************************************************/
/*                                                                     */
/* Routine:     D_calc                                                 */
/* Berechnet die i-te  Zeile der darstellenden Matrix D^part(perm)     */
/* Berechnung der i-ten Zeile der darstellenden Matrix. Dabei wird     */
/* P in dfs- Weise durchlaufen, und dann werden in D_row_calc()        */
/* die Anteile der Tableaux T_i^(m) berechnet und aufaddiert.          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT D_calc(t,D,P,perm,p_inv,sgn,zeile,i,k,Tt)  
    OP      t; OP      D; OP      P; OP      perm;
    OP      p_inv; INT     sgn; INT     zeile; INT     i;
    INT     k; OP      Tt;
{
        INT     l;
        OP      T = callocobject();
        OP      HP;
        OP      p1 = callocobject();


        b_ks_p(VECTOR,callocobject(),p1);
        m_il_v(S_P_LI(perm),S_P_S(p1));

        m_il_v(S_V_LI(S_V_I(t,0L)),T);
        for(l=0L;l<S_V_LI(T);++l)
                m_il_v(S_V_LI(S_V_I(S_V_I(t,0L),l)),S_V_I(T,l));

        if(i == S_V_LI(t))      
        goto DC_ende;
        else
        {
                if(k==i)
                {
                        get_T(T,S_V_I(t,zeile),p_inv);
                        transponiere(T,Tt);
                        D_row_calc(T,t,sgn,D,S_P_LI(p_inv),Tt);
                }
                if (!emptyp(S_V_I(P,i))) 
                {
                        HP = S_V_I(P,i);
                        for(l=0L;l<S_V_LI(HP);++l)
                        {
                                if(S_V_II(S_V_I(HP,l),0L) > k)
                                {
                                sgn*= -1;
                                invers(p_inv,p1);
                                mult(p1,perm,perm);
                                invers(S_V_I(S_V_I(HP,l),1L),p1);
                                mult(p1,perm,perm);
                                mult(p_inv,perm,perm);
                                get_T(T,S_V_I(t,zeile),perm);
                                transponiere(T,Tt);
                                D_row_calc(T,t,sgn,D,S_P_LI(p_inv),Tt);
                                D_calc(t,D,P,perm,p_inv,sgn,zeile,
                                        S_V_II(S_V_I(HP,l),0L),
                                        S_V_II(S_V_I(HP,l),0L)+1L,Tt);
                                invers(p_inv,p1);
                                mult(p1,perm,perm);
                                mult(S_V_I(S_V_I(HP,l),1L),perm,perm);
                                mult(p_inv,perm,perm);
                                sgn*= -1;
                                } 
                        } 
                } 
        }
DC_ende:
        freeall(T);
        freeall(p1);
    return OK;
}

#endif /* PERMTRUE */
/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Programme zur Berechnung  der seminormalen und der orthogonalen     */
/* Matrixdarstellungen von S_n                                         */
/*                                                                     */
/* Written by: Ralf Hager September 1991                               */
/*                                                                     */
/***********************************************************************/
/***********************************************************************/

/***********************************************************************/
/*                                                                     */
/* Routine:     sdg                                                    */
/* Gibt zu gegebener Partition part und Permutation perm die           */
/* zugehoerige seminormale irreduzible Matrixdarstellung in D zurueck. */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT sdg(part,perm,D) OP      part,perm,D;
{
    INT     i;
    INT     j;
    INT erg = OK;
    INT    lls_vgl();
    OP n,lehmer,HD,dim,t,inh;

    CTO(PARTITION,"sdg(1)",part);
    CTO(PERMUTATION,"sdg(2)",perm);

    n       =       callocobject();
    lehmer  =       callocobject();
    HD      =       callocobject();
    dim     =       callocobject();
    t       =       callocobject();
    inh    =    callocobject();


    erg += dimension(part,dim);
    erg += m_lh_nm(dim,dim,D);
    erg += m_lh_nm(dim,dim,HD);
    erg += m_i_i(S_P_LI(perm),n);
    erg += m_l_v(n,inh);

    for(i=0;i<S_I_I(n);++i)
        erg += m_i_i(1L,S_V_I(inh,i));

    erg += rz_perm(perm,lehmer);
    erg += alpha_beta_tabs(part,inh,t);
    erg += sortieren(0L,S_V_LI(t)-1L,t,lls_vgl);     

    if(!einsp(perm))
        {
        i = S_V_II(lehmer,S_V_LI(lehmer)-1L);
        erg += _xdg(i,t,D,0L);

        for(j=S_V_LI(lehmer)-2L;j>=0L;--j)
            {
            erg += _xdg(S_V_II(lehmer,j),t,HD,0L);
            MULT_APPLY(HD,D);
            }
        }
    else
        {
            for(i=0L;i<S_I_I(dim);++i)      
                M_I_I(1L,S_M_IJ(D,i,i));
        }
    if(S_PA_LI(part) == 1L)
    {
        erg += m_i_i(1L,S_M_IJ(D,0L,0L));
    }
    if(S_PA_LI(part) == S_P_LI(perm))
    {
        erg += signum_permutation(perm,dim);
        erg += m_i_i(S_I_I(dim),S_M_IJ(D,0L,0L));
    }

    FREEALL6(n,inh,lehmer,HD,dim,t);

    ENDR("sdg");
}


/***********************************************************************/
/*                                                                     */
/* Routine:     _xdg                                                   */
/* Gibt zu gegebener Partition und Elementartransposition nr           */
/* zugehoerige irreduzible Matrixdarstellung in P zurueck.             */
/* In t stehen die Standardtableaux zum gegebenen Umriss               */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT _xdg(nr,t,P,var)
    INT     nr; OP      t; OP      P; INT    var;
{
    INT     i,j,k;
    INT     main_diag = 0L;
    INT     get_main_diag();
    INT erg = OK;

    for(i=0L;i<S_V_LI(t);++i)
        for(j=0L;j<S_V_LI(t);++j)       
          m_i_i(0L,S_M_IJ(P,i,j));

    for(i=0L;i<S_V_LI(t);++i)
        {
        /* Hauptdiagonale wird besetzt */

        main_diag = get_main_diag(S_V_I(t,i),nr);
        m_i_i(main_diag,S_M_IJ(P,i,i));
        }

    /* quadratische Bloecke  wernden besetzt */

    for(i=0L;i<S_V_LI(t);++i)
        {
        for(k=i+1L;k<S_V_LI(t);++k)
            {
            get_submatrix(
              nr,i,k,S_V_I(t,i),S_V_I(t,k),P,var);
            }
        }
    CTO(MATRIX,"_xdg(e3)",P);
    ENDR("sab.c:_xdg");
}
#endif /* DGTRUE */
/***********************************************************************/
/*                                                                     */
/* Routine:     get_main_diag                                          */
/* Erstellt einen Eintrag in der Hauptdiagonalen der darst. Mat.       */
/* zum Tableau tab und der Elementartranspositon nr                    */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     get_main_diag(tab,nr) OP      tab; INT     nr;
{
        INT     row_nr;
        INT     row_nr_plus_1;


        row_nr          = get_row(tab,nr);
        row_nr_plus_1   = get_row(tab,nr+1L);

        if(row_nr == row_nr_plus_1)     return(1L);

        row_nr          = get_col(tab,nr);
        row_nr_plus_1   = get_col(tab,nr+1L);

        if(row_nr == row_nr_plus_1)     return(-1L);

        return(0L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     get_submatrix                                          */
/* Erstellt, je nachdem ob var = 0 oder var = 1 gesetzt ist,           */
/* den Diagonalblock zu den Tableaux t_i und t_k fuer die              */
/* darstellende Matrix zur Elementartransposition (nr nr+1)            */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef MATRIXTRUE
static INT get_submatrix(nr,i,k,t_i,t_k,P,var)
    INT     nr; INT     i; INT     k;
    OP      t_i; OP      t_k; OP      P; INT    var;
{
    INT erg = OK;

    OP      dist;
    OP      e_ii;
    OP      e_ik;
    OP      e_ki;
    OP      e_kk;

    INT     ti_eq_transpo_tk();
    INT     get_axial_distance();

    SYMCHECK( (var != 0)&&(var != 1), "sab:get_submatrix:wrong value of var");

    if(ti_eq_transpo_tk(nr,t_i,t_k) == 1L)
    {
        dist = callocobject();
        e_ii = callocobject();
        e_ik = callocobject();
        e_ki = callocobject();
        e_kk = callocobject();
        get_axial_distance(t_i,nr,dist);
        if(var == 0L)
        {
            m_i_i(-1L,e_ii);
            div(e_ii,dist,e_ii);
            copy(e_ii,S_M_IJ(P,i,i));

            m_i_i(1L,e_kk);
            div(e_ii,dist,e_ik);
            add_apply(e_kk,e_ik); /* AK 010692 statt add */
            copy(e_ik,S_M_IJ(P,i,k));

            m_i_i(1L,e_ki);
            copy(e_ki,S_M_IJ(P,k,i));

            m_i_i(1L,e_kk);
            div(e_kk,dist,e_kk);
            copy(e_kk,S_M_IJ(P,k,k));
        }
        if(var == 1L)
        {
            m_i_i(-1L,e_ii);
            div(e_ii,dist,e_ii);
            copy(e_ii,S_M_IJ(P,i,i));

            m_i_i(1L,e_kk);
            div(e_ii,dist,e_ik);
            add_apply(e_kk,e_ik); /* AK 010692 statt add */
            squareroot(e_ik,e_ik);
            copy(e_ik,S_M_IJ(P,i,k));

            copy(e_ik,S_M_IJ(P,k,i));

            m_i_i(1L,e_kk);
            div(e_kk,dist,e_kk);
            copy(e_kk,S_M_IJ(P,k,k));
        }
        freeall(dist);
        freeall(e_ii);
        freeall(e_ik);
        freeall(e_ki);
        freeall(e_kk);
    }


    ENDR("sab:get_submatrix");
}
#endif /* MATRIXTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     ti_eq_transpo_tk                                       */
/* Prueft ob gilt: t_i = transpo*t_k                                   */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     ti_eq_transpo_tk(nr,t_i,t_k)
    INT     nr; OP      t_i; OP      t_k;
{
        INT     i_r;
        INT     i_s;
        INT     j_r;
        INT     j_s;
        INT     erg = 0L;
        INT     ti_eq_tk();

        i_r = get_row(t_k,nr);
        j_r = get_col(t_k,nr);
        i_s = get_row(t_k,nr+1L);
        j_s = get_col(t_k,nr+1L);

        swap(S_V_I(S_V_I(t_k,i_r),j_r), 
             S_V_I(S_V_I(t_k,i_s),j_s));
        if(ti_eq_tk(t_i,t_k) == 1L) erg = 1L;
        swap(S_V_I(S_V_I(t_k,i_r),j_r), 
             S_V_I(S_V_I(t_k,i_s),j_s));
        return(erg);
}


/***********************************************************************/
/*                                                                     */
/* Routine:     get_axial_distanz                                      */
/* Berechnet die Axialdistanz von nr und nr+1 in t_i und schreibt      */
/* sie in  dist.                                                       */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     get_axial_distance(t_i,nr,dist)
    OP      t_i; INT     nr; OP      dist;
{
    INT     get_row();
    INT     get_col();

    INT     i_r;
    INT     j_r;
    INT     i_s;
    INT     j_s;

    i_r = get_row(t_i,nr);
    i_s = get_row(t_i,nr+1L);

    j_r = get_col(t_i,nr);
    j_s = get_col(t_i,nr+1L);

    m_i_i(((j_r-j_s)+(i_s-i_r)),dist);
    return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:     ti_eq_tk                                               */
/* Prueft ob gilt: t_i == t_k                                          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     ti_eq_tk(t_i,t_k) OP      t_i; OP      t_k;
{
        INT     i;
        INT     j;

        for(i=0L;i<S_V_LI(t_i);++i)
                for(j=0L;j<S_V_LI(S_V_I(t_i,i));++j)
                        if(S_V_II(S_V_I(t_i,i),j) != 
                           S_V_II(S_V_I(t_k,i),j))    
                                return(0L);
        return(1L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     lls_vgl                                                */
/* Vergleich nach last letter sequenz  zweier Operanden                */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT     lls_vgl(a,b) OP      a; OP      b;
{
        INT     i;
        INT     j;
        INT     k;
        INT     merk_a=0;
        INT     merk_b=0;

        INT     n = 0L;

        for(i=0L;i<S_V_LI(a);++i)n+= S_V_LI(S_V_I(a,i));

        for(k=n;k>=1L;--k)
                {
                for(i=0L;i<S_V_LI(a);++i)
                {
                        for(j=0L;j<S_V_LI(S_V_I(a,i));++j)
                        {
                                if(S_V_II(S_V_I(a,i),j) == k)   
                                {
                                        merk_a = i;
                                        break;
                                }
                        }
                }
                for(i=0;i<S_V_LI(a);++i)
                {
                        for(j=0L;j<S_V_LI(S_V_I(a,i));++j)
                        {
                                if(S_V_II(S_V_I(b,i),j) == k)   
                                {
                                        merk_b = i;
                                        break;
                                }
                        }
                }
                if(merk_a < merk_b)     return(-1L);
                if(merk_a > merk_b)     return(1L);
                }
        return(0L);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     odg                                                    */
/* Gibt zu gegebener Partition part und Permutation perm die           */
/* zugehoerige orthogonale irreduzible Matrixdarstellung in D zurueck. */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT cyclo_odg(a,b,c) OP a,b,c;
/* AK 110202 */
{
    INT erg = OK;
    OP d;
    INT i,j;
    d = CALLOCOBJECT();
    erg += odg(a,b,d);
    m_lh_m(S_M_L(d),S_M_H(d),c);
    for(i=0;i<S_M_HI(c);i++)
    for(j=0;j<S_M_LI(c);j++)
        {
        if (S_O_K(S_M_IJ(d,i,j)) == SQ_RADICAL)
        convert_sqrad_cyclo(S_M_IJ(d,i,j), S_M_IJ(c,i,j));
        else
        copy(S_M_IJ(d,i,j), S_M_IJ(c,i,j));
        }
    FREEALL(d);
    ENDR("cyclo_odg");
}

INT cyclo_an_tafel(a,c) OP a,c;
/* AK 130202 */
{
    INT erg = OK;
    OP d;
    INT i,j;
    d = CALLOCOBJECT();
    erg += an_tafel(a,d);
    m_lh_m(S_M_L(d),S_M_H(d),c);
    for(i=0;i<S_M_HI(c);i++)
    for(j=0;j<S_M_LI(c);j++)
        {
        if (S_O_K(S_M_IJ(d,i,j)) == SQ_RADICAL)
        convert_sqrad_cyclo(S_M_IJ(d,i,j), S_M_IJ(c,i,j));
        else
        copy(S_M_IJ(d,i,j), S_M_IJ(c,i,j));
        }
    FREEALL(d);
    ENDR("cyclo_an_tafel");
}

INT odg(part,perm,D) OP  part,perm,D;
/* RH 1991 */
/* AK 220704 V3.0 */
{
    INT erg = OK;
    CTO(PARTITION,"odg(1)",part);
    CTO(PERMUTATION,"odg(2)",perm);
    CE3(part,perm,D,odg);
    {
#ifdef DGTRUE
    INT     i;
    INT     j;
    INT    lls_vgl();
    OP rz,HD,dim,t,inh;


    HD      =       callocobject();
    dim     =       callocobject();
    t       =       callocobject();
    inh    =    callocobject();
    rz  =       callocobject();

    erg += weight(part,dim);
    if (neq(dim, S_P_L(perm)) )
        {
        error("odg: part and perm have different weights");
        erg += ERROR;
        goto odge;
        }


    erg += dimension(part,dim);
    erg += m_lh_nm(dim,dim,D);
    erg += m_lh_nm(dim,dim,HD);
    erg += m_il_v(S_P_LI(perm),inh);

    for(i=0;i<S_V_LI(inh);++i)
        M_I_I(1L,S_V_I(inh,i));

    erg += rz_perm(perm,rz);
    CTTO(INTEGERVECTOR,VECTOR,"odg(i)",rz);
    erg += alpha_beta_tabs(part,inh,t);
    erg += sortieren(0L,S_V_LI(t)-1L,t,lls_vgl);     

    if(!einsp(perm))
        {
        i = S_V_II(rz,S_V_LI(rz)-1L);
        erg += _xdg(i,t,D,1L);

        for(j=S_V_LI(rz)-2L;j>=0L;--j)
            {
            erg += _xdg(S_V_II(rz,j),t,HD,1L);
            MULT_APPLY(HD,D);
            }
        }
    else
        {
        for(i=0L;i<S_I_I(dim);++i)      
            erg += m_i_i(1L,S_M_IJ(D,i,i));
        }
    if(S_PA_LI(part) == 1L)
    {
        erg += m_i_i(1,S_M_IJ(D,0,0));
    }
    if(S_PA_LI(part) == S_P_LI(perm))
    {
        erg += signum_permutation(perm,dim);
        CLEVER_COPY(dim,S_M_IJ(D,0,0));
    }

odge:
    FREEALL5(inh,rz,HD,dim,t);
#endif
    }
    ENDR("odg");
}
#ifdef DGTRUE
/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Programm zur Berechnung einer polynomialen, irreduziblen            */
/* Matrixdarstellung von GL_m(C).                                      */
/* Dabei wird zu einer Partition part ein Satz von orthonormalen       */
/* Basisvektoren bestimmt, mit denen dann ein Basiswechsel             */
/* durchgefuehrt wird. Es werden in diesem Spezialfall nur die         */
/* Projektoren P_11 berechnet, statt einer Matrixinversion kann        */
/* man die transponierte Matrix betrachten.                            */
/* Zum orthonormalisieren wird das Gram-Schmidt-Verfahren verwendet.   */
/* Das Ergebnis steht in Matrix D.                                     */
/*                                                                     */
/* Written by: Ralf Hager September 1991                               */
/*                                                                     */
/***********************************************************************/
/***********************************************************************/


/***********************************************************************/
/*                                                                     */
/* Routine:     glpdg                                                  */
/* Diese Routine ruft zunaechst glm_sab auf, wo die Basis B berechnet  */
/* wird. Im Unterprogramm glm_B_W wird dann der Basiswechsel           */
/* durchgefuehrt.                                                      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT glpdg(m,part,D) OP    m; OP    part; OP    D;
{
    INT erg = OK; /* AK 010692 */
    OP    B    =    callocobject();
    OP    n    =    callocobject();

    erg += weight(part,n); /* AK 010692 */

    erg += glm_sab(m,n,B,part); /* Symmetrieangepasste Basis errechnen */
    erg += glm_B_W(m,n,B,D);       /* Basiswechsel durchfuehren           */ 

    erg += freeall(n);
    erg += freeall(B);
    return erg;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     glm_sab                                                */
/* Die Routine verlaeuft analog zur Routine sab, nur dass hier         */
/* ausgenutzt werden kann, dass die S_n nicht vorher erzeugt werden    */
/* muss. Ausserdem wird nur P_11 zu part bestimmt, da man sich nur     */
/* fuer einen Block der homogenen Komponente interessiert.             */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef SABTRUE
INT glm_sab(m,n,B,part) OP    m; OP    n; OP    B; OP    part;
{
    INT    TP();

    OP    f_D     =     callocobject();
    OP    irr_dim =    callocobject();
    OP    faktor     =    callocobject();
    OP    dim;
    OP    perm    =    callocobject();
    OP    tupel    =    callocobject();
    OP    D    =    callocobject();
    OP    X    =    callocobject();
    OP    PROJ    =    callocobject();

    NEW_INTEGER(dim,0);
    hoch(m,n,f_D);
    dimension_symmetrization(m,part,dim);
    m_lh_nm(dim,f_D,B);
    m_l_nv(n,tupel);
    m_il_p(S_I_I(f_D),X);

    if(S_PA_LI(part) <= S_I_I(m))
    {
    dimension_partition(part,irr_dim);
    m_lh_nm(f_D,f_D,PROJ);
    first_permutation(n,perm);
    do
    {
        invers(perm,perm);
        odg(part,perm,D); 
        invers(perm,perm);
        m_l_nv(n,tupel);
        TP(tupel,0L,n,m,perm,X);
        copy(S_M_IJ(D,0L,0L),faktor);
        if(!nullp(faktor)) 
            add_to_PROJ(PROJ,faktor,X);
    }while(next(perm,perm));
    m_i_i(0L,dim);
    glm_get_BV(PROJ,B,dim);
    reell_gram_schmidt(B);
    }
    freeall(PROJ);
    freeall(dim);
    freeall(f_D);
    freeall(irr_dim);
    freeall(X);
    freeall(faktor);
    freeall(tupel);
    freeall(perm);
    freeall(D);
    return OK;
}
#endif /* SABTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     reell_gram_schmidt                                     */
/* Dieses Unterprogramm arbeitet analog zur Routine gram_schmidt.      */
/* Es wird hier jedoch keine Konjugation durchgefuehrt, da die         */
/* betrachteten Vektoren nur relle Eintraege besitzen.                 */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */


#ifdef MATRIXTRUE
INT reell_gram_schmidt(A) OP    A;
{
    INT    i;
    INT    j;
    INT    k;

    OP    R     =    callocobject();
    OP    h    =    callocobject();
    OP    n     =    callocobject();
    OP    p     =    callocobject();
    OP    s     =    callocobject();

    m_lh_nm(S_M_H(A),S_M_L(A),R);
    m_i_i(S_M_HI(A),n);
    m_i_i(S_M_LI(A),p);

    for(k=0L;k<S_I_I(p);++k)
    {
        for(j=0L;j<k;++j)
        {
            m_i_i(0L,S_M_IJ(R,j,k));
            for(i=0L;i<S_I_I(n);++i)
            {
                mult(S_M_IJ(A,i,j),S_M_IJ(A,i,k),h);
                add_apply(h,S_M_IJ(R,j,k));
            }
            for(i=0L;i<S_I_I(n);++i)
            {
                mult(S_M_IJ(R,j,k),S_M_IJ(A,i,j),h);
                addinvers_apply(h);
                add_apply(h,S_M_IJ(A,i,k));
            }
        }
        m_i_i(0L,s);
        for(i=0L;i<S_I_I(n);++i)
        {
            mult(S_M_IJ(A,i,k),S_M_IJ(A,i,k),h);
            add_apply(h,s);
        }
        squareroot(s,S_M_IJ(R,k,k));
        invers(S_M_IJ(R,k,k),h);
        for(i=0L;i<S_I_I(n);++i)
            mult_apply(h,S_M_IJ(A,i,k));
    }

    freeall(R);
    freeall(h);
    freeall(n);
    freeall(p);
    freeall(s);
    return OK;
}
#endif /* MATRIXTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     get_poly_self                                          */
/* Diese Routine besetzt, ausgehend von einem Index den self-teil      */
/* eines polynomialen Eintrages der Matrix "n-faches Tensorprodukt     */
/* der generischen GLm(C) matrix.                                      */
/* Der Zeilenindex row und der Spaltenindex col werden dabei m-naer    */
/* ausgedrueckt.  Dies ergibt die Indices des Monoms. Diese Indices    */
/* werden in die Matrix polyself uebertragen.                          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */


#ifdef MATRIXTRUE
static INT get_poly_self(row,col,m,n,polyself)
    INT    row; INT    col; OP    m; OP    n; OP    polyself;
/* AK 010692 */
{
    INT    i;
    OP dim,zeile,spalte,oprow,opcol,x,y;
    INT erg = OK; /* AK 030197 */
    CTO(INTEGER,"get_poly_self(4)",n);


    dim    =    callocobject();
    zeile    =    callocobject();
    spalte    =    callocobject();
    oprow    =    callocobject();
    opcol    =    callocobject();
    x    =    callocobject();
    y    =    callocobject();

    erg += m_l_nv(n,zeile);
    erg += m_l_nv(n,spalte);
    erg += hoch(m,n,dim);
    erg += m_i_i(row,oprow);
    erg += m_i_i(col,opcol);
    for(i=0L;i<S_I_I(n);++i)
    {
        erg += m_i_i(S_I_I(dim)/S_I_I(m),dim);
        erg += m_i_i(S_I_I(opcol)/S_I_I(dim),S_V_I(spalte,i));
        erg += m_i_i(S_I_I(oprow)/S_I_I(dim),S_V_I(zeile,i));
        erg += m_i_i(S_I_I(dim)*S_V_II(zeile,i),x);
        erg += m_i_i(S_I_I(dim)*S_V_II(spalte,i),y);
        erg += m_i_i(S_I_I(oprow)-S_I_I(x),oprow);
        erg += m_i_i(S_I_I(opcol)-S_I_I(y),opcol);
    }

    erg += freeall(x); 
    x = cons_null;
    for(i=0;i<S_I_I(n);++i)    
        if(S_V_II(zeile,i) >= S_I_I(x)) /* copy(S_V_I(zeile,i),x); */
            x = S_V_I(zeile,i);
    freeall(y); 
    y = cons_null;
    for(i=0;i<S_I_I(n);++i)    
        if(S_V_II(spalte,i) >= S_I_I(y)) /* copy(S_V_I(spalte,i),y); */
            y = S_V_I(spalte,i);
    erg += m_ilih_nm(S_I_I(y)+1L,S_I_I(x)+1L,polyself);
    for(i=0L;i<S_I_I(n);++i)
        inc_integer(S_M_IJ(polyself,S_V_II(zeile,i),S_V_II(spalte,i)));

    erg += freeall(oprow);
    erg += freeall(opcol);
    erg += freeall(dim);
    erg += freeall(zeile);
    erg += freeall(spalte);
    ENDR("get_poly_self");
}
#endif /* MATRIXTRUE */
/***********************************************************************/
/*                                                                     */
/* Routine:     glm_B_W                                                */
/* Der Basiswechsel zur erstellung von <<part>> wird durchgefuehrt.    */
/* Er hat den Aufwand O(m^2n f^2), ist also extrem aufwendig.          */
/* Dabei ist f die Dimension derSymmetrisierung <<part>>.              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT glm_B_W(m,n,B,D)
    OP    m; OP    n; OP    B; OP    D;
{
    INT    i,j,k,l;

    OP    polyself = callocobject();
    OP    erg = callocobject();
    OP    x = callocobject();
    OP    mneu = callocobject();

    m_lh_m(S_M_L(B),S_M_L(B),D);

    for(i=0L;i<S_M_LI(B);++i)
    {
        for(j=0L;j<S_M_LI(B);++j)
        {
            m_i_i(0L,mneu);
            for(k=0L;k<S_M_HI(B);++k)
            {
                for(l=0L;l<S_M_HI(B);++l)
                {
                    if(not nullp(S_M_IJ(B,k,i)) && 
                       not nullp(S_M_IJ(B,l,j)))
                       {

                       mult(S_M_IJ(B,k,i),S_M_IJ(B,l,j),erg);
                       get_poly_self(k,l,m,n,polyself);
                       m_skn_po(polyself,erg,NULL,x);
                       add_apply(x,mneu);
                       }
                }
            }
            copy(mneu,S_M_IJ(D,i,j));
        }
    }

    freeall(polyself);
    freeall(erg);
    freeall(x);
    freeall(mneu);
    return OK;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     TP                                                     */
/* Rekursive Routine zur Berechnung der Permutationsdarstellung        */
/* von S_n auf dem Tensorraum C^(m^n). Es werden dabei alle            */
/* n-stelligen Tupel mit Eintraegen aus m durchlaufen. Die             */
/* Permutationsmatrix wird als Permutation bperm codiert.              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
static INT TP(tupel,st,n,m,sperm,bperm)
    OP    tupel; INT    st; OP    n; OP    m;
    OP    sperm; OP    bperm;
{
    INT    i;
    INT    zeile        =    0L;
    INT    spalte        =    0L;
    INT    TP();
    INT    get_nr_of_tupel();
    static    INT count     =     0L;
    OP    htupel;

    if(st == S_I_I(n)) 
    {
        htupel         =     callocobject();
        count++;
        m_l_nv(n,htupel);
        bilde_htupel(sperm,tupel,htupel);
        spalte    =    get_nr_of_tupel(tupel,m);
        zeile    =    get_nr_of_tupel(htupel,m);
        m_i_i(zeile+1L,S_P_I(bperm,spalte));
        freeall(htupel);
    }
    else
        {
        for(i=0L;i<S_I_I(m);++i)
            {
            m_i_i((INT)(S_V_II(tupel,st)+i),S_V_I(tupel,st));
            TP(tupel,(INT)(st+1L),n,m,sperm,bperm);
            m_i_i((INT)(S_V_II(tupel,st)-i),S_V_I(tupel,st));
            }
        }
    return OK;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     bilde_htupel                                           */
/* Hilfsroutine zur Tupelbildung.                                      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT bilde_htupel(perm,tupel,htupel)
    OP    perm; OP    tupel; OP    htupel;
{
    INT    i;

    invers(perm,perm);
    for(i=0L;i<S_P_LI(perm);++i)
    {
        m_i_i(S_V_II(tupel,S_P_II(perm,i)-1L),S_V_I(htupel,i));
    }
    invers(perm,perm);
    return OK;
}



/***********************************************************************/
/*                                                                     */
/* Routine:     get_nr_of_tupel                                        */
/* Hilfsroutine zur Tupelbildung.                                      */
/* Ein Tupel wird als m-naere Zahl aufgefasst. Diese wird berechnet    */
/* und zurueckgegeben.                                                 */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

static INT    get_nr_of_tupel(tupel,m) OP    tupel; OP    m;
{
    INT    i;
    INT    expo;
    INT    nr = 0L;
    INT    mhochexpo();

    for(i=0L;i<S_V_LI(tupel);++i)
    {
        if(S_V_II(tupel,i) > 0L)
        {
            expo = S_V_LI(tupel)-i-1L;
            expo = mhochexpo(S_I_I(m),expo);
            expo*= S_V_II(tupel,i);
            nr+= expo;
        }
    }

    return(nr);
}
static INT    mhochexpo(x,y) INT    x; INT    y;
{
    INT    i;
    INT    erg = 1L;

    if(y == 0L)return(1L);
    erg = x;
    for(i=2L;i<=y;++i)
        erg*=x;
    return(erg);
}

/***********************************************************************/
/*                                                                     */
/* Routine:     dimension_symmetrization                               */
/* Die Dimension der Symmetrisierung von part in GL_m(C) wird bestimmt.*/
/* Grundlange ist die in JK79 S. 188 angegebene Formel.                */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */
/* = anzahl der tableaux vom umriss part und max eintrag m */

#ifdef PARTTRUE
INT dimension_symmetrization(m,part,dim) OP m,part,dim;
/* RH 011091 */ /* AK 010692 */
{
    INT    i;
    INT    j;
    INT erg = OK;

    OP    nfak;
    OP    f_part;
    OP    hpart;
    OP    _i;
    OP    _j;
    OP    h;

    CTO(INTEGER,"dimension_symmetrization(1)",m);
    CTO(PARTITION,"dimension_symmetrization(2)",part);

    nfak     = callocobject();
    f_part = callocobject();
    hpart = callocobject();
    _i = callocobject();
    _j = callocobject();
    h = callocobject();

    m_i_i(1L,dim);
    for(i=0L;i<S_PA_LI(part);++i) 
        erg += add_apply(S_PA_I(part,i),nfak);
    erg += m_l_v(S_PA_L(part),hpart);
    for(i=0;i<S_PA_LI(part);++i) 
        erg += copy(S_PA_I(part,S_PA_LI(part)-i-1L),S_V_I(hpart,i));
    erg += fakul(nfak,nfak);
    erg += dimension_partition(part,f_part);

    for(i=1L;i<=S_V_LI(hpart);++i)
        for(j=1L;j<=S_V_II(hpart,i-1L);++j)
            {
                m_i_i(-i,_i);
                m_i_i( j,_j);
                erg += add(_i,_j,h);
                erg += add_apply(m,h);
                erg += mult_apply(h,dim);
            }

    erg += div(dim,nfak,dim);
    erg += mult(f_part,dim,dim);

    erg += freeall(nfak);
    erg += freeall(f_part);
    erg += freeall(hpart);
    erg += freeall(h);
    erg += freeall(_j);
    erg += freeall(_i);
    ENDR("dimension_symmetrization");
}
#endif /* PARTTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     glm_get_BV                                             */
/* Arbeitet analog zur Routine get_BV                                  */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

INT glm_get_BV(PROJ,B,count)
    OP    PROJ; OP    B; OP    count;
{
    INT    i;
    INT    j;
    INT    k;
    INT    l;
    INT    s;
    INT    f_D;

    OP    Proj    =    callocobject();
    OP    val    =    callocobject();
    OP    faktor  =    callocobject();
    OP    h  =    callocobject();

    copy(PROJ,Proj);
    f_D = S_M_HI(B);
    k = 0L;
    for(i=0L;i<f_D;++i)
    {
        for(j=k;j<f_D;++j)
        {
            if(!nullp(S_M_IJ(Proj,j,i)))
            {
                for(l=0L;l<f_D;++l)
                {
                    copy(S_M_IJ(PROJ,l,i),S_M_IJ(B,l,S_I_I(count)));
                }
                inc(count);
                if(j != k)
                    for(l=0L;l<f_D;++l)
                    {
                    swap(S_M_IJ(Proj,k,l),S_M_IJ(Proj,j,l));
                    }
                invers(S_M_IJ(Proj,k,i),h);
                for(l=k+1L;l<f_D;++l)
                    if(!nullp(S_M_IJ(Proj,l,i)))
                    {
                        mult(S_M_IJ(Proj,l,i),h,faktor);
                        for(s=i;s<f_D;++s)
                        {
/*
                    mult(faktor,S_M_IJ(Proj,k,s),val);
                    sub(S_M_IJ(Proj,l,s),val,val);
                    copy(val,S_M_IJ(Proj,l,s));
*/
                    mult(faktor,S_M_IJ(Proj,k,s),val);
                    addinvers_apply(val);
                    add_apply(val,S_M_IJ(Proj,l,s));
                        }
                    }
            }
        }
        k++;
    }

    freeall(Proj);
    freeall(val);
    freeall(faktor);
    freeall(h);
    return OK;
}

/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Homomorphietest fuer GLm(C) Darstellungen.                          */
/* Es werden 2 Matrizen A,B mit Zufallszahlen besetzt, und dann in     */
/* <<part>> eingesetzt. Dann wird A*B gebildet, eingesetzt und auf     */
/* Gleichheit getestet.                                                */
/*                                                                     */
/*    written by: Ralf Hager (August 1991)                           */
/***********************************************************************/
/***********************************************************************/
/* RH 011091 */

/***********************************************************************/
/*                                                                     */
/* Routine:     glm_homtest                                                */
/* Hauptroutine fuer den Homomorphietest.                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT glm_homtest(m,d) OP    m,d;
{
    OP    a;
    OP    b;
    OP    anz;


    a    =    callocobject();
    b    =    callocobject();
    anz    =    callocobject();

    m_lh_nm(m,m,a);
    m_lh_nm(m,m,b);
    bestimme_zufallsmatrizen(m,a,b);
    if(_homtest(a,b,d) == (INT)1)
    {
        printf("Homtest OK\n");
    }
    else
    {
        printf("Fehler in Homtest\n");
    }

    freeall(a);
    freeall(b);
    freeall(anz);
    return OK;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     bestimme_zufallsmatrizen                               */
/* Es werden zwei Matrizen A,B mit Zufallszahlen zwischen -5 und 5     */
/* besetzt.                                                            */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef MATRIXTRUE
INT bestimme_zufallsmatrizen(m,a,b) OP    m,a,b;
{
    INT    i;
    INT    j;
    OP    zahl    =    callocobject();
    OP    ober    =    callocobject();
    OP    unter    =    callocobject();

    m_i_i((INT)-5,unter);
    m_i_i((INT)5,ober);
    for(i=0L;i<S_I_I(m);++i)
    {
        for(j=0L;j<S_I_I(m);++j)
        {
            random_integer(S_M_IJ(a,i,j),unter,ober);
            random_integer(S_M_IJ(b,i,j),unter,ober);
        }
    }

    freeall(zahl); freeall(unter); freeall(ober);
    return OK;
}
#endif /* MATRIXTRUE */
/***********************************************************************/
/*                                                                     */
/* Routine:     _homtest                                               */
/* Die Homomorphieeigenschaft wird nachgerechnet.                      */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT _homtest(a,b,m) OP    a,b,m;
{
    OP    ab     =     callocobject();
    OP    d_a    =    callocobject();
    OP    d_b    =    callocobject();
    OP    d_ab    =    callocobject();

    m_lh_nm(S_M_L(m),S_M_L(m),d_a);
    m_lh_nm(S_M_L(m),S_M_L(m),d_b);
    m_lh_nm(S_M_L(m),S_M_L(m),d_ab);

    mult(a,b,ab);
    bestimme_D(m,a,d_a);
    bestimme_D(m,b,d_b);
    bestimme_D(m,ab,d_ab);
    mult(d_a,d_b,d_a);
    if(!EQ(d_a,d_ab)) 
    {
        error("Hilfe, keine Darstellung !!!!!!!!!!!!\n");

        freeall(ab);
        freeall(d_a);
        freeall(d_b);
        freeall(d_ab);
        return((INT)0);
    }
    else
    {
        freeall(ab);
        freeall(d_a);
        freeall(d_b);
        freeall(d_ab);
        return((INT)1);
    }
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     bestimme_D                                             */
/* Die Matrix A wird in M eingesetzt und das Ergebnis auf D_A          */
/* geschrieben.                                                        */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT bestimme_D(m,a,d_a) OP m,a,d_a;
{
    INT    i;
    INT    j;

    for(i=0L;i<S_M_LI(m);++i)
    {
        for(j=0L;j<S_M_LI(m);++j)
        {
            werte_Polynom_aus(a,S_M_IJ(m,i,j),S_M_IJ(d_a,i,j));
        }
    }
    return OK;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     werte_Polynom_aus                                      */
/* Das multivariate Polynom poly wird mit A ausgewertet.               */
/* Das Ergebnis steht in erg.                                          */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef MATRIXTRUE 
INT werte_Polynom_aus(a,poly,erg)
    OP    a; OP    poly; OP    erg;
{
    INT    k;
    INT    l;

    OP    z = poly;
    OP    x = callocobject();
    OP    y = callocobject();

    m_i_i(0L,x);
    m_i_i(0L,y);
    m_i_i(0L,erg);

    while(z != NULL)
    {
        if(!nullp(S_PO_K(z)) && !emptyp(S_PO_K(z)))    
        {
            copy(S_PO_K(z),x);
            for(k=0L;k<S_M_HI(S_PO_S(z));++k)
            {
                for(l=0L;l<S_M_LI(S_PO_S(z));++l)
                    if(S_M_IJI(S_PO_S(z),k,l) > 0L)
                    {
                hoch(S_M_IJ(a,k,l),S_M_IJ(S_PO_S(z),k,l),y);
                mult_apply(y,x); /* AK 120692 statt mult */
                    }

            }
        }
        z = S_PO_N(z);
        add_apply(x,erg); /* AK 010692 statt add */
    }
    freeall(x); /* AK 010692 */
    freeall(y);  /* AK 010692 */
    return OK;
}
#endif /* MATRIXTRUE */

/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Programm zur Bestimmung von GLm(C) Matrixdarstellungen ohne         */
/* Orthonormalisierungsschritt.                                        */
/* Es kann durch var zwischen der orthogonalen (var = 0L) und der      */
/* Boernerschen (var = 1L) Matrixdarstellung gewaehlt werden.          */
/* Es wird eine m^n-dimensionale Matrix zerlegt. Sie muss im Fall      */
/* von (S_n,GLm(C)) jedoch nicht explizit bekannt sein, sondern        */
/* wird elementweise berechnet.                                        */
/* Ansonsten ist das Verfahren identisch zu dem in sab beschriebenen.  */
/*                                                                     */
/*    written by: Ralf Hager (August 1991)                           */
/***********************************************************************/
/***********************************************************************/

/***********************************************************************/
/*                                                                     */
/* Routine:     input_glmn                                             */
/* Ein Erzeugendensystem fuer Sn wird bestimmt zusammen mit den        */
/* darstellenden Matrizen der irreduziblen Matrixdarstellungen         */
/* part mit part_1' <= m.                                              */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
INT input_glmn(m,n,S,SMat,var)
    OP    m; OP    n; OP    S; OP    SMat; INT    var;
{
    INT    i;

    OP    part    =    callocobject();
    OP    anz_irr    =    callocobject();
    OP    perm1    =    callocobject();
    OP    perm2    =    callocobject();
    OP    m_hoch_n=    callocobject();
    OP    tupel     =     callocobject();

    m_i_i(0L,anz_irr);

    hoch(m,n,m_hoch_n);
    first_partition(n,part);
    do
    {
        if(S_PA_LI(part)<= S_I_I(m)) inc(anz_irr);
    } while(next(part,part));

    if(S_I_I(n) > 2)
    {
        m_il_v(2L,S);
        m_il_p(S_I_I(m_hoch_n),S_V_I(S,0L));
        m_il_p(S_I_I(m_hoch_n),S_V_I(S,1L));
        m_il_p(S_I_I(n),perm1);
        m_il_p(S_I_I(n),perm2);

        for(i=2L;i<=S_I_I(n);++i) 
        {
            m_i_i(i,S_P_I(perm2,i-2L));
        }
        m_i_i(1L,S_P_I(perm2,S_I_I(n)-1L));

        for(i=1L;i<=S_I_I(n);++i) 
        {
            m_i_i(i,S_P_I(perm1,i-1L));
        }

        m_i_i(2L,S_P_I(perm1,0L));
        m_i_i(1L,S_P_I(perm1,1L));
        m_l_v(anz_irr,SMat);
        for(i=0L;i<S_I_I(anz_irr);++i)    m_il_v(2L,S_V_I(SMat,i));

        m_l_nv(n,tupel);
        TP(tupel,0L,n,m,perm1,S_V_I(S,0L));
        m_l_nv(n,tupel);
        TP(tupel,0L,n,m,perm2,S_V_I(S,1L));

        i = 0L;
        first_partition(n,part);
        do
        {
            if(S_PA_LI(part)<=S_I_I(m))
            {
            if(var == 0L)
            {
            odg(part,perm1,S_V_I(S_V_I(SMat,i),0L));
            odg(part,perm2,S_V_I(S_V_I(SMat,i),1L));
            }
            if(var == 1L)
            {
            bdg(part,perm1,S_V_I(S_V_I(SMat,i),0L));
            bdg(part,perm2,S_V_I(S_V_I(SMat,i),1L));
            }
            i++;
            }
        }    while(next(part,part));
    }
    else
    {
        m_il_v(1L,S);
        m_il_p(S_I_I(m_hoch_n),S_V_I(S,0L));
        m_il_p(S_I_I(n),perm1);
        for(i=2L;i<=S_I_I(n);++i) 
        {
            m_i_i(i,S_P_I(perm1,i-2L));
        }
        m_i_i(1L,S_P_I(perm1,S_I_I(n)-1L));
        m_l_v(anz_irr,SMat);
        for(i=0L;i<S_I_I(anz_irr);++i)    m_il_v(1L,S_V_I(SMat,i));
        m_l_nv(n,tupel);
        TP(tupel,0L,n,m,perm1,S_V_I(S,0L));
        i = 0L;
        first_partition(n,part);
        do
        {
            if(S_PA_LI(part)<=S_I_I(m))
            {
            if(var == 0L)
            {
            odg(part,perm1,S_V_I(S_V_I(SMat,i),0L));
            }
            if(var == 1L)
            {
            bdg(part,perm1,S_V_I(S_V_I(SMat,i),0L));
            }
            i++;
            }
        }while(next(part,part));
    }

    freeall(perm1);
    freeall(perm2);
    freeall(part);
    freeall(anz_irr);
    freeall(m_hoch_n);
    freeall(tupel); /* AK 010692 */
    return OK;
}
#endif /* DGTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     glmndg                                                 */
/* Es wird zunaechst die Eingabe erzeugt,                              */
/* dann wird die Gruppe konstruiert und schliesslich die Basis         */
/* berechnet.                                                          */
/* Dann wird der Basiswechsel durchgefuehrt.                           */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
#ifdef SABTRUE
INT glmndg(m,n,M,var) OP m,n,M; INT    var;
{
    OP    Di;
    OP    D;
    OP    B;
    OP    sym_dim;
    OP    sn_dim;
    OP    S;
    OP    SMat;

    INT erg = OK; /* AK 230893 */
    CTO(INTEGER,"glmndg(1)",m);
    CTO(INTEGER,"glmndg(2)",n);

    CALLOCOBJECT7(Di,D,B,sym_dim,sn_dim,S,SMat);
 

    erg += input_glmn(m,n,S,SMat,var);
    erg += group_gen(S,SMat,D,Di);
    erg += _sab(Di,D,B,sym_dim,sn_dim);
    erg += glmn_B_W(m,n,B,sym_dim,sn_dim,M);

    FREEALL7(Di,D,B,sym_dim,sn_dim,S,SMat);
    ENDR("glmndg");
}
#endif /* SABTRUE */
#endif /* DBTRUE */

/***********************************************************************/
/*                                                                     */
/* Routine:     glmn_B_W                                               */
/* Der Basiswechsel wird durchgefuehrt, die Matrix M wird ein          */
/* Vektor aus Matrizen, in denen die irreduziblen Matrixdarstellungen  */
/* stehen.                                                             */
/*                                                                     */
/***********************************************************************/
/* RH 011091 */

#ifdef DGTRUE
static INT glmn_B_W(m,n,B,sym_dim,sn_dim,M)
    OP    m; OP    n; OP    B; OP    sym_dim;
    OP    sn_dim; OP    M;
{
    INT    i,j,k,l,s;

    OP    B_1;
    OP    polyself;
    OP    res;
    OP    x;
    OP    mneu;
    OP    count;
    OP    r;

    INT erg = OK; /* AK 230893 */

    CTO(VECTOR,"glmn_B_W(4)",sym_dim);

    B_1    =    callocobject();
    polyself=     callocobject();
    res     =     callocobject();
    x     =     callocobject();
    mneu    =     callocobject();
    count    =    callocobject();
    r    =    callocobject();

    erg += invers(B,B_1);
        m_i_i(0L,count);
        for(s=0L;s<S_V_LI(sym_dim);++s)
                if(S_V_II(sym_dim,s) != 0L)
            erg += inc(count);
    erg += m_l_v(count,M);
        m_i_i(0L,count);
    for(i=0L;i<S_V_LI(sym_dim);++i)
                if(S_V_II(sym_dim,i) != 0L)
        {
            erg += m_lh_m(S_V_I(sym_dim,i),S_V_I(sym_dim,i),S_V_I(M,S_I_I(count)));
            erg += inc(count);
        }
        m_i_i(0L,count);
        m_i_i(0L,r);

    m_i_i(0L,count);
    for(s=0L;s<S_V_LI(sym_dim);++s)
        if(S_V_II(sym_dim,s) != 0L)    m_i_i(S_I_I(count)+1L,count);

    m_i_i(0L,count);
    for(s=0L;s<S_V_LI(sym_dim);++s)
    {
        if(S_V_II(sym_dim,s) != 0L)
        {
            for(i=S_I_I(count);i<S_I_I(count)+S_V_II(sym_dim,s);++i)
            {
                for(j=S_I_I(count);j<S_I_I(count)+S_V_II(sym_dim,s);++j)
                {
                    m_i_i(0L,mneu);
                    for(k=0;k<S_M_LI(B);++k)
                    {
                        for(l=0L;l<S_M_LI(B);++l)
                        {
                            if(!nullp(S_M_IJ(B_1,i,k)) && 
                               !nullp(S_M_IJ(B,l,j)))
                               {

                   erg += mult(S_M_IJ(B_1,i,k),S_M_IJ(B,l,j),res);
                   erg += get_poly_self(k,l,m,n,polyself);
                   erg += m_skn_po(polyself,res,NULL,x);
                   erg += add_apply(x,mneu); /* AK 010692 statt add */
                               }
                        }
                    }
                erg += copy(mneu,
                    S_M_IJ(S_V_I(M,S_I_I(r)),
                        i-S_I_I(count),j-S_I_I(count)));
                }
            }
        erg += inc(r);
        }
        erg += mult(S_V_I(sym_dim,s),S_V_I(sn_dim,s),x);
        erg += add_apply(x,count); /* AK 010692 statt add */
    }

    erg += freeall(B_1);
    erg += freeall(polyself);
    erg += freeall(res);
    erg += freeall(x);
    erg += freeall(mneu);
    erg += freeall(r);
    erg += freeall(count);
    ENDR("glmn_B_W");
}
#endif /* DGTRUE */

