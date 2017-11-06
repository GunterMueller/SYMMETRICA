/*mod_dg_sbd.c
  berechnet eine darstellende matrix,
  nach basisaenderung der bideterminanten
  modular
  um die übliche bezeichnung zu bekommen, wird die
  conjugierte partition genommen
  */
/* es wird nur die erste standard bi determinant ausgerechnet, die übrigen mit operate
   perm 
   dabei wird die permutation genommen die von SYT 0 zu SYT i führt */

/* es wird keine ff arithmetik verwendet */

#include "def.h"
#include "macro.h"

/* standard bideterminanten */
/* polynom indiziert mit integer matrix */
/* */
/* basis fuer specht modul mit sbd */

static OP zero_one_matrices = NULL;
static init_zero_one(OP part);
static close_zero_one();

static INT operate_perm_spaltenmatrix_new(a,b,c) OP a,b,c;
/* vertausch spalten gemaess der permutation */
/* spalte 0 nur wenn permutation auch 0 enthaelt */
/* AK 080802 */
{
    INT erg = OK;
    INT i,j;
    CTO(PERMUTATION,"operate_perm_spaltenmatrix(1)",a);
    CTTO(INTEGERMATRIX,MATRIX,"operate_perm_spaltenmatrix(2)",b);
    CE3(a,b,c,operate_perm_spaltenmatrix);
    SYMCHECK(S_P_LI(a) > S_M_LI(b),
        "operate_perm_spaltenmatrix: permutation degree too big");
    COPY(b,c);
    for (j=0;j<S_P_LI(a);j++)
    for (i=0;i<S_M_HI(b);i++)
        CLEVER_COPY(S_M_IJ(b,i,j), S_M_IJ(c,i,S_P_II(a,j)-1));

    CTTO(INTEGERMATRIX,MATRIX,"operate_perm_spaltenmatrix(e-3)",c);
    ENDR("operate_perm_spaltenmatrix");
}                                                                                             

static INT println_bid(a) OP a;
{
    OP z;
    INT i,j;
    if (NULLP(a)) { printf("empty bideterminant"); }
    else{
        FORALL(z,a,{
           print(S_MO_K(z)); printf(" [");
           for (i=1;i<S_M_HI(S_MO_S(z));i++) 
           for (j=1;j<S_M_LI(S_MO_S(z));j++) 
                print(S_M_IJ(S_MO_S(z),i,j));
           printf("] ");
        });
    }
    
    printf("\n");zeilenposition=0;
}

static INT make_basis(e,prim,v) OP e; OP prim;
/* the matrix e will be transformed into a basis mod prim using
   row transformations 
   the number of rows (= dimension ) may be smaller  at the end
*/
    OP v; /* vector mit zeilen nummern der original matrix
             die in die basis gehen   AK 210703 */
{
    INT i,j,k,l;
    INT erg = OK;
    OP d,c;
    
    CTO(MATRIX,"make_basis(1)",e);
    d = CALLOCOBJECT();
    c = CALLOCOBJECT();

    if (v!=NULL)
    { /* AK 210703 */
    m_il_v(S_M_HI(e),v);
    for (i=0;i<S_V_LI(v);i++) M_I_I(i,S_V_I(v,i));
    /* v initialized to 0.1.2.3.... */
    }

    if (S_M_HI(e) < 2) 
        {
        if (NULLP(e)) k=0; else k=1;
        goto a3;
        }
    
    
    j=0; k = 0;
a2:
    if (j == S_M_LI(e)) goto a3; 
    for (i=k;i<S_M_HI(e);i++)
        if (not NULLP(S_M_IJ(e,i,j))) break;
    if (i== S_M_HI(e))  /* in spalte j kein eintrag != 0 */
        { j++; goto a2; }
    change_row_ij(e,i,k);
    if (v!=NULL) SWAP(S_V_I(v,i),S_V_I(v,k)); /*AK 210703*/
    
    /* am platz k,j ist jetzt ein eintrag != 0 */
    /* in den zeilen drunter eine null an den platz in der spalte j */
    
    for (i=k+1;i<S_M_HI(e); i++)
        {
        if (NULLP(S_M_IJ(e,i,j))) continue;
    
nochmal:
        for (l=j;l<S_M_LI(e);l++)
            {
            ADD_APPLY(S_M_IJ(e,k,l),S_M_IJ(e,i,l));
            M_I_I(S_M_IJI(e,i,l)%S_I_I(prim),S_M_IJ(e,i,l));
            }
        if (! NULLP(S_M_IJ(e,i,j))) goto nochmal;
        }
    
    k++; j++; goto a2;
a3:
    /* k ist laenge der basis = dimension */
    for (i=k;i<S_M_HI(e);i++)
    for (j=0;j<S_M_LI(e);j++)
        FREESELF(S_M_IJ(e,i,j));
    M_I_I(k,S_M_H(e));
    if (v!=NULL) M_I_I(k,S_V_L(v)); /*AK 210703*/
    
    FREEALL(c);
    FREEALL(d);
    ENDR("make_basis");
}

static INT decompose_matrix(in,basis,mat,prim) OP in,basis,mat;OP prim;
{
    INT erg =  OK,i,j,k;
    CTO(VECTOR,"decompose_matrix(1)",in);
    CTO(MATRIX,"decompose_matrix(2)",basis);
    
    /* basis ist obere dreiecksmatrix */

    m_ilih_nm(S_V_LI(in),S_V_LI(in),mat);
    for (i=0;i<S_V_LI(in);i++)
        {
        OP leading_term;
        OP p,t,ko;
        INT l;
        p = CALLOCOBJECT();
        COPY(S_V_I(in,i),p);
        j = 0; k = 0;
aa:
        for (;j<S_V_LI(p);j++)
            if (not NULLP(S_V_I(p,j))) break;
        if (j==S_V_LI(p)) goto ee; 
    
    /* an der stelle j ist ein eintrag != null, es muss ein basis 
       element k geben was als ersten eintrag != 0 was an der stelle j hat */

bb:
        if (k == S_M_HI(basis))  error("decompose_matrix: could not decompose");
        if (NULLP(S_M_IJ(basis,k,j))) { k++; goto bb; }
        for (l=0;l<j;l++) 
            if (not NULLP(S_M_IJ(basis,k,l))) { k++; goto bb; } 
    
    /* der basis vektor k geht ins ergenis */

        t = CALLOCOBJECT();
        ko = CALLOCOBJECT();
        select_row(basis,k,t);
    
        M_I_I(1,ko);
        while ( (S_I_I(ko) * S_M_IJI(basis,k,j) )%S_I_I(prim) != S_V_II(p,j))
            INC_INTEGER(ko);
        COPY(ko,S_M_IJ(mat,k,i));
        M_I_I(-S_I_I(ko),ko);
        MULT_APPLY(ko,t);
        ADD_APPLY(t,p);
        for (l=0;l<S_V_LI(p);l++)
            {
            INT eintrag;
            eintrag = S_V_II(p,l);
            eintrag %= S_I_I(prim);
            if (eintrag < 0) eintrag += S_I_I(prim);
            M_I_I(eintrag, S_V_I(p,l));
            }
        FREEALL(ko);
        FREEALL(t);
        goto aa;
ee:
        FREEALL(p);
        }   /* end for */
    ENDR("decompose_matrix");
}



static INT get_dg(b,e,c,prim) OP b,e,c;OP prim;
/* berechnet die modulare darstellung */
/* dabei ist b die permutation, e die basis des moduls
   c wird matrix */
{
    OP d,a;
    INT erg = OK;
    INT i,j;
    
    if (S_M_HI(e) == 0) {
        /* z.b. part = 11....111 */
        m_ilih_m(0,0,c);
        goto endr_ende;
        }

    SYMCHECK(zero_one_matrices==NULL,"get_dg:internal error");

    a = CALLOCOBJECT();
    d = CALLOCOBJECT();
    m_il_v(S_M_HI(e),d);
    m_il_v(S_M_LI(e),a);
    for (j=0;j<S_V_LI(a);j++)
         b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),S_V_I(a,j));
     
    for (i=0;i<S_V_LI(d);i++)
        {
        for (j=0;j<S_V_LI(a);j++)
            {
            CLEVER_COPY(S_M_IJ(e,i,j),S_MO_K(S_V_I(a,j)));
            operate_perm_spaltenmatrix_new(b,S_V_I(zero_one_matrices,j),S_MO_S(S_V_I(a,j)));
            }
        qsort_vector(a);
        m_il_v(S_V_LI(a),S_V_I(d,i));
        for (j=0;j<S_V_LI(a);j++)
            COPY(S_MO_K(S_V_I(a,j)), S_V_I(S_V_I(d,i),j));
        }
 
/* im vector d stehen die bideterminanten nach anwendung der permutation
   diese jetzt zerlegen in der basis in e
   dies ergibt die zeilen der darstellenden matrix
*/

    FREEALL(a);
    decompose_matrix(d,e,c,prim);   
    FREEALL(d);
    ENDR("get_dg");
}

static INT specht_basis_mod_p(e,p) OP e,p;
/* die basis des specht moduls wird mod p gerechnet,
   die koeff sind nun FF 

   und es ist normaleweise keine basis mehr */
{
    INT i,j,erg =OK;

    for (i=0;i<S_M_HI(e);i++)
    for (j=0;j<S_M_LI(e);j++)
        {
        INT eintrag ;
        eintrag = S_M_IJI(e,i,j) % S_I_I(p);
        if (eintrag < 0) eintrag += S_I_I(p); 
        M_I_I(eintrag, S_M_IJ(e,i,j));
        }
    ENDR("specht_basis_mod_p");
}

static INT get_specht_basis_of_sbd(a,e)  OP a,e;
/* basis des specht moduls aus 
   P-symmetrizied sbd */
/* koeff sind INTEGER, e is matrix zeilenweise sortiert wie in zero_one_matrices */
/* input is partition */
{
    OP bb,cc,aa,z,dd;
    OP c,d;
    INT i,j,k;
    INT erg = OK;
    CTO(PARTITION,"get_specht_basis_of_sbd(1)",a);
    CALLOCOBJECT5(cc,c,d,bb,dd);
    
    makevectorofSYT(a,cc);
    m_lh_nm(S_V_L(zero_one_matrices),S_V_L(cc),e);
     
    m_u_t(a,bb);
    for (i=0;i<S_PA_LI(a);i++)
    for (j=0;j<S_PA_II(a,S_PA_LI(a)-1-i);j++)
        M_I_I(i+1,S_T_IJ(bb,i,j));
     
    P_symmetrized_bideterminant(bb,S_V_I(cc,0),d);
    
    k=0;
    FORALL(z,d,{
    m_ilih_m(S_M_LI(S_MO_S(z))-1,S_M_HI(S_MO_S(z))-1,dd);
    C_O_K(dd,INTEGERMATRIX);
    for (i=0;i<S_M_HI(S_MO_S(z))-1;i++)
    for (j=0;j<S_M_LI(S_MO_S(z))-1;j++)
        M_I_I(S_M_IJI(S_MO_S(z),i+1,j+1),S_M_IJ(dd,i,j));
    swap(dd,S_MO_S(z));
    while (not EQ(S_MO_S(z),S_V_I(zero_one_matrices,k))) k++;
    COPY(S_MO_K(z),S_M_IJ(e,0,k));
    });
    
    t_LIST_VECTOR(d,d);
    
     
    copy(d,dd);
    for (i=1;i<S_M_HI(e);i++)
        {
        OP ddd;
        OP aaa = S_V_I(cc,i);
        OP aa = S_V_I(cc,0);
        INT ii;
        ddd = callocobject();
        weight(aa,c);
        m_il_p(S_I_I(c),ddd);
        for (ii=0;ii<S_T_HI(aa);ii++)
        for (j=0;j<=zeilenende(aa,ii);j++)
            M_I_I(S_T_IJI(aaa,ii,j),S_P_I(ddd,S_T_IJI(aa,ii,j)-1));
     
        /* ddd is permutation to go from SYT at place 0 to SYT at place i in vector e */
        
        for (j=0;j<S_V_LI(d);j++)
            {
            copy(S_MO_K(S_V_I(d,j)), S_MO_K(S_V_I(dd,j)));
            operate_perm_spaltenmatrix_new(ddd,S_MO_S(S_V_I(d,j)),S_MO_S(S_V_I(dd,j)));
            }
     
        freeall(ddd);
        qsort_vector(dd);
    
        k=0;
        for (j=0;j<S_V_LI(dd);j++)
            {
            while (not EQ(S_MO_S(S_V_I(dd,j)),S_V_I(zero_one_matrices,k))) k++;
            COPY(S_MO_K(S_V_I(dd,j)),S_M_IJ(e,i,k));
            }                            
        }
    FREEALL5(cc,bb,dd,c,d);
    ENDR("get_specht_basis_of_sbd");
}

INT basis_mod_dg(prim,part,e) OP part,prim,e;
/* computes the basis e of the modular irreducible sn-module labeled by part */
/* AK 270503 */
/* AK 070704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"basis_mod_dg(1)",prim);
    CTO(PARTITION,"basis_mod_dg(2)",part);
    CE3(prim,part,e,basis_mod_dg);



    {
    OP a;
    init_zero_one(part);
    a = CALLOCOBJECT();
    conjugate(part,a);
    get_specht_basis_of_sbd(a,e);
    FREEALL(a);


    specht_basis_mod_p(e,prim); /*entires are now mod p*/
    make_basis(e,prim,NULL);
    }
    
    ENDR("basis_mod_dg");
}


INT kk_280604 (part,e,prim) OP part,e,prim;
/* computes the matrix e
   whose rows are basis of the irreducible sn-module labeled by part */
/* AK 270604 */
{
    INT i,j,erg =OK;
    OP a,temp;

    init_zero_one(part);
    a = callocobject();
    conjugate(part,a);
    get_specht_basis_of_sbd(a,e);
        if (S_I_I(prim)!=0){ /*dann konvertiere nach Fp*/
            for (i=0;i<S_M_HI(e);i++){ /*konvertiere jetzt die Matrix entries in FF-Elemente*/
                        for (j=0;j<S_M_LI(e);j++){
                                temp=S_M_IJ(e,i,j);
                                t_INTEGER_FF(temp,prim,S_M_IJ(e,i,j));
                        }
                }
        }
        freeall(a);
    close_zero_one();
}


static INT ss; /*size*/
static INT mycmp(a,b) OP a,b;
{
INT i;
for (i=0;i<ss;i++) if (S_I_I(a+i) < S_I_I(b+i)) return 1;
                   else if (S_I_I(a+i) > S_I_I(b+i)) return -1;
;
return 0;
}

static INT get_symm_specht_poly(a,i,c) OP a,c; INT i;
/* AK 210703 */
/* ite reihe von a ist symmetrized specht polynom 
   write it as object of type POLYNOM */
{
    INT j,erg = OK;
    init(HASHTABLE,c);
    for (j=0;j<S_M_LI(a);j++)
        {
        if (S_M_IJI(a,i,j)!=0)
        {
        OP d,m;
        INT k,l;
        m=S_V_I(zero_one_matrices,j);
        d=CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
        M_I_I(S_M_IJI(a,i,j),S_MO_K(d));
        m_il_nv(S_M_LI(m),S_MO_S(d));
        for (k=0;k<S_M_LI(m);k++)
            for (l=1;l<S_M_HI(m);l++)
                if (S_M_IJI(m,l,k) == 1) { M_I_I(l,S_MO_SI(d,k)); break; }


        insert(d,c,NULL,NULL);
        }
        }
    t_HASHTABLE_POLYNOM(c,c);
    ENDR("get_symm_specht_poly");
}

static init_zero_one(part) OP part;
/* this vector of zero one matrices are the possible exponent in the 
   sbd */
{
    OP a,b,c,d;INT erg=OK;
    zero_one_matrices=callocobject(); /*global*/
    CALLOCOBJECT4(a,b,c,d);
    erg += weight_partition(part,b);
    last_partition(b,c);
    conjugate(part,a);
    reverse_vector(S_PA_S(a),d);
    all_01_matrices(d,c,zero_one_matrices);
    FREEALL4(a,b,c,d);
    qsort_vector(zero_one_matrices);
    ENDR("internal:init_zero_one");
}
static close_zero_one()
{
    INT erg =OK;
    erg+=freeall(zero_one_matrices); zero_one_matrices=NULL;
    ENDR("internal:close_zero_one");
}
INT makevectorofsymspecht_poly(part,v) OP part,v;
/* AK 300703 */
/* produces a vector of symmetrized specht polynomials
   these are basis of the ordinary specht module
   and generator of the modular specht module
*/
{
    INT erg = OK;
    CTO(PARTITION,"makevectorofsymspecht_poly(1)",part);
    CE2(part,v,makevectorofsymspecht_poly);
    {OP a,e;INT i;
    init_zero_one(part);
    CALLOCOBJECT2(a,e);
    conjugate_partition(part,a);
    get_specht_basis_of_sbd(a,e); 
    m_l_v(S_M_H(e),v);
    for (i=0;i<S_M_HI(e);i++)
        get_symm_specht_poly(e,i,S_V_I(v,i));
    
    FREEALL2(a,e);
    close_zero_one();
    }
    ENDR("makevectorofsymspecht_poly");
}

INT code_mod_into_ord(prim,part,f) OP prim,part,f;
/* AK 210703 embedding of the mod into ord spect module
      compute mod basis, take the original symmetrized specht 
      polynomials which become bases, write them in the basis
      of the non symmetrized specht polynomials
      read it as coeff in N, get code */
{
    INT erg = OK,i,j,k;
    OP a,b,c,d,e,v;
    CTO(INTEGER,"code_mod_into_ord(1)",prim);
    CTO(PARTITION,"code_mod_into_ord(2)",part);

    CALLOCOBJECT5(a,b,c,d,v);
    init_zero_one(part);
    conjugate(part,a);
    FREEALL3(b,c,d);
    e = CALLOCOBJECT();
    get_specht_basis_of_sbd(a,e);
    copy(e,a);

    specht_basis_mod_p(e,prim); /*entires are mod p*/
    make_basis(e,prim,v);  /* v is vector 1=in basis of mod */

    CALLOCOBJECT2(c,d);

    m_ilih_nm(S_M_HI(a),S_V_LI(v),f);
    conjugate(part,e);
    makevectorofspecht_poly(e,d);
    /* compute the specht polynomials according to the rows 
       indexed in v */
    for (i=0;i<S_M_HI(f);i++)
        {
        INT j;
        get_symm_specht_poly(a,S_V_II(v,i),c);
        mod(c,prim,c);
aaa:
        if (not NULLP(c))
            for (j=0L;j<S_V_LI(d); j++)
                if (EQ(S_PO_S(c),S_PO_S(S_V_I(d,j))))
                    {
                    CLEVER_COPY(S_PO_K(c),S_M_IJ(f,i,j));
                    FREESELF(e);
                    MULT(S_PO_K(c),S_V_I(d,j),e);
                    erg += sub_apply(e,c); /* c = c -e */
                    mod(c,prim,c);
                    goto aaa;
                    }

        }
    FREEALL4(e,d,c,v);
    erg+=freeall(zero_one_matrices); zero_one_matrices=NULL;
    ENDR("code_mod_into_ord");
} 

INT code_mod_into_ord2(prim,part,f) OP prim,part,f;
/* AK 300703 embedding of the mod into ord specht module
      compute mod basis, take this basis
       write the in basis
      of the non symmetrized specht polynomials
      read it as coeff in N, get code */
/* as we take the same subspace the minimal distance in code_mod_into_ord2
and code_mod_into_ord are equal !! */
{
    INT erg = OK,i,j,k;
    OP a,b,c,d,e,v;
    CTO(INTEGER,"code_mod_into_ord2(1)",prim);
    CTO(PARTITION,"code_mod_into_ord2(2)",part);

    CALLOCOBJECT5(a,b,c,d,v);
    init_zero_one(part);
    conjugate(part,a);
    FREEALL3(b,c,d);
    e = CALLOCOBJECT();
    get_specht_basis_of_sbd(a,e);
    copy(e,a);

    specht_basis_mod_p(e,prim); /*entires are mod p*/
    make_basis(e,prim,v);  /* v is vector 1=in basis of mod*/
    CALLOCOBJECT2(c,d);

    m_ilih_nm(S_M_HI(a),S_V_LI(v),f);conjugate(part,d);
    makevectorofspecht_poly(d,d);
    /* compute the specht polynomials according to the rows
       in e */
    for (i=0;i<S_M_HI(f);i++)
        {
        INT j;
        get_symm_specht_poly(e,i,c);
        mod(c,prim,c);
aaa:
        if (not NULLP(c))
            for (j=0L;j<S_V_LI(d); j++)
                if (EQ(S_PO_S(c),S_PO_S(S_V_I(d,j))))
                    {
                    CLEVER_COPY(S_PO_K(c),S_M_IJ(f,i,j));
                    FREESELF(v);
                    MULT(S_PO_K(c),S_V_I(d,j),v);
                    erg += sub_apply(v,c); /* c = c -v */
                    mod(c,prim,c);
                    goto aaa;
                    }

        }
    FREEALL4(e,d,c,v);
    erg+=freeall(zero_one_matrices); zero_one_matrices=NULL;
    ENDR("code_mod_into_ord2");
}


INT embedding_mod_into_ord(prim,part,f) OP prim,part,f;
/* for the embedding of modular irreducible 
   into irreducible of ordinary */
/* the modular symmetrized specht polynomials are written in the basis */
/* of the symmetrized specht polynomials */
/* AK 170703 for arbitrary prime */
{
    INT erg = OK,i,j,k;
    OP a,b,c,d,e;
    CTO(INTEGER,"basis_mod_dg(1)",prim);
    CTO(PARTITION,"basis_mod_dg(2)",part);
    CE3(prim,part,f,basis_mod_dg);

    b = CALLOCOBJECT();
    weight(part,b);


    a = CALLOCOBJECT();
    conjugate(part,a);
    init_zero_one(part);
    e = CALLOCOBJECT();
    get_specht_basis_of_sbd(a,e);
    FREEALL(a);



    specht_basis_mod_p(e,prim);
    FREEALL(zero_one_matrices);
    c = CALLOCOBJECT();
    COPY(e,c);
    make_basis(e,prim,NULL);
    /* write c in the basis of e*/

    /*sortiere e*/
    ss = S_M_HI(e);
    qsort(S_M_S(e),S_M_HI(e),sizeof(struct object)*S_M_LI(e),mycmp);

    m_ilih_nm(S_M_HI(e),S_M_HI(c),f);

    d = CALLOCOBJECT();
    m_il_v(S_M_HI(e),d);
    for (i=0;i<S_M_HI(e);i++)
    for (j=0;i<S_M_LI(e);j++) if (S_M_IJI(e,i,j) != 0) {M_I_I(j,S_V_I(d,i)); break; }

    /* vector mit erster position != 0 */

    b = CALLOCOBJECT();
    m_il_v(S_M_LI(c),b);
    for (i=0;i<S_M_HI(f);i++)
        {
        INT ko;
        /* zeile aus c */
        for (j=0;j<S_V_LI(b);j++) COPY(S_M_IJ(c,i,j),S_V_I(b,j));
again:
        /* erster eintrag != 0 in b */
        for (j=0;j<S_V_LI(b);j++) if (S_V_II(b,j) != 0) break;
        if (j==S_V_LI(b)) {
                            continue; }
        /* welcher basis vector muss abgezogen werden? */
        for (k=0;k<S_V_LI(d); k++) if (S_V_II(d,k)==j) break;
        if (k==S_V_LI(d)) error("kk");
        ko = 1;
        while ((ko*S_M_IJI(e,k,j))%S_I_I(prim)  != S_V_II(b,j)) ko++;
        M_I_I(ko, S_M_IJ(f,i,k)); /* koeff schreiben*/
                                 /* aendern fuer prim != 2*/
        /* k te zeile abziehen*/
        ko = S_I_I(prim)-ko;
        for (;j<S_V_LI(b);j++)
             M_I_I( (S_V_II(b,j)+ko*S_M_IJI(e,k,j))%S_I_I(prim), S_V_I(b,j));
        goto again;
        }
      
    FREEALL(b);
    FREEALL(d);

    FREEALL(c);
    FREEALL(e);
    transpose(f,f);
    ENDR("embedding_mod_into_ord");
}


INT mod_dg_sbd(prim,part,perm,mat) 
   OP prim,part,perm,mat;
/* AK 020902 
   computes a modular irreducible representation
   using standard bideterminants */
{
    INT erg = OK;
    OP a,b,c,d,e;
    CTO(INTEGER,"mod_dg_sbd(1)",prim);
    CTO(PARTITION,"mod_dg_sbd(2)",part);
    CTO(PERMUTATION,"mod_dg_sbd(3)",perm);
    CE4(prim,part,perm,mat,mod_dg_sbd);
    
    b = CALLOCOBJECT();
    weight(part,b); 
    
    if (S_P_LI(perm) != S_I_I(b)) {
        erg += error("mod_dg_sbd: degree perm != weight part");
        FREEALL(b);
        goto endr_ende;
        }
    FREEALL(b);
    
    e = CALLOCOBJECT();
    basis_mod_dg(prim,part,e);
    get_dg(perm,e,mat,prim);
    close_zero_one();
    FREEALL(e);
    ENDR("mod_dg_sbd");
}
