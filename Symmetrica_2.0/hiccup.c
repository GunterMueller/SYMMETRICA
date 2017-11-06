/* SYMMETRICA hiccup.c */
/* HICCUP module to calculate explicit representation matrices
   of the Hecke algebra of type A. Uses the Specht module
   generalisation described by R.C.King and B.G.Wybourne in
   J.Math.Phys.33(1), pp4-14 (1992).
   The Specht modules are irreducible in the generic case when
   q is not a root of unity. Otherwise they may reduce.
   Routines which deal with those non-generic irreducibles which
   are labelled by two-rowed partitions start from about line 1210.

   Programmed by Trevor Welsh, Bayreuth, November 1995.
                               (Modified 12/1/96.)

   Data structure for q-linear combinations of tableaux is as follows:

   LIST --> LIST (next)
	--> MONOM   --> TABLEAUX
		    --> MONOPOLY (LIST) --> MONOPOLY (next)
				        --> MONOM   --> INTEGER (power)
						    --> INTEGER (coefficient).

   A similar structure is used for q-linear combinations of permutations. 

*/

#define NORMALISE 1  /* if 1, monopolies are tidied up wrt roots of unity */

#include "def.h"
#include "macro.h"

static OP children=NULL; /* AK 150197 */


/* function prototypes for generic representation routines */

#ifdef UNDEF
	INT generate_standard_tableaux (OP partition, OP std);
	INT hecke_generator_reps (OP partition, OP vector);
	INT represent_hecke_element (OP partition, OP hecke, OP mat);
	INT build_lc (OP schizo, OP list);
	INT hecke_action_lc_on_lc (OP tableaux, OP hecke, OP result);
	INT standardise_cold_tableaux_list (OP tableaux, OP result);
	INT input_tableau (OP partit, OP tab);
	INT input_lc_permutations (OP save);
	INT substitute_one_matrix (OP mat);
	INT substitute_one_monopoly (OP mp);

	INT set_garnir_parameters (OP partition);
	INT free_garnir_parameters (void);
	INT set_useful_monopolies (void);
	INT free_useful_monopolies (void);
	set_multiplier (OP extra);
	hecke_action (OP tableau, OP permutation, OP list);
	INT hecke_action_perm_on_lc (OP tableaux, OP permutation);
	INT find_non_rowstandard_pos (OP tableau, INT *r, INT *c);
	INT columns_standardise_tableau (OP tableau, INT *sig);
	INT column_standardise_tableau (OP tableau, INT col, INT *sig);
	static int standardise_tableau_list (OP list, OP expression);
	static int standardise_tableau (OP tableau, OP expression);
	garnir_juggle (OP tableau, INT power, INT coeff);
	static garnir_generate (INT head, INT wag);
	static garnir_result (OP tableau, OP mp_coeff, OP acc_list);
	INT enter_list_to_matrix (OP matrix, INT column, OP standard, OP express);
	static INT construct_mo_mp (INT power, INT coeff, OP mo_po);
	memory_check (void *query);


	/* function prototypes for non-generic representation routines */

	INT root_dimension (OP partition, OP p_root, OP dim);
	INT generate_root_tableaux (OP partition, OP p_root, OP std);
	INT hecke_root_generator_reps (OP partition, OP p_root, OP vector);
	INT root_represent_hecke_action (OP partition, 
	OP p_root, OP hecke, OP mat);
	INT root_standardise_cold_tableaux_list (OP tableaux, OP p_root, OP result);

	INT set_root_parameters (OP partition, OP p_root);
	INT free_root_parameters (void);
	INT find_non_root_standard_pos (OP tableau);
	set_root_multiplier (OP extra);
	root_standardise_tableau_list (OP list, OP expression);
	root_standardise_tableau (OP tableau, OP expression);
	root_juggle (OP tableau, INT power, INT coeff);
	strip_juggle (OP tableau, INT power, INT coeff);
	root_garnir_result (OP tableau, OP mp_coeff, OP acc_list);
	INT root_normalise_monopoly (OP mono);
	generate_sym_tableaux_list (INT piece, OP sym_list);
	coset_generate (INT head, INT wag);
	INT remove_mp_qnumber_fac (OP mp, INT qn);
	INT remove_vec_qnumber (INT qn);


	/* function prototypes for matrix representation checking routines */

	INT check_hecke_generators (OP vector, OP p_root, INT flag);
	INT check_hecke_quadratic (OP mat, OP p_root, INT flag);
	INT check_braid (OP mat1, OP mat2, OP p_root, INT flag);
	INT check_commute (OP mat1, OP mat2, OP p_root, INT flag);
	INT set_cyclotomic_parameters (OP p_root);
	INT free_cyclotomic_parameters ();
	INT check_zero_matrix (OP mat, OP p_root);


	/* function prototypes to add or multiply hecke algebra elements */

	INT hecke_add (OP hecke1, OP hecke2, OP result);
	INT hecke_mult (OP hecke1, OP hecke2, OP result);
	INT hecke_scale (OP hecke, OP power, OP coeff);

	INT hecke_action_perm_on_hecke (OP heck, OP permutation);


	/* function prototypes for some debugging routines */

	strip_buggle (OP tableau);
	dump_lc_list (OP list);
	dump_monopoly (OP mp);
#endif
static int standardise_tableau ();
static int standardise_tableau_list();
static int garnir_juggle ();
static INT free_garnir_parameters();
static INT set_garnir_parameters();
static int garnir_generate ();
static int garnir_result ();
static INT construct_mo_mp ();
static void hecke_accum (OP perm, OP mp_coeff, OP acc_list);

#ifdef TABLEAUXTRUE
INT generate_standard_tableaux (partition,std)
	OP partition;
	OP std;

/* generates all the S_n standard tableaux for the partition. 
   returns the number of standard tableaux, else ERROR.
*/

{
	OP t,last,n;
	INT count=0;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("generate_standard_tableaux() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	weight(partition,n=callocobject());
	last_partition(n,last=callocobject());
	kostka_tab(partition,last,std);

	freeall(n);
	freeall(last);

	if (!empty_listp(std))
		for (t=std;t!=NULL;t=S_L_N(t),count++);

	return(count);
}
#endif /* TABLEAUXTRUE */

#ifdef PARTTRUE
INT hecke_generator_reps ( partition,  vector)
	OP partition;
	OP vector;

/* for the given partition produces a vector of matrices, the ith
   of which represents the ith generator s_i.
*/

{
	INT i,ni;
	OP n,p,lc,mat;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("hecke_generator_reps() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	weight(partition,n=callocobject());
	ni=S_I_I(n);
	freeall(n);

	/* construct and intialize a permutation which will be passed to
      the representing routines. */

	m_il_p(ni,p=callocobject());
	for (i=0;i<ni;i++)
		m_i_i(i+1,S_P_I(p,i));

	/* encase this permutation in a linear combination list */

	build_lc(p,lc=callocobject()); /* p part of lc */

	/* construct the vector to build the results */

	m_il_v(--ni,vector);

	/* loop through all simple transpositions, obtaining representations */

	for (i=0;i<ni;i++)
	{
		C_I_I(S_P_I(p,i),i+2);
		C_I_I(S_P_I(p,i+1),i+1);

		represent_hecke_element(partition,lc,s_v_i(vector,i));

		C_I_I(S_P_I(p,i),i+1);
	}

	freeall(lc);
	return(OK);
}
#endif /* PARTTRUE */

INT represent_hecke_element (partition, hecke, mat) OP partition;
	OP hecke;
	OP mat;

/* Constructs the explicit (Specht) matrix representative in that
   representation labelled by partition, of the element
   of the hecke algebra A_{n-1} obtained by canonically mapping
   the list of permutations from the symmetric group.
*/

{
	INT k;
	INT erg = OK;
	OP temp,e,list,std_tableaux,t,tab_list,tab_cop,go_perm,perm_cop,coeff;

	/* validate parameters */
	CTO(PARTITION,"represent_hecke_element",partition);
	CTO(LIST,"represent_hecke_element",hecke);


	if (  !empty_listp(hecke) )
	{
		CTO(MONOM,"represent_hecke_element",S_L_S(hecke));
		CTO(PERMUTATION,"represent_hecke_element",S_MO_S(S_L_S(hecke)));
	}

	/* construct the list of standard tableaux and 
      make a matrix of the right size for the results */

	std_tableaux=callocobject();
	k=generate_standard_tableaux(partition,std_tableaux);
	m_ilih_m(k,k,mat);
	/* set the partition parameters */
	set_garnir_parameters(partition);
	/* run through the standard tableaux, acting on each with the
      permutation list, standardising the result and entering that
      result into the appropriate column of the matrix. */
	for (t=std_tableaux,k=0;t!=NULL;t=S_L_N(t),k++)
	{
		list=callocobject();       /* to accumualte results from all perms */
		init(LIST,list);
		tab_list=callocobject();   /* to store results of each action */
		for (go_perm=hecke;go_perm!=NULL;go_perm=S_L_N(go_perm))
		{
			tab_cop=callocobject();
			erg += copy_tableaux(S_L_S(t),tab_cop);
			erg += build_lc(tab_cop,tab_list); /* tab_cop part of list */
			perm_cop=callocobject();
			erg += copy_permutation(S_MO_S(S_L_S(go_perm)),perm_cop);
			hecke_action_perm_on_lc(tab_list,perm_cop); /* perm_cop is freed in hecke_action_perm_on_lc */

			for (temp=tab_list;temp!=NULL;temp=S_L_N(temp))
			{
				coeff=callocobject();
				erg += mult_monopoly_monopoly(S_MO_K(S_L_S(go_perm)),S_MO_K(S_L_S(temp)), coeff);
				garnir_result(S_MO_S(S_L_S(temp)),coeff,list); /* coeff is destroyed */
			}
			freeself(tab_list);
		}
		erg += freeall(tab_list);

		e = callocobject();
		erg += init(LIST,e);
		standardise_tableau_list(list,e);
		freeall(list);

		enter_list_to_matrix(mat,k,std_tableaux,e);
		erg += freeall(e);
	}

	free_garnir_parameters();
	erg += freeall(std_tableaux);
	ENDR("represent_hecke_element");
}

INT tex_hecke_monopoly(a) OP a;
/* to output an element as q-polynomial */
/* AK 201296 */
{
	OP z;
	z = a;
	if (S_O_K(a) != MONOPOLY)
		return tex(a);
	while (z != NULL)
	{
		if (not einsp(S_MO_K(S_L_S(z))))
		{
			if (negeinsp(S_MO_K(S_L_S(z))))
				fprintf(texout," - ");
			else
				tex (S_MO_K(S_L_S(z)));
		}
		fprintf (texout," q^{%ld} ",S_I_I(S_MO_S(S_L_S(z))));
		z = S_L_N(z);
		if (z != NULL)
		{
			if (posp(S_MO_K(S_L_S(z))))
				fprintf(texout,"+");
		}
	}
	return OK;
}


INT hecke_dg(part,perm,res) OP part,perm,res;
{
	INT erg = OK;
	OP c,d;
	CTO(PARTITION,"hecke_dg",part);
	CTO(PERMUTATION,"hecke_dg",perm);

	c = callocobject();
	d = callocobject();
	erg += copy(perm,d);
	erg += build_lc (d,c); /* d part of c */
	erg += represent_hecke_element(part,c,res);
	erg += freeall(c);
	ENDR("hecke_dg");
}

INT build_lc ( schizo,  list)
	OP schizo;
	OP list;

/* The entered object (schizo), which is either a TABLEAUX or a PERMUTATION,
   is converted into a linear combination of such objects - the linear
   combination consists of one term (schizo) with MONOPOLY coefficient
   1. schizo is incoporated into the list and should NOT be subsequently
   freed alone.
*/

{
	OP mo_mp,monom;
	INT erg = OK;
	CTTO(TABLEAUX,PERMUTATION,"build_lc",schizo);
	erg += construct_mo_mp((INT)0,(INT)1,mo_mp=callocobject());
	erg += b_sk_mo(schizo,mo_mp,monom=callocobject());
	erg += b_sn_l(monom,NULL,list);
	ENDR("build_lc");
}


INT hecke_action_lc_on_lc ( tableaux,  hecke,  result)
	OP tableaux;
	OP hecke;
	OP result;

/* Applies the linear combination of hecke algebra elements to the
   linear combination of tableaux. Neither of the inputs is changed.
   All initialisation is taken care of, so the user just has to 
   create a list of tableaux, and a list of permutations
   then submit it here. The result is added to result.
   */

{
	OP go_perm,coeff,temp,imitate,perm_cop;

	/* first validate the inputs */

	if (S_O_K(tableaux)!=LIST 
	    || (!empty_listp(tableaux)
	    && (S_O_K(S_L_S(tableaux)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(tableaux))) != TABLEAUX )))
	{
		error("hecke_action_lc_on_lc() did not receive a linear combination of tableaux as it was expecting!\n");
		return(ERROR);
	}

	if (S_O_K(hecke)!=LIST 
	    || (!empty_listp(hecke)
	    && (S_O_K(S_L_S(hecke)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke))) != PERMUTATION )))
	{
		error("hecke_action_lc_on_lc() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	/* if result is not already a list, then make it one */

	if (S_O_K(result)!=LIST)
		init(LIST,result);

	/* return if there is nothing to process */

	if (empty_listp(tableaux) || empty_listp(hecke))
		return(OK);

	set_garnir_parameters(s_t_u(S_MO_S(S_L_S(tableaux))));

	/* For each element of the permutation list, make a copy of the
      tableaux list, and act on it with a copy of the permutation.
      Then go though the resulting list of tableaux, multiplying
      them by the coefficient of the permutation, and accumulating
      them to result. */

	imitate=callocobject();
	for (go_perm=hecke;go_perm!=NULL;go_perm=S_L_N(go_perm))
	{
		copy_list(tableaux,imitate);
		copy_permutation(S_MO_S(S_L_S(go_perm)),perm_cop=callocobject());

		hecke_action_perm_on_lc(imitate,perm_cop); /* perm_cop freed in hecke_... */

		for (temp=imitate;temp!=NULL;temp=S_L_N(temp))
		{
			mult_monopoly_monopoly(S_MO_K(S_L_S(go_perm)),S_MO_K(S_L_S(temp)),
			    coeff=callocobject());
			garnir_result(S_MO_S(S_L_S(temp)),coeff,result); /* coeff is destroyed */
		}
		freeself(imitate);
	}
	freeall(imitate);
	free_garnir_parameters();
	return(OK);
}


INT standardise_cold_tableaux_list ( tableaux,  result)
	OP tableaux;
	OP result;

/* Similar to the function standardise_tableau_list(), but all initialisation
   is taken care of, so the user just has to create a list of tableaux,
   and then submit it here. The result is added to result which, if not
   already a list, is made into a list.
   tableaux is unchanged by this function.
*/

{
	OP a,imitate;

	/* first validate the input */

	if (S_O_K(tableaux)!=LIST 
	    || (!empty_listp(tableaux)
	    && (S_O_K(S_L_S(tableaux)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(tableaux))) != TABLEAUX )))
	{
		printf("standardise_cold_tableaux_list() did not receive a linear combination of tableaux as it was expecting!\n");
		return(ERROR);
	}

	/* if result is not already a list, then make it one */

	if (S_O_K(result)!=LIST)
		init(LIST,result);

	/* return if there is nothing to process */

	if (empty_listp(tableaux))
		return(OK);

	set_garnir_parameters(s_t_u(S_MO_S(S_L_S(tableaux))));
	imitate=callocobject();

	for (a=tableaux;a!=NULL;a=S_L_N(a))
	{
		set_multiplier(S_MO_K(S_L_S(a)));
		copy_tableaux(S_MO_S(S_L_S(a)),imitate);
		standardise_tableau(imitate,&result);
		freeself(imitate);
	}

	freeall(imitate);
	free_garnir_parameters();
	return(OK);
}

#ifdef TABLEAUXTRUE


INT input_tableau ( partit,  tab)
	OP partit;
	OP tab;

/* Requests a tableau from the user of the appropriate shape. A check
   is made on the entries. If they are not distinct and from 1...n,
   then ERROR is returned.
*/


{
	INT i,j,rows;
	INT *entries;
	OP w;

	if (S_O_K(partit)!=PARTITION)
	{
		printf("input_tableau() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	weight(partit,w=callocobject());
	entries=(INT*)SYM_calloc(S_I_I(w),sizeof(INT));

	m_u_t(partit,tab);

	printf("Please input tableau entries row by row, longest row first.\n");

	rows=s_t_hi(tab);
	for (i=0;i<rows;i++)
		for (j=0;j<S_T_UII(tab,rows-1-i);j++)
		{
			scan(INTEGER,S_T_IJ(tab,i,j));
			if (S_T_IJI(tab,i,j)<=S_I_I(w))
				entries[S_T_IJI(tab,i,j)-1]++;
		}

	/* now check that there are single entries 1,2,...,weight_of_partit. */

	for (i=S_I_I(w)-1;i>=0 && entries[i]==1;i--);
	if (i<0)
		return(OK);
	else
	{
		printf("Inappropriate tableau was entered!\n");
		return(ERROR);
	}
}
#endif /* TABLEAUXTRUE */


INT input_lc_permutations (save) OP save;

{
	char resp[8];
	OP a,b,c,perm,poly,monom,temp;

	init(LIST,save);

	a=callocobject();
	b=callocobject();

	do
	{
		fprintf(stderr,"Enter permutation (coefficient to follow):\n");
		scan(PERMUTATION,perm=callocobject());
		init(MONOPOLY,poly=callocobject());

		do
		{
			fprintf(stderr,"Enter exponent: \n");
			scan(INTEGER,a);
			fprintf(stderr,"Enter coefficient: \n");
			scan(INTEGER,b);

			m_skn_mp(a,b,NULL,c=callocobject());
			insert(c,poly,add_koeff,NULL);
			fprintf(stderr,"Current term is: \n");
			fprint(stderr,poly);
			fprintf(stderr," * ");
			fprintln(stderr,perm);

			fprintf(stderr,"continue adding to coefficient? \n");
			scanf("%6s",resp);

		}  while (resp[0]=='y');

		b_sk_mo(perm,poly,monom=callocobject());

		if (empty_listp(save))
		{
			c_l_s(save,monom);
		}
		else
		{
			b_ks_o(S_O_K(save),S_O_S(save),temp=callocobject());
			/* c_o_s(save,NULL); */
			c_o_k(save,EMPTY);
			b_sn_l(monom,temp,save);
		}

		fprintf(stderr,"continue adding terms? \n");
		scanf("%6s",resp);

	}  while (resp[0]=='y');

	freeall(a);
	freeall(b);
	return(OK);
}


INT substitute_one_matrix (mat) OP mat;

/* every entry in the matrix that is a MONOPOLY object is changed
   an INTEGER object having the value obtained by setting q=1 in
   the original entry. Returns an ERROR if a MATRIX is not passed.
*/

{
	INT i,j;

	if (S_O_K(mat)!=MATRIX)
	{
		printf("substitute_one_matrix() did not receive a matrix as it was expecting!\n");
		return(ERROR);
	}

	for (i=0;i<s_m_hi(mat);i++)
		for (j=0;j<s_m_li(mat);j++)
		{
			if (S_O_K(S_M_IJ(mat,i,j))==MONOPOLY)
				substitute_one_monopoly(S_M_IJ(mat,i,j));
		}
	return(OK);
}


INT substitute_one_monopoly (mp) OP mp;

/* replaces the MONOPOLY object with an INTEGER object obtained
   by setting q=1 in the original monopoly.
   Returns an ERROR if a MONOPOLY is not passed.
*/

{
	INT a=0;
	OP temp;

	if (S_O_K(mp)!=MONOPOLY)
	{
		error("substitute_one_monopoly() did not receive a monopoly as it was expecting!\n");
		return(ERROR);
	}

	if (!empty_listp(mp))
		for (temp=mp;temp!=NULL;temp=S_L_N(temp))
			a+=S_I_I(S_MO_K(S_L_S(temp)));
	m_i_i(a,mp);
	return(OK);
}



static INT *part,*conj,*entry_list;
static INT *garnir_sym,*garnir_inv;
static INT garnir_ready=0,no_rows,no_cols,garnir_len,no_boxs;
static INT lcol,rcol,grow,glength,gright,gleft;
static OP template;
static OP q_mp,qm1_mp;     /* monopolys storing q and q-1 */
static INT monopoly_ready=0;

static OP multiplier;      /* multiply by this prior to accumulating to all */
static OP all;             /* list accumulating standard terms found */


static INT set_garnir_parameters (partition) OP partition;

/* From the partition received, information in a convenient form
      is generated, ready for use by the standardisation methods. 
      It is only invoked if garnir_ready==0. This is so that if
      every set_garnir_parameters() is, in the code, paired with
      a free_garnir_paramters(), then we need only invoke this
      latter routine if garnir_ready==1.
   */

{
	INT i,j;
	INT erg = OK;

	if (garnir_ready++)
		return(OK);

	/* validate parameters */
	CTO(PARTITION,"set_garnir_parameters",partition);

	no_rows=S_PA_LI(partition);
	no_cols=S_PA_II(partition,no_rows-1);

	part=(INT*)SYM_calloc(no_rows,sizeof(INT));
	conj=(INT*)SYM_calloc(no_cols,sizeof(INT));
	garnir_sym=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
	garnir_inv=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
	entry_list=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

	/* put the parts in weakly decresing order 
      (as the tableaux entries are indexed) */

	for (i=no_boxs=0;i<no_rows;i++)
		no_boxs += (part[i] = S_PA_II(partition,no_rows-1-i));

	/* calculate conjugate partition */

	for (j=no_cols-1,i=1;j>=0;j--)
	{
		while (i<no_rows && part[i]>j) i++;
		conj[j]=i;
	}

	/* set up arrays that will be used to store certain permutations */

	for (i=0;i<=no_rows;i++)
		garnir_sym[i]=garnir_inv[i]=i;

	garnir_len=0;

	set_useful_monopolies();

	ENDR("set_garnir_parameters");
}


static INT free_garnir_parameters ()

/* Frees the five arrays that were constructed to facilitate Garnir
      relations. But only if garnir_ready==1.
   */

{
	if (!--garnir_ready)
	{
		SYM_free(part);
		SYM_free(conj);
		SYM_free(garnir_sym);
		SYM_free(garnir_inv);
		SYM_free(entry_list);
		free_useful_monopolies();
	}

	return(OK);
}


INT set_useful_monopolies ()

/* create monopolys which store (q) and (q-1) for ready use */

{
	OP temp;
	if (monopoly_ready++)
		return(OK);

	q_mp=callocobject();
	qm1_mp=callocobject();
	temp=callocobject();
	construct_mo_mp(1,1,q_mp);
	construct_mo_mp(1,1,qm1_mp);
	construct_mo_mp(0,-1,temp);
	C_L_N(qm1_mp,temp);            /* to link q and -1 */

	return(OK);
}


INT free_useful_monopolies ()

/* Frees the monopolies created by the above. 
      But only if monopoly_ready==1.
   */

{
	if (!--monopoly_ready)
	{
		freeall(q_mp);
		freeall(qm1_mp);
	}

	return(OK);
}


int set_multiplier (extra) OP extra;

/* all standard tableaux that are now found are added to the list
      after their coefficients have been multiplied by extra
      (which will usually be a MONOPOLY object).
   */

{
	multiplier=extra;
}


int hecke_action ( tableau,  permutation,  list)
	OP tableau;
	OP permutation;
	OP list;

/* The permutation acts upon the tableau to produce a
   monom list, each element of which consists of a tableau
   and a monopoly coefficient.
   Requires that set_garnir_parameters() has been invoked.
*/

{
	OP perm_cop,tab_cop,tab_mp,tab_mo;

	/* make a copy of the original permutation so that we can
      manipulate it */

	copy_permutation(permutation,perm_cop=callocobject());

	/* and form a list with the tableau as only element */

	copy_tableaux(tableau,tab_cop=callocobject());
	construct_mo_mp(0,1,tab_mp=callocobject());
	b_sk_mo(tab_cop,tab_mp,tab_mo=callocobject());
	b_sn_l(tab_mo,NULL,list);

	hecke_action_perm_on_lc(list,perm_cop); /* perm_cop freed in hecke_action_perm_on_lc */
}
static INT axel_ll,axel_kk;

INT hecke_action_perm_on_lc ( tableaux,  permutation)
	OP tableaux;
	OP permutation;

/* Applies the hecke algebra permutation to the linear combination
   of tableaux.
   This list is updated with the result and the permutation is
   freed. There is no attempt to collect terms in the result.
   Requires that set_garnir_parameters() has been invoked.
   An ERROR may be generated if permutation is from a group bigger
   than the entries from tableaux.
*/

{
	INT i,j,k,ll;
	INT trev_lo_col,lo_row,hi_col,hi_row;
	OP tab,temp,new,coeff,monom,ext;
	/*
	println(tableaux);
	println(permutation);
*/

	if (empty_listp(tableaux))
	{
		freeall(permutation);
		return(OK);
	}

	/* ensure that set_garnir_parameters() has been invoked */

	set_garnir_parameters(s_t_u(S_MO_S(S_L_S(tableaux))));

	while (1)
	{  /* look for a right factor s_k in reduced expression for permutation */

		for (k=S_P_LI(permutation)-1;k>0
		    && S_P_II(permutation,k)>S_P_II(permutation,k-1);k--);

		if (!k)  /* none present */
			break;

		/* now apply s_k to list of tableaux */

		temp=tableaux;
		while (temp!=NULL)
		{
			tab=S_MO_S(S_L_S(temp));
			/* println(tab); */
			lo_row= -1;
			hi_row= -1;
			/* printf("1\n"); */

			/* trawl through positions of tableau looking for k & k+1 */

			for (j=0;j<no_cols;j++)
			{
				/*printf("1.2 no_cols=%d j=%d trev_lo_col=%d\n",no_cols,j,trev_lo_col);*/
				axel_ll=ll=trev_lo_col; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
				axel_ll=ll=lo_row; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
				axel_kk=ll=hi_col; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
				for (i=0;i<conj[j];i++)
				{
					/*
					printf("2 i=%d conj[j]=%d trev_lo_col=%d\n",i,conj[j],trev_lo_col);
					println(tab);
*/
				axel_kk=ll=hi_col; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
					if (S_T_IJI(tab,i,j) == k+1)
					{
						if (lo_row> -1)      /* position of k already located */
						{
							/*							printf("3 lo_row=%d trev_lo_col=%d k=%d\n",lo_row,trev_lo_col,k);*/
							/* enact the tranposition; coefficient is unchanged */

/* printf("1 i=%d j=%d lo_row=%d trev_lo_col=%d\n",i,j,lo_row,trev_lo_col); */
							C_I_I(S_T_IJ(tab,lo_row,trev_lo_col),k+1);
							C_I_I(S_T_IJ(tab,i,j),k);

							temp=S_L_N(temp);
							goto there;       /* end processing of current tableau */
						}
						else
						{
							hi_row=i;
							/* printf("4\n");*/
							hi_col=j;
						}
					}
					else if (S_T_IJI(tab,i,j)==k)
					{
				axel_kk=ll=hi_col; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
				axel_ll=ll=hi_row; /* do not remove 
						this is to prevent optimizer
						from generating wrong code on btm2x5 */
						if (hi_row > -1)      /* position of k+1 already located */
						{
							/*printf("5\n");*/
							/* form a new element in the list, obtained by
	     simple tranposition and multiply coeff by q. */

							new=callocobject();
							copy_tableaux(tab,new);
							C_I_I(S_T_IJ(new,hi_row,hi_col),k);
							C_I_I(S_T_IJ(new,i,j),k+1);
			/*printf("2 i=%d j=%d hi_row=%d hi_col=%d\n",i,j,hi_row,hi_col);*/
							mult_monopoly_monopoly(q_mp,S_MO_K(S_L_S(temp)),
							    coeff=callocobject());
							b_sk_mo(new,coeff,monom=callocobject());
							b_sn_l(monom,S_L_N(temp),ext=callocobject());
							C_L_N(temp,ext);

							/* multiply old coefficient by q-1 */

							mult_apply_monopoly(qm1_mp,S_MO_K(S_L_S(temp)));

							temp=S_L_N(ext);
							goto there;       /* end processing of current tableau */
						}
						else
						{
							/*printf("6 i=%d j=%d\n",i,j);*/
							lo_row=i;
							trev_lo_col=j;
							/*printf("6 lo_row=%d trev_lo_col=%d\n",lo_row,trev_lo_col);*/
						}
						axel_ll=ll=trev_lo_col; /* do not remove 
						this is to prevent optimizer
												from generating wrong code on btm2x5 */
					}
					axel_ll=ll=trev_lo_col; /* do not remove 
						this is to prevent optimizer
											from generating wrong code on btm2x5 */
				}
				axel_ll=ll=trev_lo_col; /* do not remove 
						this is to prevent optimizer
										from generating wrong code on btm2x5 */
			}

			/* if we get here then we have not found both k & k+1 */

			fprintf(stderr,"Incompatible permutation in hecke_action_perm_on_lc()\n");
			return(ERROR);

there:
			;
		}
		/* need to change the permutation */

		i=S_P_II(permutation,k-1);
		C_I_I(S_P_I(permutation,k-1),S_P_II(permutation,k));
		C_I_I(S_P_I(permutation,k),i);

	}
	/* free the permutation since it has been corrupted */

	/*printf("se:");
	println(tableaux);*/
	freeall(permutation);
	free_garnir_parameters();
	return(OK);
}


INT find_non_rowstandard_pos ( tableau, r, c) OP tableau; INT *r; INT *c;

/* locates the row and column of an entry at which that to its right
   is smaller. Requires that set_garnir_parameters() has been invoked. */

{
	INT i,j,l,e1,e2;

	for (i=0;i<no_rows;i++)
	{
		l=part[i];

		e1=S_T_IJI(tableau,i,0);
		for (j=1;j<l;j++)
		{
			if (e1 > (e2=S_T_IJI(tableau,i,j)) )
			{
				*r=i,*c=j-1;
				return(OK);
			}
			e1=e2;
		}
	}

	/* no row-nonstandardness */

	*r= *c= -1;
	return(OK);
}


INT columns_standardise_tableau ( tableau,sig) OP tableau; INT *sig;

/* sorts the columns of the TABLEAUX tableau into standard order.
   Requires that set_garnir_parameters() has been invoked. */

{
	INT c;

	for (c=0;c<no_cols;c++)
		column_standardise_tableau(tableau,c,sig);

	return(OK);
}


INT column_standardise_tableau ( tableau,  col, sig) OP tableau; INT col; INT *sig;

/* sorts only the (col)th column of the TABLEAUX tableau into
   standard order. The length of the permutation (in terms of
   position transpositions) is added to *sig.
   Requires that set_garnir_parameters() has been invoked. */

{
	INT i,k,e1,e2,r1,r2,s=0;

	r1=0;
	r2=conj[col];

	/* search for an entry smaller than that above */

	e1=S_T_IJI(tableau,r1,col);
	for (i=r1+1;i<r2;i++)
	{
		if (e1 > (e2=S_T_IJI(tableau,i,col)))
		{
			/* we've found such an entry: now see how far it can be
	    moved up the column */

			C_I_I(S_T_IJ(tableau,i,col),e1);

			for (k=i-2;k>=r1 && e2<S_T_IJI(tableau,k,col);k--)
				C_I_I(S_T_IJ(tableau,k+1,col),S_T_IJI(tableau,k,col));

			/* so it can be moved up i-k-1 positions (to k+1) */

			C_I_I(S_T_IJ(tableau,++k,col),e2);
			s+=i-k;

		}
		else
			e1=e2;
	}

	*sig+=s;
	return(OK);
}


static int standardise_tableau_list ( list,  expression) OP list; 
	OP expression;

/* Expresses the monomial list of tableaux with monopoly coefficients
   in terms of a list of standard tableaux with monopoly coefficients 
   Requires that set_garnir_parameters() has been invoked.
*/

{
	OP a;

	for (a=list;a!=NULL;a=S_L_N(a))
	{
		set_multiplier(S_MO_K(S_L_S(a)));
		standardise_tableau(S_MO_S(S_L_S(a)),expression);
	}
}


static int standardise_tableau ( tableau,  expression) OP tableau; 
	OP expression;

/* Expresses the tableau in terms of a list of standard tableaux
   with polynomial coefficients. tableau is not freed by this
   function, but its entries may change.
   Requires that set_garnir_parameters() has been invoked,
   and that multiplier has been set.
*/

{

	INT swaps=0;
	OP overall;

	all=expression;

	columns_standardise_tableau(tableau,&swaps);
	find_non_rowstandard_pos(tableau,&grow,&lcol);

	if (grow<0)
	{
		overall=callocobject();
		construct_mo_mp(0,((swaps&1) ? -1 : 1),overall);
		mult_apply_monopoly(multiplier,overall);
		garnir_result(tableau,overall,all); /* overall is destroyed */
	}
	else
		garnir_juggle(tableau,(INT)0,(INT)((swaps&1) ? -1 : 1));


}


static int garnir_juggle ( tableau,  power,  coeff) OP tableau; INT power; INT coeff;

/* Recursive function which is passed a non-standard tableau,
   together with its coefficient in the form of
      coeff * q^power.
   (usually coeff is +1 or -1).
   In one invocation, a single Garnir relation is performed:
   those which result that are standard are added to the list
   of tableaux; those which are non-standard are resubmitted to
   this function.
   The tableau that is passed is assumed to be standard in columns
   AND nonstandard in rows. It is ALSO assumed that the non-standard
   position has already been stored in (grow,lcol).
   tableau is unchanged by this function,
   Requires that set_garnir_parameters() has been invoked.
*/

{
	INT p,swaps,lcoll,rcoll;
	OP store,temp,overall;

	template=tableau;

	/* obtain lengths of garnir parts and stores entries of these parts */

	glength=conj[lcol]+1;
	gright=grow+1;
	gleft=glength-gright;
	rcoll=rcol=(lcoll=lcol)+1;

	for (p=0;p<gright;p++)
		entry_list[p]=S_T_IJI(tableau,p,rcol);
	for (;p<glength;p++)
		entry_list[p]=S_T_IJI(tableau,p-1,lcol);

	/* start a list for garnir_generate() to put tableaux and their
      coeffs into. the final list address is kept in store, so that
      the list can be freed later (children is a global variable that
      will be overwritten). */

	children=callocobject();
	init(LIST,children);

	garnir_generate(glength,glength-1);
	store=children;

	/* now order the entries in the two changed columns of each tableau */

	for (temp=children;S_L_S(temp)!=NULL;temp=S_L_N(temp))
	{
		swaps=0;
		column_standardise_tableau(S_MO_S(S_L_S(temp)),lcoll,&swaps);
		column_standardise_tableau(S_MO_S(S_L_S(temp)),rcoll,&swaps);
		find_non_rowstandard_pos(S_MO_S(S_L_S(temp)),&grow,&lcol);

		if (grow<0)
		{  /* then tableau is standard and must be appended to the list */

			construct_mo_mp(
			    power+S_I_I(S_MO_K(S_L_S(temp))),
			    (swaps+S_I_I(S_MO_K(S_L_S(temp))))&1 ? coeff : -coeff,
			    overall=callocobject());
			mult_apply_monopoly(multiplier,overall);

			garnir_result(S_MO_S(S_L_S(temp)),overall,all); /* overall is destroyed */
		}
		else
		{  /* it must be resubmitted */

			garnir_juggle(S_MO_S(S_L_S(temp)),power+S_I_I(S_MO_K(S_L_S(temp))),
			    (swaps+S_I_I(S_MO_K(S_L_S(temp))))&1 ? coeff : -coeff);
		}
	}

	freeall(store);
}


static int garnir_generate ( head,  wag) INT head; INT wag;

/* Recursive function which creates all the terms in the Garnir relation,
   together with the lengths of the permutations required.
   For the purpose of eliminating repetitions, a canonical reduced
   expression for permutations is employed. This is of the form:
     s_0 s_1s_0 s_2s_1s_0 s_3s_2s_1s_0 s_4s_3s_2s_1s_0 ....,
   which consists of syllables of increasing first index, a syllable
   being of the form s_ks_{k-1}s_{k-2}...s_0 where 0 <= l <= k.
   The permutations act on the right and are built up in their
   reduced form from right to left.
   The current permutation (which is stored in garnir_sym; and its
   inverse in garnir_inv) has most recent index as wag and the index
   of the most recently completed syllable as head. Its length is
   given by garnir_len.
   This routine tests all possible transpositions which give a
   standard Garnir term and which adjoin to the left of the current
   permutation to give another in canonical form.
   Requires that set_garnir_parameters() has been invoked.
*/

{
	INT i,j,p,s;
	OP pl,mon,child,ext;

	garnir_len++;        /* all found permutations will have length 1 more */

	for (i=0;i<gright;i++)
	{
		s=garnir_sym[i];

		if ( (s<wag || (s==wag+1 && s<head))

		    /* so that the permutation will be canonically represented */

		&& (j=garnir_inv[s+1]) >= gright)

		/* s is in the right column, s+1 is in the left */

		{  /* swap the entries in sym & inv to keep track of permutation */

			garnir_inv[garnir_sym[i]=s+1]=i;
			garnir_inv[garnir_sym[j]=s]=j;

			/* place the entries in the tableau in the corresponding way */

			child=callocobject();
			copy_tableaux(template,child);

			for (p=0;p<gright;p++)
				C_I_I(S_T_IJ(child,p,rcol),entry_list[garnir_sym[p]]);
			for (;p<glength;p++)
				C_I_I(S_T_IJ(child,p-1,lcol),entry_list[garnir_sym[p]]);

			/* store tableau with its length in the list */

			m_i_i(garnir_len,pl=callocobject());
			b_sk_mo(child,pl,mon=callocobject());
			b_sn_l(mon,children,ext=callocobject());
			children=ext;

			/* resubmit with the updated permutation's info */

			if (s<wag)
				garnir_generate(wag,s);
			else
				garnir_generate(head,wag+1);

			/* remove permutation */

			garnir_inv[garnir_sym[i]=s]=i;
			garnir_inv[garnir_sym[j]=s+1]=j;
		}
	}

	garnir_len--;         /* restores value */
}


static int garnir_result ( tableau,  mp_coeff,  acc_list) OP tableau; 
	OP mp_coeff; 
	OP acc_list;

/* Adds  mp_coeff * tableau to our standard list: acc_list.
   tableau is unchanged, and copied when necessary. mp_coeff is
   destroyed. The list is maintained
   in lexicographic order (reading across rows, then top to bottom).
*/

{
	OP a,b,term;
	OP t,temp;
	INT co;

	if (empty_listp(acc_list))
	{
		t=callocobject();
		copy_tableaux(tableau,t);
		term=callocobject();
		b_sk_mo(t,mp_coeff,term);
		c_l_s(acc_list,term);            /* assuming that the self exists
						  		          for an empty list */
	}
	else
	{  /* look for tableau in list */

		for (a=acc_list,b=NULL;
		    a!=NULL && (co=comp_tableaux(S_MO_S(S_L_S(a)),tableau))<0;
		    a=S_L_N(b=a));

		if (a==NULL || co>0)  /* not present */
		{
			t=callocobject();
			copy_tableaux(tableau,t);
			term=callocobject();
			b_sk_mo(t,mp_coeff,term);

			if (b==NULL)     /* insert new first term (before a) */
			{
				b_ks_o(S_O_K(acc_list),S_O_S(acc_list),temp=callocobject());
				/* c_o_s(acc_list,NULL); */
				c_o_k(acc_list,EMPTY);
				b_sn_l(term,temp,acc_list);
			}
			else /* insert new term between b and a */
			{
				b_sn_l(term,a,temp=callocobject());
				C_L_N(b,temp);
			}
		}
		else /* term is present - must just add coefficients */
		{
			insert(mp_coeff,S_MO_K(S_L_S(a)),add_koeff,NULL);
		}
	}
}


INT enter_list_to_matrix ( matrix, column, standard, express) OP matrix; 
	INT column; 
	OP standard; 
	OP express;

/* express is an ordered list of standard tableaux with monopoly
   coefficients. this expression is used to construct a column
   of the matrix, by comparing the tableaux with the list of standard
   tableaux.
   For those tableaux that are not present in the list, or have 0
   coefficient, the column gets an INTEGER object with value 0.
*/

{
	INT r;

	/* account for an empty expression */

	if (empty_listp(express))
		express=NULL;

	/* find first non_zero term */

	while (express!=NULL && empty_listp(S_MO_K(S_L_S(express))))
		express=S_L_N(express);

	for (r=0; standard!=NULL; standard=S_L_N(standard),r++)
	{
		if ( express == NULL 
		    || comp_tableaux(S_L_S(standard),S_MO_S(S_L_S(express))) )

			m_i_i(0L,S_M_IJ(matrix,r,column));
		else
		{   /* need to transfer the coefficient across */

			copy(S_MO_K(S_L_S(express)),S_M_IJ(matrix,r,column));

			/* now look for next non-zero entry */

			do
			{
				express=S_L_N(express);
			}  while (express!=NULL && empty_listp(S_MO_K(S_L_S(express))));
		}
	}
}


static INT construct_mo_mp ( power,  coeff,  mo_po)
	INT power;
	INT coeff;
	OP mo_po;

/* Constructs a monopoly object representing the 1-term, 1-variable
   polynomial:  coeff * x^power.
*/

{
	OP p,c;
	INT erg = OK;

	p=callocobject();
	c=callocobject();
	M_I_I(power,p);
	M_I_I(coeff,c);
	erg += b_skn_mp(p,c,NULL,mo_po);
	ENDR("internal hiccup.c:construct_mo_mp");
}


#ifdef UNDEF
memory_check (query) void *query;

/* Exits with an error message if the passed item is NULL: presumably
   this results from a memory allocation when none is left.
*/

{
	if (query==NULL)
	{
		printf("Memory error? None left? Exiting!\n");
		exit(0);
	}
}
#endif

/********************************************************************
 ********************************************************************
 ********************************************************************

   HICCUP routines to calculate explicit representation matrices
   of the Hecke algebra of type A in the case where q is a root
   of unity: but only for two-rowed cases.

   Programmed by Trevor Welsh, Bayreuth, November 1995.
  
 ********************************************************************
 ********************************************************************
 ********************************************************************/



INT root_dimension (partition, p_root, dim)
	OP partition;
	OP p_root;
	OP dim;

/* calculates the dimension of the irreducible representation
   of the Hecke algebra of type A labelled by partition, at
   a primitive (p_root)th of unity. Uses Trevvie's character formula.
*/

{
	OP parti,neg,hold,vec;
	INT r1,r2,no_rows,row1,row2,kappa,o_root;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("root_dimension() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	o_root=S_I_I(p_root);
	no_rows=S_PA_LI(partition);

	if (o_root<1)
	{
		printf("ridiculous root of unity!\n");
		return(ERROR);
	}

	if (o_root>1 && no_rows>2)
	{
		printf("sorry, can only deal with partitions with length 2!\n");
		return(ERROR);
	}

	r1=row1 = no_rows>0 ? S_PA_II(partition,no_rows-1) : 0;
	r2=row2 = no_rows>1 ? S_PA_II(partition,no_rows-2) : 0;

	if ( (row1+1-row2)%o_root == 0 )   /* Specht module is irreducible */
	{
		dimension_partition(partition,dim);
	}
	else
	{
		m_il_nv(2L,vec=callocobject());
		b_ks_pa(VECTOR,vec,parti=callocobject());
		neg=callocobject();
		hold=callocobject();

		m_i_i(0L,hold);
		m_i_i(0L,neg);

		while (r2>=0)
		{
			C_I_I(s_pa_i(parti,1L),r1);
			C_I_I(s_pa_i(parti,0L),r2);

			dimension_partition(parti,hold);
#if DUMP==1
			printf("+");
			print(hold);
#endif
			add_apply(hold,dim);

			r1+=o_root;
			r2-=o_root;
		}


		kappa=(row1-row2)/o_root+1;
		r2=row1+1-kappa*o_root;
		r1=row1+row2-r2;

		while (r2>=0)
		{
			C_I_I(s_pa_i(parti,1L),r1);
			C_I_I(s_pa_i(parti,0L),r2);

			dimension_partition(parti,hold);
#if DUMP==1
			printf("-");
			print(hold);
#endif
			add_apply(hold,neg);

			r1+=o_root;
			r2-=o_root;
		}

#if DUMP==1
		printf("\n");
#endif

		addinvers_apply(neg);
		add_apply(neg,dim);

		freeall(neg);
		freeall(hold);
		freeall(parti);
	}
	return(OK);
}


INT generate_root_tableaux ( partition,  p_root,  std)
	OP partition;
	OP p_root;
	OP std;

/* generates all the root standard tableaux for the partition,
   by generating all standard tableaux and plucking from the list.
   returns the number of standard tableaux, else ERROR.
*/

{
	OP temp,bad,good,top_bad;
	OP last,n;
	INT count=0;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("generate_root_tableaux() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	if (S_PA_LI(partition)>2)
	{
		printf("sorry, can only deal with partitions with length 2!\n");
		return(ERROR);
	}

	if (S_I_I(p_root)<1)
	{
		printf("ridiculous root of unity!\n");
		return(ERROR);
	}

	set_root_parameters(partition,p_root);

	/* obtain S_n standard tableaux for partition. trawl through
      these, retaining those which are root standard. */

	weight(partition,n=callocobject());
	last_partition(n,last=callocobject());
	kostka_tab(partition,last,std);

	freeall(n);
	freeall(last);


	if (!empty_listp(std))
	{
		/* start at top of list and look for first root standard tableaux */

		for (temp=std;
		    temp!=NULL && find_non_root_standard_pos(S_L_S(temp))>=0;
		    temp=S_L_N(bad=temp));

		if (temp!=std)
{  /* need to release non root standard tableaux, and to
					    make std point to the first standard. */

			if (temp!=NULL)
			{
				C_L_N(bad,NULL);
				b_ks_o(S_O_K(temp),S_O_S(temp),std); /* this frees self of std */
				C_O_K(temp,EMPTY);
				freeall(temp);
				temp=std;
			}
			else
{  /* need to make std into an empty list: the init() routine
							       also frees the previous list */

				init(LIST,std);
			}
		}

		while (temp!=NULL)
		{
			/* go through list looking for non root standard, and
	    counting standard tableaux. */

			for (temp=S_L_N(good=temp),count++;
			    temp!=NULL && find_non_root_standard_pos(S_L_S(temp))<0;
			    temp=S_L_N(good=temp),count++);

			/* good contains previous standard, temp non-standard */

			if (temp!=NULL)
			{
				top_bad=temp;

				/* now go through non root standard tableaux */

				for (temp=S_L_N(bad=temp);
				    temp!=NULL && find_non_root_standard_pos(S_L_S(temp))>=0;
				    temp=S_L_N(bad=temp));

				/* join the standard one found (temp) with the previous
	       standard list, and eliminate the intervening tableaux. */

				C_L_N(good,temp);
				C_L_N(bad,NULL);
				freeall(top_bad);
			}
		}
	}


	free_root_parameters();
	return(count);
}


INT hecke_root_generator_reps ( partition,  p_root,  vector)
	OP partition;
	OP p_root;
	OP vector;

/* for the given partition produces a vector of matrices, the ith
   of which represents the ith generator s_i.
*/

{
	INT i,ni;
	OP n,p,lc,mat;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		error("hecke_generator_reps() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	if (S_I_I(p_root)<1)
	{
		error("ridiculous root of unity!\n");
		return(ERROR);
	}

	weight(partition,n=callocobject());
	ni=S_I_I(n);
	freeall(n);

	/* construct and intialize a permutation which will be passed to
      the representing routines. */

	m_il_p(ni,p=callocobject());
	for (i=0;i<ni;i++)
		m_i_i(i+1,S_P_I(p,i));

	/* encase this permutation in a linear combination list */

	build_lc(p,lc=callocobject()); /* p part of lc */

	/* construct the vector to build the results */

	m_il_v(--ni,vector);

	/* loop through all simple transpositions, obtaining representations */

	for (i=0;i<ni;i++)
	{
		C_I_I(S_P_I(p,i),i+2);
		C_I_I(S_P_I(p,i+1),i+1);

		root_represent_hecke_action(partition,p_root,lc,s_v_i(vector,i));

		C_I_I(S_P_I(p,i),i+1);
	}

	freeall(lc);
	return(OK);
}


INT root_represent_hecke_action (partition, p_root, hecke, mat)
	OP partition;
	OP p_root;
	OP hecke;
	OP mat;


/* Constructs the explicit matrix representative in that representation
   labelled by partition at p_root of unity, of the element of
   the hecke algebra A_{n-1} obtained by canonically mapping
   the linear combination of permutations from the symmetric group.
*/

{
	INT k;
	OP temp,e,list,std_tableaux,t,tab_list,tab_cop,go_perm,perm_cop,coeff;

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("root_represent_hecke_action() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	if (S_O_K(hecke)!=LIST 
	    || (!empty_listp(hecke)
	    && (S_O_K(S_L_S(hecke)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke))) != PERMUTATION )))
	{
		printf("root_represent_hecke_element() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	if (S_I_I(p_root)<1)
	{
		printf("ridiculous root of unity!\n");
		return(ERROR);
	}

	/* construct the list of standard tableaux and 
      make a matrix of the right size for the results */

	std_tableaux=callocobject();
	k=generate_root_tableaux(partition,p_root,std_tableaux);
	m_ilih_m(k,k,mat);

	/* set the partition parameters */

	set_garnir_parameters(partition);
	set_root_parameters(partition,p_root);

	/* run through the standard tableaux, acting on each with the
      permutation, standardising the result and entering that
      result into the appropriate column of the matrix. */

	for (t=std_tableaux,k=0;t!=NULL;t=S_L_N(t),k++)
	{
		list=callocobject();       /* to accumualte results from all perms */
		init(LIST,list);
		tab_list=callocobject();   /* to store results of each action */
		for (go_perm=hecke;go_perm!=NULL;go_perm=S_L_N(go_perm))
		{
			copy_tableaux(S_L_S(t),tab_cop=callocobject());
			build_lc(tab_cop,tab_list); /* tab_cop part of tab_list */

			copy_permutation(S_MO_S(S_L_S(go_perm)),perm_cop=callocobject());

			hecke_action_perm_on_lc(tab_list,perm_cop); /* perm_cop freed in hecke_action_perm_on_lc */

			for (temp=tab_list;temp!=NULL;temp=S_L_N(temp))
			{
				mult_monopoly_monopoly(S_MO_K(S_L_S(go_perm)),S_MO_K(S_L_S(temp)),
				    coeff=callocobject());
				garnir_result(S_MO_S(S_L_S(temp)),coeff,list);
			}
			freeself(tab_list);
		}
		freeall(tab_list);

		e = callocobject();
		init(LIST,e);
		root_standardise_tableau_list(list,e);
		freeall(list);

		enter_list_to_matrix(mat,k,std_tableaux,e);
		freeall(e);
	}

	free_root_parameters();
	free_garnir_parameters();

	freeall(std_tableaux);
	return(OK);
}


INT root_standardise_cold_tableaux_list (tableaux, p_root, result)
	OP tableaux;
	OP p_root;
	OP result;

/* Similar to the function root_standardise_tableau_list(),
   but all initialisation
   is taken care of, so the user just has to create a list of tableaux,
   and then submit it here. The result is added to result which, if not
   already a list, is made into a list.
   tableaux is unchanged by this function.
*/

{
	OP a,imitate;

	/* first validate the input */

	if (S_O_K(tableaux)!=LIST 
	    || (!empty_listp(tableaux)
	    && (S_O_K(S_L_S(tableaux)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(tableaux))) != TABLEAUX )))
	{
		printf("hecke_action_lc_on_lc() did not receive a linear combination of tableaux as it was expecting!\n");
		return(ERROR);
	}

	if (S_PA_LI(s_t_u(S_MO_S(S_L_S(tableaux))))>2)
	{
		printf("sorry, can only deal with tableaux with less than 2 rows!\n");
		return(ERROR);
	}

	if (S_I_I(p_root)<1)
	{
		printf("ridiculous root of unity!\n");
		return(ERROR);
	}

	/* if result is not already a list, then make it one */

	if (S_O_K(result)!=LIST)
		init(LIST,result);

	/* return if there is nothing to process */

	if (empty_listp(tableaux))
		return(OK);

	set_garnir_parameters(s_t_u(S_MO_S(S_L_S(tableaux))));
	set_root_parameters(s_t_u(S_MO_S(S_L_S(tableaux))),p_root);
	imitate=callocobject();

	for (a=tableaux;a!=NULL;a=S_L_N(a))
	{
		set_root_multiplier(S_MO_K(S_L_S(a)));
		copy_tableaux(S_MO_S(S_L_S(a)),imitate);
		root_standardise_tableau(imitate,result);
		freeself(imitate);
	}

	freeall(imitate);
	free_root_parameters();
	free_garnir_parameters();
	return(OK);
}



/* Note that the following variables have been defined prior to
   set_garnir_parameters() and are also made use in the routines
   that follow.

 INT *part,*conj,*entry_list;
 INT lcol,rcol,grow,glength,gright,gleft;
 OP children,template;
*/

static OP root_multiplier;  /* mult by this prior to accumulating to root_all */
static OP root_all;         /* list accumulating standard terms found */

static INT root_ready=0,per_len=0;
static INT row1,row2,calx;
static INT root,rootover2,root_cover,kappa,strip,ostrip;
static INT min_tail,max_tail;
static INT piece1,piece2,first_var,left_const,right_const;
static INT *symmetry,*inverse;
static INT *spectrum;
static OP poly,hiccup_log;
static OP ghost;
static OP accumulate;
static OP symmetrised;
static OP mq_mp;     /* monopoly storing -q */


INT set_root_parameters ( partition,  p_root)
	OP partition;
	OP p_root;


/* sets a numbers of parameters depending on the Young diagram and the
   relevant boundary strip. root_ready keeps an account of how many
   times that this routine is called, so that everything can be
   freed on the last free_root_parameters() call.
   Of course, this assumes that in every routine that calls
   set_root_parameters(), there is a corresponding call to
   free_root_parameters().
*/

{
	INT i,no_rows;

	if (root_ready++)
		return(OK);

	/* validate parameters */

	if (partition==NULL || S_O_K(partition)!=PARTITION)
	{
		printf("generate_root_tableaux() did not receive a partition as it was expecting!\n");
		return(ERROR);
	}

	root=S_I_I(p_root);
	if (root&1)               /* odd */
	{
		rootover2=root;        /* half root if even */
		root_cover=root-1;     /* minimum power at which to look for improvements */
	}
	else
		root_cover=rootover2=root/2;

	no_rows=S_PA_LI(partition);
	row1 = no_rows>0 ? S_PA_II(partition,no_rows-1) : 0;
	row2 = no_rows>1 ? S_PA_II(partition,no_rows-2) : 0;

	/* calculate length of relevant boundary strip */

	kappa=(row1-row2)/root+1;
	strip=kappa*root;

	/* set up arrays to store certain permutations */

	symmetry=(INT*)SYM_calloc(strip,sizeof(INT));
	inverse=(INT*)SYM_calloc(strip,sizeof(INT));

	for (i=0;i<strip;i++)
		symmetry[i]=inverse[i]=i;
	per_len=0;

	/* refine and augment info on lengths of strips */

	if (strip-1>row1 || strip-1 == row1-row2)
		kappa=strip=ostrip=calx=min_tail=max_tail=0;
	else
	{
		strip-=2;              /* so we just add to get co-ord in top row */

		ostrip=strip-root+2;   /* length of the other strips */
		calx=row1-strip;       /* final one to check for strip standard */
		min_tail=strip+1+row2-row1;
		max_tail=row2<root ? row2 : root-1;
	}

	/* make a tableau to be used to store default entries */

	m_u_t(partition,ghost=callocobject());
	for (i=0;i<row1;i++)
		m_i_i(0L,S_T_IJ(ghost,0,i));
	for (i=0;i<row2;i++)
		m_i_i(0L,S_T_IJ(ghost,1,i));


	/* make zeroed arrays in which to manipulate monopolies at root of unity.
      they are made the maximum size need for current root. */

	m_il_nv(2*root,poly=callocobject());
	m_il_nv(root,hiccup_log=callocobject());

	/* and a normal array for fast (!) renormalisation of monopolies */

	spectrum=(INT*)SYM_calloc(root,sizeof(INT));

	/* make monopoly storing -q */

	construct_mo_mp(1,-1,mq_mp=callocobject());

	/* the following array will store the action of symmetrising over
      i-1 boxes in the second row. */

	m_il_v(root-1,symmetrised=callocobject());

	return(OK);
}


INT free_root_parameters ()

/* frees arrays created by routine above - but only if root_ready==1 */

{
	if (!--root_ready)
	{
		SYM_free(symmetry);
		SYM_free(inverse);
		freeall(ghost);
		freeall(poly);
		freeall(hiccup_log);
		freeall(symmetrised);
		SYM_free(spectrum);
		freeall(mq_mp);
	}

	return(OK);
}



INT find_non_root_standard_pos (tableau) OP tableau;

/* determines where (in the 2nd row) the tableau is not p-root
   standard. It is assumed that set_root_parameters has been invoked.
   Also assumed that kappa>0.
*/

{
	INT i,j;

	/* check all relevant positions in 2nd row to find rightmost
      which is not strip standard */

	if (kappa)
		for (i=calx-1;i>=0;i--)
			if (S_T_IJI(tableau,1,i)>S_T_IJI(tableau,0,i+strip))
			{
				if (kappa>1)

				/* then we must also check that all positions to right are
	    not ostrip standard (ostrip=strip-root+2). */

				{
					for (j=i+root-1;
					    j<row2 && S_T_IJI(tableau,1,j)>S_T_IJI(tableau,0,j+ostrip);
					    j++);

				}

				if (kappa==1 || j>=row2)        /* then i gives non-standard pos */
				{
					return(i);
				}
			}

	return(-1);
}


set_root_multiplier (extra) OP extra;

/* all standard tableaux that are now found are added to the list
      after their coefficients have been multiplied by extra
      (which will usually be a MONOPOLY object).
   */

{
	root_multiplier=extra;
}


root_standardise_tableau_list ( list,  expression)
	OP list;
	OP expression;

/* Expresses the monomial list of tableaux with monopoly coefficients
   in terms of a list of standard tableaux with monopoly coefficients 
   Requires that set_garnir_parameters() and set_root_parameter()
   have both been invoked.
*/

{
	OP a;

	for (a=list;a!=NULL;a=S_L_N(a))
	{
		set_root_multiplier(S_MO_K(S_L_S(a)));
		root_standardise_tableau(S_MO_S(S_L_S(a)),expression);
	}
}


root_standardise_tableau ( tableau,  expression)
	OP tableau;
	OP expression;

/* Expresses the tableau in terms of a list of standard tableaux
   with polynomial coefficients. tableau is not freed by this
   function, but its entries may change.
   Requires that set_garnir_parameters() and set_root_parameter()
   have both been invoked, and that root_multiplier has been set.
*/

{
	INT swaps=0;
	OP overall;

	root_all=expression;
	columns_standardise_tableau(tableau,&swaps);
	find_non_rowstandard_pos(tableau,&grow,&lcol);

	if (grow<0)
	{  /* then tableau is S_n standard - now test root standardness */

		if ((lcol=find_non_root_standard_pos(tableau))<0)
		{
			construct_mo_mp(0,swaps&1 ? -1 : 1,overall=callocobject());
			mult_apply_monopoly(root_multiplier,overall);
#if NORMALISE==1
			root_garnir_result(tableau,overall,root_all);
#else
			garnir_result(tableau,overall,root_all);
#endif
		}
		else /* S_n standard but not root standard */
		{
			strip_juggle(tableau,0,swaps&1 ? -1 : 1);
		}
	}
	else /* S_n non-standard */
	{
		root_juggle(tableau,0,swaps&1 ? -1 : 1);
	}
}


root_juggle ( tableau,  power,  coeff)
	OP tableau;
	INT power;
	INT coeff;

/* Recursive function which is passed a non-standard tableau,
   together with its coefficient in the form of
      coeff * q^power.
   (usually coeff is +1 or -1).
   In one invocation, a single Garnir relation is performed:
   those which result that are standard are added to the list
   of tableaux; those which are non-standard are resubmitted to
   this function.
   The tableau that is passed is assumed to be standard in columns
   AND nonstandard in rows. It is ALSO assumed that the non-standard
   position has already been stored in (grow,lcol).
   tableau is unchanged by this function,
   Requires that set_garnir_parameters() and set_root_parameters()
   have been invoked.
*/

{
	INT p,swaps,lcoll,rcoll;
	OP store,temp,overall;

	template=tableau;

	/* obtain lengths of garnir parts and stores entries of these parts */

	glength=conj[lcol]+1;
	gright=grow+1;
	gleft=glength-gright;
	rcoll=rcol=(lcoll=lcol)+1;

	for (p=0;p<gright;p++)
		entry_list[p]=S_T_IJI(tableau,p,rcol);
	for (;p<glength;p++)
		entry_list[p]=S_T_IJI(tableau,p-1,lcol);

	/* start a list for garnir_generate() to put tableaux and their
      coeffs into. the final list address is kept in store, so that
      the list can be freed later (children is a global variable that
      will be overwritten). */

	children=callocobject();
	init(LIST,children);

	garnir_generate(glength,glength-1);
	store=children;

	/* now order the entries in the two changed columns of each tableau */

	for (temp=children;S_L_S(temp)!=NULL;temp=S_L_N(temp))
	{
		swaps=0;
		column_standardise_tableau(S_MO_S(S_L_S(temp)),lcoll,&swaps);
		column_standardise_tableau(S_MO_S(S_L_S(temp)),rcoll,&swaps);
		find_non_rowstandard_pos(S_MO_S(S_L_S(temp)),&grow,&lcol);

		if (grow<0)
		{  /* then tableau is S_n standard - now test root standardness */

			if ((lcol=find_non_root_standard_pos(S_MO_S(S_L_S(temp))))<0)
			{
				construct_mo_mp(
				    power+S_I_I(S_MO_K(S_L_S(temp))),
				    (swaps+S_I_I(S_MO_K(S_L_S(temp))))&1 ? coeff : -coeff,
				    overall=callocobject());
				mult_apply_monopoly(root_multiplier,overall);

#if NORMALISE==1
				root_garnir_result(S_MO_S(S_L_S(temp)),overall,root_all);
#else
				garnir_result(S_MO_S(S_L_S(temp)),overall,root_all);
#endif
			}
			else /* S_n standard but not root standard */
			{
				strip_juggle(S_MO_S(S_L_S(temp)),power+S_I_I(S_MO_K(S_L_S(temp))),
				    (swaps+S_I_I(S_MO_K(S_L_S(temp))))&1 ? coeff : -coeff);
			}
		}
		else /* S_n non-standard */
		{
			root_juggle(S_MO_S(S_L_S(temp)),power+S_I_I(S_MO_K(S_L_S(temp))),
			    (swaps+S_I_I(S_MO_K(S_L_S(temp))))&1 ? coeff : -coeff);
		}
	}

	freeall(store);
}


strip_juggle (tableau, power, coeff)
	OP tableau;
	INT power;
	INT coeff;

/* Recursive function (interlinking with root_juggle()) which is passed
   a standard tableau which is not root_standard, together with its
   coefficient in the form of
      coeff * q^power.
   (usually coeff is +1 or -1).
   In one invocation, a single strip relation is performed:
   those which result that are standard are added to the list
   of tableaux; those which are non-standard are resubmitted to
   this function or to garnir_juggle().
   This enormous function has three mutually exclusive pieces
   that perform similar tasks for the cases:
     1. No of boxes of strip in second row < root;
     2. Otherwise, and kappa==1;
     3. Otherwise (kappa>1).
   The tableau that is passed is assumed to be standard. 
   It is ALSO assumed that the 2nd row position of root non-standardness
   has already been stored in lcol.
   tableau is unchanged by this function,
   Requires that set_garnir_parameters() and set_root_parameters()
   have been invoked.
*/

{
	INT i,disp,dispr1,dispr2;
	OP save_multiplier,overall,strip_list,tab;
	INT row1_pos,row2_pos,b_entry,s_entry;
	OP temp,ext,monom,koeff,new,big_list,partit,perm;
	INT *map;

	/* identify the appropriate list: i becomes no of symmetrised boxes
      in 2nd row. disp is the rightward distance from the first box
      being symmetrised to the rightmost possible root-1 2nd row boxes
      symmetrisation. */

	disp=row2-lcol-root+1;
	i= disp<0 ? row2-lcol : root-1;

	strip_list=s_v_i(symmetrised,i-1);

	if (S_O_K(strip_list)==EMPTY)
	{  /* need to generate the model expression for this standardisation */

		generate_sym_tableaux_list(i,strip_list);
	}

	/* now hijack the multiplier - so that it can be reset */

	b_ks_o(S_O_K(root_multiplier),S_O_S(root_multiplier),
	    save_multiplier=callocobject());
	/* c_o_s(root_multiplier,NULL); */
	c_o_k(root_multiplier,EMPTY);

	/* make an array to store map between canonical root non-standard
      tableau and current particular root non-standard tableau. */

	map=(INT*)SYM_calloc(row1+row2+1,sizeof(INT));

	/* identify the map from the canonical strip relation to the current
      problem using the first term in the list. */

	tab=S_MO_S(S_L_S(strip_list));

	if (disp<=0)
{  /* easy case - number of boxes of boundary strip in second row < root.
	 The stored list is used pretty much as it stands. First form
	 the map from the canonical non strip-standard tableau (this is
			 stored as the first element in the list). */

		for (i=0;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i);
		for (i=0;i<row2;i++)
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i);

		/* run through all the tableaux in the list (discarding the first),
         map them to the required tableau using the above map, multiply
         the root_multiplier by the current coefficient and resubmit */

		for (strip_list=S_L_N(strip_list);strip_list!=NULL;
		    strip_list=S_L_N(strip_list))
		{
			tab=S_MO_S(S_L_S(strip_list));

			for (i=0;i<row1;i++)
				C_I_I(S_T_IJ(ghost,0,i),map[S_T_IJI(tab,0,i)]);
			for (i=0;i<row2;i++)
				C_I_I(S_T_IJ(ghost,1,i),map[S_T_IJI(tab,1,i)]);

			mult_monopoly_monopoly(save_multiplier,S_MO_K(S_L_S(strip_list)),
			    root_multiplier);

			find_non_rowstandard_pos(ghost,&grow,&lcol);

			if (grow<0)
			{  /* then tableau is S_n standard - now test root standardness */

				if ((lcol=find_non_root_standard_pos(ghost))<0)
				{
					/* append to the standard list */

					construct_mo_mp(power,coeff,overall=callocobject());
					mult_apply_monopoly(root_multiplier,overall);

#if NORMALISE==1
					root_garnir_result(ghost,overall,root_all);
#else
					garnir_result(ghost,overall,root_all);
#endif
				}
				else /* S_n standard but not root standard */
				{
					/* in the special case when strip_juggle() calls itself,
	          ghost could get corrupted (by generate_sym_tableau_list())
	          before being used. So copy it. */

					copy_tableaux(ghost,tab=callocobject());
					strip_juggle(tab,power,coeff);
					freeall(tab);
				}
			}
			else /* S_n non-standard */
			{
				root_juggle(ghost,power,coeff);
			}

			/* discard the current value of multiplier for the current entry */

			freeself(root_multiplier);
		}
	}
	else if (kappa==1)
{  /* this is a trickier case, where the symmetrised section needs
	 to be used at different positions to where it has been formed
			 in the canonical list */

		dispr1=row1-disp;
		dispr2=row2-disp;

		/* This first loop defines the map for the last disp entries
	 of each row. */

		for (i=0;i<disp;i++)
		{
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i+dispr1);
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i+dispr2);
		}

		/* Then provide map for remainder of entries, which after being
	 mapped are moved disp positions to the left. */

		for (i=disp;i<row2;i++)
		{
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i-disp);
		}
		for (i=row2;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);

		/* go through list, and copy each term, after acting on each with
      /* Then as before */

		for (strip_list=S_L_N(strip_list);strip_list!=NULL;
		    strip_list=S_L_N(strip_list))
		{
			tab=S_MO_S(S_L_S(strip_list));

			for (i=0;i<disp;i++)
				C_I_I(S_T_IJ(ghost,0,i+dispr1),map[S_T_IJI(tab,0,i)]);

			for (i=disp;i<row1;i++)
				C_I_I(S_T_IJ(ghost,0,i-disp),map[S_T_IJI(tab,0,i)]);

			for (i=0;i<disp;i++)
				C_I_I(S_T_IJ(ghost,1,i+dispr2),map[S_T_IJI(tab,1,i)]);

			for (i=disp;i<row2;i++)
				C_I_I(S_T_IJ(ghost,1,i-disp),map[S_T_IJI(tab,1,i)]);

			mult_monopoly_monopoly(save_multiplier,S_MO_K(S_L_S(strip_list)),
			    root_multiplier);

			find_non_rowstandard_pos(ghost,&grow,&lcol);

			if (grow<0)
			{
				if ((lcol=find_non_root_standard_pos(ghost))<0)
				{
					construct_mo_mp(power,coeff,overall=callocobject());
					mult_apply_monopoly(root_multiplier,overall);

#if NORMALISE==1
					root_garnir_result(ghost,overall,root_all);
#else
					garnir_result(ghost,overall,root_all);
#endif
				}
				else
				{
					copy_tableaux(ghost,tab=callocobject());
					strip_juggle(tab,power,coeff);
					freeall(tab);
				}
			}
			else
			{
				root_juggle(ghost,power,coeff);
			}

			freeself(root_multiplier);
		}
	}
	else /* if (kappa>1) */
{  /* this is an even trickier case, where the symmetrised section needs
	 to be used at different positions to where it has been formed
	 in the canonical list, the entries to its right set up and
			 acted on by a hecke permutation, before resubmission. */

		dispr1=row1-disp;
		dispr2=row2-disp;

		/* This first loop defines the map for the last disp entries
	 of each row. */

		for (i=0;i<disp;i++)
			map[S_T_IJI(tab,1,i)]=2*(dispr2+i)+ostrip+1;

		for (i=0;i<disp+ostrip+row2-row1;i++)
			map[S_T_IJI(tab,0,i)]=2*(dispr1+1+i)-ostrip;

		for (;i<disp;i++)
			map[S_T_IJI(tab,0,i)]=row1+row2-disp+1+i;

		/* Then provide map for remainder of entries, which after being
	 mapped are moved disp positions to the left. */

		for (i=disp;i<=row2-root;i++)
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i-disp);

		for (;i<row2;i++)
			map[S_T_IJI(tab,1,i)]=dispr2+ostrip+1-disp+i;

		for (i=disp;i<row2+ostrip;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);

		for (;i<row1 && i<row2+ostrip+disp;i++)
			map[S_T_IJI(tab,0,i)]=2*(i+1-disp)-ostrip;

		for (;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=dispr2+1+i;

		/* go through list, and copy each term, after acting on each with
	 the above permutation */

		partit=s_t_u(tableau);
		temp=big_list=NULL;

		for (;strip_list!=NULL;strip_list=S_L_N(strip_list))
		{
			tab=S_MO_S(S_L_S(strip_list));

			m_u_t(partit,new=callocobject());

			for (i=0;i<disp;i++)
				m_i_i(map[S_T_IJI(tab,0,i)],S_T_IJ(new,0,i+dispr1));

			for (i=disp;i<row1;i++)
				m_i_i(map[S_T_IJI(tab,0,i)],S_T_IJ(new,0,i-disp));

			for (i=0;i<disp;i++)
				m_i_i(map[S_T_IJI(tab,1,i)],S_T_IJ(new,1,i+dispr2));

			for (i=disp;i<row2;i++)
				m_i_i(map[S_T_IJI(tab,1,i)],S_T_IJ(new,1,i-disp));

			/* copy list in the smae order */

			copy_list(S_MO_K(S_L_S(strip_list)),koeff=callocobject());
			b_sk_mo(new,koeff,monom=callocobject());
			b_sn_l(monom,NULL,ext=callocobject());
			if (temp==NULL)
				big_list=ext;
			else
				C_L_N(temp,ext);
			temp=ext;
		}

		/* then recursively multiply each by (s_i-q) for each appropriate i. */

		for (i=disp-1;i>=0;i--)
		{
			row1_pos=row2-disp+ostrip+i;
			row2_pos=row2-disp+i;
			s_entry=row1_pos+row2_pos+1;
			b_entry=s_entry+1;

			/* act on each term to double the list size */

			for (temp=big_list;temp!=NULL;temp=S_L_N(ext))
			{
				/* put a copy of the term AFTER the current one,
	       mutliply the new by -q, and transpose the old. */

				copy_monom(S_L_S(temp),monom=callocobject());
				mult_apply_monopoly(mq_mp,S_MO_K(monom));
				C_I_I(S_T_IJ(S_MO_S(S_L_S(temp)),0,row1_pos),s_entry);
				C_I_I(S_T_IJ(S_MO_S(S_L_S(temp)),1,row2_pos),b_entry);

				b_sn_l(monom,S_L_N(temp),ext=callocobject());
				C_L_N(temp,ext);
			}
		}

		/* now effect a hecke permutation on the list, in order to
	 take the first element of the big_list to tableau (the
	 current non root-standard tableau). Then ignore
	 the first (non root-standard) element; and resubmit for
	 recursive standardisation.
      */

		m_il_p(row1+row2,perm=callocobject());
		for (i=0;i<b_entry-root;i++)
			m_i_i(i+1,S_P_I(perm,i));
		for (i=row2_pos-root+2;i<row2;i++)
			m_i_i(S_T_IJI(tableau,1,i),
			    S_P_I(perm,S_T_IJI(S_MO_S(S_L_S(big_list)),1,i)-1));
		for (i=row1_pos;i<row1;i++)
			m_i_i(S_T_IJI(tableau,0,i),
			    S_P_I(perm,S_T_IJI(S_MO_S(S_L_S(big_list)),0,i)-1));

		temp=S_L_N(big_list);
		hecke_action_perm_on_lc(temp,perm); /* perm is freed in hecke_action_perm_on_lc */

		for (;temp!=NULL;temp=S_L_N(temp))
		{
			mult_monopoly_monopoly(save_multiplier,S_MO_K(S_L_S(temp)),
			    root_multiplier);
			tab=S_MO_S(S_L_S(temp));
			find_non_rowstandard_pos(tab,&grow,&lcol);

			if (grow<0)
			{
				if ((lcol=find_non_root_standard_pos(tab))<0)
				{
					construct_mo_mp(power,coeff,overall=callocobject());
					mult_apply_monopoly(root_multiplier,overall);

#if NORMALISE==1
					root_garnir_result(tab,overall,root_all);
#else
					garnir_result(tab,overall,root_all);
#endif
				}
				else
				{
					strip_juggle(tab,power,coeff);
				}
			}
			else
			{
				root_juggle(tab,power,coeff);
			}

			freeself(root_multiplier);
		}
		freeall(big_list);
	}

	/* restore the multiplier */

	b_ks_o(S_O_K(save_multiplier),S_O_S(save_multiplier),root_multiplier);
	C_O_K(save_multiplier,EMPTY);
	freeall(save_multiplier);
	SYM_free(map);
}


#if NORMALISE == 1          /* include if we want resultant coefficients
tidied up with respect to the root of unity */

root_garnir_result ( tableau,  mp_coeff,  acc_list)
	OP tableau;
	OP mp_coeff;
	OP acc_list;

/* This routine does the same as garnir_result() except that the
   coefficients are tidied up somewhat with regard to the root of
   unity. It is assumed that set_root_parameters() has been invoked.
   Adds  mp_coeff * tableau to our standard list: acc_list.
   tableau is unchanged, and copied when necessary. mp_coeff is
   destroyed. The list is maintained
   in lexicographic order (reading across rows, then top to bottom).
*/

{
	OP a,b,term;
	OP t,temp;
	INT co;

	if (empty_listp(acc_list))
	{
		if (root_normalise_monopoly(mp_coeff))
		{
			copy_tableaux(tableau,t=callocobject());
			b_sk_mo(t,mp_coeff,term=callocobject());

			c_l_s(acc_list,term);            /* assuming that the self exists */
		}	  		                  /* for an empty list */
		else
			freeall(mp_coeff);
	}
	else
	{  /* look for tableau in list */

		for (a=acc_list,b=NULL;
		    a!=NULL && (co=comp_tableaux(S_MO_S(S_L_S(a)),tableau))<0;
		    a=S_L_N(b=a));

		if (a==NULL || co>0)  /* not present */
		{
			if (root_normalise_monopoly(mp_coeff))
			{
				copy_tableaux(tableau,t=callocobject());
				b_sk_mo(t,mp_coeff,term=callocobject());

				if (b==NULL)     /* insert new first term (before a) */
				{
					b_ks_o(S_O_K(acc_list),S_O_S(acc_list),temp=callocobject());
					/* c_o_s(acc_list,NULL); */
					c_o_k(acc_list,EMPTY);
					b_sn_l(term,temp,acc_list);
				}
				else /* insert new term between b and a */
				{
					b_sn_l(term,a,temp=callocobject());
					C_L_N(b,temp);
				}
			}
			else
				freeall(mp_coeff);
		}
		else /* term is present - must just add coefficients */
		{
			insert(mp_coeff,S_MO_K(S_L_S(a)),add_koeff,NULL);
			root_normalise_monopoly(S_MO_K(S_L_S(a)));
		}
	}
}


INT root_normalise_monopoly (mono) OP mono;

/* some attempts to simplify the monopoly using the fact that its
      over a primitive p_root of unity. Return is 0 if result is
      identically zero (not fully implemented), else 1.
   */

{
	INT i,hi,lo;
	OP a,b,mopo;

	/* return if nothing to process */

	if (empty_listp(mono))
		return(0);

	/* set whole of working array to zeros */

	memset(spectrum,0,root*sizeof(INT));

	/* copy monopoly to working array and use q^root=1 to reduce exponents */

	for (a=mono;a!=NULL;a=S_L_N(b=a))
		spectrum[S_I_I(S_MO_S(S_L_S(a)))%root]+=S_I_I(S_MO_K(S_L_S(a)));

	/* if the highest power is tooo low, end processing */

	if (S_I_I(S_MO_S(S_L_S(b)))<root_cover)
		return(1);

	if (rootover2<root)              /* even root: reduce using q^(root/2)=-1 */
	{
		for (i=0;i<rootover2;i++)
			spectrum[i]-=spectrum[i+rootover2];
	}
	else /* try to improve using 1+q+q^2+ ... + q^(root-1) =0 */
	{
		if (root>1 && (hi=lo=spectrum[i=(root-1)]))
		{
			for (i--;i>0;i--)
				if (!spectrum[i])
					goto there;          /* don't change what we've got */

				else if (spectrum[i]>hi)
					hi=spectrum[i];
				else if (spectrum[i]<lo)
					lo=spectrum[i];

			if (lo>0)
				for (i=root-1;i>=0;i--)
					spectrum[i]-=lo;
			else if (hi<0)
				for (i=root-1;i>=0;i--)
					spectrum[i]-=hi;
		}
there:
		;
	}

	for (i=0;i<rootover2 && !spectrum[i];i++);
	if (i==rootover2)          /* polynomial is identically zero */
	{
		init(MONOPOLY,mono);
		return(0);
	}
	else
	{  /* hijack the first element */
		C_I_I(S_MO_S(S_L_S(mono)),i);
		C_I_I(S_MO_K(S_L_S(mono)),spectrum[i]);
		if (S_L_N(mono)!=NULL)
		{
			freeall(S_L_N(mono));
			C_L_N(mono,NULL);
		}
		while (1)  /* append the rest of the terms */
		{
			for (i++;i<rootover2 && !spectrum[i];i++);
			if (i==rootover2)
				break;
			construct_mo_mp(i,spectrum[i],mopo=callocobject());
			C_L_N(mono,mopo);
			mono=mopo;
		}
		return(1);
	}
}


#endif          /* for NORMALISE */


generate_sym_tableaux_list (piece, sym_list)
	INT piece;
	OP sym_list;

/* generates a list of tableaux which have been symmetrised across
   the final piece boxes of the second row and the subsequent
   strip-piece-1 boxes of the first row.
   Requires that set_root_parameters() has been invoked.
*/

{
	INT i,e;
	OP temp,child,momp,mon,ext;

	piece1=strip-piece+1;
	piece2=piece;

	/* fill into the ghost template the constant entries */

	left_const=row2-piece;
	right_const=row2+piece1;
	first_var=row2+left_const+1;

	for (i=0,e=1;i<left_const;i++)
	{
		C_I_I(S_T_IJ(ghost,0,i),e++);
		C_I_I(S_T_IJ(ghost,1,i),e++);
	}

	for (;i<row2;i++)
	{
		C_I_I(S_T_IJ(ghost,0,i),e);
		C_I_I(S_T_IJ(ghost,1,i),piece2+e++);
	}

	for (e+=piece2;i<row1;i++)
		C_I_I(S_T_IJ(ghost,0,i),e++);

	/* store a copy of this tableau in the list - the first */

	child=callocobject();
	copy_tableaux(ghost,child);

	construct_mo_mp(0,1,momp=callocobject());
	b_sk_mo(child,momp,mon=callocobject());
	b_sn_l(mon,NULL,ext=callocobject());
	accumulate=ext;

	/* now append to this list all permutations of the entries
      in the strip, which are standard in the top row. */

	coset_generate(strip,strip);

#if DUMP==1
	printf("This is what we get first...\n");
	dump_lc_list(accumulate);
#endif

	/* send this list for generic standardisation */

	init(LIST,sym_list);
	standardise_tableau_list(accumulate,sym_list);
	freeall(accumulate);

#if DUMP==1
	printf("This is what we get before factor removal...\n");
	dump_lc_list(sym_list);
#endif

	/* there is a factor of [piece]_q! (if [root]_q=0) here that
      should be removed */

	for (temp=sym_list;temp!=NULL;temp=S_L_N(temp))
		remove_mp_qnumber_fac(S_MO_K(S_L_S(temp)),piece);

#if DUMP==1
	printf("This is what we get after factor removal...\n");
	dump_lc_list(sym_list);
#endif

}


coset_generate (head, wag) INT head; INT wag;

/* Recursive function which creates all the terms in the coset.
   Method is much the same as that used for garnir_generate().
   See that routine for details.
   Requires that set_garnir_parameters() has been invoked.
*/

{
	INT k,i,j,p,s;
	OP child,momp,mon,ext;

	for (i=0;i<piece2;i++)
	{
		s=symmetry[i];

		if ( (s<wag || (s==wag+1 && s<head))

		    /* so that the permutation will be canonically represented */

		&& (j=inverse[s+1]) > i)

		/* s is in the bottom row, s+1 is anywhere to the right */

		{  /* swap the entries in sym & inv to keep track of permutation */

			inverse[symmetry[i]=s+1]=i;
			inverse[symmetry[j]=s]=j;

			/* place the entries in the tableau in the corresponding way */

			child=callocobject();
			copy_tableaux(ghost,child);

			for (k=0;k<piece2;k++)
				C_I_I(S_T_IJ(child,1,k+left_const),first_var+symmetry[k]);

			for (k=0;k<piece1;k++)
				C_I_I(S_T_IJ(child,0,k+row2),first_var+symmetry[k+piece2]);

			/* store tableau in the list */

			construct_mo_mp(0,1,momp=callocobject());
			b_sk_mo(child,momp,mon=callocobject());
			b_sn_l(mon,accumulate,ext=callocobject());
			accumulate=ext;

			/* resubmit with the updated permutation's info */

			if (s<wag)
				coset_generate(wag,s);
			else
				coset_generate(head,wag+1);

			/* remove permutation */

			inverse[symmetry[i]=s]=i;
			inverse[symmetry[j]=s+1]=j;
		}
	}
}


INT remove_mp_qnumber_fac ( mp,  qn)
	OP mp;
	INT qn;

/* The q_number which is passed is divided by [qn]_q! where is it
   assumed that we have a root of unity in force and that
   set_root_parameters() has already been invoked.
   all coefficients are multiplied by -1 since this is what is
   going to be required.
*/

{
	INT i,red;
	OP temp,momp,child,mon,ext;

	/* zero the vector */

	for (i=0;i<2*root;i++)
		C_I_I(s_v_i(poly,i),0L);

	/* put the monopoly into the vector reducing all powers: q^root=1. */

	if (!empty_listp(mp))
	{
		for (temp=mp;temp!=NULL;temp=S_L_N(temp))
		{
			red=S_I_I(S_MO_S(S_L_S(temp))) < 0
			    ? root-1-(-1-S_I_I(S_MO_S(S_L_S(temp))) % root)
			    /* for -ve powers */
			: S_I_I(S_MO_S(S_L_S(temp))) % root;
			/* for +ve powers */
			add_apply(S_MO_K(S_L_S(temp)),s_v_i(poly,red));
		}

		/* dont need the list anymore - but need its memory */

		freeself(mp);

		/* quotient out q_numbers [2]_q, [3]_q, ... , [qn]_q. */

		for (i=2;i<=qn;i++)
			remove_vec_qnumber(i);

		/* this is the place to simplify using the cyclotomic polynomial
	for root. For now, just apply q^(root/2)=-1 for even roots.
	Adjust the coefficients (using [root]_q=0 for odd root and
	1=-q^(root/2) for even root) so as to make the constant term 1.
	This is nice! 
     */

#if DUMP==1
		printf("Before rootover: ");
		println(poly);
#endif

		if (rootover2<root)
		{
			for (i=0;i<rootover2;i++)
			{
				C_I_I(s_v_i(poly,i),s_v_ii(poly,i)-s_v_ii(poly,i+rootover2));
				C_I_I(s_v_i(poly,i+rootover2),0L);
			}

			if (s_v_ii(poly,0L)!=1L)
			{
				C_I_I(s_v_i(poly,rootover2),1L-s_v_ii(poly,0L));
				C_I_I(s_v_i(poly,0L),1L);
			}
		}
		else
		{
			red=s_v_ii(poly,0L)-1;
			for (i=root-1;i>0;i--)
				C_I_I(s_v_i(poly,i),s_v_ii(poly,i)-red);
			C_I_I(s_v_i(poly,0L),1L);
		}

#if DUMP==1
		printf("After rootover: ");
		println(poly);
#endif


		/* reconstruct the monopoly list from the poly vector. start
	 the list with a null since its certain to be non-empty.
	 then all are multiplied by -1, since this is what is
	 eventually needed during p-root standardisation.  */

		accumulate=NULL;

		for (i=root-1;i>=0;i--)
			if (s_v_ii(poly,i))
			{
				construct_mo_mp(i,-s_v_ii(poly,i),momp=callocobject());
				C_L_N(momp,accumulate);
				accumulate=momp;
			}

#if DUMP==1
		printf("Reduced monpoly:\n");
		dump_monopoly(accumulate);
#endif

		b_ks_o(S_O_K(accumulate),S_O_S(accumulate),mp);
		C_O_K(accumulate,EMPTY);
		freeall(accumulate);
	}
}


INT remove_vec_qnumber ( qn) INT qn;

/* The poly vector object has been loaded with a polynomial which, under
   [root]_q=0, it assumed to have a factor of [qn]_q. This factor is
   removed. Assumed that qn<root.
   Certainly set_root_parameters() should have been invoked,
   as well as poly loaded.

   This process is not so easy to implement since the factor can be
   either [qn]_q or [root-qn]_q, or even a linear combination of the two.
*/

{
	INT i,p,sweep,stream,current;
	INT save1,save2;

	/* load the polynomial into a vector hiccup_log: so as to be able to check
      easily if [qn]_q is a factor - it is when all entries are the same. */

	for (i=0;i<qn;i++)
		C_I_I(s_v_i(hiccup_log,i),s_v_ii(poly,i));

	for (;i<root;i++)
		add_apply(s_v_i(poly,i),s_v_i(hiccup_log,i%qn));

	/* now judiciously add in muliples of [root]_q. sweep will allow 
      us to update hiccup_log easily. */

	sweep=root%qn;

	while (1)
	{

#if DUMP==1
		printf("The poly vector: ");
		println(poly);

		printf("The hiccup_log vector: ");
		println(hiccup_log);
#endif

		stream=s_v_ii(hiccup_log,qn-1);
		for (p=0;p<qn && stream <= (current=s_v_ii(hiccup_log,p));p++,stream=current);

		if (p==qn)
			break;        /* since all values are the same */

		/* add in [root]_q in appropriate place */

		stream-=current;

		for (i=p;i<p+root;i++)
			C_I_I(s_v_i(poly,i),s_v_ii(poly,i)+stream);

		for (i=0;i<sweep && p<qn;i++,p++)
			C_I_I(s_v_i(hiccup_log,p),s_v_ii(hiccup_log,p)+stream);
		for (p=0;i<sweep;i++,p++)
			C_I_I(s_v_i(hiccup_log,p),s_v_ii(hiccup_log,p)+stream);
	}

	/* now poly should(!) have [qn]_q factor explicitly: remove it */

	for (save1=s_v_ii(poly,i=qn-1);i>0;i--)
		C_I_I(s_v_i(poly,i),s_v_ii(poly,i)-s_v_ii(poly,i-1));

	for (i=qn;i<root+qn;i++)
	{
		save2=s_v_ii(poly,i);
		C_I_I(s_v_i(poly,i),save2-save1+s_v_ii(poly,i-qn));
		save1=save2;
	}

	/* the quotient remains in poly and there are no entries q^root & above */
}


/********************************************************************
 ********************************************************************
 ********************************************************************

   HICCUP routines to cheack that the generated representation
   matrices, actually satisfy the algebra relations.

   Programmed by Trevor Welsh, Bayreuth, November 1995.
  
 ********************************************************************
 ********************************************************************
 ********************************************************************/



INT check_hecke_generators (vector, p_root, flag)
	OP vector;
	OP p_root;
	INT flag;

/* checks that the vector of matrices satisfy the hecke algebra
   defining relations. The check is made with respect to the
   primitive p_root of unity, if p_root>0.
   If flag is non-zero, then the difference between the two sides
   of the particular relation is displayed.
*/

{
	INT i,j,ni;

	/* validate parameters */

	if (vector==NULL || S_O_K(vector)!=VECTOR)
	{
		printf("check_hecke_generators() did not receive a vector as it was expecting!\n");
		return(ERROR);
	}

	set_cyclotomic_parameters(p_root);

	ni=s_v_li(vector);

	for (i=0;i<ni;i++)
	{
		printf("%ldth square is ",i+1);
		switch (check_hecke_quadratic(s_v_i(vector,i),p_root,flag))
		{
		case 0:
			printf("O.K!\n");
			break;
		case 1:
			printf("O.K for primitive %ldth root!\n",S_I_I(p_root));
			break;
		case 2:
			printf("codswallop!\n");
			break;
		default:
			return(ERROR);
		}
	}

	for (i=1;i<ni;i++)
	{
		printf("%ldth braid is ",i);
		switch (check_braid(s_v_i(vector,i-1),s_v_i(vector,i),p_root,flag))
		{
		case 0:
			printf("O.K!\n");
			break;
		case 1:
			printf("O.K for primitive %ldth root!\n",S_I_I(p_root));
			break;
		case 2:
			printf("codswallop!\n");
			break;
		default:
			return(ERROR);
		}
	}

	for (i=2;i<ni;i++)
		for (j=0;j<i-1;j++)
		{
			printf("(%ld,%ld)th commute is ",i+1,j+1);
			switch (check_commute(s_v_i(vector,i),s_v_i(vector,j),p_root,flag))
			{
			case 0:
				printf("O.K!\n");
				break;
			case 1:
				printf("O.K for primitive %ldth root!\n",S_I_I(p_root));
				break;
			case 2:
				printf("codswallop!\n");
				break;
			default:
				return(ERROR);
			}
		}

	free_cyclotomic_parameters();

	return(OK);
}


INT check_hecke_quadratic (mat, p_root, flag)
	OP mat;
	OP p_root;
	INT flag;

/* Checks that the matrix satisfies (mat-q)(mat+1)=0. 
   If not and flag is non-zero, the LHS is displayed.
*/

{
	INT i,j,k,erm;
	OP id,mq,mo,f1,f2,fp;

	/* validate parameters */

	if (mat==NULL || S_O_K(mat)!=MATRIX)
	{
		printf("check_hecke_quadratic() did not receive a matrix as it was expecting!\n");
		return(ERROR);
	}

	k=s_m_hi(mat);

	id=callocobject();
	m_ilih_nm(k,k,id);
	for (i=0;i<k;i++)
		C_I_I(S_M_IJ(id,i,i),1L);

	construct_mo_mp(1,-1,mo=callocobject());

	mq=callocobject();
	m_ilih_nm(k,k,mq);
	for (i=0;i<k;i++)
	{
		c_o_k(S_M_IJ(mq,i,i),MONOPOLY);
		c_o_s(S_M_IJ(mq,i,i),S_O_S(mo));
	}

	f1=callocobject();
	add_matrix(mat,id,f1);
	freeall(id);

	f2=callocobject();
	add_matrix(mat,mq,f2);
	freeall(mo);
	for (i=0;i<k;i++)
		c_o_k(S_M_IJ(mq,i,i),EMPTY);
	freeall(mq);


	fp=callocobject();
	mult_matrix_matrix(f1,f2,fp);
	freeall(f1);
	freeall(f2);

	erm=check_zero_matrix(fp,p_root);

	if (flag && erm>1)
		println(fp);

	freeall(fp);
	return(erm);
}


INT check_braid (mat1, mat2, p_root, flag)
	OP mat1;
	OP mat2;
	OP p_root;
	INT flag;

/* checks that the matrices satisfy m1*m2*m1 == m2*m1*m2. 
   If not and flag is non-zero, the difference is displayed.
*/

{
	INT erm;
	INT i,j;
	OP mat12,mat121,mat212;

	/* validate parameters */

	if (mat1==NULL || mat2==NULL || S_O_K(mat1)!=MATRIX || S_O_K(mat2)!=MATRIX)
	{
		printf("check_braid() did not receive matrices as it was expecting!\n");
		return(ERROR);
	}

	mult_matrix_matrix(mat1,mat2,mat12=callocobject());
	mult_matrix_matrix(mat12,mat1,mat121=callocobject());
	mult_matrix_matrix(mat2,mat12,mat212=callocobject());
	freeall(mat12);

	for (i=s_m_hi(mat212)-1;i>=0;i--)
		for (j=s_m_li(mat212)-1;j>=0;j--)
			addinvers_apply(S_M_IJ(mat212,i,j));

	add_apply(mat121,mat212);
	freeall(mat121);

	erm=check_zero_matrix(mat212,p_root);

	if (flag && erm>1)
		println(mat212);

	freeall(mat212);

	return(erm);
}


INT check_commute (mat1, mat2, p_root, flag)
	OP mat1;
	OP mat2;
	OP p_root;
	INT flag;

/* checks that the matrices satisfy m1*m2 == m2*m1. 
   If not and flag is non-zero, the difference is displayed.
*/

{
	INT erm;
	INT i,j;
	OP mat12,mat21;

	/* validate parameters */

	if (mat1==NULL || mat2==NULL || S_O_K(mat1)!=MATRIX || S_O_K(mat2)!=MATRIX)
	{
		printf("check_commute() did not receive matrices as it was expecting!\n");
		return(ERROR);
	}

	mult_matrix_matrix(mat1,mat2,mat12=callocobject());
	mult_matrix_matrix(mat2,mat1,mat21=callocobject());

	for (i=s_m_hi(mat21)-1;i>=0;i--)
		for (j=s_m_li(mat21)-1;j>=0;j--)
			addinvers_apply(S_M_IJ(mat21,i,j));

	add_apply(mat12,mat21);
	freeall(mat12);

	erm=check_zero_matrix(mat21,p_root);

	if (flag && erm>1)
		println(mat21);

	freeall(mat21);

	return(erm);
}


static INT c_root=0,c_rootover2,cyclo_ready=0,cyclo_roof;
static OP tomic=NULL;
static INT *c_vec=NULL;


INT set_cyclotomic_parameters (p_root) OP p_root;

/* sets paramters needed by check_zero_matrix() at roots of unity. */

{
	OP a,b;
	INT i;

	if ( (c_root=S_I_I(p_root))>0 && !cyclo_ready++)
	{
		c_rootover2 = c_root&1 ? 0 : c_root/2;

		c_vec=(INT*)SYM_calloc(c_root,sizeof(INT));

		a=callocobject();
		tomic=callocobject();
		make_cyclotomic_monopoly(p_root,tomic);

		/* need highest power in cyclotomic */

		for (a=tomic;a!=NULL;a=S_L_N(b=a));
		cyclo_roof=S_I_I(S_MO_S(S_L_S(b)));

		/* Note that its coefficient must be +1 */
	}

	return(OK);
}

INT free_cyclotomic_parameters ()
{
	if (!--cyclo_ready)
	{
		freeall(tomic);
		tomic=NULL;
		SYM_free(c_vec);
		c_vec=NULL;
		c_root=0;
	}
}


INT check_zero_matrix ( mat,  p_root)
	OP mat;
	OP p_root;

/* checks that the passed matrix is zero at the appropriate
   root of unity.
   returns:  -1 ERROR;
	      0 matrix is zero, whatever the value of q;
	      1 matrix is zero, if q is primitive p_root of unity;
	      2 matrix is non-zero, if is not a primitive p_root of unity.
*/

{
	INT i,j,k,l,erm=0,non=0;
	OP a,op;

	if (mat==NULL || S_O_K(mat)!=MATRIX)
	{
		printf("check_null_matrix() did not receive a matrix as it was expecting!\n");
		return(ERROR);
	}

	set_cyclotomic_parameters(p_root);

	for (i=0;i<S_M_HI(mat);i++)
		for (j=0;j<S_M_LI(mat);j++)
		{
			switch (S_O_K(op=S_M_IJ(mat,i,j)))
			{
			case INTEGER:
				if (S_I_I(op)!=0)
				{
					erm=1;
					goto there;
				}
				break;
			case MONOPOLY:
				if (!empty_listp(op))
					if (c_root>0)
					{
						for (k=0;k<c_root;c_vec[k++]=0);
						for (a=op;a!=NULL;a=S_L_N(a))
							c_vec[S_I_I(S_MO_S(S_L_S(a)))%c_root]
							    +=S_I_I(S_MO_K(S_L_S(a)));

						/* if c_root is even, do the obvious reduction */
						/* don't bother!

		   if (c_rootover2)
		   {  for (k=c_rootover2;k<c_root;k++)
		         c_vec[k-c_rootover2]-=c_vec[k];
		      t=c_rootover2-1;
		   }
		   else
		      t=c_root-1;
                   */

						/* now reduce using the cyclotomic polynomial */

						for (k=c_root-1;k>=0;k--)
						{
							if (c_vec[k])
								if (k<cyclo_roof)
								{
/* code folded from here */
	/* code folded from here */
	erm=1;
	goto there;  /* entry is non-zero */
	/* unfolding */
/* unfolding */
								}
								else
								{
/* code folded from here */
	/* code folded from here */
	non++;       /* counts generic non-zeros */
	for (a=tomic;a!=NULL;a=S_L_N(a))
		c_vec[S_I_I(S_MO_S(S_L_S(a)))+k-cyclo_roof]
		    -=S_I_I(S_MO_K(S_L_S(a)))*c_vec[k];
	/* unfolding */
/* unfolding */
								}
						}
					}
					else
					{
						for (a=op;a!=NULL;a=S_L_N(a))
							if (S_I_I(S_MO_S(S_L_S(a))))
							{
								erm=1;
								goto there;    /* entry is non-zero */
							}
					}
				break;
			default:
				/* shouldn't be here! */
				printf("matrix has unrecognised entry!\n");
				break;

			}
		}

there:
	free_cyclotomic_parameters();
	if (erm)
		return(2);
	else if (non)
		return(1);
	else
		return(0);

}




/********************************************************************
 ********************************************************************
 ********************************************************************

   The following routines enable arbitrary hecke algebra elements
   to be added or multiplied. They are not used by any of the
   previous routines. They make use only of the routines
   set_useful_monopolies() and free_useful_monopolies.

 ********************************************************************
 ********************************************************************
 ********************************************************************/



INT hecke_add ( hecke1,  hecke2,  result)
	OP hecke1;
	OP hecke2;
	OP result;

/* Adds hecke1 and hecke2, each of which is an hecke algebra
   element expressed as a q-linear combination of permutations.
   Neither of the inputs is changed.
   The result is added to result.
   */

{
	OP go_perm,coeff;

	/* first validate the inputs */

	if (S_O_K(hecke1)!=LIST 
	    || (!empty_listp(hecke1)
	    && (S_O_K(S_L_S(hecke1)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke1))) != PERMUTATION )))
	{
		printf("hecke_mult() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	if (S_O_K(hecke2)!=LIST 
	    || (!empty_listp(hecke2)
	    && (S_O_K(S_L_S(hecke2)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke2))) != PERMUTATION )))
	{
		printf("hecke_mult() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	/* if result is not already a list, then make it one */

	if (S_O_K(result)!=LIST)
		init(LIST,result);

	/* return if there is nothing to process */

	if (empty_listp(hecke1) || empty_listp(hecke2))
		return(OK);

	/* If result is empty, copy hecke1 to it. Otherwise accumulate
      hecke1 to it. Then accumulate hecke2 to result.
   */

	if (empty_listp(result))
	{
		copy_list(hecke1,result);
	}
	else
	{
		for (go_perm=hecke1;go_perm!=NULL;go_perm=S_L_N(go_perm))
		{
			copy_list(S_MO_K(S_L_S(go_perm)),coeff=callocobject());
			hecke_accum(S_MO_S(S_L_S(go_perm)),coeff,result);
		}
	}

	for (go_perm=hecke2;go_perm!=NULL;go_perm=S_L_N(go_perm))
	{
		copy_list(S_MO_K(S_L_S(go_perm)),coeff=callocobject());
		hecke_accum(S_MO_S(S_L_S(go_perm)),coeff,result);
	}

	return(OK);
}


INT hecke_mult ( hecke1, hecke2, result)
	OP hecke1;
	OP hecke2;
	OP result;

/* Multiplies hecke1 and hecke2, each of which is an hecke algebra
   element expressed as a q-linear combination of permutations.
   Neither of the inputs is changed.
   The result is added to result.
   An ERROR might result if elements of the hecke algebras are
   permutations from differing groups. */

{
	OP go_perm,coeff,temp,imitate,perm_cop;

	/* first validate the inputs */

	if (S_O_K(hecke1)!=LIST 
	    || (!empty_listp(hecke1)
	    && (S_O_K(S_L_S(hecke1)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke1))) != PERMUTATION )))
	{
		printf("hecke_mult() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	if (S_O_K(hecke2)!=LIST 
	    || (!empty_listp(hecke2)
	    && (S_O_K(S_L_S(hecke2)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke2))) != PERMUTATION )))
	{
		printf("hecke_mult() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	/* if result is not already a list, then make it one */

	if (S_O_K(result)!=LIST)
		init(LIST,result);

	/* return if there is nothing to process */

	if (empty_listp(hecke1) || empty_listp(hecke2))
		return(OK);

	/* For each element of the hecke1 list, make a copy of the hecke2
      list, and act on it with a copy of the permutation. Then go
      though the resulting list, multiplying each by the
      coefficient of the permutation, and accumulating them to result.
   */

	imitate=callocobject();
	for (go_perm=hecke1;go_perm!=NULL;go_perm=S_L_N(go_perm))
	{
		copy_list(hecke2,imitate);
		copy_permutation(S_MO_S(S_L_S(go_perm)),perm_cop=callocobject());

		hecke_action_perm_on_hecke(imitate,perm_cop);

		for (temp=imitate;temp!=NULL;temp=S_L_N(temp))
		{
			mult_monopoly_monopoly(S_MO_K(S_L_S(go_perm)),S_MO_K(S_L_S(temp)),
			    coeff=callocobject());
			hecke_accum(S_MO_S(S_L_S(temp)),coeff,result);
		}
		freeself(imitate);
	}
	freeall(imitate);
	return(OK);
}


INT hecke_scale ( hecke,  power,  coeff)
	OP hecke;
	OP power;
	OP coeff;

/* Multiplies hecke, which is an hecke algebra element expressed as 
   a q-linear combination of permutations, by coeff*q^power.
   hecke is updated with the result.
*/

{
	OP go_perm,temp;

	/* first validate the inputs */

	if (S_O_K(hecke)!=LIST 
	    || (!empty_listp(hecke)
	    && (S_O_K(S_L_S(hecke)) != MONOM 
	    || S_O_K(S_MO_S(S_L_S(hecke))) != PERMUTATION )))
	{
		error("hecke_scale() did not receive a linear combination of permutations as it was expecting!\n");
		return(ERROR);
	}

	if (S_O_K(power)!=INTEGER || S_O_K(coeff)!=INTEGER)
	{
		error("hecke_scale() did not receive the INTEGER parameters it was expecting!\n");
		return(ERROR);
	}

	/* return if there is nothing to process */

	if (empty_listp(hecke))
		return(OK);

	/* For each element of the hecke list, multiply the coefficient. */

	for (go_perm=hecke;go_perm!=NULL;go_perm=S_L_N(go_perm))
	{
		if ( !empty_listp(temp=S_MO_K(S_L_S(go_perm))) )
			for (;temp!=NULL;temp=S_L_N(temp))
			{
				add_apply_integer_integer(power,S_MO_S(S_L_S(temp)));
				mult_apply_integer_integer(coeff,S_MO_K(S_L_S(temp)));
			}
	}

	return(OK);
}


INT hecke_action_perm_on_hecke ( heck,  permutation)
	OP heck;
	OP permutation;

/* Applies the hecke algebra permutation to the hecke algebra
   element (linear combination of permutations).
   This list is updated with the result and the permutation is
   freed. There is no attempt to collect terms in the result.
   Requires that set_garnir_parameters() has been invoked.
   An ERROR may be generated if permutation is from a group bigger
   than the entries from heck.
*/

{
	INT i,j,k,lo_one,hi_one;
	OP perm,temp,new,coeff,monom,ext;

	if (empty_listp(heck))
	{
		freeall(permutation);
		return(OK);
	}

	set_useful_monopolies();

	while (1)
	{  /* look for a right factor s_k in reduced expression for permutation */

		for (k=S_P_LI(permutation)-1;k>0
		    && S_P_II(permutation,k)>S_P_II(permutation,k-1);k--);

		if (!k)  /* none present */
			break;

		/* now apply s_k to hecke algebra list */

		temp=heck;
		while (temp!=NULL)
		{
			perm=S_MO_S(S_L_S(temp));
			lo_one=hi_one= -1;

			/* trawl through positions of perm looking for k & k+1 */

			for (i=0;i<S_P_LI(perm);i++)
				if (S_P_II(perm,i)==k+1)
				{
					if (lo_one>-1)      /* position of k already located */
					{
						/* enact the tranposition; coefficient is unchanged */

						C_I_I(S_P_I(perm,lo_one),k+1);
						C_I_I(S_P_I(perm,i),k);

						temp=S_L_N(temp);
						goto there;       /* end processing of current perm */
					}
					else
					{
						hi_one=i;
					}
				}
				else if (S_P_II(perm,i)==k)
				{
					if (hi_one>-1)      /* position of k+1 already located */
					{
						/* form a new element in the list, obtained by
		     simple tranposition and multiply coeff by q. */

						copy_permutation(perm,new=callocobject());
						C_I_I(S_P_I(new,hi_one),k);
						C_I_I(S_P_I(new,i),k+1);
						mult_monopoly_monopoly(q_mp,S_MO_K(S_L_S(temp)),
						    coeff=callocobject());
						b_sk_mo(new,coeff,monom=callocobject());
						b_sn_l(monom,S_L_N(temp),ext=callocobject());
						C_L_N(temp,ext);

						/* multiply old coefficient by q-1 */

						mult_apply_monopoly(qm1_mp,S_MO_K(S_L_S(temp)));

						temp=S_L_N(ext);
						goto there;       /* end processing of current perm */
					}
					else
					{
						lo_one=i;
					}
				}

			/* if we get here then we have not found both k & k+1 */

			fprintf(stderr,"Incompatible permutations in hecke_action_perm_on_hecke()\n");
			free_useful_monopolies();
			return(ERROR);

there:
			;
		}
		/* need to change the permutation */

		i=S_P_II(permutation,k-1);
		C_I_I(S_P_I(permutation,k-1),S_P_II(permutation,k));
		C_I_I(S_P_I(permutation,k),i);

	}
	/* free the permutation since it has been corrupted */

	freeall(permutation);
	free_useful_monopolies();
	return(OK);
}



static void hecke_accum ( perm,  mp_coeff,  acc_list)
	OP perm;
	OP mp_coeff;
	OP acc_list;

/* Adds  mp_coeff * perm to our list: acc_list. perm is unchanged, and
   copied when necessary. mp_coeff is incorporated or destroyed.
   The list is maintained in lexicographic order.
*/

{
	OP a,b,term;
	OP t,temp;
	INT co;

	if (empty_listp(acc_list))
	{
		t=callocobject();
		copy_permutation(perm,t);
		term=callocobject();
		b_sk_mo(t,mp_coeff,term);
		c_l_s(acc_list,term);
	}
	else
	{  /* look for tableau in list */

		for (a=acc_list,b=NULL;
		    a!=NULL && (co=comp_permutation(S_MO_S(S_L_S(a)),perm))<0;
		    a=S_L_N(b=a));

		if (a==NULL || co>0)  /* not present */
		{
			t=callocobject();
			copy_permutation(perm,t);
			term=callocobject();
			b_sk_mo(t,mp_coeff,term);

			if (b==NULL)     /* insert new first term (before a) */
			{
				b_ks_o(S_O_K(acc_list),S_O_S(acc_list),temp=callocobject());
				/* c_o_s(acc_list,NULL); */
				C_O_K(acc_list,EMPTY);
				b_sn_l(term,temp,acc_list);
			}
			else /* insert new term between b and a */
			{
				b_sn_l(term,a,temp=callocobject());
				C_L_N(b,temp);
			}
		}
		else /* term is present - must just add coefficients */
		{
			insert(mp_coeff,S_MO_K(S_L_S(a)),add_koeff,NULL);

		}
	}
}



/********************************************************************
 ********************************************************************
 ********************************************************************

   The following routines are/were useful for debugging the above!
   Otherwise, they are not required.

 ********************************************************************
 ********************************************************************
 ********************************************************************/



#ifdef DUMP


dump_lc_list (list) OP list;

{
	OP mo;

	if (list==NULL)
	{
		printf("list is NULL!");
	}
	else if (S_O_K(list)!=LIST)
	{
		printf("this is not a list!\n");
	}
	else if ( (list->ob_self).ob_list==NULL )
	{
		printf("list has null self!\n");
	}
	else if (S_L_S(list)==NULL)
	{
		printf("list self part is absent! (empty list?)\n");

		/* this should be the case for an empty list (i.e. zero) */
	}
	else
	{
		mo=S_L_S(list);

		printf("term (kind %ld) is (kind %ld):\n",S_O_K(mo),S_O_K(S_MO_S(mo)));
		println(S_MO_S(mo));
		printf("coefficient (kind %ld) is:\n",S_O_K(S_MO_K(mo)));
		dump_monopoly(S_MO_K(mo));

		list=S_L_N(list);
		if (list!=NULL)
			dump_lc_list(list);
	}
}


dump_monopoly (mp)
	OP mp;
{
	OP mo;

	if (mp==NULL)
	{
		printf("monopoly is NULL!");
	}
	else if (S_O_K(mp)!=MONOPOLY)
	{
		printf("this is not a monopoly!\n");
	}
	else if ( (mp->ob_self).ob_list==NULL )
	{
		printf("monopoly has null self!\n");
	}
	else if (S_L_S(mp)==NULL)
	{
		printf("monopoly self part is absent! (empty list?)\n");

		/* this should be the case for an empty list (i.e. zero) */

	}
	else
	{
		mo=S_L_S(mp);
		printf("+ (kind %ld) ",S_O_K(mo));
		fflush(stdout);
		printf("(%d * q^(%d)) ",
		    S_I_I(S_MO_K(S_L_S(mp))),
		    S_I_I(S_MO_S(S_L_S(mp))));
		mp=S_L_N(mp);
		if (mp==NULL)
			printf(".\n");
		else
			dump_monopoly(mp);
	}
}


strip_buggle ( tableau) OP tableau;


{
	INT i,disp,dispr1,dispr2;
	OP save_multiplier,overall,strip_list,tab;
	INT row1_pos,row2_pos,b_entry,s_entry;
	OP temp,ext,monom,koeff,new,big_list,partit,perm;
	FILE *fp;

	if ((lcol=find_non_root_standard_pos(tableau))<0)
	{
		printf("Input tableau is standard.\n");
		return;
	}

	/* identify the appropriate list: i becomes no of symmetrised boxes
      in 2nd row. disp is the rightward distance from the first box
      being symmetrised to the rightmost possible root-1 2nd row boxes
      symmetrisation. */

	disp=row2-lcol-root+1;
	i= disp<0 ? row2-lcol : root-1;

	printf("lcol=%ld, disp=%ld.\n",lcol,disp);

	strip_list=s_v_i(symmetrised,i-1);

	if (S_O_K(strip_list)==EMPTY)
	{  /* need to generate the model expression for this standardisation */

		generate_sym_tableaux_list(i,strip_list);
	}

	/* identify the map from the canonical strip relation to the current
      problem using the first term in the list. */

	tab=S_MO_S(S_L_S(strip_list));

	if (disp<=0)
{  /* easy case - use stored list pretty much as it stands. First form
	 the map from the canonical non strip-standard tableau (this is
			 stored as the first element in the list). */

		printf("1st case: lcol=%ld, disp=%ld.\n",lcol,disp);

		for (i=0;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i);
		for (i=0;i<row2;i++)
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i);
	}
	else if (kappa==1)
{  /* this is a trickier case, where the symmetrised section needs
	 to be used at different positions to where it has been formed
			 in the canonical list */

		printf("2nd case: lcol=%ld, disp=%ld.\n",lcol,disp);

		dispr1=row1-disp;
		dispr2=row2-disp;

		/* This first loop defines the map for the last disp entries
	 of each row. */

		for (i=0;i<disp;i++)
		{
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i+dispr1);
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i+dispr2);
		}

		/* Then provide map for remainder of entries, which after being
	 mapped are moved disp positions to the left. */

		for (i=disp;i<row2;i++)
		{
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i-disp);
		}
		for (i=row2;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);
	}
	else /* if (kappa>1) */
{  /* this is an even trickier case, where the symmetrised section needs
	 to be used at different positions to where it has been formed
	 in the canonical list, the entries to its right set up, permuted,
			 and enacted upon. */

		printf("3rd case: lcol=%ld, disp=%ld.\n",lcol,disp);

		dispr1=row1-disp;
		dispr2=row2-disp;

		/* This first loop defines the map for the last disp entries
	 of each row. */

		for (i=0;i<disp;i++)
			map[S_T_IJI(tab,1,i)]=2*(dispr2+i)+ostrip+1;

		for (i=0;i<disp+ostrip+row2-row1;i++)
			map[S_T_IJI(tab,0,i)]=2*(dispr1+1+i)-ostrip;

		for (;i<disp;i++)
			map[S_T_IJI(tab,0,i)]=row1+row2-disp+1+i;

		/* Then provide map for remainder of entries, which after being
	 mapped are moved disp positions to the left. */

		for (i=disp;i<=row2-root;i++)
			map[S_T_IJI(tab,1,i)]=S_T_IJI(tableau,1,i-disp);

		for (;i<row2;i++)
			map[S_T_IJI(tab,1,i)]=dispr2+ostrip+1-disp+i;

		for (i=disp;i<row2+ostrip;i++)
			map[S_T_IJI(tab,0,i)]=S_T_IJI(tableau,0,i-disp);

		for (;i<row1 && i<row2+ostrip+disp;i++)
			map[S_T_IJI(tab,0,i)]=2*(i+1-disp)-ostrip;

		for (;i<row1;i++)
			map[S_T_IJI(tab,0,i)]=dispr2+1+i;

		printf("[ ");
		for (i=1;i<=row1+row2;i++)
			printf("%2ld ",i);
		printf("]\n");
		printf("[ ");
		for (i=1;i<=row1+row2;i++)
			printf("%2ld ",map[i]);
		printf("]\n");

		/* go through list, and copy each term, after acting on each with
	 the above permutation */

		partit=s_t_u(tableau);
		temp=big_list=NULL;

		for (;strip_list!=NULL;strip_list=S_L_N(strip_list))
		{
			tab=S_MO_S(S_L_S(strip_list));

			m_u_t(partit,new=callocobject());

			for (i=0;i<disp;i++)
				m_i_i(map[S_T_IJI(tab,0,i)],S_T_IJ(new,0,i+dispr1));

			for (i=disp;i<row1;i++)
				m_i_i(map[S_T_IJI(tab,0,i)],S_T_IJ(new,0,i-disp));

			for (i=0;i<disp;i++)
				m_i_i(map[S_T_IJI(tab,1,i)],S_T_IJ(new,1,i+dispr2));

			for (i=disp;i<row2;i++)
				m_i_i(map[S_T_IJI(tab,1,i)],S_T_IJ(new,1,i-disp));

			/* need to change this so that the list
	    is copied in the correct order */

			copy_list(S_MO_K(S_L_S(strip_list)),koeff=callocobject());
			b_sk_mo(new,koeff,monom=callocobject());
			b_sn_l(monom,NULL,ext=callocobject());
			if (temp==NULL)
				big_list=ext;
			else
				C_L_N(temp,ext);
			temp=ext;
		}

		/* then recursively multiply each by (s_i-q) for each appropriate i. */

		for (i=disp-1;i>=0;i--)
		{
			row1_pos=row2-disp+ostrip+i;
			row2_pos=row2-disp+i;
			s_entry=row1_pos+row2_pos+1;
			b_entry=s_entry+1;

			/* act on each term to double the list size */

			for (temp=big_list;temp!=NULL;temp=S_L_N(ext))
			{
				/* put a copy of the term AFTER the current one,
	       mutliply the new by -q, and transpose the old. */

				copy_monom(S_L_S(temp),monom=callocobject());
				mult_apply_monopoly(mq_mp,S_MO_K(monom));
				C_I_I(S_T_IJ(S_MO_S(S_L_S(temp)),0,row1_pos),s_entry);
				C_I_I(S_T_IJ(S_MO_S(S_L_S(temp)),1,row2_pos),b_entry);

				b_sn_l(monom,S_L_N(temp),ext=callocobject());
				C_L_N(temp,ext);
			}
		}


		fp=fopen("dump1.dat","w");
		fprintln(fp,big_list);
		fclose(fp);


		/* now effect a hecke permutation on the list, in order to
	 take the first element of the big_list to tableau (the
	 current non root-standard tableau). Then ignore
	 the first (non root-standard) element; and resubmit for
	 recursive standardisation.
      */

		m_il_p(row1+row2,perm=callocobject());
		for (i=0;i<b_entry-root;i++)
			m_i_i(i+1,S_P_I(perm,i));

		printf("Required 1 permutation is:\n");
		println(perm);

		for (i=row2_pos-root+2;i<row2;i++)
			m_i_i(S_T_IJI(tableau,1,i),
			    S_P_I(perm,S_T_IJI(S_MO_S(S_L_S(big_list)),1,i)-1));

		printf("Required 2 permutation is:\n");
		println(perm);

		for (i=row1_pos;i<row1;i++)
			m_i_i(S_T_IJI(tableau,0,i),
			    S_P_I(perm,S_T_IJI(S_MO_S(S_L_S(big_list)),0,i)-1));

		printf("Required 4 permutation is:\n");
		println(perm);

		hecke_action_perm_on_lc(big_list,perm);

		fp=fopen("dump2.dat","w");
		fprintln(fp,big_list);
		fclose(fp);

		freeall(big_list);
	}

}


#endif



