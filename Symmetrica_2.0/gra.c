#include "def.h"
#include "macro.h"

/* pre version of graph */

/* grabasic.c */
/* AK 090889 */

#ifdef GRAPHTRUE
OBJECTKIND s_gr_k(a) OP a;
/* AK 210889 */ /* AK 210891 V1.3 */
{
	OBJECTSELF b;
	b = s_o_s(a);
	return(b.ob_graph->gr_kind);
}
#endif	 /* GRAPHTRUE */

#ifdef GRAPHTRUE
OP s_gr_s(a) OP a;
/* AK 210889 */ /* AK 210891 V1.3 */
{
	OBJECTSELF b;
	b = s_o_s(a);
	return(b.ob_graph->gr_self);
}
#endif	 /* GRAPHTRUE */

#ifdef GRAPHTRUE
INT c_gr_s(a,c) OP a,c;
/* AK 210889 */ /* AK 210891 V1.3 */
{
	OBJECTSELF b;
	b = s_o_s(a);
	b.ob_graph->gr_self = c;
	return(OK);
}
#endif	

#ifdef GRAPHTRUE
INT c_gr_k(a,c) OP a; OBJECTKIND c;
/* change_graph_kind */
/* AK 210889 */ /* AK 210891 V1.3 */
{
	OBJECTSELF b;
	b = s_o_s(a);
	(b.ob_graph)->gr_kind = c;
	return(OK);
}
#endif	

INT m_sk_gr(self,kind,erg) OP self,erg; OBJECTKIND kind;
/* make_self_kind_graph */
/* AK 210889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	struct graph *mallocerg;

	mallocerg = (struct graph *) malloc(sizeof(struct graph));

	if (mallocerg == NULL) {
		error("m_sk_gr:no memory"); 
		return(ERROR); 
	}

	c_o_s(erg,mallocerg);
	c_o_k(erg,GRAPH);
	c_gr_k(erg,kind); 
	c_gr_s(erg,self);
	return(OK);
#else
	error("m_sk_gr:GRAPH not available");
	return(ERROR);
#endif	
}

#ifdef GRAPHTRUE
OP s_gr_kn(a) OP a;
/* select_graph_knotenliste */
/* AK 210889 */ /* AK 210891 V1.3 */
{

	/* die knoten elemente sind das erste vector element im self vector */
	OP h = s_gr_s(a);
	if (s_o_k(h) != VECTOR) {
		error("s_gr_kn:not VECTOR");
		return(NULL); 
	}

	return(s_v_i(h,0L));
}
#endif	

OP s_gr_kni(a,i) OP a; INT i;
/* select_graph_knotenliste das ite element*/
/* AK 210889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	return(s_v_i(s_gr_kn(a),i));
#else
	error("s_gr_kni:GRAPH not available");
	return(NULL);
#endif	
}


#ifdef GRAPHTRUE
OP s_gr_na(a) OP a;
/* select_graph_nachbarschaftsliste */
/* AK 210889 */ /* AK 210891 V1.3 */
{
	/* die nachbarschaftsliste ist das 
	zweite vector element im self vector */
	return(s_v_i(s_gr_s(a),1L));
}
#endif	

OP s_gr_nai(a,i) OP a; INT i;
/* select_graph_nachbarschaftsliste das ite Element, was selber
ein VECTOR ist */
/* AK 210889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	return(s_v_i(s_gr_na(a),i));
#else
	error("s_gr_nai:GRAPH not available");
	return(NULL);
#endif	
}

#ifdef GRAPHTRUE
OP s_gr_koor(a) OP a;
/* select_graph_koordinaten */
/* AK 250889 */ /* AK 210891 V1.3 */
{
	/* die koordinatenliste ist das 
	dritte vector element im self vector */
	return(s_v_i(s_gr_s(a),2L));
}
#endif

OP s_gr_koori(a,i) OP a; INT i;
/* select_graph_koordinatenliste das ite Element, was selber
ein VECTOR ist */
/* AK 250889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	return(s_v_i(s_gr_koor(a),i));
#else
	error("s_gr_koori:GRAPH not available");
	return(NULL);
#endif	
}

OP s_gr_xkoori(a,i) OP a; INT i;
/* select_graph_koordinatenliste das ite Element, was selber
ein VECTOR ist und davon die xkoordinate */
/* AK 250889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	return(s_v_i(s_gr_koori(a,i),0L));
#else
	error("s_gr_xkoori:GRAPH not available");
	return(NULL);
#endif	
}


OP s_gr_ykoori(a,i) OP a; INT i;
/* select_graph_koordinatenliste das ite Element, was selber
ein VECTOR ist und davon die ykoordinate */
/* AK 250889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	return(s_v_i(s_gr_koori(a,i),1L));
#else
	error("s_gr_ykoori:GRAPH not available");
	return(NULL);
#endif	
}



#ifdef GRAPHTRUE
INT m_vector_graph(vector,kf,erg) OP vector,erg; INT (* kf)();
/* macht aus einem vector von objecten und einer funktion kf
die testet ob zwischen zwei objecten eine kante ist einen
graphen */
/* kf gibt true oder false zurueck */
/* AK 210889 */ /* AK 210891 V1.3 */
{

	INT i,j;
	INT dt=0;

	m_sk_gr(callocobject(),NACHBARLISTE,erg);
	if (dt) {
		fprintf(stderr,"m_vector_graph:erg(1)=");
		fprintln(stderr,erg);
	}
	m_il_v(2L,s_gr_s(erg));
	if (dt) {
		fprintf(stderr,"m_vector_graph:erg(2)=");
		fprintln(stderr,erg);
	}
	copy(vector,s_gr_kn(erg));
	if (dt) {
		fprintf(stderr,"m_vector_graph:knotenvector=");
		fprintln(stderr,s_gr_kn(erg));
	}
	/* die knoten sind die elemente im vector */
	m_il_v(s_v_li(vector),s_gr_na(erg));
	if (dt) {
		fprintf(stderr,"m_vector_graph:nachbarschaftsliste=");
		fprintln(stderr,s_gr_na(erg));
	}
	/* die nachbarschaftsliste hat die laenge des vectors */
	for (i=0;i<s_v_li(vector);i++)
		for (j=0;j<s_v_li(vector);j++)
		{
			INT kferg;
			OP hv;
			hv = s_gr_nai(erg,i);
			/* hv ist der vector in der nachbarschaftsliste */
			kferg = (*kf)(s_gr_kni(erg,i),s_gr_kni(erg,j));
			if (kferg == TRUE) /* kante i,j */
			{
				if (emptyp(hv))
					/* die nachbarschaftsliste ist leer */
					m_il_v(1L,hv);
				else inc(hv);
				/* nun eintrag von j in die liste von i an der
				letzten position */
				m_i_i(j,s_v_i(hv,s_v_li(hv)-1));
			}
		}
	return(OK);
}
#endif	

#ifdef GRAPHTRUE
INT fprint_graph(f,a) FILE *f; OP a;
/* AK 210889 */ /* AK 210891 V1.3 */
{
	if (not emptyp(s_gr_s(a))) fprint(f,s_gr_na(a));
	return(OK);
}
#endif	

#ifdef GRAPHTRUE
INT copy_graph(a,b)  OP b,a;
/* AK 210889 */ /* AK 210891 V1.3 */
{
	m_sk_gr(callocobject(),(OBJECTKIND)0,b);
	c_gr_k(b,s_gr_k(a));
	copy(s_gr_s(a),s_gr_s(b));
	return(OK);
}
#endif	

INT freeself_graph(a)  OP a;
/* AK 230889 */ /* AK 210891 V1.3 */
{
#ifdef GRAPHTRUE
	OBJECTSELF d;

	freeall(s_gr_s(a)); 
	d = S_O_S(a);
	free(d.ob_graph); 
	return(OK);
#else
	error("freeself_graph:GRAPH not available");
	return(ERROR);
#endif	
}

/* verband.c */
/* AK 250889 */
/* verband ist ein graph in dem ich eine funktion habe, die mir die schicht
ausgibt, er ist leichter zu plazieren */
/* plaziert wird stets in einem feld XDIM x YDIM */
#define XDIM 100000L
#define YDIM 100000L

#ifdef GRAPHTRUE
INT plaziere_verband(a,lf) OP a; INT (*lf)();
/* a ist graph ,lf ist levelfunction */
/* AK 250889 */ /* AK 210891 V1.3 */
{
	OP b,c,d;
	INT dt=1,i;
	if (s_v_li(s_gr_s(a)) < 3L) inc(s_gr_s(a));
	/* koordinaten anhaengen */
	if (not emptyp(s_gr_koor(a))) {
		return(OK);
		/* bereits plaziert */
	}
	m_il_v(s_v_li(s_gr_kn(a)),s_gr_koor(a));
	/* koordinatenliste erstellen */
	b = callocobject(); 
	c = callocobject();
	get_level_vector_of_verband(a,lf,b,c);
	if (dt) {
		fprintf(stderr,"plaziere_verband:levelvector = ");
		fprintln(stderr,b);
		fprintf(stderr,"plaziere_verband:platzvector = ");
		fprintln(stderr,c);
	}
	/* plazieren nun zweidimensional */
	d = callocobject(); 
	copy(b,d);
	for (i=s_v_li(d)-1;i>=0;i--)
		m_i_i(XDIM / (s_v_ii(d,i)+1) , s_v_i(d,i));
	/* in d steht der abstand zwischen den elementen in der iten 
	schicht */

	for (i=s_v_li(s_gr_koor(a))-1; i>=0; i--)
	{
		m_il_v(2L,s_gr_koori(a,i));
		m_i_i(s_v_ii(c,i) * (YDIM / s_v_li(b)), 
		    s_gr_ykoori(a,i));
		m_i_i(s_v_ii(d,s_v_ii(c,i)) * s_v_ii(b,s_v_ii(c,i)),
		    s_gr_xkoori(a,i));
		dec(s_v_i(b,s_v_ii(c,i)));
	}
	if (dt) {
		fprintf(stderr,"plaziere_verband:koordinaten = ");
		fprintln(stderr,s_gr_koor(a)); 
	}
	freeall(b); 
	freeall(c); 
	freeall(d);
	return(OK);
}
#endif /* GRAPHTRUE */
#ifdef GRAPHTRUE
INT get_level_vector_of_verband(a,lf,b,c) OP a,b,c; INT (*lf)();
/* AK 250889 */
/* ergebnis ist ein vector b mit eintrag an der stelle i, wieviel
knoten in dieser schicht und ein vector c, der angibt
in welcher schicht der ite knoten 
lf ist levelfunction */ /* AK 210891 V1.3 */
{
	OP d=NULL;
	INT i,mmm;
	m_il_v(s_v_li(s_gr_kn(a)),c);
	for (i=s_v_li(s_gr_kn(a))-1;i>=0; i--)
	{
		(*lf)(s_gr_kni(a,i),s_v_i(c,i));
		if (d== NULL) {
			d = callocobject();
			copy(s_v_i(c,i),d);
		}
		else if (lt(s_v_i(c,i),d)) copy(s_v_i(c,i),d);
	}
	/* d ist nun das minimum der level */
	/* mmm wird index auf maximum */
	mmm = 0L;
	for (i=s_v_li(s_gr_kn(a))-1;i>=0; i--)
	{
		sub(s_v_i(c,i),d,s_v_i(c,i));
		if (gr(s_v_i(c,i),s_v_i(c,mmm))) mmm = i;
	}

	/* der level wert 0 ist nun die unterste schicht */
	/* mmm ist zeiger auf oberste schicht */
	/* mmm wird anzahl der schichten */
	mmm = s_v_ii(c,mmm)+1 ;
	m_il_v(mmm,b);
	for (i=0;i<mmm;i++) m_i_i(0L,s_v_i(b,i));
	for (i=s_v_li(s_gr_kn(a))-1;i>=0; i--)
		inc(s_v_i(b,s_v_ii(c,i)));

	freeall(d);
	return(OK);
}

#endif /* GRAPHTRUE */

#ifdef GRAPHTRUE
INT latex_verband(a) OP a;
/* AK 250889 */
/* der verband muss bereits plaziert sein */
/* AK 070291 V1.2 prints to texout */ /* AK 210891 V1.3 */
{
	INT i,j;

	fprintf(texout,"\n\\begin{picture}(%d,%d)\n",XDIM,YDIM);
	for (i=s_v_li(s_gr_koor(a))-1; i>=0 ;i--)
	{
		fprintf(texout,"\\put(%d,%d){ \n",s_i_i(s_gr_xkoori(a,i)),
		    s_i_i(s_gr_ykoori(a,i)));

		tex(s_gr_kni(a,i));
		fprintf(texout,"}\n");
	}
	/* nun kommen die verbindungen */
	for (i=s_v_li(s_gr_koor(a))-1; i>=0 ;i--)
		for (j=0; j<s_v_li(s_gr_nai(a,i)); j++)
		{
			INT xanfang = s_i_i(s_gr_xkoori(a,i));
			INT yanfang = s_i_i(s_gr_ykoori(a,i));
			INT xende=s_i_i(s_gr_xkoori(a,s_v_ii(s_gr_nai(a,i),j)));
			INT yende=s_i_i(s_gr_ykoori(a,s_v_ii(s_gr_nai(a,i),j)));
			if (i>s_v_ii(s_gr_nai(a,i),j))
				latex_line( xanfang,yanfang, xende,yende);
		}
	fprintf(stderr,"\n\\end{picture}\n");
	return OK;
}
#endif /* GRAPHTRUE */

#ifdef GRAPHTRUE
INT latex_line(vonx,vony,nachx,nachy) INT vonx,vony,nachx,nachy;
/* latex befehl um line zu zeichen */
/* AK 070291 V1.2  prints to texout instead of stdout */ /* AK 210891 V1.3 */
{
	fprintf(texout,"\\bezier{%d}",(nachx-vonx)/1000+(nachy-vony)/1000);
	fprintf(texout,"(%d,%d)",vonx,vony);
	fprintf(texout,"(%d,%d)", (vonx+nachx)/2, (vony+nachy)/2);
	fprintf(texout,"(%d,%d)\n",nachx,nachy);
	return OK;
}
#endif /* GRAPHTRUE */


/* AK 240603 */
/* routines for the managment of adjacency matrices */
INT add_adjacency_matrix(a,b,c) OP a,b,c;
/* AK builds the adjacancy matrix corresponding to the
   disjoint union of two graphs */
/* AK 240603 */
{
    INT erg = OK;
    INT i,j;
    CTTO(MATRIX,INTEGERMATRIX,"add_adjacency_matrix(1)",a);
    CTTO(MATRIX,INTEGERMATRIX,"add_adjacency_matrix(2)",b);
    SYMCHECK(S_M_HI(a) != S_M_LI(a),"add_adjacency_matrix(1):not quadratic");
    SYMCHECK(S_M_HI(b) != S_M_LI(b),"add_adjacency_matrix(1):not quadratic");
    CE3(a,b,c,add_adjacency_matrix);
    m_ilih_nm(S_M_HI(a)+S_M_HI(b),S_M_HI(a)+S_M_HI(b),c);
    for (i=0;i<S_M_HI(a);i++)
    for (j=0;j<S_M_LI(a);j++)
        if (i!=j) M_I_I(S_M_IJI(a,i,j),S_M_IJ(c,i,j));
    for (i=0;i<S_M_HI(b);i++)
    for (j=0;j<S_M_LI(b);j++)
        if (i!=j) M_I_I(S_M_IJI(a,i,j),S_M_IJ(c,S_M_HI(a)+i,S_M_LI(a)+j));

    ENDR("add_adjacency_matrix");
}

INT random_adjacency_matrix(n,a) OP n,a;
/* computes the adjacency matrix of random graph */
/* AK 240603 */
{
    INT erg = OK;
    INT i,j,k;

    CTO(INTEGER,"random_adjacency_matrix(1)",n);
    SYMCHECK(S_I_I(n) < 0,"random_adjacency_matrix:negative input");
    m_ilih_nm(S_I_I(n),S_I_I(n),a);
    C_O_K(a,INTEGERMATRIX);
    k=S_I_I(n)/3+1;
    for (i=0;i<S_M_HI(a);i++)
    for (j=i+1;j<S_M_LI(a);j++)
        {
        if ((rand() % k) == 0) {
            M_I_I(1,S_M_IJ(a,i,j));
            M_I_I(1,S_M_IJ(a,j,i));
            }

        }
    ENDR("random_adjacency_matrix");
}

INT Kn_adjacency_matrix(n,a) OP n,a;
/* computes the adjacency matrix of the complete graph */
/* AK 240603 */
{
    INT erg = OK;
    INT i,j;

    CTO(INTEGER,"Kn_adjacency_matrix(1)",n);
    SYMCHECK(S_I_I(n) < 0,"Kn_adjacency_matrix:negative input");
    m_ilih_nm(S_I_I(n),S_I_I(n),a);
    C_O_K(a,INTEGERMATRIX);
    for (i=0;i<S_M_HI(a);i++)
    for (j=0;j<S_M_LI(a);j++)
        if (i!=j) M_I_I(1,S_M_IJ(a,i,j));
    ENDR("Kn_adjacency_matrix");
}



INT johnson_graph_adjacency_matrix(a,b,c,m) OP a,b,c,m;
/* computes the adjacency matrix */
/* of the johnson graph:
   edge if the intersection of two b-subsets of a a-set 
   has exactly c elements */
{
    INT erg =OK;
    CTO(INTEGER,"johnson_graph_adjacency_matrix(1)",a);
    CTO(INTEGER,"johnson_graph_adjacency_matrix(2)",b);
    CTO(INTEGER,"johnson_graph_adjacency_matrix(3)",c);
    SYMCHECK(S_I_I(a)<S_I_I(b),"johnson_graph_adjacency_matrix:a<b");
    SYMCHECK(S_I_I(b)<S_I_I(c),"johnson_graph_adjacency_matrix:b<c");
    SYMCHECK(S_I_I(c)<0,"johnson_graph_adjacency_matrix:c<0");
    {
    OP d,e,f;
    INT i,j;
    CALLOCOBJECT3(d,e,f);
    binom(b,c,d); sub(a,b,e); sub(b,c,f);
    binom(e,f,f); mult_apply(d,f); makevectorofsubsets(a,b,d);
    m_lh_nm(S_V_L(d),S_V_L(d),m);
    
    for (i=0;i<S_V_LI(d);i++)
    for (j=i+1;j<S_V_LI(d);j++)
    { // schnitt der beiden subsets
      INT k,kk=0;
      for (k=0;k<S_V_LI(S_V_I(d,i)); k++)
          if ((S_V_II(S_V_I(d,i),k) == 1) &&
              (S_V_II(S_V_I(d,j),k) == 1)) kk++;
      if (kk == S_I_I(c)) // kante
          {M_I_I(1,S_M_IJ(m,i,j));M_I_I(1,S_M_IJ(m,j,i));}
    }
    
    FREEALL3(d,e,f);
    
    }
    ENDR("johnson_graph_adjacency_matrix");
}



