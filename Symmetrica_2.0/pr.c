
/*****************************************************************************/
/* BERECHNUNG DER PROJEKTIVEN MATRIXDARSTELLUNG DER S_n                      */
/*                           NACH NAZAROV                                    */
/*****************************************************************************/
/* Christine Barop Jan.93                                                    */
/*****************************************************************************/

#include "def.h"
#include "macro.h"
#define	PR_RH_MAX	(INT)100

static OP S_lambda;              /* Vektor mit allen standard shifted       */
                                 /* Tableaux mit Umriss lambda              */
static OP phi, rho;              /* Nazarov's phi- und rho-Funktion         */
static OP zwei, vier, m_eins, compl, m_compl; /* Konstanten           */
static OP e;                     /* Starteitrag von S_lambda                */
static OP M;                     /* Vektor mit den Basismatr. der Cliff.alg */
static OP E, I, J, K;            /* Pauli- Basis                            */
static OP A, B;                  /* Operation von t_k auf S_lambda          */
static OP G;                     /* Indices der M-Matr. im Tensorprod.*/


static INT rh_ccsert();
static INT rh_ccstka();
static INT rh_cnsert();
static INT rh_celete();
static INT rh_cusgabemat();
static INT ccstka_tab_partition();
static INT phi_funkt();
static INT rho_funkt();
static INT ini_kons();
static INT ini_slam();
static INT pauli();
static INT m_matr();
static INT ab_matr();
static INT hoehe();

INT prsym(lambda, T_v) OP lambda, T_v;

/*****************************************************************************/
/* BERECHNUNG DER PROJEKTIVEN MATRIXDARSTELLUNG DER TRANSPOSITION t_k        */
/*                           NACH NAZAROV                                    */
/*****************************************************************************/
/* Christine Barop Jan.93                                                    */
/*****************************************************************************/



{
	INT i,j,l,ll, nr;                /* Zaehlvariablen                   */
	INT len;                         /* #(S_lambda)                      */
	INT k;                           /* Index der Transposition          */
	INT m;                           /* 2*m +1 = Rang der Clifford--Alg. */
	INT g;                           /* Nazarov's g--Funktion            */
	INT m_lambda, n_lambda;          /* Laenge und max. Teil der Part.*/
	INT dim, hi, lf;                 /* Hilfsvariablen                 */
	OP eps;                          /* epsilon-Parameter                 */
	OP n;                            /* Gewicht der Partition             */
	OP T_k;                          /* Darstellende Matrix von t_k       */
	OP M_eins, M_zwei;                     /* M_g und M_(g-1)             */
	OP kk;                           /* Nummer der Transposition          */
	OP p, q;                         /* Hoehe von k, k+1 im Tableau       */
	OP x, y/* , z*/;                 /* Hilfsvariablen fuer versch. Zwecke*/
	OP gg;                           /* Nazarov's g-Funktion als INT      */
	OP D;                            /* Darstellende Matrix               */


	n=callocobject(); 
	p=callocobject(); 
	q=callocobject();
	x=callocobject(); 
	y=callocobject(); 
	phi=callocobject(); 
	rho=callocobject(); 
	S_lambda=callocobject();
	e=callocobject(); 
	eps=callocobject();
	zwei=callocobject(); 
	vier=callocobject(); 
	m_eins=callocobject();
	compl=callocobject(); 
	m_compl=callocobject(); 
	A=callocobject();
	M=callocobject(); 
	E=callocobject(); 
	I=callocobject();
	J=callocobject(); 
	K=callocobject(); 
	B=callocobject();
	T_k=callocobject(); 
	G=callocobject(); 
	D=callocobject();
	M_eins=callocobject(); 
	M_zwei=callocobject(); 
	kk=callocobject();
	gg=callocobject();


	ini_kons();
	pauli();
	ini_slam();



	weight(lambda,n);

	/*                   Berechnung von S_lambda                   */
	ccstka_tab_partition(lambda,n);

	/*             Dimensionen und Hilfsgroessen                   */
	m_lambda = S_PA_LI(lambda);
	n_lambda = S_PA_II(lambda,m_lambda-1L);

	m_i_i(m_lambda,x);
	sub(n,x,y);
	ganzdiv(y,zwei,y);
	m=S_I_I(y);

	m_ilih_m(1L,1L,eps);
	copy(cons_eins,S_M_IJ(eps,0L,0L));

	m_matr(m,eps);


	/* Anzahl der Tableaux                                      */
	len=0L;
	while(S_M_LI(S_V_I(S_lambda,len++))!=1L);
	len--;

	/* Berechnung der T_k */
	add(n,cons_eins,x);
	m_l_v(x,T_v);
	for(i=0L;i<S_I_I(x);i++)
		copy(e,S_V_I(T_v,i));
	for(k=1L;k<S_I_I(n);k++)
	{
		ab_matr(m_lambda,n_lambda,len,k);

		/* Berechnung von T_k                                   */
		m_i_i(m,x);
		hoch(zwei,x,y);
		dim = S_I_I(y);
		hi = dim*len;
		m_ilih_nm(hi,hi,T_k);
		m_ilih_nm(dim,dim,M_eins);
		m_ilih_nm(dim,dim,M_zwei);

		for(i=0;i<len;i++)
			for(j=0;j<len;j++)
			{
				copy(S_M_IJ(G,i,j),gg);
				g=S_I_I(gg);
				if(g>0L)
				{
					copy(S_V_I(M,g),M_eins);
					copy(S_V_I(M,g-1L),M_zwei);
					for(l=0;l<dim;l++)
						for(ll=0;ll<dim;ll++)
						{

				mult(S_M_IJ(A,i,j),S_M_IJ(M_eins,l,ll),x);
			if(g>1L)
				mult(S_M_IJ(B,i,j),S_M_IJ(M_zwei,l,ll),y);
			else
				m_i_i(0L,y);

					hi = i*dim +l; 
					lf=j*dim +ll;
					add(x,y,S_M_IJ(T_k,hi,lf)); 
				}
				}
			}
		copy(T_k,S_V_I(T_v,k));
	}
        hi = S_M_LI(S_V_I(T_v,1));
        m_ilih_nm(hi,hi,T_k);
        for(l=0;l<hi;l++)
           copy(m_eins,S_M_IJ(T_k,l,l));
        copy(T_k,S_V_I(T_v,0));
 


	freeall(D); 
	freeall(T_k); 
	freeall(M_eins);
	freeall(M_zwei); 
	freeall(E); 
	freeall(I);
	freeall(J); 
	freeall(K); 
	freeall(eps);
	freeall(vier); 
	freeall(m_eins); 
	freeall(compl);
	freeall(m_compl); 
	freeall(M); 
	freeall(n);
	freeall(p); 
	freeall(q); 
	freeall(x);
	freeall(y); 
	freeall(rho);
	freeall(phi); 
	freeall(zwei);
	freeall(S_lambda); 
	freeall(e); 
	freeall(A);
	freeall(B); 
	freeall(G); 
	freeall(kk);
	freeall(gg);
}

typedef INT PR_INTARRAY[PR_RH_MAX];

static INT ini_kons()
{
	/*        Setzen der Konstanten                          */
	m_ilih_nm((INT)1,(INT)1,e);
	m_i_i(2L,zwei);
	m_i_i(4L,vier);
	m_i_i(-1L,m_eins);
	squareroot(m_eins,compl);
	mult(m_eins,compl,m_compl);
	return(OK);
}

static INT pauli()
{
	/*        Pauli-Basis                                    */
	m_ilih_nm(2L,2L,E);
	m_ilih_nm(2L,2L,I);
	m_ilih_nm(2L,2L,J);
	m_ilih_nm(2L,2L,K);

	copy(cons_eins,S_M_IJ(E,0L,0L));
	copy(cons_eins,S_M_IJ(E,1L,1L));
	copy(compl,S_M_IJ(I,1L,0L));
	copy(m_compl,S_M_IJ(I,0L,1L));
	copy(cons_eins,S_M_IJ(J,0L,0L));
	copy(m_eins,S_M_IJ(J,1L,1L));
	copy(cons_eins,S_M_IJ(K,0L,1L));
	copy(cons_eins,S_M_IJ(K,1L,0L));
	return(OK);
}

static INT ini_slam()
{
	INT i;
	/*        Vorbesetzen von S_lambda                         */
	m_il_v(PR_RH_MAX,S_lambda);
	for(i=0L;i<PR_RH_MAX;i++)
		copy(e,S_V_I(S_lambda,i));
	return(OK);
}


static INT ccstka_tab_partition(a,nn) OP a,nn;
{
	INT i,j;
	INT *um,*pa, m_a, n;
	INT (* tab)[PR_RH_MAX];

	tab = (PR_INTARRAY *) SYM_calloc(PR_RH_MAX*PR_RH_MAX,sizeof(INT));
	um = (INT *) SYM_malloc(PR_RH_MAX * sizeof(INT));
	pa = (INT *) SYM_malloc(PR_RH_MAX * sizeof(INT));



	n = S_I_I(nn);
	m_a = S_PA_LI(a);
	for(i=1L;i<=m_a;i++)
		um[i] = pa[i] = S_PA_II(a,m_a-i);


	for(i=1L;i<=m_a; i++)
		for(j=1L;j<i; j++)
			tab[i][j]= -7L;


	rh_ccstka(tab,1L,1L,um,m_a,pa,n);
	SYM_free(um);
	SYM_free(pa);
	SYM_free(tab);
	return(OK);
}


static INT rh_ccstka(tab,st,k,um,m,pa,n)
	INT	tab[PR_RH_MAX][PR_RH_MAX];
	INT	um[PR_RH_MAX];
	INT	pa[PR_RH_MAX];
	INT	st,n,k,m;
{
	INT	l,p,q;


	if(st==n+1L)
		rh_cusgabemat(tab,m,pa[1]);
	if(st!=n+1L)
	{
		for(l=k;l<=m;l++)
		{
			if(um[l]>0L)
			{
				p=pa[l]-um[l]+l-1;
				if((l==1L)||(tab[l-1][p+1]!=0L))
				{
					um[l]--;
					rh_ccsert(tab,st,l,p+1L);
					rh_ccstka(tab,st+1L,1L,um,m,pa,n);
					rh_celete(tab,st,l,p+1L);
					um[l]++;
				}
			}
		}
	}
}




static INT rh_cusgabemat(tab,z,s)
	INT tab[PR_RH_MAX][PR_RH_MAX],z,s;
/* c ist liste, d ist umriss */
/* Ralf Hager 1989 */ /* AK 281289 V1.1 */ /* AK 210891 V1.3 */
{
	INT	i;
	INT	j;
	OP e = callocobject();
	OP f = callocobject();

	m_ilih_nm(s+1L,z+1L,f);
	for (i=0L;i <=z; i++)
		for (j=0L;j <=s; j++)
			if(tab[i][j] > 0L)
				m_i_i(tab[i][j],S_M_IJ(f,i,j));


	for(i=0L;i<=PR_RH_MAX;i++)
		if(S_M_LI(S_V_I(S_lambda,i))==1L)
		{
			copy(f,S_V_I(S_lambda,i));
			break;
		}

	freeall(e); /* AK 130392 */
	freeall(f); /* AK 071093 */
	return OK;
}


static INT rh_ccsert(v,zz,i,j) INT v[PR_RH_MAX][PR_RH_MAX]; 
	INT zz,i,j;
{
	v[i][j]=zz;
	return(OK);
}

static INT rh_celete(v,z,i,j) INT v[PR_RH_MAX][PR_RH_MAX]; 
	INT z,i,j;
{

	v[i][j]=0L;
	return(OK);
}

static INT m_matr(m,eps) OP eps; INT m;
/* CB */
{
	OP EM = callocobject();
	OP JM = callocobject();
	OP x = callocobject();
	OP y = callocobject();

	INT i,i_eins;
	/*        Berechnung der M-Matrizen                            */
	i_eins = m;
	i_eins++;
	m_il_v(i_eins,EM);
	m_il_v(i_eins,JM);
	i_eins--; 
	i_eins = 2L*i_eins+2L;
	m_il_v(i_eins,M);

	m_ilih_m(1L,1L,x);
	copy(cons_eins,S_M_IJ(x,0L,0L));
	copy(x,S_V_I(EM,0L));
	copy(x,S_V_I(JM,0L));

	for(i=1; i<= m; i++)
	{
		kronecker_product(E,S_V_I(EM,i-1L),x);
		kronecker_product(J,S_V_I(JM,i-1L),y);
		copy(x,S_V_I(EM,i));
		copy(y,S_V_I(JM,i));
	}
	copy(S_V_I(JM,m),S_V_I(M,1L));

	for(i=1;i<=m;i++)
	{
		kronecker_product(K,S_V_I(JM,m-i),x);
		kronecker_product(S_V_I(EM,i-1L),x,x);
		kronecker_product(eps,x,S_V_I(M,2*i),x);
		kronecker_product(I,S_V_I(JM,m-i),x);
		kronecker_product(S_V_I(EM,i-1L),x,x);
		kronecker_product(eps,x,S_V_I(M,2*i+1L));
	}

	freeall(EM);
	freeall(JM);
	freeall(x);
	freeall(y);

	return(OK);
}

static INT ab_matr(m_lambda,n_lambda,len,k) INT len,k; INT m_lambda, n_lambda;
{
	/* Berechnung der A- und ggf. B-Matrizen   */
	OP T =callocobject();
	OP gg = callocobject();
	OP p = callocobject();
	OP q = callocobject();
	OP Th = callocobject();
	OP x = callocobject();
	OP kk = callocobject();
	INT j,l,g;
	INT pp, qq;               /* Hoehe von k, k+1 im Tableau             */
	INT *ppp, *qqq;           /* Hoehe von k, k+1 im Tableau             */
	INT *ip, *jp, *iq, *jq;   /* Koordinaten von k, k+1 im Tableau       */
	INT *hilf;                /* Schon betrachtete Tableaux              */

	hilf = (INT *) SYM_malloc(PR_RH_MAX * sizeof(INT));
	ppp = (INT *) SYM_malloc(sizeof(INT));
	qqq = (INT *) SYM_malloc(sizeof(INT));
	jp = (INT *) SYM_malloc(sizeof(INT));
	ip = (INT *) SYM_malloc(sizeof(INT));
	iq = (INT *) SYM_malloc(sizeof(INT));
	jq = (INT *) SYM_malloc(sizeof(INT));

	m_ilih_nm(len,len,A);
	m_ilih_nm(len,len,B);
	m_ilih_nm(len,len,G);
	for(j=0L;j<len;j++)
		hilf[j]=0;

	for(j=0L;j<len;j++)
	{
		if(hilf[j]==0L)
		{
			copy(S_V_I(S_lambda,j),T);

			hoehe(k,T,m_lambda,n_lambda,ppp,ip,jp);
			pp = *ppp;
			m_i_i(pp,p);

			hoehe(k+1L,T,m_lambda,n_lambda,qqq,iq,jq);
			qq = *qqq;
			m_i_i(qq,q);

			/* Nazarov's g-Funktion */
			g=k+1;
			for(l=1L;l<=m_lambda;l++)
			{
				if(S_M_IJI(T,l,l)<=k+1L)
					g--;
			}

			m_i_i(g,gg);
			copy(gg,S_M_IJ(G,j,j)); /* Tensorprodukt mit M_g! */

			/* Besetzen der A- und ggf. B-Matrizen                                 */
			if(qq!=0L)
				phi_funkt(p,q,cons_eins,zwei);
			if(qq==0L)
			{
				phi_funkt(q,p,cons_eins,zwei);
				mult(phi,m_eins,phi);
			}

			copy(phi,S_M_IJ(A,j,j));

			if(pp*qq !=0L) /* weder k noch k+1 auf der Hauptdiagonalen */
			{
				phi_funkt(q,p,cons_eins,zwei);
				mult(phi,m_eins,phi);
				copy(phi,S_M_IJ(B,j,j));
			}
			hilf[j]=1;

			if((pp-qq)*(pp-qq)!=1L) /* k und k+1 vertauschbar */ 
			{
				rho_funkt(p,q,pp,qq,cons_eins,zwei);

				copy(T,Th);
				m_i_i(k,kk);
				m_i_i(k+1L,x);
				copy(kk,S_M_IJ(Th,*iq,*jq));
				copy(x,S_M_IJ(Th,*ip,*jp));

				l=0;
				while(comp(Th,S_V_I(S_lambda,l++))!=0L);
				l--;

				if(pp!=0L)
					phi_funkt(q,p,cons_eins,zwei);
				if(pp==0L)
				{
					phi_funkt(p,q,cons_eins,zwei);
					mult(phi,m_eins,phi);
				}

				copy(phi,S_M_IJ(A,l,l));
				copy(rho,S_M_IJ(A,j,l));
				copy(rho,S_M_IJ(A,l,j));

				if(pp*qq !=0L)
				{
					phi_funkt(p,q,cons_eins,zwei);
					mult(phi,m_eins,phi);

					copy(phi,S_M_IJ(B,l,l));
					copy(rho,S_M_IJ(B,j,l));
					copy(rho,S_M_IJ(B,l,j));
				}

				copy(gg,S_M_IJ(G,l,l));
				copy(gg,S_M_IJ(G,j,l));
				copy(gg,S_M_IJ(G,l,j));

				hilf[l]=1;
			}

		}
	}
	SYM_free(hilf); 
	SYM_free(ppp); 
	SYM_free(qqq); 
	SYM_free(ip); 
	SYM_free(iq); 
	SYM_free(jp);
	SYM_free(jq);
	freeall(T);
	freeall(gg);
	freeall(p);
	freeall(q);
	freeall(Th);
	freeall(x);
	freeall(kk);

	return(OK);
}

static INT hoehe(u,T,m_lambda,n_lambda,diff,ikor,jkor)
	OP T; 
	INT u, m_lambda, n_lambda; 
	INT *diff, *ikor, *jkor;
{
	INT l,ll;
	for(l=1L;l<=m_lambda;l++)
		for(ll=l;ll<=n_lambda;ll++)
			if(S_M_IJI(T,l,ll)==u)
			{
				*diff=ll-l;
				*ikor = l;
				*jkor = ll;
				break;
			}
	return(OK);
}

static INT phi_funkt(p,q,para_eins,para_zwei) OP p,q,para_eins,para_zwei;
/* CB 0193 */
{
	OP x = callocobject();
	OP y = callocobject();
	OP z = callocobject();

	add(q,para_eins,y); 
	mult(q,y,x); 
	mult_apply(para_zwei,x); 
	squareroot(x,x);
	add_apply(p,y); 
	sub(p,q,z); 
	mult(y,z,y); 
	div(x,y,phi);

	freeall(x);
	freeall(y);
	freeall(z);

	return(OK);
}

static INT rho_funkt(p,q,pp,qq,para_eins,zwei) OP p,q,para_eins,zwei; INT pp,qq;
{
	OP x = callocobject();
	OP y = callocobject();
	OP z = callocobject();

	sub(p,q,x); 
	add(p,q,y); 
	add(y,para_eins,y);
	mult(x,x,x); 
	mult(y,y,y);
	div(para_eins,x,x); 
	div(para_eins,y,y);
	sub(para_eins,x,x); 
	sub(para_eins,y,y);
	mult(x,y,z); 
	div(z,zwei,z);
	if(pp==0 || qq==0L) /* k oder k+1 auf der Hauptdiag. */
		mult(z,zwei,z);
	squareroot(z,rho);
	freeall(x);
	freeall(y);
	freeall(z);
	return(OK);
}
