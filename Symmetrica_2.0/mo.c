/* SYMMETRICA source code file: mo.c */
#include "def.h" 
#include "macro.h" 
#ifdef DGTRUE    
/* Darstellungen werden benoetigt */

#define ALLOCOFFSET 0
#define TL_calloc(a,b) SYM_calloc(a+ALLOCOFFSET,b)
#define TL_malloc(a) SYM_malloc(a+ALLOCOFFSET)
#define TL_free(a) SYM_free(a)

typedef signed char TL_BYTE;
typedef signed short TL_2BYTE;

#define SYM_memcmp memcmp

static close_mat();
static init_mat();
static INT _ber_inx_dec();
static INT modmat();
static INT moddreimat();
static INT r_modgauss();
static INT _modgauss();
static INT p_rel();
static INT p_writemat();
static INT zykel();
static INT modgauss();
static INT ganzgaussmod();
static INT homp();
static INT TL_darmod();
static INT d_mat();
static INT k_dimmod();
static INT _k_moddreimat();
static INT _assoziiere();
static INT alkonmat();
static INT zweikonmat();
static INT mat_comp();
static INT alcoeff();
static INT symdet ();
static INT sigper();
static INT alzyk();
static INT k_alzyk();
static INT j_zyk();
static INT inzeil();
static INT zykschnitt ();
static INT leer();
static INT a_teilmenge_b();
static INT setmin();
static INT _teste_r_mat_dim();
static INT _red_r_mat();
static INT _diff();
static INT _kleiner();
static INT _ggT();
static INT _v_eintrag();
static INT _ber_dim();
static INT _dimension();
static INT _fakul();
static INT _ber_lambdas();
static INT _r_induk();
static INT _num_part();
static INT _part_reg();
static INT _nexpart();
static INT _k_modgauss();
static INT COEFF();
static INT _search_dec();
static INT _k_zweikonmat();
static INT invp();
static INT fak();
static INT nexgitt();
static INT _ber_idx_pelem();
static INT darmod();
static INT lmatmulp();
static INT rmatmulp();
static INT homtestp();
static INT a_ohne_b_gl_c();
static INT matcopy();
static INT konjugiere();
static INT schnitt();
static INT _ggT_v();


static TL_BYTE AK_buf;
#define TL_MOD(a,b) \
 ((AK_buf = (((INT)a)%(b)))<0?AK_buf+b:AK_buf)

/* mod(a,b)=a mod b >= 0 */
#define TL_ADP(x,y,p) TL_MOD((x)+(y),(INT)p)
#define TL_MULP(x,y,p) TL_MOD(((INT)x)*((INT)y),(INT)p)
#define TL_DIVP(x,y,p) TL_MULP((x),invp((INT)y,(INT)p),(INT)p)

/*
  Global variables of MODULDAR
*/
/*******************************************************************************
*
* Datei MODDGGLB.C
*
* Globale Variablen, die eventuell geaendert werden muessen.
*
*******************************************************************************/
/*
  Ueblicher Headerfile...
*/

static INT idmat();
/*
  Globale Variablen des Programmpakets MODULDAR
*/

/*
static INT MAXN = (INT)20;
static INT MAXZEILENZ = (INT)20;
static INT MAXSPALTENZ = (INT)20;
*/
static INT MAXDM = (INT)5000;
static INT ZYK = (INT)50;

static INT PZ[] = {
	(INT)2,(INT)3,(INT)5,(INT)7,(INT)11,(INT)13,(INT)17,(INT)19,(INT)23,(INT)29,(INT)31};


/*
  Defines of possible errors
*/
#define LmbNul (INT)-10
#define LmbEmp (INT)-11
#define LmbLt_null (INT)-12
#define LmbNRg (INT)-13
#define NLe_null (INT)-14
#define NGtMax (INT)-15
#define ZzGtMx (INT)-16
#define SzGtMx (INT)-17
#define DmGtMx ((INT)-18)
#define BzNul (INT)-19
#define CntOFl (INT)-20
#define DimLe_null (INT)-21
#define DrtNul (INT)-22
#define GzlNul (INT)-23
#define NoPrm (INT)-24
#define PrmLe_null (INT)-25
#define PrmGtN (INT)-26
#define NoSolu (INT)-27
#define DDmLt_null (INT)-28
#define DDmGMx (INT)-29
#define PerNul (INT)-30
#define PerLe_null (INT)-31
#define PerGtN (INT)-32
#define PeLgGN (INT)-33
#define RTabFt (INT)-99
#define NtEMem (INT)-109


/*
  Macros for modulararithmetic


  Die Modulararithmetik berechnet Summen (adp), Produkte (mulp),
  Inverse (invp) und Quotienten (divp) modulo p. Bei Verwendung der
  entsprechenden Funktionen muss p als Parameter uebergeben werden.
*/

/*
  und schliesslich globale Variablen.
*/
static INT _zeilenz;
static INT q_zeilenz;
static INT _spaltenz;
static INT _n;
static INT _zyk;
#ifdef UNDEF
#define COEFF(x,y,z) ((z-y)%2L)?(((INT)-1)*fak(x+y-2L*z)*fak(z-y)*fak(z)) \
      : (fak(x+y-2L*z)*fak(z-y)*fak(z))
#endif
static INT COEFF(x,y,z)  INT x,y,z;
{
	return ((z-y)%(INT)2)?(((INT)-1)*fak(x+y-(INT)2*z)*fak(z-y)*fak(z))
	    : (fak(x+y-(INT)2*z)*fak(z-y)*fak(z)) ;
}

/*----------------------------------------------------------------------------*/
static INT _k_zweikonmat(lambda,bz,pz) TL_BYTE *lambda, *bz; 
           INT pz;
/*-----------------------------------------------------------------------------
  berechnet die Koeffizientenmatrix B zu einer Partition lambda, deren
  Laenge gleich zwei ist. Dabei werden die Elemente der Matrix modulo pz
  abgelegt. (Vgl. MODULKFF.C Funktion zweikonmat().)
  Variablen:  lambda, Partition;
              pz, Primzahl.
  Reuckgabe Koeffizientenmatrix bz.
  Rueckgabewerte: >(INT)0, Dimension der gewoehnlichen irred. Darstellung;
               (INT)-109, falls nicht genuegend Speicher zur Verfuegung stand.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,l,z,zaehl,mdim,dim;
	TL_BYTE *g_i,*g_j;
	TL_BYTE *start;
	TL_BYTE *_bz;
	INT g_im,g_jm;

	start=(TL_BYTE *)TL_calloc((int)_n*3,sizeof(TL_BYTE));
	if (!start) return no_memory();
	g_i=start+(INT)_n;
	g_j=g_i+(INT)_n;
	mdim=MAXDM;
	g_im=FALSE;
	if (nexgitt(start,lambda,&g_im))
	{
		SYM_free(start);
		return no_memory();
	}
	for (z=0;z<_n;g_i[z]=start[z],z++);
	_bz=bz;
	for (i=0,g_im=TRUE;g_im;i++)
	{
		for (z=0;z<_n;g_j[z]=start[z],z++);

		for (j=0,g_jm=TRUE;g_jm;j++)
		{
			for (l=0,zaehl=(INT)0;l<_n;l++)
				if (g_i[l]==(TL_BYTE)1 && g_j[l]==(TL_BYTE)1) zaehl++;
			*_bz++ = (TL_BYTE) TL_MOD( COEFF(_n,zaehl,(INT)lambda[1]) ,pz);
			if (nexgitt(g_j,lambda,&g_jm))
			{
				SYM_free(start);
				return  no_memory();
			}
		}
		if (!i)
		{
			dim=j;
			if (dim>MAXDM)
			{
				dim *= ((INT)-1);
				break;
			}
		}
		if (dim<mdim)
			mdim=dim;
		if (nexgitt(g_i,lambda,&g_im))
		{
			SYM_free(start);
			return no_memory();
		}
	}
	SYM_free(start);
	return(dim);
} /* k_zweikonmat */




/*
  Externe Funktion der Modulararithmetik aus MODULARI.C
*/
/*******************************************************************************
*
* Datei MODULARI.C
*   Version vom 29.09.1989
*
*
* Zeile Funktion
*
*       Funktion zur Berechnung des modular Inversen
*       --------------------------------------------
* 30    INT invp(INT z,INT p)
*
*******************************************************************************/
/*
  Uebliche...
*/



/*----------------------------------------------------------------------------*/
static INT invp(z,p) INT z; 
            INT p;
/*------------------------------------------------------------------------------
  berechnet das Inverse von z in GF(p) mit Hilfe Euklids.
  Variablen:  z,  ganze Zahl;
              p,  Primzahl.
  Rueckgabewert:  Inverses von z in GF(p).
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT x[2],y[2],yh,i,q,r;

	x[0]=(INT)1;
	x[1]=(INT)abs(z);
	y[0]=(INT)0;
	y[1]=(INT)abs(p);
	if (x[1]<y[1])
		for (i=(INT)0;i<2L;++i)
		{
			yh=y[i];
			y[i]=x[i];
			x[i]=yh;
		}
	while (y[1]>(INT)0)
	{
		while ((INT)2*y[1]>x[1])
			for (i=(INT)0;i<2L;++i)
			{
				yh=y[i];
				y[i]=x[i]-y[i];
				x[i]=yh;
			}
		q=x[1]/y[1];
		r=x[1]%y[1];
		yh=y[0];
		y[0]=x[0]-q*y[0];
		x[0]=yh;
		x[1]=y[1];
		y[1]=r;
	}
	x[0]= z<(INT)0 ? -x[0] : x[0];
	/* return(((x[0]%p)<(INT)0) ? x[0]%p+p : x[0]%p); */
	return(((z=(x[0]%p))<(INT)0) ? z+p : z);
} /* invp */


/*
  Makros zur Modulararithmetik
*/

/*******************************************************************************
*
* Datei MODULKFF.C
*   Version vom 29.09.89
*
*
* Zeile Funktion
*
*
*       Funktionen fuer Mengenoperationen
*       ---------------------------------
* 88    INT setmin(TL_BYTE *a)
* 107   INT a_teilmenge_b(TL_BYTE *a,TL_BYTE *b)
* 129   INT leer(TL_BYTE *a)
* 148   a_ohne_b_gl_c(TL_BYTE *a,TL_BYTE *b,TL_BYTE *c)
*
*       Funktionen zur Berechnung der Koeffizientenmatrix (B,C_eins,C_zwei)
*       -----------------------------------------------------------
* 175   INT zykschnitt(INT *t_eins,INT *t_zwei,INT *perm,INT *zykmt)
* 216   INT inzeil(INT la,TL_BYTE *zmat,TL_BYTE *fln)
* 355   INT j_zyk(INT la,INT j_zwei,TL_BYTE **xm,TL_BYTE *zh)
* 454   INT k_alzyk(INT la,INT *zmat,INT *fln,INT *cy)
* 523   INT alzyk(INT la,INT *zmat,INT *fln,INT *cy)
* 547   INT sigper(INT *fln,INT la)
* 586   INT symdet(TL_BYTE *mat,TL_BYTE *slambda,INT li,INT *tsc)
* 804   INT fak(INT i)
* 820   INT alcoeff(INT *mat,INT *slambda)
* 849   INT nexgitt(TL_BYTE *y,TL_BYTE *lambda,INT *mtc)
* 918   INT zweikonmat(INT *lambda,INT *perm,INT *bz)
* 1003  konjugiere(INT *lambda,INT *lambdastrich)
* 1025  schnitt(INT *t_eins,INT *t_zwei,INT *mat)
* 1043  INT mat_comp(TL_BYTE *co,TL_BYTE *mat,INT *slamda)
*
*       Hauptfunktion
*       -------------
* 1099  INT alkonmat(INT *lambda,INT *perm,INT *bz)
*
*******************************************************************************/
/*
  Headerfiles wie in jedem C-Programm,...
*/




/*
  interne Makros ...
*/
/* #define IND(a,b,c) (INT)((INT)(a)*(INT)(c)+(INT)(b))  */
#define IND(a,b,c) ((INT)(a)*(INT)(c)+(b))  
/*
#define COEFF(x,y,z) ((z-y)%2L)?((-1L)*fak(x+y-2L*z)*fak(z-y)*fak(z)) \
      : (fak(x+y-2L*z)*fak(z-y)*fak(z))
*/
#define INDEX(x) ZYK/2+x



/*******************************************************************************
*
* Funktionen fuer Mengenoperationen ...
*
* Mengen sind Felder a mit Eintraegen a[i]:
* Element i nicht enthalten => a[i]=0
* Element i enthalten => a[i]=1
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT setmin(a) TL_BYTE *a;
/*------------------------------------------------------------------------------
  errechnet das Minimum der Menge a.
  Rueckgabewerte: Elementnummer m, falls m Minimum ist;
                  -1L, falls kein Minimum existiert.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_a;
	INT m;

	for (m=(INT)0,_a=a;m<_n;m++,_a++)
		if (*_a)
			return(m);
	return(-1L);
}


/*----------------------------------------------------------------------------*/
static INT a_teilmenge_b(a,b) TL_BYTE *a, *b;
/*------------------------------------------------------------------------------
  ueberprueft, ob Menge a Teilmenge von Menge b ist.
  Rueckgabewerte: TRUE, falls a Teilmenge von b ist;
                 FALSE, falls a nicht Teilmenge von b ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_a,*_b;
	INT m;

	for (m=(INT)0,_a=a,_b=b;m<_n;m++,_a++,_b++)
		if (*_a)
		{
			if (! *_b)
				return(FALSE);
		}
	return(TRUE);
}


/*----------------------------------------------------------------------------*/
static INT leer(a) TL_BYTE *a;
/*------------------------------------------------------------------------------
  ueberprueft, ob die Menge a leer ist.
  Rueckgabewerte: TRUE, falls a leer ist;
                 FALSE, falls a nicht leer ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT m;

	for (m=(INT)0;m<_n;m++,a++)
		if (*a)
			return (FALSE);
	return (TRUE);
}


/*----------------------------------------------------------------------------*/
static INT a_ohne_b_gl_c(a,b,c) TL_BYTE *a,*b,*c;
/*------------------------------------------------------------------------------
  berechnet die Menge a\b.
  Rueckgabe Menge c = a\b.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT m;

	for (m=(INT)0;m<_n;m++,a++,b++,c++)
	{
		if (*b)
			*c = (TL_BYTE)0;
		else 
			*c = *a;
	}
	return OK;
}


/*******************************************************************************
*
* Funktionen fuer die Bestimmung der Koeffizientenmatrix (B,C_eins,C_zwei)...
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT zykschnitt (t_eins,t_zwei,perm,zykmt) TL_BYTE *t_eins, *t_zwei, *perm, *zykmt;
/*------------------------------------------------------------------------------
  berechnet Schnittmatrix zykmt in Abhaengigkeit von der Permutation perm.
  Rueckgabewerte: (INT)0, falls alles ohne Fehler durchgefuehrt werden konnte;
              (INT)-109, falls nicht genuegend Speicher zu Verfuegung steht.
  Rueckgabe Schnittmatrix zykmt.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j;
	TL_BYTE *zeile,*z;
	INT enthalten;

	zeile=(TL_BYTE *)TL_calloc((int)_n*(int)_n,sizeof(TL_BYTE));
	if (!zeile) return no_memory();
	for (i=q_zeilenz,z=zykmt;i>(INT)0;i--,*z++ = (INT)0);
	/*
  Berechnung der Zeilenziffernmengen von (perm)T2:
*/
	for (i=_n-1L;i>=(INT)0;--i)
		zeile[IND(t_zwei[i],perm[i]-1L,_n)]=1L;
	for (j=(INT)0;j<_n;++j)
	{
		enthalten=FALSE;
		i=(INT)0;
		do
		{
			if (zeile[IND(i,j,_n)])
			{
				++zykmt[IND(t_eins[j],i,_zeilenz)];
				enthalten=TRUE;
			}
			else
				++i;
		} while (!enthalten);
	}
	SYM_free(zeile);
	return (INT)0;
} /* zykschnitt */


/*----------------------------------------------------------------------------*/
static INT inzeil(la,zmat,fln) INT la; 
TL_BYTE *zmat, *fln;
/*------------------------------------------------------------------------------
  bestimmt, falls moeglich, paarweise verschiedene Ziffern i_eins,i2L,...,ilambda1L,
  welche die injektive erste Zeile eines Elementes von [Ts]c darstellen.
  (Weitere Erlaeuterung in:
    Golembiowski, Andreas
      Zur Berechnung modular irreduzibler Matrixdarstellungen symmetrischer
      Gruppen mit Hilfe eines Verfahrens von M.Clausen
    Bayreuther Mathematische Schriften Heft 25L, Bayreuth 1987
    SS. 162ff)
  Variablen:  la, Teil der konjugierten Partition;
              zmat, Schnittmatrix.
  Rueckgabewerte: (INT)-109, falls kein Speicher zur Verfuegung stand;
                      (INT)0, sonst.
  Rueckgabe Matrix fln.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,i_eins,j,j_eins,r,k,m,oz;
	TL_BYTE **xm,**qu,*ze[2],*un,*hilf;

	xm=(TL_BYTE **)TL_calloc((int)(_zeilenz+_zeilenz+2L),sizeof(TL_BYTE *));
	if (!xm)
		return no_memory();
	qu=xm+(INT)_zeilenz+1L;
	hilf=(TL_BYTE *)TL_calloc((int)(_zeilenz+_zeilenz+6L)*(INT)_n,sizeof(TL_BYTE));
	if (!hilf)
	{
		SYM_free(xm);
		return no_memory();
	}
	un=hilf+(INT)_n;
	ze[0]=un+(INT)_n;
	ze[1]=ze[0]+(INT)_n;
	xm[0]=ze[1]+(INT)_n;
	for (i=1L;i<=_zeilenz;xm[i]=xm[i-1]+(INT)_n,i++);
	qu[0]=xm[_zeilenz]+(INT)_n;
	for (i=1L;i<=_zeilenz;qu[i]=qu[i-1]+(INT)_n,i++);
	for (j=(INT)0;j<la;fln[j++]= (TL_BYTE) -1);
	i=(INT)0;
	while (fln[0]<(INT)0)
		if (zmat[IND(i,(INT)0,_zeilenz)])
			fln[0]=i;
		else
			++i;
	ze[0][fln[0]]=(TL_BYTE)1;
	ze[1][0]=(TL_BYTE)1;
	r=1L;
	while (r<la)
	{
		for (m=(INT)0;m<la;xm[0][m]=(ze[0][m]?(TL_BYTE)0:(TL_BYTE)1), m++);
		for (m=(INT)0;m<_n;qu[0][m]=(TL_BYTE)0,m++);
		for (j=(INT)0;j<la;++j)
		{
			i=(INT)0;
			oz=(INT)0;
			while (!oz && i<la)
				if (xm[0][i] && zmat[IND(i,j,_zeilenz)])
				{
					qu[0][j]=(TL_BYTE)1;
					oz=1L;
				}
				else
					++i;
		}
		for (m=(INT)0;m<_n;un[m]=qu[0][m],m++);
		k=(INT)0;
		while (a_teilmenge_b(qu[k],ze[1]) && (oz!=2L))
		{
			++k;
			for (m=(INT)0;m<_n;xm[k][m]=(TL_BYTE)0,m++);
			for (j=(INT)0;j<la;++j)
				if (qu[k-1][j])
					xm[k][fln[j]]=1L;
			for (m=(INT)0;m<_n;qu[k][m]=(INT)0,m++);
			for (j=(INT)0;j<la;++j)
			{
				for (m=0;m<la;m++)
					if (un[m] == 0)
						hilf[m]=1;
					else 
						hilf[m]=0;
				if (hilf[j])
				{
					i=(INT)0;
					oz=(INT)0;
					while (!oz && i<la)
						if ((xm[k][i]) && (zmat[IND(i,j,_zeilenz)]))
						{
							qu[k][j]=(TL_BYTE)1;
							oz=1L;
						}
						else
							++i;
				}
			}
			if (leer(qu[k]))
			{
				oz=2L;
				fln[0]= -1L;
			}
			else
				for (m=(INT)0;m<_n;++m)
					if (qu[k][m])
						un[m]=1L;
		}
		if (oz!=2L)
		{
			a_ohne_b_gl_c(qu[k],ze[1],hilf);
			j_eins=setmin(hilf);
			ze[1][j_eins]=(TL_BYTE)1;
			++r;
			i_eins=(INT)0;
			while (fln[j_eins]<(INT)0)
				if (xm[k][i_eins] && zmat[IND(i_eins,j_eins,_zeilenz)])
					fln[j_eins]=i_eins;
				else
					++i_eins;
			while (k>=1L)
			{
				for (j=(INT)0;fln[j]!=i_eins || j==j_eins;j++);
				j_eins=j;
				i=(INT)0;
				while (fln[j_eins]==i_eins)
					if (xm[k-1][i] && zmat[IND(i,j_eins,_zeilenz)])
						fln[j_eins]=i;
					else
						++i;
				i_eins=i;
				--k;
			}
			ze[0][i_eins]=(TL_BYTE)1;
		}
		else
			r=la;
	}
	SYM_free(hilf);
	SYM_free(xm);
	return((INT)0);
} /* inzeil */


/*----------------------------------------------------------------------------*/
static INT j_zyk(la,j_zwei,xm,zh) INT la,j_zwei; 
TL_BYTE **xm, *zh;
/*------------------------------------------------------------------------------
  berechnet Menge der Zyklen (j_null j_eins ... jk).
  (Weitere Erlaeuterung in:
    Golembiowski, Andreas
      Zur Berechnung modular irreduzibler Matrixdarstellungen symmetrischer
      Gruppen mit Hilfe eines Verfahrens von M.Clausen
    Bayreuther Mathematische Schriften Heft 25L, Bayreuth 1987
    SS. 166ff)
  Variablen:  la, Element der konjugierten Partition;
              j_zwei, erstes Element des Zykels;
              xm, Mengen.
  Rueckgabewerte: (INT)-109, nicht genug Speicher;
                      (INT)0, sonst.
  Rueckgabe Vektor zh.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,k,l,nr,m;
	static TL_BYTE *j=NULL;
	static TL_BYTE *ym=NULL,*hilf=NULL,**xm_eins=NULL;
	static INT old_z = (INT)-1;

	if (la == (INT)-15) {
		if (j != NULL) {
			SYM_free(j); 
			j = NULL;
		}
		if (xm_eins != NULL) {
			SYM_free(xm_eins);
			xm_eins = NULL;
		}
		old_z = (INT)-1;
		return (INT)0;
	}

	if (old_z < _zeilenz) {
		if (j != NULL) SYM_free(j);
		if (xm_eins != NULL) SYM_free(xm_eins);
		j=(TL_BYTE *)TL_calloc((int)_zeilenz+1
		    + (int)(_zeilenz+2L)*(int)_n ,sizeof(TL_BYTE));
		xm_eins=(TL_BYTE **)
		    TL_calloc((int)_zeilenz,sizeof(TL_BYTE *));

		if (!j)
			return no_memory();
		if (!xm_eins)
		{
			SYM_free(j);
			return no_memory();
		}

		hilf = j + (int)_zeilenz+1;
		ym=hilf+_n;
		xm_eins[0]=ym+_n;
		for (i=1L;i<_zeilenz;xm_eins[i]=xm_eins[i-1]+_n,i++);
		old_z = _zeilenz;

	}
	j[0]=j_zwei;


	memset(&zh[INDEX(-la)],0,(ZYK+la+1) * sizeof(TL_BYTE) );

	if (la >= ZYK) error("internal error MO-5");
	for (i= 0;i<la;++i)
		memcpy(xm_eins[i],xm[i],_n * sizeof(TL_BYTE));

	l=(INT)0;
	nr=1L;
	while (!leer(xm_eins[j_zwei]))
	{
		for (m=(INT)0;m<_n;ym[m++]=(INT)0);
		k=1L;
		do
		{
			a_ohne_b_gl_c(xm_eins[j[k-1]],ym,hilf);
			j[k]=setmin(hilf);
			if (xm_eins[j[k]][j[0]])
			{
				++nr;
				zh[INDEX(-nr)]=l+1L;
				++zh[INDEX(-1L)];
				if (l==(INT)0)
					zh[INDEX(0)]=k+1L;
				else if ((k+1L)<(zh[INDEX(0)]))
					zh[INDEX(0)]=k+1L;
				zh[INDEX(l+1L)]=k+1L;
				zh[INDEX(l+2L)]=j[0]+1L;
				for (i=k+1L;i>=2L;--i)
					zh[INDEX(l+k+4-i)]=j[i-1]+1L;
				l=l+k+3L;
			}
			ym[j[k-1]]=1L;
			a_ohne_b_gl_c(xm_eins[j[k]],ym,hilf);
			if (!leer(hilf))
				++k;
			else
			{
				while (leer(hilf) && (k>=1L))
				{
					xm_eins[j[k-1]][j[k]]=(INT)0;
					ym[j[k]]=(INT)0;
					for (m=(INT)0;m<_n;xm_eins[j[k]][m]=xm[j[k]][m],m++);
					--k;
					a_ohne_b_gl_c(xm_eins[j[k]],ym,hilf);
				}
				if (k>=1L)
					++k;
			}
		} while (k);
	}
	return((INT)0);
} /* j_zyk */


/*----------------------------------------------------------------------------*/
static INT k_alzyk(la,zmat,fln,cy) INT la; 
TL_BYTE *cy; 
TL_BYTE *zmat, *fln;
/*------------------------------------------------------------------------------
  initialisiert Felder, die im Unterprogramm j_zyk benoetigt werden, und ruft
  j_zyk auf.
  (Weitere Erlaeuterung in:
    Golembiowski, Andreas
      Zur Berechnung modular irreduzibler Matrixdarstellungen symmetrischer
      Gruppen mit Hilfe eines Verfahrens von M.Clausen
    Bayreuther Mathematische Schriften Heft 25L, Bayreuth 1987
    SS. 168ff)
  Variablen:  la, Element der konjugierten Partition;
              zmat, Schnittmatrix;
              fln, Matrix aus inzeil.
  Rueckgabewerte: (INT)-109,  nicht genug Speicher;
      (INT)0,  sonst.
  Rueckgabe Matrix aller Zyklen.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j_eins,j_zwei,m;
	TL_BYTE *zh;
	TL_BYTE *z_eins,*z_zwei;
	TL_BYTE **xm;

	xm=(TL_BYTE **)TL_calloc((int)_zeilenz,sizeof(TL_BYTE *));
	if (!xm)
		return no_memory();
	xm[0]=(TL_BYTE *)TL_calloc((int)_zeilenz*(int)_n,sizeof(TL_BYTE));
	if (!xm[0])
	{
		SYM_free(xm);
		return no_memory();
	}
	zh=(TL_BYTE *)TL_calloc((int)_zyk,sizeof(TL_BYTE));
	if (!zh)
	{
		SYM_free(xm[0]);
		SYM_free(xm);
		return no_memory();
	}
	for (i=1L;i<_zeilenz;xm[i]=xm[i-1]+_n,i++);
	for (j_eins=(INT)0,z_eins=zmat;j_eins<la;j_eins++,z_eins++)
	{
		j_zwei=fln[j_eins];
		for (m=(INT)0;m<_n;(xm[j_zwei])[m++]=(TL_BYTE)0);
		for (i=(INT)0,z_zwei=z_eins;i<la;i++,z_zwei += _zeilenz)
			if (*z_zwei && (i!=j_zwei))
				xm[j_zwei][i]=1L;
	}
	for (j_eins=(INT)0;j_eins<la;++j_eins)
	{
		j_zwei=fln[j_eins];
		if (j_zyk(la,j_zwei,xm,zh))
		{
			SYM_free(xm[0]);
			SYM_free(xm);
			SYM_free(zh);
			return no_memory();
		}

		memcpy(&cy[IND(j_zwei,(INT)0,_zyk)],
		    &zh[INDEX(-(ZYK/2L))], 
		    sizeof(TL_BYTE)*(ZYK+ZYK/2 + 1));
		for (m=(INT)0;m<_n;xm[j_zwei][m++]=(INT)0);
	}
	SYM_free(xm[0]);
	SYM_free(xm);
	SYM_free(zh);
	j_zyk((INT) -15,0,NULL,NULL); /* AK 050794 */
	return((INT)0);
} /* k_alzyk */


/*----------------------------------------------------------------------------*/
static INT alzyk(la,zmat,fln,cy) INT la; TL_BYTE *cy; TL_BYTE *zmat, *fln;
/*------------------------------------------------------------------------------
  ruft inzeil und k_alzyk koordiniert auf.
  Variablen:  la, Element der konjugierten Partition;
              zmat, Schnittmatrix.
  Rueckgabewerte: (INT)-109, nicht genug Speicher;
                      (INT)0, sonst.
  Rueckgabe Matrix cy aller Zyklen und Matrix fln paarweise verschiedene
      Ziffern i_eins,...,ilambda1.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	if (inzeil(la,zmat,fln))
		return no_memory();
	if (fln[0]>=(INT)0)
	{
		if (k_alzyk(la,zmat,fln,cy))
			return no_memory();
	}
	return((INT)0);
} /* alzyk */


/*----------------------------------------------------------------------------*/
static INT sigper(fln,la) TL_BYTE *fln, la;
/*------------------------------------------------------------------------------
  berechnet sgn(fln).
  Variablen:  fln, gewisses pi* aus inzeil;
              la, Element aus konjugierter Partition.
  Rueckgabewert:  (INT)-109, falls nicht genuegend Speicher;
                 signum, sonst.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *hilf;
	INT i,j,k,l,v;

	hilf=(TL_BYTE *)TL_calloc((int)_zeilenz,sizeof(TL_BYTE));
	if (!hilf)
		return no_memory();
	for (i=(INT)0;i<_zeilenz;hilf[i]=fln[i],i++);
	v=1L;
	for (i=(INT)0;i<la;++i)
		if ((hilf[i]>=(INT)0) && (hilf[i]!=i))
		{
			l=1L;
			j=hilf[i];
			while (j>=(INT)0 && hilf[j]!=i)
			{
				++l;
				k=hilf[j];
				hilf[j]= -1L;
				j=k;
			}
			if (j>=(INT)0) /* AK 030194 */
				hilf[j]= -1L;
			if (l%2L)
				v *= (-1L);
		}
	SYM_free(hilf);
	return(v);
} /* sigper */


/*----------------------------------------------------------------------------*/
static INT symdet (mat,slambda,li,tsc) TL_BYTE *mat, *slambda; INT li, *tsc;
/*------------------------------------------------------------------------------
  berechnet einen Faktor des Koeffizienten zur Schnittmatrix mat.
  (Weitere Erlaeuterung in:
    Golembiowski, Andreas
      Zur Berechnung modular irreduzibler Matrixdarstellungen symmetrischer
      Gruppen mit Hilfe eines Verfahrens von M.Clausen
    Bayreuther Mathematische Schriften Heft 25L, Bayreuth 1987
    SS. 170ff)
  Variablen:  mat, Schnittmatrix;
              slambda, konjugierte Partition;
              li, Element aus slambda.
  Rueckgabewerte: (INT)-108, falls Resttableau falsch;
                  (INT)-109, falls nicht genug Speicher;
                      (INT)0, sonst.
  Rueckgabe Koeffizientenfaktor tsc.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *cy,*pi,*zmat,*fln,*hfl,*afl,*ii,*z;
	INT lpi,i,j,k,l,d,la,_li,signum,bv,ik,r,err;
	TL_BYTE *piset,*mpi,*zm;

	_li=li;
	la=slambda[_li];
	++_li;
	if (la==1L)
	{
		if (mat[0]==(_spaltenz-_li+1L))
		{
			*tsc=1L;
			return((INT)0);
		}
		else
		{
			*tsc=(INT)0;
			return((INT)0);/*return(RTabFt);*/
		}
	}
	cy=(TL_BYTE *)TL_calloc((int)_zeilenz*((int)_zyk+2*(int)_zeilenz+5),
	    sizeof(TL_BYTE));
	if (!cy)  return no_memory();
	mpi=(TL_BYTE *)TL_calloc((int)q_zeilenz+(int)_zeilenz,sizeof(TL_BYTE));
	if (!mpi)
	{
		SYM_free(cy);
		return no_memory();
	}
	pi=cy+_zeilenz*_zyk;
	zmat=pi+_zeilenz*(_zeilenz+1L);
	fln=zmat+q_zeilenz;
	hfl=fln+_zeilenz;
	afl=hfl+_zeilenz;
	ii=afl+_zeilenz;
	piset=mpi+_zeilenz;
	*tsc=(INT)0;
	matcopy(zmat,mat,_zeilenz);
	if (alzyk(la,zmat,fln,cy))
	{
		SYM_free(cy);
		SYM_free(mpi);
		return no_memory();
	}
	if (fln[0]>=(INT)0)
	{
		for (r=(INT)0;r<_zeilenz;afl[r]=fln[r],r++);
		signum=sigper(fln,la);
		/*   kann nich sein AK 090792 
    if (signum==NtEMem)
    {
      SYM_free(cy);
      SYM_free(mpi);
      return(NtEMem);
    }
*/
		bv= *tsc;
		if (_li == _spaltenz)
			*tsc=signum;
		else
		{
			for (j=(INT)0;j<la;++j)
				--zmat[IND(fln[j],j,_zeilenz)];
			if ((err=symdet(zmat,slambda,_li,tsc))!=(INT)0)
			{
				SYM_free(cy);
				SYM_free(mpi);
				return(err);
			}
			*tsc *= signum;
		}
		*tsc +=  bv;
		matcopy(zmat,mat,_zeilenz);
		if (_li == _spaltenz)
		{
			SYM_free(cy);
			SYM_free(mpi);
			return((INT)0);
		}
		for (k=(INT)0,z=pi+1L;k<la;k++,z += (_zeilenz+1L))
			*z=(INT)0;
		for (r=(INT)0;r<_zeilenz;mpi[r++]=(INT)0);
		lpi=(INT)0;
		k=(INT)0;
fl111:
		if ((lpi+cy[IND(k,INDEX((INT)0),_zyk)])<=la)
		{
			ii[k]=1L;
fl100:
			if (ii[k]<=cy[IND(k,INDEX(-1L),_zyk)])
			{
				ik=ii[k];
				i=cy[IND(k,INDEX(-ik-1L),_zyk)];
				d=(INT)0;
				l=1L;
				while ((d!=1L) && (l<=cy[IND(k,INDEX(i),_zyk)]))
				{
					if (mpi[cy[IND(k,INDEX(i+1L),_zyk)]-1])
						d=1L;
					++l;
				}
				if (d==(INT)0)
				{
					for (r=(INT)0,zm= &piset[IND(k,(INT)0,_zeilenz)];r<_zeilenz;r++,zm++)
						*zm=(INT)0;
					for (j=i+1L;j<=(i+cy[IND(k,INDEX(i),_zyk)]);++j)
					{
						pi[IND(k,(INT)0,_zeilenz+1L)]=cy[IND(k,INDEX(i),_zyk)];
						pi[IND(k,j-i,_zeilenz+1L)]=cy[IND(k,INDEX(j),_zyk)];
						piset[IND(k,cy[IND(k,INDEX(j),_zyk)]-1L,_zeilenz)]=1L;
					}
					for (r=(INT)0,zm= &piset[IND(k,(INT)0,_zeilenz)];r<_zeilenz;r++,zm++)
						if (*zm)
							mpi[r]=1L;
					lpi += pi[IND(k,(INT)0,_zeilenz+1L)];
					for (r=(INT)0;r<_zeilenz;hfl[r]=fln[r],r++);
					l=pi[IND(k,(INT)0,_zeilenz+1L)];
					for (j=1L,z= &pi[IND(k,1L,_zeilenz+1L)];j<=l;j++,z++)
						for (i=(INT)0;i<la;++i)
							if (*z==fln[i]+1L)
								hfl[i]= (j==1L)?pi[IND(k,l,_zeilenz+1L)]-1
								    :pi[IND(k,j-1L,_zeilenz+1L)]-1L;
					for (r=(INT)0;r<_zeilenz;fln[r]=hfl[r],r++);
					for (j=(INT)0;j<la;++j)
						--zmat[IND(fln[j],j,_zeilenz)];
					bv= *tsc;
					if ((err=symdet(zmat,slambda,_li,tsc))!=(INT)0)
					{
						SYM_free(cy);
						SYM_free(mpi);
						return(err);
					}
					if ((l+1L)%(INT)2)
						signum *= (INT)(-1);
					*tsc = bv + signum * (*tsc);
					matcopy(zmat,mat,_zeilenz);
					if ((lpi<=(la-(INT)2)) && (k<la-1L))
					{
						++k;
						goto fl111;
					}
					else
					{
						for(r=(INT)0;r<_zeilenz;fln[r]=afl[r],r++);
						pi[IND(k,1L,_zeilenz+1L)]=(INT)0;
						for (r=(INT)0,zm= &piset[IND(k,(INT)0,_zeilenz)];r<_zeilenz;r++,zm++)
							if (*zm)
								mpi[r]=(INT)0;
						--lpi;
						if ((l+1L)%2L)
							signum *= (-1L);
						++ii[k];
						goto fl100;
					}
				}
				else
				{
					++ii[k];
					goto fl100;
				}
			}
			else
			{
				if (k<la-1L)
				{
					pi[IND(k,1L,_zeilenz+1L)]=(INT)0;
					++k;
					goto fl111;
				}
				else
					goto fl222;
			}
		}
		else
fl222:
			{
				while ((pi[IND(k-1L,1L,_zeilenz+1L)]==(INT)0) && k>1L)
					--k;
				if (pi[IND(k-1L,1L,_zeilenz+1L)])
				{
					--k;
					for (r=(INT)0;r<_zeilenz;fln[r]=afl[r],r++);
					pi[IND(k,1L,_zeilenz+1L)]=(INT)0;
					for (r=(INT)0,zm= &piset[IND(k,(INT)0,_zeilenz)];r<_zeilenz;r++,zm++)
						if (*zm)
							mpi[r]=(INT)0;
					lpi -= pi[IND(k,(INT)0,_zeilenz+1L)];
					if ((pi[IND(k,(INT)0,_zeilenz+1L)]+1L)%2L)
						signum *= (-1L);
					++ii[k];
					goto fl100;
				}
			}
	}
	SYM_free(cy);
	SYM_free(mpi);
	return((INT)0);
} /* symdet */



/*----------------------------------------------------------------------------*/
static INT alcoeff(mat,slambda) TL_BYTE *mat, *slambda;
/*------------------------------------------------------------------------------
  berechnet aus der Schnittmatrix mat und Partition slambda den Koeffizienten.
  Variablen:  mat, Schnittmatrix;
              slambda, konjugierte Partition zu lambda;
  Rueckgabewerte: koeff, Koeffizient zu mat und slambda;
                  (INT)-108, falls ein Resttableau falsch war;
                  (INT)-109, falls kein Speicherplatz vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *z;
	INT i,tsc,faktor;

	faktor=symdet(mat,slambda,(INT)0,&tsc);
	if (faktor)
		return(faktor);
	if (tsc)
	{
		for (i=q_zeilenz,z=mat,faktor=1L;i>(INT)0;i--,z++)
			if (*z)
				faktor *= fak((INT) *z);
		return(faktor*tsc);
	}
	else
		return (INT)0;
} /* alcoeff */


/*----------------------------------------------------------------------------*/
static INT zweikonmat(lambda,perm,bz) TL_BYTE *lambda,*perm,*bz;
/*------------------------------------------------------------------------------
  berechnet die Koeffizientenmatrix bz fuer Partitionen lambda der
  Laenge 2.
  Variablen:  lambda, eigentliche Partition;
              perm, Permutation.
  Rueckgabe Koeffizientenmatrix bz.
  Rueckgabewerte: dim, Dimension der gewoehnlichen Darstellungen, dim ist
                       negativ, falls dim groesser MAXDM;
                (INT)-109, falls kein Speicherplatz vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,k,l,z,zaehl[3],mdim,dim;
	TL_BYTE *hz,*g_i,*g_j,*start,*hilf_zwei,*hilf_drei,*_hz,*_bz,*z_eins;
	INT g_im,g_jm;

	start=(TL_BYTE *)TL_calloc((int)_n*5+(int)MAXDM*3,sizeof(TL_BYTE));
	if (!start)
		return no_memory();
	g_i=start+_n;
	g_j=g_i+_n;
	hilf_zwei=g_j+_n;
	hilf_drei=hilf_zwei+_n;
	hz=hilf_drei+_n;
	mdim=MAXDM;
	g_im=FALSE;
	if (nexgitt(start,lambda,&g_im))
	{
		SYM_free(start);
		return no_memory();
	}
	for (z=(INT)0;z<_n;g_i[z]=start[z],z++);
	for (i=(INT)0,g_im=TRUE;g_im;++i)
	{
		for (z=(INT)0;z<_n;g_j[z]=start[z],z++);
		for (z=3L*mdim,_hz=hz;z>(INT)0;z--,*_hz++ = (INT)0);
		for (j=(INT)0,g_jm=TRUE,_hz=hz;g_jm;j++,_hz++)
		{
			for (z=(INT)0;z<3L;zaehl[z++]=(INT)0);
			for (z=(INT)0;z<_n;hilf_zwei[z]=hilf_drei[perm[z]-1]=g_j[z],z++);
			hilf_zwei[1]=(INT)0;
			for (l=(INT)0;l<_n;++l)
				if (g_i[l]==1L)
				{
					if (g_j[l]==1L) ++zaehl[0];
					if (hilf_zwei[l]==1L) ++zaehl[1];
					if (hilf_drei[l]==1L) ++zaehl[2];
				}
			for (z=(INT)0,z_eins=_hz;z<3L;z++,z_eins += mdim)
				*z_eins=COEFF(_n,(INT)zaehl[z],(INT)lambda[1]);
			if (nexgitt(g_j,lambda,&g_jm))
			{
				SYM_free(start);
				return no_memory();
			}
		}
		if (!i)
		{
			dim=j;
			if (dim>MAXDM)
			{
				dim *= (-1L);
				break;
			}
			else
				_bz=bz;
		}
		for (z=(INT)0,_hz=hz;z<3L;z++,_hz += mdim)
			for (k=(INT)0,z_eins=_hz;k< dim;k++)
				*_bz++ = *z_eins++;
		if (dim<mdim)
			mdim=dim;
		if(nexgitt(g_i,lambda,&g_im))
		{
			SYM_free(start);
			return no_memory();
		}
	}
	SYM_free(start);
	g_im = 280194L; 
	nexgitt(NULL,NULL,&g_im); /* AK 280194 */
	return(dim);
} /* zweikonmat */


/*----------------------------------------------------------------------------*/
static INT konjugiere(lambda,lambdastrich) TL_BYTE *lambda, *lambdastrich;
/*------------------------------------------------------------------------------
  konjugiert die eigentliche Partition lambda mit Ergebnis lambdastrich.
  Variablen:  lambda, eigentliche Partition.
  Rueckgabe lambdastrich.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j;

	for (i=(INT)0;i<lambda[0];++i)
	{
		for (j=(INT)0;j<_zeilenz && lambda[j]>=i+1L;++j);
		if ((j<_n) && (lambda[j] < i+1L))
			lambdastrich[i]=j;
		else
			lambdastrich[i]=_zeilenz;
	}
	return OK;
} /* konjugiere */


/*----------------------------------------------------------------------------*/
static INT schnitt(t_eins,t_zwei,mat) TL_BYTE *t_eins, *t_zwei, *mat;
/*------------------------------------------------------------------------------
  berechnet Schnittmatrix zu den Tableaux t_eins und t_zwei.
  Variablen:  t_eins, Tableau;
              t_zwei, Tableau.
  Rueckgabe Schnittmatrix mat.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  *z;
	INT i;


	memset(mat,0,q_zeilenz * sizeof(TL_BYTE));

	for (i=(INT)0;i<_n;++i)
		++mat[IND(t_eins[i],t_zwei[i],_zeilenz)];
	return OK;
} /*schnitt*/

struct ak { 
	INT c; 
	INT p; 
	char *ptr; 
};

static struct ak * ak_tmpfile()
{
#ifdef UNDEF
	struct ak *a;
	a = (struct ak *) TL_calloc((int)1,sizeof(struct ak));
	if (a==NULL) return (struct ak *) no_memory();
	a->c = (INT)0; /* erste unzulaessige stelle */
	a->p = (INT)0;
	a->ptr = NULL;
#endif
	init_mat();
}

static ak_rewind(a) struct ak *a;
{
	a->p = (INT)0;
	return OK;
}

static ak_fread(buf,size,numb,a) char **buf; 
	INT size; 
	INT numb; 
	struct ak *a;
{
	size = size * numb;

	if (a->p + size > a->c)
		size = a->c - a->p;

	*buf = a->ptr + a->p;
	a->p = a->p + size;
	return a->p;
}

#define AXSIZE 10000

static ak_fwrite(buf,size,numb,a) char *buf; 
	INT size; 
	INT numb; 
	struct ak *a;
{
	size = size *numb;

	if (a->ptr == NULL) {
		a->ptr = (char *)TL_calloc(AXSIZE,1);
		a->c =  AXSIZE;
	}
again:
	if (a->ptr == NULL)
		return no_memory();
	if (a->p + size > a->c) {
		a->ptr = (char *) SYM_realloc(a->ptr,a->c + AXSIZE);
		if (a->ptr == NULL)
			return no_memory();
		a->c = a->c + AXSIZE;
		goto again;
	}
	memcpy(a->ptr + a->p, buf,(int) size);
	a->p = a->p + size;
	return a->p;
}

static ak_fclose(a) struct ak *a;
{
	close_mat();
}
/*
#define ak_fclose(a) fclose(a)
#define ak_tmpfile() tmpfile()
#define ak_rewind(a) rewind(a)
#define ak_fwrite(buf,size,numb,a) fwrite(buf,size,numb,a)
#define ak_fread(buf,size,numb,a) fread(buf,size,numb,a)
*/

static INT tl_prime = (INT) 9973;
static INT tl_max_numb = (INT) 8;
static INT tl_index_inc = (INT) 1;
static TL_BYTE **mat_table;
static TL_2BYTE **koeff_table;
static INT *mat_length;
static INT mat_size;
INT tl_set_prime(p) INT p;
{ 
	tl_prime = p; 
}
INT tl_set_max_numb(p) INT p;
{ 
	tl_max_numb = p; 
}
INT tl_set_index_inc(p) INT p;
{ 
	tl_index_inc = p; 
}
#ifdef UNDEF
#define PRIME  9973 /*  40993  */
#define INDEX_INC 1
#define MAX_NUMB 8
TL_BYTE *mat_table[PRIME];
TL_2BYTE *koeff_table[PRIME];
INT mat_length[PRIME];
#endif

static init_mat()
{
	INT i,size;
	TL_BYTE *a,*b;
	mat_table = (TL_BYTE **) TL_calloc(tl_prime,sizeof(TL_BYTE *));
	mat_length = (INT *) TL_calloc(tl_prime,sizeof(INT));
	koeff_table = (TL_2BYTE **) TL_calloc(tl_prime,sizeof(TL_2BYTE *));
	mat_size = q_zeilenz;

	size = tl_prime * tl_max_numb * (q_zeilenz +  sizeof(TL_2BYTE));
	a = (TL_BYTE *) TL_malloc(size * sizeof(TL_BYTE));
	b = a;

	for (i=(INT)0;i<tl_prime;i++)
	{
		mat_length[i] = (INT)0;
		/*koeff_table[i] = mat_table[i]=NULL; */

		mat_table[i] = a;
		a += (tl_max_numb * q_zeilenz );
		koeff_table[i] = (TL_2BYTE *) a;
		a += tl_max_numb * sizeof(TL_2BYTE) ;
	}


}

static close_mat()
{
	INT i;
	if (mat_size != q_zeilenz) error("MO-35");
	TL_free(mat_table[0]);
	TL_free(mat_table);
	TL_free(koeff_table);
	for (i=(INT)0;i<tl_prime;i++)
	{
		mat_length[i] = (INT)0;
	}
	TL_free(mat_length);
}

static UINT offset[32] = {
	1,1<<1,1<<2,1<<3,1<<4,1<<5,1<<6,1<<7,
	1<<8,1<<9,1<<10,1<<11,1<<12,1<<13,1<<14,1<<15,
	1<<16,1<<17,1<<18,1<<19,1<<20,1<<21,1<<22,1<<23,
	1<<24,1<<25,1<<26,1<<27,1<<28,1<<29,1<<30,((UINT)1)<<31 };

static INT write_mat(mat,koeff) TL_BYTE *mat; 
TL_2BYTE koeff;
{
	INT i,j,k;
	UINT index=(INT)0;
	/* compute adress */

	i=(INT)0;
	if (q_zeilenz > 31)
	{
		k = q_zeilenz / 32;
		for (;k>0;k--)
			for (j=(INT)0; j<32;i+=tl_index_inc,j+=tl_index_inc)
				if (mat[i]) index += offset[j];
	}

	for (j=(INT)0; i<q_zeilenz;i+=tl_index_inc,j+=tl_index_inc)
		if (mat[i]) index += offset[j];

	index = index % tl_prime;

	if (mat_length[index] >= tl_max_numb)
	{
		mat_length[index]++;
		* (koeff_table[index]+
		    (mat_length[index] % tl_max_numb)
		    ) = koeff;
		memcpy(mat_table[index]+
		    (q_zeilenz*
		    (mat_length[index]%tl_max_numb)
		    ), 
		    mat, q_zeilenz * sizeof(TL_BYTE));
	}
	else {
		mat_length[index]++;
		* (koeff_table[index]+mat_length[index]-1) = koeff;
		memcpy(mat_table[index]+
		    (q_zeilenz*(mat_length[index]-1)), 
		    mat, q_zeilenz * sizeof(TL_BYTE));
	}


}


static INT search_mat(co,mat, koeff) TL_BYTE *mat; 
	TL_2BYTE *koeff; 
	INT *co;
	{
	INT  i=(INT)0,k,j;
	UINT index=(INT)0;
	/* compute adress */

	if (q_zeilenz > 31)
	{
		k = q_zeilenz / 32;
		for (;k>0;k--)
			for (j=(INT)0; j<32;i+=tl_index_inc,j+=tl_index_inc)
				if (mat[i]) index += offset[j];
	}

	for (j=0; i<q_zeilenz;i+=tl_index_inc,j+=tl_index_inc)
		if (mat[i]) index += offset[j];

	index = index % tl_prime;
	for (i=mat_length[index]%tl_max_numb -1 ; i>=0 ; i--)
		if (SYM_memcmp(mat,(mat_table[index])+(q_zeilenz * i),
		    sizeof(TL_BYTE) * q_zeilenz) == 0)
		{
			*koeff = * (koeff_table[index] + i);
			return OK;
		}


	return -12L;
}

/*----------------------------------------------------------------------------*/
static INT mat_comp(co,mat,slambda) INT *co; 
TL_BYTE  *mat,*slambda;
/*------------------------------------------------------------------------------
  ueberprueft die Schnittmatrix mat, ob mit dieser schon gerechnet wurde. Ist
  dies der Fall, so ist der Koeffizient gleich. Ansonsten wird fuer mat der
  neue Koeffizient berechnet.
  Variablen:  co, Zaehler der verschiedenen Schnittmatrizen;
              mat, Schnittmatrix;
              slambda, konjugierte Partition zu lambda;
  Rueckgabe co mit alter bzw. neuer Anzahl der verschiedenen Schnittmatrizen.
  Rueckgabewerte: koeff,  Koeffizient zu mat und slambda;
                  (INT)-109,  falls nicht genuegend Speicher vorhanden ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT  gefunden, i,erg;
	TL_BYTE *schnittmat  ,*z_eins,*z_zwei ,rr ;
	TL_2BYTE koeff;
	TL_BYTE *ak_buffer; /* AK 060392 */
	i=1L;
	if ((*co)>(INT)0)
	{
		erg = search_mat(co,mat,&koeff);
		if (erg == OK) return koeff;
	}
	++(*co);
	koeff = alcoeff(mat,slambda);
	if (koeff==RTabFt || koeff==NtEMem)
		return(koeff);
	write_mat(mat,koeff);
	return koeff;
} /* mat_comp */


/*----------------------------------------------------------------------------*/
static INT alkonmat(lambda,perm,bz) TL_BYTE *lambda, *perm, *bz;
/*------------------------------------------------------------------------------
  berechnet zu einer Partition lambda und einer Permutation perm die Koeffi-
  zientenmatrix (B|C(12)|C(perm)).
  Variablen:  lambda, eigentliche Partition;
              perm, Permutation.
  Rueckgabewerte: >(INT)0, kein Fehler aufgetreten;
                 (INT)-10, falls Pointer auf lambda NULL ist;
                 (INT)-11, falls lambda leer ist;
                 (INT)-12, falls ein Element von lambda kleiner 0 ist;
                 (INT)-13, falls lambda keine eigentliche Partition ist;
                 // -15L, falls n > MAXN;
                 // -16L, falls Laenge von lambda groesser MAXZEILENZ ist;
                 // -17L, falls erstes Element von lambda groesser MAXSPALTENZ ist;
                 (INT)-18, falls Dimension der gew. irred. Dg. >MAXDIM;
                 (INT)-19, falls Pointer auf bz NULL ist;
                 (INT)-20, falls sich der temporaere File nicht oeffnen laesst;
                 (INT)-30, falls Pointer auf perm NULL ist;
                 (INT)-31, falls Teil von perm <= 0 ist;
                 (INT)-32, falls Teil von perm > n ist;
                 (INT)-33, falls perm zu viele Elemente hat;
               (INT)-108, falls Resttableau in SYMDET falsch ist;
               (INT)-109, falls nicht genuegend Speicher vorhanden ist.
  Rueckgabe Koeffizientenmatrix bz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *mat,*transmt,*zykmt,*hz,*t_eins,*t_zwei;
	TL_BYTE *ht,*asslambda,*_hz,*_bz,*z_eins;
	INT ii,jj,kk,i,k,z,co = (INT)0,co_eins,co_zwei,dim,diag,mdim,dim_,koeff;
	INT mehr_eins,mehr_zwei;

	/* Moegliche Eingabefehler...  */
	if (!lambda)
		return(LmbNul);
	else if (!lambda[0])
		return(LmbEmp);
	else if (!bz)
		return(BzNul);
	for (i=(INT)0,_n=(INT)0;lambda[i];++i)
		if (lambda[i]<(TL_BYTE)0)
			return(LmbLt_null);
		else
			_n += lambda[i];
	/*
  if (_n>MAXN)
    return(NGtMax);

  else */ if (perm==NULL)
return(PerNul);
/*
  for (i=(INT)0;i<MAXN && perm[i];i++);
  if (i>_n)
    return(PeLgGN);
*/
for (i=(INT)0;i<_n;i++)
if (perm[i]<=(INT)0)
return(PerLe_null);
else if (perm[i]>_n)
return(PerGtN);
for (i=1L;lambda[i];++i)
if (lambda[i]>lambda[i-1])
return(LmbNRg);


/*
  Na denn ma' los...
*/
_zyk=ZYK/2+ZYK+1L;
_spaltenz=lambda[0]; /*AK 240194 */
_zeilenz = i ; /* AK 240194 */
/*
  if ((_spaltenz=lambda[0])>MAXSPALTENZ)
    return(SzGtMx);
  if ((_zeilenz=i)>MAXZEILENZ)
    return(ZzGtMx);
*/
q_zeilenz=_zeilenz*_zeilenz;
if (_zeilenz==2L)
{
	dim_=zweikonmat(lambda,perm,bz);
	if (dim_<(INT)0)
		dim=DmGtMx;
	else
		dim=dim_;
}
else
{ /* allgemeine Partition/Anfang */
	init_mat();
	mat=(TL_BYTE *)TL_calloc((int)(q_zeilenz+MAXDM)*3+(int)(4*_n),sizeof(TL_BYTE));
	if (mat == NULL)
	{
		close_mat();
		return no_memory();
	}
	transmt=mat+q_zeilenz;
	zykmt=transmt+q_zeilenz;
	t_eins=zykmt+q_zeilenz;
	t_zwei=t_eins+_n;
	ht=t_zwei+_n;
	asslambda=ht+_n;
	hz=asslambda+_n;
	mdim=MAXDM;
	konjugiere(lambda,asslambda);
	for (ii=(INT)0,diag=1L;ii<_zeilenz;++ii)
		diag *= fak(lambda[ii]);
	for (ii=(INT)0,kk=(INT)0;ii<_n && lambda[ii];++ii)
	{
		for (jj=kk;jj < (kk+lambda[ii]);ht[jj++]= ii);
		kk += lambda[ii];
	}
	for (z=(INT)0;z<_n;t_zwei[z]=ht[z],z++);
	co_eins=co_zwei=(INT)0;
	for (i=(INT)0,mehr_zwei=TRUE;mehr_zwei;++i)
	{
		for (z=(INT)0;z<_n;t_eins[z]=ht[z],z++);
		for (z=3L*mdim,_hz=hz;z>(INT)0;z--,*_hz++ =(INT)0);
		for (k=(INT)0,mehr_eins=TRUE;mehr_eins;++k)
		{
			if (i==k)
			/*Hauptdiag. von B(lambda) und C(lambda/(12))*/
			{
				hz[i]=diag;
				if (t_zwei[1]== 1)
					hz[i+mdim]=((TL_BYTE) -1)*(hz[i]/lambda[0]);
				else
					hz[i+mdim]=hz[i];
			}
			else if (i<k)
			{
				schnitt(t_eins,t_zwei,mat);
				/*Rest von B(lambda)*/
				koeff=mat_comp(&co,mat,asslambda);
				if (koeff!=NtEMem && koeff!=RTabFt)
					hz[k]=koeff;
				else
				{
					close_mat();
					SYM_free(mat);
					return(koeff);
				}
				if ((t_zwei[1]==1L) && (t_eins[1]==1L))
				/*Rest von C(lambda/(12))*/
				{
					matcopy(transmt,mat,_zeilenz);
					--transmt[0];
					--transmt[_zeilenz+1];
					++transmt[1];
					++transmt[_zeilenz];
					ii=co;
					koeff=mat_comp(&co,transmt,asslambda);
					if (koeff!=NtEMem && koeff!=RTabFt)
						hz[k+mdim]=koeff;
					else
					{
						close_mat();
						SYM_free(mat);
						return(koeff);
					}
					if (co>ii) co_eins++;
				}
				else
					hz[k+mdim]= hz[k];
			}
			if (zykschnitt(t_zwei,t_eins,perm,zykmt))
			{
				close_mat();
				SYM_free(mat);
				return no_memory();
			}
			/*Berechnung von C(lambda/(1..n)).*/
			if (!i && !k)
			{
				co=(INT)0;
				koeff=mat_comp(&co,zykmt,asslambda);
				if (koeff!=NtEMem && koeff!=RTabFt)
					hz[2L*mdim]=koeff;
				else
				{
					close_mat();
					SYM_free(mat);
					mehr_zwei = 280194L; 
					nexgitt(NULL,NULL,&mehr_zwei); /* AK 280194 */
					return(koeff);
				}
			}
			ii=co;
			koeff=mat_comp(&co,zykmt,asslambda);
			if (koeff!=NtEMem && koeff!=RTabFt)
				hz[k+2L*mdim]=koeff;
			else
			{
				close_mat();
				SYM_free(mat);
				mehr_zwei = 280194L; 
				nexgitt(NULL,NULL,&mehr_zwei); /* AK 280194 */
				return(koeff);
			}
			if (co>ii) ++co_zwei;
			if (nexgitt(t_eins,lambda,&mehr_eins))
			{
				close_mat();
				SYM_free(mat);
				return no_memory();
			}
		}
		if ((_zeilenz==1L) || (_spaltenz==1L))
			co=1L;
		if (!i)
		{
			dim=dim_=k;
			if (dim>MAXDM)
			{
				dim_ *= (-1L);
				dim=DmGtMx;
				break;
			}
			else
				_bz=bz;
		}
		for (z=(INT)0,_hz=hz;z<3L;z++,_hz += mdim)
			for (k=(INT)0,z_eins=_hz;k<dim;k++)
				*_bz++ = *z_eins++;
		if (dim<mdim)
			mdim=dim;
		if (nexgitt(t_zwei,lambda,&mehr_zwei))
		{
			close_mat();
			SYM_free(mat);
			return no_memory();
		}
	}
	close_mat();
	SYM_free(mat);


} /*allgemeine Partition/Ende*/


mehr_zwei = 280194L; 
nexgitt(NULL,NULL,&mehr_zwei); /* AK 280194 */
return(dim);
}  /*alkonmat*/
/*******************************************************************************
*
* Datei MODULDIM.C
*   Version vom 17.11.89
*
*
* Zeile Funktion
*
*       Funktionen zur Berechnung der Dimensionen mod. irred. Darstellungen
*       -------------------------------------------------------------------
* 77    INT _k_zweikonmat(INT *lambda,TL_BYTE *bz,INT pz)
* 139   INT k_alkonmat(TL_BYTE *lambda,TL_BYTE *bz,INT pz)
* 269   INT _k_moddreimat(TL_BYTE *bz,INT pz)
* 311   INT _k_modgauss(TL_BYTE *bz,INT pz)
* 359   INT k_dimmod(TL_BYTE *bz,INT dim,INT pz)
*
*******************************************************************************/

static INT dm;
static INT dm_zwei;
static INT qdm;


/*
  Defines...
*/
/*----------------------------------------------------------------------------*/
static INT k_alkonmat(lambda,bz,pz) TL_BYTE * lambda; 
	TL_BYTE *bz; 
	INT pz;
/*------------------------------------------------------------------------------
  berechnet die Koeffizientenmatrix B fuer alle Partitionen lambda. Dabei
  werden die Eintraege der Matrix modulo pz abgelegt.
  (Vgl. in MODULKFF.C Funktion alkonmat().)
  Variablen:  lambda, Partition;
              pz, Primzahl.
  Rueckgabe Koeffizientenmatrix bz.
  Rueckgabewerte: >(INT)0, Dimension der gew. irred. Darstellung;
               sonst, s. MODULKFF.C Funktion alkonmat().
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *mat,*t_eins,*t_zwei,*ht,*slambda,*hz;
	INT ii,jj,kk,i,k,z,co = (INT)0,dim,diag,mdim,dim_,koeff;
	INT mehr_eins,mehr_zwei;
	TL_BYTE *_bz;

	/*
  Moegliche Eingabefehler...
*/
	if (!lambda) return(LmbNul);
	else if (!lambda[0]) return(LmbEmp);
	else if (!bz) return(BzNul);
	for (i=(INT)0,_n=(INT)0;lambda[i];++i)
		if (lambda[i]<0) return(LmbLt_null);
		else _n += (INT)lambda[i];
	/*
  if (_n>MAXN) return(NGtMax);

  else */
	if (pz<=(INT)0) return(PrmLe_null);
	else if (pz)
	{
		for (i=(INT)0;PZ[i]<=pz;i++);
		if (pz!=PZ[i-1]) return(NoPrm);
	}
	for (i=1L;lambda[i];++i)
		if (lambda[i]>lambda[i-1]) return(LmbNRg);


	/*
  Na denn ma' los...
*/
	/* printeingabe("C1");*/
	_zyk=ZYK/2L+ZYK+1L;
	_zeilenz = i; /* AK 240194 */
	_spaltenz = lambda[0]; /* AK 240194 */
	/*
  if ((_spaltenz=lambda[0])>MAXSPALTENZ) return(SzGtMx);
  if ((_zeilenz=i)>MAXZEILENZ) return(ZzGtMx);
*/
	q_zeilenz=_zeilenz*_zeilenz;
	if (_zeilenz==2L)
	{
		dim_=_k_zweikonmat(lambda,bz,pz);
		/* kann nich sein AK 090792
    if (dim_==NtEMem)
      return(NtEMem);
*/
		if (dim_<(INT)0)
			dim=DmGtMx;
		else
			dim=dim_;
	}
	else
	{ /* allgemeine Partition/Anfang */
		/* printeingabe("C2");*/
		init_mat();
		mat=(TL_BYTE *)TL_calloc((int)(q_zeilenz)+(int)(4*_n)+1,sizeof(TL_BYTE));
		if (mat == NULL)
		{
			close_mat();
			return no_memory();
		}
		t_eins=mat+(INT)q_zeilenz;
		t_zwei=t_eins+(INT)_n;
		ht=t_zwei+(INT)_n;
		/* printeingabe("C3");*/
		slambda=ht+_n;
		mdim=MAXDM;
		_assoziiere(lambda,slambda,_n);
		for (ii=(INT)0,diag=1L;ii<_zeilenz;++ii)
			diag *= fak((INT)lambda[ii]);
		for (ii=(INT)0,kk=(INT)0;ii<_n && lambda[ii];++ii)
		{
			for (jj=kk;jj < (kk+lambda[ii]);jj++)
				ht[jj]=(TL_BYTE)ii;
			kk += lambda[ii];
		}
		for (z=(INT)0;z<_n;t_zwei[z]=ht[z],z++);
		_bz=bz;
		for (i=(INT)0,mehr_zwei=TRUE;mehr_zwei;++i)
		{
			for (z=(INT)0;z<_n;t_eins[z]=ht[z],z++);
			for (k=0,hz=bz+i,mehr_eins=TRUE;mehr_eins;++k)
			{
				/* printeingabe("C4");*/
				if (i==k)
					*_bz++ = (TL_BYTE) TL_MOD(diag,pz);
				else if (k<i)
					/* *_bz++ = bz[k*MAXDM+i];  */
					_bz++;
				else if (i<k)
				{
					schnitt(t_eins,t_zwei,mat);
					/* printeingabe("C5");*/
					koeff=mat_comp(&co,mat,slambda);
					if (koeff!=NtEMem && koeff!=RTabFt)
					{
						*_bz++ = TL_MOD(koeff,pz);
					}
					else
					{
						close_mat();
						SYM_free(mat);
						mehr_zwei = 280194L; 
						nexgitt(NULL,NULL,&mehr_zwei); /* AK 280194 */
						return(koeff);
					}
				}
				/* printeingabe("C6");*/
				if (nexgitt(t_eins,lambda,&mehr_eins))
				{
					close_mat();
					SYM_free(mat);
					return no_memory();
				}
			}
			if ((_zeilenz==1L) || (_spaltenz==1L))
				co=1L;
			if (!i)
			{
				/* printeingabe("C7");*/
				dim=dim_=k;
				if (dim>MAXDM)
				{
					dim_ *= (-1L);
					dim=DmGtMx;
					error("mo.c:internal error 400");
					break;
				}
			}
			if (dim<mdim)
				mdim=dim;
			/* printeingabe("C7");*/
			if (nexgitt(t_zwei,lambda,&mehr_zwei))
			{
				close_mat();
				SYM_free(mat);
				return no_memory();
			}
		}

		close_mat();
		SYM_free(mat);


#define AKSIZE 100
		hz = (TL_BYTE *) TL_malloc(sizeof(TL_BYTE) * MAXDM * AKSIZE);
		for (kk=MAXDM -1; kk>0; kk-= AKSIZE)
		{
			for (jj=0;jj<kk;jj++)
				for (ii=0;(ii<AKSIZE) && (kk-ii > 0) ;ii++)
				{
					hz[MAXDM*ii+jj] = bz[jj*MAXDM+(kk-ii)];
				}
			for (ii=0;(ii<AKSIZE) && (kk-ii > 0) ;ii++)
				memcpy(&bz[(kk-ii)*MAXDM], &hz[ii * MAXDM], kk-ii);
		}


		/*
	for (i=0;i<MAXDM;i++)
		{
		for (k=0;k<i;k++)
			  if(bz[i*MAXDM+k] != bz[k*MAXDM+i])
				printf("%d %d\n",i,k); 
		}

*/
		SYM_free(hz);

	} /*allgemeine Partition/Ende*/
	/* printeingabe("C8");*/
	mehr_zwei = 280194L; 
	nexgitt(NULL,NULL,&mehr_zwei); /* AK 280194 */
	return(dim);
}  /*alkonmat*/


/*----------------------------------------------------------------------------*/
static INT _k_moddreimat(_bz,pz) TL_BYTE *_bz; 
	INT pz;
/*------------------------------------------------------------------------------
  bringt die Matrix bz mit Hilfe des Gaussalgorithmus ueber GF(pz) auf obere
  Dreiecksform mit 1 oder 0 auf der Hauptdiagonalen.
  (Vgl. in MODULDG.C Funktion moddreimat().)
  Variablen:  bz, Koeffizientenmatrix aus k_alkonmat();
              pz, Primzahl;
  Rueckgabe bz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *jz, *z_eins,*z_zwei;
	TL_BYTE qu,mu;
	INT i,j,k;

	for (i=0;i<dm;i++,_bz += (dm+1))
	{
		for (k=i+1,jz=_bz+dm;!*_bz && k<dm;k++,jz += dm)
			if (*jz)
				for (j=dm,z_eins=jz,z_zwei=_bz;j>i;j--)
				{
					mu= *z_zwei;
					*z_zwei++ = *z_eins;
					*z_eins++ = mu;
				}
		if (*_bz)
		{
			if ((qu= *_bz)!=(TL_BYTE)1)
				for (j=dm,z_eins=_bz;j>i;j--,z_eins++)
				{
					if (*z_eins) /* AK 010394 */
						*z_eins=(TL_BYTE)TL_DIVP(*z_eins,qu,pz);
				}
			if (i<dm-(INT)1)
				for (k=i+1L,jz=_bz+dm;k<dm;k++,jz += dm)
					if ((qu= *jz)!=(TL_BYTE)0)
						for (j=dm,z_eins=jz,z_zwei=_bz;j>i;j--,z_eins++,z_zwei++)
							if (*z_zwei)
							{
								*z_eins = TL_MOD( *z_eins - qu * *z_zwei, pz);
							}
		}
	}
	return OK;
} /* _k_moddreimat */


/*----------------------------------------------------------------------------*/
static INT _k_modgauss(bz,pz) TL_BYTE *bz; 
	INT pz;
/*------------------------------------------------------------------------------
  berechnet mit Hilfe des Gaussalgorithmus ueber GF(pz) die Dimension der
  modular irreduziblen Darstellung.
  (Vgl. in MODULDG.C Funktion modgauss().)
  Variablen:  bz, Matrix mit Basis;
              pz, Primzahl.
  Rueckgabe bz.
  Rueckgabewert: Dimension der mod. irred. Darstellung.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_bz,*z_eins,*z_zwei,*z_drei,*z_vier,qu;
	INT i,j,k,prang;

	TL_BYTE mu;

	prang=(INT)0;
	for (i=dm-1,_bz= &bz[qdm-1];i>0;i--,_bz -= (dm+1L))
		if (*_bz)
		{
			if ((qu= *_bz)!=(TL_BYTE)1)
				for (k=i,z_eins=_bz;k<dm;k++,z_eins++)
					if (*z_eins)
						*z_eins=(TL_BYTE)TL_DIVP(*z_eins,qu,pz);

			for (j=i-1L,z_eins= &bz[i*dm+i],z_zwei=z_eins-dm;j>=0;j--,z_zwei -= dm)
				if ((qu= *z_zwei)!=(TL_BYTE)0)
					for (k=dm,z_drei=z_eins,z_vier=z_zwei;k>i;k--,z_drei++,z_vier++)
						if (*z_drei)
						{
							*z_vier = TL_MOD(*z_vier - qu * *z_drei, pz);
						}
		}
		else
			prang++;

	if (bz[0]!=(TL_BYTE)1)
	{
		if ((qu=bz[0])==(TL_BYTE)0)
			prang++;
		else
			for (j=0,_bz=bz;j<dm;j++,_bz++)
				if (*_bz)
					*_bz= (TL_BYTE)TL_DIVP(*_bz,qu,pz);
	}
	return(dm-prang);
} /* _k_modgauss */

INT co_070295(m,p) OP m,p;
/* AK eingabe primzahl p und schnittmatrix m */
{
	TL_BYTE *bz,*z;
	INT i,j;
	bz = (TL_BYTE *) TL_calloc(S_M_HI(m) * S_M_LI(m), sizeof(TL_BYTE));

	for (i=0,z=bz;i<S_M_HI(m);i++)
		for(j=0;j<S_M_LI(m);j++,z++)
			*z = TL_MOD((TL_BYTE)S_M_IJI(m,i,j), S_I_I(p));
	i= k_dimmod(bz,S_M_HI(m),S_I_I(p));
	TL_free(bz);
	return i;
}

INT co_k_dimmod(bz,dim,pz) signed char *bz; INT dim,pz;
{
	return k_dimmod(bz,dim,pz);
}

/*----------------------------------------------------------------------------*/
static INT k_dimmod(bz,dim,pz) TL_BYTE *bz; INT dim,pz;
/*------------------------------------------------------------------------------
  berechnet aus bz, der Koeffizientenmatrix aus k_alkonmat(), die Dimension
  der modular irreduziblen Darstellung fuer ein pz.
  Variablen:  bz, Koeffizientenmatrix aus k_alkonmat();
              dim, Dimension der Matrix;
              pz, Primzahl.
  Rueckgabewert:  Dimension der mod. irred. Darstellung.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	dm=dim;
	dm_zwei=(INT)2*dm;
	qdm=(INT)dm*(INT)dm;
	_k_moddreimat(bz,pz);
	return(_k_modgauss(bz,pz));
} /* k_dimmod */
/*******************************************************************************
*
* Datei MODULDCM.C
*   Version vom 22.11.89
*
*
* Zeile Funktionen
*
*       Funktionen zur Berechnung der Zerlegungszahlen
*       ----------------------------------------------
* 61    INT _nexpart(INT n,INT mode,TL_BYTE *r,TL_BYTE *m)
* 103   INT _part_reg(INT p,INT *r,INT *m)
* 124   INT _num_part(INT n,INT pz)
* 159   INT _r_induk(INT *lambda,INT n,INT pz,INT i,INT r)
* 188   INT _ber_lambdas(INT **lambda,INT n,INT p)
* 238   INT _fakul(INT n)
* 250   INT _assoziiere(TL_BYTE *lambda,TL_BYTE *slambda,INT n)
* 274   INT _dimension(INT *lambda,INT n)
* 302   INT _ber_dim(INT *dim,TL_BYTE **lambda,INT lda,INT n,INT p)
* 366   INT _v_eintrag(TL_BYTE **lambda,INT lanz,TL_BYTE *part,TL_BYTE *v,INT vv,INT n)
* 405   INT _ggT(INT a,INT b)
* 431   INT _ggT_v(TL_BYTE *v,INT vl)
* 455   INT _kleiner(TL_BYTE *col_eins,TL_BYTE *col_zwei,INT len)
* 483   INT _diff(TL_BYTE *col_eins,TL_BYTE *col_zwei,TL_BYTE *erg,INT len)
* 507   INT _red_r_mat(TL_BYTE **r_mat,INT col,INT row)
* 608   INT _teste_r_mat_dim(TL_BYTE **r_mat,INT col,INT row,INT p,INT *dim,
*              INT *rg_dim,INT ab)
* 709   INT _search_dec(INT *decomp,INT n, INT pz)
* 753   _append_dec(INT *decomp,INT row,INT col,INT n,INT pz)
* 778   INT d_mat(TL_BYTE *decomp,INT col,INT row,INT n,INT pz)
*
*******************************************************************************/
/*
  Uebliche Headerfiles
*/




/*
  Defines...
*/
#define _H_IJ(l,i,sl,j) (l[i]-i+sl[j]-j-1L) /* Macro Hook_length */


/*----------------------------------------------------------------------------*/
static INT _nexpart(n,mode,r,m) TL_BYTE *r,*m; INT n, mode;
/*------------------------------------------------------------------------------
  berechnet die naechste Partition von n. Dabei enthaelt r die r[0] Teile der
  Partition und m die Vielfachheiten.
  Variablen:  n, die zu partitionierende Zahl;
              mode, =0 erste Partitionierung,
                    !=0 weitere Partitionierungen.
  Rueckgabe r und m.
  Rueckgabewerte: (INT)0, falls keine weitere Partitionierung moeglich;
                  1L, falls weitere Partitionen von n existieren.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT d,s,sum,f;

	if (sym_timelimit > 0L) /* AK 230996 */
		check_time();

	d=r[0];
	if (mode)
	{
		sum=(r[d]==1L)? m[d--]+1L : 1L;
		f=r[d]-1L;
		if (m[d]!=1L) m[d++]--;
		r[d]=f;
		m[d]=(sum/f)+1L;
		s=sum % f;
		if (s>(INT)0)
		{
			r[++d]=s;
			m[d]=1L;
		}
		r[0]=d;
		return(m[d]!=n);
	}
	else
	{
		r[0]=m[1]=1L;
		r[1]=n;
		return(n!=1L);
	}
} /* _nexpart */


/*----------------------------------------------------------------------------*/
static INT _part_reg(p,r,m) INT p; 
TL_BYTE *r, *m;
/*------------------------------------------------------------------------------
  ueberprueft die Partition gegeben durch r und m, ob sie p-regulaer ist.
  Variablen:  p, Primzahl;
              r, Partition mit r[0]=Laenge von r und m,
                 r[1]...r[r[0]] Elemente der Partition;
              m, Vielfachheiten von r[1]...r[r[0]].
  Rueckgabewerte: (INT)0, falls Partition nicht p-regulaer;
                  1L, falls Partition p-regulaer ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i;
	for (i=1L;i<=r[0];i++)
		if (m[i]>=p)
			return((INT)0);
	return(1L);
} /* _part_reg */


/*----------------------------------------------------------------------------*/
static INT _num_part(n,pz) INT n,pz;
/*------------------------------------------------------------------------------
  berechnet  fuer pz=0 die Anzahl der Partitionen zu n und fuer pz!=0 die
  Anzahl der regulaeren Partitionen.
  Variablen:  n, die zu partitionierende Zahl;
              pz, Primzahl oder 0.
  Rueckgabewerte: >(INT)0, die Anzahl der (p-regulaeren) Partitionen von n;
               (INT)-109, falls nicht genuegend Speicher vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT num,d,e;
	TL_BYTE *r,*m;

	r=(TL_BYTE *)SYM_calloc(2*(int)(n+1),sizeof(TL_BYTE));
	m=r+(INT)n+1L;
	num=(INT)0;
	e=1L;
	d=(INT)0;
	while (e)
	{
		e=d=_nexpart(n,d,r,m);
		if (pz)
		{
			if (_part_reg(pz,r,m)) num++;
		}
		else num++;
	}
	SYM_free(r);
	return(num);
} /* _num_part */


/*----------------------------------------------------------------------------*/
static INT _r_induk(lambda,n,pz,i,r) TL_BYTE *lambda;
	INT n,pz,i,r;
/*------------------------------------------------------------------------------
  ueberprueft die Moeglichkeit einer r-Induktion des zur Partition lambda
  gehoerenden Tableaux in der Zeile i.
  Variablen:  lambda, Partition zu n;
              n;
              pz, Primzahl;
              i, Zeile des Tableaux;
              r, die "Ordnung" des anzuhaengenden Knotens.
  Rueckgabewerte: (INT)0, falls r-Induktion nicht moeglich;
                  1L, falls r-Induktion moeglich ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT len;

	for (len=(INT)0;len<n && lambda[len];len++);
	if (!i) return(TL_MOD(lambda[0],pz)==r);
	else if (i<len)
	{
		if (lambda[i-1]>lambda[i]) return(TL_MOD(lambda[i]-i,pz)==r);
		else return((INT)0);
	}
	else if (i==len) return(TL_MOD(-i,pz)==r);
	else return((INT)0);
} /* _r_induk */


/*----------------------------------------------------------------------------*/
static INT _ber_lambdas(lambda,n,p) INT n,p; 
TL_BYTE **lambda;
/*------------------------------------------------------------------------------
  berechnet fuer p=0 alle eigentlichen Partitionen von n und fuer p!=(INT)0, p
  Primzahl, alle p-regulaeren Partitionen von n.
  Variablen:  n, die zu partitionierende Zahl;
              p, Primzahl oder (INT)0;
  Rueckgabe lambda, Vektor von Partitionen.
  Rueckgabewerte: (INT)0, falls alle Partitionen ohne Fehler berechnet wurden;
              (INT)-109, falls kein Speicher zur Verfuegung stand.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *r,*m;
	INT d,e,i,j,k,l;

	r=(TL_BYTE *)TL_calloc((int)(n+1)*2,sizeof(TL_BYTE));
	if (r == NULL) return no_memory();
	m=r+(INT)(n+1L);
	e=1L;
	k=d=(INT)0;
	while(e)
	{
		d=e=_nexpart(n,d,r,m);
		if (!p)
		{
			for (i=(INT)0;i<n;lambda[k][i++]=(TL_BYTE)0);
			for (i=1L,l=(INT)0;i<=r[0];i++)
				for (j=(INT)0;j<m[i];j++)
					lambda[k][l++]=r[i];
			k++;
		}
		else
		{
			if (_part_reg(p,r,m))
			{
				for (i=(INT)0;i<n;lambda[k][i++]=(TL_BYTE)0);
				for (i=1L,l=(INT)0;i<=r[0];i++)
					for (j=(INT)0;j<m[i];j++)
						lambda[k][l++]=r[i];
				k++;
			}
		}
	}
#ifndef __TURBOC__ /* leider gibt Turbo C hier nicht sauber frei?? */
	SYM_free(r);
#endif
	return((INT)0);
} /* _ber_lambdas */


/*----------------------------------------------------------------------------*/
static INT _fakul(n) INT n;
/*------------------------------------------------------------------------------
  berechnet n! und gibt das Ergebnis als Langzahl zurueck.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	if (n > 12) error("mo:internal error: 500");
	if (n<=1L) return(1L);
	else return ((INT)n*_fakul(n-1L));
} /* _fakul */



/*----------------------------------------------------------------------------*/
static INT _dimension(lambda,n) TL_BYTE *lambda; 
	INT n;
/*------------------------------------------------------------------------------
  berechnet die Dimension der Darstellung zu einer eigentlichen Partition
  mit Hilfe der Hakenformel.
  Variablen:  lambda, Partition;
              n, die partitionierte Zahl.
  Rueckgabewert: Dimension.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,l;
	INT zz,zn;
	TL_BYTE *slambda;
	if (n > (INT)12) /* AK 260195 */
	{
		OP p,a;
		a = callocobject();
		p = callocobject();
		for (l=(INT)0;lambda[l]>0;l++);
		b_ks_pa(VECTOR,callocobject(),p);
		m_il_v(l,S_PA_S(p));
		l--;
		for (i=0;l>=0;i++,l--)
			m_i_i((INT)(lambda[l]),S_PA_I(p,i));

		dimension_partition(p,a);
		l=s_i_i(a);
		freeall(a);
		freeall(p);
		return l;
	}

	slambda=(TL_BYTE *)TL_calloc((int)(n+1),sizeof(TL_BYTE));
	if (slambda == NULL) return no_memory();
	_assoziiere(lambda,slambda,n);
	zz=_fakul(n);
	for (l=(INT)0;l<n && lambda[l];l++);
	for (i=(INT)0,zn=1L;i<l;i++)
		for (j=(INT)0;j<lambda[i];j++)
			zn *= (INT)_H_IJ(lambda,i,slambda,j);
	SYM_free(slambda);
	return((INT)(zz/zn));
} /* _dimension */


/*----------------------------------------------------------------------------*/
static INT _ber_dim(dim,lambda,lda,n,p) INT *dim; 
	TL_BYTE **lambda;
	INT  lda, n,p;
/*------------------------------------------------------------------------------
  berechnet fuer p=0 die Dimensionen zu allen eigentlichen Partitionen lambda
  und fuer p!=(INT)0, p Primzahl, die p-Dimensionen zu allen p-regulaeren Parti-
  tionen lambda.
  Variablen:  lambda, Vektor von Partitionen;
              lda, Laenge des Vektors lambda;
              n, die partitionierte Zahl;
              p, Primzahl oder 0.
  Rueckgabe dim, Vektor der Dimensionen.
  Rueckgabewerte: (INT)0, falls alles ohne Fehler berechnet wurde;
                 <(INT)0, s. Datei MODULKFF.C Funktion alkonmat().
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *slambda;
	INT i,dm,omaxdim,k;
	TL_BYTE *bz;

	omaxdim=MAXDM;
	for (i=(INT)0;i<lda;dim[i++]=(INT)0);
	for (i=(INT)0;i<lda;i++)
	{
		if (p) /* D.h. keine gewoehnliche darstellung */
		{

			MAXDM=_dimension(lambda[i],n);
			if (MAXDM<(INT)0)
			{
				MAXDM=omaxdim;
				return(MAXDM);
			}
			slambda=(TL_BYTE *)TL_calloc((int)(n+1),sizeof(TL_BYTE));
			if (slambda == NULL)
			{
				MAXDM=omaxdim;
				return no_memory();
			}
			bz=(TL_BYTE *)TL_calloc((int)MAXDM*(int)MAXDM,sizeof(TL_BYTE));
			if (bz == NULL)
			{
				MAXDM=omaxdim;
				SYM_free(slambda);
				return no_memory();
			}
			if (lambda[i][0]==5 && lambda[i][1]==4 && lambda[i][2]==2 && n==11L && p==2L)
				dim[i]=416L;
			else
			{
				_assoziiere(lambda[i],slambda,n);
				if ((dm=k_alkonmat(slambda,bz,p))<(INT)0)
				{
					MAXDM=omaxdim;
					SYM_free(slambda);
					SYM_free(bz);
					error("mo:internal error : 345");
					return(dm);
				}
				if ((dim[i]=k_dimmod(bz,MAXDM,p))<(INT)0)
				{
					MAXDM=omaxdim;
					SYM_free(slambda);
					SYM_free(bz);
					error("mo:internal error : 346");
					return(dim[i]);
				}
			}
			SYM_free(bz);
			SYM_free(slambda);

		}
		else
			if ((dim[i]=_dimension(lambda[i],n))<(INT)0)
			{
				MAXDM=omaxdim;
				error("mo:internal error : 347");
				return(dim[i]);
			}
	}
	MAXDM=omaxdim;
	j_zyk((INT) -15,0,NULL,NULL); /* AK 020294 */
	return((INT)0);
} /* _ber_dim */


/*----------------------------------------------------------------------------*/
static INT _v_eintrag(lambda,lanz,part,v,vv,n)
	TL_BYTE **lambda, *part, *v; 
	INT lanz,vv,n;
/*------------------------------------------------------------------------------
  zaehlt das Vorkommen der durch r-Induktion erhaltenen Partition part von
  n in lambda. Dabei wird der Eintrag der Zerlegungsmatrix fuer n-1 berueck-
  sichtigt.
  Variablen:  lambda, Vektor der Partitionen von n;
              lanz, Laenge des Vektors lambda;
              part, Partition, errechnet durch r-Induktion von n-1 nach n;
              v, Spalte der Zerlegungsmatrix;
              vv, Eintrag der Partition part vor der r-Induktion in der Zer-
                  legungsmatrix fuer n-1L;
              n, partitionierte Zahl.
  Rueckgabewerte: (INT)0, alles in Ordnung;
                 -1L, warum existiert kein solches lambda?????
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j;
	INT gefunden;

	for (i=0,gefunden=0;i<lanz && !gefunden;i++)
	{
		for (j=0;j<n;j++)
			if (lambda[i][j]!=part[j])
				break;
		gefunden= (j==n);
	}
	if (gefunden)
	{
		v[i-1] += (TL_BYTE)vv;
		return (INT)0;
	}
	else
		return (INT)-1L;
} /* _v_eintrag */


/*----------------------------------------------------------------------------*/
static INT _ggT(a,b) INT a,b;
/*------------------------------------------------------------------------------
  berechnet mit Hilfe Euklids den ggT zweier Zahlen a und b.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT x,y,r;

	if (a==b)    return(a);
	else if (!a) return(b);
	else if (!b) return(a);
	x=a;
	y=b;
	if (x<y)
	{
		r=x;
		x=y;
		y=r;
	}
	x=a;
	y=b;
	while(y)
	{
		r=x%y;
		x=y;
		y=r;
	}
	return(x);
} /* _ggT */


/*----------------------------------------------------------------------------*/
static INT _ggT_v(v,vl) TL_BYTE *v; 
	INT vl;
/*------------------------------------------------------------------------------
  berechnet den ggT der Eintraege eines Vektors v der Laenge vl und
  multipliziert den Vektor mit 1/ggT.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,ggT;

	for (i=0;i<vl;i++)
		if (v[i]==(TL_BYTE)1)
			return OK;
	ggT=_ggT((INT)v[0],(INT)v[1]);
	for (i=2;i<vl;i++)
		ggT=_ggT(ggT,(INT)v[i]);
	if (ggT>1)
	{
		for (i=0;i<vl;i++)
			v[i] = (TL_BYTE)(v[i]/ggT);
	}
	return OK;
} /* _ggT_v */


/*----------------------------------------------------------------------------*/
static INT _kleiner(col_eins,col_zwei,len)
	TL_BYTE *col_eins, *col_zwei; 
	INT len;
/*------------------------------------------------------------------------------
  vergleicht zwei Spalten col_eins und col_zwei.  Ist col_eins (lexikographisch)
  kleiner als col_zwei, so gibt _kleiner eine 1 zurueck, sonst 0.
  Variablen:  col_eins, erste Spalte;
              col_zwei, zweite Spalte;
              len, Laenge der Spalten.
  Rueckgabewerte: 1L, falls col_eins kleiner col_zwei;
                  (INT)0, sonst.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i;

	if (!col_zwei) return((INT)0);
	if (!col_eins) return(1L);
	for (i=(INT)0;i<len;i++)
		if (col_eins[i] || col_zwei[i])
		{
			if (col_eins[i]<col_zwei[i]) return(1L);
			else if (col_eins[i]==col_zwei[i]) continue;
			else break;
		}
	return((INT)0);
} /* _kleiner */


/*----------------------------------------------------------------------------*/
static INT _diff(col_eins,col_zwei,erg,len)
	TL_BYTE *col_eins, *col_zwei, *erg; 
	INT len;
/*------------------------------------------------------------------------------
  berechnet die Differenz erg=col_eins-col_zwei. Existiert in erg ein Eintrag
  kleiner als (INT)0, so gibt _diff 0 zurueck, sonst 1.
  Variablen:  col_eins, erste Spalte;
              col_zwei, zweite Spalte;
              len, Laenge der Spalten.
  Rueckgabe Ergebnis erg.
  Rueckgabewerte: (INT)0, falls Eintrag von erg <(INT)0;
                  1L, sonst.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i;

	for (i=0;i<len;erg[i++]=(TL_BYTE)0);
	for (i=0;i<len;i++)
		if ((erg[i]=col_eins[i]-col_zwei[i])<(TL_BYTE)0)
			return (INT)0;
	return (INT)1;
} /* _diff */


/*----------------------------------------------------------------------------*/
static INT _red_r_mat(r_mat,col,row) TL_BYTE **r_mat; 
	INT col,row;
/*------------------------------------------------------------------------------
  untersucht die Matrix r_mat auf Spalten, die (INT)0, gleich oder von
  anderen abgezogen werden koennen.
  Variablen:  r_mat, Matrix aller durch r-Induktion entstandenen
                     Spalten;
              col, Anzahl der Spalten von r_mat;
              row, Anzahl der Zeilen von r_mat;
  Rueckgabe ausreduzierte Matrix r_mat.
  Rueckgabewerte: (INT)0, alles ohne Fehler gelaufen;
              (INT)-109, falls nicht genuegend Speicher verfuegbar war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,k,l,max;
	TL_BYTE *r;
	TL_BYTE *hp,*c;
	INT gleiche;

	c=(TL_BYTE *)TL_calloc((int)(col+row),sizeof(TL_BYTE));
	if (c == NULL)
		return no_memory();
	r=c+(int)row;
	for (i=0;i<col;i++) /* pruefe, ob in r_mat Spalte=0 existiert */
	{
		if (r_mat[i] == NULL)
			continue;
		for (j=0;j<row;j++)
			if (r_mat[i][j] != (TL_BYTE)0)
				break;
		if (j==row)       /* wenn ja, vergesse Spalte */
			r_mat[i]=(TL_BYTE *)NULL;
	}
	for (i=0;i<col-1;i++)
	/* pruefe, ob in r_mat zwei Spalten gleich sind */
	{
		if (r_mat[i] == NULL) continue;
		for (j=i+1L;j<col;j++)
		{
			if (!r_mat[j])
				continue;
			for (k=0;k<row;k++)
				if (r_mat[i][k]!=r_mat[j][k])
					break;
			if (k==row)      /* wenn ja, vergesse eine davon */
				r_mat[j]=NULL;
		}
	}
	for (i=0;i<col-1;i++) /* sortiere Spalten in r_mat lexikographisch */
	{                     /* absteigend */
		max=i;
		for (j=i+1L;j<col;j++)
			if (_kleiner(r_mat[max],r_mat[j],row))
				max=j;
		if (max!=i)
		{
			hp=r_mat[i];
			r_mat[i]=r_mat[max];
			r_mat[max]=hp;
		}
	}
	for (i=0;i<col;i++)      /* belege r[i] mit der Zeilennummer des ersten */
		if (!r_mat[i]) r[i]=(TL_BYTE)0; /* Eintrags in  der Spalte r_mat[i] */
		else
			for (j=0;j<row;j++)
				if (r_mat[i][j])
				{
					r[i]=(TL_BYTE)j+1;
					break;
				}
	for (i=0,gleiche=0;i<col-1 && !gleiche;i++)
	{ /* ueberpruefe r auf gleiche Eintraege */
		if (!r[i]) continue;
		for (j=i+1L;j<col;j++)
		{
			if (!r[j]) continue;
			if (r[i]==r[j]) /* existieren zwei gleiche Eintraege: */
			{
				if (_diff(r_mat[i],r_mat[j],c,row)) /* probiere, die zwei Spalten */
					for (k=0;k<row;k++)               /* voneinander abzuziehen */
						r_mat[i][k]=c[k];
				else /* lassen sie sich nicht abziehen, probiere, hintere Spalten */
					/* von der lex. kleineren der beiden Spalten abzuziehen */
					for (k=col-(INT)1;k>j;k--)
					{
						if (!r_mat[k]) continue;
						if (_diff(r_mat[j],r_mat[k],c,row))
						{
							for (l=0;l<row;l++)
								r_mat[j][l]=c[l];
							break;
						}
					}
				gleiche=1;
				break;
			}
		}
	}
	if (gleiche)                     /* gab es gleiche Spalten, so */
		if (_red_r_mat(r_mat,col,row)) /* untersuche r_mat nochmals */
		{
			SYM_free(c);
			return no_memory();
		}
	SYM_free(c);
	return (INT)0;
} /* _red_r_mat */


/*----------------------------------------------------------------------------*/
static INT _teste_r_mat_dim(r_mat,col,row,p,dim,rg_dim,ab)
	INT *dim, *rg_dim; 
	TL_BYTE **r_mat; 
	INT col,row,p,ab;
/*------------------------------------------------------------------------------
  untersucht die Zeilen von r_mat auf Richtigkeit. Dabei werden die p-Dimen-
  sionen der p-regulaeren Partitionen multipliziert mit den korrespon-
  dierenden Eintraegen in den Zeilen von r_mat aufsummiert und schliesslich
  mit den jeweiligen gewoehnlichen Dimensionen zu den Partitionen verglichen.
  Variablen:  r_mat, vorher mit _red_r_mat() ueberpruefte Matrix der mit
                     r-Induktion erhaltenen Spalten;
              col, Anzahl der p-regulaeren Partitionen;
              row, Anzahl der eigentlichen Partitionen;
              dim, Dimensionen der gew. irred. Dg.en zu den eigentlichen
                   Partitionen;
              rg_dim, p-Dimensionen der mod. irred. Dg.en zu den p-regulaeren
                      Partitionen.
  Rueckgabe Matrix r_mat, ueberprueft und eventl. mit neuen Spalten, die
    durch Abziehen lexikographisch kleinerer Spalten von der alten entstanden
    ist.
  Rueckgabewerte: (INT)0, alles ohne Fehler abgelaufen;
              (INT)-109, falls nicht genuegend Speicher vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,k,clmn,dm;
	TL_BYTE *c,*r, *hp;
	INT err,l;

	clmn=col*p;
	c=(TL_BYTE *)TL_calloc((int)row*2+(int)clmn,sizeof(TL_BYTE));
	if (c == NULL) return no_memory();
	hp=c+(int)row;
	r=hp+(int)row;

	for (i=ab;i<row;i++)
	{
		for (j=0,k=0,dm=0;j<clmn;j++)
		/* summiere in den Zeilen die Produkte */
		{                             /* aus Eintraegen von r_mat und Dimen- */
			if (r_mat[j] == NULL) continue;    /* sionen der p-regulaeren Partitionen */
			dm += (rg_dim[k++]*(INT)r_mat[j][i]);
		}
		if (dm>dim[i]) break;
		else if (dm<dim[i])
		{
			fprintf(stderr,"\n dm = %d : %d \n",dm,dim[i]);
			SYM_free(c);
			error("MO-1:internal error");
			return (INT)-1;
		}
	}
	if (i==row)
	{
		SYM_free(c);
		return((INT)0);
	}
	for (j=(INT)0;j<clmn;j++)     /* belege r[i] mit der Zeilennummer des ersten */
		if (r_mat[j])          /* Eintrags in  der Spalte r_mat[i] */
			for (k=(INT)0;k<row;k++)
			{
				if (r_mat[j][k])
				{
					r[j]=(TL_BYTE)k+1;
					break;
				}
			}
		else r[j]=(INT)0;
	for (j=(INT)0;j<clmn-(INT)1;j++)
	{
		if (!r_mat[j]) continue;
		if (r_mat[j][i])
		{
			for (k=j+1L;k<clmn;k++)
			{
				if (!r[k]) continue;
				if (i+1!=r[k]) continue;
				if (r_mat[k][i])
				{
					if (_diff(r_mat[j],r_mat[k],c,row))
					{
						for (l=(INT)0;l<row;l++)
						{
							hp[l]=r_mat[j][l];
							r_mat[j][l]=c[l];
						}
						if ((err=_teste_r_mat_dim(r_mat,col,row,p,dim,rg_dim,i))<(INT)0 )
						{
							for (l=(INT)0;l<row;l++)
								r_mat[j][l]=hp[l];
							if (err == (INT)-109)
							{
								SYM_free(c);
								return(err);
							}
							break;
						}
						SYM_free(c);
						return((INT)0);
					}
				}
			}
		}
	}
	SYM_free(c);
	return (INT)0;
} /* _teste_r_mat_dim */


/*----------------------------------------------------------------------------*/
static INT _search_dec(decomp,n,pz)  INT pz,n; 
TL_BYTE *decomp;
/*------------------------------------------------------------------------------
  sucht im File 'decommix.dat' nach, ob die Zerlegungsmatrix fuer n und pz
  schon einmal berechnet wurde.
  Variablen:  decomp, Zerlegungsmatrix;
              n, Sn;
              pz, Primzahl.
  Rueckgabe der Zerlegungsmatrix fuer n und pz, falls gefunden.
  Rueckgabewerte: (INT)0, falls keine Zerlegungsmatrix fuer n und pz gefunden werden
                     konnte;
                  1L, falls Zerlegungsmatrix fuer n und pz existiert.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	FILE *dfp;
	INT  info[4],i,j,k;
	TL_BYTE *d;
	INT end;

	dfp=fopen("decommix.dat","r");
	if (!dfp) return (INT) 0;
	rewind(dfp);
	do
	{
		/* fread(info,sizeof(INT),4,dfp); */
		fscanf(dfp,"%d",&info[0]);
		fscanf(dfp,"%d",&info[1]);
		fscanf(dfp,"%d",&info[2]);
		fscanf(dfp,"%d",&info[3]);
		if (info[0]==n && info[1]==pz)
		{
			/*
      fread(decomp,sizeof(TL_BYTE),(int)info[2]*(int)info[3],dfp);
	*/
			j = info[2] * info[3];
			for (i=(INT)0; i<j;i++)
			{ 
				fscanf(dfp,"%d",&end);  
				decomp[i] = (TL_BYTE) end; 
			}
			fclose(dfp);
			return (INT) 1;
		}
		else
		{
			if ( (int)info[2]*(int)info[3] == 0) /* AK 311293 */
				return (INT)0;
			/*
      d=(TL_BYTE *)TL_calloc((int)info[2]*(int)info[3],sizeof(TL_BYTE));
      if (d==NULL) return((INT)0);
      end=fread(d,sizeof(TL_BYTE),(int)info[2]*(int)info[3],dfp);
      SYM_free(d);
	*/
			j = info[2] * info[3];
			for (i=(INT)0; i<j;i++)
			{ 
				end = (fscanf(dfp,"%d",&k) > 0) ;
			}
		}
	} while(end);
	fclose(dfp);
	return((INT)0);
} /* _search_dec */


/*----------------------------------------------------------------------------*/
static INT _append_dec(decomp,row,col,n,pz) TL_BYTE *decomp; 
	INT row,col,n,pz;
/*------------------------------------------------------------------------------
  haengt an das Ende des Files 'decommix.dat' eine fuer n und pz noch nicht
  berechnete Zerlegungsmatrix.
  Variablen:  decomp, Zerlegungsmatrix;
              row, Zeilenzahl der Zerlegungsmatrix;
              col, Spaltenzahl der Zerlegungsmatrix;
              n, Sn;
              pz, Primzahl.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	FILE *dfp;
	INT  info[4],i,j;

	dfp=fopen("decommix.dat","a+");
	if (!dfp) return ERROR;
	info[0]=n;
	info[1]=pz;
	info[2]=row;
	info[3]=col;
	fprintf(dfp,"%ld %ld %ld %ld \n ",info[0],info[1],info[2],info[3]);
	j = info[2] * info[3];
	for (i=(INT)0; i<j;i++)
		fprintf(dfp,"%d ",(int)decomp[i]);
	fprintf(dfp,"\n");
	fclose(dfp);
	return OK;
} /*_append_dec */


/*----------------------------------------------------------------------------*/
static INT d_mat(decomp,col,row,n,pz) TL_BYTE *decomp; 
	INT col,row,n,pz;
/*------------------------------------------------------------------------------
  berechnet die (row x col)-Zerlegungsmatrix decomp zu n und der Primzahl pz.
  Variablen:  col, Spaltenzahl der Zerlegungsmatrix;
              row, Zeilenzahl der Zerlegungsmatrix;
              n;
              pz, Primzahl.
  Rueckgabe Zerlegungsmatrix decomp.
  Rueckgabewerte: (INT)0, alles ohne Fehler;
              sonst, s. Datei MODULKFF.C Funktion alkonmat().
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  **lambda,**rg_lambda,*part,*pr,*mr,*v;
	INT *dim,*rg_dim;
	INT num,i,j,k,l,r,e,d,o,p,m,err,vv;
	TL_BYTE  *odec;
	INT orow,ocol;
	TL_BYTE **r_mat,*z;
	TL_BYTE **hr,*hrc;
	INT erg = OK;

	if (n<=1L)
	{
		decomp[0]=(TL_BYTE)1;
		return((INT)0);
	}
	else
	{
		if (_search_dec(decomp,n,pz))
			return((INT)0);
		if ((orow=_num_part(n-1L,(INT)0))<(INT)0) return(orow);
		ocol=_num_part(n-1L,pz);
		odec=(TL_BYTE *)TL_calloc((int)ocol*(int)orow,sizeof(TL_BYTE));
		if (!odec) return no_memory();
		if ((err=d_mat(odec,ocol,orow,n-1L,pz))<(INT)0)
		{
			SYM_free(odec);
			return error("d_mat:error in n-1");
		}
		lambda=(TL_BYTE **)TL_calloc((int)row+(int)col,sizeof(TL_BYTE *));
		if (lambda == NULL)
		{
			SYM_free(odec);
			return no_memory();
		}
		/* printeingabe("1");*/
		rg_lambda=lambda+(INT)row;
		lambda[0]=(TL_BYTE *)TL_calloc((int)(row+col)*(int)(n+1),sizeof(TL_BYTE));
		if (lambda[0] == NULL)
		{
			SYM_free(odec);
			SYM_free(lambda);
			return no_memory();
		}
		for (i=1L;i<row;i++)
			lambda[i]=lambda[i-1]+n;
		/* printeingabe("2");*/
		if ((err=_ber_lambdas(lambda,n,(INT)0))<(INT)0)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			return error("d_mat:error in ber_lambdas");
		}
		rg_lambda[0]=lambda[row-1]+(TL_BYTE)n;
		for (i=1L;i<col;i++)
			rg_lambda[i]=rg_lambda[i-1]+(INT)n;
		/* printeingabe("3");*/
		if ((err=_ber_lambdas(rg_lambda,n,pz))<(INT)0)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			return error("d_mat:error in ber_rlambdas");
		}
		/* dim=rg_lambda[col-1]+(INT)n; */
		dim = (INT *) TL_calloc(row+col,sizeof(INT));
		rg_dim=dim+(INT)row;
		/* printeingabe("4");*/
		if ((err=_ber_dim(dim,lambda,row,n,(INT)0))<(INT)0)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(dim);
			return error("d_mat: error in ber_dim");
		}
		/* printeingabe("5");*/
		if ((err=_ber_dim(rg_dim,rg_lambda,col,n,pz))<(INT)0)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(dim);
			return error("d_mat: error in ber_dim rlambdas");
		}
		hr=r_mat=(TL_BYTE **)TL_calloc((int)(col*pz),sizeof(TL_BYTE *));
		/* printeingabe("6");*/
		if (!r_mat)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(dim);
			return no_memory();
		}
		hrc=r_mat[0]=(TL_BYTE *)TL_calloc((int)(col*pz)*(int)row,sizeof(TL_BYTE));
		if (!r_mat[0])
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(r_mat);
			SYM_free(dim);
			return no_memory();
		}
		/* printeingabe("7");*/
		for (i=1L;i<col*pz;i++)
			r_mat[i]=r_mat[i-1]+row;
		part=(TL_BYTE *)TL_calloc(3*(int)n+2+(int)row,sizeof(TL_BYTE));
		if (!part)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(r_mat[0]);
			SYM_free(r_mat);
			SYM_free(dim);
			return no_memory();
		}
		pr=part+(INT)n;
		mr=pr+(INT)n+1L;
		v=mr+(INT)n+1L;
		k=(INT)0;
		/*
  Berechne alle r-Induktionen und lege die Ergebnisse in der Matrix r_mat
  spaltenweise ab.
*/
		/* printeingabe("8");*/
		for (l=(INT)0;l<ocol && k<(col*pz);l++)
		{
			for (i=(INT)0,num=(INT)0;i<orow;i++)
				if (odec[i*ocol+l])
					num ++;
			for (r=(INT)0;r<pz && k<(col*pz);r++)
			{
				e=1L;
				d=(INT)0;
				j=(INT)0;
				for (i=(INT)0;i<row;v[i++]=(TL_BYTE)0);
				for (i=(INT)0;i<num;i++)
				{
					do
					{
						e=d=_nexpart(n-1L,d,pr,mr);
						vv=odec[j*ocol+l];
						j++;
					} while(!vv && e);
					for (o=(INT)0;o<n;part[o++]=(TL_BYTE)0);
					for (p=1L,m=(INT)0;p<=pr[0];p++)
					{
						for (o=(INT)0;o<mr[p];o++)
							part[m++]=pr[p];
					}
					for (p=(INT)0;p<n;p++)
						if (_r_induk(part,(INT)n-1,pz,p,r))
						{
							part[p]++;
							_v_eintrag(lambda,row,part,v,vv,n);
							part[p]--;
						}
				}
				for (i=0;i<row;i++)
					if(v[i])
					{
						_ggT_v(v,row);
						break;
					}
				for (i=0;i<row;i++)
					r_mat[k][i]=v[i];
				k++;
			}
		}
		/* printeingabe("9");*/
		/*
  Durchsuche nun r_mat nach ueberfluessigen Spalten und
  errechne schliesslich die entgueltige Zerlegungsmatrix fuer n und pz.
*/
		if ((err=_red_r_mat(r_mat,col*pz,row))<(INT)0)
		{
			SYM_free(odec);
			SYM_free(lambda[0]);
			SYM_free(lambda);
			SYM_free(hrc);
			SYM_free(hr);
			SYM_free(part);
			SYM_free(dim);
			erg += error("d_mat:red_r_mat");
			goto dm1;
		}
		/* printeingabe("10");*/
		if ((err=_teste_r_mat_dim(r_mat,col,row,pz,dim,rg_dim,(INT)0))<(INT)0)

		{
			erg += SYM_free(odec);
			erg += SYM_free(lambda[0]);
			erg += SYM_free(lambda);
			erg += SYM_free(hrc);
			erg += SYM_free(hr);
			erg += SYM_free(part);
			erg += SYM_free(dim);
			erg += error("d_mat:teste_r_mat_dim");
			goto dm1;

		}
		for (i=(INT)0,k=(INT)0;i<col*pz;i++)
			if (r_mat[i])
			{
				for (j=(INT)0,z=decomp+k;j<row;j++,z +=col)
					*z = r_mat[i][j];
				k++;
			}
		/* printeingabe("11");*/
		_append_dec(decomp,row,col,n,pz);
		SYM_free(lambda[0]);
		SYM_free(lambda);
		SYM_free(hrc);
		SYM_free(hr);
		SYM_free(odec);
		SYM_free(part);
		SYM_free(dim);
dm1:
		if (erg != OK)
			EDC("mo.c:d_mat");
		return (INT)0;
	}
} /* d_mat */

/*----------------------------------------------------------------------------*/
INT moddg(prime,llambda,pi,dmat) OP prime; 
	OP llambda; 
	OP pi; 
	OP dmat;
/*------------------------------------------------------------------------------
  berechnet zu einer Primzahl prime, einer Partition llambda und einer
  Permutation pi die modulare Matrixdarstellung dmat.
  Variablen:  prime,  Primzahl  (objectkind: INTEGER);
      lambda, Partition (objectkind: PARTITION);
      pi, Permutation (objectkind: PERMUTATION).
  Rueckgabewerte: >=(INT)0, Dimension der Darstellung;
      -1L,  falls Fehler Aufgetreten ist.
  Rueckgabe darstellende Matrix dmat, die erst hier dimensioniert wird,
    falls die Dimension groesser 0 ist.
------------------------------------------------------------------------------*/
{
	TL_BYTE *part,*bz,*perm;
	TL_BYTE *darmat[2],*dar;
	INT pz,dim;
	INT spe,i,j,l_pa,l_p,gzl;
	OP   dimen;
	OP lambda;

	if (equal_parts(llambda,prime))
	{
		fprint(stderr,llambda);
		fprintln(stderr,prime);
		return error("moddg: wrong partition, wrong prime");
	}


	if (S_PA_LI(llambda) == 1L)  /* AK 020692 */
		if (S_PA_II(llambda,(INT)0) == 1L)  /* AK 020692 */
		{  /* AK 020692 */
			m_ilih_m(1L,1L,dmat);  /* AK 020692 */
			m_i_i(1L,S_M_IJ(dmat,(INT)0,(INT)0));  /* AK 020692 */
			return OK;  /* AK 020692 */
		}  /* AK 020692 */

	dimen=callocobject();
        weight(llambda,dimen);
        if (neq(dimen,S_P_L(pi))) { /* AK 310702 */
	    fprint(stderr,llambda);
	    fprintln(stderr,pi);
	    error("moddg: wrong permutation, wrong degree");
            freeall(dimen);
            return ERROR;
            }
	lambda=callocobject();

	conjugate(llambda,lambda);

	l_pa=S_PA_LI(lambda);
	l_p=S_P_LI(pi);
	spe=l_pa+l_p+2L;
	dimension(lambda,dimen);
	MAXDM=(INT)S_I_I(dimen);
	spe += ((INT)MAXDM*(INT)MAXDM*5L);
	part=(TL_BYTE *)TL_calloc(spe,sizeof(TL_BYTE));
	if (!part)
                {
                freeall(dimen);
                freeall(lambda); 
		return(-1L);
                }
	perm=part+l_pa+1;
	bz=perm+l_p+1;
	for (i=0;i<l_pa;i++)
		part[i]=(TL_BYTE)S_PA_II(lambda,(l_pa-1L-i));
	for (i=0;i<l_p;i++)
		perm[i]=(TL_BYTE)S_P_II(pi,i);
	if ((dim=alkonmat(part,perm,bz))<(INT)0)
	{
		freeall(dimen);
		freeall(lambda);
		SYM_free(part);
		return error("mo.c: internal MO-12");
	}
	darmat[0]=(TL_BYTE *)TL_calloc((int)dim*(int)dim,sizeof(TL_BYTE));
	darmat[1]=(TL_BYTE *)TL_calloc((int)dim*(int)dim,sizeof(TL_BYTE));
	if (!darmat[0])
	{
		freeall(dimen);
		freeall(lambda);
		SYM_free(part);
		return error("mo.c: internal MO-13");
	}
	if (!darmat[1])
	{
		freeall(dimen);
		freeall(lambda);
		SYM_free(part);
		return error("mo.c: internal MO-14");
	}
	pz=(INT)S_I_I(prime);
	gzl=1L;
	if ((dim=darmod(part,dim,bz,pz,&gzl,perm,darmat))
	    <=(INT)0) /* AK 020692 <= statt < */
	{
		freeall(dimen);
		freeall(lambda);
		SYM_free(part);
		SYM_free(darmat[0]); /* AK 020692 statt free(darmat) */
		SYM_free(darmat[1]); /* AK 020692 statt free(darmat) */
		fprintf(stderr,"error-no = %ld\n",dim);
		return error("mo.c: internal MO-15");
	}
	m_ilih_m(dim,dim,dmat);
	for (i=(INT)0,dar=darmat[1];i<dim;i++)
		/* darmat[1] statt darmat[0] *//* AK 301091 */
		for (j=(INT)0;j<(INT)dim;j++)
			m_i_i((INT)(*dar++),s_m_ij(dmat,i,j));
	freeall(dimen);
	freeall(lambda);
	SYM_free(part);
	SYM_free(darmat[0]);
	SYM_free(darmat[1]);
	return((INT)dim);
} /* moddg */


/*----------------------------------------------------------------------------*/
INT decp_mat(sn,prime,dmat) OP sn; OP prime; OP dmat;
/*-----------------------------------------------------------------------------
  berechnet zu Sn und einer Primzahl prime die Zerlegungsmatrix dmat.
  Variablen:    sn, Sn;
                prime, Primzahl.
  Rueckgabewerte: (INT)0, falls kein Fehler aufgetreten ist;
                 -1L, falls Fehler aufgetreten ist.
  Rueckgabe Zerlegungsmatrix dmat.
-----------------------------------------------------------------------------*/
/* AK 300398 V2.0 */
{
	INT TL_n,p,row,col;
	TL_BYTE *dec,*d;
	INT i,j,erg=OK;

	TL_n=(INT)S_I_I(sn);
	p=(INT)S_I_I(prime);
	if ((col=_num_part(TL_n,p))<(INT)0) return(ERROR);
	row=_num_part(TL_n,(INT)0);
	dec=(TL_BYTE *)TL_calloc((int)col*(int)row,sizeof(TL_BYTE));
	if (!dec) return(ERROR);
	if (d_mat(dec,col,row,TL_n,p))
	{
		SYM_free(dec);
		return EDC("decp_mat");
	}
	m_ilih_m((INT)col,(INT)row,dmat);
	for (i=(INT)0,d=dec;i<(INT)row;i++)
		for (j=(INT)0;j<(INT)col;j++)
			m_i_i((INT)(*d++),S_M_IJ(dmat,i,j));
	SYM_free(dec);
	return((INT)0);
} /* decp_mat */


/*----------------------------------------------------------------------------*/
static INT homp(transmat,nzykmat,sn,prime,relation)
	OP transmat; 
	OP nzykmat; 
	OP sn; 
	OP prime; 
	OP relation;
/*------------------------------------------------------------------------------
  testet die Darstellung ueber die darstellenden Matrizen einer
  Transposition und eines n-Zykels.
  Variablen:  transmat, darstellende Matrix einer Transposition
        (objectkind: MATRIX);
      nzykmat,  darstellende Matrix eines n-Zykels
        (objectkind: MATRIX);
      sn,  Sn (objectkind: INTEGER);
      prime,  Primzahl,fuer welche die darstellenden Matrizen
        berechnet wurden (objectkind: INTEGER).
  Rueckgabewerte: (INT)0,  alle Relationen sind erfuellt;
      >(INT)0, Relation ... ist nicht erfuellt;
      -1L,  Fehler aufgetreten.
  Rueckgabe relation erhaelt die Nummer der nicht erfuellten Relation
    oder 0.
------------------------------------------------------------------------------*/
{
	TL_BYTE  *darmat[2],*d[2];
	INT dm,i_n,rl,pz;
	INT i,j;

	if (!S_M_LI(transmat))
	{
		m_i_i((INT)0,relation);
		return((INT)0);
	}
	dm=(INT)S_M_LI(transmat);
	i_n=(INT)S_I_I(sn);
	pz=(INT)S_I_I(prime);
	darmat[0]=(TL_BYTE *)TL_calloc((int)dm*(int)dm*2,sizeof(TL_BYTE));
	if (!darmat[0])
		return(-1L);
	darmat[1]=darmat[0]+(INT)dm*(INT)dm;
	for (i=(INT)0,d[0]=darmat[0],d[1]=darmat[1];i<(INT)dm;i++)
		for (j=(INT)0;j<(INT)dm;j++)
		{
			*d[0]++ =(INT)S_M_IJI(transmat,i,j);
			*d[1]++ =(INT)S_M_IJI(nzykmat,i,j);
		}
	if ((rl=homtestp(darmat,i_n,dm,pz))<(INT)0)
	{
		SYM_free(darmat[0]);
		return(-1L);
	}
	m_i_i((INT)rl,relation);
	SYM_free(darmat[0]);
	return((INT)rl);
} /* homp */


/*----------------------------------------------------------------------------*/
INT brauer_char(sn,prime,bc) OP sn,prime,bc;
/*------------------------------------------------------------------------------
  berechnet die Charaktertafel der Brauercharaktere der Sn zur Primzahl prime.
  Variablen:    sn, Sn (objectkind:INTEGER);
                prime,Primzahl (objectkind:INTEGER).
  Rueckgabewerte: (INT)0, falls fehlerfrei;
                 -1L, falls Fehler aufgetreten ist.
  Rueckgabe der Charaktertafel bc.
------------------------------------------------------------------------------*/
{
	INT _n,p,col,*idx,*idm;
	INT i,j,k,erg = OK;
	OP  tafel,decomp, su, mu, _su;

	if (not primep(prime))
		return error("brauer_char:second parameter no prime");


	_n=(INT)S_I_I(sn);
	p=(INT)S_I_I(prime);
	if ((col=_num_part(_n,p))<(INT)0)
		return(-1L);
	idx=(INT *)TL_calloc((int)col*2,sizeof(INT));
	if (!idx)
	{
		return ERROR;
	}
	idm=idx+(INT)col;
	if (_ber_idx_pelem(_n,p,col,idx))
	{
		SYM_free(idx);
		return(-1L);
	}

	tafel=callocobject();
	decomp=callocobject();
	su=callocobject();
	mu=callocobject();
	_su=callocobject();

	if (decp_mat(sn,prime,decomp))
	{
		SYM_free(idx);
		freeall(tafel);
		freeall(decomp);
		freeall(su);
		freeall(mu);
		freeall(_su);
		return(-1L);
	}
	_ber_inx_dec(decomp,idm);
	chartafel(sn,tafel);
	m_ilih_m((INT)col,(INT)col,bc);
	for (i=(INT)0;i<(INT)col;i++)
		for (j=(INT)0;j<(INT)col;j++)
		{
			copy(S_M_IJ(tafel,(INT)idm[i],(INT)idx[j]),su);
			for (k=(INT)0;k<i;k++)
			{
				erg += mult(S_M_IJ(decomp,(INT)idm[i],k),S_M_IJ(bc,k,j),mu);
				erg += addinvers(mu,_su);
				erg += add_apply(_su,su);
			}
			erg += copy(su,S_M_IJ(bc,i,j));
		}
	SYM_free(idx);
	erg += freeall(tafel);
	erg += freeall(decomp);
	erg += freeall(su);
	erg += freeall(_su);
	erg += freeall(mu);
	ENDR("brauer_char");
} /* brauer_char */
/*
  test the functions moddg(...), homp(...), decp_mat(...) and
  brauer_char(...).
*/


INT test_mdg()
{
	OP  lambda=callocobject();
	OP  trans=callocobject();
	OP  transmat=callocobject();
	OP  nzyk=callocobject();
	OP  nzykmat=callocobject();
	OP  prime=callocobject();
	OP  sn=callocobject();
	OP  relation=callocobject();
	INT i_n,i,dim;

	scan(PARTITION,lambda);
	scan(INTEGER,prime);
	weight(lambda,sn);
	i_n=S_I_I(sn);
	init(PERMUTATION,trans);
	m_il_v(i_n,S_P_S(trans));
	m_i_i(2L,S_P_I(trans,(INT)0));
	m_i_i(1L,S_P_I(trans,1L));
	for (i=2L;i<i_n;i++) m_i_i(i+1L,S_P_I(trans,i));
	println(trans);
	if ((dim=moddg(prime,lambda,trans,transmat))<(INT)0)
	{
		freeall(lambda);
		freeall(prime);
		freeall(trans);
		freeall(transmat);
		freeall(nzyk);
		freeall(nzykmat);
		freeall(sn);
		freeall(relation);
		return(-1L);
	}
	println(transmat);
	init(PERMUTATION,nzyk);
	m_il_v(i_n,S_P_S(nzyk));
	for(i=(INT)0;i<i_n-1L;i++) m_i_i(i+2L,S_P_I(nzyk,i));
	m_i_i(1L,S_P_I(nzyk,i_n-1L));
	println(nzyk);
	if ((dim=moddg(prime,lambda,nzyk,nzykmat))<(INT)0)
	{
		freeall(lambda);
		freeall(prime);
		freeall(trans);
		freeall(transmat);
		freeall(nzyk);
		freeall(nzykmat);
		freeall(sn);
		freeall(relation);
		return(-1L);
	}
	println(nzykmat);
	if (homp(transmat,nzykmat,sn,prime,relation)<(INT)0)
	{
		freeall(lambda);
		freeall(prime);
		freeall(trans);
		freeall(transmat);
		freeall(nzyk);
		freeall(nzykmat);
		freeall(sn);
		freeall(relation);
		return(-1L);
	}
	println(relation);
	freeall(lambda);
	freeall(relation);
	freeall(trans);
	freeall(transmat);
	freeall(nzyk);
	freeall(nzykmat);
	freeall(sn);
	freeall(prime);
	return OK;
} /* test_mdg */


INT test_dcp()
{
	OP  prime=callocobject();
	OP  sn=callocobject();
	OP  decmat=callocobject();

	scan(INTEGER,sn);
	scan(INTEGER,prime);
	if (decp_mat(sn,prime,decmat))
	{
		freeall(prime);
		freeall(sn);
		freeall(decmat);
		return(-1L);
	}
	println(decmat);
	freeall(prime);
	freeall(sn);
	freeall(decmat);
	return((INT)0);
} /* test_dcp */


INT test_brc()
{
	OP  prime=callocobject();
	OP  sn=callocobject();
	OP  tafel=callocobject();

	scan(INTEGER,sn);
	scan(INTEGER,prime);
	if (brauer_char(sn,prime,tafel))
	{
		freeall(prime);
		freeall(sn);
		freeall(tafel);
		return(-1L);
	}
	println(tafel);
	freeall(prime);
	freeall(sn);
	freeall(tafel);
	return((INT)0);
} /* test_brc */

/*----------------------------------------------------------------------------*/
static INT _ber_idx_pelem(sn,p,c,idx) INT sn,p,c,*idx;
/*------------------------------------------------------------------------------
  berechnet Index eines p-Elements in der Liste der Partitionen der Sn.
  Variablen:    sn, Sn;
                p, Primzahl;
                c, Anzahl der p-Elemente.
  Rueckgabewerte: (INT)0, kein Fehler aufgetreten;
              (INT)-109, nicht genuegend Speicher.
  Rueckgabe Indexvektor idx.
------------------------------------------------------------------------------*/
{
	INT i,j,e,d;
	TL_BYTE *r,*m;
	INT *id;

	for (i=(INT)0;i<c;idx[i++]=(INT)0);
	r=(TL_BYTE *)TL_calloc((int)(sn+1)*2,sizeof(TL_BYTE));
	if (r == NULL) return no_memory();
	m=r+sn+1L;
	e=1L;
	d=(INT)0;
	i=(INT)0;
	id=idx;
	while (e)
	{
		e=d=_nexpart(sn,d,r,m);
		for (j=1L;j<=r[0];j++)
			if (!(r[j]%p))
				break;
		if (j>r[0]) *id++ =i;
		i++;
	}
	SYM_free(r);
	return((INT)0);
} /* _ber_idx_pelem */


/*----------------------------------------------------------------------------*/
static INT _ber_inx_dec(dcm,idx) OP dcm; 
	INT *idx;
/*------------------------------------------------------------------------------
  berechnet in den Spalten der Zerlegungsmatrix dcm den Zeilenindex des ersten
  Elements !=0.
  Variablen:    dcm, Zerlegungsmatrix;
                col, Spaltenanzahl der Zerlegungsmatrix;
                row, Zeilenanzahl der Zerlegungsmatrix.
  Rueckgabe Indexvektor idx.
------------------------------------------------------------------------------*/
{
	INT i,j,col,row;
	INT *id;

	col=S_M_LI(dcm);
	row=S_M_HI(dcm);
	for (i=(INT)0;i<col;idx[i++]=(INT)0);
	for (j=(INT)0,id=idx;j<col;j++)
		for (i=(INT)0;i<row;i++)
			if (!nullp(S_M_IJ(dcm,i,j)))
			{

				*id++ = (INT)i;
				break;
			}
	return OK;
} /* _ber_idx_dec */

/*******************************************************************************
*
* Datei HOMP.C
*   Version vom 29.09.1989
*
*
* Zeile Funktion
*
*       Funktion zur Ueberpruefung der Darstellungen
*       --------------------------------------------
* 30    INT homtestp(INT **darmat,INT n,INT ddim,INT pz)
*
*******************************************************************************/

/*----------------------------------------------------------------------------*/
static INT homtestp(darmat,n,ddim,pz) TL_BYTE **darmat; 
	INT n,ddim,pz;
/*------------------------------------------------------------------------------
  ueberprueft, ob die im Buch von Carmichael auf Seite 175  (Aufgabe 2)
  angegebenen Relationen erfuellt sind, d.h. eine treue Darstellung von Sn
  erzeugt wird. Dabei wird ueber GF(pz) gerechnet. Es handelt sich insgesamt
  um 4+[n/2] Relationen.
  Indexnummern: 1.  t^2 = I,
                2.  s^n = I,
                3.  (st)^(n-1L) = I,
                4.  (ts^(-1L)ts)^3 = I,
                3+j.  (ts^(-j)ts^j)^2 = I fuer j=2L,...,[n/2].
  Variablen:  darmat, darstellende Matrizen einer Transposition
                      und eines n-Zykels;
              n,  Sn;
              ddim, Dimension der darstellenden Matrizen;
              pz, Primzahl.
  Rueckgabewerte: (INT)0,  falls alle Relationen erfuellt sind;
              index,  falls Relation mit Indexnummer index nicht
                      erfuellt ist;
                -14L,  falls n kleiner 1 ist;
                // -15L,  falls n groesser MAXN ist;
                -22L,  falls Pointer auf darmat NULL ist;
                -24L,  falls pz keine Primzahl ist;
                -25L,  falls pz kleiner 1 ist;
                -26L,  falls pz groesser n ist;
                -28L,  falls ddim kleiner 0 ist;
                -29L,  falls ddim groesser MAXDM ist;
              (INT)-109,  falls nicht genuegend Speicher zu Verfuegung war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *invzyk,*mat,*mat_eins;
	INT k,i,j,az;

	if (ddim<(INT)0) return(DDmLt_null);
	else if (ddim==(INT)0) return((INT)0);
	else if (ddim>MAXDM) return(DDmGMx);
	else if (darmat==NULL) return (DrtNul);
	else if (n<=(INT)0) return(NLe_null);
	/* else if (n>MAXN) return(NGtMax); */
	else if (pz<=(INT)0) return(PrmLe_null);
	else if (pz>n) return(PrmGtN);
	for (i=(INT)0;PZ[i]<=n && PZ[i]<=pz;i++);
	if (pz!=PZ[i-1]) return(NoPrm);
	/*
  Kein Eingabefehler, also koennen wir loslegen:
*/
	mat=(TL_BYTE *)TL_calloc((int)ddim*(int)ddim*3,sizeof(TL_BYTE));
	if (!mat)
		return no_memory();
	mat_eins= &mat[(INT)ddim*(INT)ddim];
	invzyk= &mat_eins[(INT)ddim*(INT)ddim];
	matcopy(mat,darmat[0],ddim);
	if (rmatmulp(mat,darmat[0],ddim,pz)<(INT)0)
	{
		SYM_free(mat);
		return no_memory();
	}
	if (!idmat(mat,ddim)) /* t^2 = 1 ? */
	{
		SYM_free(mat);
		return(1L);
	}
	matcopy(mat,darmat[1],ddim);
	rmatmulp(mat,darmat[0],ddim,pz);
	matcopy(mat_eins,mat,ddim);
	az=1L;
	while (2L*az <= (n-1L))
	{
		matcopy(invzyk,mat_eins,ddim);
		rmatmulp(mat_eins,invzyk,ddim,pz);
		az *= 2L;
	}
	for (i=az+2L; i<= n; i++)
		rmatmulp(mat_eins,mat,ddim,pz);
	if (!idmat(mat_eins,ddim))  /* (s * t) ^ (n-1L) =1 ? */
	{
		SYM_free(mat);
		return(3L);
	}
	matcopy(mat,darmat[1],ddim);
	az=1L;
	while (2L*az <= n-1L)
	{
		matcopy(mat_eins,mat,ddim);
		rmatmulp(mat,mat_eins,ddim,pz);
		az*=2L;
	}
	for (i=az+2L;i<=n;++i)
		rmatmulp(mat,darmat[1],ddim,pz);
	matcopy(invzyk,mat,ddim); /* s^(-1L) = s^(n-1L) */
	rmatmulp(mat,darmat[1],ddim,pz);
	if (!idmat(mat,ddim)) /* s^n = 1 ? */
	{
		SYM_free(mat);
		return(2L);
	}
	matcopy(mat,darmat[0],ddim);
	rmatmulp(mat,invzyk,ddim,pz);
	rmatmulp(mat,darmat[0],ddim,pz);
	rmatmulp(mat,darmat[1],ddim,pz);
	matcopy(mat_eins,mat,ddim);
	rmatmulp(mat_eins,mat,ddim,pz);
	rmatmulp(mat_eins,mat,ddim,pz);
	if (!idmat(mat_eins,ddim))  /* (t * s^(-1L) * t * s) ^ 3 = 1 ? */
	{
		SYM_free(mat);
		return(4L);
	}
	k=n/2L;
	for (j=2L; j<=k; j++)
	{
		rmatmulp(mat,darmat[1],ddim,pz);  /* in mat ist noch t*s^1*t*s */
		lmatmulp(darmat[0],mat,ddim,pz);
		lmatmulp(invzyk,mat,ddim,pz);
		lmatmulp(darmat[0],mat,ddim,pz);
		matcopy(mat_eins,mat,ddim);
		rmatmulp(mat_eins,mat,ddim,pz);
		if (!idmat(mat_eins,ddim))  /* (t*s^(-j)*t*s^j)^2 = 1 fuer j=2L,...k ? */
		{
			SYM_free(mat);
			return(j+3L);
		}
	}
	SYM_free(mat);
	return((INT)0);
} /*homtestp */
/*******************************************************************************
*
* Datei MODMAT.C
*   Version vom 11.10.1989
*
*
* Zeile Funktion
*
*       Funktionen fuer Matrixoperationen
*       ---------------------------------
* 39    INT matcopy(TL_BYTE *ziel,TL_BYTE *quelle,INT dim)
* 59    INT rmatmulp(TL_BYTE *lmat,TL_BYTE *rmat,INT pdim,INT pz)
* 102   INT lmatmulp(TL_BYTE *lmat,TL_BYTE *rmat,INT pdim,INT pz)
* 152   INT idmat(TL_BYTE *z,INT dm)
*
*******************************************************************************/
/*
  Uebliche Headerfiles...
*/



/*----------------------------------------------------------------------------*/
static INT rmatmulp(lmat,rmat,pdim,pz) INT pz, pdim;
TL_BYTE *lmat, *rmat;
/*-----------------------------------------------------------------------------
  multipliziert die (pdim x pdim)-Matrix lmat von rechts mit der
  (pdim x pdim)-Matrix rmat. Dabei werden Multiplikationen und Additionen
  modulo pz ausgefuehrt.
  Variablen:  lmat, Matrix;
              rmat, Matrix;
              pdim, Dimension der Matrizen;
              pz, Primzahl.
  Rueckgabe Ergebnismatrix lmat.
  Ruechgabewerte: (INT)0,  falls alles geklappt hat;
              (INT)-109,  falls der noetige Speicher nicht vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT h,i,j,k,o_eins,o_zwei;
	TL_BYTE *aa,*bb,*hilf,*aa_eins;

	hilf=(TL_BYTE *)TL_calloc((int)pdim,sizeof(TL_BYTE));
	if (hilf == NULL) return no_memory();
	aa_eins=lmat;
	for (i=(INT)0 ; i < pdim; ++i)
	{
		for (j=(INT)0 ; j < pdim; ++j)
		{
			h=(INT)0;
			bb= &rmat[(INT)j];
			aa=aa_eins;
			for (k=(INT)0; k<pdim; k++,bb+=(INT)pdim)
			{
				if ((o_eins= *aa++)==(INT)0) continue;
				if ((o_zwei= *bb)==(INT)0) continue;
				h=TL_ADP(h,TL_MULP(o_eins,o_zwei,pz),pz);
			}
			hilf[j]=h;
		}
		for (j=(INT)0; j < pdim; ++j) *aa_eins++=hilf[j];
	}
	SYM_free(hilf);
	return((INT)0);
} /* rmatmulp */


/*----------------------------------------------------------------------------*/
static INT lmatmulp(lmat,rmat,pdim,pz) TL_BYTE *lmat, *rmat;
	INT pz, pdim;
/*------------------------------------------------------------------------------
  multipliziert die (pdim x pdim)-Matrix rmat von links mit der
  (pdim x pdim)-Matrix lmat. Dabei werden Multiplikationen und Additionen
  modulo pz ausgefuehrt.
  Variablen:  lmat, Matrix;
              rmat, Matrix;
              pdim, Dimension der Matrizen;
              pz, Primzahl.
  Rueckgabe Ergebnismatrix rmat.
  Rueckgabewerte: (INT)0,  falls kein Fehler aufgetreten ist;
              (INT)-109,  falls kein Speicher zu Verfuegung stand.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT h,i,j,k;
	TL_BYTE *hilf,*_a,*_b;
	INT o_eins,o_zwei;

	hilf=(TL_BYTE *)TL_calloc((int)pdim,sizeof(TL_BYTE));
	if (hilf==NULL) no_memory();

	for (j=(INT)0 ;j < pdim; ++j)
	{
		_a=lmat;
		for (i=(INT)0 ; i < pdim; ++i)
		{
			_b=rmat+j;
			h=(INT)0;
			for (k=(INT)0 ; k < pdim; k++,_b+=pdim)
			{
				if ((o_eins= *_a++)==(INT)0) continue;
				if ((o_zwei= *_b)==(INT)0) continue;
				h=TL_ADP(h,TL_MULP(o_eins,o_zwei,pz),pz);
			}
			hilf[i]=h;
		}
		_b=rmat+j;
		for (i=(INT)0; i < pdim; ++i)
		{
			*_b=hilf[(INT)i];
			_b+=pdim;
		}
	}
	SYM_free(hilf);
	return((INT)0);
} /* lmatmulp */


/*----------------------------------------------------------------------------*/
static INT idmat(z,dm) TL_BYTE *z;
	INT dm;
/*------------------------------------------------------------------------------
  testet die (dm x dm)-Matrix z, ob sie die Einheitsmatrix ist.
  Variablen:  z,  Matrix;
              dm, Dimension der Matrix.
  Rueckgabewerte: TRUE, falls z Einheitsmatrix ist;
                 FALSE, falls z keine Einheitsmatrix ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,o_eins;
	TL_BYTE *zz;

	zz=z;
	for (i=(INT)0; i<dm; ++i)
		for (j=(INT)0; j<dm; ++j)
		{
			o_eins= *zz++;
			if (i==j)
			{
				if (o_eins!=1L) return(FALSE);
			}
			else
			{
				if (o_eins) return(FALSE);
			}
		}
	return(TRUE);
} /* idmat */
/*******************************************************************************
*
* Datei MODULDG.C
*   Version vom 29.09.1989
*
*
* Zeile Funktion
*
*       Funktionen zur Berechnung der gew./p-mod. irred. Darst.
*       -------------------------------------------------------
* 75    INT moddreimat(TL_BYTE *hz,INT pz,INT mode)
* 126   INT _modgauss(TL_BYTE *hz,INT pz,INT i,INT mode)
*
*       Funktionen zur Berechnung der gew. irred. Darstellungen
*       -------------------------------------------------------
* 160   INT r_modgauss(TL_BYTE *hz,INT pz)
* 181   INT ganzgaussmod(TL_BYTE *bz,TL_BYTE *hz)
*
*       Funktionen zur Berechnung der p-mod. irred. Darstellungen
*       ---------------------------------------------------------
* 269   INT modmat(TL_BYTE *hz,INT pr)
* 290   INT modgauss(TL_BYTE *hz,TL_BYTE *v,INT pr)
* 363   p_rel(TL_BYTE *hz,TL_BYTE *v,INT pr)
* 392   zykel(INT *liste,INT *zyk)
* 439   INT p_writemat(INT *hz,INT *v,INT *lambda,INT pr,INT *perm,INT **darmat,
*             INT prang)
* 521   INT TL_darmod(TL_BYTE *hz,TL_BYTE *lambda,INT pr,TL_BYTE *perm,TL_BYTE **darmat)
*
*       Hauptfunktion
*       -------------
* 563   INT darmod(TL_BYTE *lambda,INT dim,TL_BYTE *bz,INT pz,INT *gzl,TL_BYTE *perm,
*             TL_BYTE **darmat)
*
*******************************************************************************/
/*
  Uebliche Headerfiles,...
*/

/* #define IND(a,b,c) (INT)((INT)(a)*(INT)(c)+(INT)(b)) */


/*
  und globale Variablen.
*/
static INT _dm;
static INT _dm_zwei;
static INT _dm_drei;


/*******************************************************************************
*
* Funktionen fuer die Bestimmung gew./p-mod. irred. Darstellungen...
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT moddreimat(hz,pz,mode) INT mode,pz; 
TL_BYTE *hz;
/*------------------------------------------------------------------------------
  mode=1:
    bringt die erste (_dm x _dm)-Teilmatrix von hz mit Hilfe des Gaussalgorith-
    mus ueber GF(pz) auf obere Dreiecksform mit 1 oder 0 auf der Hauptdiago-
    nalen,
  mode=3:
    wendet auf das (_dm x 3_dm)-Gleichungsschema hz den Gaussalgorithmus ueber
    GF(pz) an, bis die erste der drei (_dm x _dm)-Teilmatrizen eine obere Drei-
    ecksmatrix mit 1 oder 0 auf der Hauptdiagonalen ist.
    (Simultanes Loesen von 2_dm linearen Gleichungssystemen.)
  Variablen:  hz, Matrix mit Basis und Darstellungen;
              pz, Primzahl;
              mode, s.o.
  Rueckgabe Matrix hz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  *_hz,*jz,*z_eins,*z_zwei,qu,mu;
	INT i,j,k,mdm;

	mdm=mode*_dm;
	for (i=(INT)0,_hz=hz;i<_dm;i++,_hz += (_dm_drei+1L))
	{
		for (k=i+1L,jz=_hz+_dm_drei;!*_hz && k<_dm;k++,jz += _dm_drei)
			if (*jz)
				for (j=mdm,z_eins=jz,z_zwei=_hz;j>i;j--)
				{
					mu= *z_zwei;
					*z_zwei++ = *z_eins;
					*z_eins++ = mu;
				}
		if (*_hz)
		{
			if ((qu= *_hz)!=1L)
				for (j=mdm,z_eins=_hz;j>i;j--,z_eins++)
				{
					if (*z_eins)
						*z_eins=TL_DIVP(*z_eins,qu,pz);
				}
			if (i<_dm-1L)
				for (k=i+1L,jz=_hz+_dm_drei;k<_dm;k++,jz += _dm_drei)
					if ((qu= *jz)!=(INT)0)
						for (j=mdm,z_eins=jz,z_zwei=_hz;j>i;j--,z_eins++,z_zwei++)
							if (*z_zwei)
							{
								/*
                mu=(-1L)*(TL_MULP(qu,*z_zwei,pz));
                *z_eins=TL_ADP(*z_eins,mu,pz);
*/

								*z_eins = TL_MOD((-1 * qu * *z_zwei) + *z_eins, pz);

							}
		}
	}
	return OK;
} /* moddreimat */


/*----------------------------------------------------------------------------*/
static INT _modgauss(hz,pz,i,mode) INT pz,i,mode; 
TL_BYTE *hz;
/*------------------------------------------------------------------------------
  wird benoetigt fuer die Funktionen modgauss und r_modgauss.
  Variablen:  hz, Matrix mit Basis und Darstellungen;
              pz, Primzahl;
              i, Anfangswert der Schleife;
              mode, =1L, fuer modgauss,
                    =3L, fuer r_modgauss;
  Rueckgabe Matrix hz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE mu,qu,*_hz,*jz,*z_eins,*z_zwei;
	INT j,k,mdm;

	mdm=mode*_dm;
	for (j=i-1L,_hz= &hz[IND(i,i,_dm_drei)],jz=_hz-_dm_drei;j>=(INT)0;j--,jz -= _dm_drei)
		if ((qu= *jz)!=(TL_BYTE)0)
			for (k=mdm,z_eins=_hz,z_zwei=jz;k>i;k--,z_zwei++,z_eins++)
				if (*z_eins)
				{
					mu=(TL_BYTE) (-1L)*(TL_MULP(qu,*z_eins,pz));
					*z_zwei= TL_ADP(*z_zwei,mu,pz);
				}
	return OK;
} /* _modgauss */


/*******************************************************************************
*
* Funktionen zur Bestimmung der gew. irred. Darstellungen...
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT r_modgauss(hz,pz) TL_BYTE *hz; 
	INT pz;
/*------------------------------------------------------------------------------
  wendet den Gaussalgorithmus ueber GF(pz) auf das (_dm x 3_dm)-Koeffizienten-
  schema an, wobei die erste (_dm x _dm)-Teilmatrix eine obere Dreiecksmatrix
  mit 0 oder 1 auf der Hauptdiagonalen sein muss.
  (Simultanes Loesen von 2_dm linearen Gleichungssystemen.)
  Variablen:  hz, Matrix mit Basis und Darstellungen;
              pz, Primzahl.
  Rueckgabe Matrix hz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_hz;
	INT i;

	for (i=_dm-1L,_hz= &hz[IND(_dm-1L,_dm-1L,_dm_drei)];i>(INT)0;i--,_hz -= (_dm_drei+1L))
		if (*_hz)
			_modgauss(hz,pz,i,3L);
	return OK;
} /* r_modgauss */


/*----------------------------------------------------------------------------*/
static INT ganzgaussmod(bz,hz) TL_BYTE *hz, *bz;
/*------------------------------------------------------------------------------
  loest simultan die in dem (_dm x 3_dm)-Koeffizientenschema bz kodierten 2_dm
  linearen Gleichungssysteme. Am Ende stehen die Loesungen fuer die gew.
  irred. Darstellungen in den letzten 2_dm Spalten von bz.
  Koennen keine ganzz. Loesungen errechnet werden, wird die Berechnung abge-
  brochen.
  Variablen:  bz, Matrix aus alkonmat;
              hz, Matrix wie bz.
  Rueckgabe Matrix hz mit Basis und Matrizen der gewoehnlichen Darstellungen.
  Rueckgabewerte: (INT)0, falls alles geglueckt ist;
                -27L, falls keine ganzzahlige Loesung existiert.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  *_hz,*_bz,*z_eins,*z_zwei,*z_drei;
	INT i,j,k,pz,su;
	INT  il,cl;
	INT chance;

	pz=(INT)29;
	chance=TRUE;
	while (chance)
	{
		/*
  Interpretation von bz ueber GF(pz) und Uebergabe an hz
*/
		for (il=(INT)_dm*(INT)_dm_drei,_hz=hz,_bz=bz;il>(INT)0;il--,_hz++,_bz++)
			if (*_bz)
				*_hz = (TL_BYTE) TL_MOD(*_bz,pz);
			else
				*_hz = (TL_BYTE) 0;
		/*
  Anwendung des Gaussalgorithmus ueber GF(pz)
*/
		moddreimat(hz,pz,3L);
		r_modgauss(hz,pz);
		/*
  Rekonstruktion der ganzzahligen Loesungen
*/
		for (i=(INT)0,_hz=hz+_dm;i<_dm;i++,_hz += _dm_drei)
			for (j=_dm,z_eins=_hz;j<_dm_drei;j++,z_eins++)
				if (*z_eins)
				{
					if ((*z_eins + *z_eins) > pz)
						*z_eins -= pz;
				}
		/*
  Verifikation der Loesungen: Die Koeffizientenmatrix der Gleichungssysteme
  (die ersten _dm Spalten von bz) wird mit der Loesungsmatrix (die letzten
  2_dm Spalten von hz) multipliziert. Jeder Eintrag der Produktmatrix wird
  unmittelbar nach seiner Berechnung mit dem entsprechenden Eintrag in den
  letzten 2_dm Spalten von bz verglichen.
  cl gibt die Anzahl der Uebereinstimmungen an.
*/
		for(i=(INT)0,cl=(INT)0,_bz=bz;i<_dm;i++,_bz += _dm_drei)
			for (j=_dm,z_eins=_bz+_dm,_hz=hz+_dm;j<_dm_drei;j++,z_eins++,_hz++)
			{
				for (k=(INT)0,su=(INT)0,z_zwei=_hz,z_drei=_bz;k<_dm;k++,z_drei++,z_zwei +=_dm_drei)
				{
					if (! *z_zwei) continue;
					if (! *z_drei) continue;
					su += (*z_zwei * *z_drei);
				}
				if (su == *z_eins)
					++cl;
			}
		if (cl==((INT)_dm_zwei*(INT)_dm))
			chance=FALSE;
		else
		{
			if (pz==(INT)211)
			{
				error("internal error: MO_50");
				return(NoSolu);
			}
			pz=(INT)211;
			chance=TRUE;
		}
	}
	return((INT)0);
} /* ganzgaussmod */


/*******************************************************************************
*
* Funktionen zur Bestimmung der p-mod. irred. Darstellungen...
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT modmat(hz,pr) TL_BYTE *hz; 
	INT pr;
/*------------------------------------------------------------------------------
  transformiert die (_dm x 3_dm)-Matrix hz nach (hz mod pr).
  Variablen:  hz, Matrix mit Basis und Darstellungen;
              pr, Primzahl.
  Rueckgabe Matrix hz gerechnet modulo pr.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_hz;
	INT  il;

	for (il=(INT)_dm*(INT)_dm_drei,_hz=hz;il>(INT)0;il--,_hz++)
		if (*_hz)
			*_hz=(TL_BYTE)TL_MOD(*_hz,pr);
		else
			*_hz=(TL_BYTE)0;
	return OK;
} /* modmat */


/*----------------------------------------------------------------------------*/
static INT modgauss(hz,v,pr) TL_BYTE *hz, *v; 
	INT pr;
/*------------------------------------------------------------------------------
  berechnet mit Hilfe des Gaussalgorithmus ueber GF(pr) die Dimension der
  p-mod. irred. Darstellung. Der Gaussalgorithmus wird dabei auf die erste
  (_dm x _dm)-Teilmatrix von hz angewendet, wobei diese eine obere Dreiecks-
  matrix mit 0 oder 1 auf der Hauptdiagonalen sein muss.
  Variablen:  hz, Matrix mit Basis und Darstellungen;
              pr, Primzahl.
  Rueckgabe Nummernvektor v der abhaengigen Spalten in hz.
  Rueckgabewerte: prang, Dimension der p-modular irreduziblen Darstellung.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *_hz,*z_eins,*z_zwei,*_v,qu,su;
	INT z,i,j,k,prang;

	prang=(INT)0;
	for (i=(INT)0;i<_dm;v[i++]=(TL_BYTE)0);

	for (i=_dm-1L,_hz= &hz[IND(_dm-1L,_dm-1L,_dm_drei)],_v= &v[_dm-1];i>(INT)0;
	    i--,_hz -= (_dm_drei+1L),_v--)
		if (*_hz)
		{
			if ((qu = *_hz)!=(TL_BYTE)1)
				for (k=i,z_eins=_hz;k<_dm;k++,z_eins++)
					if (*z_eins)
						*z_eins= TL_DIVP(*z_eins,qu,pr);
			_modgauss(hz,pr,i,1L);
		}
		else
		{
			*_v = (TL_BYTE)i+1;
			++prang;
		}
	if (hz[0]!=(TL_BYTE)1)
	{
		if ((qu=hz[0])==(TL_BYTE)0)
		{
			v[0]=(TL_BYTE)1;
			++prang;
		}
		else
			for (j=(INT)0,_hz=hz;j<_dm;j++,_hz++)
				if (*_hz)
					*_hz = TL_DIVP(*_hz,qu,pr);
	}
	prang=_dm-prang;


	for (i=_dm-2L,_v= &v[_dm-2],_hz= &hz[IND(_dm-2L,_dm-1L,_dm_drei)];i>=(INT)0;
	    i--,_v--,_hz -= (_dm_drei+1L))
		if (*_v == (TL_BYTE) i+1)
		{
			for (j=i+1L,su=(TL_BYTE)0,z_eins=_hz;!su && j<_dm;j++,z_eins++)
				if (*z_eins)
					su=(TL_BYTE)j;
			if (su)
			{
				v[su]=(TL_BYTE)0;
				z_eins= &hz[IND(i,su,_dm_drei)];
				z_zwei= &hz[IND(su,su,_dm_drei)];
				for (j=su;j<_dm;++j)
				{
					z= *z_eins;
					*z_eins++ = *z_zwei;
					*z_zwei++ = z;
				}
			}
			_modgauss(hz,pr,su,1L);
		}
	return(prang);
} /* modgauss */


/*----------------------------------------------------------------------------*/
static INT p_rel(hz,v,pr) TL_BYTE *hz, *v; 
	INT pr;
/*------------------------------------------------------------------------------
  Simultane Ermittlung und Anwendung der p-Relationen.
  (Lineare Algebra!)
  Variablen:  v, Nummern der abhaengigen Spalten in hz;
              pr, Primzahl;
              hz, Matrix mit Basis und Darstellungen.
  Rueckgabe Matrix hz.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  *_v,*_hz,*z_eins,*z_zwei,*z_drei,*z_vier,mu,su;
	INT i,j,k;

	for (i=(INT)0,_v=v,_hz=hz;i<_dm;i++,_v++,_hz += _dm_drei)
		if (*_v == i+1L)
			for (j=(INT)0,z_eins=_hz+_dm,z_zwei=hz+_dm;j<_dm_zwei;j++,z_eins++,z_zwei++)
				if ((mu= *z_eins)!=(TL_BYTE)0)
					for (k=(INT)0,z_drei=hz+i,z_vier=z_zwei;k<=i-1L;k++,z_drei += _dm_drei,z_vier +=
					    _dm_drei)
						if (*z_drei != (TL_BYTE)0)
						{
							su= TL_MULP(mu,*z_drei,pr);
							*z_vier=TL_ADP(su,*z_vier,pr);
						}
	return OK;
} /* p_rel */


/*----------------------------------------------------------------------------*/
static INT zykel(liste,zyk) TL_BYTE *liste, *zyk;
/*------------------------------------------------------------------------------
  berechnet die Zykelschreibweise einer Permutation liste aus ihrer Listen-
  schreibweise. Dabei steht eine negative Zahl immer als Ende des Zykels.
  Variablen:  liste, Pointer auf die Permutation in Listenschreibweise.
  Rueckgabe Permutation zyk in Zykelschreibweise.
  Rueckgabewerte: (INT)0, falls kein Fehler aufgetreten ist;
              (INT)-109, falls nicht genuegend Speicher vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *z;
	INT merk,merk_eins,i,j,n;
	INT fertig;
	TL_BYTE *besucht;

	for (n=(INT)0;liste[n];n++);
	if ((besucht=(TL_BYTE *)TL_calloc((int)n,sizeof(TL_BYTE)))==NULL)
		return no_memory();
	z=zyk;
	i=(INT)0;
	*z++ =(TL_BYTE)(merk=merk_eins=1L);
	fertig=FALSE;
	do
	{
		besucht[i]=(TL_BYTE)1;
		if (liste[i]==merk_eins)
		{
			z--;
			*z++ = -merk;
			for (j=(INT)0;j<n && besucht[j] && liste[j];j++);
			i=j;
			if (i>=n || !liste[i])
				fertig=TRUE;
			else
				*z++ =(TL_BYTE)(merk=merk_eins=i+1L);
		}
		else
		{
			merk= *z++ =(TL_BYTE)liste[i];
			i=liste[i]-1L;
		}
	} while (!fertig && i<n && liste[i]);
	return((INT)0);
} /* zykel */


/*----------------------------------------------------------------------------*/
static INT p_writemat(hz,v,lambda,pr,perm,darmat,prang)
	INT prang,pr; 
	TL_BYTE *hz,*v,*lambda, *perm, **darmat;
/*------------------------------------------------------------------------------
  schreibt die in darmod berechneten Matrizen unter Beruecksichtigung der
  pr-Relationen auf stream. In darmat stehen die Darstellungsmatrizen, falls
  sie mindestens eine Spalte und eine Zeile enthalten.
  Rueckgabe Darstellungsmatrizen darmat.
  Rueckgabewerte: (INT)0, falls alles ohne Fehler durchgefuehrt wurde;
              (INT)-109, falls nicht genuegend Speicherplatz vorhanden ist.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *dar,*_hz,*vi,*vj,*z_eins,*z_zwei,*z;
	INT i,j,n;
	INT q,klam;

	if (prang)
	{
		for (n=(INT)0;perm[n];n++);
		n++;
#ifdef UNDEF
		if (stream && prang<85L)
		{
			if ((z=(TL_BYTE *)TL_calloc((int)n,sizeof(TL_BYTE)))==NULL)
				return no_memory();
			if (zykel(perm,z))
				return no_memory();
		}
#endif
		for (q=(INT)0,_hz=hz+_dm;q<2L;q++,_hz += _dm)
		{
			for (i=(INT)0,vi=v,z_eins=_hz,dar=darmat[q];i<_dm;i++,vi++,z_eins += _dm_drei)
				if (! *vi)
					for (j=(INT)0,vj=v,z_zwei=z_eins;j<_dm;j++,vj++,z_zwei++)
						if (! *vj)
							*dar++ = *z_zwei;
#ifdef UNDEF
			if (stream && prang<85L)
			{

				fprintf(stream,"D(%d/(%d",pr,lambda[0]);
				for (i=1L;i<n && lambda[i];++i)
					fprintf(stream,",%d",lambda[i]);
				switch ((int)q)
				{
				case (INT)0:
					fprintf(stream,")/(1 2L))");
					break;
				case 1L:
					fprintf(stream,")/(");
					klam=1L;
					for (i=(INT)0;i<n && z[i];i++)
					{
						if (!klam)
						{
							fprintf(stream,"(");
							klam = 1-klam;
						}
						if (z[i]>(TL_BYTE)0)
							fprintf(stream,"%d ",z[i]);
						else
						{
							fprintf(stream,"%d)",-z[i]);
							klam=1-klam;
						}
					}
					fprintf(stream,")");
					break;
				}
				fprintf(stream,"\n");
				for (i=prang*prang,dar=darmat[q];i>(INT)0;i--,dar++)
				{
					if (!(i%prang)) fprintf(stream,"\n");
					fprintf(stream,"%3d",*dar);
				}
				fprintf(stream,"\n\n\n");
				SYM_free(z);
			}
#endif
		}
	}
	return((INT)0);
}  /* p_writemat */

/*----------------------------------------------------------------------------*/
static INT TL_darmod(hz,lambda,pr,perm,darmat)
	TL_BYTE *perm,*hz, *lambda, **darmat;
	INT pr;
/*------------------------------------------------------------------------------
  berechnet die pr-modular irreduziblen Darstellungsmatrizen fuer zwei Permu-
  tationen. Dazu muessen die Spalten der ersten (_dm x _dm)-Teilmatrix von hz
  die zugrunde gelegte Basis kodieren sowie die naechsten beiden (_dm x _dm)-
  Teilmatrizen von hz die  zugehoerigen gewoehnlichen darstellenden Matrizen
  sein. (_dm ist die gewoehnliche Dimension der Darstellung.)
  Variablen:  hz, Matrix mit der zugrunde gelegten Basis und die zugehoerigen
                  gewoehnlichen Darstellungsmatrizen;
              lambda, Partition;
              pr, Primzahl;
              perm, Permutation.
  Rueckgabe Matrizen darmat der p-modular irreduziblen Darstellungen.
  Rueckgabewerte: prang, Dimension der p-modular irreduziblen Darstellungen;
                  (INT)-109, falls nicht genuegend Speicher vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *v;
	INT prang;

	if ((v=(TL_BYTE *)TL_calloc((int)_dm,sizeof(TL_BYTE)))==NULL)
		return no_memory();
	modmat(hz,pr);
	moddreimat(hz,pr,1L);
	prang=modgauss(hz,v,pr);
	p_rel(hz,v,pr);
	if (p_writemat(hz,v,lambda,pr,perm,darmat,prang))
		return no_memory();
	SYM_free(v);
	return(prang);
} /* TL_darmod */


/*******************************************************************************
*
* Hauptfunktion zur Berechnung der p-mod. irred. Darstellungen...
*
*******************************************************************************/


/*----------------------------------------------------------------------------*/
static INT darmod(lambda,dim,bz,pz,gzl,perm,darmat)
	TL_BYTE *lambda, *bz, *perm, **darmat; 
	INT dim,pz,*gzl;
/*------------------------------------------------------------------------------
  koordiniert die Berechnung der gew. irred. Darstellungen mit der Berechnung
  der p-mod. irred.
  Variablen:  lambda, Partition;
              dim, Dimension der gewoehnlichen Darstellungen;
              bz, Koeffizientenschema aus alkonmat;
              pz, Primzahl,fuer welche die p-mod. Darstellungsmatrizen be-
                  rechnet werden;
              gzl, #(INT)0, d.h. berechne zuerst die gew. irred. Darstellungen,
                   =(INT)0, d.h. gew. irred. Darstellungen existieren schon;
              perm, Permutation, fuer die die Darstellungen berechnet werden.
  Rueckgabe Matrizen darmat der p-modular irreduziblen Darstellungen.
  Rueckgabewerte: prang, Dimension der Darstellung;
                    (INT)-10, falls Pointer auf lambda NULL ist;
                    -11L, falls lambda keinen Eintrag hat;
                    -12L, falls lambda einen Eintrag kleiner 0 hat;
                    -13L, falls lambda keine eigentliche Partition ist;
                    // -15L, falls n MAXN uebersteigt;
                    -18L, falls dim groesser MAXDM ist;
                    -19L, falls Pointer auf bz NULL ist;
                    -21L, falls dim kleiner 1 ist;
                    -22L, falls Pointer auf darmat NULL ist;
                    -23L, falls Pointer auf gzl NULL ist;
                    -24L, falls pz keine Primzahl ist;
                    -25L, falls pz kleiner 1 ist;
                    -26L, falls pz groesser n ist;
                    -27L, falls keine ganzzahlige Loesung bei der Berechnung
                         der gewoehnlichen Darstellungen existiert;
                    (INT)-30, falls Pointer auf perm NULL ist;
                    -31L, falls ein Element von perm kleiner 1 ist;
                    -32L, falls ein Element von perm groesser n ist;
                    -33L, falls Laenge von perm groesser n ist;
                  (INT)-109, falls nicht genuegend Speicher zu Verfuegung steht.
  Bemerkungen:
    gzl veraendert sich selbststaendig. Wird darmod mit einem von alkonmat
    neuberechneten bz aufgerufen, muss gzl einen von 0 verschiedenen Wert
    haben. Sind die ganzzahligen Loesungen der gewoenlichen  Darstellungen
    berechnet, so ist gzl=(INT)0, und man kann durch nochmaliges Aufrufen von
    darmod mit diesem die Berechnungen der gew. Darstellungen ueberspringen.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE  *_hz,*z_eins,*z_zwei,*z_drei;
	INT prang,n,j,i;
	TL_BYTE  *hz;  /* dim x 3dim */
	INT  il;


	/*
  Abfangen moeglicher Uebergabefehler...
*/
	if (lambda==NULL)
		return(LmbNul);
	else if (!lambda[0])
		return(LmbEmp);
	for (j=(INT)0,n=(INT)0;lambda[j];j++)
		if (lambda[j]<(TL_BYTE)0)
			return(LmbLt_null);
		else
			n+=lambda[j];
	for (j=1L;lambda[j];j++)
		if (lambda[j]>lambda[j-1])
			return(LmbNRg);
	
	if (darmat==NULL)
		return(DrtNul);
	else if (gzl==NULL)
		return(GzlNul);
	else if (bz==NULL)
		return(BzNul);
	else if (dim<=(INT)0)
		return(DimLe_null);
	else if (dim>MAXDM)
		return(DmGtMx);
	else if (pz<=(INT)0)
		return(PrmLe_null);
	else if (pz>n)
		return(PrmGtN);
	else if (pz)
	{
		for (j=(INT)0;PZ[j]<=n && PZ[j]<=pz;j++);
		if (pz!=PZ[j-1])
			return(NoPrm);
	}
	else if (perm==NULL)
		return(PerNul);



	for (j=(INT)0;j<n;j++)
		if (perm[j]<=(INT)0)
			return(PerLe_null);
		else if (perm[j]>n)
			return(PerGtN);

	/*
  Auf geht's...
*/
	_dm=dim;
	_dm_zwei=2L*_dm;
	_dm_drei=3L*_dm;
	if ((hz=(TL_BYTE *)TL_calloc((int)_dm_drei*(int)_dm,sizeof(TL_BYTE)))==NULL)
		return no_memory();
	for (il=(INT)_dm*(INT)_dm_drei,z_eins=hz,z_zwei=bz;il>(INT)0;il--)
		*z_eins++ = *z_zwei++;
	if (*gzl)
	{
		if (lambda[2])
			for (i=(INT)0,_hz=hz+1,z_zwei=hz+_dm_drei;i<_dm-1L;i++,_hz += (_dm_drei+1L),z_zwei += (_dm_drei+1L))
			{
				for (j=i+1L,z_eins=_hz,z_drei=z_zwei;j<_dm;j++,z_eins++,z_drei += _dm_drei)
					*z_drei = *z_eins;
				for (j=i+1L,z_eins=_hz+_dm,z_drei=z_zwei+_dm;j<_dm;j++,z_eins++,z_drei += _dm_drei)
					*z_drei = *z_eins;
			}
		for (il=(INT)_dm*(INT)_dm_drei,z_eins=bz,z_zwei=hz;il>(INT)0;il--)
			*z_eins++ = *z_zwei++;
		/*
  Berechnung der gewoehnlichen irreduziblen Darstellung mit Hilfe
  einer modularen Arithmetik.
*/
		*gzl=ganzgaussmod(bz,hz);
		for (i=(INT)0,z_eins=hz,z_zwei=bz;i<_dm;++i)
		{
			for (j=(INT)0;j<_dm;++j)
				*z_eins++ = *z_zwei++;
			for (j=_dm;j<_dm_drei;++j)
				*z_zwei++ = *z_eins++;
		}
	}
	if (!(*gzl))
		/*
  Berechnung der modular irred. Darstellg.
*/
		prang=TL_darmod(hz,lambda,pz,perm,darmat);
	else
		prang= *gzl;
	SYM_free(hz);
	return(prang);
} /* darmod */


INT dimension_mod(part,prim,res) OP part,prim; OP res;
/* AK 200294 */
{
	/* AK 240194 for a single dimension */
	TL_BYTE  *lambda;
	TL_BYTE *slambda;
	INT erg = OK;
	INT i,dm,omaxdim;
	INT ak_j;
	TL_BYTE *bz;
	INT res_dim;
	INT n,p;
	OP w;
	CTO(INTEGER,"dimension_mod",prim);
	CTO(PARTITION,"dimension_mod",part);
	C2R(part,prim,"dimension_mod",res);

	if (S_I_I(prim) < (INT)0)
	{
		fprintf(stderr,"number = %ld\n",S_I_I(prim));
		error("dimension_mod: prime number (2. parameter) is negativ");
		goto endr_ende;
	}
	if (S_I_I(prim) == (INT)0) /* ordinary dimension */
	{
		erg +=  dimension(part,res);
		goto s2r;
	}
	if (not primep(prim))
	{
		fprintf(stderr,"number = %ld\n",S_I_I(prim));
		error("dimension_mod: prime number (2. parameter) is not prime");
		goto endr_ende;
	}

	if (equal_parts(part,prim))
	{
		erg += m_i_i((INT)0,res);
		goto s2r;
	}

	omaxdim=MAXDM;
	w = callocobject();
	weight(part,w);
	n = S_I_I(w);
	p = S_I_I(prim);
	lambda = (TL_BYTE *)TL_calloc((int)n, sizeof(TL_BYTE));
	if (lambda == NULL)
	{
		MAXDM=omaxdim;
		erg += ERROR;
		goto endr_ende;
	}

	for (i=(INT)0;i<n;i++) lambda[i]=(INT)0;

	for (i=S_PA_LI(part)-(INT)1,ak_j=(INT)0; i>=(INT)0;i--,ak_j++)
		lambda[ak_j]=S_PA_II(part,i);

	dimension(part,w);
	MAXDM= S_I_I(w);
	freeall(w);
	if (MAXDM<(INT)0)
	{
		MAXDM=omaxdim;
		SYM_free(lambda);
		error("dimension_mod:internal error");

		erg =MAXDM;
		goto endr_ende;
	}

	slambda=(TL_BYTE *)TL_calloc((int)(n+1),sizeof(TL_BYTE));
	if (slambda == NULL)
	{
		MAXDM=omaxdim;
		SYM_free(lambda);
		erg += ERROR; 
		goto endr_ende;
	}
	bz=(TL_BYTE *)TL_calloc((int)MAXDM*(int)MAXDM,sizeof(TL_BYTE));
	if (bz == NULL)
	{
		MAXDM=omaxdim;
		SYM_free(slambda);
		SYM_free(lambda);
		erg += ERROR; 
		goto endr_ende;
	}
	_assoziiere(lambda,slambda,n);
	if ((dm=k_alkonmat(slambda,bz,p))<(INT)0)
	{
		res_dim=dm;
		MAXDM=omaxdim;
		goto dme;
	}
	if ((res_dim=k_dimmod(bz,MAXDM,p))<(INT)0)
	{
		MAXDM=omaxdim;
		SYM_free(bz);
		SYM_free(slambda);
		SYM_free(lambda);
		goto endr_ende;

	}
dme:
	SYM_free(bz);
	SYM_free(slambda);
	SYM_free(lambda);
	m_i_i(res_dim,res);
	j_zyk((INT)-15,(INT)0,NULL,NULL); /* AK 020294 */

s2r:
	S2R(part,prim,"dimension_mod",res);
	ENDR("dimension_mod");
}


INT schnitt_mat(part,prim,res) OP part,prim; OP res;
/* input: partition part
   prime number: p
   output integer matrix modulo p, whose rang = degree of mod irrep */
/* AK 200294 */ /* AK 070498 V2.0 */
{
	TL_BYTE  *lambda;
	TL_BYTE *slambda;
	INT i,j,dm,omaxdim;
	INT ak_j;
	TL_BYTE *bz;
	INT res_dim;
	INT n,p;
	OP w;
	INT erg = OK;

	CE3(part,prim,res,schnitt_mat);

	if (equal_parts(part,prim))
		return m_i_i((INT)0,res);

	C2R(part,prim,"schnitt_mat",res);
	omaxdim=MAXDM;
	w = callocobject();
	weight(part,w);
	n = S_I_I(w);
	p = S_I_I(prim);
	lambda = (TL_BYTE *)TL_calloc((int)n, sizeof(TL_BYTE));
	if (lambda == NULL)
	{
		MAXDM=omaxdim;
		return no_memory();
	}

	for (i=(INT)0;i<n;i++) lambda[i]=(INT)0;

	for (i=S_PA_LI(part)-(INT)1,ak_j=(INT)0; i>=(INT)0;i--,ak_j++)
		lambda[ak_j]=S_PA_II(part,i);

	dimension(part,w);
	MAXDM= S_I_I(w);
	freeall(w);
	/* _dimension(lambda,n); */
	if (MAXDM<(INT)0)
	{
		MAXDM=omaxdim;
		SYM_free(lambda);
		error("dimension_mod:internal error");
		return(MAXDM);
	}

	slambda=(TL_BYTE *)TL_calloc((int)(n+1),sizeof(TL_BYTE));
	if (slambda == NULL)
	{
		MAXDM=omaxdim;
		SYM_free(lambda);
		return no_memory();
	}
	bz=(TL_BYTE *)TL_calloc((int)MAXDM*(int)MAXDM,sizeof(TL_BYTE));
	if (bz == NULL)
	{
		MAXDM=omaxdim;
		SYM_free(slambda);
		SYM_free(lambda);
		return no_memory();
	}
	_assoziiere(lambda,slambda,n);
	if ((dm=k_alkonmat(slambda,bz,p))<(INT)0)
	{
		res_dim=dm;
		MAXDM=omaxdim;
		goto dme;
	}

	erg += m_ilih_m(MAXDM,MAXDM,res);
	for (i=0;i<MAXDM;i++)
		for (j=0;j<MAXDM;j++)
			M_I_I((INT)(bz[i*MAXDM+j]),S_M_IJ(res,i,j));
dme:
	SYM_free(bz);
	SYM_free(slambda);
	SYM_free(lambda);
	S2R(part,prim,"schnitt_mat",res);

	j_zyk((INT)-15,(INT)0,NULL,NULL); /* AK 020294 */
	ENDR("schnitt_mat");
}

/*----------------------------------------------------------------------------*/
static INT _assoziiere(lambda,slambda,n) TL_BYTE *lambda, *slambda; 
	INT n;
/*------------------------------------------------------------------------------
  konjugiert die eigentliche Partition lambda mit Ergebnis slambda.
  Variablen:  lambda, eigentliche Partition.
  Rueckgabe slambda.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT i,j,llen;

	for (i=(INT)0;i<=n;slambda[i++]=(TL_BYTE)0);
	for (llen=(INT)0;llen<n && lambda[llen];llen++);
	for (i=(INT)0;i<lambda[0];++i)
	{
		for (j=(INT)0;j<llen && lambda[j]>=i+1;++j);
		if ((j<n) && (lambda[j] < i+1))
			slambda[i]=(TL_BYTE)j;
		else
			slambda[i]=(TL_BYTE)llen;
	}
	return OK;
} /* _assoziiere */

/*----------------------------------------------------------------------------*/
static INT matcopy(ziel,quelle,dim) TL_BYTE *ziel,*quelle,dim;
/*------------------------------------------------------------------------------
  kopiert die (dim x dim)-Matrix quelle auf die (dim x dim)-Matrix ziel.
  Variablen:  quelle, Matrix;
              dim,  Dimension beider Matrizen.
  Rueckgabe Matrix ziel, Kopie von Matrix quelle.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	INT  i;
	TL_BYTE *bb,*aa;

	bb=ziel;
	aa=quelle;
	for (i=(INT)dim*(INT)dim; i>(INT)0 ; i--)
		*bb++= *aa++;
	return OK;
} /* matcopy */


/*----------------------------------------------------------------------------*/
static INT fak(x) INT x;
/*------------------------------------------------------------------------------
  berechnet x!.
  Variable: x,  natuerliche Zahl.
  Rueckgabewert:  x!.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	if (x<=1L)
		return(1L);
	else
		return (x*fak(x-1L));
} /*fak*/

/*----------------------------------------------------------------------------*/
static INT nexgitt(y,lambda,mtc) TL_BYTE *lambda, *y; 
	INT *mtc;
/*------------------------------------------------------------------------------
  berechnet aus Tableau y und Partition lambda das naechste Tableau y.
  Variablen:  y, Tableau;
              lambda, Partition.
  Rueckgabe neues Tableau y, falls ein neues existiert (mtc = TRUE).
  Rueckgabewerte: (INT)0, falls kein Fehler aufgetreten ist;
              (INT)-109,  falls kein Speicherplatz vorhanden war.
------------------------------------------------------------------------------*/
/* TL 0790 */ /* AK 210891 V1.3 */
{
	TL_BYTE *hilf;
	static TL_BYTE *h=NULL;
	static int _nn = 0;
	INT  m,i,j,l,merke;
	INT durch;

	if (*mtc == 280194L) {
		if (h != NULL) SYM_free(h); 
		h = NULL;
		return OK;
	}
	if (_nn != _n)
	{
		if (h != NULL) SYM_free(h);
		h = NULL;
	}

	if (h == NULL)
	{
		h=(TL_BYTE *)TL_calloc(_n+_n,sizeof(TL_BYTE));
		_nn = _n;
	}

	if (!h)
		return no_memory();

	hilf=h+_n;
	memcpy(h,y,_n * sizeof(TL_BYTE));

	if (!(*mtc))
		for (i=(INT)0,j=(INT)0;lambda[i];++i)
		{
			for (l=j;l<j+lambda[i];h[l++]=(TL_BYTE)i);
			j += lambda[i];
		}
	else
	{
		memset(hilf,0,_n * sizeof(TL_BYTE));
		i=_n-(INT)1;
		durch=FALSE;
		do
		{
			++ hilf[m=h[i]];
			if (m>(l=h[i-1]))
			{
				if ((lambda[l]-lambda[m])>
				    (hilf[l]-hilf[m]+(TL_BYTE)1))
				{
					durch=TRUE;
					merke=l;
					j=merke+(TL_BYTE)1;
					while ((hilf[j]==(TL_BYTE)0) ||
					    ((lambda[l]-lambda[j])<
					    (hilf[l]-hilf[j]+(TL_BYTE)2)))
						++j;
					h[i-1]=j;
					--hilf[j];
					++hilf[merke];
					for (l=i;l<_n;++l)
						if (j<_n)
						{
							for (j=(TL_BYTE)0;!hilf[j];++j);
							h[l]=j;
							--hilf[j];
						}
				}
			}
			--i;
			if (i == (INT)0)
				*mtc=FALSE;
		} while (!durch && *mtc);
	}
	memcpy(y,h,_n * sizeof(TL_BYTE) );
	return (INT)0;
}  /*nexgitt*/


#endif /* DGTRUE */
