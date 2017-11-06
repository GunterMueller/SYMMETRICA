#include "def.h"
#include "macro.h"

#ifdef DGTRUE  /* Darstellungen */

static INT homtest();
static INT tf_idmat();
static INT imult();
/*
static INT nw_nexperm();
static INT test_nw_nexperm();
static INT nw_nexpart();
static INT test_nw_nexpart();
*/

/*** maximale Laenge von Permutationen ***/
#define TFNMAX 200

#define FIRST_ST 0
#define NEXT_ST 1


/* Zugriff auf das Element (i,j) in der oberen D-Matrix m
   der Dimension fa; Diagonale ist 1! */
#define ODM(m,fa,i,j) m[((long)fa-1L)*(long)(i)-((long)(i)\
                        *((long)(i)+1L))/2L+(j)-1L]
/* Zugriff auf das Element (i,j) in der quadratischen Matrix
   m der Dimension fa */
#define MAT(v,fa,i,j) v[(long)fa*(long)(i)+(long)(j)]


/* imult.c */
static INT imult(a,b,d) OP a,b,d;
/* TF 210989 */
/* multipliziert zwei INTEGER matrizen */
/* AK 191289 V1.1 */ /* AK 210891 V1.3 */
{
	OP c;

	/* sonderfaelle bei gleichen variablennamen */
	if	(a == d)
		{ c =callocobject(); copy(a,c); imult(c,b,d); freeall(c);
		return(OK); }
	if	(b == d)
		{ c =callocobject(); copy(b,c); imult(a,c,d); freeall(c);
		return(OK); }

	/*freigabe des speichers belegt durch d */
	freeself(d);
	/*falls beides leere objecte => d auch leer  */
	if (emptyp(a) || emptyp(b)) return(OK);

	if (nullp(a)) return(m_i_i(0L,d));
	if (nullp(b)) return(m_i_i(0L,d));
	if (einsp(b)) return(copy(a,d));
	if (einsp(a)) return(copy(b,d));

	if (S_O_K(a)==MATRIX && S_O_K(b)==MATRIX)
		return(mult_imatrix_imatrix(a,b,d));
	else
	{
		printobjectkind(a); printobjectkind(b);
		error("kann ich nicht multiplizieren");
		return(ERROR);
	}
}

/**************************************/
/*** Spezialfall: zwei INT-Matrizen ***/
/**************************************/
INT mult_imatrix_imatrix(a,b,c) OP a,b,c;
/* TF 210989 */
	{
#ifdef MATRIXTRUE
	INT i,j,k,ha,lb,la;
	OP ll, height,pi,pj;
	INT zi,aiki,bkji; /* zwischen ergebnis bei matrix-multiplikation */

	if (S_M_LI(a) != S_M_HI(b))
		{
		error("matrizen koennen nicht multipliziert werden");
		return(ERROR);
		};

	ll=callocobject(); 
	height=callocobject(); 
	COPY_INTEGER(S_M_H(a),height); ha=S_M_HI(a);
	COPY_INTEGER(S_M_L(b),ll); lb=S_M_LI(b); la=S_M_LI(a);

	b_lh_m(ll,height,c);

	for (i=0L;i<ha;i++) 	/* ueber zeilen der linken Matrix */
	{
		for (j=0L;j<lb;j++) 	/* ueber spalten der rechten Matrix */
		{
			zi=0L;
			pi=S_M_IJ(a,i,0L); /* Zeiger auf 1. Objekt in Zeile i */
			pj=S_M_IJ(b,0L,j); /* Zeiger auf erstes Objekt in Spalte j */
			for (k=0L; k<la; k++,pi++,pj+=lb)
			{
				if ((aiki=S_I_I(pi))==0L) continue;
				if ((bkji=S_I_I(pj))==0L) continue;
				zi += aiki*bkji;
			};
			m_i_i(zi,S_M_IJ(c,i,j));
		}
	}
	return(OK);
#endif 
	}


INT test_ndg()
/* zum testen von ndg() und homtest() */
/* TF 211189 */
/* AK 191289 V1.1 */ /* AK 210891 V1.3 */
{
  INT i,n;
  OP  part = callocobject();
  OP  trans = callocobject();
  OP  nzyk = callocobject();
  OP  transmat = callocobject();
  OP  nzykmat = callocobject();
  OP  ob_n    = callocobject();

  scan(PARTITION,part);
  n=0L;
  for (i=0L; i<S_PA_LI(part); i++) n+=S_PA_II(part,i);
  m_i_i(n,ob_n);

  b_ks_p(VECTOR,callocobject(),trans);
  b_ks_p(VECTOR,callocobject(),nzyk);
  m_il_v(n,s_p_s(trans));
  m_il_v(n,s_p_s(nzyk));

  m_i_i(2L,s_p_i(trans,0L));
  m_i_i(1L,s_p_i(trans,1L));
  for (i=2L; i < n; i++) m_i_i(i+1L,s_p_i(trans,i));
  println(trans); ndg(part,trans,transmat); println(transmat);

  for (i=0L; i < n; i++) m_i_i(i+2L,s_p_i(nzyk,i));
  m_i_i(1L,s_p_i(nzyk,n-1L));
  println(nzyk); ndg(part,nzyk,nzykmat); println(nzykmat);

  homtest(transmat,nzykmat,ob_n,stdout);
  freeall(ob_n);freeall(transmat);freeall(nzykmat);freeall(nzyk);
  freeall(part);freeall(trans);
  return(OK);
}

/***************************************************************************
*
*  HOMTEST fuer SYMLIB (T. Fuerbringer, August 1989)
*
*  Die Prozedur "homtest" ueberprueft, ob die im Buch von Carmichael
*  auf Seite 175  (Aufgabe 2) angegebenen Relationen erfuellt sind, d.h.
*  eine treue Darstellung von Sn erzeugt wird. Es handelt sich insgesamt
*  um 4+[n/2] Relationen. 
*
*  Mit imult linken.
*
***************************************************************************/


/***************************************************************************
*
* Prozedur:
*   INT tf_idmat(z)
*
* Beschreibung:
*   "tf_idmat" testet, ob die Matrix z die Einheitsmatrix ist.
*
* Rueckgabe:
*   1,falls erfuellt oder 0, falls nicht erfuellt.
*
***************************************************************************/
static INT tf_idmat(z) OP z;
/* AK 191289 V1.1 */ /* TF 011289 */ /* AK 210891 V1.3 */
{
  INT i,j,o1,dm;

  dm=S_M_LI(z);
  for (i=0L; i<dm; ++i)
  for (j=0L; j<dm; ++j)
  {
    o1=S_M_IJI(z,i,j);
    if (i==j)
    {
      if (o1!=1L) return(FALSE);
    }
    else
    {
      if (o1) return(TRUE);
    }
  }
  return(FALSE);
}

/***************************************************************************
*
* Prozedur:
*   INT homtest(trans,nzyk,n,logfp)
*
* Beschreibung:
*   Parameter sind
*     trans  : darstellende Matrix einer Transposition
*     nzyk   : darstellende Matrix eines n-Zyklus
*     n      : Sn,
*     logfp  : log-File fuer Zwischenmeldungen (oder NULL)
*
* Rueckgabe:
*   Index einer nicht erfuellten Relationen, oder
*   0L, falls alle Relationen erfuellt;
*   Indexreihenfolge:
*   1.   t^2 = I
*   2.   s^n = I
*   3.   (st)^(n-1) = I
*   4.   (ts^(-1)ts)^3 = I
*   3+j. (ts^(-j)ts^j)^2 = I  fuer j=2,...,[n/2]
*
***************************************************************************/
static INT homtest(trans,nzyk,n,logfp) OP trans,nzyk,n; FILE *logfp;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  OP  invzyk = callocobject(),
      mat    = callocobject(),
      mat1   = callocobject();
  INT dim,k,i,j,az,ni;

  dim=S_M_LI(trans);
  ni=S_I_I(n);
  m_ilih_m(dim,dim,invzyk);
  m_ilih_m(dim,dim,mat1);

  if (logfp) fprintf(logfp,"%ld Tests:\n",ni/2L+3L);
  copy(trans,mat);
  imult(mat,trans,mat1);
  if (!tf_idmat(mat1))
  {
    if (logfp) fprintf(logfp,"Test 1 failed\n");
    freeall(mat); freeall(mat1); freeall(invzyk);
    return(1L);
  }
  if (logfp)
  {
    fprintf(logfp,"Test 1 ok"); fflush(logfp);
  }

  copy(nzyk,mat);       /*  (s * t) ** (n-1) = 1 ? */
  imult(mat,trans,mat);
  copy(mat,mat1);
  az=1L;
  while (2L*az <= (ni-1L))
  {
    copy(mat1,invzyk);
    imult(mat1,invzyk,mat1);
    az *= 2L;
  }
  for (i=az+2L; i<= ni; i++)
    imult(mat1,mat,mat1);
  if (!tf_idmat(mat1))
  {
    if (logfp) fprintf(logfp,"Test 3 failed\n");
    freeall(mat); freeall(mat1); freeall(invzyk);
    return(3L);
  }
  if (logfp)
  {
    fprintf(logfp,", 3 ok");
    fflush(logfp);
  }

  copy(nzyk,mat);
  az=1L;
  while (2L*az <= ni-1L)
  {
    copy(mat,mat1);
    imult(mat,mat1,mat);
    az*=2L;
  }
  for (i=az+2L;i<=ni ;++i)   /* s**n=1 ? */
    imult(mat,nzyk,mat);
  copy(mat,invzyk); /*  s**-1 = s**(n-1) */
  imult(mat,nzyk,mat);
  if (!tf_idmat(mat))
  {
    if (logfp) { fprintf(logfp,"Test 2 failed\n"); fflush(logfp); }
    freeall(mat); freeall(mat1); freeall(invzyk);
    return(2L);
  }
  if (logfp) { fprintf(logfp,", 2 ok"); fflush(logfp); }

  copy(trans,mat);      /*  (t*(s**-1)*t*s)**3 = 1 ? */
  imult(mat,invzyk,mat);
  imult(mat,trans,mat);
  imult(mat,nzyk,mat);
  copy(mat,mat1);
  imult(mat1,mat,mat1);
  imult(mat1,mat,mat1);
  if (!tf_idmat(mat1))
  {
    if (logfp) fprintf(logfp,"Test 4 failed \n");
    freeall(mat); freeall(mat1); freeall(invzyk);
    return(4L);
  }
  if (logfp) { fprintf(logfp,", 4 ok"); fflush(logfp); }

  k=ni/2L;   /* ( t * (s**-j) * t * (s**j) ) **2 = 1 fuer j=2,...k ? */

  for (j=2L; j<=k; j++)
  {
    imult(mat,nzyk,mat); /* mat ist noch ts^-1 ts */
    imult(trans,mat,mat);
    imult(invzyk,mat,mat);
    imult(trans,mat,mat);
    copy(mat,mat1);
    imult(mat1,mat,mat1);
    if (!tf_idmat(mat1))
    {
      if (logfp) fprintf(logfp,"Test %ld failed\n",j+3L);
      freeall(mat); freeall(mat1); freeall(invzyk);
      return(j+3L);
    }
    if (logfp) { fprintf(logfp,", %ld ok",j+3L); fflush(logfp); }
  }
  if (logfp) fprintf(logfp,"\n");
  freeall(mat); freeall(mat1); freeall(invzyk);
  return(0L);
}

/*********************************************************************
*
*   Permutationen nach Nijenhuis/Wilf
*   T. Fuerbringer
*
*********************************************************************/
#ifdef UNDEF
/*********************************************************************
  r=nw_nexperm(m,n,a,sig)
    INT  m	: 0 = erste Permutation berechnen
		  1 = folgende Permutation berechnen
    OP	 n	: Laenge der Permutation
    OP	 a	: Permutation
    OP	 sig: Vorzeichen der berechneten Permutation
    INT  r	: 0 = dies war die letzte Permuation
		  1 = noch weitere Permutationen berechenbar
*********************************************************************/
static INT nw_nexperm(m,n,a,sig) INT m; OP n,a,sig;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
	static INT sgn,ni;
	INT	 i,j,ai=0,s,d=0;

	if (!m)
	{
		ni=S_I_I(n); if (ni<1L) return(0L);
		b_ks_p(VECTOR,callocobject(),a);
		m_il_v(ni,s_p_s(a));
		for (i=0L; i<ni; i++) m_i_i(i+1L,S_P_I(a,i));
		sgn=1L;
		if (sig) m_i_i(1L,sig);
		return((INT)(ni>1L));
	}
	if (sig) m_i_i(-sgn,sig);
	if (sgn<0L)
	{
		sgn=1L;
		s=0L;
		for (i=1L; i<ni; i++)
		{
			ai=S_P_II(a,i);
			d=0L;
			for (j=0L; j<i; j++) if (S_P_II(a,j) > ai) d++;
			s+=d;
			if (s % 2L && d < i)
			{
				for (d=0L; S_P_II(a,d) >= ai; d++);
				for (j=d+1L; j<i; j++)
					if (S_P_II(a,j) < ai && 
					  S_P_II(a,j) > S_P_II(a,d)) d=j;
				break;
			}
			else if ((s%2L)==0L && d>0L)
			{
				for (d=0L; S_P_II(a,d)<=ai; d++);
				for (j=d+1L; j<i; j++)
					if (S_P_II(a,j)>ai && 
					  S_P_II(a,j)<S_P_II(a,d)) d=j;
				break;
			}
		}
		m_i_i(S_P_II(a,d),S_P_I(a,i));
		m_i_i(ai,S_P_I(a,d));
	}
	else
	{
		sgn= -1L;
		s=S_P_II(a,0L);
		m_i_i(S_P_II(a,1L),S_P_I(a,0L));
		m_i_i(s,S_P_I(a,1L));
	}
	if (S_P_II(a,ni-1L)!=1L || S_P_II(a,0L)!=(ni%2L+2L)) return(1L);
	if (ni<=3L) return(0L);
	j=ni-3L;
	for (i=0L; i<j; i++) if (S_P_II(a,i+1L)!=S_P_II(a,i)+1L) return(1L);
	return(0L);
}

#ifdef TEST

static INT test_nw_nexperm()
/* AK 191289 V1.1 */ /* TF 011289 */ /* AK 210891 V1.3 */
{
	OP a = callocobject();
	OP n = callocobject();
	OP s = callocobject();
	INT e,anz;

	scan(INTEGER,n);
	e=nw_nexperm(0L,n,a,s);
	println(a); anz=1L;
	while (e)
	{
		e=nw_nexperm(1L,n,a,s);
		println(a); anz++;
	}
	printf("%ld\n",anz);
}

#endif


/***************************************************************************
*
* Berechnung der Partitionen zu einem n > 0 nach Nijenhuis/Wilf
* T. Fuerbringer 
*
***************************************************************************/

/***************************************************************************
*
* Prozedur:
*   INT nw_nexpart(mode,n,part)
*
* Beschreibung:
*   mode=0:
*     "nexpart" berechnet erste Partition (n).
*     Rueckgabe erfolgt in part.
*
*     Statische Variable:
*       r[0]: Anzahl verschiedener Ziffern in r[1...];
*       r[i] (i>0): Eine Ziffer der Partition;
*       m[i] (i>0): Vielfachheit von r[i];
*   mode<>0:
*     Die nach Hijenhuis/Wilf auf part folgende Partition wird
*     berechnet.
*
* Rueckgabe:
*   0: part ist letzte Partition, sonst !=0.
*
***************************************************************************/
static INT nw_nexpart(mode,n,part) INT mode; OP n,part;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  INT i,j,d,s,sum,f;
  static INT ni,r[50],m[50];

  d=r[0];
  if (mode!=0L)
  {
    sum=(r[d]==1L)? m[d--]+1L : 1L;
    f=r[d]-1L;
    if (m[d]!=1L)
      m[d++]--;
    r[d]=f;
    m[d]=(sum/f)+1L;
    s= sum % f;
    if (s>0L)
    {
      r[++d]=s;
      m[d]=1L;
    }
    r[0]=d;

    f=0L;
    for (i=1L; i<=d; f+=m[i++]);

    m_il_v(f,S_PA_S(part));
    f=0L;
    for (i=1L; i<=d; i++)
      for (j=m[i]; j>0L; j--) m_i_i(r[i],S_PA_I(part,f++));
    return((INT)(m[d]!=ni));
  }
  else
  {
    r[0]=m[1]=1L;
    ni=r[1]=s_i_i(n);
    b_ks_pa(VECTOR,callocobject(),part);
    m_il_v(1L,s_pa_s(part));
    M_I_I(ni,S_PA_I(part,0L));
    return((INT)(ni!=1L));
  }
}

#ifdef TEST

static INT test_nw_nexpart()
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  OP  part = callocobject();
  OP  n    = callocobject();
  INT e;

  scan(INTEGER,n);
  e=nw_nexpart(0L,n,part);
  println(part);
  while(e!=0L)
  {
    e=nw_nexpart(1L,n,part);
    println(part);
  }
}

#endif

#endif
/************************ 1.TEIL *************************************
* bestehend aus PERMFIND.C, NEXTST.C, NATDG.C
*********************************************************************/



/*** Zeiger auf Bereich fuer Standardtableaux ***/
static int *stptr = (int *)0L;

/*** momentan gueltige Dimension ***/
static int stdim = 0;

/*** Zugriff auf x-tes Tableau ***/
#define STAB(x) (stptr+x*(n+1))

/********************************************************************
*
* PERMFIND.C
*
* Prozeduren zur Berechnung von Vertikal- und Horizontalpermutationen
* und deren Vorzeichen.
*
********************************************************************/

/********************************************************************
*
* Prozedur:
*    void ltmult(pi,t1,t2)
*
* Beschreibung:
*    ltmult multipliziert die Permutation pi von links mit
*    der Transposition (t1 t2).
*
********************************************************************/
static void ltmult( pi , t1 , t2 ) int *pi; int t1; int t2;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  register int flag = 0; /* flag protokolliert die Anzahl
                            getauschter Elemente */

  while (flag<2)
  {
    if (*++pi == t1)
    { *pi=t2; flag++; }
    else if (*pi == t2)
    { *pi=t1; flag++; }
  }
}

/********************************************************************
*
* Prozedur:
*    int sign(pi)
*
* Beschreibung:
*    sign berechnet das Vorzeichen der Permutation pi.
*
* Rueckgabe:
*    Vorzeichen
*
********************************************************************/
static int sign(pi ) int *pi;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int k,j,i,s,anz;
  int d[TFNMAX];

  /*** d protokolliert, auf welche Elemente in pi schon
       zugegriffen wurde ***/

  for (i=1; i<=pi[0]; d[i++]=0);

  /*** Vorzeichen berechnen ***/

  s=1; /* sign := 1 */
  k=1; /* Elementindex, ab dem gesucht wird */
  anz=0; /* Anzahl erledigter Elemente */
  while (anz < pi[0])
  {
    i=k++;
    while (d[i]) i++; /* suche unberuehrtes Element */
    j=i;
    d[i]=1;
    anz++;
    while (pi[i]!=j) /* durchlaufe zu i gehoerenden Zykel */
    {
      s= -s; /* Vorzeichen dreht sich staendig um */
      i=pi[i];
      d[i]=1; /* alle Zykelelemente als erledigt kennzeichnen */
      anz++;
      if (k==i) k++; /* vor i muss nicht mehr gesucht werden */
    }
  }
  return(s);
}

/********************************************************************
*
* Prozedur:
*    int find_pq(alpha,t1,t2,q,ps)
*
* Beschreibung:
*    Seien t1 und t2 Tableaux zum Rahmen [alpha].
*    find_pq sucht q aus V(t1), ps aus H(q*t1) mit t2= ps*q t1.
*
* Rueckgabe:
*    0 gefunden, -1 sonst.
*
********************************************************************/
static int find_pq(alpha,t1,t2,q,ps) int *alpha,*t1,*t2; int *q; int *ps;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  register int ss,zs,ks,n,i;
  int tloc[TFNMAX];
  int d[TFNMAX],z,k,ks_pos,k_pos;
  int zpos[TFNMAX],spos[TFNMAX];

  n=tloc[0]=ps[0]=q[0]=t1[0];

  /*** erstmal vorbesetzen ***/

  for (i=1; i<=n; i++)
  {
    d[i]=0; /* Zugriffsprotokoll auf Elemente in t2 */
    q[i]=i; /* q := id */
    tloc[i]=t1[i]; /* tloc:=t1, da in t1 selbst keine Elemente
                      getauscht werden duerfen */
  }

  /*** bestimme Zeilen- und Spaltenpositionen 
       der Elemente im Tableau tloc ***/

  i=1; /* Laufindex durchs Tableau tloc */
  for (zs=1; zs<=alpha[0]; zs++) /* Zeilen */
  for (ss=1; ss<=alpha[zs]; ss++) /* Spalten */
  {
    ks=tloc[i++];
    zpos[ks]=zs;
    spos[ks]=ss;
  }

  /*** durchlaufe nun t2 v.l.n.r. und v.o.n.u.: Position (zs,ss) ***/

  ks_pos=1; /* Position des Laufelements im Vektor t2 */
  k_pos=0; /* Position von Element k in tloc */
  for (zs=1; zs<=alpha[0]; zs++)
  {
    for (ss=1; ss<=alpha[zs]; ss++)
    {
      ks=t2[ks_pos++]; /* ks ist das Element in Zeile zs, Spalte ss */
      z=zpos[ks]; /* z ist Zeilenposition von ks in tloc */
      if (z != zs) /* z!=zs, dann muss man in tloc vertauschen */
      {
        k=tloc[k_pos+spos[ks]]; /* Vertauschungselement in tloc an
                            Position (zs,s), wobei s die Spalten-
                            position von ks in tloc ist */
        if (d[k]) return(-1); /* Fehler: Element wurde schon mal
                                 getauscht: kein q gefunden */
        ltmult(q,k,ks); /* sonst: q = (k ks)q */
        ltmult(tloc,k,ks); /* und tloc ebenso */
        zpos[ks]=zs; /* auch die Zeilenpositionen sind neu */
        zpos[k]=z;
      }
      d[ks]=1; /* ks erledigt */
    }
    k_pos+=alpha[zs]; /* k_pos zeigt jetzt auf 1. Element in der
                         naechsten Zeile von tloc */
  }

  /*** Nun muss ggf. noch ps bestimmt werden. Das ist aber fuer
       dieses Programm nicht notwendig. Fuer andere Anwendungen
       sind die Kommentarklammern zu entfernen ***/

  /* for (i=1; i<=n; i++) ps[tloc[i]]=t2[i]; */

  return(0);
}

/********************************************************************
*
* NEXTST.C
*
* Prozeduren zur Berechnung der Standardtableaux
* (geordnet nach der letzten Ziffer)
*
********************************************************************/

/********************************************************************
*
* Prozedur:
*    void set_LL_min(st,talpha,alpha)
*
* Beschreibung:
*    set_LL_min belegt das Tableau zum Teilrahmen talpha von alpha
*    so vor, dass es im Teilrahmen LL-kleinstes ist. st ist das zu
*    alpha gehoerende Tableau.
*
********************************************************************/
static void set_LL_min(st,talpha,alpha) int *st; int *talpha; int *alpha;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  register int k,s,z,*pos;

  /*** k ist die einzusetzende Ziffer, d.h k=1,2,... ***/

  k=1;

  /*** Durchlaufe nun den Teilrahmen spalten- und zeilenweise ***/

  for (s=1; s<=talpha[1]; s++)
  {
    pos=st+s; /* "absolute" (Vektor-)Position in st */
    for (z=1; talpha[z] >= s; z++)
    {
      *pos=k++;
      pos+=alpha[z]; /* eine Zeile weiter */
      if (z >= talpha[0]) break;
    }
  }
}

/********************************************************************
*
* Prozedur:
*    int nextst(mode,alpha,st)
*
* Beschreibung:
*
*    mode=FIRST_ST:
*      nextst berechnet das LL-kleinste Standardtableau.
*   
*    mode=NEXT_ST:
*      nextst berechnet das auf st folgende Tableau in der LLS.
*
* Rueckgabe:
*    0 zeigt an, dass st schon letztes war, sonst 1.
*
********************************************************************/
static int nextst(mode,alpha,st) int mode; int *alpha; int *st;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int talpha[TFNMAX];
  register int n,s,z,zz,pos,i,j,k;

  /*** LL-kleinstes ***/

  if (mode==FIRST_ST)
  {
    st[0]=0; /* n bestimmen */
    for (i=1; i<=alpha[0]; i++) st[0]+=alpha[i];
    set_LL_min(st,alpha,alpha);
    return(1);
  }
  else

  /*** LL-naechstes ***/

  {

  /*** berechne kleinstes Teiltableau, so dass man die
       groesste Ziffer darin nach unten schieben kann ***/

    n=st[0];
    talpha[0]=1;
    talpha[1]=1; /* Teiltableau talpha mit [1] vorbesetzen */
    for (i=2; i<=n; i++) /* durchlaufe alle Ziffern 2,...,n */
    {

  /*** bestimme Zeile z und "absolute" Position k von i in st ***/

      z=1; /* (1,1) ist immer mit 1 besetzt -> uebergehen */
      s=2;
      k=1;
      while (st[++k]!=i)
      {
        if (s++>=alpha[z])
        {
          s=1;
          z++;
        }
      }

  /*** erweitere Rahmen talpha um Kaestchen fuer i ***/

      if (z > talpha[0])
      { 
        talpha[0]++;
        talpha[z]=0;
      }
      talpha[z]++;

  /*** pruefe nun in talpha, ob man i nach unten bringen kann ***/

      if (talpha[0] > 1 && talpha[1] > 1) /* talpha gross genug ? */
      {
        pos=k+alpha[z]-s;
        for (zz=z+1; zz <= talpha[0]; zz++) 
          /* die Zeilen unter z testen */
        {
          pos+=talpha[zz]; /* pos zeigt auf Endziffer in Zeile zz */
          if (zz==talpha[0]) /* Ist zz die letzte Zeile ... */
            j=1;
          else if (talpha[zz] > talpha[zz+1])
                             /* oder steht nichts darunter, ... */
            j=1; /* so ist tauschen mglich */
          else
            j=0;  /* sonst nicht */
          if (j && st[pos] < i) /* Tauschen erlaubt, falls Endziffer
                                   kleiner als Ziffer i ist */
          {
            s=st[pos]; /* tausche i mit st[pos] */
            st[pos]=i;
            st[k]=s;
            if (--talpha[zz]==0) talpha[0]--;
              /* Teiltableau ohne Ziffer i neu sortieren */
            if (talpha[0] > 1 && talpha[1] > 1)
              set_LL_min(st,talpha,alpha);
            return(1); /* fertig */
          }
          pos+=alpha[zz]-talpha[zz];
            /* sonst naechste Zeile testen */
        }
      }
    }

  /*** alle Ziffern getestet und keine Tauschmoeglichkeit gefunden:
       letztes Tableau erreicht ***/

    return(0);
  }
}

/********************************************************************
*
* NATDG.C (ohne getdim)
*
* Prozeduren zur Berechnung der natuerlichen Darstellung der Sn
* Version mit Pufferung aller Standardtableaux.
*
********************************************************************/

/********************************************************************
*
* Prozedur:
*    int allst(alpha,n)
*
* Beschreibung:
*    allst berechnet alle Standardtableaux, belegt entsprechend
*    viel Speicher und liefert Zeiger auf den Speicherbereich.
*    Der Bereich muss mit free(Bereich) freigegeben werden.
*
* Rueckgabe:
*    0 (OK) oder <>0 (FEHLER)
********************************************************************/
static int allst(alpha,n) int *alpha; int n;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int i,e,*b;
  int st[TFNMAX];

  if (stptr)
  {
    SYM_free(stptr);
    stptr=(int *)0L;
  }
  stptr=b=(int *)SYM_malloc(sizeof(int)*(long)(n+1)*(long)stdim);
  if (!b) return(-1);
  e=nextst(FIRST_ST,alpha,st);
  while (e)
  {
    for (i=0; i<=n; *b++=st[i++]);
    e=nextst(NEXT_ST,alpha,st);
  }
  return(0);
}

/********************************************************************
*
* Prozedur:
*    int koeff(alpha,pi,stk,stj)
*
* Beschreibung:
*    koeff berechnet den Koeffizienten der Permutation pi
*    im Gruppenalgebra-Element e(kj) := e(k)*pi(kj).
*    Dabei beziehen sich k und j auf die zugehoerigen LLS-geordneten
*    Standardtableaux stk und stj, wobei stj = pi(kj)stk. 
*
* Rueckgabe:
*    Koeffizient -1,0,1
*
********************************************************************/
static int koeff(alpha,pi,stk,stj) int *alpha; int *pi; int *stk; int *stj;
/* AK 191289 V1.1 */
/* TF 011289 */
{
  int i,ps[TFNMAX],q[TFNMAX];
  int t2[TFNMAX];

  /*** berechne Tableau t2 = pi * st[j] ***/

  t2[0]=pi[0];
  for (i=1; i<=pi[0]; i++)
    t2[i]=pi[stj[i]];

  /*** finde nun Permutationen q,ps ***/

  if (find_pq(alpha,stk,t2,q,ps)<0) return(0);

  /*** der Koeffizient ist dann sgn(q) ***/

  return(sign(q));
}

/********************************************************************
*
* Prozedur:
*    int koeffid(alpha,stk,stj)
*
* Beschreibung:
*    koeffid ist ein Spezialfall von koeff fuer pi=id.
*
* Rueckgabe:
*    Koeffizient -1,0,1
*
********************************************************************/
static int koeffid(alpha,stk,stj) int *alpha; int *stk; int *stj;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int ps[TFNMAX],q[TFNMAX];

  /*** finde nun Permutationen q,ps ***/

  if (find_pq(alpha,stk,stj,q,ps) < 0) return(0);

  /*** der Koeffizient ist dann sgn(q) ***/

  return(sign(q));
}

/********************************************************************
*
* Prozedur:
*    int ndg_L_alpha(alpha,la)
*
* Beschreibung:
*     ndg_L_alpha berechnet die Matrix L_alpha := M_alpha ^ (-1), 
*     mit M_alpha = (( koeff(id,e(kj) )).
*     Die Matrix L_alpha wird in la zurueckgegeben.
*     Es wird nur die rechte obere Haelfte der oberen Dreiecksmatrix
*     gespeichert. Auch die Diagonale aus Einsen wird nicht gespeichert.
*     Die Matrix liegt dann in Vektorform vor. Auf die Komponenten
*     kann mit dem Makro ODM(la,z,s) zugegriffen werden.
*
* Rueckgabe:
*     0, -1 fuer Fehler
*
********************************************************************/
static int ndg_L_alpha(alpha,la) int *alpha; int *la;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int dim,n,*TF_la,*TF_la1,*TF_la2,o1,o2,i,k;
  int id[TFNMAX];
  int j;
  int stj,stk;

  /*** erstmal n aus der Partition berechnen ***/

  n=0;
  for (i=1; i<=alpha[0]; n+=alpha[i++]);

  id[0]=n;
  for (i=1; i<=n; i++) id[i]=i;

  TF_la=la;

  /*** alle Tableaux berechnen, dim muss bekannt sein ***/

  if (stptr)
  {
    SYM_free(stptr);
    stptr=(int *)0L;
  }
  dim=stdim;
  if (allst(alpha,n)) return(-1);

  /*** M_alpha transponiert berechnen ***/

  for (stj=0; stj < dim ; stj++)
    for (stk=stj+1; stk < dim; stk++)
      *TF_la++=koeffid(alpha,STAB(stk),STAB(stj));

  /**** dann L_alpha := M_alpha hoch -1 berechnen ***/

  for (j=dim-1; j>=1; j--)
  {
    TF_la=la+dim*(long)j-((long)j*((long)j+1L))/2L-(long)j-1L;
    TF_la1=TF_la2= &ODM(la,dim,j-1,j);
    for (i=j-1; i>=0; i--)
    {
      *TF_la1= -(*TF_la1); /* ODM(la,dim,i,j) */
      TF_la1 -= dim-i-1; /* eine Zeile aufwaerts */
    }
    for (k=j+1; k<dim; k++)
    {
      if ((o2=TF_la[k])==0) continue; /* ODM(la,dim,j,k)==0 ? */
      TF_la1=TF_la2; /* zeigt auf ODM(la,dim,j-1,j) */
      for (i=j-1; i >= 0; i--)
      {
        if ((o1= *TF_la1)!=0) /* ODM(la,dim,i,j) */
          ODM(la,dim,i,k) += o1*o2;
        TF_la1 -= dim-i-1; /* eine Zeile hoch */
      }
    }
  }
  return(0);
}

/********************************************************************
*
* Prozedur:
*    int ndg_P_pi(alpha,pi,p)
*
* Beschreibung:
*    ndg_P_pi berechnet die Koeffizientenmatrix P_pi zur Permutation
*    pi.
*    Die Matrix wird wie bei L_alpha als Vektor gespeichert.
*    Zugriff erfolgt mit dem Makro MAT(pi,z,s).
*
* Rueckgabe:
*    0
*
********************************************************************/
static int ndg_P_pi(alpha,pi,p) int *alpha; int *pi; int *p;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int n,k,*TF_p;
  int pi1[TFNMAX];
  int stj,stk;

  TF_p=p; 

  /*** berechne pi1 = pi hoch -1 ***/

  n=pi1[0]=pi[0];
  for (k=1; k<=n; k++) pi1[pi[k]]=k;

  /*** berechne Koeffizientenmatrix ***/

  for (stk=0; stk < stdim; stk++)
  for (stj=0; stj < stdim; stj++)
    *TF_p++=koeff(alpha,pi1,STAB(stj),STAB(stk));

  return(0);
}

/********************************************************************
*
* Prozedur:
*    int tfmult(la,p,dim,fp,dig)
*
* Beschreibung:
*    tfmult berechnet Produkt p=la*p. Dabei wird die Dreiecksstruktur
*    bei la zugrunde gelegt, ebenso die Vektorform der Matrizen.
*    Als Ergebnis erhaelt man die Darstellungsmatrix.
*
*    Ist fp!=NULL, so werden Werte mit Breite <dig> auf FILE
*    fp ausgegeben. Bei dig=0 werden die Werte nur durch
*    ein Leerzeichen getrennt.
*
* Rueckgabe:
*    Charakterwert fuer P(pi)
*
********************************************************************/
static int tfmult(la,p,dim,fp,dig) int *la; int *p; int dim; FILE *fp; int dig;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int o1,p2,*TF_la,*TF_p,*TF_pp,i,j;
  int h,k,ch;
  char format[6];

  /*** Format-String fuer die Ausgabe ***/

  if (dig) sprintf(format,"%%%dd",dig);
  else strcpy(format,"%d ");

  /*** multipliziere Matrizen ***/

  ch=0; /* Charakter = 0 */
  for (j=0; j<dim; j++)
  {
    TF_la=la;
    TF_p=p+(long)j;
    for (i=0; i<dim; i++)
    {
      h= *TF_p; /* MAT(p,dim,i,j) */
      TF_pp=TF_p+(long)dim;
      for (k=i+1; k<dim; k++,TF_pp+=(long)dim)
      {
        if ((o1= *TF_la++)==0) continue; /* ODM(i,k) */
        if ((p2= *TF_pp) != 0)  /* MAT(p,dim,k,j)*/
          h = (p2 > 0) ? h+o1 : h-o1 ;
      }
      *TF_p=h; /* MAT(p,dim,i,j) */
      if (i==j) ch+=h;
      TF_p+=dim;
    }
  }

  /*** Ausgabe ***/

  if (fp!=NULL)
  {
    TF_la=p;
    for (i=0; i<dim; i++)
    {
      for (j=0; j<dim; j++) fprintf(fp,format,*TF_la++);
      fprintf(fp,"\n");
    }
  }

  return(ch);
}

#ifdef UNDEF
/********************************************************************
*
* Prozedur:
*   int tfchmult(alpha,la,pi,dim)
*
* Beschreibung:
*    tfchmult berechnet Charakter mittels dem Produkt la*p(pi).
*    Die Matrix p(pi) wird berechnet, aber nicht gespeichert.
*
* Rueckgabe:
*    Charakterwert
*
********************************************************************/
static int tfchmult(alpha,la,pi) int *la; int *pi; int *alpha;
/* AK 191289 V1.1 */
/* TF 011289 */ /* AK 210891 V1.3 */
{
  int h,ch,k,n,o1,p2;
  int *TF_la,pi1[TFNMAX],stj,stk;

  /*** berechne Charakter ***/

  ch=0;
  TF_la=la;

  /*** berechne pi1 = pi hoch -1 ***/

  n=pi1[0]=pi[0];
  for (k=1; k<=n; k++) pi1[pi[k]]=k;

  /*** durchlaufe alle Zeilen von la ***/

  for (stk=0; stk < stdim; stk++)
  {

  /*** durchlaufe entsprechende Spalte in p(pi) ***/

    h=koeff(alpha,pi1,STAB(stk),STAB(stk)); /* Diagonalelement */
    for (stj=stk+1; stj < stdim; stj++)
    {
      if ((o1= *TF_la++)!=0)
      {
        p2=koeff(alpha,pi1,STAB(stk),STAB(stj));
        if (p2) h+=o1*p2;
      }
    }
    ch+=h;
  }
  return(ch);
}
#endif
/****************************** TEIL 2 *******************************
* hier befindet sich die Bindung zu SYMCHAR
*********************************************************************/

/*********************************************************************
*
* Prozedur:
*    ndg(part,perm,dg_mat)
*
* Beschreibung:
*    "ndg" berechnet Darstellungs-Matrix dg_mat 
*    zur Permutation perm und Partition part.
*
****************************************************************************/
INT ndg(part,perm,dg_mat) OP part,perm,dg_mat;
/* AK 191289 V1.1 */ /* TF 011289 */ /* AK 210891 V1.3 */
{
  int  alpha[TFNMAX],pi[TFNMAX],*la,*p,*pp;
  INT  i,j;
  long dim;
  OP   opdim = callocobject();

  dimension(part,opdim);
  dim=(long)S_I_I(opdim);
  stdim=(int)dim;
  freeall(opdim);

  la=(int *)SYM_calloc((dim*(dim-1L))/2L + 1L,sizeof(int));
  p=(int *)SYM_calloc(dim*dim,sizeof(int));

  if (!p)
  {
    error("no memory available for matrices");
    return(ERROR);
  }
  if ((!la) && (dim > 1L))
  {
    error("no memory available for matrices");
    return(ERROR);
  }
  alpha[0]=(int)S_PA_LI(part);
  for (i=0L; i<S_PA_LI(part); i++)
    alpha[alpha[0]-i]=(int)S_PA_II(part,i);
  pi[0]=(int)S_P_LI(perm);
  for (i=0L; i<S_P_LI(perm); i++)
    pi[i+1]=(int)S_P_II(perm,i);

  if (ndg_L_alpha(alpha,la))
  {
    error("calling ndg_L_alpha / allst");
    return(ERROR);
  }
  ndg_P_pi(alpha,pi,p);
  tfmult(la,p,(int)dim,NULL,0);
  SYM_free(la);
  if (stptr)
  {
    SYM_free(stptr);
    stptr=(int *)0L;
  }
  pp=p;
  m_ilih_m((INT)dim,(INT)dim,dg_mat);
  for (i=0L; i<dim; i++)
  for (j=0L; j<dim; j++) m_i_i((INT)(*pp++),S_M_IJ(dg_mat,i,j));
  SYM_free(p);
  return(OK);
}

#endif /* DGTRUE */

