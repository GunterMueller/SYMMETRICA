
#include"def.h"
#include"macro.h"

/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Algorithmus von DIXON-WILF                                          */
/* --------------------------                                          */
/*                                                                     */
/* Dieses Programm berechnet Bahnrepresentanten der Bahnen einer Gruppe*/
/* G, die auf einer Menge M operiert. Es handelt sich um eine gewich-  */
/* tete Version des Algorithmus von Dixon/Wilf.                        */
/* Die Represanten sind gleichverteilt auf den Bahnen von G auf M.     */
/* Je nach Aufruf koennen entweder ein Beispielsatz von Bahnrepresen-  */
/* tanten oder eine Bahnentransversale (oder Teile davon) erzeugt      */
/* werden.                                                             */
/*                                                                     */
/* Aufruf 1:                                                           */
/* ---------                                                           */
/*	dixon_wilf_examples(G,weight,anz,FP);                              */
/*                                                                     */
/*  In diesem Fall werden anz Bahnrepresentanten in die Struktur FP    */
/*  geschrieben. (VECTOR von VECTOREN, die Laenge der einzelnen Rep-   */
/*  praesentanten ist gleich dem Grad der operierenden Permutations-   */
/*  gruppe. Diese muss in der Struktur G (VECTOR von PERMUTATIONEN)    */
/*  uebergeben werden. Es genuegt ein beliebiges Erzeugendensystem,    */
/*  da die komplette Gruppe daraus erzeugt wird.                       */
/*  Der VECTOR weight enthaelt die Anzahl der verschiedenen Gewichte,  */
/*  also die eigentliche Information ueber die Menge, auf der operiert */
/*  wird.                                                              */
/*  Der ungewichtete Fall kann mit diesem Programm ebenfalls simuliert */
/*  werden.                                                            */
/*                                                                     */
/*                                                                     */
/* Aufruf 2:                                                           */
/* ---------                                                           */
/*	dixon_wilf_transversal(G,weight,anz,FP);                           */
/*                                                                     */
/*  In diesem Fall werden anz Bahnrepresentanten aus verschiedenen     */
/*  Bahnen in die Struktur FP geschrieben.                             */
/*  (VECTOR von VECTOREN, die Laenge der einzelnen Rep-                */
/*  praesentanten ist gleich dem Grad der operierenden Permutations-   */
/*  gruppe. Diese muss in der Struktur G (VECTOR von PERMUTATIONEN)    */
/*  uebergeben werden. Es genuegt ein beliebiges Erzeugendensystem,    */
/*  da die komplette Gruppe daraus erzeugt wird.                       */
/*                                                                     */
/*  Der VECTOR weight enthaelt die Anzahl der verschiedenen Gewichte,  */
/*  also die eigentliche Information ueber die Menge, auf der operiert */
/*  wird.                                                              */
/*  Der ungewichtete Fall kann mit diesem Programm ebenfalls simuliert */
/*  werden.                                                            */
/*                                                                     */
/*  Ist die eingegebene Zahl anz groesser als die Zahl der Bahnen, so  */
/*  werden |M//G| Representanten in FP zurueckgegeben.                 */
/*                                                                     */
/*  Wird anz mit 0L uebergeben, so werden ebenfalls |M//G| Representan-*/
/*  ten berechnet.                                                     */
/*                                                                     */
/*---------------------------------------------------------------------*/
/* Written by: Ralf Hager Oktober 1992                                 */
/*---------------------------------------------------------------------*/
/*                                                                     */
/***********************************************************************/
/***********************************************************************/


#define war_schon_da(a,b) ((index_vector(a,b) == -1L ) ? 1L : 0L)
static INT get_edge();
static INT bestimme_egf();
static INT mult_g_fix();
static INT berechne_Mgi();
static INT MGgen();
static INT berechne_Mgi_z();
static INT bestimme_pz();
static INT besetze_fixpunkt();
static INT Mggen();

/***********************************************************************/
/*                                                                     */
/* Routine:   Ggen                                                     */
/* Ausgehend von einem Erzeugendensystem S von Permutationen           */
/* wir die Gruppe G erzeugt und in D abgespeichert.                    */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT Ggen(G) OP      G;
{
        INT     i;
        INT     j;

        OP      D               =       callocobject();
        OP      hperm           =       callocobject();

		if(!einsp(S_V_I(G,0L)))
		{
				m_il_v(S_V_LI(G)+1L,D);
				m_il_nv(S_P_LI(S_V_I(G,0L)),S_V_I(D,0L));
				first_permutation(S_P_L(S_V_I(G,0L)),S_V_I(D,0L));
				for(i=1L;i<S_V_LI(D);++i)       
					copy(S_V_I(G,i-1L),S_V_I(D,i));

	/********************************************************************/
	/* Algorithmus:                                                     */
	/* ------------                                                     */
	/* fuer alle s aus Liste S                                          */
	/*      fuer alle g aus Liste G                                     */
	/*           falls s*g nicht in G                                   */
	/*                 fuege s*g in G ein.                              */
	/********************************************************************/

				for(i=0L;i<S_V_LI(D);++i)
				{
						for(j=0L;j<S_V_LI(G);++j)
						{
								mult(S_V_I(D,i),S_V_I(G,j),hperm);
								if(war_schon_da(hperm,D) != 0L)
								{
										inc(D);
										copy(hperm,S_V_I(D,S_V_LI(D)-1L));
								}
						}
				}
				copy(D,G);
		}

		freeall(D);
        freeall(hperm);
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   Cgen                                                     */
/* --------                                                            */
/* Ausgehend von einer Gruppe G von Permutationen werden zu jedem      */
/* Gruppenelement die Nummer der Konjugiertenklasse, in der es liegt   */
/* Im Vektor C gespeichert.                                            */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT Cgen(G,C) OP	G,C;
{
	INT	i;
	INT	j;
	INT	k;
	INT	c;

	OP  besucht = callocobject();
	OP	h  = callocobject();
	OP	g  = callocobject();
	OP	r  = callocobject();
	OP	ri = callocobject();
	OP	zw = callocobject();

	m_il_nv(S_V_LI(G),C);
	m_il_nv(S_V_LI(G),besucht);

/********************************************************************/
/* Algorithmus:                                                     */
/* ------------                                                     */
/* fuer alle g aus G                                                */
/*      fuer alle h aus G                                           */
/*           fuer alle r aus G                                      */
/*                 falls g = r h r^-1                               */
/*                       h liegt in derselben Klasse wie g          */
/********************************************************************/


	c = 0L;
	for(i=0L;i<S_V_LI(G);++i)
	{
		if(S_V_II(besucht,i)== 0L)
		{
			c++;
			M_I_I(c,S_V_I(C,i));
			M_I_I(1L,S_V_I(besucht,i));
			copy(S_V_I(G,i),g);
			for(j=0L;j<S_V_LI(G);++j)
			{
				if(S_V_II(besucht,j) == 0L)
				{
					copy(S_V_I(G,j),h);
					for(k=0L;k<S_V_LI(G);++k)
					{
 						copy(S_V_I(G,k),r);
						invers(r,ri);
						mult(h,ri,zw);
						mult(r,zw,zw);
						if(EQ(zw,g))
						{
							M_I_I(1L,S_V_I(besucht,j));
							M_I_I(c,S_V_I(C,j));
							break;
						}
					}
				}
			}
		}
	}
	freeall(h);
	freeall(g);
	freeall(r);
	freeall(ri);
	freeall(zw);
	freeall(besucht);
	return(c);
}

/***********************************************************************/
/*                                                                     */
/* Routine:   Cdeg                                                     */
/* --------                                                            */
/* Aus dem in Cgen erzeugten Vektor C werden durch Akkumulation  die   */
/* Ordnungen der Konjugiertenklassen bestimmt.                         */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT Cdeg(C,stat) OP	C,stat;
{
	INT	i;

	for(i=0L;i<S_V_LI(C);++i)
		M_I_I(1L+S_V_II(stat,S_V_II(C,i)-1L),S_V_I(stat,S_V_II(C,i)-1L));
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   make_real_cycletype                                      */
/* --------                                                            */
/* Aus dem in Form einer Partition abgelegten Zykeltyps einer Permuta- */
/* tion, wird ein Vektor erstellt in dessen i-ter Komponente die An-   */
/* zahl der i+1L -  Zykel steht.                                       */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT make_real_cycletype(c,a) OP	c,a;
{
	INT	i;
	for(i=0L;i<S_PA_LI(c);++i)
		M_I_I(S_V_II(a,S_PA_II(c,i)-1L)+1L,S_V_I(a,S_PA_II(c,i)-1L));
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   calculate_fixed_point_number                             */
/* --------                                                            */
/* Es wird ein folgender Binomialkoeffifient berechnet:                */
/*                                                                     */
/*                                                                     */
/*               n    n-i_1         n-sum_j_=1to_m-1(i_j)              */
/*             (   )*(     )* ... *(                     )             */
/*              i_1   i_2                i_m                           */
/*                                                                     */
/*                                                                     */
/* Diese Zahl entspricht gerade der Zahl der Belegungen von n Plaetzen */
/* mit k verschiedenen Objekten mit insgesamt m Farben k = sum_j=1to_m */
/* ueber die i_j                                                       */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT calculate_fixed_point_number(a,b,mg) OP	a,b,mg;
{
	INT	i;
	INT	k;

	OP	zw = callocobject();
	OP	erg = callocobject();
	OP	x = callocobject();
	OP	y = callocobject();
	OP	sum = callocobject();


	M_I_I(1L,erg);
	for(i=0L;i<S_V_LI(a);++i)
	{
		M_I_I(0L,sum);
		for(k=0L;k<S_V_LI(b);++k) add(sum,S_V_I(S_V_I(b,k),i),sum);
		if(S_I_I(sum) > S_V_II(a,i))	
		{
			M_I_I(0L,erg);
			break;
		}
		M_I_I(1L,zw);
		copy(S_V_I(a,i),x);
		for(k=0L;k<S_V_LI(b);++k)
		{
			if(S_V_II(S_V_I(b,k),i) > 0L)
			{
				binom(x,S_V_I(S_V_I(b,k),i),zw);
				sub(x,S_V_I(S_V_I(b,k),i),x);
				mult(zw,erg,erg);
			}
		}
	}
	copy(erg,mg);

	freeall(erg);
	freeall(zw);
	freeall(x);
	freeall(y);
	freeall(sum);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   build_propab_vector                                      */
/* --------                                                            */
/*                                                                     */
/* Im Vektor propab werden die Wahrscheinlichkeiten fuer die Konju-    */
/* tenklassen der Gruppe G gemaess folgender Verteilung bestimmt:      */
/*                                                                     */
/*                                                                     */
/*                |C_i| * |M_gi|                                       */
/*    P(C_i)  =  ---------------                                       */
/*                 |G| * |M//G|                                        */
/*                                                                     */
/*                                                                     */
/* In propab[i] steht dabei stehts sum_j=1L_to_i(P(C_j)                */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT build_propab_vector(propab,Cdeg,G,orb,Mg) OP propab,Cdeg,G,orb,Mg;
{
	OP zaehler = callocobject();
	OP nenner = callocobject();
	OP zw = callocobject();
	OP sum = callocobject();

	INT	i;

	M_I_I(0L,sum);
	mult(S_V_L(G),orb,nenner);

	for(i=0L;i<S_V_LI(propab);++i)
	{
		mult(S_V_I(Cdeg,i),S_V_I(Mg,i),zaehler);
		div(zaehler,nenner,zw);
		add(zw,sum,sum);
		copy(sum,S_V_I(propab,i));
	}

	freeall(zaehler);
	freeall(nenner);
	freeall(zw);
	freeall(sum);
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   bestimme_konjugiertenklasse                              */
/* --------                                                            */
/*                                                                     */
/* Mittels einer Zufallszahl wird die Konjugiertenklasse bestimmt zu   */
/* der ein Fixpunkt konstruiert werden soll.                           */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT bestimme_konjugiertenklasse(propab,ind,G,Orb) OP	propab;
	INT	*ind; OP	G; OP	Orb;
{
	INT	i;

	OP	oben = callocobject();
	OP	unten = callocobject();
	OP	z = callocobject();

	M_I_I(0L,unten);
	mult(Orb,S_V_L(G),z);
	M_I_I(S_I_I(z),oben);

	random_integer(z,unten,oben);
	div(z,oben,z);
	for(i=0L;i<S_V_LI(propab);++i)
	{
		if(LE(z,S_V_I(propab,i)))
		{
			*ind = i;
			break;
		}
	}

	freeall(oben);
	freeall(unten);
	freeall(z);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   bestimme_fixpunkt                                        */
/* --------                                                            */
/*                                                                     */
/* Zu einem Gruppenelement wird gleichverteilt ein Fixpunkt konstru-   */
/* iert. Dabei wird zwischen der Identitaet und den anderen Konjugier- */
/* tenklassen unterschieden, da fuer die Identitaet die Situation ein- */
/* facher ist und diese auch bei weitem am haeufigsten aufgerufen wird.*/
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

#ifdef PERMTRUE
INT bestimme_fixpunkt(G,C,Cdegrees,ind,weight,FP,Mg)
	OP	G; OP	C; OP	Cdegrees; INT	ind;
	OP	weight; OP	FP; OP	Mg;
{
	INT	i;
	INT	j;
	INT	k;
	INT	besetzt;
	INT	zaehler;
	OP	z = callocobject();
	OP	oben = callocobject();
	OP	unten = callocobject();
	OP	g = callocobject();
	OP	a = callocobject();
	OP	sum = callocobject();
	OP	pz = callocobject();
	OP	part_g = callocobject();
	OP	ergzyk = callocobject();
	OP	multizyk = callocobject();
	OP	multipart = callocobject();
	OP	BEENDEN = callocobject();


	if(ind == 0L)
	{
		M_I_I(S_P_LI(S_V_I(G,0L)),oben);
		M_I_I(0L,unten);
		for(k=0L;k<S_P_LI(S_V_I(G,0L));++k) M_I_I(0L,S_V_I(FP,k));

		for(i=0L;i<S_V_LI(weight);++i)
		{
			if(S_V_II(weight,i)>0L)
			{
				for(j=0L;j<S_V_II(weight,i);++j)
				{
					zaehler = 0;
					besetzt = 1L;
					while(besetzt)
					{
						random_integer(z,unten,oben);
						for(k=0L;k<S_V_LI(FP);++k)
						{
							if(zaehler == S_I_I(z) &&
							   S_V_II(FP,k) == 0L)
							   {
								M_I_I(i+1L,S_V_I(FP,k));
								M_I_I(S_I_I(oben)-1L,oben);
								besetzt = 0L;
								break;
							   }
							else
								if(S_V_II(FP,k) == 0L)
									zaehler++;
						}
					}
				}
			}
		}
	}
	else
	{
		if(S_V_II(Mg,ind) != 0L)
		{
				M_I_I(1L,unten);
				M_I_I(S_V_II(Cdegrees,ind),oben);
				random_integer(z,unten,oben);

				zaehler = 0L;
				for(i=0L;i<S_V_LI(G);++i)
				{
					if(S_V_II(C,i) == ind+1L)	zaehler++;
					if(zaehler == S_I_I(z))
					{
						copy(S_V_I(G,i),g);
						break;
					}
				}
				zykeltyp(g,part_g);
				m_il_nv(S_P_LI(g),a);
				make_real_cycletype(part_g,a);
				m_il_nv(2L,pz);
				m_il_nv(S_P_LI(g),S_V_I(pz,0L));
				m_il_nv(S_P_LI(g),S_V_I(pz,1L));
				bestimme_pz(a,g,pz);

				M_I_I(1L,unten);
				M_I_I(S_V_II(Mg,ind),oben);
				random_integer(z,unten,oben);

				m_il_nv(S_V_LI(weight),multipart);
				m_il_nv(S_V_LI(weight),multizyk);
				for(i=0L;i<S_V_LI(weight);++i) 
					m_il_nv(S_P_LI(S_V_I(G,0L)),S_V_I(multizyk,i));
				M_I_I(0L,sum);
				M_I_I(0L,BEENDEN);

				berechne_Mgi_z(z,a,multipart,multizyk,
							   weight,sum,0L,ergzyk,BEENDEN);

				besetze_fixpunkt(a,ergzyk,pz,FP);
		}
		else
		{
#ifdef UNDEF
			fprintf(stderr,"Diese Konjugiertenklasse liefert keine Fixpunkte !!!\n");
			/* Darf eigentlich nicht ausgegeben werden !!! */
#endif
		}
	}

	freeall(z);
	freeall(oben);
	freeall(unten);
	freeall(g);
	freeall(a);
	freeall(pz);
	freeall(sum);
	freeall(part_g);
	freeall(multizyk);
	freeall(ergzyk);
	freeall(multipart);
	freeall(BEENDEN);
	return OK;
}
#endif /* PERMTRUE */


/***********************************************************************/
/*                                                                     */
/* Routine:   dixon_wilf_examples                                      */
/* --------                                                            */
/*                                                                     */
/* Steuerprogramm fuer den Algorithmus von Dixon Wilf. Beschreibung    */
/* siehe Modulanfang.                                                  */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

dixon_wilf_examples(G,weight,anz,FP)
	OP	G; OP	weight; OP	anz; OP	FP;
{
	INT Canz;
	INT i;
	INT j;
	INT ind;

	OP	Cdegrees = callocobject();
	OP	C  = callocobject();
	OP	Mg = callocobject();
	OP	MG = callocobject();
	OP	propab = callocobject();
	OP	fix = callocobject();

	freeself(FP);

    Ggen(G);
	Canz = Cgen(G,C);
	m_il_nv(Canz,Cdegrees);
	Cdeg(C,Cdegrees);

	m_il_nv(Canz,Mg);
	Mggen(G,C,Cdegrees,weight,Mg);

	MGgen(Mg,G,Cdegrees,MG);

	m_il_nv(S_V_LI(Cdegrees),propab);
	build_propab_vector(propab,Cdegrees,G,MG,Mg);

	m_il_nv(S_P_LI(S_V_I(G,0L)),fix);
	m_il_nv(S_I_I(anz),FP);

	for(i=0L;i<S_I_I(anz);++i)
	{
		for(j=0;j<S_P_LI(S_V_I(G,0L));++j) M_I_I(0L,S_V_I(fix,j));
		bestimme_konjugiertenklasse(propab,&ind,G,MG);
		bestimme_fixpunkt(G,C,Cdegrees,ind,weight,fix,Mg);
		copy(fix,S_V_I(FP,i));
	}

	freeall(Mg);
	freeall(MG);
	freeall(C);
	freeall(propab);
	freeall(Cdegrees);
	freeall(fix);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   dixon_wilf_transversal                                   */
/* --------                                                            */
/*                                                                     */
/* Steuerprogramm fuer den Algorithmus von Dixon Wilf. Beschreibung    */
/* siehe Modulanfang.                                                  */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT dixon_wilf_transversal(G,weight,anz,FP)
	OP	G; OP	weight; OP	anz; OP	FP;
{
	INT Canz;
	INT j;
	INT k;
	INT ind;
	INT anz_fp;
	INT count;

	OP	Cdegrees = callocobject();
	OP	C  = callocobject();
	OP	Mg = callocobject();
	OP	MG = callocobject();
	OP	propab = callocobject();
	OP	fix = callocobject();

	freeself(FP);

	m_il_nv(0L,FP);

    Ggen(G);
	Canz = Cgen(G,C);
	m_il_nv(Canz,Cdegrees);
	Cdeg(C,Cdegrees);

	m_il_nv(Canz,Mg);
	Mggen(G,C,Cdegrees,weight,Mg);

	MGgen(Mg,G,Cdegrees,MG);

	m_il_nv(S_V_LI(Cdegrees),propab);
	build_propab_vector(propab,Cdegrees,G,MG,Mg);

	m_il_nv(S_P_LI(S_V_I(G,0L)),fix);
	if(S_I_I(anz) == 0L || S_I_I(anz) > S_I_I(MG))
		anz_fp = S_I_I(MG);
	else
		anz_fp = S_I_I(anz);


	k = 0L;
	count = 0L;
	while(k < anz_fp)
	{
		for(j=0;j<S_V_LI(fix);++j) M_I_I(0L,S_V_I(fix,j));
		bestimme_konjugiertenklasse(propab,&ind,G,MG);
		bestimme_fixpunkt(G,C,Cdegrees,ind,weight,fix,Mg);
		if(new_orbit(G,fix,FP))
			{
				inc(FP);
				copy(fix,S_V_I(FP,S_V_LI(FP)-1L));
				k++;
			}
			count++;
	if(count %100  == 0L)fprintf(stderr,"Versuch nr:  %d Gef.: %d\r",count,k);
	}

	freeall(Mg);
	freeall(MG);
	freeall(C);
	freeall(propab);
	freeall(Cdegrees);
	freeall(fix);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   MGgen                                                    */
/* --------                                                            */
/*                                                                     */
/* Mittels des Lemmas von Cauchy-Frobenius wird die Anzahl der Bahnen  */
/* |M//G| berechnet.                                                   */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

static INT MGgen(Mg,G,Cdeg,MG)
	OP	Mg; OP	G; OP	Cdeg; OP	MG;
{
	INT	i;

	OP summand = callocobject();

	/* Lemma von Cauchy-Frobenius  orb = 1/|G| * (summe ueber Mg[i]) */

	M_I_I(0L,MG);
	for(i=0L;i<S_V_LI(Mg);++i)
	{
		mult(S_V_I(Cdeg,i),S_V_I(Mg,i),summand);
		add(summand,MG,MG);
	}
	div(MG,S_V_L(G),MG);
	freeall(summand);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   Mggen                                                    */
/* --------                                                            */
/*                                                                     */
/* Fuer die einzelnen Konjugiertenklassen werden die entsprechenden    */
/* Fixpunktanzahlen als Summenvon Binomialkoeffizienten berechnet.     */
/*                                                                     */
/*                                                                     */
/* Dabei werden Multipartitionen des Gewichtsvektor weight bestimmt    */
/* und dann die moeglichen Belegungen auf der Partition des ausgewaehl-*/
/* ten Gruppenelements g_i berechnet.                                  */
/*                                                                     */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

static INT Mggen(G,C,Cdegrees,weight,Mg)
	OP	G; OP	C; OP	Cdegrees; OP	weight; OP	Mg;
{
	INT	i;
	INT	j;
	INT	k;

	OP	a = callocobject();
	OP	cycle_a = callocobject();
	OP	multipart = callocobject();
	OP	multizyk = callocobject();
	OP	hpart = callocobject();

	m_il_nv(S_P_LI(S_V_I(G,0L)),a);
	m_il_nv(S_V_LI(weight),multipart);
	m_il_nv(S_V_LI(weight),multizyk);
	for(i=0L;i<S_V_LI(weight);++i) 
		m_il_nv(S_P_LI(S_V_I(G,0L)),S_V_I(multizyk,i));

	for(i=1L;i<=S_V_LI(Cdegrees);++i)
	{
		for(j=0L;j<S_V_LI(G);++j)
		{
			if(S_V_II(C,j) == i)
			{
				for(k=0L;k<S_V_LI(a);++k)	M_I_I(0L,S_V_I(a,k));
				zykeltyp(S_V_I(G,j),cycle_a);
				make_real_cycletype(cycle_a,a);
				berechne_Mgi(a,multipart,multizyk,weight,S_V_I(Mg,i-1L),0L);
				break;
			}
		}
	}

	freeall(a);
	freeall(cycle_a);
	freeall(multipart);
	freeall(multizyk);
	freeall(hpart);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   berechne_Mgi                                             */
/* --------                                                            */
/*                                                                     */
/* Unterroutine zu Mggen die die Multipartitionen berechnet.           */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

static INT berechne_Mgi(a,multipart,multizyk,weight,Mgi,ind)
	OP	a,multipart; OP	multizyk; OP	weight; OP	Mgi;
	INT	ind;
{
	INT	k;
	OP	hpart = callocobject();
	OP	hzyk = callocobject();
	OP	FP = callocobject();

	if(ind == S_V_LI(weight))
	{
				M_I_I(0L,FP);
				calculate_fixed_point_number(a,multizyk,FP);
				if(S_I_I(FP) > 0L)
					add(FP,Mgi,Mgi);
	}
	else
	{
		if(S_V_II(weight,ind) > 0L)
		{
			first_partition(S_V_I(weight,ind),
							S_V_I(multipart,ind));
			do
			{
				for(k=0L;k<S_V_LI(a);++k)
					M_I_I(0L,S_V_I(S_V_I(multizyk,ind),k));
				make_real_cycletype(S_V_I(multipart,ind),
									S_V_I(multizyk,ind));
				copy(S_V_I(multipart,ind),hpart);
				copy(S_V_I(multizyk,ind),hzyk);
				berechne_Mgi(a,multipart,multizyk,weight,Mgi,ind+1L);
				copy(hpart,S_V_I(multipart,ind));
				copy(hzyk,S_V_I(multizyk,ind));
			}
			while(next(S_V_I(multipart,ind),S_V_I(multipart,ind)));
		}
		else
		{
			berechne_Mgi(a,multipart,multizyk,weight,Mgi,ind+1L);
		}
	}
	freeall(hpart);
	freeall(hzyk);
	freeall(FP);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   new_orbit                                                */
/* --------                                                            */
/*                                                                     */
/* Indem die Gruppe G auf den Vektor FP losgelassen und dann mit       */
/* fix vergleichen wird, wird festgestellt, ob ein neuer Bahnreprae-   */
/* sentant vorliegt.                                                   */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

INT new_orbit(G,fix,FP) OP	G; OP	fix; OP	FP;
{
	INT	i;
	INT	j;
	INT	erg = 1L;
	OP	hfix = callocobject();

	m_il_nv(S_V_LI(fix),hfix);

	if (S_V_LI(FP) == 0L)
		{
		erg = 1L; 
		}
	else
	for(i=0L;i<S_V_LI(G);++i)
	{
		mult_g_fix(S_V_I(G,i),fix,hfix);
		for(j=0L;j<S_V_LI(FP);++j)
		{
			if(EQ(hfix,S_V_I(FP,j)))
			{
				erg = 0L;
				break;
			}
		}
		if(erg == 0L) break;
	}

	freeall(hfix);

	return(erg);
}


/***********************************************************************/
/*                                                                     */
/* Routine:   bestimme_pz                                              */
/* --------                                                            */
/*                                                                     */
/* Zur Permutation g mit Zykeltyp a wird folgender zweizeiliger Vektor */
/* bestimmt: (Er dient spaeter bei der Besetzung der Fixpunkte)        */
/*                                                                     */
/* pz[0][i] = j  i+1L liegt in Zykel der Laenge j                      */
/* pz[1][i] = k  i+1L liegt im k-ten Zykel                             */
/*                                                                     */
/***********************************************************************/
/* RH 031092 */

static INT bestimme_pz(a,g,pz) OP	a,g,pz;
{
	INT	weiter;
	INT	anz;
	INT	length;
	INT	beginn;
	INT	i;

	OP	anz_length = callocobject();
	OP	besucht = callocobject();

	anz = length = 0L;
	weiter = 1L;
	beginn = 1L;

	m_il_nv(S_V_LI(a),besucht);
	m_il_nv(S_V_LI(a),anz_length);

	M_I_I(1L,S_V_I(besucht,0L));

	while(anz < S_V_LI(a))
	{
		length = 0L;
		weiter = beginn;
		do
		{
			length++;
			weiter = S_P_II(g,weiter-1L);
			M_I_I(1L,S_V_I(besucht,weiter-1L));
		}
		while(weiter != beginn);

		M_I_I(1L+S_V_II(anz_length,length),
			  S_V_I(anz_length,length));
		M_I_I(length,S_V_I(S_V_I(pz,0L),beginn-1L));
		M_I_I(S_V_II(anz_length,length),
			  S_V_I(S_V_I(pz,1L),beginn-1L));

		weiter = beginn;
		do
		{
			weiter = S_P_II(g,weiter-1L);
			M_I_I(length,S_V_I(S_V_I(pz,0L),weiter-1L));
			M_I_I(S_V_II(anz_length,length),
				  S_V_I(S_V_I(pz,1L),weiter-1L));
		}
		while(weiter != beginn);

		for(i=0L;i<S_V_LI(a);++i)
		{
			if(S_V_II(besucht,i) == 0L)
			{
				beginn = i+1L;
				break;
			}
		}
		anz+= length;
	}

	freeall(anz_length);
	freeall(besucht);
	return OK;
}


/***********************************************************************/
/*                                                                     */
/* Routine:   berechne_Mgi_z                                           */
/* --------                                                            */
/*                                                                     */
/* Zu einer Zufallszahl z, die zwischen 1L und der Anzahl der Fixpunkte*/
/* der ausgewaehlten Konjugiertenklasse liegt wird eine Multipartition */
/* bestimmt, in der der z-te Fixpunkt enthalten ist.                   */
/*                                                                     */
/* Verlaeuft analog zur Routine berechne_Mgi.                          */ 
/*                                                                     */ 
/*                                                                     */ 
/***********************************************************************/ 
/* RH 031092 */ 

static INT berechne_Mgi_z(z,a,multipart,multizyk,weight,sum,ind,erg,BEENDEN) 
	OP	z; OP	a; OP	multipart; OP	multizyk; OP	weight;
	OP	sum; INT	ind; OP	erg; OP	BEENDEN;
{
	INT	k;
	OP	hpart = callocobject();
	OP	hzyk = callocobject();
	OP	FP = callocobject();

	if(ind == S_V_LI(weight))
	{
				M_I_I(0L,FP);
				calculate_fixed_point_number(a,multizyk,FP);
				add(FP,sum,sum);
				if(S_I_I(FP) != 0L && S_I_I(BEENDEN) == 0L)
				{
					if(S_I_I(sum)+S_I_I(FP) > S_I_I(z))
					{
						copy(multizyk, erg);
						M_I_I(1L,BEENDEN);
					}
				}
	}
	else
	{
	  if(S_I_I(sum) < S_I_I(z))
	  {
		if(S_V_II(weight,ind) > 0L)
		{
			first_partition(S_V_I(weight,ind),
							S_V_I(multipart,ind));
			do
			{
				for(k=0L;k<S_V_LI(a);++k)
					M_I_I(0L,S_V_I(S_V_I(multizyk,ind),k));
				make_real_cycletype(S_V_I(multipart,ind),
									S_V_I(multizyk,ind));
				copy(S_V_I(multipart,ind),hpart);
				copy(S_V_I(multizyk,ind),hzyk);
				berechne_Mgi_z(z,a,multipart,multizyk,weight,sum,
							   ind+1L,erg,BEENDEN);
				copy(hpart,S_V_I(multipart,ind));
				copy(hzyk,S_V_I(multizyk,ind));
			}
			while(next(S_V_I(multipart,ind),S_V_I(multipart,ind)));
		}
		else
		{
			berechne_Mgi_z(z,a,multipart,multizyk,
						   weight,sum,ind+1L,erg,BEENDEN);
		}
	  }
	}
	freeall(hpart);
	freeall(hzyk);
	freeall(FP);
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   besetze_fixpunkt                                         */
/* --------                                                            */
/*                                                                     */
/* Im Fall der Auswahl einer nicht-trivialen Konjugiertenklasse wird   */
/* hier der Fixpunkt konstruiert, indem mittels Zufallszahlen aus der  */
/* Multipartition die passende Belegung konstruiert wird.              */
/*                                                                     */ 
/***********************************************************************/ 
/* RH 031092 */ 

static INT besetze_fixpunkt(a,ergzyk,pz,FP) OP	a,ergzyk,pz,FP;
{
	INT	i;
	INT	j;
	INT	k;
	INT	l;
	INT	besetzt; INT	zaehler;

	OP	z = callocobject();
	OP	unten = callocobject();
	OP	oben = callocobject();
	OP	besucht = callocobject();

	m_il_nv(S_V_LI(a),besucht);

	M_I_I(1L,unten);
	for(i=0L;i<S_V_LI(a);++i)
	{
		if(S_V_II(a,i) > 0L)
		{
		M_I_I(S_V_II(a,i),oben);
			for(j=0L;j<S_V_LI(ergzyk);++j)
			{
				if(S_V_II(S_V_I(ergzyk,j),i) > 0L)
				{
					k = 0L;	
					while(k < S_V_II(S_V_I(ergzyk,j),i))
					{
						besetzt = 1L;
						zaehler = 0L;
						while(besetzt)
						{
							random_integer(z,unten,oben);
							for(l=0L;l<S_V_LI(a);++l)
							{
							if(S_V_II(S_V_I(pz,0L),l) == i + 1L    &&
							   S_V_II(S_V_I(pz,1L),l) == S_I_I(z))
							   if( S_V_II(besucht,l) == 0L)
							   {
							   M_I_I(j+1L,S_V_I(FP,l));
							   M_I_I(1L,S_V_I(besucht,l));
							   besetzt = 0L;
							   M_I_I(S_I_I(oben)-1L,oben);
							   }
							   else
							   {
							   M_I_I(S_I_I(z)+1L,z);
							   l = 0L;
							   }
							}
							k++;
						}
					}
				}
			}
		}
	}

	freeall(z);
	freeall(unten);
	freeall(oben);
	freeall(besucht);
	return OK;
}

/***********************************************************************/
/*                                                                     */
/* Routine:   mult_g_fixpunkt                                          */
/* --------                                                            */
/*                                                                     */
/* Die Permutation g wird auf fix angewendet und das Ergebnis in hfix  */ 
/* gespeichert.                                                        */
/*                                                                     */ 
/***********************************************************************/ 
/* RH 031092 */ 

static INT mult_g_fix(g,fix,hfix) OP	g,fix,hfix;
{
	INT	i;

	invers(g,g);
	for(i=0L;i<S_P_LI(g);++i)
		M_I_I(S_V_II(fix,S_P_II(g,i)-1L),S_V_I(hfix,i));
	invers(g,g);
	return OK;
}

static INT bestimme_egf(fix,egf) OP	fix; OP	egf;
{
	INT	i,e1,e2;

	for(i=0L;i<S_V_LI(fix);++i)
	{
		if(S_V_II(fix,i) != 0L)
		{
			get_edge(S_V_LI(egf),i+1L,&e1,&e2);
			M_I_I(S_V_II(egf,e1-1L)+1L,S_V_I(egf,e1-1L));
			M_I_I(S_V_II(egf,e2-1L)+1L,S_V_I(egf,e2-1L));
		}
	}
	return OK;
}

static INT get_edge(n,i,e1,e2) INT	n,i,*e1,*e2;
{
	INT w;

	w = n-1L;

	*e1 = 1L;
	*e2 = 1L;

	if(i-w<=0L)
	{
	*e1 = 1L;
	*e2 = (*e1)+i;;
	}
	else
	{
		while(i - w > 0L)
		{
			i-= w;
			(*e1)++;
			w--;
		}
		(*e2) = (*e1)+i;
	}
	return OK;
}

/***********************************************************************/
/***********************************************************************/
/*                                                                     */
/* Konstruktion von Bahnrepraesentatnen vorgegebener Laenge einer      */
/* Gruppe G, die auf m^n operiert.                                     */
/*                                                                     */
/*---------------------------------------------------------------------*/
/* Written by: Ralf Hager November 1992                                */
/*---------------------------------------------------------------------*/
/*                                                                     */
/***********************************************************************/
/***********************************************************************/



/***********************************************************************/
/*                                                                     */
/* Die Erzeuger der Gruppe G, die auf dem File stehen muessen werden   */
/* als Vektor von Permutationen gespeichert.                           */
/*                                                                     */
/* Es wird keine Pruefung vorgenommen, ob die Eingaben sinnvoll sind   */
/* z.B. len | |G|, usw.                                                */
/*                                                                     */
/* Auch hier, wie bei allen Anwendungen von Dixon-Wilf sind nur kleine */
/* Gruppen sinnvoll, da die Konjugiertenkl. berechnet werden muessen   */
/*                                                                     */
/* Wird beim Aufruf des Programms get_orb_rep der letzte Parameter     */
/* mit 0L besetzt, so wird nur die Anzahl der Bahnrepraesentanten      */
/* berechnet, bei 1L werden sie konstruiert. Beidesmal steht das Ergeb-*/
/* nis in L.                                                           */
/* Die Anzahlberechnung empfiehlt sich vorab, denn bei mehr als ca.    */
/* 5000 zu konstruierenden Fixpunkten treten eventuell Speicherplatz-  */
/* probleme auf.                                                       */
/*                                                                     */
/* ------------------------------------------------------------------- */
/*                                                                     */
/* Der Vorteil bei diesem Programm besteht darin, dass nur fuer einige */
/* Gewichte die Fixpunkte berechnet werden, alle uebrigen dann durch   */
/* Einfaerben gewonnen werden.                                         */
/* Dadurch werden z.B. fuer G = C_7 , auf 7^7 nur ca. 11400 Versuche   */
/* durchgefuehrt, es gibt aber 117648 Lyndon-Woerter.                  */
/*                                                                     */
/* Durch das noch nicht optimal programmierte Einfaerben waechst der   */
/* Aufwand mit wachsendem m besonders stark.                           */
/*                                                                     */
/* ------------------------------------------------------------------- */
/*                                                                     */
/***********************************************************************/



INT get_orb_rep(G,m,n,L,len,konstr)
	OP	G; OP	m; OP	n; OP	L; OP	len; INT	konstr;
{
	INT		i;
	INT		j;
	INT 	k;

	INT		c_fp  	= 0L;
	INT		c_lyn 	= 0L;
	INT		c_v 	= 0L;
	INT		count 	= 0L;
	INT 	Canz 	= 0L;
	INT 	ind		= 0L;
	INT 	anz_fp	= 0L;

	INT		hfix_in_ww();
	INT		Cgen();

	OP	weight 		= callocobject();
	OP	anz 		= callocobject();
	OP	FP 			= callocobject();
	OP	part 		= callocobject();
	OP	perm 		= callocobject();
	OP	fix 		= callocobject();
	OP	hfix 		= callocobject();
	OP	Cdegrees 	= callocobject();
	OP	C  			= callocobject();
	OP	Mg 			= callocobject();
	OP	MG 			= callocobject();
	OP	propab 		= callocobject();
	OP	perm_vec	= callocobject();
	OP	p 			= callocobject();
	OP	b 			= callocobject();
	OP	hweight 	= callocobject();
	OP	weight_watcher	= callocobject();

	if(S_I_I(n) == 1L) 
	{
		if(konstr == 0L)
			M_I_I(S_I_I(m),L);
		else
		{
			m_il_nv(S_I_I(m),L);
			for(i=0L;i<S_I_I(m);++i)
				M_I_I(i,S_V_I(L,i));
		}
		goto ende; /* AK 281093 */
	}

	m_il_p(S_I_I(m),p);
	m_il_nv(S_I_I(m),b);
	m_il_nv(S_I_I(n),hweight);
	M_I_I(0L,anz);

	if(konstr == 1L)
		m_il_nv(0L,L);
	c_lyn= 0L;


	m_il_nv(0L,FP);

    Ggen(G);
	fprintf(stderr,"Gruppe erzeugt Ordnung %d\n",S_V_LI(G));

	if(S_I_I(len) == 0L)
		M_I_I(S_V_LI(G),len);

	Canz = Cgen(G,C);
	fprintf(stderr,"Konjugiertenklassen erzeugt Anzahl %d\n",Canz);
	m_il_nv(Canz,Cdegrees);
	Cdeg(C,Cdegrees);

	first_partition(n,part);
	next(part,part);
	do
	{
		if(S_PA_LI(part) <= S_I_I(m))
		{
			m_il_nv(0L,FP);
			m_il_nv(S_I_I(n),weight);

			for(j=1L;j<S_PA_LI(part);++j)
				M_I_I(S_PA_II(part,j),S_V_I(weight,j-1L));

			for(j=0L;j<S_PA_LI(part);++j)
				M_I_I(S_PA_II(part,j),S_V_I(hweight,j));

			m_il_nv(Canz,Mg);
			Mggen(G,C,Cdegrees,weight,Mg);

			MGgen(Mg,G,Cdegrees,MG);
			printf("Anzahl Bahnrepraesentanten: %d\n",S_I_I(MG));

			m_il_nv(S_V_LI(Cdegrees),propab);
			build_propab_vector(propab,Cdegrees,G,MG,Mg);

			m_il_nv(S_P_LI(S_V_I(G,0L)),fix);
			if(S_I_I(anz) == 0L || S_I_I(anz) > S_I_I(MG))
				anz_fp = S_I_I(MG);
			else
				anz_fp = S_I_I(anz);

			k = 0L;
			count = 0L;
			while(k < anz_fp)
			{
				for(j=0;j<S_V_LI(fix);++j) M_I_I(0L,S_V_I(fix,j));
				bestimme_konjugiertenklasse(propab,&ind,G,MG);
				bestimme_fixpunkt(G,C,Cdegrees,ind,weight,fix,Mg);
				if(new_orbit(G,fix,FP))
					{
						inc(FP);
						copy(fix,S_V_I(FP,S_V_LI(FP)-1L));
						k++;
					}
					count++;
			if(count %100  == 0L)
				fprintf(stderr,"Versuch nr:  %d Gef.: %d\r",count,k);
			}
			fprintf(stderr,"Anzahl der gemachten Versuche: %d\n",count);

			c_fp+= S_V_LI(FP);
			c_v+=  count;
			lyndon_orb(G,FP,len);


			if(S_V_LI(FP)>0L)
			{
				m_il_nv(S_I_I(m),b);
				m_il_nv(0L,weight_watcher);
				m_il_nv(0L,perm_vec);
				copy(S_V_I(FP,0L),fix);
				sort(fix);

				get_perm(hweight,p,b,S_I_I(n),S_I_I(m),0L,
						 perm_vec,weight_watcher,fix);

				if(konstr == 1L)
					for(i=0L;i<S_V_LI(perm_vec);++i)
					{
						for(j=0L;j<S_V_LI(FP);++j)
						{
							mult_perm_fix(S_V_I(perm_vec,i),
										  S_V_I(FP,j),hfix);
							inc(L);
							copy(hfix,S_V_I(L,c_lyn));
							c_lyn++;
						}
					}
				else 
				{
					M_I_I(S_V_LI(perm_vec)*S_V_LI(FP)+S_I_I(L),L);
					c_lyn+= S_V_LI(perm_vec)*S_V_LI(FP);
				}
			}
			printf("Fixpunkte  %d  Gef. Bahnrepr.: %d Versuche %d\n",
				   c_fp,c_lyn,c_v);
		}
	} while(next(part,part));

ende:
	freeall(part);
	freeall(anz);
	freeall(FP);
	freeall(perm);
	freeall(fix);
	freeall(hfix);
	freeall(weight_watcher);
	freeall(Mg);
	freeall(MG);
	freeall(C);
	freeall(propab);
	freeall(Cdegrees);
	freeall(hweight);
	freeall(perm_vec);
	freeall(p);
	freeall(b);
	return OK;
}

INT lyndon_orb(G,FP,len) OP	G; OP	FP; OP	len;
{
	INT	i;
	INT	orblen();
	OP	lyn = callocobject();

	m_il_nv(1L,lyn);
	for(i=0L;i<S_V_LI(FP);++i)
		if(orblen(G,S_V_I(FP,i)) == S_I_I(len))
		{
			copy(S_V_I(FP,i),S_V_I(lyn,S_V_LI(lyn)-1L));
			inc(lyn);
		}

	dec(lyn);
	copy(lyn,FP);

	freeall(lyn);
	return OK;
}

INT orblen(G,fix) OP	G; OP	fix;
{
	INT	i;
	INT	j;
	INT	neu = 1L;
	INT	erg = 0L;
	OP	orb = callocobject();
	OP	hfix = callocobject();

	m_il_nv(1L,orb);
	copy(fix,S_V_I(orb,0L));

	m_il_nv(S_V_LI(fix),hfix);

	for(i=0L;i<S_V_LI(G);++i)
	{
		neu = 1L;
		mult_g_fix(S_V_I(G,i),fix,hfix);		
		for(j=0L;j<S_V_LI(orb);++j)
		{
			if(EQ(hfix,S_V_I(orb,j)))
			{
				neu = 0L;
				break;
			}
		}
		if(neu)
		{
			inc(orb);
			copy(hfix,S_V_I(orb,S_V_LI(orb)-1L));
		}
	}
	erg = S_V_LI(orb);

	freeall(orb);
	freeall(hfix);

	return(erg);
}

INT mult_perm_fix(perm,fix,hfix) OP	perm,fix,hfix;
{
	INT	i;
	OP	hilf = callocobject();

	m_il_nv(S_V_LI(fix),hilf);
	for(i=0L;i<S_V_LI(fix);++i)
		M_I_I(S_P_II(perm,S_V_II(fix,i))-1L,S_V_I(hilf,i));

	copy(hilf,hfix);
	freeall(hilf);
	return OK;
}

INT hfix_in_ww(fix,ww) OP	fix,ww;
{
	INT	i;
	INT	erg = 0L;

	if(S_V_LI(ww) > 0L)
		for(i=0L;i<S_V_LI(ww);++i)
			if(EQ(S_V_I(ww,i),fix)) 
			{
				erg = 1L;
				break;
			}
	return(erg);
}

INT get_perm(w,p,b,n,m,ind,perm_vec,ww,fix)
	OP	w,p,b; INT	n,m,ind; OP	perm_vec,ww,fix;
{
	INT	i;
	OP  hfix = callocobject();

	if(ind == m)
	{
		mult_perm_fix(p,fix,hfix);
		sort(hfix);
		if(!hfix_in_ww(hfix,ww))
		{
			inc(ww);
			copy(hfix,S_V_I(ww,
				 S_V_LI(ww)-1L));
			inc(perm_vec);
			copy(p,S_V_I(perm_vec,S_V_LI(perm_vec)-1L));
		}
	}
	else
	{
		for(i=0L;i<m;++i)
		{
			if(S_V_II(b,i) == 0L)
			{
				if(i != ind)
				{
					if(S_V_II(w,i) != S_V_II(w,ind))
					{
						M_I_I(ind+1L,S_P_I(p,i));
						M_I_I(1L,S_V_I(b,i));
						get_perm(w,p,b,n,m,ind+1L,perm_vec,ww,fix);
						M_I_I(0L,S_V_I(b,i));
					}
				}
				else
				{
					M_I_I(ind+1L,S_P_I(p,i));
					M_I_I(1L,S_V_I(b,i));
					get_perm(w,p,b,n,m,ind+1L,perm_vec,ww,fix);
					M_I_I(0L,S_V_I(b,i));
				}
			}
		}
	}
	freeall(hfix);
	return OK;
}

