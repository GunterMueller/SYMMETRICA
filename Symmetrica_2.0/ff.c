/* SYMMETRICA ff.c */
#include "def.h"
#include "macro.h"

#define MAXDEGREE 20
INT null_ip[MAXDEGREE];
INT eins_ip[MAXDEGREE];

#ifdef FFTRUE
/*
#define SYM_free(a) SYM_free_debug(a)
#define SYM_malloc(a) SYM_malloc_debug(a)
#define SYM_calloc(a,b) SYM_calloc_debug(a,b)
#define SYM_free(a)
*/

#define UE_malloc(a) SYM_malloc(a)
#define UE_realloc(a,b) SYM_realloc(a,b)

static INT init_ff();
static INT Charakteristik=(INT)0;
static INT UE_Erw_Grad=(INT)0;
static INT *UE_Platz_Mult=NULL;

#define Mult_Tafel_Speicher XYZ_ABC
static INT ***Mult_Tafel_Speicher = NULL;
static INT *Mult_Tafel_Grad = NULL;
static INT *Mult_Tafel_Charakteristik = NULL;
static INT **UE_Platz_Mult_Speicher = NULL;
static INT Mult_Tafel_Counter = (INT)0;

static int globalno=0;
static INT **Mult_Tafel=NULL;
static FILE *Datei =NULL;     /* UWH */


static INT *Faktor_eins = NULL; /* AK 190802 */
static INT Faktor_eins_size = 0; /* AK 190802 */
static INT *Faktor_zwei = NULL; /* AK 190802 */
static INT Faktor_zwei_size = 0; /* AK 190802 */


static INT getString();
static INT UE_add();
static INT UE_fZeige();
static INT UE_invers();
static INT UE_ist_gleich();
static INT UE_ist_eins();
static INT UE_ist_null();
static INT UE_kgv();
static INT UE_mult();
static INT UE_negativ();
/* static INT UE_sqrt(); */
static INT UE_scan();
static INT UE_hoch();
/* static INT UE_prim(); */
static INT liestracepol();
static INT UE_Random();
static INT UE_order();
static INT UE_Int_Aequivalent();
static INT UE_Platz();
static INT UE_Free();
static INT minimalErw();
static int spezHoch();
static INT spezMult();
static INT spezEinsGGT();
static INT testirrPolynom();
static INT reduzierpoly();

/*
about the datastructure used for finite field elements:

*/
#define UE_IST_NULL(e) \
    { INT i=**e; for (;i>0;i--) if ((*e)[i] != 0) return 0; return 1; }

#define UE_ADDG(a,b) (((a)+(b)) >= Charakteristik ?\
    ((a)+(b))-Charakteristik: (a)+(b))

#define UE_MULTG(a,b) ((a) && (b) ? ((a)*(b)) % Charakteristik : 0 )

#define UE_FREE(a) do { SYM_FREE(*a); *a=NULL; } while(0)

INT ff_anfang()
/* AK 011204 */
{
    INT i;
    for (i=0;i<MAXDEGREE;i++) eins_ip[i]=1;
    for (i=0;i<MAXDEGREE;i++) null_ip[i]=0;
    return OK;
}

/******************************************************************************/
/*      Endliche Koerper   :   Grundkoerperarithmetik                 */
/*                             */
/*                  Verfasser : Ulrich Eidt      */
/*                  Stand    : 04.11.91        */
/******************************************************************************/
static INT * s_ff_ip(a) OP a;
/* AK 180194 */ /* select .. int pointer */
/* returns an INT pointer with vector of coefficients */
/* AK 130704 V3.0 */
{
    return s_o_s(s_v_i(a,1)).ob_INTpointer;
}

INT c_ff_ip(a,b) OP a; INT *b;
{
    OBJECTSELF c;
    c.ob_INTpointer = b;
    c_o_s(s_v_i(a,(INT)1) , c);
    return OK;
}

INT s_ff_ii(a,i) OP a; INT i;
/* at point 0, the degee
   at point 1,...,s_ff_di  the values */
{
    if (i > s_ff_di(a))
        error("s_ff_ii: index too big");
    return * (s_ff_ip(a)+i);
}


static INT UE_addg(a,b) INT a,b;
/* Summation : a,b sind die Summanden (Integerzahlen) */
{
    if (!b)
        return(a);
    if (!a)
        return(b);
    if (a+b>=Charakteristik)
        return(a+b-Charakteristik);
    return(a+b);
}

static INT UE_subg (a,b) INT a,b;/* Subtraktion : a,b sind Integerzahlen */
{
    if (!b)
        return(a);
    if (!a)
        return(Charakteristik-b);
    if (a>=b)
        return(a-b);
    return(Charakteristik+a-b);
}

static INT UE_multg(a,b) INT a,b;
/* Multiplikation : a,b sind Faktoren (Integerzahlen) */
{
    if (a && b)
        return((a*b) % Charakteristik);
    return((INT)0);
}


static INT UE_divg(a,b) INT a,b;/* Division : a,b sind Integerzahlen */
/* UE */
{
    INT j,i,s;
    if (!b)
    {
        error("UE_divg:zero-division ");
        return(ERROR);
    }
    if (!a || b==(INT)1)
        return(a);
    s = a;
    j = b;
    i = Charakteristik-2L;
    while(i>(INT)0)
    {
        while(!i % 2L)
        {
            i /= 2L;
            j =(j*j) % Charakteristik;
            if (j==(INT)1)
                return(s);
        }
        i--;
        s = (s*j) % Charakteristik;
    }
    return(s);
}


/******************************************************************************/
/* Gaussalgorithmen : Algorithmen fuer Gleichungssystemloesung            */
/*                                                         */
/*                                   Verfasser : Ulrich Eidt      */
/*                                   Stand    : 07.11.91        */
/******************************************************************************/

/******************************************************************************/
/* Funktion gausszerlegu fuehrt die Dreieckszerlegung PA = LR durch         */
/* Uebergabeparameter : Mat  : ist die Matrix                         */
/*                 n   : Dimension der Matrix                     */
/*                 P   : Platz fuer Permutationsvektor              */
/*                                                         */
/* Rueckgabeparameter : 0 falls Matrix singulaer                       */
/*                 1 falls Zerlegung erfolgreich durchgefuehrt         */
/*                                                         */
/* Bemerkungen : - Die Eintraege der Matrix Mat sind Zeile fuer Zeile von oben*/
/*              nach unten in Mat eingetragen.                     */
/*            - Die Funktionen add,sub,mult,div werden verwendet.        */
/*              Diese stehen in EndlArithmet.c                     */
/******************************************************************************/
static INT gausszerlegu(Mat,n,P) INT **Mat; INT n; INT *P;
{ 
    INT i,j,k=(INT)0,StellePermutation,Zwischenspeicher;
/*
    { INT ii,jj; printf("(1)\n"); for (ii=0;ii<n;ii++)
    { for (jj=0;jj<n;jj++) printf("%ld ",Mat[ii][jj]); printf("\n"); }}
*/

    for (k=(INT)0;k<n;k++)
    {

        /* Sollte ein Eintrag = 1 sein, dann sind wir optimal */
        /*  ansonsten nehmen wir den ersten Eintrag <> 0     */
        StellePermutation = -1;
        for (i=k;i<n;i++)
            if (Mat[i][k] == 1)
            {
                StellePermutation = i;
                i = n+1;
            }
        if (StellePermutation < 0)
            for (i=k;i<n;i++)
                if (Mat[i][k] > 0)
                {
                    StellePermutation = i;
                    i = n+1;
                }

        /* Falls kein Eintrag <> 0 : Abbruch da Matrix singulaer */
        if (StellePermutation < (INT)0)
        {
/*
    { INT ii,jj; printf("(2)\n"); for (ii=0;ii<n;ii++)
    { for (jj=0;jj<n;jj++) printf("%ld ",Mat[ii][jj]); printf("\n"); }}
*/
            
            return((INT)0);
        }

        /* Permutation speichern */
        P[k] = StellePermutation;

        /* Vertauschung falls notwendig */
        if (StellePermutation > k)
            for (j=(INT)0;j<n;j++)
            {
                Zwischenspeicher = Mat[k][j];
                Mat[k][j] = Mat[StellePermutation][j];
                Mat[StellePermutation][j] = Zwischenspeicher;
            }

        /* Berechnung von L */
        Zwischenspeicher = Mat[k][k];
        if (Zwischenspeicher != (INT)1)
        {
            Zwischenspeicher = UE_divg((INT)1,Zwischenspeicher);
            for (i=k+(INT)1;i<n;i++)
                Mat[i][k] = UE_MULTG(Mat[i][k],Zwischenspeicher);
        }

        /* Spaltenweise Berechnung der Untermatrix */
        for (j=k+(INT)1;j<n;j++)
        {
            Zwischenspeicher = Mat[k][j];
            for (i=k+(INT)1;i<n;i++)
                Mat[i][j] = UE_subg(Mat[i][j],UE_MULTG(Mat[i][k],                              Mat[k][j]));
        }
    }
    if (!Mat[n-1][n-1])
        {
        return((INT)0);
        }

    return((INT)1);
}



/******************************************************************************/
/* Funktion gaussaufloes berechnet die Loesung des Gleichungssystems :    */
/*                  LRx = Pb                                 */
/* Uebergabeparameter : Mat  : ist die Matrix mit den Informationen zu L und R*/
/*                 n   : Dimension der Matrix                  */
/*                 b   : rechte Seite des Permutationsvektors       */
/*                 P   : Permutationsvektor                     */
/*                                                         */
/* Bemerkungen : - Die Funktion ist ohne Rueckgabeparameter.            */
/*            - Der Vektor b enthaelt nach der Aktion das Ergebnis      */
/*         - Die Funktionen UE_addg,UE_subg,UE_multg,UE_divg werden verwendet. */
/******************************************************************************/
static INT gaussaufloes(Mat,n,b,P) INT **Mat, n, *b, *P;
{
    INT i,k=0,Zwischenspeicher;

    /* b := Pb */
    for (k=(INT)0;k<n-(INT)1;k++)
        if (k<P[k])
        {
            Zwischenspeicher = b[k];
            b[k] = b[P[k]];
            b[P[k]] = Zwischenspeicher;
        }

    /* b := L^-1b */
    for (k=(INT)0;k<n-(INT)1;k++)
        for (i=k+(INT)1;i<n;i++)
            b[i] = UE_subg(b[i],UE_MULTG(Mat[i][k],b[k]));

    /* b := R^-1b */
    for (k=n-(INT)1;k>=(INT)0;k--)
    {
        b[k] = UE_divg(b[k],Mat[k][k]);
        for (i=(INT)0;i<=k-(INT)1;i++)
            b[i] = UE_subg(b[i],UE_MULTG(Mat[i][k],b[k]));
    }
    return OK;
}


/******************************************************************************/
/* Funktion reduzierpoly fuehrt die Reduktion eines Polynoms modulo eines    */
/* anderen durch. Funktion nur fuer endliche Koerper verwendbar.           */
/*                                */
/* Bemerkungen : - Funktion ohne Rueckgabeparameter.              */
/*            - Polynome werden in Potenzaufsteigender Reihenfolge       */
/*              sortiert, beginnend bei 0. ZB. Pol = x^2 + x + 3  wird   */
/*              uebergeben als : Pol[0] = 3, Pol[1] = 1, Pol[3] = 1.     */
/*            - ReduzierPolynom wird als normiert vorrausgesetzt, dh. in   */
/*              der Funktion wird der Koeffizient der hoechsten Potenz   */
/*              automatisch als 1 angenommen.                      */
/*            - Polynom wird in der Funktion geaendert und enthaelt      */
/*              beim Abschluss der Funktion das reduzierte Polynom.      */
/*            - die Funktionen UE_multg,UE_addg,UE_subg werden verwendet.    */
/*                                */
/*               Autor : Ulrich Eidt           */
/*               Stand : 04.11.91           */
/******************************************************************************/
static INT reduzierpoly(Polynom,Grad,ReduzierPolynom,GradReduzierPol)

    INT *Polynom;       /* enthaelt das Polynom vor Reduktion       */
    INT Grad;          /* Grad des Polynoms vorher               */
    INT *ReduzierPolynom; /* Polynom nach dem reduziert wird         */
    INT GradReduzierPol;  /* Grad des Polynoms nach dem reduziert wird  */

{
    INT Polynomzeiger, i, Stelle, Faktor;

    /* falls Grad < GradReduzierPol ohne Aenderung zurueck   */
    if (Grad < GradReduzierPol)
    {
        return OK;
    }
    Polynomzeiger = Grad;

    /* Reduzieren, solange der Grad reduzierten Polynoms < Grad ReduzierPolynoms */
    while (Polynomzeiger >= GradReduzierPol)
    {
        Faktor = Polynom[Polynomzeiger];

        /* Reduzierung nur noetig, falls der Koeffizient <> 0         */
        if (Faktor)
        {
            Polynom[Polynomzeiger] = (INT)0;
            for (i=(INT)0;i<GradReduzierPol;i++)
            {
                Stelle = Polynomzeiger+i-GradReduzierPol;

                /* Hier findet die Reduktion statt   */
                Polynom[Stelle] = UE_subg(Polynom[Stelle],                                 UE_MULTG(Faktor,
                    ReduzierPolynom[i]));
            }
        }
        Polynomzeiger--;
    }
    return OK;
}


INT ff_ende()
/* AK 170393 */
{
    INT i;
    if (Mult_Tafel_Grad != NULL)
    { 
    SYM_free((char *) Mult_Tafel_Grad); 
    Mult_Tafel_Grad=NULL; 
    }

    if (Mult_Tafel_Charakteristik != NULL)
    { 
    SYM_free((char *) Mult_Tafel_Charakteristik); 
    Mult_Tafel_Charakteristik=NULL; 
    }

    if (Mult_Tafel_Speicher != NULL)
    { 
    for (i=0;i<Mult_Tafel_Counter; i++)
        SYM_free((char*) Mult_Tafel_Speicher[i]);
    SYM_free((char *) Mult_Tafel_Speicher); 
    Mult_Tafel_Speicher=NULL; 
    }

    if (UE_Platz_Mult_Speicher != NULL)
    { 
    for (i=0;i<Mult_Tafel_Counter; i++)
        SYM_free((char*) UE_Platz_Mult_Speicher[i]);
    SYM_free((char *) UE_Platz_Mult_Speicher); 
    UE_Platz_Mult_Speicher=NULL; 
    }

    Mult_Tafel=NULL;
    UE_Platz_Mult=NULL;

    if (Faktor_eins != NULL) { SYM_free(Faktor_eins); Faktor_eins=NULL; }
    Faktor_eins_size = 0;
    if (Faktor_zwei != NULL) { SYM_free(Faktor_zwei); Faktor_zwei=NULL; }
    Faktor_zwei_size = 0;
    return OK;
}

static INT insert_mt() /* AK 070294 */
/* fuegt in globalen speicher ein */
{
    Mult_Tafel_Counter++;
    if (Mult_Tafel_Counter > 1) {
    Mult_Tafel_Speicher = (INT ***) SYM_realloc(Mult_Tafel_Speicher, 
        sizeof(INT**)* Mult_Tafel_Counter);
    Mult_Tafel_Grad = (INT *) SYM_realloc(Mult_Tafel_Grad, 
        sizeof(INT)* Mult_Tafel_Counter);
    Mult_Tafel_Charakteristik = (INT *) SYM_realloc(Mult_Tafel_Charakteristik, 
        sizeof(INT)* Mult_Tafel_Counter);
    UE_Platz_Mult_Speicher = (INT **) SYM_realloc(UE_Platz_Mult_Speicher, 
        sizeof(INT*)* Mult_Tafel_Counter);
    }
    else {
    Mult_Tafel_Speicher = (INT ***) SYM_malloc( 
        sizeof(INT**)* Mult_Tafel_Counter);
    Mult_Tafel_Grad = (INT *) SYM_malloc( 
        sizeof(INT)* Mult_Tafel_Counter);
    Mult_Tafel_Charakteristik = (INT *) SYM_malloc( 
        sizeof(INT)* Mult_Tafel_Counter);
    UE_Platz_Mult_Speicher = (INT **) SYM_malloc( 
        sizeof(INT*)* Mult_Tafel_Counter);
    }
    Mult_Tafel_Speicher[Mult_Tafel_Counter-1] = Mult_Tafel;
    Mult_Tafel_Grad[Mult_Tafel_Counter-1] = UE_Erw_Grad;
    Mult_Tafel_Charakteristik[Mult_Tafel_Counter-1] = Charakteristik;
    UE_Platz_Mult_Speicher[Mult_Tafel_Counter-1] = UE_Platz_Mult;
    return OK;
}
 
/******************************************************************************/
/* Funktion erzmulttafel berechnet die Multiplikationstafel fuer die        */
/* Normalbasis.                                                */
/*                                                         */
/* Uebergabeparameter :                                          */
/*  - Erweiterungsgrad :  Gibt den gewuenschten Erweiterungsgrad an         */
/*  - zweitAufruf       :  1=Aufruf aus erzeugePol, 0 normaler Aufruf       */
/*                        -1=Aufruf aus erzeugePol mit Tracepolynombergabe */
/*  - Tracepolynom      :  Tracepolynom, falls bueergeben                    */
/*                                                         */
/* Rueckgabeparameter : 0 falls Tafel nicht erzeugt werden konnte.         */
/*                 1 sonst.                                   */
/*                                                         */
/* Bemerkungen:                                                */
/*            - Funktionen, die benutzt werden (also eingebunden sein     */
/*              muessen) :                                    */
/*               liestracepol    : aufgerufen von erzmulttafel()      */
/*                              zu finden in LiesTracePol.c        */
/*               reduzierpoly    : aufgerufen von erzmulttafel()      */
/*                              zu finden in ReduzierPoly.c        */
/*               gausszerlegu    : aufgerufen in erzmulttafel()       */
/*                              zu finden in GaussAlgorit.c        */
/*               gaussaufloes    : aufgerufen in erzmulttafel()       */
/*                              zu finden in GaussAlgorit.c        */
/*        UE_addg,UE_subg,UE_multg,UE_divg : aufgerufen von reduzierpoly(),      */
/*                              gausszerlegu()                 */
/*                              zu finden in EndlArithmet.c        */
/*                                                         */
/* Zur Implementierung:                                          */
/*  Zunaechst wird das Tracecompatible Polynom eingelesen, und falls dies    */
/*   erfolgreich war die noetigen Speicherbelegungen durchgefuehrt.         */
/*                                                         */
/*  Dann wird die Normalbasis in der Polynomialen Basis ermittelt und sowohl  */
/*   in Tafel als auch in Gaussmatrix abgespeichert. Dafuer wird immer in    */
/*   Grosspolynom das letzte Basiselement^Erweiterungsgrad (= Frobeniushomom.)*/
/*   eingelesen und nach Tracepolynom reduziert.                       */
/*                                                         */
/*  Mit Gausszerlegu() wird die Basistransformation (Gleichungssystem)      */
/*   Polynomialbasis -> Normalbasis ermoeglicht.                       */
/*                                                         */
/*  Diese Transformation wird auf die gewuenschten x - Potenzen in Polynomial-*/
/*   basis angewendet, die man erhaelt, indem die in Tafel abgespeicherten   */
/*   Polynome mit x multipliziert, und dann reduziert.                  */
/*                                                         */
/*                                 Autoer : Ulrich Eidt         */
/*                                 Stand  : 05.11.91            */
/******************************************************************************/

#define FASTCHECKMULTTAFEL(grad) \
/* AK 221104 V3.0 */ \
do { \
   INT i; \
   for (i=0, Mult_Tafel =NULL ;i<Mult_Tafel_Counter; i++) \
        if ((grad == Mult_Tafel_Grad[i]) && \
            (Charakteristik == Mult_Tafel_Charakteristik[i])) \
            { \
            Mult_Tafel = Mult_Tafel_Speicher [i]; \
            UE_Erw_Grad = grad; \
            } \
   } while(0)

static INT erzmulttafel(Erweiterungsgrad,zweitAufruf,para_Tracepolynom)
    INT Erweiterungsgrad;
    INT zweitAufruf;   /* UWH */
                    /* 1 heisst ja, 0 heisst nein, -1 heisst
                    ja mit bergabe von Tracepolynom */
    INT *para_Tracepolynom; /* UWH */
/* Tracecompatibles Polynom        */
{
    INT *Gaussmatrix;  /* Matrix fuer Basistransformation             */
    INT **Gau;       /* Zeigersystem fuer Gaussmatrix               */
    INT *Grosspolynom; /* Platz fuer Polynome mit Grad > Erweiterungsgrad */
    INT Grosspolzeiger;/* Hilfszeiger fuer Grosspolynom               */
    INT Gradgrosspol;  /* Gibt den Grad von Grosspolynom an            */
    INT *Tracepolynom; /* Tracecompatibles Polynom                  */
    INT *Permutation;  /* Permutationsvektor bei Gleichungssystemloesung  */
    INT i,j;         /* Laufvariable                          */
    INT *ax;
    int k;

#ifdef UNDEF
    Mult_Tafel=NULL;
    /* schaue ob schon von frueher da AK 070294 */
    for (i=0;i<Mult_Tafel_Counter; i++)
        {
        if ((Erweiterungsgrad == Mult_Tafel_Grad[i]) &&
            (Charakteristik == Mult_Tafel_Charakteristik[i]))
            {
            Mult_Tafel = Mult_Tafel_Speicher [i];
            UE_Erw_Grad = Erweiterungsgrad;
            return OK;
            }
        }
#endif
    FASTCHECKMULTTAFEL(Erweiterungsgrad);
    if (Mult_Tafel != NULL) return OK;
    
    /* also noch nicht frueher berechnet */

    if (UE_Erw_Grad && !zweitAufruf)  /* UWH */
        Erweiterungsgrad = UE_kgv(UE_Erw_Grad,Erweiterungsgrad);

    /* Tracecompatibles Polynom wird eingelesen, 
       falls nicht moeglich Zurueck */
    /* falls moeglich Speicher freimachen                            */

    if (zweitAufruf>=0)    /* UWH */
    {                   /* UWH */
        Tracepolynom = (INT *) SYM_calloc(Erweiterungsgrad,sizeof(INT));
        if (liestracepol(Erweiterungsgrad,Tracepolynom,zweitAufruf) != OK) /* UWH */
        {
            SYM_free((char *) Tracepolynom);
            return error("ff.c: internal error FF-41");
            /* printf("Tracecompatibles Polynom nicht beschaffbar!\n"); */
        }                /* UWH */
    }
    else 
        Tracepolynom = para_Tracepolynom; /* AK 040294 */

    /* Bestehende Tafeln freimachen, falls nicht Aufruf aus erzeugePol */
    for (i=0;i<Mult_Tafel_Counter; i++)
        {
        if (Erweiterungsgrad == Mult_Tafel_Grad[i] &&
            Charakteristik == Mult_Tafel_Charakteristik[i])
            {
            Mult_Tafel = Mult_Tafel_Speicher [i];
            UE_Erw_Grad = Erweiterungsgrad;
            if (zweitAufruf>=0)    /* UWH */
                SYM_free((char *) Tracepolynom);
            return OK;
            }
        }
    UE_Platz_Mult = (INT *) UE_malloc(Erweiterungsgrad
                                      *Erweiterungsgrad*
                                      sizeof(INT));

    /* Abspeichern der jeweiligen Zeilenanfaenge der Matrix, 
       um Multiplikationen */
    /*  bei der Addressierung zu vermeiden */
    Mult_Tafel = (INT **) UE_malloc(Erweiterungsgrad*sizeof(INT*));

    k=(INT)0;
    for (i=(INT)0;i<Erweiterungsgrad;i++)
    {
        Mult_Tafel[i] = & UE_Platz_Mult[k];
        k += Erweiterungsgrad;
    }
    

    if (Erweiterungsgrad == (INT)1)
    {
        if (zweitAufruf>=0) SYM_free((char *) Tracepolynom);
        Mult_Tafel[0][0] = (INT)1;
        UE_Erw_Grad = (INT)1;
        insert_mt();
        return(OK);
    }

    Grosspolynom = (INT *) SYM_calloc(Erweiterungsgrad*Charakteristik,                          sizeof(INT));
    Gaussmatrix = (INT *) UE_malloc(Erweiterungsgrad*Erweiterungsgrad*                        sizeof(INT));
    Permutation = (INT *) UE_malloc(Erweiterungsgrad*sizeof(INT));

    /* Abspeichern der jeweiligen Zeilenanfaenge der Matrix, 
       um Multiplikationen */
    /*  bei der Addressierung zu vermeiden */
    Gau = (INT **) UE_malloc(Erweiterungsgrad*sizeof(INT*));
    k=(INT)0; 
    ax = Gaussmatrix;
    for (i=(INT)0;i<Erweiterungsgrad;i++)
    {
        Gau[i] = ((INT *)Gaussmatrix) + (int)k;
        ax = Gaussmatrix;
        for (j=0;j<k;j++)
            ax = ax++;
        k += (int)Erweiterungsgrad;
    }

    /* Initialisierung der Gaussmatrix und Zwischenspeichern der Potenzen */
    for (i=(INT)0;i<Erweiterungsgrad;i++)
    {
        (Gau[i])[0] = (INT)0;
        Mult_Tafel[0][i] = (INT)0;
    }
    Gau[1][0] = (INT)1;
    Mult_Tafel[0][1] = (INT)1;
    for (i=(INT)1;i<Erweiterungsgrad;i++)
    {
        for (j=0;j<Erweiterungsgrad;j++) Grosspolynom[j] = 0;
        Grosspolzeiger = (INT)0;
        for (j=0;j<Erweiterungsgrad;j++)
        {

            /* Grosspolynom = letztes Polynom ^ Charakteristik (Frobenius)*/
            if (Gau[j][i-1])
            {
                Grosspolynom[Grosspolzeiger] = Gau[j][i-1];
                Gradgrosspol = Grosspolzeiger;
            }
            Grosspolzeiger += Charakteristik;
        }

        /* Grosspolynom wird nach Tracepolynom reduziert und abgespeichert */
        reduzierpoly(Grosspolynom,Gradgrosspol,Tracepolynom,                      Erweiterungsgrad);

        for (j=0;j<Erweiterungsgrad;j++)
        {
            Gau[j][i] = Grosspolynom[j];
            Mult_Tafel[i][j] = Grosspolynom[j];
        }
    }

    /* Gaussdreieckszerlegung */
    if(!gausszerlegu(Gau,Erweiterungsgrad,Permutation))
    {
        error("ff.c: internal error FF6");
        SYM_free((char *) Gaussmatrix);
        SYM_free((char *) Grosspolynom);
        if (zweitAufruf>=0)    /* UWH */
            SYM_free((char *) Tracepolynom);
        SYM_free((char *) Permutation);
        SYM_free((char *) Gau);
        error("internal error FF200");
        return ERROR;
    }

    /* Berechnung der Tafeleintraege von x*x^(p^i) in der Normalbasis */
    for (i=(INT)0;i<Erweiterungsgrad;i++)
    {

        /* Grosspolynom wird belegt mit x*x^(p^i) in Polynomialbasis */
        Grosspolynom[0] = (INT)0;
        for (j=(INT)0;j<Erweiterungsgrad;j++)
            Grosspolynom[j+1] = Mult_Tafel[i][j];

        /* Grosspolynom wird reduziert und der Basiswechsel durchgefuehrt */
        reduzierpoly(Grosspolynom,Erweiterungsgrad,Tracepolynom,                   Erweiterungsgrad);
        gaussaufloes(Gau,Erweiterungsgrad,Grosspolynom,                     Permutation);

        /* Abschliessend wird das Ergebnis gespeichert */
        for (j=(INT)0;j<Erweiterungsgrad;j++)
            Mult_Tafel[i][j] = Grosspolynom[j];
    }

    /* Speicher wieder freigeben */
    SYM_free((char *) Gaussmatrix);
    SYM_free((char *) Grosspolynom);
    if (zweitAufruf>=0)    /* UWH */
        SYM_free((char *) Tracepolynom);
    SYM_free((char *) Permutation);
    SYM_free((char *) Gau);
    UE_Erw_Grad = Erweiterungsgrad;

    insert_mt();
    return OK;
}



/******************************************************************************/
/* Funktion UE_kgv berechnet das kleinste gemeinsame Vielfache von zwei       */
/*           Integerzahlen.                                    */
/******************************************************************************/
static INT UE_kgv(a,b) INT a,b;
{
    INT c,d;
    if (a==1) return b;
    if (b==1) return a;
    c = a;
    d = b;
    while(c && d)
    {
        c = c % d;
        if(c)
            d = d % c;
    }
    if(c)
        return(a*b/c);
    else
        return(a*b/d);
}



#ifdef UNDEF
/******************************************************************************/
/* Funktion UE_sqrt berechnet die abgerundete integer-Wurzel einer Integerzahl*/
/******************************************************************************/
static INT UE_sqrt(x) INT x;
{
    INT i;
    if (x==(INT)0)
        return((INT)0);
    for (i=(INT)1;i<x;i++)
        if (i*i > x)
            return(i-(INT)1);
    return((INT)1);
}

#endif

/******************************************************************************/
/* Funktion UE_power berechnet die y-te Potenz von x                      */
/******************************************************************************/
static INT UE_power(x,y) INT x,y;
{
    INT i, s = (INT)1;
    for (i=(INT)0;i<y;i++)
        s *= x;
    return(s);
}



#ifdef UNDEF
/******************************************************************************/
/* Funktion UE_prim prueft, ob p eine Primzahl ist.                       */
/* Rueckgabewert: 1, falls p Primzahl, 0 sonst.                        */
/******************************************************************************/
static INT UE_prim(p)
INT p;
{
    INT i, s;

    s = UE_sqrt(p);
    if (p < 2L)
        return((INT)0);
    if (p > 2 && ((p % 2L) == (INT)0))
        return((INT)0);
    else
    {
        for (i=3L;i<=s;i+=2L)
        {
            if ((p % i) == (INT)0)
                return((INT)0);
        }
    }
    return((INT)1);
}

#endif

/******************************************************************************/
/*                  FUNKTIONEN FUER ENDLICHE KOERPER                */
/* Die folgenden Funktionen stellen eine Arithmetik fuer endliche Koerper in  */
/* Normalbasenrepraesentation dar. Ein Koerperelement wird wie folgt        */
/* abgespeichert:                                              */
/*   e[0] enthaelt den Erweiterungsgrad, die weiteren <e[0]>     */
/*   Stellen die Eintraege des es bezueglich der entsprechenden       */
/*   Normalbasis.  e[0] = 0 ist gleichbedeutend mit 'nicht definiert'.  */
/*                                                         */
/*                  Verfasser : Ulrich Eidt      */
/*                  Stand    : 04.11.91        */
/******************************************************************************/

/******************************************************************************/
/* Funktion minimalErw stellt den Koerper mit dem kleinsten Erweiterungsgrad  */
/* fest, in dem ein e enthalten ist. Ist dieser kleiner als e[0]  */
/* so wird die Speicherung des ees auf den kleinsten moeglichen Erwei-  */
/* terungsgrad angepasst.                                        */
/* Ein e ist genau dann aus einem Unterkoerper, wenn fuer einen Teiler  */
/* m des Erweiterungsgrades sich die Eintraege immer nach m Eintraegen wieder-*/
/* holen.                                                    */
/******************************************************************************/
static INT minimalErw(e) INT **e;
{
    INT i,j,maximum=(*e)[0]/2L,Grad=(*e)[0],minGrad=(INT)0;
    INT erfolgreich;
    /* falls nicht definiert keine Aenderungen */
    if ((*e)[0] == 0) return OK;

    /* Teiler suchen nur bis zum maximalen Teiler  */
    while(minGrad<=maximum)
    {
        minGrad++;
        /* Nur Teiler muessen ueberprueft werden */
        if (!(Grad % minGrad))
        {
            erfolgreich = 1;
            for (i=minGrad;i<Grad;i+=minGrad)
                for (j=(INT)1;j<=minGrad;j++)
                    if ((*e)[j] != (*e)[i+j])
                    {
    /* Keine Wiederholung -> minGrad nicht der minimale Erweiterungsgrad */
                        erfolgreich = 0;
                        j = minGrad+(INT)1;
                        i = Grad;
                    }
            if (erfolgreich) { **e = minGrad; goto endeme; }
        }
    }
endeme:
    return OK;
}

INT s_ff_ci(a) OP a;
/* AK 080306 V3.0 */
/* select finite field characteristik as INT */
{
    return S_V_II(a,0);
}

OP s_ff_c(a) OP a;
/* AK 080306 V3.0 */
/* select finite field characteristik */
{
    return S_V_I(a,0);
}

INT s_ff_di(a) OP a;
/* select finite field degree as INT */
/* AK 130704 V3.0 */
{ 
    return S_FF_II(a,0); 
}




INT copy_ff(a,b) OP a,b;
/* AK 100393 */
/* AK 221104 V3.0 */
{
    INT erg = OK;
    {
    OBJECTSELF ma,mb;
    INT al,i;
    init_ff(b);
    COPY(S_FF_C(a),S_FF_C(b)); /*characteristic*/
    COPY(S_FF_ME(a),S_FF_ME(b)); /* minimal extension ??*/
    ma = S_O_S(S_V_I(a,1));
    al =  *(S_O_S(S_V_I(a,1)).ob_INTpointer); 
    UE_Erw_Grad=al;
    mb.ob_INTpointer = (INT *) UE_malloc((al+1) * sizeof(INT)); 
    for (i=0;i<=al;i++)
        *(mb.ob_INTpointer+i) = *(ma.ob_INTpointer+i);
    C_O_S(S_V_I(b,1),mb); 
    }
    ENDR("copy_ff");
}

INT scan_ff(a) OP a;
{
    OP b;
    INT erg = OK;
    b = callocobject();
    printeingabe("Enter the Characteristik of the finite field");
    erg += scan(INTEGER,b);
    Charakteristik = S_I_I(b);
    erg += init_ff(a); /* AK 160594 */
    erg += copy(b,S_FF_C(a));
    erg += UE_scan(& S_FF_IP(a));
    erg += freeall(b);
    ENDR("scan_ff");
}

/******************************************************************************/
/* Funktion UE_scan uebernimmt das Einlesen der Koerperelemente            */
/*                                                         */
/* Struktur : 0-te Stelle enthaelt den Grad der Koerpererweiterung         */
/*         Die darauffolgenden <Grad> Stellen enthalten das e      */
/******************************************************************************/
static INT UE_scan(Koerperzeiger) INT **Koerperzeiger;
{
    INT i,j=(INT)0,ZeichenZeiger = (INT)1,*Koerperelement;
    char *Zeichen;
    Koerperelement = *Koerperzeiger;
    Zeichen = (char *) SYM_calloc(500,sizeof(char));
    printeingabe("input of a finite field element");
    printeingabe("degree of extension");
    scanf("%ld",&i);
    SYM_free((char *) Koerperelement);
    Koerperelement = (INT *) UE_malloc((i+1)*sizeof(INT));
    *Koerperzeiger = Koerperelement;
    for (j=(INT)0;j<=i;j++)
        Koerperelement[j] = (INT)0;
    fprintf(stderr,"input   of %ld entries, seperated by comma",i);
    fprintf(stderr,"\nmissing entries are 0\n");
    scanf("%s",Zeichen);
    j = (INT)1;
    ZeichenZeiger = (INT)0;
    while (j<=i)
    {
        /* 44 = 'Komma' */
        while (Zeichen[ZeichenZeiger]!=44 && Zeichen[ZeichenZeiger]!=0)
        {
            Koerperelement[j] = Koerperelement[j] * 10 +
                Zeichen[ZeichenZeiger] - 48;
            ZeichenZeiger++;
        }
        ZeichenZeiger++;
        j++;
    }
    for (j=(INT)1;j<=i;j++)
        Koerperelement[j] %= Charakteristik;
    Koerperelement[0] = i;
    UE_Erw_Grad  = i;
    /* minimalErw(Koerperzeiger); */
    SYM_free(Zeichen); /* AK 051093 */
    return OK;
}



/******************************************************************************/
/* Funktion UE_Platz stellt ein undefiniertes Koerperelement bereit.         */
/******************************************************************************/
static INT UE_Platz(Koerperzeiger) INT **Koerperzeiger;
{
    if (UE_Erw_Grad < 0)
        {
        error("ff.c: internal error FF331");
        }
    *Koerperzeiger = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
    (*Koerperzeiger)[0] = (INT)0;
    return OK;
}

static INT UE_Free(a) INT **a; /* AK 060294 */
{
    SYM_free(*a);
    *a = NULL;    
    return OK;
}


#ifdef UNDEF
/******************************************************************************/
/* Funktion UE_Zeige gibt ein Koerperelement auf dem Bildschirm aus.        */
/******************************************************************************/
static INT UE_Zeige(Koerperzeiger) INT **Koerperzeiger;
{
    return UE_fZeige(stdout,Koerperzeiger);
}
#endif

/******************************************************************************/
/* Funktion UE_fZeige gibt ein Koerperelement auf f aus.                 */
/******************************************************************************/
static INT UE_fZeige(f,Koerperzeiger) INT **Koerperzeiger; FILE *f;
/* AK 201204 V3.0 */
{
    INT i,*Koerperelement;
    if ((*Koerperzeiger)[0] == (INT)0)
    {
        return error("ff.c: internal error FF1");
    }
    /* minimalErw(Koerperzeiger); */
    Koerperelement = *Koerperzeiger;
    for (i=(INT)1;i<Koerperelement[0];i++)
        {
        fprintf(f,"%ld,",Koerperelement[i]);
        if (f == stdout) {
            zeilenposition += (intlog_int(Koerperelement[i])+1);
            }
        }
    fprintf(f,"%ld",Koerperelement[Koerperelement[0]]);
    if (f == stdout) {
        zeilenposition += intlog_int(Koerperelement[Koerperelement[0]]);
        }

    return OK;
}

#endif /* FFTRUE */

INT comp_ff(a,b) OP a,b;
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"comp_ff(1)",a);
    CTO(FF,"comp_ff(2)",b);
    SYMCHECK (S_FF_CI(a) != S_FF_CI(b), "comp_ff:different characteristic");
    {
#ifdef FFTRUE
    INT res,res2;

    if (S_FF_DI(a) == S_FF_DI(b)) {
        INT i;
        for (i=1;i<=S_FF_DI(a);i++)
             if (S_FF_II(a,i) != S_FF_II(b,i)) {
                 res = S_FF_II(a,i)-S_FF_II(b,i);
                 goto re;
                 }
        res=0;
        }
    else if (S_FF_DI(a)==1) /* AK 180607 */
	{
	INT i;
        for (i=1;i<=S_FF_DI(b);i++)
	     if (S_FF_II(a,1) != S_FF_II(b,i)) {
                 res = S_FF_II(a,1)-S_FF_II(b,i);
                 goto re;
                 }
        res=0;
	}
    else if (S_FF_DI(b)==1) /* AK 180607 */
        {
        INT i;
        for (i=1;i<=S_FF_DI(a);i++)
             if (S_FF_II(a,i) != S_FF_II(b,1)) {
                 res = S_FF_II(a,i)-S_FF_II(b,1);
                 goto re;
                 }
        res=0;
        }
    else /* if the expansion degree different */
        res= UE_ist_gleich(& S_FF_IP(a), & S_FF_IP(b));
re:
    return res;
#endif /* FFTRUE */
    }
    ENDR("comp_ff");
}

INT addinvers_apply_ff(a) OP a;
/* AK 160393 */
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"addinvers_apply_ff(1)",a);
    {
#ifdef FFTRUE
    erg += UE_negativ(& S_FF_IP(a), & S_FF_IP(a));
#endif
    }
    ENDR("addinvers_apply_ff");
}

INT invers_apply_ff(a) OP a;
/* AK 190707 V3.0 */
{
    INT erg = OK;
    CTO(FF,"invers_apply_ff(1)",a);
    {
#ifdef FFTRUE
    erg += UE_invers(& S_FF_IP(a), & S_FF_IP(a));
#endif
    }
    ENDR("invers_apply_ff");
}


INT null_ff_given_q(q,b) OP b; OP q;
/* builds the zero element in the finite field with q elements */
/* AK 020304 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"null_ff_given_q(1)",q);
    SYMCHECK(S_I_I(q) < 2,"null_ff_given_q:q<2");
    {
#ifdef FFTRUE
    OP v;
    INT i,*ip;
    v = CALLOCOBJECT();
    erg += factorize_integer(q,v);
    if (S_V_II(v,0)!=S_V_II(v,S_V_LI(v)-1))
        {
        erg += error("null_ff_given_q:q no prime power");
        FREEALL(v);
        goto endr_ende;
        }
    Charakteristik=S_V_II(v,0);
    UE_Erw_Grad=S_V_LI(v);
    erg += init_ff(b); ip = S_FF_IP(b);
    for (i=0;i<UE_Erw_Grad;i++) ip[i+1]=0;
    ip[0]=UE_Erw_Grad;
    M_I_I(Charakteristik,S_FF_C(b));
    erg += erzmulttafel(UE_Erw_Grad,(INT)0,NULL); /* UWH */
    FREEALL(v);
#endif
    }
    ENDR("null_ff_given_q");
}

INT eins_ff_given_q(q,b) OP b; OP q;
/* builds the unit element in the finite field with q elements */
/* AK 020304 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"eins_ff_given_q(1)",q);
    SYMCHECK(S_I_I(q) < 2,"eins_ff_given_q:q<2");
    {
#ifdef FFTRUE
    OP v;
    INT i,*ip;
    v = CALLOCOBJECT();
    erg += factorize_integer(q,v);
    if (S_V_II(v,0)!=S_V_II(v,S_V_LI(v)-1))
        {
        erg += error("eins_ff_given_q:q no prime power");
        FREEALL(v);
        goto endr_ende;
        }
    Charakteristik=S_V_II(v,0);
    UE_Erw_Grad=S_V_LI(v);
    erg += init_ff(b); ip = S_FF_IP(b);
    for (i=0;i<UE_Erw_Grad;i++) ip[i+1]=1;
    ip[0]=UE_Erw_Grad;
    M_I_I(Charakteristik,S_FF_C(b));
    erg += erzmulttafel(UE_Erw_Grad,(INT)0,NULL); /* UWH */
    FREEALL(v);
#endif
    }
    ENDR("eins_ff_given_q");
}


INT random_ff_given_q(q,b) OP b; OP q;
/* AK 020304 */
/* random element with given field size q */
/* AK 210704 V3.0 */ /* AK 211106 V3.1 */ 
{
    INT erg = OK;
    CTO(INTEGER,"random_ff_given_q(1)",q);
    SYMCHECK(prime_power_p(q) ==FALSE,"random_ff_given_q:q no prime power");
    {
#ifdef FFTRUE
    OP v;
    v = CALLOCOBJECT();
    erg += factorize_integer(q,v);
    Charakteristik=S_V_II(v,0);
    UE_Erw_Grad=S_V_LI(v);
    FREEALL(v);
    erg += random_ff(b);
#endif
    }
    CTO(FF,"random_ff_given_q(2e)",b);
    ENDR("random_ff_given_q");
}

INT random_ff(b) OP b;
/* AK 170393 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    {
#ifdef FFTRUE
    if (Charakteristik == (INT)0) /* not yet set */
        Charakteristik = (INT)5;
    if( UE_Erw_Grad==(INT)0)
        UE_Erw_Grad=(INT)9;
    erg += init_ff(b);
    erg += UE_Random( & S_FF_IP(b));
    M_I_I(Charakteristik,S_FF_C(b));
    erg += erzmulttafel(UE_Erw_Grad,(INT)0,NULL); /* UWH */
    SYMCHECK (S_FF_II(b,1) > Charakteristik, "random_ff:internal error 070295");
    SYMCHECK (S_FF_II(b,1) < 0, "random_ff:internal error 170304");
#endif
    }
    ENDR("random_ff");
}

INT random_char_ff(a,b) OP a,b;
/* AK 220294 */
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"random_char_ff(1)",a);
    SYMCHECK(not primep(a),"random_char_ff: no prime");
    {
#ifdef FFTRUE
    Charakteristik = S_I_I(a);
    return random_ff(b);
#endif
    }
    ENDR("random_char_ff");
}


INT addinvers_ff(a,b) OP a,b;
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"addinvers_ff(1)",a);
    {
#ifdef FFTRUE
    Charakteristik = S_FF_CI(a);
    erg += init_ff(b);
    erg += UE_negativ(& S_FF_IP(a), & S_FF_IP(b));
    erg += m_i_i(Charakteristik,S_FF_C(b));
    SYMCHECK (S_FF_II(b,1) > Charakteristik, "addinvers_ff:internal error 070295");
    SYMCHECK (S_FF_II(b,1) < 0, "addinvers_ff:internal error 170304");
#endif
    }
    ENDR("addinvers_ff");
}

INT invers_ff(a,b) OP a,b;
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"invers_ff(1)",a);
    {
#ifdef FFTRUE
    Charakteristik = S_FF_CI(a);
    erg += init_ff(b);
    erg += UE_invers(& S_FF_IP(a), & S_FF_IP(b));
    erg += m_i_i(Charakteristik,S_FF_C(b));
    SYMCHECK (S_FF_II(b,1) > Charakteristik, "invers_ff:internal error 070295");
    SYMCHECK (S_FF_II(b,1) < 0, "invers_ff:internal error 170304");
#endif
    }
    ENDR("invers_ff");
}


INT mult_ff_integer(a,b,c) OP a,b,c;
/* AK 070802 */
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"mult_ff_integer(1)",a);
    CTO(INTEGER,"mult_ff_integer(2)",b);
    CTO(EMPTY,"mult_ff_integer(3)",c);
    {
#ifdef FFTRUE
    OP d;
    d = CALLOCOBJECT();
    COPY_INTEGER(b,d);
    cast_apply_ff(d);
    erg += mult_ff_ff(a,d,c);
    FREEALL(d);
#endif
    }
    ENDR("mult_ff_integer");
}

INT mult_ff_ff(a,b,c) OP a,b,c;
/* AK 070802 */
/* AK 280704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"mult_ff_ff(1)",a);
    CTO(FF,"mult_ff_ff(2)",b);
    if (S_O_K(c) != FF) FREESELF(c);
    CTTO(FF,EMPTY,"mult_ff_ff(3)",c);
    SYMCHECK(S_FF_CI(a) != S_FF_CI(b),"mult_ff_ff:different characteristic");
    {
#ifdef FFTRUE
    Charakteristik = S_FF_CI(a);

    if (S_O_K(c) != FF) 
         erg += init_ff(c);
    else {
         INT *ap,*bp;
         ap =S_FF_IP(a);
         bp =S_FF_IP(c);
         // printf("*ap = %d *bp = %d\n",*ap,*bp);
         if (*ap > *bp)
                 bp = (INT*) SYM_realloc(bp,(S_FF_DI(a)+1)*sizeof(INT));
         bp[0]=*ap;
         C_FF_IP(c,bp);
         M_I_I(0,S_FF_ME(c));
         // println(c);
         }
    M_I_I(Charakteristik,S_FF_C(c));                                                          
    if ((S_FF_DI(a)==1) && (S_FF_DI(b)==1))  /* AK 270705 */
       {
       INT *cp;
       cp = S_FF_IP(c); 
       cp[0]=1; cp[1]=(S_FF_II(a,1)*S_FF_II(b,1)) % Charakteristik;
       } 
    else
        UE_mult(& S_FF_IP(a), & S_FF_IP(b), & S_FF_IP(c) );
    SYMCHECK (S_FF_II(c,1) > Charakteristik, "mult_ff_ff:internal error 070295");
    SYMCHECK (S_FF_II(c,1) < 0, "mult_ff_ff:internal error 170304");
#endif
    }
    ENDR("mult_ff_ff");
}


INT einsp_ff(a) OP a;
{
#ifdef FFTRUE
    if (UE_ist_eins(& S_FF_IP(a)) == (INT)1) return TRUE;
#endif
    return FALSE;
}


INT add_ff(a,b,c) OP a,b,c;
{
    INT erg = OK;
#ifdef FFTRUE
    if (NULLP(b))
        return copy(a,c);
    if (S_O_K(b) != FF) /* AK 230294 */
        cast_apply_ff(b);
    if ((S_O_K(a) != FF)   || (S_O_K(b) != FF))
        return WTT("add_ff",a,b);

    if (S_FF_CI(a) != S_FF_CI(b))
        error("add_ff:different characteristic");
    Charakteristik = S_FF_CI(a);
    erg += init_ff(c);
    erg += UE_add(& S_FF_IP(a), &S_FF_IP(b), &S_FF_IP(c));
    erg += m_i_i(Charakteristik,S_FF_C(c));

    SYMCHECK (S_FF_II(c,1) > Charakteristik, "add_ff:internal error 070295");
    SYMCHECK (S_FF_II(c,1) < 0, "add_ff:internal error 170304");
#endif /* FFTRUE */
    ENDR("add_ff");
}

INT t_INTEGER_FF(a,b,c) OP a,b,c;
/* AK 070394 */ /* AK 091204 V3.0 */
/* a is INTEGER 
   b is INTEGER = Charakteristik 
   c becomes FF */
{
    INT erg = OK;
    CTO(INTEGER,"t_INTEGER_FF(1)",a);
    CTO(INTEGER,"t_INTEGER_FF(2)",b);
    /* CE3(a,b,c,t_INTEGER_FF); AK 200802 */
    {
#ifdef FFTRUE
    INT i;
    Charakteristik = S_I_I(b);
    i = S_I_I(a) % Charakteristik;     /* AK 210802 mod added */
    while (i<0) i += Charakteristik; /* AK 070295 */
    erg += init_ff(c); /* c must not be empty */
    erg += UE_Int_Aequivalent(i, &S_FF_IP(c));
    M_I_I(Charakteristik,S_FF_C(c));
#endif /* FFTRUE */
    }
    ENDR("t_INTEGER_FF");
    
}

INT cast_apply_ff(a) OP a;
/* AK 230294 */
{
    INT erg = OK,i;
#ifdef FFTRUE
    switch (S_O_K(a)) {
        case INTEGER:
            i = S_I_I(a);     
            erg += init_ff(a);
            erg += UE_Int_Aequivalent(i, &S_FF_IP(a));
            erg += m_i_i(Charakteristik,S_FF_C(a));
            break;
        default:
            printobjectkind(a);
            erg += error("cast_apply_ff: transfer not possible");
            break;
        }
    SYMCHECK (S_FF_II(a,1) > Charakteristik, "cast_apply_ff:internal error 070295");
    SYMCHECK (S_FF_II(a,1) < 0, "cast_apply_ff:internal error 170304");
#endif /* FFTRUE */
    ENDR("cast_apply_ff");
}


INT minimal_extension(ff) OP ff;
{
   INT erg = OK;
   CTO(FF,"minimal_extension(1)",ff);
   {
   erg = reduce_ff(ff);
   }
   ENDR("minimal_extension");
}

#ifdef FFTRUE

/******************************************************************************/
/* Funktion UE_add belegt Ergebzeig mit seins+szwei               */
/******************************************************************************/
static INT UE_add(seins,szwei,Ergebzeig) INT **seins; INT **szwei, **Ergebzeig;
{
    INT i,j,k,*Summ1hilf,*Summ2hilf,*Summand_eins,*Summand_zwei,*Ergebnis;
    INT h1=0,h2=0;
    Summand_eins = *seins;
    Summand_zwei = *szwei;
    Ergebnis = *Ergebzeig;


    /* Falls der Grad einer der Summanden nicht Den Erweiterungsgrad teilt, */
    /* Wird eine Koerpererweiterung noetig */
    if (!UE_Erw_Grad ||
        (UE_Erw_Grad % Summand_eins[0]+UE_Erw_Grad%Summand_zwei[0]))
    {
        minimalErw(seins);
        minimalErw(szwei);
    }
    if (!UE_Erw_Grad ||
        (UE_Erw_Grad % Summand_eins[0]+UE_Erw_Grad%Summand_zwei[0]))
        {
        k = UE_kgv(Summand_eins[0],Summand_zwei[0]);
        if ( erzmulttafel(k,(INT)0,NULL) != OK)  /* UWH */
            return error("ff.c:internal error FF70");
        }

    /* ist der Grad einer der Summanden m nicht gleich dem aktuellen Grad, so */
    /* muss eine Einbettung vorgenommen werden, indem man die Koeffizienten   */
    /* (<aktueller Grad> / m)-mal wiederholt.                         */
    if (Summand_eins[0] != UE_Erw_Grad)
    {
        k=1;
        Summ1hilf = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
        h1=1;
        for (i=(INT)0;i<UE_Erw_Grad/Summand_eins[0];i++)
            for (j=(INT)1;j<=Summand_eins[0];j++)
                {
                Summ1hilf[k++] = Summand_eins[j];
                }
    }
    else
        Summ1hilf = Summand_eins;

    if (Summand_zwei[0] != UE_Erw_Grad)
    {
        k=1;
        h2=1;
        Summ2hilf = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
        for (i=0;i<UE_Erw_Grad/Summand_zwei[0];i++)
            for (j=1;j<=Summand_zwei[0];j++)
                Summ2hilf[k++] = Summand_zwei[j];
    }
    else
        Summ2hilf = Summand_zwei;

    /* Der Grad des Ergebniselementes muss korrekt sein */
    if (Ergebnis[0]!=UE_Erw_Grad)
    {
        Ergebnis = (INT *) SYM_realloc(Ergebnis, (UE_Erw_Grad+1)*sizeof(INT));
        Ergebnis[0] = UE_Erw_Grad;
        *Ergebzeig = Ergebnis;
    }

    /* Addition */
    for (i=1;i<=UE_Erw_Grad;i++)
        Ergebnis[i] = UE_ADDG(Summ1hilf[i],Summ2hilf[i]);

    if (h1==1) /* AK 160393 */ SYM_free(Summ1hilf);
    if (h2==1) /* AK 160393 */ SYM_free(Summ2hilf);
    return OK;
}




/******************************************************************************/
/* Funktion UE_mult belegt Ergebzeig mit feins+Fakt2zeig              */
/******************************************************************************/
static INT UE_mult(feins,Fakt2zeig,Ergebzeig) INT **feins, **Fakt2zeig, **Ergebzeig;
{
    INT i,j,k,l,m,*Fakt1hilf,*Fakt2hilf, *Ergebnis,zwisch;

/* AK 190802 */
    if (Faktor_eins == NULL) {
        Faktor_eins_size = 100;
        Faktor_eins = (INT *) UE_malloc(Faktor_eins_size*sizeof(INT));
        }
    else if (Faktor_eins_size < ((*feins)[0]+1)) {
        Faktor_eins_size = ((*feins)[0]+1)+100;
        Faktor_eins = (INT *) UE_realloc(Faktor_eins,Faktor_eins_size*sizeof(INT));
        }
     
    memcpy(Faktor_eins, *feins,  ((*feins)[0]+1) * sizeof(INT));

/* AK 190802 */
    if (Faktor_zwei == NULL) {
        Faktor_zwei_size = 100;
        Faktor_zwei = (INT *) UE_malloc(Faktor_zwei_size*sizeof(INT));
        }
    else if (Faktor_zwei_size < ((*Fakt2zeig)[0]+1)) {
        Faktor_zwei_size = ((*Fakt2zeig)[0]+1)+100;
        Faktor_zwei = (INT *) UE_realloc(Faktor_zwei,Faktor_zwei_size*sizeof(INT));
        }

    memcpy(Faktor_zwei, *Fakt2zeig,  ((*Fakt2zeig)[0]+1) * sizeof(INT));
    Ergebnis = *Ergebzeig;


    /* Falls der Grad einer der Faktoren nicht Den Erweiterungsgrad teilt, */
    /* Wird eine Koerpererweiterung noetig */

if (globalno!=1) /* AK else bad recusrion for degree = 6,10, 
                    product of diff primes */
    {
    FASTCHECKMULTTAFEL(UE_Erw_Grad);
    if (Mult_Tafel == NULL)  erzmulttafel(UE_Erw_Grad,(INT)0,NULL); 
    }

    if (!UE_Erw_Grad || (UE_Erw_Grad%Faktor_eins[0] + UE_Erw_Grad%Faktor_zwei[0]))
    {
        minimalErw(feins);
        minimalErw(Fakt2zeig);
    }
    if (!UE_Erw_Grad || 
        (UE_Erw_Grad%Faktor_eins[0] + UE_Erw_Grad%Faktor_zwei[0])
       )
         {
         FASTCHECKMULTTAFEL(UE_kgv(Faktor_eins[0],Faktor_zwei[0]));
         if (Mult_Tafel == NULL) 
              erzmulttafel(UE_kgv(Faktor_eins[0],Faktor_zwei[0]),(INT)0,NULL);
         }
#ifdef UNDEF
        if (erzmulttafel(UE_kgv(Faktor_eins[0],Faktor_zwei[0]),(INT)0,NULL) != OK) /* UWH */
        {
            return error("ff.c: internal error (FF3)");
        }
#endif

    /* ist der Grad einer der Faktoren m nicht gleich dem aktuellen Grad, so  */
    /* muss eine Einbettung vorgenommen werden, indem man die Koeffizienten   */
    /* (<aktueller Grad> / m)-mal wiederholt.                         */
    if (Faktor_eins[0] != UE_Erw_Grad)
    {
        k=(INT)1;
        Fakt1hilf = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
        for (i=(INT)0;i<UE_Erw_Grad/Faktor_eins[0];i++)
            for (j=(INT)1;j<=Faktor_eins[0];j++)
                Fakt1hilf[k++] = Faktor_eins[j];
    }
    else
        Fakt1hilf = Faktor_eins;

    if (Faktor_zwei[0] != UE_Erw_Grad)
    {
        k=1;
        Fakt2hilf = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
        for (i=0;i<UE_Erw_Grad/Faktor_zwei[0];i++)
            for (j=1;j<=Faktor_zwei[0];j++)
                Fakt2hilf[k++] = Faktor_zwei[j];
    }
    else
        Fakt2hilf = Faktor_zwei;

    /* der Grad des Ergebnisselementes muss korrekt sein */
    if (Ergebnis[0]!=UE_Erw_Grad)
    {
        Ergebnis = (INT *) SYM_realloc(Ergebnis, (UE_Erw_Grad+1)*sizeof(INT) );
        Ergebnis[0] = UE_Erw_Grad;
        *Ergebzeig = Ergebnis;
    }

    /* Ergebniselement mit 0 vobelegen */
    for (i=1;i<=UE_Erw_Grad;i++) Ergebnis[i] = 0;

    /* Multiplikation mittels Multiplikationstafel */
    for (i=1;i<=UE_Erw_Grad;i++)
    {
        if(Fakt1hilf[i])
        {
            l=0;
            for (j=UE_Erw_Grad-i+1;j<=UE_Erw_Grad-1;j++)
            {
                l++;
                if (Fakt2hilf[l])
                {
                    zwisch=UE_MULTG(Fakt1hilf[i],Fakt2hilf[l]);
                    m=0;
                    for (k=UE_Erw_Grad-i+(INT)1;k<=UE_Erw_Grad-(INT)1;k++)
                    {
                    m++;
                    if (Mult_Tafel[j][k])
                        Ergebnis[m]=UE_ADDG(Ergebnis[m],
                                            UE_MULTG(zwisch,Mult_Tafel[j][k])
                                           );
                    }
                    for (k=(INT)0;k<=UE_Erw_Grad-i;k++)
                    {
                    m++;
                    if (Mult_Tafel[j][k])
                        Ergebnis[m] = UE_ADDG(Ergebnis[m],
                                              UE_MULTG(zwisch,Mult_Tafel[j][k])
                                             );
                    }
                }
            }
            for (j=(INT)0;j<=UE_Erw_Grad-i;j++)
            {
                l++;
                if (Fakt2hilf[l])
                {
                    zwisch = UE_MULTG(Fakt1hilf[i],Fakt2hilf[l]);
                    m=(INT)0;
                    for (k=UE_Erw_Grad-i+(INT)1;k<=UE_Erw_Grad-(INT)1;k++)
                    {
                    m++;
                    if (Mult_Tafel[j][k])
                        Ergebnis[m] = UE_ADDG(Ergebnis[m],
                                              UE_MULTG(zwisch,Mult_Tafel[j][k]));
                    }
                    for (k=(INT)0;k<=UE_Erw_Grad-i;k++)
                    {
                    m++;
                    if (Mult_Tafel[j][k])
                        Ergebnis[m] = UE_ADDG(Ergebnis[m],
                                              UE_MULTG(zwisch,Mult_Tafel[j][k]));
                    }
                }
            }
        }
    }

    if (Faktor_eins!=Fakt1hilf) SYM_free ((char *) Fakt1hilf);
    if (Faktor_zwei!=Fakt2hilf) SYM_free ((char *) Fakt2hilf);
    return OK;
}



/******************************************************************************/
/* Funktion UE_negativ belegt Ergebnis mit -e                  */
/******************************************************************************/
static INT UE_negativ(e,Ergebnis) INT **e,**Ergebnis;
/* e and Ergebnis may be equal */
{
    INT i;
    /* minimalErw(e); */
    /* 0 e */
    if ((*e)[0] == (INT)1 && (*e)[1] == (INT)0)
    {
        (*Ergebnis)[0] = (INT)1;
        (*Ergebnis)[1] = (INT)0;
        return OK;
    }
    /* Ergebniselement muss korrekte Erweiterung haben */
    if ((*Ergebnis)[0] < (*e)[0])
    {
        SYM_free((char*) (*Ergebnis));
        *Ergebnis = (INT *) UE_malloc(((*e)[0] +1)*sizeof(INT));
    }

    (*Ergebnis)[0] = (*e)[0];
    for (i=(INT)1;i<=(*e)[0];i++)
        if ((*e)[i])
            /* Negativbildung modulo Charakteristik */
            (*Ergebnis)[i] = Charakteristik-(*e)[i];
        else
            (*Ergebnis)[i] = (INT)0;
    return OK;
}


/******************************************************************************/
/* Funktion UE_hoch berechnet e^m und gibt das Ergebnis in Ergebzeig aus*/
/******************************************************************************/
static INT UE_hoch(e,m,Ergebnis) INT **e, m, **Ergebnis;
{
    INT *Elemhelp,i;
    /* minimalErw(e); AK 231296 */
    if ((*e)[0] == 1 && (*e)[1] == 0)
    {
        (*Ergebnis)[0] = (INT)1;
        (*Ergebnis)[1] = (INT)0;
        return OK;
    }

    /* falls Einselement */
    if ((*e)[0] == 1 && (*e)[1] == 1)
    {
        (*Ergebnis)[0] = (INT)1;
        (*Ergebnis)[1] = (INT)1;
        return OK;
    }

    /* Erzeugung eines Hilfselementes  */
    Elemhelp = (INT *) UE_malloc(((*e)[0] +(INT)1)*sizeof(INT));
    for (i=(INT)0;i<=(*e)[0];i++)
        Elemhelp[i] = (*e)[i];

    /* falls Ergebniselement nicht den benoetigten Erweiterungsgrad hat */
    if ((*Ergebnis)[0] < Elemhelp[0])
    {
        SYM_free((char*) (*Ergebnis));
        *Ergebnis = (INT *) UE_malloc(((*e)[0] +(INT)1)*sizeof(INT));
    }

    for (i=(INT)0;i<=(*e)[0];i++)
        (*Ergebnis)[i] = (*e)[i];
    i = m-(INT)1;
    while(i>(INT)0)
    {
        while(!(i % 2L))
        {
            i /= 2L;
            UE_mult(&Elemhelp,&Elemhelp,&Elemhelp);
        }
        i--;
        UE_mult(Ergebnis,&Elemhelp,Ergebnis);
    }
    SYM_free((char *) Elemhelp);
    return OK;
}



/******************************************************************************/
/* Funktion invers berechnet 1/e und gibt das Ergebnis in Ergebzeig aus.*/
/******************************************************************************/
static INT UE_invers(e,Ergebnis) INT **e,**Ergebnis;
{
    INT i;
    if ((*e)[0] == 1 && (*e)[1] == (INT)0)
    {
        return error("UE_invers:division by 0");
/*
        (*Ergebnis)[0] = (INT)0;
        return OK;
*/
    }

    /* 1/e = e^(Charakteristik^(Erweiterungsgrad des ees)-2) */
    i = UE_power(Charakteristik,(*e)[0])-2;
    UE_hoch(e,i,Ergebnis);
    return OK;
}



/******************************************************************************/
/* Funktion UE_ist_null testet, ob e = 0                        */
/* Rueckgabewert : 1 falls e = 0, 0 sonst                        */
/******************************************************************************/
static INT UE_ist_null(e) INT **e;
{
   /* AK 020304 */
/*
    INT i;
    for (i=(*e)[0];i>0;i--) if ((*e)[i] != 0) return 0;
    return 1;
*/
     UE_IST_NULL(e);
}

/******************************************************************************/
/* Funktion UE_ist_eins testet, ob e = 1                        */
/* Rueckgabewert : 1 falls e = 1, 0 sonst                        */
/******************************************************************************/
static INT UE_ist_eins(e) INT **e;
{
    /* AK 020304 */
    INT i;
    for (i=1;i<=(*e)[0];i++) if ((*e)[i] != 1) return 0;
    return 1;
}



/******************************************************************************/
/* Funktion Int_Aequivalent berechnet zu einer Integerzahl a das zugehoerige  */
/* Grundkoerperelement und belegt Ergebnis damit.                      */
/******************************************************************************/
static INT UE_Int_Aequivalent(a,Ergebnis) INT a; INT **Ergebnis;
{
    /* falls Ergebniselement nicht den benoetigten Erweiterungsgrad hat */
    if ((*Ergebnis)[0] < (INT)1)
    {
        SYM_free((char*) (*Ergebnis));
        *Ergebnis = (INT *) UE_malloc(2*sizeof(INT));
    }
    (*Ergebnis)[0] = 1;
    (*Ergebnis)[1] = a % Charakteristik;
    if ( (*Ergebnis)[1] < 0 ) (*Ergebnis)[1]=(*Ergebnis)[1] +Charakteristik; /* AK 170304 */
    UE_Erw_Grad = 1;  /* AK 190100 */
    return OK;
}




/******************************************************************************/
/* Funktion UE_ist_gleich vergleicht e_eins mit e_zwei               */
/* Rueckgabewert :  1  falls e_eins > e_zwei,                      */
/*             -1  falls e_eins < e_zwei,                      */
/*              0  falls e_eins = e_zwei.                      */
/******************************************************************************/
static INT UE_ist_gleich(e_eins,e_zwei) INT **e_eins, **e_zwei;
{
    INT i,j,k,*Elem1hilf,*Elem2hilf;
    INT gemein_grad;

    /* falls die ee verschiedene Erweiterungsgrade ueber dem Grundkoerper */
    /* haben, muessen sie in den gemeinsammen Erweiterungskoerper eingebettet   */
    /* werden.                                                  */
    if ((*e_eins)[0] != (*e_zwei)[0])
    {
        gemein_grad = UE_kgv((*e_eins)[0],(*e_zwei)[0]);
        if ((*e_eins)[0] != gemein_grad)
        {
            k=(INT)1;
            Elem1hilf = (INT *) UE_malloc((gemein_grad+1)*sizeof(INT));
            for (i=(INT)0;i<gemein_grad/(*e_eins)[0];i++)
                for (j=(INT)1;j<=(*e_eins)[0];j++)
                    Elem1hilf[k++] = (*e_eins)[j];
        }
        else
            Elem1hilf = *e_eins;

        if ((*e_zwei)[0] != gemein_grad)
        {
            k=(INT)1;
            Elem2hilf = (INT *) UE_malloc((gemein_grad+1)*sizeof(INT));
            for (i=(INT)0;i<gemein_grad/(*e_zwei)[0];i++)
                for (j=(INT)1;j<=(*e_zwei)[0];j++)
                    Elem2hilf[k++] = (*e_zwei)[j];
        }
        else
            Elem2hilf = *e_zwei;
    }
    else
    {
        Elem1hilf = *e_eins;
        Elem2hilf = *e_zwei;
        gemein_grad = (*e_eins)[0] ; /* AK 230395 */
    }

    /* Vergleich */
    k = 0;
    for (i=1;i<=gemein_grad;i++)
        if (Elem1hilf[i] != Elem2hilf[i])
        {
            k = i;
            i = gemein_grad+(INT)1;
        }

    if (k > 0 && Elem1hilf[k] < Elem2hilf[k])
        k = -1;

    if (k > 0 && Elem1hilf[k] > Elem2hilf[k])
        k = 1;

    /* Speicher, fallsbenoetigt freigeben */
    if (*e_eins!=Elem1hilf) SYM_free ((char *) Elem1hilf);
    if (*e_zwei!=Elem2hilf) SYM_free ((char *) Elem2hilf);

    return(k);
}



INT order_ff(a,b) OP a,b;
/* AK 170194 */
{
    INT erg = OK;
    if (a == b)
        return ERROR;
    CTO(FF,"order_ff",a);
    erg += erzmulttafel(UE_Erw_Grad,0,NULL); /* UWH */
    erg += m_i_i(UE_order(  & S_FF_IP(a) ), b);
    ENDR("order_ff");
}

/******************************************************************************/
/* Funktion UE_order berechnet das kleinste m mit e^m = 1              */
/* Rueckgabewert : die berechnete Ordnung.                           */
/******************************************************************************/
static INT UE_order(e) INT **e;
{
    INT maxord = UE_power(Charakteristik,(*e)[0])-(INT)1;
    INT maxteiler = maxord/2L;

    INT i,*Ergebnis;
    UE_Platz(&Ergebnis);
    for (i=(INT)1;i<=maxteiler;i++)
        if (!(maxord % i))
        {
            UE_hoch(e,i,&Ergebnis);
            if (UE_ist_eins(&Ergebnis))
                {
                SYM_free(Ergebnis);
                return i;
                }
        }
    UE_Free(&Ergebnis);
    return(maxord);
}



/******************************************************************************/
/* Funktion UE_Random erzeugt ein zufaelliges e im Koerper des aktuellen*/
/* Grades.                                                   */
/******************************************************************************/
static INT UE_Random(e) INT **e;
{
    INT i;
    /* Der Erweiterungsgrad des ees muss mit dem aktuellen uebereinstimmen */
    SYM_free(*e); /* AK 170393 */
    *e = (INT *) UE_malloc((UE_Erw_Grad+1)*sizeof(INT));
    (*e)[0] = UE_Erw_Grad;
    /* Zufallserzeugung */
    for (i=(INT)1;i<=UE_Erw_Grad;i++)
        (*e)[i] = rand() % Charakteristik;
    /* minimalErw(e); */ /* AK 020304 */
    return OK;
}




#ifdef UNDEF
UE_main()
{
    INT u=1,i,j=0,*test,*test_eins,*test_zwei;
    UE_Erw_Grad = (INT)0;
    do {
        printf("Geben sie die gewuenschte Charakteristik ein ");
        scanf("%d",&Charakteristik); 
        fflush(stdout);
        j = UE_prim(Charakteristik);
        if (!j)
            printf("\n   Dies ist keine Primzahl!\n");
    } while (!j);
    while(u)
    {
        UE_Platz(&test);
        UE_scan(&test);
        printf("\n");
        UE_Platz(&test_eins);
        UE_scan(&test_eins);
        printf("\n");
        UE_Platz(&test_zwei);
        UE_add(&test,&test_eins,&test_zwei);
        UE_Zeige(&test);
        printf(" + \n");
        UE_Zeige(&test_eins);
        printf(" = \n");
        UE_Zeige(&test_zwei);
        if (UE_ist_null(&test_zwei))
            printf("ist Null\n");
        if (UE_ist_eins(&test_zwei))
            printf("ist Eins\n");
        printf("\n\n");
        UE_mult(&test,&test_eins,&test_zwei);
        UE_Zeige(&test);
        printf(" * \n");
        UE_Zeige(&test_eins);
        printf(" = \n");
        UE_Zeige(&test_zwei);
        if (UE_ist_null(&test_zwei))
            printf("ist Null\n");
        if (UE_ist_eins(&test_zwei))
            printf("ist Eins\n");
        printf("\n\n");
        UE_invers(&test_zwei,&test_eins);
        printf("1/ ");
        UE_Zeige(&test_zwei);
        printf(" = ");
        UE_Zeige(&test_eins);
        if (UE_ist_null(&test_eins))
            printf("ist Null\n");
        if (UE_ist_eins(&test_eins))
            printf("ist Eins\n");
        printf("\n\n");
        UE_negativ(&test_zwei,&test_eins);
        printf("0- ");
        UE_Zeige(&test_zwei);
        printf(" = ");
        UE_Zeige(&test_eins);
        if (UE_ist_null(&test_eins))
            printf("ist Null\n");
        if (UE_ist_eins(&test_eins))
            printf("ist Eins\n");
        UE_Free(&test);
        UE_Free(&test_eins);
        UE_Free(&test_zwei);
        printf("Momentane Koerpererweiterung: %d\n",UE_Erw_Grad);
        printf("Ende = 1   Weiter = 2   neuer Grad und weiter = 3 ");
        scanf("%d",&i);
        if (i==1)
            u=(INT)0;
        if (i==3)
        {
            printf("Grad :");
            scanf("%ld",&UE_Erw_Grad);
            erzmulttafel(UE_Erw_Grad,0,NULL); /* UWH */
        }
    }
}
#endif /* UNDEF */

static INT init_ff(a) OP a;
{
    INT erg = OK;
    erg += m_il_v(3L,a); 
           /* first = characteristic
              second = vector of components of ff
              third = minimalErw = y=1/unknown=0 
           */
    C_O_K(a,FINITEFIELD);
    erg += UE_Platz(&S_FF_IP(a));
    M_I_I(0,S_FF_ME(a));
    return erg;
}


INT debugprint_ff(a) OP a;
/* AK 160393 */
{
    INT i;
    INT *iv;
    for (i=(INT)0;i<doffset;i++) fputc(' ',stderr);
    fprintf(stderr,"ff:Charakteristik =\n");
    doffset += 2L;
    debugprint(s_v_i(a,(INT)0));
    doffset -= 2L;
    fprintf(stderr,"ff:reduce_info =\n");
    doffset += 2L;
    debugprint(s_v_i(a,(INT)2));
    doffset -= 2L;
    iv = S_O_S(S_V_I(a,(INT)1)).ob_INTpointer;
    for (i=(INT)0;i<doffset;i++) fputc(' ',stderr);
    fprintf(stderr,"ff:INT vektor =\n");
    for (i=(INT)0;i<doffset;i++) fputc(' ',stderr);
    for (i=(INT)0;i<= *iv;i++)
        fprintf(stderr,"%ld ",*(iv+i));
    fprintf(stderr,"\n");
    return OK;
}


INT reduce_ff(a) OP a;
/* AK 290304 */
/* computes the minimal extension over the
   prime field, where a lives in */
{
    INT erg = OK;
    CTO(FF,"reduce_ff(1)",a);
    {
    INT *ai;
    if (S_FF_MEI(a) != 1) {
       ai = S_O_S(S_V_I(a,1)).ob_INTpointer;
       minimalErw(&ai); 
       M_I_I(1,S_FF_ME(a)); /* 1 = this is a minimal extension */
       }
    }
    ENDR("reduce_ff");
}

INT primep_ff(a) OP a;
/* AK 130704 */
/* returns true if a is an element of the prime field */
/* AK 130704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"primep_ff(1)",a);
    {
    INT deg = S_FF_DI(a);
    if (S_FF_MEI(a)==1) /* is the minimal extension */
        {
        if (deg == 1) return TRUE; 
        else return FALSE;
        }
    else
        {
        INT i,vi=S_FF_II(a,0); /* first entry */
        for (i=1;i<deg;i++) if (S_FF_II(a,i) != vi) return FALSE;
        /* the degree could be reduced */
        return TRUE;
        }
    }
    ENDR("primep_ff");
}


INT hash_ff(a) OP a;
/* AK 200104 */
/* AK 130704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"hash_ff(1)",a);
    {
    INT i,res,deg;
    // reduce_ff(a); /* minimal extension*/
    deg=S_FF_DI(a);
    res = 11011;
    for (i=0;i<=deg;i++)
        res = res*11+S_FF_II(a,i);
    
    return res;
    }
    ENDR("hash_ff");
}

INT fprint_ff(f,a) OP a; FILE *f;
/* AK 180194 *//* AK 260594 */
/* AK 080704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"fprint_ff(2)",a);

    {
    fputc('[',f);
    erg += UE_fZeige(f,& S_FF_IP(a));
    fputc(']',f);
    if (f == stdout) zeilenposition += 2;
    }

    ENDR("fprint_ff");
}


INT objectwrite_ff(f,a) FILE *f; OP a;
/* AK 040304 */
/* AK 130704 V3.0 */
{
    INT erg = OK;
    COP("objectread_ff(1)",f);
    CTO(FF,"objectwrite_ff(2)",a);
    {
    INT i,*ip;
    fprintf(f,"%ld\n%ld\n%ld ", 
              (INT)FF,S_FF_CI(a),S_FF_DI(a));
    ip = S_FF_IP(a);
    for (i=0;i<S_FF_DI(a);i++) fprintf(f,"%ld ",ip[i+1]);
    fputc('\n',f);
    }
    ENDR("objectwrite_bruch");
}



INT objectread_ff(f,a) FILE *f; OP a;
/* AK 040304 */
/* AK 130704 V3.0 */
{
    INT erg = OK;
    COP("objectread_ff(1)",f);
    {
    INT i,j,*ip;
    fscanf(f,"%ld",&i);Charakteristik=i;
    fscanf(f,"%ld",&i);UE_Erw_Grad=i;
    init_ff(a);ip = S_FF_IP(a);
    for (j=0;j<UE_Erw_Grad;j++) { fscanf(f,"%ld",&i); ip[j+1]=i;}
    ip[0]=UE_Erw_Grad;
    M_I_I(Charakteristik,S_V_I(a,0));
    }
    CTO(FF,"objectread_ff(i)",a);
    ENDR("objectread_ff");
}




INT sprint_ff(f,a) OP a; char *f;
/* AK 040304 */
{
    INT erg = OK,i,j;
    sprintf(f,"[%d,",S_FF_CI(a)); i = strlen(f); f = f+i;
    for (i=0;i<S_FF_DI(a)-1;i++)  {
        sprintf(f,"%d,",S_FF_II(a,i));
        j=strlen(f);f=f+j;
        }
    sprintf(f,"%d]",S_FF_II(a,i));
    return erg;
}


INT m_vector_ff(a,b,c) OP a,b,c;
/* AK 170194 */ /* a Charakteristik, b INTEGERVECTOR */
/* AK 310106 V3.0 */
{
    INT erg = OK;
    INT i;
    INT *bi;

        if (check_equal_3(a,b,c,m_vector_ff,&erg) == EQUAL)
                goto mve;

    if (S_O_K(a) != INTEGER)
        return WTT("m_vector_ff",a,b);
    if (not VECTORP(b))
        return WTT("m_vector_ff",a,b);

    Charakteristik = S_I_I(a);
    UE_Erw_Grad = S_V_LI(b);
    init_ff(c);
    erg += UE_Platz(&S_FF_IP(c));
    bi = S_FF_IP(c);
    *bi = S_V_LI(b);
    for (i=(INT)0;i<S_V_LI(b);i++)
        *(bi+i+1) = S_V_II(b,i);

    erg += m_i_i(Charakteristik,S_V_I(c,(INT)0));
    erg += erzmulttafel(UE_Erw_Grad,0,NULL); /* UWH */
mve:
    ENDR("m_vector_ff");
}

INT m_ff_vector(a,b) OP a,b;
/* AK 230395 */
{
    INT erg = OK;
    INT i;
    CTO(FINITEFIELD,"m_ff_vector(1)",a);
    CE2(a,b,m_ff_vector);

    erg += m_il_v(S_FF_DI(a),b);
    for (i=0;i<S_V_LI(b);i++)
        M_I_I(S_FF_II(a,i+1),S_V_I(b,i));
    C_O_K(b,INTEGERVECTOR);
    ENDR("m_ff_vector");
}

INT first_ff(a,b,c) OP a,b,c;
/* AK 170194 a Charakteristik, b Grad der Erweiterung */
{
    INT erg = OK;
    CTO(INTEGER,"first_ff(1)",a);
    CTO(INTEGER,"first_ff(2)",b);
	{
	OP d;
	d = callocobject();
	erg += m_il_nv(S_I_I(b),d);
	erg += m_vector_ff(a,d,c);
	FREEALL(d);
	}
    ENDR("first_ff");
}

INT first_ff_given_q(q,c) OP q,c;
/* AK 290304 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"first_ff_given_q(1)",q);
    SYMCHECK(S_I_I(q) < 2,"first_ff_given_q:q<2");
    SYMCHECK(prime_power_p(q) ==FALSE,"first_ff_given_q:q no prime power");
    {
    OP v;
    v = CALLOCOBJECT();
    erg += factorize_integer(q,v);
    erg += first_ff(S_V_I(v,0),S_V_L(v),c);
    FREEALL(v);
    }
    ENDR("first_ff_given_q");
}

INT next_apply_ff(a) OP a;
/* AK 090804 V3.0 */
{
    return next_ff(a,a); 
} 

INT next_ff(a,b) OP a,b;
/* a and b may be equal */
/* AK 090804 V3.0 */
{
    INT erg = OK;
    CTO(FF,"next_ff(1)",a);
    {
    INT i,*ai,l;
    Charakteristik = S_V_II(a,(INT)0);
    if (a != b) copy(a,b);
    ai = S_O_S(S_V_I(b,(INT)1)).ob_INTpointer;
    UE_Erw_Grad = *ai;
    l = *ai;
    for (i=l;i>0;i--)
        if ( *(ai+i) < (Charakteristik-1) )
        {
            *(ai+i) = *(ai+i) + 1;
            for (i++;i<=l;i++)
            {
                *(ai+i) = 0;
            }
            return OK;
        }
    if (i == 0)
        return LAST_FF;
    }
    erg = ERROR;
    ENDR("next_ff");
}

/****************************************************************************/
/* Funktion einfuegTrace fuegt ein neu berechnetes Polynom in die           */
/*          entsprechende Datei ein.                                        */
/* bergabeparameter   Grad           Erweiterungsgrad der Datei            */
/*                     tracePolynom   einzutragendes Polynom                */
/****************************************************************************/
void einfuegTrace(Grad,tracePolynom) INT Grad; INT *tracePolynom;
{
    INT j;
    INT i;
    INT Laenge;
    char Zeichenkette[50];
    /* "G<GRAD>:" */
    if (Datei==NULL) {
                     // error("internal error FF311");
                     return;
                     }
                     
    Laenge = getString(Grad,Zeichenkette);
    fseek(Datei,0,2);
    putc('G',Datei);
    for (i=0;i<Laenge;i++)
        putc(Zeichenkette[i],Datei);
    putc(':',Datei);

    /* Polynomkoeffizienten  */
    for (j=0;j<Grad;j++)
    {
        Laenge = getString(tracePolynom[j],Zeichenkette);
        for (i=0;i<Laenge;i++)
            putc(Zeichenkette[i],Datei);
        putc(' ',Datei);
    }
    putc('\n',Datei);
    fflush(Datei);
    return;
}




/****************************************************************************/
/* Funktion spezGrad ermittelt den Grad von Polynom                         */
/*                                                                          */
/* Uebergabeparameter : Polynom,Grad                                         */
/*                                                                          */
/* Rueckgabeparameter Grad des Polynoms                                      */
/****************************************************************************/
static INT spezGrad(Polynom,Grad) INT *Polynom; INT Grad;
{
    INT i;
    for (i=Grad;i>=0;i--)
        {
        if (Polynom[i])
            {
            return(i);
            }
        }
    return(-1);
}




/****************************************************************************/
/* Funktion spezNormiert normiert Polynom                                   */
/* bergabeparameter : Polynom, NormalPolynom,Grad                          */
/****************************************************************************/
static INT *spezNormiert(Polynom,Grad) INT *Polynom; INT Grad;
{
    INT i;
    INT maxGrad = spezGrad(Polynom,Grad);
    INT Faktor = Polynom[maxGrad];
    if (Faktor==1)
        return(Polynom);
    Faktor = UE_divg(1,Faktor);
    for (i=maxGrad;i>=0;i--)
        Polynom[i] = UE_multg(Polynom[i],Faktor);
    return(Polynom);
}



/***************************************************************************/
/* Funktion spezEinsGGT berprft, ob GGT(Pol1,Pol2) = 1                   */
/* bergabeparameter Pol1, Pol2, Grad = Grad der Polynome                  */
/* Rckgabewert : 1, falls GGT = 1, 0 sonst                                */
/***************************************************************************/
static INT spezEinsGGT(Pol1,Pol2,Grad) INT *Pol1; INT *Pol2; INT Grad;
{
    INT i;
    INT *hilf1pol;
    INT *hilf2pol;
    if (!(hilf1pol = (INT *) UE_malloc((Grad+1)*sizeof(INT))))
        return no_memory();

    if (!(hilf2pol = (INT *) UE_malloc((Grad+1)*sizeof(INT))))
    {
        SYM_free((char *) hilf1pol);
        return no_memory();
    }
    for (i=0;i<=Grad;i++)
    {
        hilf1pol[i] = Pol1[i];
        hilf2pol[i] = Pol2[i];
    }
    while (spezGrad(hilf1pol,Grad)>=0 && spezGrad(hilf2pol,Grad)>=0)
    {
        reduzierpoly(hilf1pol,spezGrad(hilf1pol,Grad),spezNormiert(hilf2pol,Grad),spezGrad(hilf2pol,Grad));
        if(spezGrad(hilf1pol,Grad)>=0)
            reduzierpoly(hilf2pol,spezGrad(hilf2pol,Grad),spezNormiert(hilf1pol,Grad),spezGrad(hilf1pol,Grad));
    }

    /* Grad = 0 bedeutet von 0 verschiedenes Grundkoerperelement */
    if (spezGrad(hilf1pol,Grad)==0)
    {
        SYM_free((char *) hilf1pol);
        SYM_free((char *) hilf2pol);
        return (INT)1;
    }

    /* hilf1pol = 0  und hilf2pol von 0 verschiedenes Grundkorperelement */
    if (spezGrad(hilf1pol,Grad)<0)
        if (spezGrad(hilf2pol,Grad)==0)
        {
            SYM_free((char *) hilf1pol);
            SYM_free((char *) hilf2pol);
            return (INT) 1;
        }

    SYM_free((char *) hilf1pol);
    SYM_free((char *) hilf2pol);
    return(INT)0;
}



/****************************************************************************/
/* Funktion spezMult Multiplikation zweier Koerperelemente Modulo           */
/*                   NormalPolynom                                          */
/* bergabeparameter : Faktor1, Faktor2, Ergebnis, NormalPolynom, Grad      */
/*                                                                          */
/* Rckgabeparameter 1, falls ohne Probleme durchgefuehrt, 0 sonst.         */
/****************************************************************************/
static INT spezMult(Faktor1,Faktor2,Ergebnis,NormalPolynom,Grad)
    INT *Faktor1;
    INT *Faktor2;
    INT *Ergebnis;
    INT *NormalPolynom;
    INT Grad;
{
    INT i;
    INT j;
    INT ergebnisGrad=0;
    INT *zwischenErgebnis;
    zwischenErgebnis = (INT *) SYM_calloc(Grad+Grad,sizeof(INT));

    for (i=0;i<Grad;i++)
        for(j=0;j<Grad;j++)
            if(Faktor1[i] && Faktor2[j])
            {
                if (ergebnisGrad < i+j)
                    ergebnisGrad = i+j;
                zwischenErgebnis[i+j] = UE_addg(zwischenErgebnis[i+j],
                            UE_multg(Faktor1[i],Faktor2[j]));
            }

    reduzierpoly(zwischenErgebnis,ergebnisGrad,NormalPolynom,Grad);

    for (i=0;i<Grad;i++)
        Ergebnis[i] = zwischenErgebnis[i];

    SYM_free((char *) zwischenErgebnis);
    return(1);
}

/*******************************************************************************/ 
/* Funktion spezHoch berechnet Element^m und gibt das Ergebnis in Ergebzeig aus*/ 
/*******************************************************************************/ 
static int spezHoch(Element,m,Ergebnis,NormalPolynom,Grad) INT *Element;
    INT m;
    INT *Ergebnis;
    INT *NormalPolynom;
    INT Grad;
{
    INT *Elemhelp,i;

    /* Erzeugung eines Hilfselementes  */
    if(!(Elemhelp = (INT *) UE_malloc(Grad*sizeof(INT))))
    {
        return(0);
    }
    for (i=0;i<Grad;i++)
        Elemhelp[i] = Element[i];

    for (i=0;i<Grad;i++)
        Ergebnis[i] = Element[i];

    i = m-1;
    while(i>0)
    {
        while(!(i % 2))
        {
            i /= 2;
            spezMult(Elemhelp,Elemhelp,Elemhelp,NormalPolynom,Grad);
        }
        i--;
        spezMult(Ergebnis,Elemhelp,Ergebnis,NormalPolynom,Grad);
    }
    SYM_free((char *) Elemhelp);
    return(1);
}

/****************************************************************************/
/* Funktion triang bildet Dreiecksmatrix von Matrix                         */
/****************************************************************************/
static void triang(Matrix,Deg) INT **Matrix; INT Deg;

{
    INT i,j,k,l,pp,u;
    for(i=0;i<Deg;i++)
    {
        j=i;
        while((!(Matrix[i])[j]) && (j<Deg-1))
            j++;
        if(!(Matrix[i])[j])
        {
            j=0;
            while((j<i) && ((!(Matrix[i])[j]) || (Matrix[j][j])))
                j++;
        }
        if (Matrix[i][j])
        {
            u = UE_divg(1,Matrix[i][j]);
            for(k=i;k<Deg;k++)
                Matrix[k][j] = UE_multg(Matrix[k][j],u);
            for(k=0;k<Deg;k++)
                if (k!=j)
                {
                    u = UE_subg(0,Matrix[i][k]);
                    if (Matrix[i][k])
                        for(l=i;l<Deg;l++)
                        {
                            Matrix[l][k] = UE_addg(Matrix[l][k],UE_multg(u,Matrix[l][j]));
                        }
                }
            if (i!=j)
                for(k=i;k<Deg;k++)
                {
                    pp = Matrix[k][i];
                    Matrix[k][i] = Matrix[k][j];
                    Matrix[k][j] = pp;
                }
        }
    }
}




/****************************************************************************/
/* Funktion testirrPolynom testet, ob Polynom irreduzibel ist.              */
/* Uebergabeparameter NormaltestPolynom,Grad                          */
/*        Rueckgabewert   1, falls NormaltestPolynom irreduzibel, 0 sonst    */
/****************************************************************************/
static INT testirrPolynom(NormaltestPolynom,Grad)
    INT *NormaltestPolynom;
    INT Grad;
{
    INT i;
    INT j;
    INT *Ableitung,*hf,*x,*q_mat;
    INT **Matrix;
    Ableitung = (INT *) SYM_calloc(Grad+1,sizeof(INT));
    /* Bildung der Ableitung */
    for(i=0;i<Grad-1;i++)
        Ableitung[i] = UE_multg(NormaltestPolynom[i+1],i+1);
    Ableitung[Grad-1] = Grad % Charakteristik;

    for(i=0;i<Grad;i++)
        if(Ableitung[i] != 0)
            i = Grad + 1;
    /* Alle EINTraege = 0 -> Ableitung = 0   -> nicht irreduzibel */
    if (i == Grad)
    {
        SYM_free((char *) Ableitung);
        return(0);
    }

    if (!spezEinsGGT(NormaltestPolynom,Ableitung,Grad))
    {
        SYM_free((char *) Ableitung);
        return(0);
    }

    hf = (INT *) SYM_calloc(Grad,sizeof(INT));
    q_mat = (INT *) SYM_calloc(Grad*Grad,sizeof(INT));
    x = (INT *) SYM_calloc(Grad*2,sizeof(INT));
    Matrix = (INT **) SYM_calloc(Grad,sizeof (INT *));
    
    i=0;
    for (j=0;j<Grad;j++)
    {
        Matrix[j]=q_mat+(j*Grad);
    }

    (Matrix[0])[0] = 1;
    x[1] = 1;
    spezHoch(x,Charakteristik,x,NormaltestPolynom,Grad);
    for(i=1;i<Grad;i++)
    {
        for(j=0;j<Grad;j++)
        {
            hf[j] = (Matrix[i-1])[j];
        }
        spezMult(hf,x,hf,NormaltestPolynom,Grad);
        for(j=0;j<Grad;j++)
            {
            (Matrix[i])[j] = hf[j];
            }
    }
    for(i=0;i<Grad;i++)
        (Matrix[i])[i]=UE_subg((Matrix[i])[i],1);
    triang(Matrix,Grad);
    j=0;
    for(i=0;i<Grad;i++)
        if ((Matrix[i])[i]==1)
            j++;
    SYM_free((char *) hf);
    SYM_free((char *) x);
    SYM_free((char *) q_mat);
    SYM_free((char *) Matrix);
    SYM_free((char *) Ableitung);
    if(j==(Grad-1))
        return(1);
    return(0);
}





/****************************************************************************/
/* Funktion testNormalPol berprft, ob Polynom NormalPolynom ist.          */
/*                                                                          */
/* bergabeparameter : NormalPolynom, Grad                                  */
/*                                                                          */
/* Rckgabeparameter : 1, falls Normalpolynom, 0 sonst                      */
/****************************************************************************/
static INT testNormalPol(NormaltestPolynom,Grad)
    INT *NormaltestPolynom;
    INT Grad;
{
    INT i;
    INT j;
    INT *Permutation;
    INT *NormalPolynom;
    INT *a_Hoch_q;
    INT **Pol1;

    if(!(NormalPolynom = (INT *) UE_malloc(Grad*sizeof(INT))))
    {
        return no_memory();
    }

    for (i=0;i<Grad;i++)
        NormalPolynom[i] = NormaltestPolynom[i];

    if(!(Permutation = (INT *) UE_malloc(Grad*sizeof(INT))))
    {
        SYM_free((char *) NormalPolynom);
        return no_memory();
    }

    if(!(Pol1 = (INT **) UE_malloc((Grad+1)*sizeof(INT*))))
    {
        SYM_free((char *) NormalPolynom);
        SYM_free((char *) Permutation);
        return(0);
    }

    if(!(a_Hoch_q = (INT *) SYM_calloc(Charakteristik+1,sizeof(INT))))
    {
        SYM_free((char *) NormalPolynom);
        SYM_free((char *) Permutation);
        SYM_free((char *) Pol1);
        return(0);
    }

    /* Belegung von ax^(m-1)+a^qx^(m-2)+...a^(q^(m-1)) */
    for (i=0;i<=Grad;i++)
        if(!(Pol1[i] = (INT *) SYM_calloc(Grad,sizeof(INT))))
        {
            SYM_free ((char *) a_Hoch_q);
            SYM_free((char *) NormalPolynom);
            SYM_free((char *) Permutation);
            for (j=i-1;i>=0;j--)
                SYM_free((char *) Pol1[j]);
            SYM_free((char *) Pol1);
            return(0);
        }


    Pol1[Grad-1][1] = 1; /* a */

    a_Hoch_q[Charakteristik] = 1;
    reduzierpoly(a_Hoch_q,Charakteristik,NormalPolynom,Grad);
    for (i=0;i<Grad && i<=Charakteristik;i++)
        Pol1[Grad-2][i] = a_Hoch_q[i];
    SYM_free ((char *) a_Hoch_q);


    for (i=Grad-3;i>=0;i--)
        spezHoch(Pol1[i+1],Charakteristik,Pol1[i],NormalPolynom,Grad);


    if (!gausszerlegu(Pol1,Grad,Permutation))
    {
        for (i=0;i<=Grad;i++)
            SYM_free((char *) Pol1[i]);
        SYM_free((char *) Pol1);
        SYM_free((char *) Permutation);
        SYM_free((char *) NormalPolynom);
        return(0);
    }
    else
    {
        for (i=0;i<=Grad;i++)
            SYM_free((char *) Pol1[i]);
        SYM_free((char *) Pol1);
        SYM_free((char *) Permutation);
        SYM_free((char *) NormalPolynom);
        return(1);
    }

}


/****************************************************************************/
/* Funktion getNormalPol erzeugt ein Normalpolynom.                         */
/*                                                                          */
/* Uebergabeparameter : NormalPolynom, Grad                                  */
/*                                                                          */
/* Rueckgabeparameter : OK falls erfolgreich, ERROR sonst                         */
/****************************************************************************/
static INT getNormalPol(NormalPolynom,Grad) INT *NormalPolynom, Grad;
{
    INT i;
    INT j;

    /* Vorbelegung von NormalPolynom */
    for (i=1;i<Grad-1;i++)
        NormalPolynom[i] = 0;
    NormalPolynom[0] = 1;
    NormalPolynom[Grad-1] = UE_subg(0,1);
    NormalPolynom[Grad] = 1;

    while(!(testirrPolynom(NormalPolynom,Grad) && testNormalPol(NormalPolynom,Grad)))
    {
        j = 0;
        while(NormalPolynom[j]==(Charakteristik-1))
        {
            if (j>0)
                NormalPolynom[j] = 0;
            else
                NormalPolynom[0] = 1;
            j++;
            if (j==Grad-1)
                return(ERROR);
        }
        if (j==Grad-1)
            return(ERROR);
        NormalPolynom[j]++;
    }
    return(OK);
}


/****************************************************************************/
/* Funktion minimalPolynom berechnet zu einem Element in                    */
/*          Normalbasenreprsentation das Minimalpolynom,                   */
/* bergabeparameter : Element (Element[0] = Grad, dann die EINTrge a,a^p,.*/
/*                     minPolynom : Grad eINTrge Platz  (da normiert)      */
/*                     (aufsteigende x-Potenzen                             */
/* Rckgabewert : 1, falls Minimalpoylom berechnet., 0 sonst                */
/****************************************************************************/
static INT minimalPolynom(Element,minPolynom) INT *Element; INT *minPolynom;
{
    INT rueckwert = 1;
    INT Grad = Element[0];
    INT i;
    INT j;
    INT *ElementPotenz;
    INT *MinusElementPotenz;
    INT *zwischElement;
    INT **Polynom;
    if(!(Polynom = (INT **) UE_malloc((Grad+1)*sizeof(INT *))))
        return no_memory();

    UE_Platz(&ElementPotenz);
    UE_Platz(&MinusElementPotenz);
    for (i=0;i<=Grad;i++)
        ElementPotenz[i] = Element[i];

    UE_negativ(&ElementPotenz,&MinusElementPotenz);
    UE_Platz(&zwischElement);

    /* Minimalpolynom mit 0 vorbelegen */
    for(i=0;i<=Grad;i++)
    {
        UE_Platz(&Polynom[i]);
        Polynom[i][0] = (INT)1;
        Polynom[i][1] = (INT)0;
    }

    /* Fuer die Multiplikation mit x-a^q^i starten wir bei der hchsten
       Potenz, auf diese Weise kann das Schiften fr die x-Multiplikation
       vernachlssigt werden */

    Polynom[Grad][1] = (INT)1;
    for(i=0;i<=Grad;i++)
        Polynom[Grad-1][i] = MinusElementPotenz[i];

    /* Berechnung des Minimalpolynoms */
    for(i=Grad;i>1;i--)
    {
        UE_hoch(&ElementPotenz,Charakteristik,&ElementPotenz);
        UE_negativ(&ElementPotenz,&MinusElementPotenz);
        for(j=i;j<=Grad;j++)
        {
            UE_mult(&MinusElementPotenz,&Polynom[j-1],&zwischElement);
            UE_add(&Polynom[j-2],&zwischElement,&Polynom[j-2]);
        }
        UE_add(&MinusElementPotenz,&Polynom[Grad-1],&Polynom[Grad-1]);
    }
    /* berprfung ob Ergebnispolynom nur aus Skalaren besteht */
    for (i=0;i<Grad;i++)
    {
        minimalErw(&Polynom[i]);
#ifdef UNDEF
        if(Polynom[i][0] != 1)
        {
            for(j=0;j<Grad;j++)
                UE_Zeige(&Polynom[j]);
            rueckwert = 0;
        }
#endif
        minPolynom[i] = (Polynom[i])[1];
        UE_Free(& Polynom[i]);
    }
    UE_Free(& Polynom[Grad]);
    SYM_free(Polynom);
    UE_Free(& ElementPotenz);
    UE_Free(& MinusElementPotenz);
    UE_Free(&zwischElement);
    return(rueckwert);
}



/******************************************************************************/
/* erzeugePol erzeugt ein Tracecompatibles Polynom                            */
/* Uebergabeparameter :                                                      */
/* Datei = Dateizeiger, Grad = gewuenschter Erweiterungsgrad,                  */
/* tracePolynom = Zeiger auf Tracecompatibles Polynom                         */
/*                                                                            */
/* Rueckgabe = 1 falls Erzeugung erfolgreich, 0 sonst.                         */
/******************************************************************************/
static INT erzeugePol(Grad,tracePolynom,DateiOffen)
    INT Grad;           /* gewnschter Erweiterungsgrad */
    INT *tracePolynom;  /* Platz fr tracecompatibles Polynom */
    INT DateiOffen; /*1 falls zweitaufruf */

{
    INT Gradsich ;
    INT i=2;
    INT j;
    INT k;
    INT spur,hll;

    INT *kleinPolynom;        /* Tracepolynom p^(n-1)         */
    INT kleinGrad;            /* Grad von kleinPolynom */
    INT *kleinElement;        /* Element in GF(p^(n-1)) */
    INT *grossElement;        /* Element in GF(p^n)     */
    INT *minPolynom;          /* Minimalpolynom von kleinElement */
    INT *xHOCHmPLUS1;         /* Polynom x^m+1  */
    INT *Faktor;              /* Faktor zu x^p^(Grad-1) - 1      */

    INT anzahlPrimfakt = 0;   /* Anzahl der Primpotenzfaktoren */
    INT Basis[20];            /* Basen der Primpotenzen */
    INT Potenz[20];           /* Potenzen der Primpotenzen */
    INT **multTafel[20];      /* Zeiger auf Multiplikationstafeln */

    INT **Gauss;              /* fr Gaussalgorithmus */
    INT *Permutation;         /* fr Gaussalgorithmus */
    INT *NormalPolynom;       /* Platz fr Normalpolynom */
    INT **hilfsZeiger;        /* Hilfszeiger */

    /* Zerlegung von Grad in Primfaktoren */
    Gradsich = Grad;
    while (Gradsich > 1)
    {
        while(!(Gradsich%i) && Gradsich > 1)
        {
            Gradsich /= i;
            if (anzahlPrimfakt>0 && Basis[anzahlPrimfakt-1] == i)
                Potenz[anzahlPrimfakt-1] ++;
            else
            {
                Basis[anzahlPrimfakt] = i;
                Potenz[anzahlPrimfakt] = 1;
                anzahlPrimfakt++;
            }
        }
        i++;
    }

    /* Falls nur eine Primpotenz -> Erzeugung, andernfalls Berechnung aus
        Multiplikationstabellen bestehender Erweiterungspolynome ->
        Rekursiver Aufruf */

    if (anzahlPrimfakt==1)    /* Starten des Erzeugungsvorgangs */
    {
        /* Erzeugen eines Normalpolynoms */
        UE_Erw_Grad = Grad; /* AK 130197 */
        kleinGrad = Grad/Basis[0];
        UE_Platz(&kleinElement);

        if(!(NormalPolynom = (INT *) UE_malloc((Grad+1)*sizeof(INT))))
            return no_memory();

        if(getNormalPol(NormalPolynom,Grad) != OK)
        {
            SYM_free((char *) NormalPolynom);
            /*
                        printf("Kann kein Normalpolynom zum Grad %d erzeugen.\n",Grad);
                        return(0);
*/
            error("ff.c: internal error FF-40");
        }

        /* Hole Polynom vom Grad p^(n-1) */
        if(!(kleinPolynom = (INT *) UE_malloc((kleinGrad+1)*sizeof(INT))))
        {
            SYM_free((char *) NormalPolynom);
            return no_memory();
        }

        if(!(minPolynom = (INT *) UE_malloc((Grad+1)*sizeof(INT))))
        {
            SYM_free((char *) NormalPolynom);
            SYM_free((char *) kleinPolynom);
            return no_memory();
        }

        if(liestracepol(kleinGrad,kleinPolynom,DateiOffen) != OK)
        {
            SYM_free((char *) NormalPolynom); SYM_free((char *) minPolynom);
            SYM_free((char *) kleinPolynom);
            return error("internal error FF201");
        }

        if(erzmulttafel(Grad,-1,NormalPolynom) != OK)
        {
            SYM_free((char *) NormalPolynom); SYM_free((char *) minPolynom);
            SYM_free((char *) kleinPolynom);
            return error("internal error FF202");
        }
        kleinElement[0] = kleinGrad;
        for(i=1;i<=kleinGrad;i++)
            kleinElement[i] = 0;
        k = 1;
        while(k)
        {
            j = 1;
            while(kleinElement[j]==Charakteristik-1)
            {
                kleinElement[j] = 0;
                j++;
                if (j>kleinGrad)
                {
                    SYM_free((char *) NormalPolynom);
                    SYM_free((char *) kleinPolynom);
                    SYM_free((char *) minPolynom);
                    UE_Free(& kleinElement);
                    error("internal error FF203");
                    return ERROR;
                }
            }
            if (j>kleinGrad)
            {
                SYM_free((char *) NormalPolynom);
                SYM_free((char *) kleinPolynom);
                SYM_free((char *) minPolynom);
                UE_Free(& kleinElement);
                error("internal error FF204");
                return ERROR;
            }
            kleinElement[j]++;

/* spur wird mit -Spur von Kleinelement belegt. fuer Trace-kompatibilitaet ist
    spur == 1 erforderlich  auaerdem mua der 1. Koeffizient
    <> 0 sein, da andernfalls das Element (geschiftet) bereits
    berprft wurde     */

            spur = 0;
            for (i=1;i<=kleinGrad;i++)
                spur = UE_addg(spur,kleinElement[i]);

            if(kleinElement[1] && spur == 1)
            {
                minimalPolynom(kleinElement,minPolynom);
                for(i=0;i<kleinGrad;i++)
                    if(minPolynom[i] != kleinPolynom[i])
                        i = kleinGrad + 1;
                if(i==kleinGrad)
                    k = 0;
            }
        }

        SYM_free((char*)NormalPolynom);
        UE_Platz(&grossElement);
        xHOCHmPLUS1 = (INT *) SYM_calloc(Grad+1,sizeof(INT));
        xHOCHmPLUS1[0] = UE_subg(0,1);
        xHOCHmPLUS1[Grad] = 1;
        Faktor = (INT *) SYM_calloc(Basis[0],sizeof(INT));
        Faktor[0] = 0;
        grossElement[0] = Grad;

        for (i=1;i<=kleinGrad;i++)
            grossElement[i-1] = kleinElement[i];

        UE_Free(&kleinElement);

        for (i=kleinGrad;i<=Grad;i++)
            grossElement[i] = 0;
        k = 1;
        while(k && !spezEinsGGT(xHOCHmPLUS1,grossElement,Grad))
        {
            j = 0;
            while(Faktor[j]==Charakteristik-1)
            {
                Faktor[j] = 0;
                grossElement[j] = UE_subg(grossElement[j],1);
                grossElement[kleinGrad+j] = UE_addg(grossElement[kleinGrad+j],1);
                j++;
                if (j==Basis[0])
                {
                    SYM_free((char *) kleinPolynom);
                    SYM_free((char *) minPolynom);
                    SYM_free((char *) grossElement);
                    error("internal error FF206");
                    return ERROR;
                }
            }
            Faktor[j]++;
            grossElement[j] = UE_subg(grossElement[j],1);
            grossElement[kleinGrad+j] = UE_addg(grossElement[kleinGrad+j],1);
        }
        SYM_free((char*)xHOCHmPLUS1); /* AK 030294 */
        SYM_free((char*)minPolynom); /* AK 030294 */
        SYM_free((char *) kleinPolynom); /* AK 040293 */
        SYM_free((char*)Faktor); /* AK 030294 */
        for (i=Grad;i>0;i--)
            grossElement[i] = grossElement[i-1];
        grossElement[0] = Grad;
        minimalPolynom(grossElement,tracePolynom);
        UE_Free(& grossElement);  /* AK 030294 */
    }
    /****************************************************************************/
else /* Polynom erzeugen aus bestehenden
                                         Polynomen */
    {
        /* Belegung von Basis[i] mit Basis[i]^Potenz[i] */
        for(i=0;i<anzahlPrimfakt;i++)
            Basis[i] = UE_power(Basis[i],Potenz[i]);


        /* Erzeugung der bentigten Multiplikationstabellen */
        for (i=0;i<anzahlPrimfakt;i++)
        {
            if (erzmulttafel(Basis[i],1,NULL) != OK)
            {
                error("internal error FF207");
                return ERROR;
            }
            else
                multTafel[i]=Mult_Tafel;
        }

        /* Erzeugung der Multiplikationsmatrix aus den berechneten Tafeln */
        if(!(Mult_Tafel = (INT **) UE_malloc(Grad*sizeof(INT*))))
        {
            return no_memory();
        }

        if(!(UE_Platz_Mult = (INT *) UE_malloc(Grad*Grad*sizeof(INT))))
        {
            return no_memory();
        }

        k = 0;
        for (i=0;i<Grad;i++)
        {
            Mult_Tafel[i] = &UE_Platz_Mult[k];
            k += Grad;
        }

        for(j=0;j<Grad*Grad;j++)
            UE_Platz_Mult[j] = 1;

        for(k=0;k<Grad;k++)
            for(j=0;j<Grad;j++)
                for(i=0;i<anzahlPrimfakt;i++)
                    Mult_Tafel[k][j] *= multTafel[i][k%Basis[i]][j%Basis[i]];


        /* Um aus der Multiplikationstafel das zugehrige Polynom zu berechnen
        geht man wie folgt vor:
        Aufstellen der Basisdarstellung von 1,a,a^2,a^3, ... in Normalbasen-
        reprsentation == Matrix A
        Aufstellen des Vektors a^Grad in Normalbasenreprsentation = Vektor v
        Lsen des Gleichungssystems Ax = v  -> Lsung x ist a^Grad in Basis
        1,a,a^2,a^3, ... Tracecompatibles Polynom
        f(x) = x^Grad-v[Grad-1]*x^(Grad-1)-v[Grad-2]*x^(Grad-2)-....-v[0] . */

        /* Vorbereitungen */
        UE_Erw_Grad = Grad;
        if(!(Permutation = (INT *) UE_malloc(Grad*sizeof(INT))))
            return no_memory();
        if(!(Gauss = (INT **) UE_malloc(Grad*sizeof(INT*))))
        {
            SYM_free((char *) Permutation);
            return no_memory();
        }

        if(!(hilfsZeiger = (INT **) UE_malloc((Grad+1)*sizeof(INT*))))
        {
            SYM_free((char *) Permutation);
            SYM_free((char *) Gauss);
            return no_memory();
        }

        for(i=0;i<=Grad;i++)
            UE_Platz(&hilfsZeiger[i]);

        /* Belegung des 1-Elementes   */
        hilfsZeiger[0][0] = Grad;
        for(i=1;i<=Grad;i++)
            hilfsZeiger[0][i] = 1;
        /* Belegung von a^1 */
        hilfsZeiger[1][0] = Grad;
        hilfsZeiger[1][1] = 1;
        for(i=2;i<=Grad;i++)
            hilfsZeiger[1][i] = 0;

        /* Belegung von a^2 bis a^(Grad-1) */
        for(i=2;i<=Grad;i++)
            {
            globalno=1; /* AK 260104*/
            UE_mult(&hilfsZeiger[1],&hilfsZeiger[i-1],&hilfsZeiger[i]);
            globalno=0;
            }

        for(i=0;i<Grad;i++)
            Gauss[i] = &hilfsZeiger[i][1];

        /* transponieren von Gauss  */
        for(i=0;i<Grad-1;i++)
            for(j=i+1;j<Grad;j++)
            {
                k = Gauss[i][j];
                Gauss[i][j] = Gauss[j][i];
                Gauss[j][i] = k;
            }

        if (!gausszerlegu(Gauss,Grad,Permutation))
        {
            for(i=0;i<=Grad;i++)
                UE_Free(& hilfsZeiger[i]);

            SYM_free((char *) Permutation);
            SYM_free((char *) Gauss);
            SYM_free((char *) hilfsZeiger);
            error("internal error FF208"); return ERROR;
        }
        gaussaufloes(Gauss,Grad,&hilfsZeiger[Grad][1],Permutation);
        for(i=1;i<=Grad;i++)
            tracePolynom[i-1] = UE_subg(0,hilfsZeiger[Grad][i]);
        for(i=0;i<=Grad;i++)
            UE_Free(& hilfsZeiger[i]);

        SYM_free((char *) Permutation);
        SYM_free((char *) Gauss);
        SYM_free((char *) hilfsZeiger);
        SYM_free((char *) Mult_Tafel);
        SYM_free((char *) UE_Platz_Mult);

    }
    einfuegTrace(Grad,tracePolynom);
    return OK;
}


/******************************************************************************/
/* Funktion getString verwandelt eine Zahl in einen entsprechenden String im  */
/*                    10 'ner System.                                         */
/* bergabeparameter       Zahl : umzuwandelnde Zahl                          */
/*                         String       : Zeiger auf Platz fr String         */
/*                                                                            */
/* Rckgabeparameter : Lnge : Lnge des Zugehrigen Strings                  */
/******************************************************************************/
static INT getString(Zahl,String) INT Zahl; char *String;
{
    INT i=49;
    char hilfsString[50];

    if(Zahl == 0) { String[0] = '0'; return(1); }
    while(Zahl)
    {
        hilfsString[i--] = 48 + (Zahl % 10);
        Zahl /= 10;
    }
    Zahl = i;
    for (i=Zahl+1;i<=49;i++) String[i-Zahl-1] = hilfsString[i];
    return(49-Zahl);
}



INT get_ff_irred(OP p , OP deg, OP pol)
/* AK 211106 V3.1 */
/* the irreducible polynomial of given characteristic and degree, which is 
   used for the object type FF */
{
	INT erg = OK;
	INT *tp,i;
	OP z;
	Charakteristik=S_I_I(p);
	tp=(INT*)SYM_calloc(S_I_I(deg)+3,sizeof(INT));
	liestracepol(S_I_I(deg),tp,0);
	init(MONOPOLY,pol);z=pol;
	for (i=0;i<S_I_I(deg);i++)
		{
		C_L_S(z,callocobject());
		b_sk_mo(callocobject(),callocobject(),S_L_S(z));
		m_i_i(i,S_PO_S(z));
		m_i_i(tp[i],S_PO_K(z));
		C_L_N(z,callocobject()); z = S_L_N(z); init(MONOPOLY,z); 
		}

	C_L_S(z,callocobject());
	b_sk_mo(callocobject(),callocobject(),S_L_S(z));
	m_i_i(i,S_PO_S(z));
	m_i_i(1,S_PO_K(z));
	SYM_free(tp);
	ENDR("get_ff_irred");
}

/******************************************************************************/
/*   Funktion lies_tracepol liesst das tracecompatible Polynom zu gegebener   */
/*   Charakteristik und gegebenen Erweiterungsgrad ein.                       */
/*                                                                            */
/*   In der Datei trace_??.pol (?? stehen fr die Charakterisktik bei         */
/*      Charakteristik > 99 wird z.B. trac1021.pol gesucht)                   */
/*   wird nach 'G<GRAD>:' gesucht. Die nachfolgenden Zahlen enthalten die     */
/*   Positionen a[0] bis a[GRAD-1] des zugehrigen Polynoms.                  */
/*   Sollte dieses nicht vorhanden sein, versucht das Programm es zu erzeugen.*/
/*                                                                            */
/*   Rueckgabewert : 0 , falls das Polynom nicht initialisiert werden konnte, */
/*                   1 , sonst.                                               */
/*                                                                            */
/*                                   Verfasser: Ulrich Eidt                   */
/*                                   Stand    : 16.01.94                       */
/******************************************************************************/
static INT liestracepol(Grad,tracePolynom,DateiOffen)
    INT Grad;           /* Gibt den gewuenschten Erweiterungsgrad an.            */
    INT tracePolynom[]; /* Vektor mit Platz fuer die EINTraege des ermittelten   */
/* Polynoms (die i-te Stelle von tracePolynom gibt den   */
/* Koeffizienten zu x^i an der hoechste Koeffizient wird */
/* (da normiert) nicht belegt)).                         */
    INT DateiOffen;     /* Kennzeichen ob die Datei bereits offen ist */
{
    INT datneu = 0;     /* Kennzeichen ob Datei neu  */
    INT gefunden = 0;   /* Kennzeichen ob Polynom gefunden */
    INT zahl;           /* Einlesevariable */
    /* INT gelesen=1;*/      /* Anzahl der gelesenen Zeichen, 0 falls Dateiende*/
    INT Pufferzeiger=0; /* Zeiger fuer Bearbeitung des Puffer             */
    INT hilfsChar=Charakteristik;
    INT i;
    INT ret_val = OK;    /* Rckgabewert */
    char Puffer[50];             /* Einlesepuffer            */
    char Dateiname[15] ; /* Name der Datei                   */
    char Zeichen;       /* Platz fuer ein Zeichen wird benutzt beim       */
    /*  Einlesen des Polynoms                         */
    strcpy(Dateiname,"trace_00.pol");

    if (!DateiOffen)
    {
        /* Datei oeffnen und erstes Zeichen lesen     */
        if(Charakteristik<100)
        {
            Dateiname[6] = 48+(Charakteristik / 10);
            Dateiname[7] = 48+(Charakteristik % 10);
        }
        else
            if(Charakteristik>=100000000)
            { error("ff.c:internal error FF50"); return(0); }
            else
            {
                i = 7;
                while(hilfsChar)
                {
                    Dateiname[i--] = 48 + (hilfsChar % 10);
                    hilfsChar /= 10;
                }
            }

        Datei = fopen(Dateiname,"a+");
        if (Datei == NULL)
        {
/*
            Datei = fopen(Dateiname,"w");
            if (Datei == NULL)
            {
*/
                /*printf("Die Datei %s ist nicht erstellbar !\n",Dateiname);*/
                // error("ff.c:internal error FF51");
                if (erzeugePol(Grad,tracePolynom,0) != OK) 
                     return error("ff.c: internal error FF516");
                return OK;
/*
            }
            datneu = 1;
*/
        }
    }
    Puffer[0] = 'G';
    Pufferzeiger = getString(Grad,&(Puffer[1]));
    Puffer[Pufferzeiger+1] = ':';
    Pufferzeiger += 2;

    /* Suchen des Strings ('G<GRAD>:')      */
    fseek(Datei,0,0);
    i = 0;
    while(!gefunden && (Zeichen = getc(Datei)) != (char)EOF)
    {
        if(Zeichen==Puffer[i])
            i++;
        else
            i = 0;

        if (i==Pufferzeiger)
            gefunden = 1;
    }
    /* falls gefunden -> Einlesen */
    if (gefunden)
    {
        for (i=0;i<Grad;i++)
        {
            /* */ 
            zahl = 0;
            while((Zeichen = getc(Datei)) != (char)32 && 
                   Zeichen != (char)10 && (ret_val==OK))
            {
                if (Zeichen < (char)48 || Zeichen > (char)57)
                { error("ff.c: internal error FF55"); ret_val = ERROR; }
                else
                    zahl = zahl*10+(int)Zeichen-48;
            }
            tracePolynom[i] = zahl;
        }
    }
    else
    {
        if (erzeugePol(Grad,tracePolynom,1) != OK)
        {
            error("ff.c: internal error FF56");
            fclose(Datei);
            ret_val = ERROR;
        }
    }
    if (!DateiOffen)
        {
        fclose(Datei);
        Datei = NULL;  /* AK 260104 */
        }
    return(ret_val);
}


INT generators_glnq(n,p,k,v) OP n,p,k,v;
/* AK 210104 */
/* Two generating matrices of GL(n,p^k) */
{
    OP y,z; INT i,j;
    OP nv,ev,nev;
    INT erg = OK;
    CTO(INTEGER,"generators_glnq(1)",n);
    CTO(INTEGER,"generators_glnq(2)",p);
    CTO(INTEGER,"generators_glnq(3)",k);

    SYMCHECK(S_I_I(n)<1,"generators_glnq:degree not > 0 ");
    SYMCHECK(S_I_I(k)<1,"generators_glnq:power not > 0 ");
    SYMCHECK(primep(p)==FALSE,"generators_glnq:p not prime ");
    CE4(n,p,k,v,generators_glnq);
    CALLOCOBJECT3(nv,ev,nev);

    erg += m_l_nv(k,nv);
    erg += m_l_v(k,ev);FORALL(z,ev,{m_i_i(1,z);});
    erg += m_l_v(k,nev);FORALL(z,nev,{m_i_i(S_I_I(p)-1,z);});
    erg += m_il_v(2,v);
    z=S_V_I(v,0);
    erg += m_lh_m(n,n,z);
    FORALL(y,z,{ m_vector_ff(p,nv,y); });
    erg += m_vector_ff(p,ev,S_M_IJ(z,0,S_M_LI(z)-1));
    erg += m_vector_ff(p,nev,S_M_IJ(z,0,0));
    for (i=0;i<S_M_LI(z)-1;i++) m_vector_ff(p,nev,S_M_IJ(z,i+1,i));
    z=S_V_I(v,1);
    erg += m_lh_m(n,n,z);
    FORALL(y,z,{ m_vector_ff(p,nv,y); });
    erg += primitive_element_ff(p,k,S_M_IJ(z,0,0));
    for (i=1;i<S_M_LI(z);i++) m_vector_ff(p,ev,S_M_IJ(z,i,i));
    FREEALL3(nv,ev,nev);
    ENDR("generators_glnq");
}




INT primitive_element_ff_given_q(q,b) OP b; OP q;
/* AK 090304 */
{
    INT erg = OK;
    CTO(INTEGER,"primitive_element_ff_given_q(1)",q);
    SYMCHECK(S_I_I(q) < 2,"primitive_element_ff_given_q:q<2");
    SYMCHECK(prime_power_p(q) ==FALSE,"primitive_element_ff_given_q:q no prime power");
    {
    OP v;
    v = CALLOCOBJECT();
    erg += factorize_integer(q,v);
    erg += primitive_element_ff(S_V_I(v,0),S_V_L(v),b);
    FREEALL(v);
    }
    ENDR("primitive_element_ff_given_q");
}

INT primitive_element_ff(p,k,c) OP p,k,c;
/* AK 210104 */
/* primitive element in GF(p^k) */
{
   INT erg = OK;
   OP e,a;
   INT i;
   CE3(p,k,c,primitive_element_ff);
   CTO(INTEGER,"primitive_element_ff(1)",p);
   CTO(INTEGER,"primitive_element_ff(2)",k);
   SYMCHECK(S_I_I(k)<=0,"primitive_element_ff:degree>0");
   SYMCHECK(primep(p)==FALSE,"primitive_element_ff:ip not a prime");
   e=callocobject(),a=callocobject();
   hoch (p,k,a);
   first_ff(p,k,e); next(e,e); /* otherwise zero */
       do {
          copy(e,c);
          i = 1;
  bb:
          if (einsp(c) && (i==S_I_I(a)-1)) {  copy(e,c); break; }
          if (einsp(c)) continue;
          i++; mult_apply(e,c);
          goto bb;
          } while(next(e,e));
   FREEALL2(a,e);
   ENDR("primitive_element_ff");
}


INT generators_slnq(n,p,k,v) OP n,p,k,v;
/* AK 220104 */
/* generator of SL(n,p^k) */
{
    OP y,z; INT i,j;
    OP nv,ev,nev;
    INT erg = OK;
    CTO(INTEGER,"generators_slnq(1)",n);
    CTO(INTEGER,"generators_slnq(2)",p);
    CTO(INTEGER,"generators_slnq(3)",k);

    SYMCHECK(S_I_I(n)<1,"generators_slnq:degree not > 0 ");
    SYMCHECK(S_I_I(k)<1,"generators_slnq:power not > 0 ");
    SYMCHECK(primep(p)==FALSE,"generators_slnq:p not prime ");
    CE4(n,p,k,v,generators_slnq);

    nv = callocobject(); m_l_nv(k,nv);
    ev = callocobject(); m_l_v(k,ev);FORALL(z,ev,{m_i_i(1,z);});
    nev = callocobject(); m_l_v(k,nev);FORALL(z,nev,{m_i_i(S_I_I(p)-1,z);});
    erg += m_il_v(2,v);
    z=S_V_I(v,0);
    erg += m_lh_m(n,n,z);
    FORALL(y,z,{ m_vector_ff(p,nv,y); });
    erg += m_vector_ff(p,ev,S_M_IJ(z,0,S_M_LI(z)-1));
    erg += m_vector_ff(p,nev,S_M_IJ(z,0,0));
    for (i=0;i<S_M_LI(z)-1;i++) m_vector_ff(p,nev,S_M_IJ(z,i+1,i));
    z=S_V_I(v,1);
    m_lh_m(n,n,z);
    FORALL(y,z,{ m_vector_ff(p,nv,y); });
    
    if (((S_I_I(p)==2)||(S_I_I(p)==3) )&&(einsp(k)))
    {
    erg += m_vector_ff(p,ev,S_M_IJ(z,0,0));
    erg += m_vector_ff(p,ev,S_M_IJ(z,0,1));
    erg += m_vector_ff(p,ev,S_M_IJ(z,1,1));
    }
    else {
    erg += primitive_element_ff(p,k,S_M_IJ(z,0,0));
    erg += invers(S_M_IJ(z,0,0),S_M_IJ(z,1,1));
    }
    for (i=2;i<S_M_LI(z);i++) m_vector_ff(p,ev,S_M_IJ(z,i,i));
    FREEALL3(nv,ev,nev);
    ENDR("generators_slnq");
}

INT rank_ff(a,b) OP a,b;
/* number between 0 ... q-1 
   for a from GF(q) */
/* a and b may be equal */
/* AK 151204 V3.0 */
{
    INT erg = OK;
    CTO(FF,"rank_ff(1)",a);
    {
    OP res,q,ql,h;
    INT i;
    CALLOCOBJECT4(res,q,ql,h);
    M_I_I(0,res);
    M_I_I(S_FF_CI(a),q);
    M_I_I(1,ql);
     
    for (i=0;i<S_FF_DI(a);i++)   
    // for (i=S_FF_DI(a)-1;i>=0;i--) AK 290607
        {
        erg += m_i_i(S_FF_II(a,i+1),h);
        MULT_APPLY(ql,h);
        ADD_APPLY(h,res);
        MULT_APPLY(q,ql);
        }
    SWAP(b,res);
    FREEALL4(res,q,ql,h);
    }
    ENDR("rank_ff");
}

INT unrank_given_q_ff(a,q,b) OP a,q,b;
/* a,b may be equal */
/* AK 161204 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"unrank_given_q_ff(1)",a);
    SYMCHECK(NEGP(a),"unrank_given_q_ff(1):negative number");
    CTO(INTEGER,"unrank_given_q_ff(2)",q);
    SYMCHECK(prime_power_p(q)==FALSE,"unrank_given_q_ff(2): no prime power");
    {
    OP v=CALLOCOBJECT();
    OP res=CALLOCOBJECT();
    OP ca=CALLOCOBJECT();
    OP h=CALLOCOBJECT();
    INT *ip,i;
    factorize(q,v); /* v is vector of equal primes */
    Charakteristik=S_V_II(v,0); 
    UE_Erw_Grad=S_V_LI(v);
    erg += init_ff(res);
    M_I_I(Charakteristik,S_FF_C(res));
    ip = S_FF_IP(res);
    ip[0]=S_V_LI(v);
    COPY(a,ca);
    for (i=0;i<S_V_LI(v);i++)
        {
        mod(ca,S_V_I(v,0),h); ip[i+1]=S_I_I(h);
        ganzdiv(ca,S_V_I(v,0),ca);
        }
    SWAP(res,b);
    FREEALL4(v,res,ca,h);
    }
    ENDR("unrank_given_q_ff");
}


#endif /* FFTRUE */

/* outside because of macro */
INT freeself_ff(a) OP a;
/* AK 100393 */ /* AK 290402 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(FF,"freeself_ff(1)",a);
    {
#ifdef FFTRUE
    UE_Free( & S_FF_IP(a)); /* AK 200802 */
    C_O_K(a,VECTOR);
    freeself_vector(a);
#endif
    }
    ENDR("freeself_ff");
}
/* outside because of macro */
INT add_apply_ff(a,b) OP a,b;
/* AK 170393 */ /* b = b+a */
{
    INT erg = OK;
#ifdef FFTRUE
    CTO(FF,"add_apply_ff(1)",a);
    if (S_O_K(b) == POLYNOM)  /* AK 170304 */
        {
        OP c=callocobject();
        erg += m_scalar_polynom(a,c);
        ADD_APPLY(c,b);
        erg += freeall(c);
        goto endr_ende;
        }
    else if (S_O_K(b) != FF) /* AK 230294 */ cast_apply_ff(b);
    CTO(FF,"add_apply_ff(2)",b);
    SYMCHECK(S_FF_CI(a) != S_FF_CI(b), "add_ff:different characteristic");

    if( (S_FF_DI(a) == 1) && (S_FF_DI(b)==1) ) { /* AK 270705 */
        INT *bp;
        bp = S_FF_IP(b); 
        bp[1]=(S_FF_II(b,1)+S_FF_II(a,1)) % Charakteristik;
        }
    else
        erg += UE_add(& S_FF_IP(a), &S_FF_IP(b), &S_FF_IP(b));
#endif
    ENDR("add_apply_ff");
}
/* outside because of macro */

INT multadd_apply_ff(a,b,c) OP a,b,c;
/* AK 170607 */
/* c += a*b */
{
	INT erg =OK;
	SYMCHECK(S_FF_CI(a)!=S_FF_CI(b),"multadd_apply_ff:different characteristic");
	SYMCHECK(S_FF_CI(a)!=S_FF_CI(c),"multadd_apply_ff:different characteristic");
	if ((S_FF_DI(a)==1) && (S_FF_DI(b)==1) && (S_FF_DI(c)==1))
		{
		INT *ip,*jp,*kp;
		ip = S_FF_IP(a);
                jp = S_FF_IP(b);
                kp = S_FF_IP(c);
		kp[1]=kp[1]+ip[1]*jp[1];
		kp[1]=kp[1]%S_FF_CI(c);
		}
	else
		multadd_apply_default(a,b,c);
	ENDR("multadd_apply_ff");
}


INT mult_apply_ff(a,b) OP a,b;
/* AK 170393 */ /* AK 211204 V3.0 */
{ 
    INT erg = OK;
    CTO(FF,"mult_apply_ff(1)",a);
    CE2A(a,b,mult_apply_ff);
    {
    switch(S_O_K(b)) 
    {
    case FF:
        {
        OP c; INT *ip, *jp;
        SYMCHECK(S_FF_CI(a)!=S_FF_CI(b),"mult_apply_ff:different characteristic");
	if ((S_FF_DI(a)==1) && (S_FF_DI(b)==1)) { /* easy multiplication */
		ip = S_FF_IP(a);
		jp = S_FF_IP(b);
                jp[1]*=ip[1];
		jp[1]=jp[1]%S_FF_CI(b);
		goto endr_ende;
		}
        c = CALLOCOBJECT();
        SWAP(b,c);
        erg += mult_ff_ff(a,c,b);
        FREEALL(c);
        goto endr_ende;
        }
    case MATRIX:
    case VECTOR:
        {
        OP z;
        FORALL(z,b,{ erg += mult_apply_ff(a,z); } );
        goto endr_ende;
        }
    default:
        erg+= mult_apply_default(a,b); 
        break;
    }
    }
    ENDR("mult_apply_ff");
}

/* outside because of macro */
INT nullp_ff(a) OP a;
/* AK 110804 V3.0 */
    { 
#ifdef FFTRUE
    /* return UE_ist_null(& S_FF_IP(a));  */
    /* UE_IST_NULL( (& S_FF_IP(a)));  */
    if (S_FF_DI(a) > MAXDEGREE) { UE_IST_NULL( (& S_FF_IP(a))); }
    else {
         INT *ip = S_FF_IP(a);
         INT res,res2;
         res=memcmp(ip+1, null_ip, S_FF_DI(a)* sizeof(INT));
         // res2=UE_ist_null(& S_FF_IP(a));
         // printf("res = %d is_null=%d\n", res, res2);
         if (res == 0) return 1; else return 0;
         // return res2;
         }
#endif /* FFTRUE */
    }

/* outside because of macro */
INT mult_ff(a,b,c) OP a,b,c;
/* AK 070802 */
{
    INT erg = OK;
#ifdef FFTRUE
    CTO(FF,"mult_ff(1)",a);
    CTTO(FF,EMPTY,"mult_ff(3)",c);
    if (S_O_K(c)==FF) FREESELF(c);
    switch(S_O_K(b))
        {
        case INTEGER:
            erg += mult_ff_integer(a,b,c);
            break;
        case FF:
            if (nullp_ff(a)) 
                erg += null_ff(a,c);
            else
                erg += mult_ff_ff(a,b,c);
            break;
        case MATRIX: /* AK 300304 */
            erg += mult_scalar_matrix(a,b,c);
            break;
        case MONOM:
            erg += mult_scalar_monom(a,b,c);
            break;
        case POLYNOM:
            erg += mult_scalar_polynom(a,b,c);
            break;

#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case VECTOR:
            erg += mult_scalar_vector(a,b,c);
            break;
#endif /* VECTORTRUE */ 

        default: 
            WTO("mult_ff(2)",b);
            break;
        }
#endif /* FFTRUE */
    ENDR("mult_ff");
}
INT null_ff(a,b) OP a,b;
/* given a finite field element, compute the corresponding 0 element */
/* AK 040803 */
/* AK 210704 V3.0 */
{
    INT erg =OK;
    CTO(FF,"null_ff(1)",a);
    {
#ifdef FFTRUE

    INT i,*ip;
    Charakteristik=S_FF_CI(a);
    UE_Erw_Grad=S_FF_DI(a);
    erg += init_ff(b); 
    ip = S_FF_IP(b);
    for (i=0;i<UE_Erw_Grad;i++) ip[i+1]=0;
    ip[0]=UE_Erw_Grad;
    M_I_I(Charakteristik,S_FF_C(b));
    erg += erzmulttafel(UE_Erw_Grad,(INT)0,NULL); /* UWH */

#endif
    }
    CTO(FF,"null_ff(2e)",b);
    ENDR("null_ff");
}

INT eins_ff(a,b) OP a,b;
/* given a finite field element, compute the corresponding 1 element */
/* AK 040803 */
/* AK 210704 V3.0 */
{
    INT erg =OK;
    CTO(FF,"eins_ff(1)",a);
    {
#ifdef FFTRUE

    INT i,*ip;
    Charakteristik=S_FF_CI(a);
    UE_Erw_Grad=S_FF_DI(a);
    erg += init_ff(b);
    ip = S_FF_IP(b);
    for (i=0;i<UE_Erw_Grad;i++) ip[i+1]=1;
    ip[0]=UE_Erw_Grad;
    M_I_I(Charakteristik,S_FF_C(b));
    erg += erzmulttafel(UE_Erw_Grad,(INT)0,NULL); /* UWH */
#endif
    }
    ENDR("eins_ff");
}

INT all_irred_polynomials(n,q,res) OP n,q,res;
/* all irreducible polynomials of degree n with coeffs 
   from GF(q)   q prime */
/* AK 290304 */
/* AK 210704 V3.0 */
{
   INT erg = OK;
   CTO(INTEGER,"all_irred_polynomials(1)",n);
   SYMCHECK(S_I_I(n)<1,"all_irred_polynomials:degree < 1");
   CTO(INTEGER,"all_irred_polynomials(2)",q);
   SYMCHECK(prime_power_p(q)==FALSE,"all_irred_polynomials(2): no prime power");
   {
#ifdef FFTRUE
   if (einsp(n) )
      {
      OP mox,mcons,ff; INT i=0;
      mox=CALLOCOBJECT(); m_iindex_monom(0,mox);
      eins_ff_given_q(q,S_PO_K(mox));
      CALLOCOBJECT2(ff,mcons);
      first_ff_given_q(q,ff);
      m_l_v(q,res); 
         /* there are q different irreducible polynomials of degree 1 */
      do {
         m_scalar_polynom(ff,mcons);
         add(mcons,mox,S_V_I(res,i));
         i++;
         } 
      while(next_apply(ff));
      FREEALL3(mox,mcons,ff);
      }
   else
   {
   OP nn,fac,ff2,d,c,mox,ff;INT i,j,k=1,l,counter=0;
   CALLOCOBJECT6(c,d,ff,ff2,fac,nn);

   hoch(q,n,c);primitive_element_ff_given_q(c,ff);
   DEC(c);m_l_nv(c,c);m_il_v(0,res);
   mox=CALLOCOBJECT(); m_iindex_monom(0,mox);
   eins_ff_given_q(q,S_PO_K(mox));
   /* in bahnen zerlegen */
   for (i=0;i<S_V_LI(c);i++)
       if (S_V_II(c,i)==0) /* new orbit */
          {
          eins_ff_given_q(q,nn);
          l=1;j=i;
ww:
          M_I_I(k,S_V_I(c,j));m_i_i(j,d);
          hoch(ff,d,ff2);addinvers_apply(ff2);
          add(mox,ff2,fac); /* fac =  x-primitive^i */
          mult_apply(fac,nn);

          j = (S_I_I(q)*j) % S_V_LI(c);
          if (S_V_II(c,j)==0) { l++; goto ww; }
          else if (S_V_II(c,j)==k) {

              if (l==S_I_I(n)) {
                 OP z;
                 inc(res);
                 FORALL(z,nn,{ reduce_ff(S_MO_K(z)); });
                 swap(S_V_I(res,S_V_LI(res)-1),nn);
                 }
              k++; continue;
              }
          else {
               error("all_irred_polynomials:internal");
               }
          }
   FREEALL3(c,ff,mox);FREEALL4(d,ff2,fac,nn);
   }
#endif
   }
   ENDR("all_irred_polynomials");
}


static INT make_vector_given_q_co();
static INT make_matrix_given_q_co();

INT make_matrix_add_given_q(q,v) OP q,v;
{ return make_matrix_given_q_co(q,v,0); }
INT make_matrix_mult_given_q(q,v) OP q,v;
{ return make_matrix_given_q_co(q,v,1); }

INT make_vector_addinvers_given_q(q,v) OP q,v;
/* vector entry at position i is the rank number of the additiv invers to the
   GF(q) element with rank number i */
{ return make_vector_given_q_co(q,v,0); }

INT make_vector_multinvers_given_q(q,v) OP q,v;
/* vector entry at position i is the rank number of the multiplikativ invers to the
   GF(q) element with rank number i */
{ return make_vector_given_q_co(q,v,1); }
INT make_vector_frobenius_given_q(q,v) OP q,v;
/* vector entry at position i is the rank number of the frobenius image to the
   GF(q) element with rank number i */
{ return make_vector_given_q_co(q,v,2); }

static INT make_matrix_given_q_co(q,v,s) OP q,v;INT s;
{
	INT erg = OK;
	{
	OP l,r,m,n;
	INT i,j;
	CALLOCOBJECT4(m,l,r,n);
	m_lh_m(q,q,v);
	for (i=0;i<S_M_HI(v);i++)
	for (j=0;j<S_M_LI(v);j++)
		{
		m_i_i(i,r);
		m_i_i(j,m);
		unrank_given_q_ff(r,q,l);
		unrank_given_q_ff(m,q,n);
		if (s==0) add_apply_ff(l,n);
		else if (s==1) mult_apply_ff(l,n);
		rank_ff(n,m);
		SWAP(m,S_M_IJ(v,i,j));
		}
	FREEALL4(m,l,r,n);
	}
	ENDR("make_matrix_given_q_co");
}

static INT make_vector_given_q_co(q,v,s) OP q,v;INT s;
{
	INT erg = OK;
	{
	OP l,r;
	INT i=0;
	CALLOCOBJECT2(l,r);
	m_l_v(q,v);
	m_i_i(0,r);
	do {
		unrank_given_q_ff(r,q,l);
		if (s==0) addinvers_apply_ff(l);
		else if (s==1) {
				if (i!=0) invers_apply_ff(l);
				}
		else if (s==2) {
				UE_hoch( & S_FF_IP(l) ,Charakteristik,& S_FF_IP(l)  );
				}
		rank_ff(l,r);
		SWAP(r,S_V_I(v,i));
		i++;
		m_i_i(i,r);
		} while (lt(r,q));
	FREEALL2(l,r);
	}
	ENDR("make_vector_given_q_co");
	
}


   
