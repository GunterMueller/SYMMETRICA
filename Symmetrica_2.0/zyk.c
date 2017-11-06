
/* Routinen zur Berechnung von Zykelindikatorpolynomen
 * Nikolaus Schueler 90/91
 */
#include "def.h"
#include "macro.h"

/* Hier wird eigenes FALSE und TRUE eingefuehrt , weil es sich
 * hier im Gegensatz zu def.h auf unsigned short bezieht
 */
#define N_FALSE 0 
#define N_TRUE 1


#define OFFSET 0
/* diverse prozeduren zu den zykelindikatorpolynom- programmen */


#ifdef PERMTRUE
#ifdef VECTORTRUE
#ifdef MATRIXTRUE
#ifdef PARTTRUE
#ifdef POLYTRUE
#define ZYKTRUE
#endif
#endif
#endif
#endif
#endif

#ifdef ZYKTRUE


static INT colltypes();
static INT strongen();
static INT polyasub();

/* Die beiden naechsten Routinen werden zur Berechnung des 
 * Zykelindikators der zyklischen Gruppe benoetigt
 */

/* liefert den gcd (greatest common divisor) von a und b zurueck */

static INT gcd(a,b) INT a,b;
/* NS 060891 V1.3 */
{
    INT c=5L; /* AK 240692 ERROR muss initialisiert werden */

    /* a soll immer den groesseren Wert enthalten */
    if (b > a) { c=b;b=a;a=c; }  
    /* Euklidischer Algorithmus */
    while(c != 0L)
    {
        c=a%b; /* c ist der Rest  bei der Division */
        a=b; b=c;
    }
    return(a);
}

static INT eulerfunc(n) INT n;
/* NS 060891 V1.3 */
{
    INT i,h=0L;

    if(n == 1L) return(1L);
    for(i=1L; i < n; i++)
    {
        if(gcd(n,i) == 1L) 
        {
            h++;
        }
    }
    return(h);
}
/* Berechnet das Zykelindikatorpolynom der Cn */   

#ifdef BRUCHTRUE
INT zykelind_Cn(l,pol) OP l; OP pol;
/* NS 060891 V1.3 */
{
    INT d,li;
    INT erg = OK;
    OP b;

    CTO(INTEGER,"zykelind_Cn",l);
    if (S_I_I(l) < 1L) /* AK 060792 */
        {
        error("zykelind_Cn: input < 1");
        goto endr_ende;
        }


    init(POLYNOM,pol);
        
    if (einsp(l)) /* AK 060792 */
        {
        erg += m_iindex_monom(0L,pol);
        goto endr_ende;
        }

    b=callocobject();
    li=S_I_I(l);    
    for(d=1L; (d <= li) ; d++)
        if(li%d == 0L)
        {
        /* stopf den Koeffizienten in den Typ BRUCH von symchar */
        /* stopf das Ergebnis in den Typ POLYNOM von symchar */
            erg += b_skn_po(callocobject(),callocobject(),NULL,b);
            erg += m_ioiu_b(eulerfunc(d),li,S_PO_K(b)); 
                        erg += kuerzen(S_PO_K(b));
            erg += m_il_nv(li,S_PO_S    (b));
            erg += m_i_i(li/d,S_PO_SI(b,d-1L));
            erg += add_apply(b,pol);
        }
    erg += freeall(b);
    ENDR("zykelind_Cn");
}
#endif /* BRUCHTRUE */

/* Berechnet das Zykelindikatorpolynom der Dn */   
/* Beruht auf dem Programm fuer den Zykelindex der Cn, da fuer
 * den Zykelindex der Diedergruppe Dn nur ein Summand dazukommt
 * , ruft zykelind_Cn auf.
 */

INT zykelind_Dn(l,pol) OP l; OP pol;
/* NS 060891 V1.3 */
{
#ifdef BRUCHTRUE
    INT len,erg=OK;
    OP b,halb,hilf;

        CTO(INTEGER,"zykelind_Dn(1)",l);
        SYMCHECK( S_I_I(l) < 1L,"zykelind_Dn: input < 1");


    len=S_I_I(l);

    init(POLYNOM,pol);
        

    if (einsp(l)) /* AK 060792 */
        return m_iindex_monom(0L,pol);

    /* Berechne den Zykelindiktor der Cn */

    zykelind_Cn(l,pol);

    b=callocobject();
    halb=callocobject();
    hilf=callocobject();

    /* Vorfaktor 1/2 */
    div(pol,cons_zwei,pol);

    /* Anhaengen der zusaetzlichen Summanden */

    b_skn_po(callocobject(),callocobject(),NULL,b);
    m_l_nv(l,S_PO_S    (b)); 

    /* Wenn m gerade ist ..*/

    if((long)len%2L == 0L)
    {
        erg += m_ioiu_b(1L,4L,S_PO_K(b));
                erg += kuerzen(S_PO_K(b));
        m_i_i(len/2L,S_PO_SI(b,1L));
        add_apply(b,pol); /* addiere die zusaetzlichen Summanden */
        erg += m_ioiu_b(1L,4L,S_PO_K(b));
                erg += kuerzen(S_PO_K(b));
        m_i_i(2L,S_PO_SI(b,0L));
        m_i_i((len-2L)/2L,S_PO_SI(b,1L));
        erg += add_apply(b,pol); /* addiere die zusaetzlichen Summanden */
    }        

    /* Wenn m ungerade ist .. */

    if(len%2L == 1L)
    {
        m_ioiu_b(1L,2L,S_PO_K(b));
                kuerzen(S_PO_K(b));

        /* y1 in das Polynom eintragen */

        m_i_i(1L,S_PO_SI(b,0L)); 

        /* y2 hoch (n-1L)/2 in das Polynom eintragen */

        m_i_i(((long)len-1L)/2L,S_PO_SI(b,1L)); 
        add_apply(b,pol); /* addiere die zusaetzlichen Summanden */
    }        
    freeall(b);
    freeall(halb);
    freeall(hilf);
    ENDR("zykelind_Dn");
#endif /*BRUCHTRUE*/
}
/* Berechnet das Zykelindikatorpolynom der An */   


INT zykelind_An(l,pol) OP l; OP pol;
/* NS 060891 V1.3 */
{
#ifdef BRUCHTRUE
    INT i,j,veklen,veklen2;

    OP a;
    OP hilf;
    OP k;
    OP n;
    OP v;
    OP party;
    OP zahl;
    OP zwisch;

    if (S_O_K(l) != INTEGER)  /* AK 060792 */
        return error("zykelind_An: input not INTEGER");
    if (S_I_I(l) < 1L) /* AK 060792 */
        return error("zykelind_An: input < 1");

    if (einsp(l)) /* AK 040692 */
        {
        return m_iindex_monom(0L,pol);
        }

    init(POLYNOM,pol);

    a = callocobject();
    hilf=callocobject();
    k=callocobject();
    n = callocobject();
    v = callocobject();
    party = callocobject();
    zahl = callocobject();
    zwisch = callocobject();

    b_skn_po(callocobject(),callocobject(),NULL,a);

    /* lasse alle partitionen berechnen */

    makevectorofpart(l,v); 
    veklen=S_V_LI(v);
    m_l_nv(l,S_PO_S    (a));  /* AK 040692 Macro */
    for(i=0L; i < veklen ; i++)
    {
        /* umwandeln in Exponentenschreibweise */
        t_VECTOR_EXPONENT(S_V_I(v,i),party);
        /* und umwandeln in ein Monom */
        copy(S_PA_S(party),S_PO_S    (a));  /* AK 040692 Macro */
         
        veklen2=S_V_LI(S_PO_S    (a));  /* AK 040692 Macro */
        m_i_i(0L,zwisch); /* Variable entleeren */

        for(j=1L; j < veklen2; j+=2L)
        {
        /* addiere a[2], a[4], ... auf */
        add_apply(S_PO_SI(a,j),zwisch);  /* AK 040692 statt add */
        }    
        /* Nur wenn a[2]+a[4]+... ungerade ist, dann gibts einen Koeff-
         * izienten 
         */
        if(even(zwisch))
        {
            /* Berechnen der Koeffizienten */

            m_i_i(1L,k);
            for(j=0L; j < veklen2; j++)
            {
                fakul(S_PO_SI(a,j),zwisch);
                mult(k,zwisch,k);
                m_i_i(j+1L,zahl);
                hoch(zahl,S_PO_SI(a,j),zwisch);
                mult(k,zwisch,k);
            }
            m_i_i(2L,zwisch);
            m_ou_b(zwisch,k,S_PO_K(a));
            kuerzen(S_PO_K(a));
            add_apply(a,pol); /* AK 040692 statt add */
        }
    }
    freeall(a);
    freeall(hilf);
    freeall(k);
    freeall(n);
    freeall(party);
    freeall(v);
    freeall(zahl);
    freeall(zwisch);
    return OK;
#else /* BRUCHTRUE */
    return error("zykelind_An: BRUCH not available");
#endif /* BRUCHTRUE */
}
/* 
 * Berechnet das Zykelindikatorpolynom der Sn    
 */


INT zykelind_Sn(l,pol) OP l; OP pol;
/* NS 060891 V1.3 */
/* AK 300998 V2.0 */
/* l and pol may be equal */
{
    INT erg = OK;

    CTO(INTEGER,"zykelind_Sn(1)",l);
    SYMCHECK(S_I_I(l)<1,"zykelind_Sn(1): input < 1");
    {
    INT i,j,veklen,veklen2;
    OP a,hilf,k,v,party,zahl,zwisch;

    CALLOCOBJECT4(a,k,hilf,party);
    CALLOCOBJECT3(v,zahl,zwisch);

    erg += b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,a);

    erg += makevectorofpart(l,v); 
    veklen=S_V_LI(v);
    erg += m_l_nv(l,S_PO_S    (a));
    erg += init(POLYNOM,pol);
    for(i=0L; i < veklen ; i++)
    {
        /* umwandeln in Exponentenschreibweise */
        erg += t_VECTOR_EXPONENT(S_V_I(v,i),party); 
        /* und umwandeln in ein Monom */
        CLEVER_COPY(S_PA_S(party),S_PO_S(a));
         
        /* Berechnen der Koeffizienten */

        m_i_i(1,k);
        veklen2=S_V_LI(S_PO_S    (a));
        for(j=0L; j < veklen2; j++)
        {
            erg += fakul(S_V_I(S_PO_S(a),j),zwisch);
            MULT_APPLY(zwisch,k);
            M_I_I(j+1,zahl);
            erg += hoch(zahl,S_V_I(S_PO_S(a),j),zwisch);
            MULT_APPLY(zwisch,k);
        }
        erg += invers(k,S_PO_K(a));
        ADD_APPLY(a,pol);
    }
    FREEALL4(a,k,hilf,party);
    FREEALL3(v,zahl,zwisch);
    }
    ENDR("zykelind_Sn");
}

/* Hier folgen die Routinen fuer die Berechnung der Zykel-
 * indizes von beliebigen Permutationsgruppen, die durch
 * erzeugende Permutationen gegeben sind
 */
/* routinen zur berechnung eines starken Erzeugers nach Hoffmann 
 */


struct treecomp {
    unsigned short atr; /* 0=FALSE, 1=TRUE */
    INT gen;
    INT point;
};

static INT stabilizer(i,vec,stabi) INT i; OP vec; OP stabi;
/* NS 060891 V1.3 */
/* AK 101291 vec ist VECTOR of PERMUTATION
             stabi wird VECTOR of PERMUTATION */
{
    unsigned short is_stab;
    INT j,k; /* Schleifenzaehler */
    INT veclen;

    m_il_v(0L,stabi); /* stabi is freed first */

    veclen=S_V_LI(vec);
    for(j=0L; j < veclen; j++)
    {
        is_stab=N_TRUE;
        for(k=0 ; k < i-1L; k++)
        {
            if(S_P_II(S_V_I(vec,j),k) != k+1L)
            {    
                is_stab=N_FALSE;
                break;
            }
        }
        if(is_stab)
        {
            inc(stabi);
            copy(S_V_I(vec,j),S_V_I(stabi,S_V_LI(stabi)-1L));
        }
    }
    return OK;
}

static INT updatemat(degree,i,tree,stabi,repma) 
    INT degree,i; struct treecomp *tree; OP stabi,repma;
/* NS 060891 V1.3 */
{
    INT l,next;
    OP id=callocobject();
    OP ob_degree=callocobject();
    OP operm=callocobject();

    m_i_i(degree,ob_degree);
    first_permutation(ob_degree,id);

    /* Untersuche die Bahn von i, fuer jedes k aus der Bahn von
     * von i mache einen Eintrag i,k in der Repraesentations
     * matrix und zwar das Produkt aller Erzeuger, die i
     * sukzessive nach k bewegt haben, dazu benutzte alle
     * Eintrage in tree.gen auf dem Weg zurueck von k nach i (=wort)  
     * und multipliziere die entsprechenden Erzeuger
     */
    for(l=i; l < degree; l++)
    {
        if(tree[l].atr == N_TRUE)
        {
            /* suche rueckwaerts */
            next=l;
            copy(id,operm);
            while(tree[next].point)
            {
                mult(operm,S_V_I(stabi,tree[next].gen),operm);
                next=(tree[next].point)-1L;
            }
            copy(operm,S_M_IJ(repma,i-1L,l));
        }
    }
    freeall(id);
    freeall(ob_degree);
    freeall(operm);
    return OK;
}


/* sift() sieht nach, ob perm in der Repraesentationsmatrix
 * repma enthalten ist. sift() wird von strongen benoetigt.
 */

static INT sift(degree,insrow,perm,repma) INT degree, *insrow; OP perm,repma;
/* NS 060891 V1.3 */
{
    register unsigned short ismember=N_TRUE;
    INT i=0L,j;
    OP invperm=callocobject();

    while((i < degree) && ismember)
    {
        i++;
        j=S_P_II(perm,i-1L);
        if(not EMPTYP    (S_M_IJ(repma,i-1L,j-1L)))
        {
            invers(S_M_IJ(repma,i-1L,j-1L),invperm);
            mult(invperm,perm,perm);
        }
        else
        {
            ismember=N_FALSE;
            copy(perm,S_M_IJ(repma,i-1L,j-1L));
            /* In diese Zeile wurde die Permutation eingefuegt */
            (*insrow)=i-1L; 
            break;
        }
    }
    freeall(invperm);
    return(ismember);
}

/* porbit(degree,i,stabi,tree) berechnet die Bahn eines Punktes 
 * i und gibt 
 * folgenden Baum (tree) zurueck:
 *
 * 
 * tree[r].atr: TRUE, wenn r in der Bahn von i liegt, sonst FALSE
 * tree[r].gen: Nummer k des Generators g[k], der s-> r abb.
 * tree[r].point: Bahnpunkt s, der von dem generator g[k] nach
 *                  r abbgebildet wird, tree[i].point = 0L, um
 * anzuzeigen, dass i die Wurzel des Baumes ist.
 * 
 * porbit() wird von strongen() benoetigt.
 */


static INT porbit(degree,i,stabi,tree) INT degree,i; 
    OP stabi; /* Stabilisator von 1L,...,i-1 */ 
    struct treecomp tree[];
/* NS 060891 V1.3 */
{
    INT pos=0L;
    INT stablen;
    INT g,j, /* Schleifenzaehler */ r,s; /* Bahnpunkte */
    INT *points;

    stablen=S_V_LI(stabi);
    points=(INT *) SYM_malloc(sizeof(INT)*degree+OFFSET);
    points[pos] = i; /* initialisiere points mit dem Punkt,
                    * dessen Bahn gesucht wird
                    */
    for(j=0L; j < degree; j++)
    {
        tree[j].atr=N_FALSE;
        tree[i-1].atr=N_TRUE;
        tree[i-1].point=0L; /* i ist Wurzel des Baumes */
    }

    while(pos >= 0L)
    {
        s=points[pos];
        points[pos--]=0L;
        for(g=0L; g < stablen; g++)
        {
            /* Bestimme das Bild r von s unter dem g-ten Stabilisator */
            r=S_P_II(S_V_I(stabi,g),s-1L);  

            if(not tree[r-1].atr)
            {
                points[++pos]=r;
                tree[r-1].atr=N_TRUE;
                tree[r-1].gen=g;
                tree[r-1].point=s;
            }
        }
    }
    SYM_free(points);
    return OK;
}

/* Eigentliche Prozedur zur Berechnung eines starken Erzeugers
 * beziehungsweise einer Repraesentationsmatrix repma
 */

#ifdef MATRIXTRUE
INT strong_generators(a,b) OP a,b;
/* AK 290192 */
/* a VECTOR of generators
   b becomes MATRIX of stronggenerators */
{
    INT degree, numgen;
    INT erg = OK;
    degree=S_P_LI    (S_V_I(a,0L));
    numgen=S_V_LI(a);
    erg += m_ilih_m(degree+1L,degree+1L,b);
    erg += strongen(degree,numgen,a,b);
    ENDR("strong_generators");
}



static INT strongen(degree,numgen,genvec,repma) 
    INT degree; /* numgen= Anzahl der Erzeuger wird von 
        strongen an sift() * weitergereicht.  */ 
    INT numgen; 
    OP genvec; /* Vektor der die Erzeuger einer Gruppe enthaelt */
    OP repma; /* Repraesentationsmatrix fuer die Gruppe */
/* NS 060891 V1.3 */
{
    INT i,j,k,l; /* Schleifenzaehler */
    INT row;
    INT stablen;
    INT erg = OK; /* AK 290192 */
    struct treecomp *tree;

    OP id=callocobject();
    OP queue=callocobject();
    OP ob_degree=callocobject();
    OP perm_eins=callocobject();
    /* stabi ist Vektor von Permutationen. 
     */
    OP stabi=callocobject();
    OP strgset=callocobject();

    tree=(struct treecomp*) SYM_malloc(degree*sizeof(struct treecomp)+OFFSET);
    m_i_i(degree,ob_degree);
    erg +=first_permutation(ob_degree,id);


    /* Stabilisator ist am Anfang der ganze Erzeuger */
    erg +=m_il_v(numgen,strgset);
    erg +=m_il_v(0L,stabi);
    for(k=0L; k < numgen; k++)
    {
        erg +=copy(S_V_I(genvec,k),S_V_I(strgset,k));
    }

    /* Diagonale der Repraesentationsmatrix mit id besetzen */
    for(k=0L; k < degree; k++)
        erg +=copy(id,S_M_IJ(repma,k,k));
    
    for(i=1L; i <= degree; i++)
    {

        erg +=stabilizer(i,strgset,stabi);
        erg +=porbit(degree,i,stabi,tree);
        erg +=updatemat(degree,i,tree,stabi,repma);
    }
    m_il_v(0L,queue);

    for(i=1L; i <= degree; i++)
    {
        erg +=stabilizer(i,strgset,stabi);
        stablen=S_V_LI(stabi);


        for(l=0L; l < stablen; l++)
        {
        /* for(k=i-1L; k <= degree; k++) */
            for(k=i-1L; k < degree; k++) 
                /* statt <= degree < degree */
                if(not EMPTYP(S_M_IJ(repma,i-1L,k)))
                {
        erg +=mult(S_V_I(stabi,l),S_M_IJ(repma,i-1L,k),perm_eins);
        erg +=inc(queue);
        erg +=copy(perm_eins,S_V_I(queue,S_V_LI(queue)-1L));
                }
        }
    
    while(S_V_LI(queue))
    {
        erg +=copy(S_V_I(queue,S_V_LI(queue)-1L),perm_eins);
        erg +=dec(queue);
        if(not sift(degree,&row,perm_eins,repma)) /* ismember == 0 */
        {
            erg +=inc(strgset);
            erg +=copy(perm_eins,S_V_I(strgset,S_V_LI(strgset)-1L));

            for(j=1L; j <= row; j++)

            {    
                erg +=stabilizer(j,strgset,stabi);
                erg +=porbit(degree,j,stabi,tree);
                erg +=updatemat(degree,j,tree,stabi,repma); 

                /*for(l=j-1L; l <= degree; l++)*/
                for(l=j-1L; l < degree; l++) 
                    /* < degree statt <= degree */
                {
                    if(not EMPTYP(S_M_IJ(repma,j-1L,l)))
                    {
            erg +=mult(perm_eins,S_M_IJ(repma,j-1L,l),perm_eins);
            erg +=inc(queue);
            erg +=copy(perm_eins,S_V_I(queue,S_V_LI(queue)-1L));
                    }
                }
            }
        } /* end if */
    }    /* end while */
    } /* AK end for 110292 */
    erg +=freeall(id);
    erg +=freeall(queue);
    erg +=freeall(ob_degree);
    erg +=freeall(perm_eins);
    erg +=freeall(stabi);
    erg +=freeall(strgset);
    SYM_free(tree);
    return erg;
} /* end all :-) */
#endif /* MATRIXTRUE */


static INT recu(degree,start,numnontriv,ztvec,numztvec,perm,repma)
    INT degree; INT start; INT numnontriv;
    OP ztvec; OP numztvec; OP perm; OP repma;
/* NS 060891 V1.3 */
{
    INT i,j;

    OP saveperm=callocobject();


    if(start == numnontriv-1L)
    {
        for(i=start; i< degree; i++)
        {
            if(not EMPTYP(S_M_IJ(repma,start,i)))
            {
            mult(perm,S_M_IJ(repma,start,i),saveperm); 
            colltypes(saveperm,ztvec,numztvec);
            }
        }


    }
    else
        for(j=start; j < degree; j++)
        {
            if(not EMPTYP(S_M_IJ(repma,start,j)))
            {
            mult(perm,S_M_IJ(repma,start,j),saveperm);
            recu(degree,start+1L,numnontriv,ztvec,numztvec,saveperm,repma);
            }
        }

    freeall(saveperm);
    return OK;
}
        




static INT callrecu(grad,ztvec,numztvec,repma) INT grad; OP ztvec,numztvec,repma;
/* NS 060891 V1.3 */
{
    unsigned short trivrow;
    INT i,j;
    INT numnontriv=1L; /* AK 021291 */
    OP id=callocobject();
    OP ob_grad=callocobject();
    OP perm=callocobject();

    /* Weil die unteren Zeilen der Matrix meistens bis auf
     * die Identitaet in der Diagonalen leer sind, wird
     * hier erstmal festgestellt, ab wo die Matrix leer
     * ist
     */

    for(i=grad-1L; i > 0L; i--)
    {
        trivrow=N_TRUE;
        
        for(j=i+1L; j < grad; j++)
        {
            if(not EMPTYP(S_M_IJ(repma,i,j)))
            {
                trivrow=N_FALSE;
                break;
            }
        }
        if(trivrow == N_FALSE)
        {
            numnontriv=i+1L;
            break;
        }
    }
    m_i_i(grad,ob_grad);
    first_permutation(ob_grad,id);
    copy(id,perm);
    recu(grad,0L,numnontriv,ztvec,numztvec,perm,repma);
    freeall(id);
    freeall(ob_grad);
    freeall(perm);
    return OK;
} /* end all */



static INT colltypes(perm,ztvec,numztvec) OP perm, ztvec, numztvec;
/* NS 060891 V1.3 */
{
    INT i;
    INT ztveclen;
    OP ztperm=callocobject();
    OP expztperm=callocobject();

    ztveclen=S_V_LI(ztvec);
    zykeltyp(perm,ztperm);
    t_VECTOR_EXPONENT(ztperm,expztperm);
    
    for(i=0L; i < ztveclen; i++)
    {
        if(comp(expztperm,S_V_I(ztvec,i)) == 0L)
        {
            inc(S_V_I(numztvec,i));
            goto ende;
        }
    }

    inc(ztvec);
    copy(expztperm,S_V_I(ztvec,S_V_LI(ztvec)-1L));
    inc(numztvec);
    m_i_i(1L,S_V_I(numztvec,S_V_LI(numztvec)-1L));
ende:
    freeall(ztperm);
    freeall(expztperm);
    return OK;
}            
/* berechnet das Zykelindikatorpolynom einer beliebigen Permutations-
 * gruppe, benutzt dazu die uebergebenen Vektoren, die die
 * Zykeltypen (expztvec), bzw deren Anzahlen (numztvec)
 * enthalten.
 */

#ifdef BRUCHTRUE
static INT zykelind_arb_co(expztvec,numztvec,pol)
    OP expztvec;
    OP numztvec;
    OP pol; /* enhaelt nach Ablauf der Routine das Zykelindikator-
             * polynom (noch nicht Polyasubstituiert)
             */
/* NS 060891 V1.3 */
{
    INT i,order,veklen;
        INT erg = OK;

    OP a,hilf,k,party,zahl,zwisch,zykeltypvec;
    OP ak_order;

    a = CALLOCOBJECT();
    hilf=CALLOCOBJECT();
    k=CALLOCOBJECT();
    party = CALLOCOBJECT();
    zahl = CALLOCOBJECT();
    zwisch = CALLOCOBJECT();
    zykeltypvec = CALLOCOBJECT();
    ak_order = CALLOCOBJECT();

    sum(numztvec,ak_order); /* AK 060295 */



    b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,a);

    veklen=S_V_LI(expztvec);
    m_il_nv(5,S_PO_S(a)); 
    init(POLYNOM,pol);
    for(i=0L; i < veklen ; i++)
    {
        COPY(S_PA_S(S_V_I(expztvec,i)),S_PO_S    (a));
        /* m_i_i(order,k); */
        m_ou_b(S_V_I(numztvec,i),ak_order,S_PO_K(a));
        /* m_ou_b(S_V_I(numztvec,i),k,S_PO_K(a)); */
        kuerzen(S_PO_K(a));
        add_apply(a,pol);
    }
    FREEALL3(a,hilf,k); 
    FREEALL5(ak_order,party,zahl,zwisch,zykeltypvec); 
    ENDR("zykelind_arb_co:internal routine");
}
#endif /* BRUCHTRUE */

/*
 * Die Funktion zykelind_arb fasst die Funktionen strongen,
 * callrecu und zykelind_arb_co zusammen. Eingabeparameter
 * der Vektor von Permutationen genvec, er enthaelt die Erzeuger 
 * der Gruppe, in pol wird dann das Zykelindikator polynom 
 * geliefert.
 */

INT zykelind_arb(genvec,pol) OP genvec; OP pol;
/* NS 060891 V1.3 */
/* AK 180998: now the generating permutations may have different
                degree */
{
#ifdef BRUCHTRUE
        INT degree,i,j;
        INT numgen;
        INT erg = OK;
        OP mat=callocobject();
        OP numztvec=callocobject();
        OP ztvec=callocobject();
        OP axl = callocobject();
        OP mygenvec = callocobject();

        erg += m_l_v(cons_null,numztvec);
        erg += m_l_v(cons_null,ztvec);

        /* degree und numgen bestimmen */
        degree=S_P_LI   (S_V_I(genvec,0L));
        for (i=1;i<S_V_LI(genvec);i++) /* AK 180998 */
                if (S_P_LI   (S_V_I(genvec,i)) > degree)
                        degree=S_P_LI   (S_V_I(genvec,i));
        numgen=S_V_LI(genvec);
        erg += m_il_v(numgen,mygenvec); /* AK 180998 */
        for (i=0;i<numgen;i++) /* AK 180998 */
                {
                if (degree==S_P_LI   (S_V_I(genvec,i)))
                        erg += copy_permutation(S_V_I(genvec,i), S_V_I(mygenvec,i));
                else    {
                        erg += m_il_p(degree,S_V_I(mygenvec,i));
                        for (j=0;j<S_P_LI(S_V_I(genvec,i));j++)
                                M_I_I(S_P_II(S_V_I(genvec,i),j),S_P_I(S_V_I(mygenvec,i),j));
                        for(;j<S_P_LI(S_V_I(mygenvec,i));j++)
                                M_I_I(j+1,S_P_I(S_V_I(mygenvec,i),j));
                        }
                }
        erg += m_i_i(degree+1L,axl);
        erg += m_lh_m(axl,axl,mat);
        erg += strongen(degree,numgen,mygenvec,mat);
        erg += callrecu(degree,ztvec,numztvec,mat);
        erg += zykelind_arb_co(ztvec,numztvec,pol);
	FREEALL5(axl,numztvec,ztvec,mygenvec,mat);
        ENDR("zykelind_arb");
#else /* BRUCHTRUE */
        return error("zkelind_arb: BRUCH not available");
#endif /* BRUCHTRUE */
}
/* routine zur Polyasubstitution */


INT polya_n_sub(p,n,e) OP p,n,e;
/* AK 060792 */
{
    return polyasub(S_I_I(n),p,e);
}

static INT polyasub(numcol,pol,pattpol)
    INT numcol; /* Anzahl der Farben */
    OP pol; /* Zykelindikatorpolynom */
    OP pattpol; /* Ergebnis: Musterpolynom */
/* NS 060891 V1.3 */
{
    INT i,j; /* Schleifenzaehler */
    INT degree;
    INT erg = OK;
    OP colvec=callocobject();
    OP compcolpol=callocobject();
    OP hpol=callocobject();
    OP exp=callocobject();

    /* Farbenvector herstellen:
     * Monom abc...... -> [11...1][22...2]...[nn...n]
     * wobei die Laenge von [xx...x] gleich der Anzahl der 
     * Farben ist und n die Maechtigkeit der Menge X,
     * auf der die Gruppe operiert.
     */
    erg += numberofvariables(pol,exp);     /* AK 211194 */
    degree=S_I_I(exp);
    erg += m_il_v(degree,colvec);
    erg += b_skn_po(callocobject(),callocobject(),NULL,compcolpol);
    erg += b_skn_po(callocobject(),callocobject(),NULL,hpol);

    FREESELF(pattpol);
    
    for(i=0L; i < degree; i++)
    {
        erg += init(POLYNOM,compcolpol);

        for(j=0L; j < numcol; j++)
        {
            if (not EMPTYP(hpol))
                erg += freeself(hpol);
            erg += m_iindex_iexponent_monom(j,i+1L,hpol);
            erg += add_apply(hpol,compcolpol);
        }
        erg += copy(compcolpol,S_V_I(colvec,i));
    }
    erg += eval_polynom(pol,colvec,pattpol);

    FREEALL4(colvec,compcolpol,hpol,exp);
    ENDR("zyk:internal function polyasub");
}    

/* Algorithmus von dimino, berechnet eine Liste mit allen
 * Elementen einer Gruppe aus den erzeugenden Permutationen.
 */

INT dimino(elm) OP elm; 
/* enthaelt am Anfang die Erzeuger der Gruppe, nach 
 * Ablauf der Routine dann alle Gruppenelemente */
/* NS 060891 V1.3 */
{
    INT i,j,k,
        cosetlen, elt_not_elm, numgen,
        order=0L,
        rep_pos, s_count, si_not_elm;
    INT erg = OK;


    OP elt,g,genvec,id;
    CTO(VECTOR,"dimino(1)",elm);

    elt=callocobject(); /* Hilfsvariable fuer Test auf Enhaltensein
                            * in elm
                            */
    g=callocobject(); /* eine Permutation */
    genvec=callocobject(); /* enhaelt die Erzeuger */
    id=callocobject(); /* die identische Permutation */

    numgen=S_V_LI(elm);
    erg += m_il_v(numgen,genvec);
    /* Kopiere die Erzeuger in einen eigenen Vektor genvec */
    for(i=0L; i < numgen; i++)
        COPY(S_V_I(elm,i),S_V_I(genvec,i));
    eins(S_V_I(genvec,0),id);

    /* Liste der Elemente anlegen, laenge ist erstmal = 1 */
    erg += m_il_v(1L,elm); 

    /* Spezialfall G= <S1> */

    COPY(id,S_V_I(elm,order)); /* 1. Element ist id */
    COPY(S_V_I(genvec,0L),g); /* g:=s1 */
    // while(comp(g,id)) /* Solange g ungleich id */
    while(not einsp(g)) /* Solange g ungleich id */
    {
        /* Elementevektor muss jedesmal erst um 1 verlaengert werden */
        INC(elm); 
        ++order; /* AK 060891 */
        COPY(g,S_V_I(elm,order)); /* elm[order]=g */
        CLEVER_MULT(S_V_I(elm,order),S_V_I(genvec,0L),g); /* g:=g*s1 */
    }

    /* Laenge der Nebenklassen feststellen, muss man nur einmal machen,
     * da alle Nebenklassen gleiche Laenge haben
     */
    cosetlen=S_V_LI(elm); 

    /* Falls es mehr als einen Erzeuger gibt */
    for(i=1L; i < numgen; i++)
    {
        si_not_elm=1L;
        for(k=0L; k <= order; k++) /* s(i) in elm ? */
        if((si_not_elm=comp(S_V_I(genvec,i),S_V_I(elm,k))) == 0L)
                break;

        /* Wenn s[i] nicht in elm:
         * s[i] und seine Nebenklasse g*s[i]
         * zu elm hinzufuegen
         */
        if(si_not_elm) /* Wenn s(i) nicht in elm */
        {
            /* s[i] hinzufuegen */
            /* Elementevektor muss jedesmal erst um 1 verlaengert werden */
            inc(elm); 
            ++order;
            COPY(S_V_I(genvec,i),S_V_I(elm,order));
            /* Nebenklasse zu elm hinzufuegen */
            for(j=1L; j < cosetlen; j++)        
            {
            /* ++order,elm[order]:=elm[j]*s[i] */
            /* Elementevektor muss jedesmal erst 
                um 1 verlaengert werden */
            inc(elm);
            ++order; 
            MULT(S_V_I(elm,j),S_V_I(genvec,i),S_V_I(elm,order));
            } /* end for */

            rep_pos=cosetlen;

            do {
                for(s_count=0L; s_count <= i; s_count++)
                {
                    /* elt=elm[rep_pos]*s[s_count] */
                    MULT(S_V_I(elm,rep_pos),
                        S_V_I(genvec,s_count),elt);

                    elt_not_elm=1L;
                    for(k=0L; k <= order; k++) 
                        /* elt in elm ? */
                        if((elt_not_elm=comp(elt,S_V_I(elm,k))) == 0L)
                            break;
            
                    /* Wenn elt nicht in elm:
                     * elt und seine Nebenklasse g*elt
                     * zu elm hinzufuegen
                     */
                    if(elt_not_elm)
                    {
                    /* elt hinzufuegen */
                    /* Elementevektor muss jedesmal erst 
                         * um 1 verlaengert werden 
                         */
                        INC(elm); 
                        ++order;
                        COPY(elt,S_V_I(elm,order));
                    /* Nebenklasse zu elm hinzufuegen */
                        for(j=1L; j < cosetlen; j++)        
                        {
                           /* ++order,elm[order]:=elm[j]*s[i] */
                           /* Elementevektor muss jedesmal erst 
                            * um 1 verlaengert werden 
                             */
                           INC(elm); 
                           ++order;
                           MULT(S_V_I(elm,j),elt,S_V_I(elm,order));
                        } /* end for */
                    } /* end if */
                } /* end for */
                rep_pos+=cosetlen;
            } while(rep_pos <= order);
        } /* end if */
        cosetlen=order+1L;
    } /* end for */

    FREEALL4(elt,g,genvec,id);
    CTO(VECTOR,"dimino(1e)",elm);
    ENDR("dimino");
}


INT grf_arb(gr,n,res) OP gr,n,res;
/* AK 220998 V2.0 */
/* AK 091204 V3.0 */
{
        INT erg = OK;
        CTO(INTEGER,"grf_arb(2)",n);
        CTO(VECTOR,"grf_arb(1)",gr);
        CE3(gr,n,res,grf_arb);
        {
        OP zw;
        zw = CALLOCOBJECT();
        erg += zykelind_arb(gr,zw);
        erg += polya_n_sub(zw,n,res);
        FREEALL(zw);
        }
        ENDR("grf_arb");
}


INT grf_Sn(gr,n,res) OP gr,n,res;
/* AK 220998 V2.0 */
{
        INT erg = OK;
        CTO(INTEGER,"grf_Sn",n);
        CTO(INTEGER,"grf_Sn",gr);
        CE3(gr,n,res,grf_Sn);
        {
        OP zw;
        zw = callocobject();
        erg += zykelind_Sn(gr,zw);
        erg += polya_n_sub(zw,n,res);
        erg += freeall(zw);
        }
        ENDR("grf_Sn");
}

INT grf_An(gr,n,res) OP gr,n,res;
/* AK 220998 V2.0 */
{
        OP zw;
        INT erg = OK;
        CTO(INTEGER,"grf_An",n);
        CTO(INTEGER,"grf_An",gr);
        CE3(gr,n,res,grf_An);
        zw = callocobject();
        erg += zykelind_An(gr,zw);
        erg += polya_n_sub(zw,n,res);
        erg += freeall(zw);
        ENDR("grf_An");
}

INT grf_Cn(gr,n,res) OP gr,n,res;
/* AK 220998 V2.0 */
{
        OP zw;
        INT erg = OK;
        CTO(INTEGER,"grf_Cn",n);
        CTO(INTEGER,"grf_Cn",gr);
        CE3(gr,n,res,grf_Cn);
        zw = callocobject();
        erg += zykelind_Cn(gr,zw);
        erg += polya_n_sub(zw,n,res);
        erg += freeall(zw);
        ENDR("grf_Cn");
}

INT grf_Dn(gr,n,res) OP gr,n,res;
/* AK 220998 V2.0 */
{
        OP zw;
        INT erg = OK;
        CTO(INTEGER,"grf_Dn",n);
        CTO(INTEGER,"grf_Dn",gr);
        CE3(gr,n,res,grf_Dn);
        zw = callocobject();
        erg += zykelind_Dn(gr,zw);
        erg += polya_n_sub(zw,n,res);
        erg += freeall(zw);
        ENDR("grf_Dn");
}




INT no_orbits_arb(a,b,c) OP a,b,c;
/* AK 071098 V2.0 */
{
    OP d,e;
    OP z;
    INT erg = OK;
    CE3(a,b,c,no_orbits_arb);
    d = callocobject();
    e = callocobject();
    erg += zykelind_arb(a,d);
    z = d;
    erg += m_i_i(0,c);
    while (z!=NULL)
        {
        erg += sum(S_PO_S(z),e);
        erg += hoch(b,e,e);
        erg += mult_apply(S_PO_K(z),e);
        erg += add_apply(e,c);
        z = S_PO_N(z);
        }

    erg += freeall(d);
    erg += freeall(e);
    ENDR("no_orbits_arb");
}

#endif /* ZYKTRUE */

