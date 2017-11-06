
#include "def.h"
#include "macro.h"

static INT rh_kostka();
static INT rh_insert();
static INT rh_delete();
static INT rh_ausgabemat();
static OP lookupinschurspeicher();
static INT kostka_tab_partition();
static INT kostka_tab_skewpartition();
static INT neu_n_kostka();
static INT nspeicherkostka();


#define    RH_MAX    100




#ifdef KOSTKATRUE

INT kostka_number(inh,shape,res) OP inh,shape,res;
/* AK 020890 V1.1 */ /* AK 210891 V1.3 */
/* AK 240398 V2.0 */
{
    OP d;
    INT i;
    INT erg = OK;
    CE3(inh,shape,res,kostka_number);

    if (S_O_K(inh) == PARTITION) /* AK 100992 */
        d = S_PA_S(inh);
    else if (S_O_K(inh) == VECTOR)
        d = inh;
    else if (S_O_K(inh) == INTVECTOR)
        d = inh;
    else
        {
        WTO(inh,"kostka_number:content");
        goto endr_ende;
        }

    for (i=(INT)0;i<S_V_LI(d);i++)
        if (S_O_K(S_V_I(d,i)) != INTEGER)
            {
            erg += error("kostka_number: wrong content type");
            goto endr_ende;
            }

    if (S_O_K(shape) == PARTITION)
        erg += kostka_number_partition(d,shape,res);
    else if (S_O_K(shape) == SKEWPARTITION)
        erg += kostka_number_skewpartition(d,shape,res);
    else 
        WTO(shape,"kostka_number:shape");

    ENDR("kostka_number");
}

static INT mkn_co();
INT kostka_number_partition(a,b,c) OP a,b,c;
/* inhalt, umriss,  res */
/* AK 240901 */
/* much faster, uses recursion with skew partition */
{
    OP d;
    INT erg = OK;
    CTO(PARTITION,"kostka_number_partition",b);
    CTO(EMPTY,"kostka_number_partition(3)",c);

    d = CALLOCOBJECT();
    erg += m_pa_s(b,d);
    erg += mkn_co(d,a,c);
    FREEALL(d);
    ENDR("kostka_number_partition");
}

INT kostka_number_skewpartition(a,b,c) OP a,b,c;
/* AK 240901 */
/* inhalt, umriss,  res */
{
    OP d;
    INT erg = OK;
    CTO(SKEWPARTITION,"kostka_number_skewpartition",b);
    CTO(EMPTY,"kostka_number_skewpartition(3)",c);

    d = callocobject();
    erg += part_part_skewschur(S_SPA_G(b),S_SPA_K(b),d);
    erg += mkn_co(d,a,c);
    erg += freeall(d);
    ENDR("kostka_number_skewpartition");
}

static INT mkn_co(b,a,c) OP b,a,c;
/* b is schur
   a is inhalt */
{
    INT i,erg=OK;
    OP s,z;
    CTO(EMPTY,"mkn_co(2)",c);

    s = CALLOCOBJECT();
    for (i=0;i<S_V_LI(a);i++)
        if (S_V_II(a,i) > 0)
        {
            erg += init(HASHTABLE,s);
            erg += schur_part_skewschur(b,S_V_I(a,i),s);
            SWAP(b,s);
        }

    CTO(HASHTABLE,"mkn_co(internal)",b);
    FORALL(z,b,{ goto ee; } );
    M_I_I(0,c);
    goto ende;
ee:
    COPY(S_MO_K(z),c); 
ende:
    FREEALL(s);
    CTTO(INTEGER,LONGINT,"mkn_co(res)",c);
    ENDR("internal to kostka_number_partition");
}


INT kostka_tafel(a,b) OP a,b;
    /* AK 220488 */ 
    /* AK 220897 S1R */
    /* AK 160299 input tested */
    {    
    INT erg=OK;
    CTO(INTEGER,"kostka_tafel",a);
    if (S_I_I(a) == 0)
        {
        erg += m_ilih_m((INT)0, (INT)0, b);
        goto endr_ende;
        }
    if (S_I_I(a) < 0)
        {
        error("kostka_tafel:weight <= 0");
        goto endr_ende;
        }
    C1R(a,"kostka_tafel",b);
    erg += neu_n_kostka(a,b);
    S1R(a,"kostka_tafel",b);
    ENDR("kostka_tafel");
    }

INT invers_kostka_tafel(a,b) OP a,b;
    /* AK 220897 */
    /* AK 171297 input tested */
    {
    INT erg = OK;
    OP c;
    CTO(INTEGER,"invers_kostka_tafel",a);
    if (S_I_I(a) == 0)
        {
        erg += m_ilih_m((INT)0, (INT)0, b);
        goto endr_ende;
        }
    else    if ( S_I_I(a) < 0 )
        {
        erg += error("invers_kostka_tafel: weight < 0");
        goto endr_ende;
        }
    C1R(a,"invers_kostka_tafel",b);


    c = callocobject();
    erg += kostka_tafel(a,c);
    erg += invers(c,b);
    erg += freeall(c);

    S1R(a,"invers_kostka_tafel",b);
    ENDR("invers_kostka_tafel");
    }

INT make_n_transpositionmatrix(dim,mat) OP dim,mat;
/* 300388 berechnet die matrix J [MD p.55]
J_PQ = 1 <==> conjugierte Partition von P ist Q, null sonst */
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT i;
    INT erg = OK;
    OP conpart;
    OP vector;

    CTO(INTEGER,"make_n_transpositionmatrix(1)",dim);

    conpart=callocobject(); 
    vector=callocobject(); 

    erg += init_kostka(dim,mat,vector);
    for (i=(INT)0;i<s_m_hi(mat);i++)
        { 
        erg += conjugate(S_V_I(vector,i),conpart);
        M_I_I(1L,S_M_IJ(mat,i,indexofpart(conpart))); 
        };
    erg += freeall(conpart);
    erg += freeall(vector); 
    ENDR("make_n_transpositionmatrix");
    }



INT tex_kostka(koma,vector) OP koma,vector;
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* koma ist die matrix, vector der vector der partitionen */
/* AK 070291 V1.2 prints to texout */
/* AK 210891 V1.3 */
    {
    INT i,j;
    fprintf(texout,"$ \\matrix {  ");
    for (i=(INT)0;i<S_V_LI(vector);i++)
        { 
        fprintf(texout," & "); 
        fprint(texout,S_V_I(vector,i)); 
        texposition = (INT)0; 
        };
    fprintf(texout," \\cr \n");
    for (i=(INT)0;i<S_V_LI(vector);i++)
        {
        fprint(texout,S_V_I(vector,i)) ; 
        texposition = (INT)0;
        for (j=(INT)0;j<=i;j++)
            { fprintf (texout," & ");
            fprintf(texout," %ld ",S_M_IJI(koma,i,j)); };
        for (j=i+1L;j<S_V_LI(vector);j++) 
             fprintf(texout," & ");
        fprintf(texout," \\cr \n");
        };
    fprintf(texout," } $"); return(OK);
    }

INT scan_kostka(a) OP a;
/* AK 280388 */ /* AK 170789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    OP i = callocobject(); 
    INT erg = OK;
    CTO(EMPTY,"scan_kostka(1)",a);

    printeingabe("Weight of the Kostka matrix");
    erg += scan(INTEGER,i); 
    erg += kostka_tafel(i,a); 
    erg += freeall(i); 
    ENDR("scan_kostka");
    }

static OP lookupinschurspeicher(part,c) OP part,c;
/* sucht in speicher die entsprechenden eintraege 
falls nicht vorhanden werden sie berechnet
140687 */
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT i;
    OP w,zeigerw,zeigeri;
    
    w = callocobject();

    /* sortiert nach gewicht und index der partition */
    
    weight_partition(part,w);      /* gewicht w ist erster index */
    i = indexofpart(part);      /* index i der part. ist 2. index */

    zeigerw = S_V_I(c,S_I_I(w)-1L); 
/* zeiger auf zeile in der speicher- matrix mit partitionen vom gewicht w*/

    if (EMPTYP(zeigerw))     /* wenn in zeile w noch keine eintraege */
        {
             /* laenge der zeile w ist gerade anzahl
            der part vom gewicht w */
        m_il_v(numberofpart_i(w),zeigerw);   
            /* schaffe speicherplatz fuer zeile w */
        };

    zeigeri = S_V_I(zeigerw,i);    /* zeiger auf spaltenindex */

    freeself(w);
    if (EMPTYP(zeigeri))
        {
        OP einspart;
        OP einspartschur;
        OP kurzergebnis;

        if (i==0) /* einteilige partition */
            {
            copy_partition(part,w);
            b_pa_s(w,zeigeri); /* dann die schurfunktion {n} */
            return zeigeri;      /* ende */
            }
        einspart = callocobject();
        einspartschur = callocobject();
        
        m_i_pa(S_PA_I(part,S_PA_LI(part)-1L),einspart);
        b_pa_s(einspart,einspartschur);
                /* einspartschur ist schurfunktion
                aus dem letzten element von part */

        copy_partition(part,w); dec(w);
                /* w ist part ohne letztes element*/
        kurzergebnis=lookupinschurspeicher (w,c);
        freeall(w);
                /* w war nur zum suchen noetig */


        mult_schur_schur(kurzergebnis,einspartschur,zeigeri);
        freeall(einspartschur);
        return zeigeri;
        };

    /* falls ergebnis im speicher */
    freeall(w);
    return zeigeri;
    }



static INT neu_n_kostka(n,komatrix) OP n,komatrix;
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    OP speicher = callocobject();
    /* hier werden die bereits berechneten schurfunktionen
    gespeichert */

    m_il_v((INT)150,speicher);
    /* d.h maximal bis dim 150 */
    /* initialisieren der Matrix */

    nspeicherkostka(n,speicher,komatrix);
    freeall(speicher); 
    return(OK);
    }



INT allkostka(n) OP n;
/* AK 190687 gibt alle kostkamatrizen bis n aus */
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    OP speicher = callocobject();
    /* hier werden die bereits berechneten schurfunktionen
    gespeichert */
    OP lauf = callocobject();
    /* lauf variable bis n */
    /* initialisieren des speichers */
    OP komatrix = callocobject() ;
    
    m_il_v(150L,speicher);
    /* d.h maximal bis dim 150 */
    /* initialisieren der Matrix */
    

    for (M_I_I(1L,lauf);le(lauf,n);inc(lauf))
        {
        OP var = callocobject();
        copy(lauf,var);
        printf("kostkamatrix fuer ");
        println(lauf);
        nspeicherkostka(var,speicher,komatrix);
        println(komatrix);
        freeself(komatrix);
        }

    freeall(lauf); freeall(komatrix); freeall(speicher); return(OK);
    }



static INT nspeicherkostka(n,sp,komatrix) OP n; OP komatrix; OP sp;
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT i,j,pi,pj, k,partadr;
    INT erg = OK;
    OP zeiger;
    OP schur;
    OP vector;
    OP prepart;

    CTO(INTEGER,"nspeicherkostka(1)",n);

    schur = callocobject();
    vector = callocobject();
    prepart = callocobject();


    init_kostka(n,komatrix,vector);
    /* initialisieren der 1. Zeile */
    M_I_I(1L,S_M_IJ(komatrix,(INT)0,(INT)0));
    /* globale schleife ueber alle partitionen */

    for (i=1L;i<S_V_LI(vector);i++)
        {
        /* suche die benachbarte partition bzgl
        der dominanzordnung */
        prepartdom(S_V_I(vector,i),&pi,&pj,prepart);
        j=(i-1L);
        while (NEQ(prepart,S_V_I(vector,j))) j--;
        /* j ist jetzt die adresse von prepart in partvec */
        /* pi, pj die zeilennummer in denen getauscht wurde um
        den dominanten nachbarn zu erhalten
        */
        make_neu_partij_schur(S_V_I(vector,i),pi,pj,schur,sp);
        /* die zeile j der matrix wird in die zeile i kopiert */
        for (k=(INT)0;k<=j;k++)
            M_I_I(S_M_IJI(komatrix,j,k),S_M_IJ(komatrix,i,k));
        /* jetzt werden die beitraege von schur addiert */
        zeiger = schur;
        while (zeiger != NULL)
            {
            partadr=(INT)0;
            while(NEQ(S_S_S(zeiger),S_V_I(vector,partadr)))
                partadr++;
            /* partadr ist index des monoms von zeiger */

            ADD_APPLY(S_S_K(zeiger),S_M_IJ(komatrix,i,partadr));
                
            zeiger = S_S_N(zeiger);
            };
        freeself(schur); 
        freeself(prepart);
        };
    freeall(schur); freeall(prepart); freeall(vector); 
    ENDR("nspeicherkostka");
    }



INT removepartij(part,i,j,neupart) OP part,neupart; INT i,j;
/* AK 260587 */
/* entfernt aus partition part die Teile i,j
und ergibt so die neue partition neupart */
/* bsp: removepartij(1224568, 2,3, neupart ist dann 12568 */
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT l,nl;
    INT erg = OK;
    OP self;
    CTO(PARTITION,"removepartij(1)",part);

    if (not EMPTYP(neupart)) freeself(neupart);
    if (S_PA_LI(part) <2L) 
        { error("partition der laenge < 2 in removepartij");
        return(ERROR); }
    else if (S_PA_LI(part) == 2L) return(OK);


    self = CALLOCOBJECT();
    erg += m_il_v(S_PA_LI(part)-2L,self);
    erg += b_ks_pa(VECTOR,self,neupart);

    nl =(INT)0; /* adr. in neupart */

    for (l=(INT)0;l<S_PA_LI(part);l++)
        if ((l!=i)&&(l!=j))
            {
            M_I_I(S_PA_II(part,l),S_PA_I(neupart,nl));
            nl++;
            };

    ENDR("removepartij");
    }



INT make_ij_part(part,i,j,neupart) INT i,j; OP part,neupart;
/* macht zweizeilige Partition aus den teilen i und j der
   partition part */
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    OP self;
    CTO(PARTITION,"make_ij_part(1)",part);

    if (S_PA_LI(part) <2L) 
        {
        erg += error("partition der laenge < 2 in removepartij");
        goto endr_ende;
        }

    self = CALLOCOBJECT();
    erg += m_il_v(2,self);
    erg += b_ks_pa(VECTOR,self,neupart);
    M_I_I(S_PA_II(part,i),S_PA_I(neupart,(INT)0));
    M_I_I(S_PA_II(part,j),S_PA_I(neupart,1L));
    ENDR("make_ij_part");
    }



INT make_partij_perm(part,i,j,perm) OP part,perm; INT i,j;
/* AK 190587 */
/* es gilt i<j
partition ist eine aufsteigende zahlenfolge
prozedur bildet aus einer partition p = [p1,p2,..,pn]
eine permutation, die den index zum schubert-
polynom fuer
{pi,pj} x {p1}x..x{pi-1}x{pi+1}x..x{pj-1}x{pj+1}x..x{pn}
bildet */
/* ok am 190587 */ /* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    OP permlength = callocobject();
    OP zw = callocobject();
    OP code = callocobject();
    INT l,
    codeadresse ;/* stelle zum einfuegen im code */

    /* 
    als erstes die laenge der permutation berechnen
    */

    if (not EMPTYP(perm)) freeself(perm);
    weight_partition(part,permlength);
    sub(permlength,S_PA_I(part,i),permlength);
    length(part,zw);
    add(zw,permlength,permlength);
    INC_INTEGER(permlength);

    /* den lehmercode aufbauen */
    m_il_v(S_I_I(permlength),code); freeall(permlength);
    for (l=(INT)0;l<S_I_I(permlength);l++) M_I_I((INT)0,S_V_I(code,l));
    M_I_I(S_PA_II(part,i),S_V_I(code,1L));
    M_I_I(S_PA_II(part,j),S_V_I(code,2L));
    codeadresse = 2L + S_PA_II(part,j) + 1L;
    for (l=(INT)0;l<S_PA_LI(part);l++)
        {
        if ((l!=i) && (l!=j)) 
            {
            M_I_I(S_PA_II(part,l),S_V_I(code,codeadresse));
            codeadresse += S_PA_II(part,l);
            codeadresse++;
            };
        }
    /* den code umwandeln in permutation */
    
    lehmercode_vector(code,perm);
    /* alles unnoetige wieder freigeben */

    freeall(code); freeall(zw);
    return(OK);
    }



INT make_neu_partij_schur(part,i,j,schur,sp) 
        OP part,schur, sp;INT i,j;
/* AK 140687 */ /* mit lookup */ /* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    OP a,b,zweizeilenpart,kleinerpart;

    CTO(PARTITION,"make_neu_partij_schur(1)",part);

    a = callocobject();
    zweizeilenpart = callocobject();
    kleinerpart = callocobject();

    if (not EMPTYP(schur)) freeself(schur);
    removepartij(part,i,j,kleinerpart);
    make_ij_part(part,i,j,zweizeilenpart);
    b_pa_s(zweizeilenpart,a);/*zweizeilenpart muss nicht freigegeben
                werden */
    if (EMPTYP(kleinerpart))     
        erg += copy(a,schur);
    else    { 
        b=lookupinschurspeicher(kleinerpart,sp);
        mult_schur_schur(a,b,schur); 
        };

    freeall(a); 
    freeall(kleinerpart); 
    ENDR("make_neu_partij_schur");
    }



INT make_partij_schur(part,i,j,schur) OP part,schur; INT i,j;
/* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    OP perm = callocobject();
    make_partij_perm(part,i,j,perm);
    if (not EMPTYP(schur)) freeself(schur);
    newtrans(perm,schur); freeall(perm); return(OK);
    }



INT prepartdom(part,i,j,prepart) OP part,prepart; INT *i,*j;
/* AK 190587 */
/* berechnet einen groesseren nachbarn prepart 
der Partition part bezueglich der
dominanzordnung
dazu wird der satz verwandt, dass ein dominanter nachbar
sich nur durch ein verschobenes kaestchen im young-diagramm
unterscheidet
i ist die zeile in part wo ein kaestchen weggenommen wird
j ist die zeile in part wo es angefuegt wird */
/* ok 200587 */ /* AK 200789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT l;
    INT erg = OK;

    CTO(PARTITION,"prepartdom(1)",part);
    if (part == prepart) {
        error("prepartdom:identical");
        goto endr_ende;
        }

    FREESELF(prepart);
    
    *i = (INT)0;
    /* falls die partition part mit 1 beginnt */
    if (einsp(S_PA_I(part,(INT)0)))
        {
        OP self;
        self = CALLOCOBJECT();
        erg += m_il_v(S_PA_LI(part) - 1L,self);
        erg += b_ks_pa(VECTOR,self,prepart);

        /* prepart ist dann um eins kuerzer */
        /* kopiere part ohne den ersten teil*/
        for (l=1L;l<S_PA_LI(part);l++)
            M_I_I(S_PA_II(part,l),S_PA_I(prepart,(l-1L)));
        /* suche die stelle zum anfuegen des kaestchenens */
        for (l=1L;l<S_PA_LI(prepart);l++)
            if (S_PA_II(prepart,l) > S_PA_II(prepart,(l-1L)))
                {
                INC_INTEGER(S_PA_I(prepart,(l-1L)));
                *j = l; goto prepartende;
                };
        /* der Sonderfall falls in der letzten Zeile ein
        kaestchen angefuegt wird */
        INC_INTEGER(S_PA_I(prepart,(l-1L)));
        *j = l; goto prepartende;
        }
    else     {
        /* part beginnt mit > 1 */

        copy_partition(part,prepart);
        DEC_INTEGER(S_PA_I(prepart,(INT)0));
        for (l=2L;l<S_PA_LI(prepart);l++)
            if (S_PA_II(prepart,l) > S_PA_II(prepart,(l-1L)))
                {
                INC_INTEGER(S_PA_I(prepart,(l-1L)));
                *j = l-1L; goto prepartende;
                };
        INC_INTEGER(S_PA_I(prepart,(l-1L)));
        *j = l-1L; goto prepartende;
        };
    prepartende:
    ENDR("prepartdom");
    }



INT init_kostka(n,koma,vector) OP koma,n,vector;
/* AK 250587 */ /* AK 200789 V1.0 */
/* koma wird eine Matrix gross genug, vector ein vector der partitionen */
/* AK 181289 V1.1 */
/* AK 210891 V1.3 */
    {
    INT i,j,l;

    if (not EMPTYP(koma)) freeself(koma);
    if (not EMPTYP(vector)) freeself(vector);
    makevectorofpart(n,vector);
    l = S_V_LI(vector);
    m_ilih_m(l,l,koma);  /* AK 030189 */
    for (i=(INT)0;i<l;i++) for (j=(INT)0;j<l;j++) M_I_I((INT)0,S_M_IJ(koma,i,j));
    return(OK);
    }




INT test_kostka() 
/* AK 181289 V1.1 */ /* AK 210891 V1.3 */
    {
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();

    printf("test_kostka:scan(a)");
    scan(KOSTKA,a);println(a);
    printf("test_kostka:add(a,a,b)");
    add(a,a,b);
    println(b);
    printf("test_kostka:mult(a,b,b)"); mult(a,b,b); println(b);
#ifdef BRUCHTRUE
    printf("test_kostka:invers(a,b)");
    invers(b,a);
    println(a);
#endif /* BRUCHTRUE */
    printf("test_kostka:make_n_transpositionmatrix(a,b)"); 
    scan(INTEGER,a);
    make_n_transpositionmatrix(a,b); println(b);
    printf("test_kostka:scan(PARTITION,a)(inh)"); scan(PARTITION,a);
    printf("test_kostka:scan(PARTITION,b)(umriss)"); scan(PARTITION,b);
    printf("test_kostka:kostka_number(a,b,c)"); 
    kostka_number(a,b,c);println(c);

    freeall(a);freeall(b);
    return(OK);
    }

    

INT kostka_tab(shape,content,c) OP shape,content,c;
/* AK 131190 V1.1 */ 
/* AK 160791 V1.3 */
/* return: LIST of TABLEAUX or SKEWTABLEAUX */
/* AK 100902 V2.1 */
{
    INT i,erg = OK;

    CE3(shape,content,c,kostka_tab);
    if (S_O_K(content) == PARTITION) /* AK 100992 */
        content = S_PA_S(content);
    else if (S_O_K(content) == VECTOR);
    else if (S_O_K(content) == INTEGERVECTOR);
    else
        {
        WTO(content,"kostka_tab(2)");
        goto endr_ende;
        }

    for (i=(INT)0;i<S_V_LI(content);i++)
        if (S_O_K(S_V_I(content,i)) != INTEGER)
            {
            erg += error("kostka_tab: wrong content type");
            goto endr_ende;
            }

    switch (S_O_K(shape)) 
        {
        case PARTITION: 
            if (S_PA_LI(shape) == 0) /* AK 100902 */
                {
                OP d;
                erg += init(LIST,c);
                d = CALLOCOBJECT();
                erg += m_u_t(shape,d);
                insert(d,c,NULL,NULL);
                }
            else
                erg += kostka_tab_partition(shape,content,c);
            break;
        case SKEWPARTITION: 
            erg += kostka_tab_skewpartition(shape,content,c);
            break;
        default: 
            WTO(shape,"kostka_tab(1)");
            goto endr_ende;
    }
    ENDR("kostka_tab");
}

    

typedef INT KO_INTARRAY[RH_MAX];

static INT kostka_tab_partition(a,b,c) OP a,b,c;
/* Ralf Hager 1989 */
/* a ist partition fuer umriss */ /* b ist vector fuer inhalt */
/* c wird liste mit allen tableau */ /* AK 271289 V1.1 */
/* AK 210891 V1.3 */
{
    INT    i,j;

    INT    *um,*hilf,*ziel,len,n;
    INT    (* tab)[RH_MAX];
    INT    x,*inh,*hilf_zwei,k;
    INT    counter = (INT)0;
    tab = (KO_INTARRAY *) SYM_calloc(RH_MAX*RH_MAX,sizeof(INT));
    ziel = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    hilf = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    hilf_zwei = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    inh = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    um = (INT *) SYM_malloc(RH_MAX * sizeof(INT));

    init(BINTREE,c); /* AK 170392 */

    for (i=1L;i <=S_PA_LI(a); i++)
        hilf_zwei[i] = S_PA_II(a,S_PA_LI(a)-i);
    x = S_PA_LI(a);
    n = hilf_zwei[1];
    um[1] =  k = x;
    j = 2L;
    while(k >= 1L)
        {
        counter = (INT)0;
        for(i=j;i<=hilf_zwei[k];++i) { counter++; um[i] = x; }
        k--;
        x=k;
        j+= counter;
        }
    for(i=1L;i<=n;++i) hilf[i] = um[i];
    um[0] = -1L;
    for(i=(INT)0;i<n;++i)
        { um[i+1] = um[1]+i; ziel[i+1] = um[i+1] - hilf[i+1]; }
    len = S_V_LI(b);
    for (i=1L;i <= S_V_LI(b); i++) 
        inh[i] = S_V_II(b,i-1L);

    SYM_free(hilf_zwei);
    SYM_free(hilf);
    rh_kostka(tab,um,ziel,inh,(INT)0,(INT)0,inh[1],1L,len,n,um[1],c,a);
    SYM_free(um);
    SYM_free(ziel);
    SYM_free(inh);
    SYM_free(tab);
    t_BINTREE_LIST(c,c); /* AK 170392 */
    return(OK);
    
}

    


static INT rh_kostka(tab,um,ziel,inh,k,i,zahl,st,len,n,deg,c,d)
    INT    tab[RH_MAX][RH_MAX];
    INT    um[RH_MAX];
    INT    ziel[RH_MAX];
    INT    inh[RH_MAX];
    INT    k,i,zahl,st,len,n,deg;
    OP c,d;
{
    INT    l;

    if(i==zahl)    
        {
        if(st==len) 
            rh_ausgabemat(tab,deg,n,c,d); 
        else
        rh_kostka(tab,um,ziel,inh,(INT)0,(INT)0,
            inh[st+1],st+1L,len,n,deg,c,d);
        }
    else 
        {
        for(l=k+1L;l<=n;++l)
            {
            if(((um[l]-1L) > um[l-1])&&(um[l] > ziel[l]))
                {
                    um[l]--;
                    rh_insert(tab[l],st,len);
                    rh_kostka(tab,um,ziel,inh,l,
                        i+1L,zahl,st,len,n,deg,c,d);
                    rh_delete(tab[l],st,len);
                    um[l]++;
                }
            }
        }
    return(OK);
}

    

static INT rh_ausgabemat(tab,n,laenge,c,d)
        INT tab[RH_MAX][RH_MAX],n,laenge; OP c,d;
/* c ist liste, d ist umriss */
/* Ralf Hager 1989 */ /* AK 281289 V1.1 */ /* AK 210891 V1.3 */
{
    INT    i;
    INT    j;
    INT erg = OK;
    OP e = callocobject();
    OP f = callocobject();

    erg += copy(d,e);
    erg += m_u_t(e,f);
    for(i=1L;i<=n;++i)
        for(j=1L;j<=laenge;++j)
            { 
            if (tab[j][i] > (INT)0) 
                M_I_I(tab[j][i],S_T_IJ(f,i-1L,j-1L));
            }
    
    insert(f,c,NULL,NULL);
    erg += freeall(e); /* AK 130392 */
    return erg;
}

    
static INT rh_insert(v,z,len) INT    v[RH_MAX]; INT z,len;
{
    INT    i;

    for(i=1L;i<=len;++i)
        if(v[i]==(INT)0) { v[i]=z; break; }
    return(OK);
}

    
static INT rh_delete(v,z,len) INT    v[RH_MAX]; INT z,len;
{
    INT    i;

    for(i=len;i>=1L;--i)
        if(v[i]>(INT)0) { v[i]=(INT)0; break; }
    return(OK);
}

    
INT kostka_character(a,b) OP a,b;
/* AK 020290 V1.1 */
/* AK 210891 V1.3 */
{
    OP c = callocobject();
    m_part_kostkaperm(a,c);
    newtrans(c,b);
    freeall(c);
    return(OK);
}
    

INT m_part_kostkaperm(a,b) OP a,b; 
/* AK 020290 V1.1 */
/* AK 210891 V1.3 */
{
    INT i,j;
    OP z;
    OP c = callocobject();
    OP d = callocobject();
    weight(a,c);
    m_il_v(S_I_I(c) + S_PA_LI(a),d);
    z = S_V_S(d);
    for (i=(INT)0;i<S_PA_LI(a);i++)
        { M_I_I(S_PA_II(a,i), z++); 
      for (j=0;j<S_PA_II(a,i);j++) M_I_I((INT)0,z++);
        }
    lehmercode(d,b);
    freeall(c);freeall(d);
    return(OK);
}

    
INT moebius_tafel(n,m) OP n,m;
/* eins an den eintraegn der kostkatafel */
/* AK 300790 V1.1 */
/* AK 210891 V1.3 */

    {
    INT i , j;
    OP c = callocobject();
    kostka_tafel(n,c);
    for (i=0;i<S_M_HI(c); i++) 
    for (j=0;j<S_M_HI(c); j++) 
        if (not nullp(S_M_IJ(c,i,j))) {
            if (S_O_K(S_M_IJ(c,i,j)) != INTEGER) 
                freeself(S_M_IJ(c,i,j));
            m_i_i(1L,S_M_IJ(c,i,j)); }
    invers(c,m);
    freeall(c);
    return(OK);
    }


    

INT stirling_second_number_kostka(n,k,result) OP n,k,result;
/* computes stirling number of the second kind,
using kostkanumbers */
/* AK 300790 V1.1 */
/* AK 210891 V1.3 */
{
    OP lp = callocobject();
    OP pv = callocobject();
    OP h1 = callocobject();
    OP h2 = callocobject();
    OP h3 = callocobject();
    OP h4 = callocobject();
    INT i,j;
    m_i_i((INT)0,result); /* freese result first */
    makevectorofpart(n,pv);
    for (i=0;i<S_V_LI(pv);i++)
    {
    if (S_PA_LI(S_V_I(pv,i)) == S_I_I(k))
        {
        m_i_i((INT)0,h4);
        for (j=0;j<S_V_LI(pv);j++)
            {
            kostka_number(S_V_I(pv,i),S_V_I(pv,j),h1);
            kostka_number(S_V_I(pv,S_V_LI(pv)-1L),S_V_I(pv,j),h2);
            mult(h1,h2,h3);
            add_apply(h3,h4);
            }
        t_VECTOR_EXPONENT(S_V_I(pv,i),h3);
        for(j=(INT)0;j<S_PA_LI(h3);j++)
            {
            fakul(S_PA_I(h3,j),h2);
            div(h4,h2,h4);
            }
        add(h4,result,result);
        }
    }
    freeall(h1); freeall(h2); freeall(h3); freeall(h4);
    freeall(lp);freeall(pv);
    return(OK);
}


    

INT stirling_second_number(n,k,result) OP n,k,result;
/* AK 010890 V1.1 */
/* using rekursion */
/* AK 210891 V1.3 */
{
    OP a,b,c,d,e;
    if (negp(n) ) return error("stirling_second_number:neg n");
    if (negp(k) ) return error("stirling_second_number:neg k");
    if (lt(n,k) ) return m_i_i((INT)0,result);
    if (eq(n,k) ) return m_i_i(1L,result);
    if (nullp(n))  return m_i_i((INT)0,result);
    if (nullp(k))  return m_i_i((INT)0,result);
    if (einsp(k))  return m_i_i(1L,result);
    a = callocobject(); b = callocobject(); c = callocobject();
    d = callocobject(); e = callocobject();

    M_I_I(1L,a); 
    copy(n,b);dec(b);
    copy(k,d);dec(d);
    m_i_i((INT)0,result);
    while (lt(a,n))
        {
        binom(b,a,c);
        stirling_second_number(a,d,e);
        mult(c,e,e);
        add(e,result,result);
        inc(a);
        }
    freeall(a); freeall(b); freeall(c); freeall(d); freeall(e);
    return OK;
}

    
INT stirling_first_tafel(a,b) OP a,b;
{
    INT erg = OK;
    erg += stirling_second_tafel(a,b);
    erg += invers(b,b);
    return erg;
}
    

INT stirling_second_tafel(a,b) OP a,b;
{
    INT i,j;
    INT erg = OK;
    OP oi=callocobject();
    OP oj=callocobject();
    erg += m_ilih_m(S_I_I(a)+1L,S_I_I(a)+1L,b);
    for (i=(INT)0; i<=S_I_I(a); i++)
        for (j=(INT)0; j<=S_I_I(a); j++)
            {
        M_I_I(i,oi);
        M_I_I(j,oj);
        erg += stirling_second_number_tafel(oi,oj,S_M_IJ(b,i,j),b);
            }
    erg += freeall(oi); 
    erg += freeall(oj);
    return erg;
}
    

INT stirling_second_number_tafel(n,k,result,t) OP n,k,result,t;
/* AK 010890 V1.1 */
/* using rekursion */
/* AK 210891 V1.3 */
{
    OP a,b,c,d,e;
    if (negp(n) ) return error("stirling_second_number:neg n");
    if (negp(k) ) return error("stirling_second_number:neg k");
    if (lt(n,k) ) return m_i_i((INT)0,result);
    if (eq(n,k) ) return m_i_i(1L,result);
    if (nullp(n))  return m_i_i((INT)0,result);
    if (nullp(k))  return m_i_i((INT)0,result);
    if (einsp(k))  return m_i_i(1L,result);

    if (lt(n,S_M_H(t))) /* wert is in tafel */
        {
        if (not EMPTYP(S_M_IJ(t,S_I_I(n),S_I_I(k))))
            return copy(S_M_IJ(t,S_I_I(n),S_I_I(k)), result);
        }

    a = callocobject(); b = callocobject(); c = callocobject();
    d = callocobject(); e = callocobject();

    M_I_I(1L,a); 
    copy(n,b);dec(b);
    copy(k,d);dec(d);
    m_i_i((INT)0,result);
    while (lt(a,n))
        {
        binom(b,a,c);
        stirling_second_number_tafel(a,d,e,t);
        mult(c,e,e);
        add(e,result,result);
        inc(a);
        }
    freeall(a); freeall(b); freeall(c); freeall(d); freeall(e);
    return OK;
}

    
static INT kostka_tab_skewpartition(a,b,c) OP a,b,c;
/* Ralf Hager 1989 */ /* a ist skewpartition fuer umriss */
/* b ist vector fuer inhalt */ /* c wird liste mit allen tableau */
/* AK 020890 V1.1 */ /* AK 210891 V1.3 */
{
    INT    i,j;

    INT    *um,*hilf,*ziel,len,n;
    INT    (* tab)[RH_MAX];
    INT    x,*inh,*hilf_zwei,k,m;
    INT    counter = (INT)0;
    OP cp = callocobject();

    tab = (KO_INTARRAY *) SYM_calloc(RH_MAX*RH_MAX,sizeof(INT));
    ziel = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    hilf = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    hilf_zwei = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    inh = (INT *) SYM_malloc(RH_MAX * sizeof(INT));
    um = (INT *) SYM_malloc(RH_MAX * sizeof(INT));

    init(BINTREE,c); /* AK 170392 */

    for (i=1L;i <=S_SPA_GLI(a); i++)
        hilf_zwei[i] = S_SPA_GII(a,S_SPA_GLI(a)-i);
    x = S_SPA_GLI(a);
    n = hilf_zwei[1];
    um[1] =  k = x;
    j = 2L;
    while(k >= 1L)
        {
        counter = (INT)0;
        for(i=j;i<=hilf_zwei[k];++i) { counter++; um[i] = x; }
        k--;
        x=k;
        j+= counter;
        }
    for(i=1L;i<=n;++i) hilf[i] = um[i];
    um[0] = -1L;
    for(i=(INT)0;i<n;++i)
        { um[i+1] = um[1]+i; ziel[i+1] = um[i+1] - hilf[i+1]; }
    m= S_SPA_KLI(a);
    conjugate(S_SPA_K(a),cp);
    m = S_PA_LI(cp);
    for(i=(INT)0;i<m;++i) { 
        for (j=(INT)0;j<S_PA_II(cp,m-i-1); j++)
            {
            tab[i+1][j+1]=   -7L;  
            } 
        }
    for(i=(INT)0;i<m;++i) { 
         um[i+1]=um[i+1]-S_PA_II(cp,m-i-1);   
            }
    len = ((S_SPA_GLI(a) > S_V_LI(b)) ? S_SPA_GLI(a) : S_V_LI(b) ) ;
    for (i=1L;i <= S_V_LI(b); i++) inh[i] = S_V_II(b,i-1L);
    for (;i<=len;i++) inh[i]=(INT)0;  /* AK 240593 */
    SYM_free(hilf);
    SYM_free(hilf_zwei);
    
    rh_kostka(tab,um,ziel,inh,(INT)0,(INT)0,inh[1],1L,
        len,n,um[1]+S_PA_II(cp,m-1),c,a);
    freeall(cp);
    t_BINTREE_LIST(c,c); /* AK 170392 */
    SYM_free(um);
    SYM_free(ziel);
    SYM_free(inh);
    SYM_free(tab);
    return(OK);
    
}



/* bricknumber */

static INT bco();

INT SYMMETRICA_bricknumber(umriss,cont,res)
/* brick tabloids linke in remmel egecioglu:
   disc appl math 34 (1991) 107-120 */
/* AK 120901 */
    OP umriss,cont,res;
{
    INT erg = OK,i,j=0;
    /* rekursion per zeile */
    /* der cont muss sortiert sein */
    OP ni,bb;
    CE3(umriss,cont,res,SYMMETRICA_bricknumber);

    if (S_O_K(umriss) == PARTITION) umriss = S_PA_S(umriss);
    if (S_O_K(cont) == PARTITION) {
          cont = S_PA_S(cont);
          ni = cont;
          }
    else {
        j=1;
        ni = callocobject();
        erg += copy_integervector(cont,ni);
        erg += sort_vector(ni); /* ansteigend */
        }
    if (umriss == cont) {
        j=1;
        ni = callocobject();
        erg += copy_integervector(umriss,ni);
        erg += sort_vector(ni); /* ansteigend */
        }
    erg += m_i_i(0,res);
    bb = callocobject();
    erg += m_il_nv(S_V_LI(umriss),bb);
    for (i=0;i<S_V_LI(bb);i++)
         erg += m_il_nv(S_V_II(ni,S_V_LI(ni)-1),S_V_I(bb,i));
    erg += bco(0,0,umriss,ni,res,bb);
    if (j==1) erg += freeall(ni);
    erg += freeall(bb);
    ENDR("SYMMETRICA_bricknumber");
}

static INT bco(spalte,zeile,umriss,cont,res,bb)  int spalte,zeile;OP umriss,cont,res,bb;
{
    INT erg = OK;
    int i,temp,tt=0;


    if (zeile >= S_V_LI(umriss)) {
         /* end of recursion */
         erg += inc(res);
         goto endr_ende;
         }

    if (S_V_II(umriss,zeile) == 0) {
         /* es kann an die naechste zeile gegangen werden, das ergebnis von dort
            muss mit dem pasenden multimomial coeff multipliziert werden */

         OP newres = callocobject();
         OP mn = callocobject();
         erg += m_i_i(0,newres);

        /* in bb[zeile] ist die besetzung der unteren zeile 
                   nun multinomial coeff berechnen fuer die multiplikation */

         for (i=0;i<S_V_LI(S_V_I(bb,zeile));i++)
            M_I_I(S_I_I(newres)+S_V_II(S_V_I(bb,zeile),i),newres);

         /* new res ist die summe ueber die multnomial koeff, d.h. das was oben hinkommt
            bei der berechnung des multinomial koeff */

         if (S_I_I(newres) > 1) {
             if (S_I_I(newres) < 13) {
         erg += multinom_small(newres,S_V_I(bb,zeile),mn);
                 tt=1; }
             else
                 erg += multinom(newres,S_V_I(bb,zeile),mn);
             }
         else m_i_i(1,mn);

         /* in mn ist nun der multinomial koeff */


     erg += m_i_i(0,newres);
         erg += bco(0,zeile+1,umriss,cont,newres,bb);

         /* nun noch multiplizieren */
         if (tt==1) {
              if (S_I_I(mn) > 1)
                  erg += mult_apply_integer(mn,newres);
              }
         else
              erg += mult_apply(mn,newres);
         erg += add_apply(newres,res);
         freeall(newres);
         freeall(mn);
         goto endr_ende;
        }

    /* die unterste zeile ist noch nicht gefuellt */
    /* da ansteigend gefuellt wird, muss
       abspalte im cont gesucht werden ob weitere
       eintraege moeglich */

    for (i=spalte;i<S_V_LI(cont);i++)
        {
        if ((i>0) && 
            (S_V_II(cont,i) == S_V_II(cont,i-1))) 
            continue;
        else if (S_V_II(cont,i) > 0) {
            if (S_V_II(cont,i) <= S_V_II(umriss,zeile)) {
                temp = S_V_II(cont,i);
                M_I_I(0,S_V_I(cont,i));
                m_i_i( s_v_ii(umriss,zeile)-temp,s_v_i(umriss,zeile));
                INC_INTEGER(S_V_I(S_V_I(bb,zeile),temp-1));
                erg += bco(i+1,zeile,umriss,cont,res,bb);
                DEC_INTEGER(S_V_I(S_V_I(bb,zeile),temp-1));
                M_I_I(temp,S_V_I(cont,i));
                M_I_I( S_V_II(umriss,zeile)+temp,S_V_I(umriss,zeile));
                }
            else goto endr_ende; /* wenn schon das trum an der stelle i nicht
                                    rein passt, dann auch keine die spaeter kommen, 
                                    da ja der cont ansteigend sortiert ist */
            }
        }
    ENDR("internal bricknumber routine");
}

/* to compute the transition matrices */

static INT newindexofpart_co11(a,b) OP a,b;
/* AK 030102 */
{
    INT h;
    if (S_PA_HASH(a) == -1) C_PA_HASH(a,hash_partition(a));
    h = S_PA_HASH(a) % S_V_LI(b);
    if (h < 0) h += S_V_LI(b);
    return (S_V_II(b,h));
}
 
static INT newtafel(a,b,tf) OP a,b; INT (*tf)();
/* AK 030102 */
{
    INT erg = OK,i,j;
    INT f = 2;
    OP c,h1,h2;
    CTO(INTEGER,"newtafel(1)",a);
    c = CALLOCOBJECT();
    h2 = CALLOCOBJECT();
    erg += makevectorofpart(a,c);
again:
    init_size_hashtable(h2,S_V_LI(c)*f);
    C_O_K(h2,INTEGERVECTOR);
    for (i=0;i<S_V_LI(h2);i++) M_I_I(-1,S_V_I(h2,i));
    for (i=0;i<S_V_LI(c);i++)
        {
        INT h;
        C_PA_HASH(S_V_I(c,i),hash(S_V_I(c,i)));
        h = S_PA_HASH(S_V_I(c,i)) % S_V_LI(h2);
        if (h <0) h += S_V_LI(h2);
 
        if (S_V_II(h2, h) != -1) /* coll */ { f++; goto again; }
        M_I_I(i, S_V_I(h2,h));
        }
 
 
    erg += m_ilih_nm(S_V_LI(c),S_V_LI(c),b);
    NEW_HASHTABLE(h1);
    for (i=0;i<S_V_LI(c);i++)
         {
         OP z;
         CTO(HASHTABLE,"newtafel(i1)",h1);
         (*tf)(S_V_I(c,i),h1);
         CTO(HASHTABLE,"newtafel(i2)",h1);
         FORALL(z,h1, {
            j = newindexofpart_co11(S_MO_S(z),h2);
            FREESELF(S_M_IJ(b,i,j));
            COPY(S_MO_K(z),S_M_IJ(b,i,j));
            FREESELF(S_MO_K(z));
            M_I_I(0,S_MO_K(z));
            });
         }
    FREEALL(c);
    FREEALL(h1);
    FREEALL(h2);
    ENDR("chartafel");
}

INT SYMMETRICA_HM(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_HM(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_HM:parameter < 0");
    newtafel(a,b,t_HOMSYM_MONOMIAL);
    ENDR("SYMMETRICA_HM");
}

INT SYMMETRICA_HE(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_HE(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_HE:parameter < 0");
    newtafel(a,b,t_HOMSYM_ELMSYM);
    ENDR("SYMMETRICA_HE");
}

INT SYMMETRICA_HS(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_HS(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_HS:parameter < 0");
    newtafel(a,b,t_HOMSYM_SCHUR);
    ENDR("SYMMETRICA_HE");
}

INT SYMMETRICA_HP(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_HP(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_HP:parameter < 0");
    newtafel(a,b,t_HOMSYM_POWSYM);
    ENDR("SYMMETRICA_HP");
}

/* from schur */
 
INT SYMMETRICA_SM(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_SM(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_SM:parameter < 0");
    newtafel(a,b,t_SCHUR_MONOMIAL);
    ENDR("SYMMETRICA_SM");
}
 
INT SYMMETRICA_SE(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_SE(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_SE:parameter < 0");
    newtafel(a,b,t_SCHUR_ELMSYM);
    ENDR("SYMMETRICA_SE");
}
 
INT SYMMETRICA_SH(a,b) OP a,b;
/* AK 040102 */
/* AK 270202 via MS */
{
    INT erg = OK;
    OP c;
    CTO(INTEGER,"SYMMETRICA_SH(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_SH:parameter < 0");

    c = CALLOCOBJECT();
    erg += newtafel(a,c,t_MONOMIAL_SCHUR);
    erg += transpose(c,b);
    FREEALL(c);
    ENDR("SYMMETRICA_EH");
}
 
INT SYMMETRICA_SP(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_SP(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_SP:parameter < 0");
    newtafel(a,b,t_SCHUR_POWSYM);
    ENDR("SYMMETRICA_SP");
}
 
/* from monomial */
 
INT SYMMETRICA_MH(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_MH(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_MH:parameter < 0");
    newtafel(a,b,t_MONOMIAL_HOMSYM);
    ENDR("SYMMETRICA_MH");
}
 
INT SYMMETRICA_ME(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_ME(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_ME:parameter < 0");
    newtafel(a,b,t_MONOMIAL_ELMSYM);
    ENDR("SYMMETRICA_ME");
}
 
INT SYMMETRICA_MS(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_MS(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_MS:parameter < 0");
    newtafel(a,b,t_MONOMIAL_SCHUR);
    ENDR("SYMMETRICA_MS");
}
 
INT SYMMETRICA_MP(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_MP(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_MP:parameter < 0");
    newtafel(a,b,t_MONOMIAL_POWSYM);
    ENDR("SYMMETRICA_MP");
}

/* from elmsym */ 
 
INT SYMMETRICA_EM(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_EM(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_EM:parameter < 0");
    newtafel(a,b,t_ELMSYM_MONOMIAL);
    ENDR("SYMMETRICA_EM");
}
 
INT SYMMETRICA_EH(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_EH(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_EH:parameter < 0");
    newtafel(a,b,t_ELMSYM_HOMSYM);
    ENDR("SYMMETRICA_EH");
}
 
INT SYMMETRICA_ES(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_ES(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_ES:parameter < 0");
    newtafel(a,b,t_ELMSYM_SCHUR);
    ENDR("SYMMETRICA_ES");
}
 
INT SYMMETRICA_EP(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_EP(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_EP:parameter < 0");
    newtafel(a,b,t_ELMSYM_POWSYM);
    ENDR("SYMMETRICA_EP");
}
/* from powsym */ 
 
INT SYMMETRICA_PM(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_PM(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_PM:parameter < 0");
    newtafel(a,b,t_POWSYM_MONOMIAL);
    ENDR("SYMMETRICA_PM");
}
 
INT SYMMETRICA_PE(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_PE(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_PE:parameter < 0");
    newtafel(a,b,t_POWSYM_ELMSYM);
    ENDR("SYMMETRICA_PE");
}
 
INT SYMMETRICA_PS(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_PS(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_PS:parameter < 0");
    newtafel(a,b,t_POWSYM_SCHUR);
    ENDR("SYMMETRICA_PS");
}
 
INT SYMMETRICA_PH(a,b) OP a,b;
/* AK 040102 */
{
    INT erg = OK;
    CTO(INTEGER,"SYMMETRICA_PH(1)",a);
    SYMCHECK(S_I_I(a)<0,"SYMMETRICA_PH:parameter < 0");
    newtafel(a,b,t_POWSYM_HOMSYM);
    ENDR("SYMMETRICA_PH");
}
 

#endif /* KOSTKATRUE */
