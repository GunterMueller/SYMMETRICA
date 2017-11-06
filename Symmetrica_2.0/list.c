/* file: list.c */
#include "def.h"
#include "macro.h"

static struct list * calloc_list();
static INT free_list();

static INT mem_counter_list;
static int list_speicherindex=-1; /* AK 290102 */
static int list_speichersize=0; /* AK 290102 */
static struct list **list_speicher=NULL; /* AK 290102 */


#ifdef LISTTRUE
INT list_anfang()
/* AK 100893 */
    {
    mem_counter_list=0L;
    return OK;
    }





INT list_ende()
/* AK 100893 */
    {
    INT erg = OK;

    if (no_banner != TRUE)
    if (mem_counter_list != 0L)
        {
        fprintf(stderr,"mem_counter_list = %ld\n",mem_counter_list);
        erg += error("list memory not freed");
        goto endr_ende;
        }

    if (list_speicher!=NULL)
        {
        INT i;
        for (i=0;i<=list_speicherindex;i++)
            SYM_free(list_speicher[i]);
        SYM_free(list_speicher);
        }
 
    list_speicher=NULL;
    list_speicherindex=-1;
    list_speichersize=0;

    ENDR("list_ende");
    }


INT empty_listp(a) OP a; 
/* true falls es sich um eine leere liste handelt
d.h. self == NULL */
/* AK 130690 V1.1 */ /* AK 060891 V1.3 */
{ 
    if (not listp(a)) 
        return FALSE;
    if (S_L_S(a) != NULL) 
        return FALSE;
    return TRUE;
}



INT fprint_list(f,list) FILE *f; OP list;
/* ausgabe eines list-objects
ausgabe bis einschliesslich next == NULL */
/* AK 210688 */ /* AK 030789 V1.0 */ /* AK 281289 V1.1 */
/* AK 060891 V1.3 */
{
    INT erg = OK;
    OP zeiger = list;
    OBJECTSELF d; /* AK 141091 */

    COP("fprint_list(1)",f);
    
    if (list == NULL) /* AK 141091 */
        {
        erg +=  NOP("fprint_list");
        goto fple;
        }
    d = S_O_S(list); /* AK 141091 */
    if (d.ob_list == NULL) /* AK 141091 */
        return error("fprint_list:s_o_s == NULL");

    if     ((S_L_S(list) == NULL)&&(S_L_N(list)==NULL))
    /* AK 030389 */
    /* so wird ein list object initialisiert mit b_sn_l(NULL,NULL,obj) */
        {
        fprintf(f,"empty list");
        if (f == stdout) 
            {
            zeilenposition += 10L;
            if (zeilenposition >row_length)
                { 
                fprintf(stdout,"\n"); 
                zeilenposition = 0L; 
                }
            }
        }
    else
        while (zeiger != NULL) 
        {
            if (not LISTP(zeiger))
                {
                erg += WTO("fprint_list:internal",zeiger);
                goto fple;
                }
            erg += fprint(f,S_L_S(zeiger));
            fprintf(f,"  ");
            if (f == stdout) 
            {
                zeilenposition += 2L;
                if (zeilenposition >row_length)
                { 
                fprintf(stdout,"\n"); 
                zeilenposition = 0L; 
                }
            }
            zeiger=S_L_N(zeiger);
        }
fple:
    ENDR("fprint_list");
}
#endif /* LISTTRUE */



INT insert_list(von,nach,eh,cf) OP von,nach; INT (*eh)(), (*cf)();
/* fuegt das object von in die liste nach ein AK 220688 */
/* AK 030789 V1.0 */ /* AK 201289 V1.1 */
/* AK 060891 V1.3 */
/* moegliche faelle:
    a)zwei listen
    b)von ist ein scalar und kann in das entsprechende list object umgewandelt werden 
    c)a ist hashtable und die objecte werden eingefuegt
    d)a ist monom und wird in das entsprechende LIST object umgewandelt
*/
  
{
    OP c;
    INT erg = OK;
    if (LISTP(von))  /* fall a */
        {
        erg += insert_list_list(von,nach,eh,cf);
        goto endr_ende;
        }

    if (S_O_K(von) == HASHTABLE) { /* fall c */
        if (S_O_K(nach) == MONOMIAL) {
            erg += t_HASHTABLE_MONOMIAL(von,von);
            insert_list_list(von,nach,eh,cf);
            goto endr_ende;
            }
        if (S_O_K(nach) == SCHUR) {
            erg += t_HASHTABLE_SCHUR(von,von);
            insert_list_list(von,nach,eh,cf);
            goto endr_ende;
            }
        if (S_O_K(nach) == HOMSYM) {
            erg += t_HASHTABLE_HOMSYM(von,von);
            insert_list_list(von,nach,eh,cf);
            goto endr_ende;
            }
        if (S_O_K(nach) == POWSYM) {
            erg += t_HASHTABLE_POWSYM(von,von);
            insert_list_list(von,nach,eh,cf);
            goto endr_ende;
            }
        if (S_O_K(nach) == ELMSYM) {
            erg += t_HASHTABLE_ELMSYM(von,von);
            insert_list_list(von,nach,eh,cf);
            goto endr_ende;
            }
        FORALL(c,von, {
            OP f;
            f = CALLOCOBJECT();
            erg += swap(c,f);
            insert_list(f,nach,eh , cf);
            });
        erg += freeall(von);
        goto endr_ende;
        }

    



    if (S_O_K(nach) == POLYNOM)
        {
        if (scalarp(von)) 
            {
            c = CALLOCOBJECT();
            erg += b_skn_po(CALLOCOBJECT(),von,NULL,c);
            erg += m_il_v(1L,S_PO_S(c));
            erg += m_i_i(0L,S_PO_SI(c,0L));
            }
        else if (S_O_K(von) == MONOM)
            {
            CTTTTO(INTEGERMATRIX,MATRIX,
                   INTEGERVECTOR,VECTOR,"insert_list(1-monom-self)",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_l(von,NULL,c);
            C_O_K(c,POLYNOM);
            }
        else
            { 
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }

#ifdef SCHURTRUE
    else if (S_O_K(nach) == SCHUR)
        {
        if (scalarp(von)) 
            { 
            c = CALLOCOBJECT();
            erg += b_scalar_schur(von,c); 
            }
        else if (S_O_K(von) == MONOM)
            {
            CTO(PARTITION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_s(von,NULL,c);
            }
        else
            { 
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
    else if (S_O_K(nach) == HOMSYM)
        {
        if (S_O_K(von) == MONOM)
            {
            CTO(PARTITION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_h(von,NULL,c);
            }
        else if (scalarp(von))
            {
            c = CALLOCOBJECT();
            erg += b_scalar_homsym(von,c);
            }
        else
            {
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
    else if (S_O_K(nach) == MONOMIAL)
        {
        if (S_O_K(von) == MONOM)
            {
            CTO(PARTITION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_mon(von,NULL,c);
            }
        else if (scalarp(von))
            {
            c = CALLOCOBJECT();
            erg += b_scalar_monomial(von,c);
            }
        else
            {
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
 
    else if (S_O_K(nach) == ELMSYM)
        {
        if (S_O_K(von) == MONOM)
            {
            CTO(PARTITION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_e(von,NULL,c);
            }
        else if (scalarp(von))
            {
            c = CALLOCOBJECT();
            erg += b_scalar_elmsym(von,c);
            }
        else
            {
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
 
 
    else if (S_O_K(nach) == POWSYM)
        {
        if (scalarp(von))
            {
            c = CALLOCOBJECT();
            erg += b_scalar_powsym(von,c);
            }
        else if (S_O_K(von) == MONOM)
            {
            CTO(PARTITION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_ps(von,NULL,c);
            }
        else
            {
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }

#endif /* SCHURTRUE */

#ifdef SCHUBERTTRUE 
    else if (S_O_K(nach) == SCHUBERT)
        {
        if (scalarp(von)) 
            {
            c = CALLOCOBJECT();
            erg += b_skn_sch(CALLOCOBJECT(),von,NULL,c);
            erg += m_ks_p(VECTOR,CALLOCOBJECT(),S_SCH_S(c));
            erg += m_il_v(1L,S_SCH_S(c));
            erg += m_i_i(1L,S_SCH_SI(c,0L));
            }
        else if (S_O_K(von) == MONOM)
            {
            CTO(PERMUTATION,"insert_list",S_MO_S(von));
            c = CALLOCOBJECT();
            erg += b_sn_l(von,NULL,c);
            C_O_K(c,SCHUBERT);
            }
        else
            { 
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
#endif /* SCHUBERTTRUE */
    else if (S_O_K(nach) == MONOPOLY)
        {
        if (S_O_K(von) == MONOM)
            {
            c = CALLOCOBJECT();
            erg += b_sn_l(von,NULL,c);
            C_O_K(c,MONOPOLY);
            }
        else {
            erg += WTT("insert_list(1,2)",von,nach);
            goto endr_ende;
            }
        }
    else   {
        c = CALLOCOBJECT();
        erg += b_sn_l(von,NULL,c);
        }
    erg +=  insert_list_list(c,nach,eh,cf);

    ENDR("insert_list");
}


#ifdef LISTTRUE
INT copy_list(von,nach) OP von, nach;
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */ /* AK 060891 V1.3 */
{
    OBJECTSELF d; /* AK 141091 */
    d= S_O_S(von);
    if (d.ob_list == NULL)
        return error("copy_list:sos = NULL");
    return transformlist(von,nach,copy);
}



INT lastp_list(list) OP list;
/* AK 210688 */ /* AK 290689 V1.0 */ /* AK 281289 V1.1 */
/* AK 060891 V1.3 */
{
    return(S_L_N(list) == NULL);
    /* das letzte element falls das naechste==NULL */
}



static struct list * calloc_list()
/* AK 210688 */ /* AK 290689 V1.0 */ /* AK 281289 V1.1 */
/* AK 060891 V1.3 */
{
/*
    struct list *a = 
        (struct list *) SYM_MALLOC(sizeof(struct list));

    mem_counter_list++;
    return a;
*/
    struct list *ergebnis;
 
    mem_counter_list++;
 
 
    if (list_speicherindex >= 0) /* AK 301001 */
        return list_speicher[list_speicherindex--];
 
 
 
    ergebnis = (struct list *)
        SYM_malloc( sizeof(struct list));
 
    if (ergebnis == NULL) no_memory();
 
    return ergebnis;

}

static INT free_list(a) struct list *a;
/* AK 300197 */
{
    INT erg = OK;
    COP("free_list(1)",a);
/*
    mem_counter_list--;
    erg += SYM_free(a);
*/
    if (list_speicherindex+1 == list_speichersize) {
       if (list_speichersize == 0) {
           list_speicher = (struct list **) SYM_malloc(100 * sizeof(struct list *));
           if (list_speicher == NULL) {
               erg += error("no memory");
               goto endr_ende;
               }
           list_speichersize = 100;
           }
       else {
           list_speicher = (struct list **) SYM_realloc (list_speicher,
               2 * list_speichersize * sizeof(struct list *));
           if (list_speicher == NULL) {
               erg += error("no memory");
               goto endr_ende;
               }
           list_speichersize = 2 * list_speichersize;
           }
       }
 
    mem_counter_list--;
 
    list_speicher[++list_speicherindex] = a;
 
    ENDR("free_list");
}




INT m_sn_l(self,nx,a) OP self,nx,a;
/* AK 290590 V1.1 */ /* AK 050891 V1.3 */
{
    OP s = NULL,n = NULL;
    INT erg = OK;
    COP("m_sn_l(3)",a);
    if (self != NULL) 
        { 
        s = CALLOCOBJECT(); 
        erg += copy(self,s); 
        }
    if (nx != NULL) 
        { 
        n = CALLOCOBJECT(); 
        erg += copy(nx,n); 
        }
    erg += b_sn_l(s,n,a);
    ENDR("m_sn_l");
}


INT b_sn_l(self,nx,a) OP self,nx,a;
/* build_self next_list AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_l",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(LIST,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_l");
}

INT b_sn_e(self,nx,a) OP self,nx,a;
/* build_self next_elmsym AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_e",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(ELMSYM,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_e");
}

INT b_sn_s(self,nx,a) OP self,nx,a;
/* build_self next_schur AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_s",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(SCHUR,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_s");
}

INT b_sn_ps(self,nx,a) OP self,nx,a;
/* build_self next_powsym AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_ps",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(POWSYM,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_ps");
}

INT b_sn_h(self,nx,a) OP self,nx,a;
/* build_self next_homsym AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_h",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(HOMSYM,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_h");
}

INT b_sn_mon(self,nx,a) OP self,nx,a;
/* build_self next_monomial AK 210688 */
/* AK 290689 V1.0 */ /* AK 281289 V1.1 */  /* AK 050891 V1.3 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_mon",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(MONOMIAL,d,a); 
    C_L_S(a,self); 
    C_L_N(a,nx);
    ENDR("b_sn_mon");
}


INT b_sn_po(self,nx,a) OP self,nx,a;
/* build_self next_polynom AK 230703 */
{
    INT erg =OK;
    OBJECTSELF d;

    COP("b_sn_po",a);
    d.ob_list = calloc_list();
    erg += b_ks_o(POLYNOM,d,a);
    C_L_S(a,self);
    C_L_N(a,nx);
    ENDR("b_sn_po");
}



INT hash_list(list) OP list;
/* AK 170304 */
{
    INT erg = 1257;
    OP z;
    FORALL(z,list, { erg = erg * 1257 + hash(S_MO_S(z))*hash(S_MO_K(z)); } );
    return erg;
}

INT length_list(list,res) OP list,res;
/* AK 220688 */ /* AK 290689 V1.0 */ /* AK 281289 V1.1 */
/* AK 060891 V1.3 */
{
    OP zeiger = list;
    INT erg = OK;
        CTO(EMPTY,"length_list",res);
    M_I_I(0L,res);

    if (empty_listp(list)) 
        goto endr_ende;

    while (zeiger != NULL) /* abbruch bedingung */
    {
        INC_INTEGER(res); 
        zeiger = S_L_N(zeiger);
    }

    ENDR("length_list");
}


INT filter_list(a,b,tf) OP a,b; INT (*tf)();
/* AK 020394 */
{
    OP z,zb=b;
    INT erg = OK, f = 0;
    COP("filter_list(3)",tf);
    z = a;
    while (z != NULL)
        {
        if ((*tf)(S_L_S(z)) == TRUE)
            {
            if (f == 0)
                {
                erg += b_sn_l(CALLOCOBJECT(),NULL,b);
                C_O_K(b,S_O_K(a));
                erg += copy(S_L_S(z),S_L_S(b));
                f = 1;
                }
            else {
                C_L_N(zb,CALLOCOBJECT());
                erg += b_sn_l(CALLOCOBJECT(),NULL,S_L_N(zb));
                erg += copy(S_L_S(z),S_L_S(S_L_N(zb)));
                zb = S_L_N(zb);
                C_O_K(zb,S_O_K(a));
                }
            
            }
        z = S_L_N(z);
        }
    ENDR("filter_list");

}

INT transform_apply_list(von,tf) OP von; INT (*tf)();
/* AK 201289 V1.1 */
/* AK 060891 V1.3 */
/* AK 210498 V2.0 */
{
    OP zeiger = von;
    INT erg = OK;
    COP("transform_apply_list(2)",tf);

    while (zeiger != NULL)
        { erg += (*tf)(S_L_S(zeiger)); zeiger = S_L_N(zeiger); }
    ENDR("transform_apply_list");
}

INT transformlist(von,nach,tf) OP von, nach;INT (*tf)();
/* AK 270688 */ /* AK 030789 V1.0 */ /* AK 010890 V1.1 */ /* AK 060891 V1.3 */
/* AK 210498 V2.0 */
{
    OP zeiger = von;
    OP nachzeiger = nach;
    OBJECTSELF d;
    INT erg = OK; /* AK 100893 */
    COP("transformlist(3)",tf);

    if (not EMPTYP(nach)) 
        erg += freeself(nach);
    while (zeiger != NULL)
    {
        d= S_O_S(zeiger);
        if (d.ob_list == NULL)
            return error("transformlist:sos = NULL");
        if (S_L_S(zeiger) != NULL)
            {
            erg += b_sn_l(CALLOCOBJECT(),NULL,nachzeiger);
            /* AK 100789 b_sn_l() statt init() */
            C_O_K(nachzeiger,S_O_K(zeiger));
            /* AK 107089 fuer faelle wie polynom etc */
            erg += (*tf)(S_L_S(zeiger),S_L_S(nachzeiger));
            }
        else 
            {
            erg += b_sn_l(NULL,NULL,nachzeiger);
            C_O_K(nachzeiger,S_O_K(zeiger));
            }
        if (not lastp(zeiger)) 
            C_L_N(nachzeiger,CALLOCOBJECT());
    
        zeiger = S_L_N(zeiger);
        nachzeiger = S_L_N(nachzeiger);
    }
    ENDR("transformlist");
}

INT trans2formlist(ve,vz,nach,tf) OP ve,vz,nach; INT (*tf)();
/* AK 270688 *//* ve ist konstante , vz ist liste */
/* AK 030789 V1.0 */ /* AK 211289 V1.1 */ /* AK 060891 V1.3 */
{
    OP zeiger = vz;
    OP nachzeiger = nach;
    INT erg = OK;
    COP("trans2formlist(4)",tf);
    

    while (zeiger != NULL)
    {
        erg += b_sn_l(CALLOCOBJECT(),NULL,nachzeiger);
        C_O_K(nachzeiger,S_O_K(vz));
        erg += (*tf)(ve,S_L_S(zeiger),S_L_S(nachzeiger));
        if (not lastp(zeiger))
        { 
            C_L_N(nachzeiger,CALLOCOBJECT());
            nachzeiger = S_L_N(nachzeiger); 
        }
        zeiger = S_L_N(zeiger);
    }
    ENDR("transformlist");
}
#endif /* LISTTRUE */

INT comp_list(a,b) OP a,b;
{
    if ((S_L_S(b) == NULL) && (S_L_S(a) == NULL))
        return 0;
    else if (S_L_S(a) == NULL) 
        return -1;
    else if (S_L_S(b) == NULL)
        return 1;
    else 
        return comp_list_co(a,b,comp);
}

INT comp_list_co(a,b,cf) OP a,b; INT (*cf)();
/* vergleich zweier listen, z.b. 1,1,3  < 1,2,2 z.b. 2,2,3  > 2/3   AK 140788 */
/* AK 030789 V1.0 */ /* AK 010890 V1.1 */
/* AK 060891 V1.3 */
/* self parts are non null */

{
    INT erg;
    SYMCHECK(S_L_S(a) == NULL,"comp_list_co:self(1) == NULL");
    SYMCHECK(S_L_S(b) == NULL,"comp_list_co:self(2) == NULL");
cla:
    erg=(*cf)(S_L_S(a),S_L_S(b));
    if (erg == 0L) /* gleicher listenanfang */
    {
        if ((S_L_N(a) == NULL)&&(S_L_N(b) == NULL)) return(0L);
        /* gleich */
        else if (S_L_N(a) == NULL) return(-1L);
        /* a < b */
        else if (S_L_N(b) == NULL) return(1L);
        /* a > b */
        else {
            a = S_L_N(a);
            b = S_L_N(b);
            goto cla;
            }
        /* rest ist wieder liste */
    }
    else return(erg);
    ENDR("comp_list_co");
}

#ifdef LISTTRUE
OP s_l_s(a) OP a;
/* AK 010890 V1.1 */ /* AK 060891 V1.3 */
{ 
    OBJECTSELF c; 
    if (a == NULL) 
        return error("s_l_s: a == NULL"),(OP)NULL;
    if (not listp(a)) 
        return error("s_l_s: a not list"),(OP)NULL;
    c = s_o_s(a); 
    return(c.ob_list->l_self); 
}

OP s_l_n(a) OP a;
/* AK 010890 V1.1 */ /* AK 060891 V1.3 */
{ 
    OBJECTSELF c; 
    if (a == NULL) 
        return error("s_l_n: a == NULL"),(OP)NULL;
    if (not listp(a)) 
        return error("s_l_n: a not list"),(OP)NULL;
    c = s_o_s(a); 
    return(c.ob_list->l_next); 
}

INT c_l_n(a,b) OP a,b;
/* AK 010890 V1.1 */ /* AK 060891 V1.3 */

{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_list->l_next = b; 
    return(OK); }

INT c_l_s(a,b) OP a,b;
/* AK 010890 V1.1 */ /* AK 060891 V1.3 */
{ 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_list->l_self = b; 
    return(OK); 
}



INT freeself_list(obj) OP obj;
/* AK 290689 V1.0 */ /* AK 211189 V1.1 */ /* AK 170591 V1.2 */
/* AK 060891 V1.3 */
{
    INT erg = OK;
    OP z = obj,za=NULL;


    z = S_L_N(obj);
    while (z != NULL)
        {
        za = z;
        z = S_L_N(z);
        C_L_N(za,NULL);
        if (S_L_S(za) != NULL) FREEALL(S_L_S(za));
        erg += free_list(S_O_S(za).ob_list);
        C_O_K(za,EMPTY);
        FREEALL(za);
        }

    if (S_L_S(obj) != NULL)
        FREEALL(S_L_S(obj));

    erg += free_list(S_O_S(obj).ob_list);
    C_O_K(obj,EMPTY);
    ENDR("freeself_list");
}




INT scan_list(a,givenkind) OP a; OBJECTKIND givenkind;
/* genaue art der liste */
/* AK 210688 */ /* AK 030789 V1.0 */ /* AK 010890 V1.1 */
/* AK 060891 V1.3 */
{
    char antwort[2];
    INT erg;


    /* a ist ein leeres object */
    b_sn_l(callocobject(),NULL,a);
    /* self ist nun initialisiert */
    if (givenkind == (OBJECTKIND)0) {
        /*
            a ----> kind: LIST
                       self: --|
                           |
                           V
                       |-------------|
                       | self : OP   |
                       | next : NULL |
                       |-------------|
            */
        printeingabe("please enter kind of list element");
        givenkind = scanobjectkind(); /* nun weiss man das */
    }


    erg=scan(givenkind,S_L_S(a));
    if (erg == ERROR) {
        error("scan_list:error in scaning listelement");
        goto endr_ende;
    }

    printeingabe("one more listelement y/n");
    skip_comment(); /* AK 210395 */
    scanf("%s",antwort);
    if (antwort[0]  == 'y')
    {
        C_L_N(a,callocobject());
        erg += scan_list(S_L_N(a),givenkind);
    };
    ENDR("scan_list");
}
#endif /* LISTTRUE */


#ifdef VECTORTRUE
#ifdef LISTTRUE
INT t_LIST_VECTOR(a,b) OP a,b;
/* AK 090889 wandelt eine Liste in einen Vektor um */
/* die daten werden dabei kopiert */
/* AK 090889 V1.1 */ /* AK 060891 V1.3 */
{
    INT i;
    INT erg = OK;
    OP l;

    if (not LISTP(a)) 
        WTO("t_LIST_VECTOR",a);
    CE2(a,b,t_LIST_VECTOR);
    l = callocobject();
    erg += length(a,l); 
    erg += b_l_v(l,b); 
    for(i=0L;i<S_I_I(l);i++,a=S_L_N(a))
        erg += copy(S_L_S(a),S_V_I(b,i));
    ENDR("t_LIST_VECTOR");
}

#define T_VECTOR_LIST_CO(a,b,t)\
/* AK 140802 */\
    {\
    INT i;\
    for(i=0L;b != NULL;)\
    {\
        erg += b_sn_l(CALLOCOBJECT(),NULL,b);\
        C_O_K(b,t);\
        COPY(S_V_I(a,i),S_L_S(b));\
        if (++i < S_V_LI(a)) C_L_N(b,CALLOCOBJECT());\
        b = S_L_N(b);\
    }  \
    }

INT t_VECTOR_LIST(a,b) OP a,b;
/* AK 090889 change from vector to list */
/* the order will be the same, data will be copied */
/* AK 090889 V1.1 */ /* AK 130591 V1.2 */ /* AK 060891 V1.3 */
{
    INT i,erg=OK;

    if (not VECTORP(a)) 
        WTO("t_VECTOR_LIST",a);
    CE2(a,b,t_VECTOR_LIST);
    T_VECTOR_LIST_CO(a,b,LIST);
    ENDR("t_VECTOR_LIST");
}

INT t_VECTOR_POLYNOM(a,b) OP a,b;
/* AK 140802 */
{
    INT erg = OK;
    CTO(VECTOR,"t_VECTOR_POLYNOM(1)",a);
    CE2(a,b,t_VECTOR_POLYNOM);
    T_VECTOR_LIST_CO(a,b,POLYNOM);
    ENDR("t_VECTOR_POLYNOM");
}
#endif /* LISTTRUE */
#endif /* VECTORTRUE */


INT test_list() 
/* AK 010890 V1.1 */ /* AK 060891 V1.3 */
{
    OP a= callocobject();
    OP b= callocobject();
    b_sn_l(NULL,NULL,a);
    println(a);
    freeself(a);
    scan(LIST,a);
    println(a);
    scan(LIST,b);
    println(b);
    insert(a,b,NULL,NULL);
    println(b);
    freeself(b);
    return(OK);
}


#ifdef LISTTRUE
INT tex_list(list) OP list;
/* zur ausgabe einer liste */
/* AK 210688 */ /* AK 290689 V1.0 */ /* AK 191289 V1.1 */
/* AK 070291 V1.2 texout instead of stdout for output */
/* AK 060891 V1.3 */
{
    OP zeiger = list;
    while (zeiger != NULL) /* abbruch bedingung */
    {
        tex(S_L_S(zeiger));
        fprintf(texout,"\\ "); 
        texposition += 3L;
        zeiger = S_L_N(zeiger);
    }
    return(OK);
}
#endif /* LISTTRUE */


INT insert_list_list_2(von,nach,eh,cf) OP von,nach; INT (*eh)(), (*cf)();
/* for compability */
{
    return insert_list_list(von,nach,eh,cf);
}

INT insert_list_list(von,nach,eh,cf) OP von,nach; INT (*eh)(), (*cf)();
/* programmiert nach
christopher J. van Wyk : Data  structures and c programs */
/* AK 201289 V1.1 */ /* AK 130591 V1.2 */
/* AK 060891 V1.3 */
{
    struct object dummy;
    struct list dummy_list;
    OP p;
    INT res,erg=OK;
    OBJECTSELF d;
    OBJECTKIND kind=S_O_K(von);
    OP nn,altnext;


    
    if (nach == NULL) {
        error("insert_list_list:nach == NULL");
        /* darf nicht vorkommen, nach muss initialisiert sein */
        goto ende;
    }

    if (EMPTYP(nach)) 
        init(kind,nach);


    if (S_L_S(nach) == NULL)
    {
        C_L_S(nach,S_L_S(von)); 
        C_L_N(nach,S_L_N(von));
        C_L_S(von,NULL); /* AK 300197 */
        C_L_N(von,NULL); /* AK 300197 */
        FREEALL(von); /* AK 300197 */
        goto ende;
    }

    if (S_L_S(von) == NULL)
        {
        FREEALL(von);
        goto ende;
        }


    if (EMPTYP(S_L_S(nach)))    /* nach ist leer */
        {
        erg +=  error("insert_list_list: result is a LIST with empty self");
        goto ende;
        }

    nn = CALLOCOBJECT();
    *nn = *nach;
    p = &dummy;

    d.ob_list = &dummy_list;
    C_O_S(p,d);
    C_O_K(p,LIST);

    if (cf == NULL) cf = comp;
    while((von != NULL) && (nn != NULL))
    {
        res = (* cf)(S_L_S(von),S_L_S(nn));
        if (res < 0L) { 
            C_L_N(p,von);
            von = S_L_N(von);
            p = S_L_N(p);
        }
        else if (res >0L){
            C_L_N(p,nn);
            nn = S_L_N(nn);
            p = S_L_N(p);
        }
        else {
            if (eh == NULL);
            else if (eh == add_koeff) /* AK 011101 */
                {
                ADD_KOEFF(S_L_S(von),S_L_S(nn));
                }
            else (*eh)(S_L_S(von),S_L_S(nn));
            if (not EMPTYP(S_L_S(nn))) {
                /* eh hat nicht geloescht */
                C_L_N(p,nn);
                p = S_L_N(p);
                nn = S_L_N(nn);
            }
            else {
                FREEALL(S_L_S(nn));
                altnext=S_L_N(nn);
                C_L_N(nn,NULL); /* AK 300197 */
                C_L_S(nn,NULL); /* AK 300197 */
                FREEALL(nn); /* AK 300197 */
                nn = altnext;
            }

            FREEALL(S_L_S(von));
            altnext=S_L_N(von);
            C_L_N(von,NULL); /* AK 300197 */
            C_L_S(von,NULL); /* AK 300197 */
            FREEALL(von); /* AK 300197 */
            von = altnext;
        }
    }

    C_L_N(p,NULL);
    if (von == NULL) 
        von = nn;
    if (von != NULL) 
        C_L_N(p,von);
    if (S_L_N(&dummy) == NULL) 
        {
        C_O_K(nach,EMPTY); 
        init (kind,nach);
        }
    else     { 
        *nach = *(S_L_N(&dummy));
        C_O_K(S_L_N(&dummy),EMPTY);
        FREEALL(S_L_N(&dummy));
        }
ende:
    ENDR("insert_list_list");
}

#ifdef LISTTRUE 
INT objectwrite_list(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 100591 V1.2 */
/* AK 060891 V1.3 */
{
    fprintf(f,"%ld ", (INT)S_O_K(a));
    if (S_L_S(a) == NULL) /* 100591 */
        fprintf(f,"%ld\n",0L);
    else    {
        fprintf(f,"%ld\n",1L);
        objectwrite(f,S_L_S(a));
        }
    if (S_L_N(a) == NULL) 
        {
        fprintf(f,"%ld\n",0L);
        return OK;
        }
    else    { 
        fprintf(f,"%ld\n",1L); 
        return objectwrite(f,S_L_N(a)); 
        }
}


INT objectread_list(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 100591 V1.2 */
/* AK 060891 V1.3 */
{
    INT i;
    fscanf(f,"%ld",&i);
    if (i == 0L) 
        b_sn_l(NULL,NULL,a);
    else if (i == 1L)
        {
        b_sn_l(callocobject(),NULL,a);
        objectread(f,S_L_S(a));
        }
    else
        return error("objectread_list: wrong format (1) ");
    fscanf(f,"%ld",&i);
    if (i == 0L) 
        return OK;
    else if (i == 1L) 
        {
        C_L_N(a,callocobject());
        return objectread(f,S_L_N(a)); 
        }
    else
        return error("objectread_list: wrong format (2) ");
}


INT filter_apply_list(a,tf) OP a; INT (*tf)();
/* AK 020394 */
/* if tf return true the elements stays in the list */
/* error beseitigt am 110397 */
/* tf takes a list element as input */
{
    OP z,zb,vorg=NULL;
    INT erg = OK;
    OBJECTKIND typ = S_O_K(a);
    z = a;
    if (S_L_S(a) == NULL) 
        goto endr_ende;
    while (z != NULL)
        {
        if ((*tf)(S_L_S(z)) == TRUE)
            /* stays inside the list */
            {
            if (vorg != NULL)  C_L_N(vorg,z);
            zb = z;
            z = S_L_N(z);
            C_L_N(zb,NULL);
            if (vorg == NULL)
                {
                if (a != zb)
                    {
                    *a = *zb;
                    C_O_K(zb,EMPTY);
                    FREEALL(zb);
                    }
                vorg = a;
                }
            else
                vorg = zb; 
            }
        else    
            /* remove from the list */
            {
            zb = z;
            z = S_L_N(z);
            C_L_N(zb,NULL);
            if (zb != a) FREEALL(zb);
            else FREESELF(zb);
            }
        } /* end while z!=NULL */
    if (vorg == NULL)
        erg += init(typ,a);
        
    ENDR("filter_apply_list");
}
#endif /* LISTTRUE */

