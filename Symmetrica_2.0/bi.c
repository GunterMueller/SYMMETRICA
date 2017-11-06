#include "def.h"
#include "macro.h"
/* AK  291288 */
typedef struct node {
    char * _key; /* dies enthaelt ein object */
    struct node * _l, * _r;
    char _rtag;
} Node;

#define KEY(p) ((p) -> _key)
#define LINKS(p) ((p) -> _l)
#define RECHTS(p) ((p) -> _r)
#define RTAG(p) ((p) -> _rtag)


/* TSEARCH(3C) */
typedef enum {
    preorder, postorder, endorder, leaf }
VISIT;


static INT AK_twalk();
static void AK_tfree();
static char ** AK_tsearch();
static char ** AK_tdelete();
static char ** AK_tfind();
static void walk();
static void freeself_bintree_action();
static void fprint_bintree_action();
static void insert_bt_bt_action();
static void copy_bintree_action();
static void t_BINTREE_LIST_action();
static void t_BINTREE_SCHUR_action();
static void t_BINTREE_POLYNOM_action();
static void t_BINTREE_HOMSYM_action();
static void t_BINTREE_ELMSYM_action();
static void t_BINTREE_POWSYM_action();
static void t_BINTREE_MONOMIAL_action();
static void t_BINTREE_SCHUBERT_action();
static void t_BINTREE_GRAL_action();
static void t_BINTREE_SCHUR_action_apply();
static void t_BINTREE_POLYNOM_action_apply();
static void t_BINTREE_HOMSYM_action_apply();
static void t_BINTREE_POWSYM_action_apply();
static void t_BINTREE_MONOMIAL_action_apply();
static void t_BINTREE_ELMSYM_action_apply();

static char *_bt_p1, *_bt_p2, *_bt_p3; /* fur twalk */
#define TWALK(a,b) AK_twalk((Node *)a,b)
#define TSEARCH AK_tsearch
#define TFIND(a,b,c) AK_tfind((char*)a,(Node **) b,c)
#define TDELETE AK_tdelete

#ifdef BINTREETRUE
static void freeself_bintree_action(a,type) OP *a; VISIT type;
/* AK 210891 V1.3 */
{
    if ((type==postorder) ||  (type==leaf))     
        freeall(*a);
}


INT freeself_bintree(a) OP a;
/* AK 050891 V1.3 */
{
    OBJECTSELF d ;
    d = S_O_S(a);
    AK_tfree(& d.ob_charpointer,freeself_bintree_action,NULL,NULL,NULL);
    C_O_K(a,EMPTY);
    return OK; /* AK 050891 */
}




INT init_bintree(a) OP a;
/* AK 050891 V1.3 */
{
    OBJECTSELF d;
    C_O_K(a,BINTREE);
    d.ob_charpointer = (char *) NULL;
    C_O_S(a,d);
    return(OK);
}



static void length_bintree_action(a,type,l) OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    OP p1 = (OP ) _bt_p1;
    if ((type==postorder)||  (type==leaf))
    {
        inc(p1);
    }
}

static void fprint_bintree_action(a,type,l) OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    FILE *p1 = (FILE *) _bt_p1;
    if ((type==postorder)||  (type==leaf))
    {
        fprint(p1,*a);
        fprintf(p1," ");
        if (p1==stdout) 
            {    
            zeilenposition++;
            if (zeilenposition >70L) {
                fprintf(p1,"\n");
                zeilenposition=0L; }
            }
    }
}




INT length_bintree(a,b) OP a,b;
/* AK 211097 */
{
    void length_bintree_action();
    OBJECTSELF d;
    m_i_i(0,b);
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        }
    else
        {
        _bt_p1 = (char *) b;
        TWALK(d.ob_charpointer,length_bintree_action);
        }
    return OK;
}

INT fprint_bintree(fp,a) FILE *fp; OP a;
/* AK 050891 V1.3 */
/* gibt einen bintree aus */
{
    void fprint_bintree_action();
    OBJECTSELF d;
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        fprintf(fp,"empty tree");
        if (fp == stdout) zeilenposition += 10L;
        }
    else
        {
        _bt_p1 = (char *) fp;
        _bt_p2 = (char *) NULL;
        _bt_p3 =(char *)  NULL;
        TWALK(d.ob_charpointer,fprint_bintree_action);
        }
    return OK;
}



INT insert_bintree(a,bt,eh,cf) OP a,bt; INT (*cf)(), (*eh)();
/* fuegt a in bintree bt ein */
/* cf ist die vergleichsfunktion
       eh gibt die operation bei schon vorhandenem
       gleichen eintrag an */
/* AK 040189 */ /* AK 210891 V1.3 */
{
    INT erg = OK;
    char ** result;

    if (S_O_K(a) == BINTREE) 
        {
        OBJECTSELF d;
        d = S_O_S(a);
        if (d.ob_charpointer == NULL) /* AK 300997 */
            {
            freeall(a);
            return INSERTOK;
            }
        d = S_O_S(bt);
                if (d.ob_charpointer == NULL) /* AK 300997 */
                        {
                        swap(a,bt);
            freeall(a);
                        return INSERTOK;
                        }
        return insert_bt_bt(a,bt,eh,cf);
        }
    else if ( LISTP(a) )
        {
        OP z;
        z = a;
        if (S_L_S(z) != NULL)
            while (z != NULL)
                {
                insert_bintree(S_L_S(z),bt,eh,cf);
                C_L_S(z,NULL);
                z = S_L_N(z);
                }
        FREEALL(a);
        return INSERTOK;
        }

    if (cf == NULL) cf = comp;
    /* default wert */

    result = TSEARCH(a, &((S_O_S(bt)).ob_charpointer) ,cf);
    if (*result == (char *)a) 
        return INSERTOK;
                /* d.h. das element wurde eingefuegt */
    else             /* d.h. es wurde ein gleiches element festgestelt
                und result ist ein pointer darauf */
        {
        if (eh != NULL) 
            (*eh)(a,*result);
        if (EMPTYP((OP)*result)) /* eq-handle hat geloescht */
            {
            OP z = (OP)*result;
            *z = *a;
            TDELETE(a,&((S_O_S(bt)).ob_charpointer) ,cf);
            C_O_K(z,EMPTY);
            FREEALL(z);
            }
        FREEALL(a);
        
        return INSERTEQ;
        }
    ENDR("insert_bintree");
}



INT insert_bt_bt(a,bt,eh,cf) OP a,bt; INT (*cf)(), (*eh)();
/* fuegt a was auch bintree ist in bintree bt ein */
/* cf ist die vergleichsfunktion
       eh gibt die operation bei schon vorhandenem
       gleichen eintrag an */
/* AK 090189 */ /* AK 210891 V1.3 */
{
    OBJECTSELF d;
    INT erg = OK;
    CTO(BINTREE,"insert_bt_bt(1)",a);
    CTO(BINTREE,"insert_bt_bt(2)",bt);
        
    d = S_O_S(a);
    AK_tfree(&d.ob_charpointer,insert_bt_bt_action,bt,eh,cf);
    C_O_K(a,EMPTY); /* leer setzen */
    erg += freeall(a);
    ENDR("insert_bt_bt");
}



static void insert_bt_bt_action(a,type,bt,eh,cf)OP *a,bt; VISIT type; 
        INT (*eh)(),(*cf)();
/* AK 210891 V1.3 */
{
    INT insert_erg;

    if ((type==postorder)||  (type==leaf))
    {
        insert_erg = insert_bintree(*a,bt,eh,cf);
    }
}



INT copy_bintree(a,b) OP a,b;
/* AK 210891 V1.3 */
{
    OBJECTSELF d;

    init(BINTREE,b);
    d = S_O_S(a);
        _bt_p1 = (char *) b;
        _bt_p2 = (char *) NULL;
        _bt_p3 = (char *) NULL;
    TWALK(d.ob_charpointer,copy_bintree_action);
    return OK;
}

static void copy_bintree_action(a,type,l) OP *a; VISIT type; INT l;
/* AK 210891 V1.3 */
{
    OP bt = (OP) _bt_p1;
    if ((type==postorder)||  (type==leaf))
    {
        OP c=callocobject();
        copy(*a,c);
        insert_bintree(c,bt,NULL,NULL);
    }
}


OP find_user_bintree(a,b,f) OP a,b; INT (*f)();
{
    char ** result;
    result = TFIND(a, &((S_O_S(b)).ob_charpointer) ,f);
    if (result == NULL) return NULL;
    return (OP) *result;
}

OP find_bintree(a,b) OP a,b;
/* test ob a in b */
/* AK 050396 */
{
    char ** result;
    result = TFIND(a, &((S_O_S(b)).ob_charpointer) ,comp);
    if (result == NULL) return NULL;
    return (OP) *result;
    
}



static Node ** bi_find(k,rootp,compar, parent, c) char *k; 
    register Node ** rootp; INT (*compar)(); 
    Node ** parent; INT *c;
/* AK 210891 V1.3 */
{
    *parent = (Node *) 0;
    if (rootp && *rootp)
        for (;;)
        {
            if ((*c = (*compar) (k,KEY(*rootp))) == 0L)
                break;
            *parent = *rootp;
            if( *c < 0L)
            {
                rootp = & LINKS(*parent);
                if (! *rootp) break;
            }
            else {
                rootp = & RECHTS(*parent);
                if (RTAG(*parent)) break;
            }
        }

    return (rootp);
}


static char ** AK_tfind(k,rootp,compar) char *k; 
    register Node ** rootp;
    INT (*compar)();
{
    Node * parent;
        INT c;
    if ((rootp = bi_find(k,rootp,compar, &parent, &c)))
                if (*rootp && (c == 0))
                        return (&KEY(*rootp));
    return NULL;
}


static char ** AK_tdelete(k,rootp,compar) char *k;
        register Node ** rootp;
        INT (*compar)();
{
/* Schreiner: UNIX Sprechstude p.248 */
    register Node *p;
    char **result;
    Node * parent; INT c;

    if (! (rootp = bi_find(k,rootp,compar,&parent, &c))
        || ! * rootp || c)
            return (char **) 0;

    result = ! parent ? & KEY (*rootp): & KEY(parent);

    if (!RTAG(*rootp)) {
        Node * R = RECHTS(*rootp);
        if (!LINKS(*rootp)) {
            p = *rootp, *rootp=R, SYM_free(p);
            return result;
            }
        if (! LINKS(R))
            LINKS(R) = LINKS(*rootp), SYM_free(*rootp), *rootp = R;
        else    {
            p = R;
            while(LINKS(LINKS(p)))    p = LINKS(p);
            LINKS(LINKS(p)) = LINKS(*rootp);
            SYM_free(*rootp), *rootp = LINKS(p);
            LINKS(p) = RTAG(LINKS(p))? (Node *)0: RECHTS(LINKS(p));
            RECHTS(*rootp) = R, RTAG(*rootp)=0;
            }
        if ((p = LINKS(*rootp))) {
            while (! RTAG(p)) p = RECHTS(p);
            RECHTS(p) = *rootp, RTAG(p)=1;
            }
        }
    else if ((p=LINKS(*rootp))) {
        while(! RTAG(p)) p = RECHTS(p);
        RECHTS(p) = RECHTS(*rootp), RTAG(p)=1;
        p = *rootp, *rootp = LINKS(p), SYM_free(p);
        }
    else if (parent && RECHTS(parent) == *rootp) {
        p = *rootp;
        RECHTS(parent) = RECHTS(p), RTAG(parent) = 1;
        SYM_free(p);
        }
    else
        SYM_free(*rootp), *rootp = (Node *)0;

    return result;
}

static char ** AK_tsearch(k,rootp,compar) char *k; 
    register Node ** rootp;
    INT (*compar)();
/* AK 210891 V1.3 */
{
    register Node *p;
    Node * parent;
    INT c;

    if ((rootp = bi_find(k,rootp,compar, &parent, &c)))
        if (*rootp && c == 0)
            return (&KEY(*rootp));
        else if ((p = (Node *) SYM_malloc(sizeof(Node))))
        {
            KEY(p) =k;
            LINKS(p) = (Node *) 0;
            if (parent && c>0)
            {
                RECHTS(p) = RECHTS(parent);
                RECHTS(parent) = p, RTAG(parent)= 0;
            }
            else
            {
                RECHTS(p) = parent;
                * rootp = p;
            }
            RTAG(p) = 1;
            return (&KEY(p));
        }
    return ((char**) 0);
}


static void walk(root,action,l) register Node *root; 
    void (*action) (); 
    INT l; 
/* fuer parameter bei action */

/* AK 210891 V1.3 */
{
    if (! LINKS(root) && RTAG(root))
        (*action) (&KEY(root), leaf, l);
    else
    {
        (*action) (&KEY(root), preorder, l);
        if (LINKS(root))
            walk(LINKS(root), action, l+1L);
        (*action) (&KEY(root), postorder, l);
        if (! RTAG(root))
            walk(RECHTS(root), action, l+1L);
        (*action) (&KEY(root), endorder, l);

    }
}

static INT AK_twalk(root,action) Node *root; 
    void (*action) (); 
/* AK 210891 V1.3 */
{
    if (root)
        walk(root,action,0L);
    return OK;
}


static void AK_tfree(rootp,a,bt,eh,cf) Node **rootp; void (*a)();
    OP bt; INT (*eh)(); INT (*cf)();
/* AK 210891 V1.3 */
{
    register Node *root,*p;

    if (!rootp || ! (root = *rootp))
        return;
    * rootp = (Node *)0;
    for (;;)
    {
        while ((p = LINKS(root)))
            root = p;
        if (RTAG(root))
        {
            if (a)
                (* a)(&KEY(root), leaf,bt,eh,cf);
            do
            {
                p=RECHTS(root),SYM_free(root),root=p;
                if (! root)
                    return;
                if (a)
                    (* a)(&KEY(root),postorder,bt,eh,cf);
            } while(RTAG(root));
        }
        else
        {
            if (a)
                (* a)(&KEY(root),postorder,bt,eh,cf);
        }
        p=RECHTS(root),SYM_free(root),root=p;
    }
}


INT t_BINTREE_VECTOR(a,b) OP a,b;
/* input: BINTREE object a
   output: sorted VECTOR object b with copy of the objects in a as content */
/* a and b may be equal */
/* AK V2.0 170298 */
{
    INT erg = OK;
    OP c;
    CTO(BINTREE,"t_BINTREE_VECTOR",a);
    c = callocobject();
    erg += t_BINTREE_LIST(a,c);
    erg += t_LIST_VECTOR(c,b);
    erg += freeall(c);
    ENDR("t_BINTREE_VECTOR");
}

INT t_BINTREE_LIST(a,b) OP a,b;
/* wandelt einen BINTREE in ein LIST object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_LIST_action();
    INT erg = OK; /* AK 170392 */
    OP h, *h2;
    OBJECTSELF d;

    CTO(BINTREE,"t_BINTREE_LIST",a);
    CE2(a,b,t_BINTREE_LIST);

    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(LIST,b);    
        goto endr_ende;
        }

    h = callocobject();
    erg += b_sn_l(NULL,NULL,h);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    erg += TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_LIST_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        erg += b_sn_l(NULL,NULL,b);

    C_O_K(S_L_N(h),EMPTY);
    freeall(S_L_N(h));
    C_L_N(h,NULL); 
    erg += freeall(h); 
    ENDR("t_BINTREE_LIST");
}



static void t_BINTREE_LIST_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder) ||  (type==leaf))
        {
        **(OP **)_bt_p1 = callocobject();
        b_sn_l(callocobject(),NULL,**(OP **)_bt_p1);
        copy(*a,S_L_S(**(OP **)_bt_p1));
        *(OP **)_bt_p1 = & S_L_N(**(OP **)_bt_p1);
        }
}


#ifdef SCHURTRUE
INT t_BINTREE_SCHUR_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_SCHUR_action_apply();
    OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    b = CALLOCOBJECT();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(SCHUR,a);
                goto endr_ende;
                }

        h = CALLOCOBJECT();
        erg += b_sn_s(NULL,NULL,h);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_SCHUR_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                {
        erg += b_sn_s(NULL,NULL,b);
                }

        C_O_K(S_L_N(h),EMPTY);
        FREEALL(S_L_N(h));
        C_L_N(h,NULL);
        FREEALL(h);

    erg += swap(b,a);
    FREEALL(b);

    
    ENDR("t_BINTREE_SCHUR_apply");
}

INT t_BINTREE_SCHUR(a,b) OP a,b;
/* wandelt einen BINTREE in ein SCHUR object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_SCHUR_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;

    CTO(BINTREE,"t_BINTREE_SCHUR(1)",a);

    if (a == b) {
        erg += t_BINTREE_SCHUR_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(SCHUR,b);    
        goto endr_ende;
        }

    h = CALLOCOBJECT();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,SCHUR);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_SCHUR_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,SCHUR);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    FREEALL(h); 
    ENDR("t_BINTREE_SCHUR");
}



static void t_BINTREE_SCHUR_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = CALLOCOBJECT();
        b_sn_s(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}

static void t_BINTREE_SCHUR_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = CALLOCOBJECT();
                b_sn_s(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

INT t_BINTREE_POWSYM_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_POWSYM_action_apply();
    OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    CTO(BINTREE,"t_BINTREE_POWSYM_apply(1)",a);

    b = CALLOCOBJECT();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(POWSYM,a);
                goto endr_ende;
                }

        h = CALLOCOBJECT();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,POWSYM);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_POWSYM_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                {
        erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,POWSYM);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);

    erg += swap(b,a);
    erg += freeall(b);

    
    ENDR("t_BINTREE_POWSYM_apply");
}

INT t_BINTREE_POWSYM(a,b) OP a,b;
/* wandelt einen BINTREE in ein POWSYM object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_POWSYM_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;
    CTO(BINTREE,"t_BINTREE_POWSYM(1)",a);

    if (a == b) {
        erg += t_BINTREE_POWSYM_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(POWSYM,b);    
        goto endr_ende;
        }

    h = CALLOCOBJECT();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,POWSYM);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_POWSYM_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,POWSYM);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    erg += freeall(h); 
    ENDR("t_BINTREE_POWSYM");
}



static void t_BINTREE_POWSYM_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = CALLOCOBJECT();
        b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
        C_O_K(**(OP**)_bt_p1,POWSYM);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}
static void t_BINTREE_POWSYM_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = CALLOCOBJECT();
                b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,POWSYM);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

INT t_BINTREE_ELMSYM_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_ELMSYM_action_apply();
    OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    CTO(BINTREE,"t_BINTREE_ELMSYM_apply(1)",a);
    b = CALLOCOBJECT();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(ELMSYM,a);
                goto endr_ende;
                }

        h = CALLOCOBJECT();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,ELMSYM);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_ELMSYM_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                {
        erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,ELMSYM);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);

    erg += swap(b,a);
    erg += freeall(b);

    
    ENDR("t_BINTREE_ELMSYM_apply");
}

INT t_BINTREE_ELMSYM(a,b) OP a,b;
/* wandelt einen BINTREE in ein ELMSYM object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_ELMSYM_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;
    CTO(BINTREE,"t_BINTREE_ELMSYM(1)",a);

    if (a == b) {
        erg += t_BINTREE_ELMSYM_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(ELMSYM,b);    
        goto endr_ende;
        }

    h = CALLOCOBJECT();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,ELMSYM);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_ELMSYM_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,ELMSYM);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    erg += freeall(h); 
    ENDR("t_BINTREE_ELMSYM");
}



static void t_BINTREE_ELMSYM_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = CALLOCOBJECT();
        b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
        C_O_K(**(OP**)_bt_p1,ELMSYM);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}
static void t_BINTREE_ELMSYM_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = CALLOCOBJECT();
                b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,ELMSYM);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

INT t_BINTREE_HOMSYM_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_HOMSYM_action_apply();
    OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    CTO(BINTREE,"t_BINTREE_HOMSYM_apply(1)",a);
    b = CALLOCOBJECT();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(HOMSYM,a);
                goto endr_ende;
                }

        h = CALLOCOBJECT();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,HOMSYM);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_HOMSYM_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                {
        erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,HOMSYM);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);

    erg += swap(b,a);
    erg += freeall(b);

    
    ENDR("t_BINTREE_HOMSYM_apply");
}

INT t_BINTREE_HOMSYM(a,b) OP a,b;
/* wandelt einen BINTREE in ein HOMSYM object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_HOMSYM_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;
    CTO(BINTREE,"t_BINTREE_HOMSYM(1)",a);

    if (a == b) {
        erg += t_BINTREE_HOMSYM_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(HOMSYM,b);    
        goto endr_ende;
        }

    h = CALLOCOBJECT();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,HOMSYM);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_HOMSYM_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,HOMSYM);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    erg += freeall(h); 
    ENDR("t_BINTREE_HOMSYM");
}



static void t_BINTREE_HOMSYM_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = CALLOCOBJECT();
        b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
        C_O_K(**(OP**)_bt_p1,HOMSYM);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}
static void t_BINTREE_HOMSYM_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = CALLOCOBJECT();
                b_sn_l(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,HOMSYM);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

#endif /* SCHURTRUE */

#ifdef SCHUBERTTRUE
INT t_BINTREE_SCHUBERT(a,b) OP a,b;
/* wandelt einen BINTREE in ein SCHUBERT object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_SCHUBERT_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;
    CTO(BINTREE,"t_BINTREE_SCHUBERT(1)",a);

    CE2(a,b,t_BINTREE_SCHUBERT);

        d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(SCHUBERT,b);
                goto endr_ende;
                }

        h = callocobject();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,SCHUBERT);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_SCHUBERT_action);

        if (S_L_N(h) != NULL)
                *b = *S_L_N(h);
        else
                {
                erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,SCHUBERT);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);
        ENDR("t_BINTREE_SCHUBERT");
}



static void t_BINTREE_SCHUBERT_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = callocobject();
                b_sn_l(callocobject(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,SCHUBERT);
                copy_monom(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

#endif /* SCHUBERTTRUE */
static void t_BINTREE_GRAL_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = callocobject();
                b_sn_l(callocobject(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,GRAL);
                copy_monom(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

INT t_BINTREE_GRAL(a,b) OP a,b;
/* wandelt einen BINTREE in ein GRAL object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
        void t_BINTREE_GRAL_action();
        OP *h2,h;
        INT erg = OK;
        OBJECTSELF d;

        CE2(a,b,t_BINTREE_GRAL);

        d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(GRAL,b);
                goto endr_ende;
                }

        h = callocobject();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,GRAL);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_GRAL_action);

        if (S_L_N(h) != NULL)
                *b = *S_L_N(h);
        else
                {
                erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,GRAL);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);
        ENDR("t_BINTREE_GRAL");
}


INT test_bintree()
{
    OP a,b,c;
    a = callocobject();
    b = callocobject();
    c = callocobject();
    printeingabe("test_bintree:init(BINTREE,a) ");
    init(BINTREE,a); println(a);
    printeingabe("test_bintree:insert(5L,a) ");
    m_i_i(5L,b);insert(b,a,NULL,NULL); println(a);
    printeingabe("test_bintree:insert(7L,a) ");
    b = callocobject();
    m_i_i(7L,b);
    insert(b,a,NULL,NULL);  println(a);
    printeingabe("test_bintree:copy(a,c) ");
    copy(a,c); println(c);
    printeingabe("test_bintree:insert(9L,c) ");
    b = callocobject();
    m_i_i(9L,b);
    insert(b,c,NULL,NULL); 
    println(c);
    freeall(a);
    freeall(c);
    return OK;
}

INT t_BINTREE_MONOMIAL_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_MONOMIAL_action_apply();
        OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    b = callocobject();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(MONOMIAL,a);
                goto endr_ende;
                }

        h = callocobject();
        erg += b_sn_l(NULL,NULL,h);
        C_O_K(h,MONOMIAL);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_MONOMIAL_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                {
        erg += b_sn_l(NULL,NULL,b);
                C_O_K(b,MONOMIAL);
                }

        C_O_K(S_L_N(h),EMPTY);
        erg += freeall(S_L_N(h));
        C_L_N(h,NULL);
        erg += freeall(h);

    erg += swap(b,a);
    erg += freeall(b);

    
    ENDR("t_BINTREE_MONOMIAL_apply");
}

INT t_BINTREE_MONOMIAL(a,b) OP a,b;
/* wandelt einen BINTREE in ein MONOMIAL object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_MONOMIAL_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;

    if (a == b) {
        erg += t_BINTREE_MONOMIAL_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(MONOMIAL,b);    
        goto endr_ende;
        }

    h = callocobject();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,MONOMIAL);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_MONOMIAL_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,MONOMIAL);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    erg += freeall(h); 
    ENDR("t_BINTREE_MONOMIAL");
}



static void t_BINTREE_MONOMIAL_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = callocobject();
        b_sn_l(callocobject(),NULL,**(OP**)_bt_p1);
        C_O_K(**(OP**)_bt_p1,MONOMIAL);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}
static void t_BINTREE_MONOMIAL_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = callocobject();
                b_sn_l(callocobject(),NULL,**(OP**)_bt_p1);
                C_O_K(**(OP**)_bt_p1,MONOMIAL);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

#endif /* BINTREETRUE */
#ifdef BINTREETRUE
INT t_BINTREE_POLYNOM_apply(a) OP a;
/* AK 010198 V2.0 */
{
    OP b;
    void t_BINTREE_POLYNOM_action_apply();
    OP *h2,h;
    OBJECTSELF d;
    INT erg = OK;
    b = CALLOCOBJECT();

    d = S_O_S(a);
        if (d.ob_charpointer == NULL)
                {
                erg += init(POLYNOM,a);
                goto endr_ende;
                }

        h = CALLOCOBJECT();
        erg += b_sn_s(NULL,NULL,h);

        h2 = &S_L_N(h);
                _bt_p1 = (char *)&h2;
                _bt_p2 = (char *)NULL;
                _bt_p3 = (char *)NULL;
        TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_POLYNOM_action_apply);

        if (S_L_N(h) != NULL) 
                *b = *S_L_N(h);
        else
                erg += b_sn_po(NULL,NULL,b);

        C_O_K(S_L_N(h),EMPTY);
        FREEALL(S_L_N(h));
        C_L_N(h,NULL);
        FREEALL(h);

    erg += swap(b,a);
    FREEALL(b);

    
    ENDR("t_BINTREE_POLYNOM_apply");
}

INT t_BINTREE_POLYNOM(a,b) OP a,b;
/* wandelt einen BINTREE in ein POLYNOM object um */
/* die liste ist nach den gleichen vergleich sortiert */
/* AK 070390 V1.1 */ /* AK 050891 V1.3 */
{
    void t_BINTREE_POLYNOM_action();
    OP *h2,h;
    INT erg = OK;
    OBJECTSELF d;

    CTO(BINTREE,"t_BINTREE_POLYNOM(1)",a);

    if (a == b) {
        erg += t_BINTREE_POLYNOM_apply(a);
        goto endr_ende;
        }
        
    d = S_O_S(a);
    if (d.ob_charpointer == NULL)
        {
        erg += init(POLYNOM,b);    
        goto endr_ende;
        }

    h = CALLOCOBJECT();
    erg += b_sn_l(NULL,NULL,h);
    C_O_K(h,POLYNOM);

    h2 = &S_L_N(h);
        _bt_p1 = (char *)&h2;
        _bt_p2 = (char *)NULL;
        _bt_p3 = (char *)NULL;
    TWALK((S_O_S(a)).ob_charpointer,t_BINTREE_POLYNOM_action);

    if (S_L_N(h) != NULL) 
        *b = *S_L_N(h);
    else 
        {
        erg += b_sn_l(NULL,NULL,b);
        C_O_K(b,POLYNOM);
        }

    C_O_K(S_L_N(h),EMPTY);
    erg += freeall(S_L_N(h));
    C_L_N(h,NULL); 
    FREEALL(h); 
    ENDR("t_BINTREE_POLYNOM");
}



static void t_BINTREE_POLYNOM_action(a,type,l)OP *a;VISIT type;INT l;
/* AK 210891 V1.3 */
{
    if ((type==postorder)||  (type==leaf))
        {
        **(OP**)_bt_p1 = CALLOCOBJECT();
        b_sn_po(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
        copy_monom(*a,S_L_S(**(OP**)_bt_p1));
        *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
        }
}

static void t_BINTREE_POLYNOM_action_apply(a,type,l)OP *a;VISIT type;INT l;
/* AK 080199 V2.0 */
{
        if ((type==postorder)||  (type==leaf))
                {
                **(OP**)_bt_p1 = CALLOCOBJECT();
                b_sn_po(CALLOCOBJECT(),NULL,**(OP**)_bt_p1);
                swap(*a,S_L_S(**(OP**)_bt_p1));
                *(OP**)_bt_p1 = & S_L_N(**(OP**)_bt_p1);
                }
}

#endif /* BINTREETRUE */

