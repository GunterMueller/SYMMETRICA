/* SYMMETRICA rh.c */
#include "def.h"
#include "macro.h"

#ifdef REIHETRUE

/* ++++++++++++ jetzt Variablendeklaration +++++++++++++++ */
static INT zuwachs=(INT)5;

/* +++++++++++ Funktionsdeklaration +++++++++++++++++ */

#define new_var new_drei
#define new_mon new_zwei
static INT co_261093();
static INT reihevergleich ();
static INT Eins_eingabe();
static INT co_eingabe();
static INT Random_eingabe();
static INT co_REIHE();
static int debugprint_rh();
static int debugprint_rh_var();
static int debugprint_rh_mon();
static int debugprint_rh_poly();
static struct REIHE_variablen *new_drei();
static struct REIHE_mon *new_zwei();
static struct REIHE_poly *new_eins();
static INT JH_add_reihe();
static INT JH_mult_reihe();
static  int pot_reihe();
static  int transform_reihe();
static  int subst_reihe();
static  int ableitung_reihe();
static INT initial_reihe();
static  INT einfuegen_in_reihe();
static int del_reihe();
static int del_var();
static int del_mon();
static int del_poly();
static  int normalisiere_reihe();
static int make_skalar_reihe();
static  INT make_reihe();
static INT ergaenze_reihe();
static int card_typ_reihe();
static  int card_reihe();
static int variablenvergleich();
static int monomvergleich ();
static int monomgrad();
static INT monommult();
static INT monomausgabe();
static  int trans_reihe_in_monom();
static int copyy_monom();
static JH_copy_reihe();
static JH_copy_reihe_co();
static INT  reihe_zu_sympolynom(), monom_zu_symmonom();
static INT  poly_zu_sympolynom();
static int ausgabe(), copy_var(), copy_mon();
static int free_drei(), free_zwei(), free_eins();

static int del_poly(p) struct REIHE_poly **p;
/* AK 110393 */
{
   if (*p != NULL)
      {
      del_mon(& (*p) ->unten);
      del_poly(& (*p) ->rechts);
      free_eins((char*)*p);
      *p = NULL;
      }
}

static int del_mon(m) struct REIHE_mon **m;
/* AK 110393 */
{
   if (*m != NULL)
      {
      del_var(& (*m)->zeiger);
      if ((*m)-> coeff != NULL)
         freeall((*m)->coeff);
      del_mon(& (*m)->ref);
      free_zwei((char*)(*m));
      *m = NULL;
      }
}

static int del_var(v) struct REIHE_variablen **v;
/* AK 110393 */
{
   if (*v != NULL)
      {
      del_var(&(*v)->weiter);
      free_drei((char*)*v);
      *v = NULL;
      }
}

static int copy_poly(a,b) struct REIHE_poly **b,*a;
/* AK 150393 */
{
   if (a==NULL)
      return (int)(*b = NULL);
   *b = (struct REIHE_poly *) SYM_malloc(sizeof(struct REIHE_poly));
   if (*b == NULL)
      return (int)no_memory;
   (*b)->grad = a->grad;

   copy_mon(a->unten, & (*b)->unten);
   copy_poly(a->rechts, & (*b)->rechts);
}

static int copy_mon(a,b) struct REIHE_mon **b,*a;
/* AK 150393 */
{
   if (a==NULL)
      return (int)(*b = NULL);
   *b = (struct REIHE_mon *) SYM_malloc(sizeof(struct REIHE_mon));
   if (*b == NULL)
      return (int)no_memory;
   (*b)->coeff=callocobject();
   copy(a->coeff, (*b)->coeff);
   copy_mon(a->ref, & (*b)->ref);
   copy_var(a->zeiger, & (*b)->zeiger);
}

static int copy_var(a,b) struct REIHE_variablen **b,*a;
/* AK 150393 */
{
   if (a == NULL)
      return (int)(*b = NULL);
   *b = (struct REIHE_variablen *) SYM_malloc(sizeof(struct REIHE_variablen));
   if (*b == NULL)
      return (int)no_memory;
   (*b)->index = a->index;
   (*b)->potenz = a->potenz;
   copy_var(a->weiter, & (*b)->weiter);
}

static int copy_rh(a,b) REIHE_zeiger a,*b;
{
   if (a == NULL)
      return (int)(*b = NULL);
   *b = (struct reihe *) SYM_malloc(sizeof(struct reihe));
   if (*b == NULL)
      return (int)no_memory;
   (*b)->exist = a->exist;
   (*b)->reihenart = a->reihenart;
   (*b)->z = a->z;
   (*b)->ope = a->ope;
   (*b)->eingabefkt = a->eingabefkt;
   copy_rh(a->x, & (*b)->x);
   copy_rh(a->y, & (*b)->y);
   copy_rh(a->p, & (*b)->p);
   copy_poly(a->infozeig, & (*b)->infozeig);
}


INT max_degree_reihe(a,b) OP a,b;
/* AK 100393 */
{
	OBJECTSELF d;
	INT i;
	INT erg = OK;
	CTO(REIHE,"max_degree_reihe",a);
	d = S_O_S(a);
	if (d.ob_reihe == NULL)
		{
		erg +=  m_i_i((INT)-1,b);
		goto endr_ende;
		}
	i = d.ob_reihe -> exist;
	erg +=  m_i_i(i,b);
	ENDR("max_degree_reihe");
}


static struct REIHE_variablen *new_drei()
{ 
   return (struct REIHE_variablen*) SYM_calloc(1,sizeof(struct REIHE_variablen)); 
}
static int free_drei(a) char *a; { SYM_free(a); }
static int free_zwei(a) char *a; { SYM_free(a); }
static int free_eins(a) char *a; { SYM_free(a); }
static int free_null_debug(a) char *a; { printf("free_null:%ld\n",a); SYM_free(a); }
static int free_null(a) char *a; { SYM_free(a); }

static struct REIHE_mon *new_zwei()
{ 
   return (struct REIHE_mon*) SYM_calloc(1,sizeof(struct REIHE_mon)); 
}

static struct REIHE_poly *new_eins()
{ 
   return
   (struct REIHE_poly*) SYM_calloc(1,sizeof(struct REIHE_poly)); 
}

static struct reihe *new_null() { 
   struct reihe *a;
   a = (struct reihe*) SYM_calloc(1,sizeof(struct reihe)); return a; }

static struct reihe *new_null_debug() { 
   struct reihe *a;
   a = (struct reihe*) SYM_calloc(1,sizeof(struct reihe)); 
   printf("new_null:%ld\n",a);
   return a; }

static INT initial_reihe(adress) REIHE_zeiger* adress;
/* JH 0293 */
{
   *adress=new_null();
   if (*adress == NULL)
      return no_memory();
   (*adress)->exist=0L;
   (*adress)->reihenart=1L;
   (*adress)->x=NULL;
   (*adress)->y=NULL;
   (*adress)->z=0L;
   (*adress)->p=NULL;
   (*adress)->eingabefkt=NULL;
   (*adress)->ope='#';
   (*adress)->infozeig=new_eins();
   (*adress)->infozeig->unten=NULL;
   (*adress)->infozeig->rechts=NULL;
   (*adress)->infozeig->grad=0L;
   return OK;
}

static struct reihe *callocreihe()
/* AK 090393 */
{
   struct reihe *a;
   initial_reihe(&a);
   return a;
}

INT init_reihe(a) OP a;
/* AK 090393 */
{
   OBJECTSELF c;
   c.ob_reihe = callocreihe();
   B_KS_O(REIHE,c,a);
   return OK;
}

static int  normalisiere_reihe(a) REIHE_zeiger a;
{   /* entfernen des absoluten Gliedes wegen pletist. Subst. */
   a->infozeig->unten=NULL;
}

static int card_reihe(a) REIHE_zeiger a;
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon;

   if (a!=NULL)
   {
      zeigpoly=a->infozeig;
      do
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            if (((zeigmon->zeiger)==NULL) ||
                ((zeigmon->zeiger->potenz)==(zeigpoly->grad)))
               monomausgabe(zeigmon);
         }
         zeigpoly=zeigpoly->rechts;
      }  while (zeigpoly!=NULL);
   }
}

static int card_typ_reihe(a) REIHE_zeiger a;
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon;
   OP e;

   if (a!=NULL)
   {
      zeigpoly=a->infozeig;
      do
      {
         if (zeigpoly->unten!=NULL)
         {
            e=callocobject();
            m_i_i(0L,e);
            zeigmon=zeigpoly->unten;
            do
            {
               add_apply(zeigmon->coeff,e);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
            print(e);
            if (zeigpoly->grad!= (INT)0) printf("X^%i\n",zeigpoly->grad);
            else printf("\n");
            freeall(e);
         }
         zeigpoly=zeigpoly->rechts;
      }  while (zeigpoly!=NULL);
   }
}


static int variablenvergleich(p,q) struct REIHE_variablen* p, * q;
{
   int hilf;
   if (q==NULL) hilf=2;
   else if (p == NULL) hilf = -1; /* AK 040893 */
   else
   {                   /* referenzmonom ist ....... als einzufuegendes monom */
      hilf=0;                             /* gleich   */
      if ((p->index)>(q->index)) hilf= -1; /* kleiner  */
      if ((p->index)<(q->index)) hilf=1;  /* groesser */
   }
   return hilf;
}

static int monomvergleich (p,q) struct REIHE_mon* p, * q;
{                                  /* p einzufuegendes Monom */
   struct REIHE_variablen* p1;
   struct REIHE_variablen* q1;
   int hilf;

   if (q==NULL) hilf=2;               /* q ist NULLREIHE_zeiger */
   else
   {
   p1=p->zeiger;             /* koennen NULL sein bei abs. Glied  */
   q1=q->zeiger;
      if ((p1==NULL) && (q1==NULL)) hilf=0;        /* gleich */
      else if (p1==NULL) hilf= -1; /* AK 030893 */
      else if (q1==NULL) hilf=1; /* AK 030893 */
      else
      {
         while (((p1->index)==(q1->index))
          && ((p1->potenz)==(q1->potenz))
          && ((p1->weiter)!=NULL)) /* nur wenn gleiche Monome,  */
         {            /* sonst schon vorher Unterschied */
            p1=p1->weiter;
            q1=q1->weiter;
         }

         if ((p1->weiter==NULL) &&
             ((p1->index)==(q1->index)) &&
             ((p1->potenz)==(q1->potenz)))
            hilf=0;   /* gleiche Monome */

      /* falls Unterschied erst beim letzten Monomteil
          und p->weiter ist also Null */

         else
		{
            if ((p1->index<q1->index) ||
                ((p1->index==q1->index) 
               && (p1->potenz>q1->potenz)))
			    hilf=1;      /*  Referenzmonom ist groeaer  */
            else 
			hilf= -1;/*  Referenzmonom ist kleiner  */
		}
      }
   }

   return hilf;
}

static int monomgrad(p) struct REIHE_mon* p;
{
   struct REIHE_variablen* p1;
   int hilf;

   hilf=0;
   p1=p->zeiger;
   if (p1!=NULL) 
   {
      do
      {
         /* hilf=hilf+((p1->index))*(p1->potenz); */
         hilf=hilf+((p1->index)+1)*(p1->potenz);
         p1=p1->weiter;
      }    while (p1!=NULL);
   }
return hilf;
}


static INT einfuegen_in_reihe(m,in) struct REIHE_mon* m; REIHE_zeiger in;
{
   /* ein neuer Grad ist immer groeaer als Null,
     es wurde mit Null initialisiert */

   int g,v,gefunden;
   INT erg = OK;

   struct REIHE_poly *zeigpol,*p;
   struct REIHE_mon* zeigmon;
   struct REIHE_mon* hilfmon;
   struct REIHE_variablen* zeigvar,hilfvar;

   g=monomgrad(m);

   gefunden=0;

   p=in->infozeig;

   if (p==NULL)
      error("internal error:RH6");

   while ((p->rechts!=NULL) && (gefunden==0))
   {
      if ((p->rechts->grad)<=g)
         p=p->rechts;
      else gefunden=1;
   }

   /* Vergleiche von links nach rechts , Abbruch sobald etwas zutrifft */
   /* also while ((p->rechts!=NULL) && (p->rechts->grad<g)) */

   if (p->grad==g)
   {
      switch(v=monomvergleich(m,p->unten))  /* falls ganz oben */
      {                                     /*eingesetzt werden mua */
      case 2: 
         p->unten=m; 
         break;    /* als erstes Monom bei Grad 0 */

      case 1: 
         hilfmon=p->unten;     /* ganz oben einsetzen */
         p->unten=m;
         m->ref=hilfmon;
         break;

      case 0: 
         add_apply(m->coeff,p->unten->coeff);
         del_mon(& m); /* AK 110393 */
         break;
      }

      if (v==-1)               /* also noch nicht ganz vorne eingefuegt */
      {
         zeigmon=p->unten;
         while ((v=monomvergleich(m,zeigmon->ref))<=0)
            zeigmon=zeigmon->ref;

         if (monomvergleich(m,zeigmon)==0)      /* passendes Monom gefunden */
            {
            erg += add_apply(m->coeff,zeigmon->coeff) ;
            del_mon(& m); /* AK 110393 */
            }
         else
            switch(v)
            {
            case 2 : /* am Ende anfuegen */
               zeigmon->ref=m; 
               break;

            case 1 : /* naechstes Monom ist groeaer */
               hilfmon=zeigmon->ref;
               zeigmon->ref=m;
               m->ref=hilfmon; 
               break;
            }
      }
   }
   else
      if (p->rechts==NULL)   /* am Ende neuen Grad erzeugen */
      {
         p->rechts=new_eins();
         p=p->rechts;
         p->grad=g;
         p->unten=m;
         p->rechts=NULL;
      }
      else /* neuen Grad dazwischenschieben */
      {
         zeigpol=p->rechts;
         p->rechts=new_eins();
         p=p->rechts;
         p->rechts=zeigpol;
         p->grad=g;
         p->unten=m;
      }
   if (erg != OK)
      error("internal error:RH7");
   return erg;
}

INT Exp_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
/* JH 0293 */
{
   OP b,d,f;
   INT l;
   struct REIHE_mon *zeigmon;

   b=callocobject();
   d=callocobject();
   f=callocobject();

   if (root->exist==0)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      m_i_i(1L,zeigmon->coeff);
      einfuegen_in_reihe(zeigmon,root);
   }

   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
      m_i_i(l,d);
      fakul(d,b);
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      m_i_i(1L,f);
      m_ou_b(f,b,zeigmon->coeff);
      kuerzen(zeigmon->coeff);
      zeigmon->zeiger=new_drei();
      zeigmon->zeiger->weiter=NULL;
      zeigmon->zeiger->index=1;
      zeigmon->zeiger->potenz=l;
      einfuegen_in_reihe(zeigmon,root);
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(f);
}


static INT co_261093(root,anzahl,func) REIHE_zeiger root; INT anzahl;
	INT (*func)();
/* bei benutzer definierten funktionen
   f ist vom typ (OP degree, OP koeff) */
{
   OP b,d,f;
	OP bb;
   INT i,j,l,k;
	INT erg=OK;
   struct REIHE_mon *zeigmon;
   struct REIHE_variablen *zeigvar,*help_drei;

   b=callocobject();
   d=callocobject();
   f=callocobject();

   if (root->exist==0L)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      /* m_i_i(1L,zeigmon->coeff); */
      (*func)(cons_null,b);
      if (S_O_K(b) != POLYNOM)
		EDC("RH11:internal error");
      copy(S_PO_K(b),zeigmon->coeff);
      einfuegen_in_reihe(zeigmon,root);
   }
   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
      m_i_i(l,d);
      (*func)(d,b); 
      if (S_O_K(b) != POLYNOM)
		EDC("RH12:internal error");
	bb = b;
      while (bb!=NULL)
      {
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->zeiger=NULL;
         zeigmon->ref=NULL;
         /* m_i_i(1L,f);  */
         copy(S_PO_K(bb) ,zeigmon->coeff);
         /* for (j=1L;j<=l;j++) */
         for (j=1L;j<=S_PO_SLI(bb);j++)
         {
            if ((k=S_PO_SII(bb,j-1))!=0L)
            {
               help_drei=new_drei();
               help_drei->weiter=NULL;
               if (zeigmon->zeiger==NULL) zeigmon->zeiger=help_drei;
               else zeigvar->weiter=help_drei;
               zeigvar=help_drei;
               /* zeigvar->index=j; */
               zeigvar->index=j-1;
               zeigvar->potenz=k;
            }
         }
         einfuegen_in_reihe(zeigmon,root);
         bb=S_PO_N(bb);
      }
	freeall(b);
      b=callocobject();
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(f);
}

INT Sinus_eingabe(root,anzahl) REIHE_zeiger root; INT anzahl;
{
   OP a,b,c,d,e,f;
   INT l;
   struct REIHE_mon *zeigmon;

   b=callocobject();
   d=callocobject();
   f=callocobject();
   e=callocobject();
   m_i_i(2L,e);

   for (l=(root->exist)+1;l<=(root->exist)+anzahl;l++)
   {
      a=callocobject();
      c=callocobject();
      m_i_i(l,a);
      mod(a,e,c);
      if (einsp(c))
      {
         m_i_i(l,d);
         fakul(d,b);
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->zeiger=NULL;
         zeigmon->ref=NULL;
         freeall(c);
         c=callocobject();
         ganzdiv(a,e,c);
         freeall(a);
         a=callocobject();
         mod(c,e,a);
         if (einsp(a)) m_i_i(-1L,f);
         else m_i_i(1L,f);
         m_ou_b(f,b,zeigmon->coeff);
         kuerzen(zeigmon->coeff);
         zeigmon->zeiger=new_drei();
         zeigmon->zeiger->weiter=NULL;
         zeigmon->zeiger->index=0;
         zeigmon->zeiger->potenz=l;
         einfuegen_in_reihe(zeigmon,root);
      }
      freeall(a);
      freeall(c);
   }
   root->exist = (root->exist)+anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(f);
   freeall(e);
   return OK;
}

INT Cosinus_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
/* JH 0293 */
{
   OP a,b,c,d,e,f;
   INT l;
   struct REIHE_mon *zeigmon;

   b=callocobject();
   d=callocobject();
   f=callocobject();
   e=callocobject();
   m_i_i(2L,e);

   if (root->exist==0L)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      m_i_i(1L,zeigmon->coeff);
      einfuegen_in_reihe(zeigmon,root);
   }

   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
      a=callocobject();
      c=callocobject();
      m_i_i(l,a);
      mod(a,e,c);
      if (nullp(c))
      {
         m_i_i(l,d);
         fakul(d,b);
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->zeiger=NULL;
         zeigmon->ref=NULL;
         freeall(c);
         c=callocobject();
         ganzdiv(a,e,c);
         freeall(a);
         a=callocobject();
         mod(c,e,a);
         if (einsp(a)) m_i_i(-1L,f);
         else m_i_i(1L,f);
         m_ou_b(f,b,zeigmon->coeff);
         kuerzen(zeigmon->coeff);
         zeigmon->zeiger=new_drei();
         zeigmon->zeiger->weiter=NULL;
         zeigmon->zeiger->index=0;
         zeigmon->zeiger->potenz=l;
         einfuegen_in_reihe(zeigmon,root);
      }
      freeall(a);
      freeall(c);
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(e);
   freeall(f);
   return OK;
}

#ifdef PARTTRUE

INT Perm_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
{
   OP b,d,f;
	OP bb;
   INT i,j,l,k;
   struct REIHE_mon *zeigmon;
   struct REIHE_variablen *zeigvar,*help_drei;

   b=callocobject();
   d=callocobject();
   f=callocobject();

   if (root->exist==0)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      m_i_i(1L,zeigmon->coeff);
      einfuegen_in_reihe(zeigmon,root);
   }
   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
      m_i_i(l,d);
      zykelind_Sn(d,b);
	bb = b;
      while (bb!=NULL)
      {
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->zeiger=NULL;
         zeigmon->ref=NULL;
         m_i_i(1L,f); 
         copy(f,zeigmon->coeff);
         for (j=1L;j<=l;j++)
         {
            if ((k=S_PO_SII(bb,j-1))!=0)
            {
               help_drei=new_drei();
               help_drei->weiter=NULL;
               if (zeigmon->zeiger==NULL) zeigmon->zeiger=help_drei;
               else zeigvar->weiter=help_drei;
               zeigvar=help_drei;
               zeigvar->index=j;
               zeigvar->potenz=k;
            }
         }
         einfuegen_in_reihe(zeigmon,root);
         bb=s_po_n(bb);
      }
	freeall(b);
      b=callocobject();
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(f);
	return OK;
}


INT E_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
/* JH 0293 */
{
	OP bb;
   OP b,d,f;
   INT i,j,l,k;
   struct REIHE_mon *zeigmon;
   struct REIHE_variablen *zeigvar,*help_drei;

   b=callocobject();
   d=callocobject();
   f=callocobject();

   if (root->exist==0)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      m_i_i(1L,zeigmon->coeff);
      einfuegen_in_reihe(zeigmon,root);
   }
   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
      m_i_i(l,d);
      zykelind_Sn(d,b);
	bb = b;
      while (bb!=NULL)
      {
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->zeiger=NULL;
         zeigmon->ref=NULL;
         zeigmon->coeff=s_po_k(bb);
         for (j=1L;j<=l;j++)
         {
            if ((k=S_V_II(s_po_s(bb),j-1))!=0L)
            {
               help_drei=new_drei();
               help_drei->weiter=NULL;
               if (zeigmon->zeiger==NULL) zeigmon->zeiger=help_drei;
               else zeigvar->weiter=help_drei;
               zeigvar=help_drei;
               zeigvar->index=j;
               zeigvar->potenz=k;
            }
         }
         einfuegen_in_reihe(zeigmon,root);
         bb=s_po_n(bb);
      }
	freeall(b);
      b=callocobject();
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
   freeall(b);
   freeall(d);
   freeall(f);
	return OK;
}

#endif /* PARTTRUE */
static INT make_reihe(a,eingabe) REIHE_zeiger* a; INT (*eingabe)();
{
   initial_reihe(a);
   (*a)->reihenart=1L;
   (*a)->eingabefkt=eingabe;
   return OK;
}

INT m_function_reihe(f,a) OP a; INT (*f)();
/* AK 261093 */
{
   REIHE_zeiger *b;
   OBJECTSELF d;
	INT erg = OK;
   init(REIHE,a);
   d = S_O_S(a);
   b = & d.ob_reihe;
   (  S_O_S(a).ob_reihe)->reihenart=2L;
   (  S_O_S(a).ob_reihe)->eingabefkt=f;
   erg += ergaenze_reihe( & S_O_S(a).ob_reihe,5L);
   return erg;
}


INT m_scalar_reihe(c,b) OP c,b;
/* AK 100393 */
{
   REIHE_zeiger *a;
   OBJECTSELF d;
   init(REIHE,b);
   d = S_O_S(b);
   a = & d.ob_reihe;
   (*a)->reihenart=1L;
   (*a)->infozeig->unten=new_zwei();
   (*a)->infozeig->unten->coeff=callocobject();
   copy(c,(*a)->infozeig->unten->coeff);
   (*a)->infozeig->unten->zeiger=NULL;
   (*a)->infozeig->unten->ref=NULL;
   return OK;
}

static int make_skalar_reihe(a) REIHE_zeiger* a;
{
   initial_reihe(a);
   (*a)->reihenart=1;
   (*a)->infozeig->unten=new_zwei();
   (*a)->infozeig->unten->coeff=callocobject();
   scan(scanobjectkind(),(*a)->infozeig->unten->coeff);
   (*a)->infozeig->unten->zeiger=NULL;
   (*a)->infozeig->unten->ref=NULL;
}


INT inc_reihe(a) OP a;
/* AK 100393 */
{
   INT erg = OK;
   erg += ergaenze_reihe( & S_O_S(a).ob_reihe,1L);
  ENDR("inc_reihe");
}

static  INT ergaenze_reihe(a,zunahme) REIHE_zeiger* a; INT zunahme;
/* JH 0293 */
{
   INT erg = OK;
   if ((*a)->reihenart==1L)
   {
      if (((*a)->eingabefkt)!=NULL)
         (*((*a)->eingabefkt))((*a),zunahme);
   }
   else if ((*a)->reihenart==0L)
   {                   /* schon definierte Verknuepfung erweitern */
      switch((*a)->ope)
      {
      case 'a': 
         JH_add_reihe((*a)->x,(*a)->y,*a,zuwachs);
         break;
      case 'm': 
         JH_mult_reihe((*a)->x,(*a)->y,*a,zuwachs);
         break;
      case 's': 
         subst_reihe((*a)->x,(*a)->y,a,((*a)->exist)+zuwachs);
         break;    /* immer neue Berechnung */
      case 'p': 
         pot_reihe((*a)->x,(*a)->z,*a,zuwachs);
         break;
      case 'l': 
         ableitung_reihe((*a)->x,(*a)->z,*a,zuwachs);
         break;
      case 't': 
         transform_reihe((*a)->x,(*a)->z,*a,zuwachs);
         break;
      default : 
         erg += error("RH2:internal error");
      }
   }
   else if ((*a)->reihenart == 2L)
	{
	co_261093((*a),zunahme,(*a)->eingabefkt);
	}
   else if ((*a)->reihenart == -1L)
      erg += error("RH1:internal error");
   else
      erg += error("RH10:internal error");
   return erg;
}

INT comp_reihe(a,b)  OP a,b;
/* AK 300793 */
{
	OBJECTSELF c,d;
	INT erg = OK;
	CTO(REIHE,"comp_reihe",a);
	CTO(REIHE,"comp_reihe",b);
	c = S_O_S(a);
	d = S_O_S(b);
	return reihevergleich(c.ob_reihe,d.ob_reihe);
	ENDR("comp_reihe");
}

INT fprint_reihe(f,a) FILE *f; OP a;
/* AK 090393 */
{
   OBJECTSELF c;
   c = S_O_S(a);
   ausgabe(f,c.ob_reihe);
   return OK;
}


static int ausgabe(f, r) REIHE_zeiger r; FILE *f;
/* JH 0293 */
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon;

   if (r!=NULL)
   {
      zeigpoly=r->infozeig;
      do
      {
         if (zeigpoly->unten!=NULL)  
            /* weil p mit Grad 0 initial. wurde,  */
         {                           
            /* aber Konst. nicht unbedingt exist. */
            zeigmon=zeigpoly->unten;
            do
            {
               monomausgabe(f, zeigmon);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }  while (zeigpoly!=NULL);
   }
}

static INT reihevergleich (s, r) REIHE_zeiger s,r;
/* AK 300793 */
{
   struct REIHE_poly *zeigpoly_r;
   struct REIHE_poly *zeigpoly_s;
   struct REIHE_mon *zeigmon_r;
   struct REIHE_mon *zeigmon_s;
   int erg;

   if ((r == NULL) && (s==NULL)) return 0L;
   if ((r == NULL) && (s!=NULL)) return 1L;
   if ((r != NULL) && (s==NULL)) return -1L;
   
      zeigpoly_r=r->infozeig;
      zeigpoly_s=s->infozeig;
      do
      {
         if (zeigpoly_s == NULL) return -1L;
         if (zeigpoly_r == NULL) return 1L;

         if ((zeigpoly_s->unten!=NULL)  &&
          (zeigpoly_r->unten!=NULL)  )
            /* weil p mit Grad 0 initial. wurde,  */
         {                           
            /* aber Konst. nicht unbedingt exist. */
            zeigmon_s=zeigpoly_s->unten;
            zeigmon_r=zeigpoly_r->unten;
            do
            {
               if (zeigmon_s == NULL) return -1L;
               if (zeigmon_r == NULL) return 1L;

               erg = monomvergleich(zeigmon_s, zeigmon_r);
               if (erg != 0) return (INT) erg;
               zeigmon_s=zeigmon_s->ref;
               zeigmon_r=zeigmon_r->ref;
            }      while ((zeigmon_s!=NULL)||(zeigmon_r!=NULL));
         }
         zeigpoly_s=zeigpoly_s->rechts;
         zeigpoly_r=zeigpoly_r->rechts;
      }  while ( (zeigpoly_s!=NULL) ||  (zeigpoly_r!=NULL) ) ;
   return 0L;
}

static int  ableitung_reihe(a,n,c,anzahl) REIHE_zeiger a,c; INT n,anzahl;
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon, *hmon;
   struct REIHE_variablen *zeigvar,*hvar1,*hvar2;
   OP e;
   int gefunden;


   if (c->ope=='#') c->ope='l';
   c->reihenart=0L;
   if ((c->x==NULL) && (c->z==0))
   { 
      c->x=a; 
      c->z=n; 
   }
   else if ((c->x!=a) || (c->z!=n))
   { 
      printf("Falsche Operanden beim Transformieren!"); 
      exit(3); 
   }

   if (a->exist<c->exist+anzahl+1)
      ergaenze_reihe(&a,c->exist+anzahl+n-a->exist);

   /* Ableitung erniedrigt Grad des Monoms um n */

   if (a!=NULL)
   {
      zeigpoly=a->infozeig;
      if (c->exist!=0)
         while ((zeigpoly->grad<=c->exist+n) 
               && (zeigpoly->rechts!=NULL))
            zeigpoly=zeigpoly->rechts;


      while ((zeigpoly!=NULL) && (zeigpoly->grad<=c->exist+anzahl+n))
      {
         if (zeigpoly->unten!=NULL)  /* weil p mit Grad 0 initial. wurde,  */
         {                           /* aber Konst. nicht unbedingt exist. */
            zeigmon=zeigpoly->unten;
            do
            {
               gefunden=0;
               if (zeigmon->zeiger!=NULL)    /* fuer Grad 0 ex. keine Monome */
               {
                  zeigvar=zeigmon->zeiger;
                  do     /* Pruefen, ob Variable im Monom enthalten ist */
                  {
                     if ((zeigvar->index*1L==n) && (zeigvar->potenz>0))
                        gefunden=1;
                     zeigvar=zeigvar->weiter;
                  }     while ((zeigvar!=NULL) && (gefunden==0));
                  if (gefunden==1)
                  {
                     hmon=new_zwei();
                     hmon->zeiger=NULL;
                     hmon->ref=NULL;
                     hmon->coeff=callocobject();
                     copy(zeigmon->coeff,hmon->coeff);
                     zeigvar=zeigmon->zeiger;
                     do
                     {
                        if (((zeigvar->index*1L==n) && (zeigvar->potenz>1)) ||
                            (zeigvar->index!=n))
                        {
/* code folded from here */
   hvar1=new_drei();
   hvar1->weiter=NULL;
   if (zeigvar->index==n)
   {
      e=callocobject();
      m_i_i(zeigvar->potenz*1L,e);
      mult(hmon->coeff,e,hmon->coeff);
      freeall(e);
      hvar1->potenz=zeigvar->potenz-1;
      hvar1->index=zeigvar->index;
   }
   else
   {
      hvar1->index=zeigvar->index;
      hvar1->potenz=zeigvar->potenz;
   }
   if (hmon->zeiger==NULL) hmon->zeiger=hvar1;
   else hvar2->weiter=hvar1;
   hvar2=hvar1;
/* unfolding */
                        }
                        zeigvar=zeigvar->weiter;
                     }       while (zeigvar!=NULL);
                     einfuegen_in_reihe(hmon,c);
                  }
               }
               zeigmon=zeigmon->ref;
            }
                while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
   }
   c->exist+=anzahl;
}



static INT monomausgabe(f, m) struct REIHE_mon* m; FILE *f;
{
   struct REIHE_variablen *zeigvar;
   INT erg = OK;
   if (not(nullp(m->coeff)))
   {
      fprintf(f, " ");
	if (f == stdout) zeilenposition++; /* AK 040893 */
      erg += fprint(f, m->coeff);
      if (m->zeiger!=NULL)               /* fuer Grad 0 ex. keine Monome */
      {
         zeigvar=m->zeiger;
         do
         {
            if (zeigvar->potenz>0L)
               fprintf(f," X%ld^%ld",zeigvar->index,zeigvar->potenz);
	if (f == stdout) zeilenposition+=5L; /* AK 040893 */
            zeigvar=zeigvar->weiter;

		if ((f == stdout) &&
		 (zeilenposition > 70L)) /* AK 040893 */
			{
			zeilenposition = 0L;
			fprintf(f,"\n");
			}
         }    while (zeigvar!=NULL);
	}
	fprintf(f," +");
	if (f == stdout)
		zeilenposition += 2L;
   }
   return erg;
}


static int copyy_monom(m1,m2) struct REIHE_mon* m1, **m2;
{
   struct REIHE_variablen *zvar_eins,*zvar2,*help;

   *m2=new_zwei();
   (*m2)->coeff=callocobject();
   (*m2)->ref=NULL;
   (*m2)->zeiger=NULL;
   copy(m1->coeff,(*m2)->coeff);
   if (m1->zeiger!=NULL)
   {
      zvar_eins=m1->zeiger;
      do
      {
         help=new_drei();
         help->weiter=NULL;
         help->index=zvar_eins->index;
         help->potenz=zvar_eins->potenz;
         if ((*m2)->zeiger==NULL) (*m2)->zeiger=help;
         else zvar2->weiter=help;
         zvar2=help;
         zvar_eins=zvar_eins->weiter;
      }  while (zvar_eins!=NULL);
   }
}


static INT monommult(m1,m2,m3) struct REIHE_mon* m1,*m2, **m3;
{
   int i,p,v;
   INT erg = OK;
   struct REIHE_variablen *help,*zeigvar1, *zeigvar2,  *kopie;
   struct REIHE_mon *helpmon;

   if (monomgrad(m1)<monomgrad(m2))  { 
      helpmon=m1;
      m1=m2;
      m2=helpmon; 
   }
   /*Tausch wegen Multiplikationsalgorithmus */

   copyy_monom(m1,m3);

   erg +=mult(m1->coeff,m2->coeff,(*m3)->coeff);
   zeigvar1=m2->zeiger;

   if (zeigvar1!=NULL)  /* also nicht nur absolutes Glied */
   {

      while (zeigvar1!=NULL)
      {
         i=zeigvar1->index;
         p=zeigvar1->potenz;
         if ((*m3)->zeiger == NULL)   /* AK 040893 */
         {
            zeigvar2=(*m3)->zeiger;
            kopie=new_drei();
            kopie->index=i;
            kopie->potenz=p;
            kopie->weiter=NULL;
            (*m3)->zeiger=kopie;
            (*m3)->zeiger->weiter=zeigvar2;
         }
         
         else if (i<(*m3)->zeiger->index)      /* ganz vorn als erstes */
         {
            zeigvar2=(*m3)->zeiger;
            kopie=new_drei();
            kopie->index=i;
            kopie->potenz=p;
            kopie->weiter=NULL;
            (*m3)->zeiger=kopie;
            (*m3)->zeiger->weiter=zeigvar2;
         }
         else
         {
            zeigvar2=(*m3)->zeiger;
		if (zeigvar2 == NULL) 
			return error("internal error:RH9");
            while ( (v=variablenvergleich(zeigvar1,zeigvar2->weiter)) <=0)
               zeigvar2=zeigvar2->weiter;

            if (variablenvergleich(zeigvar1,zeigvar2)==0)
               zeigvar2->potenz=zeigvar2->potenz+zeigvar1->potenz;
            else
            {
               kopie=new_drei();
               kopie->index=i;
               kopie->potenz=p;
               kopie->weiter=NULL;
               switch(v)
               {
               case 1: 
                  help=zeigvar2->weiter;
                  zeigvar2->weiter=kopie;
                  kopie->weiter=help;
                  break;

               case 2: 
                  zeigvar2->weiter=kopie;
                  break;
               }
            }
         }
         zeigvar1=zeigvar1->weiter;
      }
   }
#ifdef DEBUGRH7
	printf("m1:");monomausgabe(stdout,m1);printf("\n");
	printf("m2:");monomausgabe(stdout,m2);printf("\n");
	printf("m3:");monomausgabe(stdout,*m3);printf("\n");
	zeilenposition = 0L;
#endif /* DEBUGRH7 */
#undef DEBUGRH7
   return erg;
}


static INT  monom_zu_symmonom(m,c) struct REIHE_mon* m; OP c;
{
   struct REIHE_variablen *zeigvar;

   OP a,b,e,f;
   INT g;
   INT i;
   INT erg = OK;

   e=callocobject();
   erg += m_iindex_iexponent_monom(0L,0L,e);
   if (m->zeiger!=NULL)               /* fuer Grad 0 ex. keine Monome */
   {
      zeigvar=m->zeiger;
      do
      {
         if (zeigvar->potenz>0)
         {
            a=callocobject();
            erg += m_iindex_iexponent_monom(
                (zeigvar->index)*1L,(zeigvar->potenz)*1L,a); 
            erg += mult_apply(a,e);
            erg += freeall(a);
         }
         zeigvar=zeigvar->weiter;
      }  while (zeigvar!=NULL);
   }
/*
   erg += mult(m->coeff,e,c);
*/
   erg += mult_scalar_polynom(m->coeff,e,c);
   erg += freeall(e);
   return erg;
}


INT t_REIHE_POLYNOM(a,b) OP a,b;
/* AK 150393 */
{
   INT erg = OK;
	
	if (check_equal_2(a,b,t_REIHE_POLYNOM,&erg) == EQUAL)
                goto tre;

   erg += reihe_zu_sympolynom(S_O_S(a).ob_reihe,b);
tre:
   if (erg != OK)
      EDC("t_REIHE_POLYNOM");
   return erg;
}

INT is_scalar_reihe(c) OP c;
{
   return co_REIHE(c,is_scalar_polynom);
}

INT nullp_reihe(a) OP a;
{
   return co_REIHE(a,nullp);
}
INT einsp_reihe(a) OP a;
{
   return co_REIHE(a,einsp);
}

static INT co_REIHE(a,f) OP a; INT (*f)();
/* AK 280793 */
{
   OP b;
   INT erg;
   b = callocobject();
   t_REIHE_POLYNOM(a,b);
   erg = (*f)(b);
   freeall(b);
   return erg;
}


static INT  poly_zu_sympolynom(a,c) struct REIHE_poly *a; OP c;
/* AK 040893 */
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon;
   INT erg = OK;
   OP h;

   init(POLYNOM,c);
   h=callocobject();
   zeigpoly=a;
   if (zeigpoly->unten!=NULL)
   {
      zeigmon=zeigpoly->unten;
      do
      {
         if (not(nullp(zeigmon->coeff)))
         {
            erg += monom_zu_symmonom(zeigmon,h);
            erg += add_apply(h,c);
         }
         zeigmon=zeigmon->ref;
      }      
      while (zeigmon!=NULL);
   }
	erg += freeall(h); /* AK 131093 */
   return erg;
}

static INT  reihe_zu_sympolynom(a,c) REIHE_zeiger a; OP c;
{
   INT erg = OK;
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *zeigmon;
   struct REIHE_variablen *zeigvar;
   OP h;

	if ((OP)a == c)
		return ERROR;
   h=callocobject();
   erg += init(POLYNOM,c);
   if (a!=NULL)
   {
      zeigpoly=a->infozeig;
      do
      {
         erg += poly_zu_sympolynom(zeigpoly,h);
         erg += add_apply(h,c);
         zeigpoly=zeigpoly->rechts;
      }
          while (zeigpoly!=NULL);
   }
   erg += freeall(h);
   return erg;
}

INT add_apply_reihe(a,b) OP a,b;
/* AK 020893 */
{
   OP c;
   INT erg = OK;

   if (S_O_K(a) != REIHE)
      return WTO("add_apply_reihe",a);

   c = callocobject();
   *c = *b;
   C_O_K(b,EMPTY);
   erg += add(c,a,b);
   erg += freeall(c);
aar_ende:
   if (erg != OK)
      EDC("add_apply_reihe");
   return erg;
}


INT freeself_reihe(a) OP a;
/* AK 100393 */
{
   INT erg = OK;
   CTO(REIHE,"freeself_reihe(1)",a);
   del_reihe(& (S_O_S(a).ob_reihe) );
   C_O_K(a,EMPTY);
   ENDR("freeself_reihe");
}

static int del_reihe(a) REIHE_zeiger *a;
/* AK 110393 */
{
    if (*a != NULL)
      {
      del_reihe(& (*a)->x);
      del_reihe(& (*a)->y);
      del_reihe(& (*a)->p);
      del_poly( & (*a)->infozeig);
      free_null((char*)*a);
      *a = NULL;
      }
}

INT copy_reihe(a,b) OP a,b;
/* AK 100393 */
{
   copy_rh( (S_O_S(a)).ob_reihe,& S_O_S(b).ob_reihe);
   C_O_K(b,REIHE);
   return OK;
}


static JH_copy_reihe(a,c) REIHE_zeiger a; REIHE_zeiger* c;
{
   return JH_copy_reihe_co(a,c,1);
}
static AK_copy_reihe(a,c) REIHE_zeiger a; REIHE_zeiger* c;
{
   return JH_copy_reihe_co(a,c,0);
}

static JH_copy_reihe_co(a,c,i) REIHE_zeiger a; REIHE_zeiger* c; int i;
/* JH 0293 */
{
   struct REIHE_mon *zeigmon,*hmon;
   struct REIHE_poly *zeigpoly;

   del_reihe(c);
   initial_reihe(c);
   (*c)->exist=a->exist;

if  (i==1)
   (*c)->x=a->x;
if  (i==0)
   AK_copy_reihe(a->x, & ((*c)->x) );
if  (i==1)
   (*c)->y=a->y;
if  (i==0)
   AK_copy_reihe(a->y, & ((*c)->y) );

   (*c)->z=a->z;
   (*c)->ope=a->ope;
   (*c)->reihenart=a->reihenart;
if  (i==1)
   (*c)->p=a->p;
if  (i==0)
   AK_copy_reihe(a->p, & ((*c)->p) );

   (*c)->eingabefkt=a->eingabefkt;

if(i==1) {
   if (a!=NULL)     /* dann ist auch a->infozeig!=NULL wegen initial */
   {
      zeigpoly=a->infozeig;
      do
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               copyy_monom(zeigmon,&hmon);
               einfuegen_in_reihe(hmon,*c);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }  while (zeigpoly!=NULL);
   }
   }
if (i==0)
   {
   if (a == NULL)
      if(a->infozeig == NULL) 
         error("JH_copy_reihe_co:(1)");
   copy_poly(a->infozeig, & (*c)->infozeig);
   }
}

static int  pot_reihe(a,n,c,anzahl) REIHE_zeiger a,c; INT n, anzahl;
{
   struct  reihe *help;
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon *hmon,*zeigmon;
   int zaehler;

   if (c->ope=='#') c->ope='p';
   c->reihenart=0L;
   if ((c->x==NULL) && (c->z==0)) { 
      c->x=a; 
      c->z=n; 
   } /* fuer 1.Aufruf */
   else if ((c->x!=a) || (c->z!=n))
   { 
      printf("Falsche Operanden beim Potenzieren!\n"); 
      exit(3); 
   }

   if (a->exist<c->exist+anzahl) ergaenze_reihe(&a,c->exist+anzahl-a->exist);

   help=a;         /* help zeigt jetzt auch auf a */

   zaehler=1;

   while ((help->p!=NULL) && (zaehler!=n))
   {
      help=help->p;
      zaehler=zaehler+1;
   }
   if (zaehler==n)
   {
      if (help->exist<c->exist+anzahl)
         ergaenze_reihe(&help,c->exist+anzahl-help->exist);
   }
   else
   {
      do
      {
         initial_reihe(&(help->p));
         zaehler=zaehler+1;
         help->p->reihenart=0L;
         help->p->ope='m';
         help->p->x=a;
         help->p->y=help;
         JH_mult_reihe(a,help,help->p,c->exist+anzahl);
         help=help->p;
      }  while (zaehler<n);
   }
   /* anhaengen an bestehende Reihe */
   if (help!=NULL)     /* dann ist auch a->infozeig!=NULL wegen initial */
   {
      zeigpoly=help->infozeig;
      if (c->exist!=0)
         while ((zeigpoly->grad<=c->exist) && (zeigpoly->rechts!=NULL))
            zeigpoly=zeigpoly->rechts;

      while ((zeigpoly!=NULL) && (zeigpoly->grad<=c->exist+anzahl))
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               copyy_monom(zeigmon,&hmon);
               einfuegen_in_reihe(hmon,c);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
   }
   c->exist+=anzahl;
}


INT mult_reihe(a,b,c) OP a,b,c;
/* AK 100393 */
{
   INT erg = OK;
   switch(S_O_K(b))
   {
   case BRUCH:
   case INTEGER:
   case LONGINT:
      {
      OP d;
      d = callocobject();
      erg += m_scalar_reihe(b,d);
      erg += mult_reihe(a,d,c);
      erg += freeall(d);
      break;
      }
   case REIHE:
      {
         OBJECTSELF as,bs,cs;
         OP d,e,f,g;
         d = callocobject();
         e = callocobject();
         g = callocobject();
         f = callocobject();
         erg += max_degree_reihe(a,d);
         erg += max_degree_reihe(b,e);
         if (lt(e,d)) copy(d,e);
         erg += copy(a,f);
         erg += copy(b,g);

         erg += init(REIHE,c);
         as = S_O_S(f);
         bs = S_O_S(g);
         cs = S_O_S(c);
         erg += JH_mult_reihe(as.ob_reihe,bs.ob_reihe,cs.ob_reihe,S_I_I(e));
         erg += freeall(d);
         erg += freeall(e);
	C_O_K(f,EMPTY);
	C_O_K(g,EMPTY);
         erg += freeall(f);
         erg += freeall(g);
         break;
      }
   default:
      return WTT("mult_reihe",a,b);
   }
   if (erg != OK)
      EDC("mult_reihe");
   return erg;
}

static INT  JH_mult_reihe(a,b,c,anzahl) REIHE_zeiger a,b,c; INT anzahl;
{
   struct REIHE_poly *zeigpoly1,*zeigpoly2;
   struct REIHE_mon *zeigmon1, *zeigmon2, *hmon;

   if (c->ope=='#') c->ope='m';
   c->reihenart=0L;
   if ((c->x==NULL) && (c->y==NULL))
   { 
      c->x=a; 
      c->y=b; 
   }
   else if (((c->x!=a) || (c->y!=b)) && ((c->x!=b) || (c->y!=a)))
   { 
	return error("RH-internal error");
   }

   if (a->exist<c->exist+anzahl) ergaenze_reihe(&a,c->exist+anzahl-a->exist);
   if (b->exist<c->exist+anzahl) ergaenze_reihe(&b,c->exist+anzahl-b->exist);

   if (a!=NULL)     /* dann ist auch a->infozeig!=NULL wegen initial */
   {
      zeigpoly1=a->infozeig;
      while ((zeigpoly1!=NULL) && (zeigpoly1->grad<=c->exist+anzahl))
      {
         if (zeigpoly1->unten!=NULL)
         {
            zeigmon1=zeigpoly1->unten;
            do
            {
               if (b!=NULL)   
/* dann ist auch b->infozeig!=NULL wegen initial */
               {
                  zeigpoly2=b->infozeig;
                  if (c->exist!=0)
                     while ((zeigpoly2->grad<=c->exist-zeigpoly1->grad) &&
                         (zeigpoly2->rechts!=NULL))
                        zeigpoly2=zeigpoly2->rechts;

                  if (((zeigpoly2->grad+zeigpoly1->grad>c->exist) &&
                      (zeigpoly2->grad+zeigpoly1->grad<=c->exist+anzahl))
                      || (c->exist==0))
                     /* richtiger Grad ist erreicht */
                     do
                     {
                        if (zeigpoly2->unten!=NULL)
                        {
			   zeigmon2=zeigpoly2->unten;
			   do
			   {
			      monommult(zeigmon1,zeigmon2,&hmon);
			      einfuegen_in_reihe(hmon,c);
			      zeigmon2=zeigmon2->ref;
			   }          while (zeigmon2!=NULL);
                        }
                        zeigpoly2=zeigpoly2->rechts;
                     }    /* do */      while ((zeigpoly2!=NULL) &&
                      (zeigpoly2->grad<=c->exist+anzahl-zeigpoly1->grad));
                  /* hier endet das if vor dem do */
               }
               zeigmon1=zeigmon1->ref;
            }      while (zeigmon1!=NULL);
         }
         zeigpoly1=zeigpoly1->rechts;
      }
   }
   c->exist+=anzahl;
   return OK;
}


static int  trans_reihe_in_monom(a,m,b,anzahl) 
		REIHE_zeiger a,*b; struct REIHE_mon *m; INT anzahl;
{
   REIHE_zeiger help_eins,help_zwei,help_drei;
   struct REIHE_variablen *zeigvar;

   del_reihe(b);

   initial_reihe(&help_eins);
   help_eins->exist=1;
   help_eins->reihenart=1L;
   help_eins->infozeig->unten=new_zwei();
   help_eins->infozeig->unten->ref=NULL;
   help_eins->infozeig->unten->zeiger=NULL;
   help_eins->infozeig->unten->coeff=callocobject();
   m_i_i(1L,help_eins->infozeig->unten->coeff);

   if (m->zeiger!=NULL)    /* wegen abs. Glied */
   {
      zeigvar=m->zeiger;
      do
      {
         initial_reihe(&help_zwei);
         pot_reihe(a,zeigvar->potenz,help_zwei,anzahl);
         help_zwei->reihenart=1L;
         initial_reihe(&help_drei);
         transform_reihe(help_zwei,zeigvar->index,help_drei,anzahl);
         help_drei->reihenart=1L;
         del_reihe(&help_zwei);
         initial_reihe(&help_zwei);
         JH_mult_reihe(help_eins,help_drei,help_zwei,anzahl);
         help_zwei->reihenart=1L;
         del_reihe(&help_eins);
         del_reihe(&help_drei);
         help_eins=help_zwei;
         help_zwei=NULL;

         zeigvar=zeigvar->weiter;
      }  while (zeigvar!=NULL);
   }

   initial_reihe(&help_zwei);     /* Realisation der Skalarmult. mit coeff */
   help_zwei->exist=1;
   help_zwei->reihenart=1L;
   help_zwei->infozeig->unten=new_zwei();
   help_zwei->infozeig->unten->ref=NULL;
   help_zwei->infozeig->unten->zeiger=NULL;
   help_zwei->infozeig->unten->coeff=callocobject();
   copy(m->coeff,help_zwei->infozeig->unten->coeff);

   initial_reihe(&help_drei);
   JH_mult_reihe(help_eins,help_zwei,help_drei,anzahl);
   help_drei->reihenart=1L;
   del_reihe(&help_eins);
   del_reihe(&help_zwei);

   *b=help_drei;
}


static int subst_reihe(a,b,c,anzahl) REIHE_zeiger a,b,* c; INT anzahl ;
{
   struct REIHE_poly *zeigpoly;
   REIHE_zeiger help_eins,help_zwei,help_drei,help4;
   struct REIHE_mon *zeigmon;
   int m;

   /*  a Basisreihe   b einzusetzende Reihe   c Ergebinsreihe  */
   if (((*c)->x==NULL) && ((*c)->y==NULL)) { 
      (*c)->x=a; 
      (*c)->y=b; 
   }
   else if ((((*c)->x!=a) || ((*c)->y!=b)) && (((*c)->x!=b) || ((*c)->y!=a)))
   { 
      printf("Falsche Operanden bei der Substitution!"); 
      exit(3); 
   }

   normalisiere_reihe(b);
   del_reihe(c);
   if (a->exist<anzahl) ergaenze_reihe(&a,anzahl-a->exist);
   if (b->exist<anzahl) ergaenze_reihe(&b,anzahl-b->exist);

   initial_reihe(&help4);    /* help4 enthaelt immer das ergebnis */
   help4->reihenart=1L;       /* wird somit zum Skalar = 0 */

   if (a!=NULL)
   {
      zeigpoly=a->infozeig;
      do
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               initial_reihe(&help_eins);
               trans_reihe_in_monom(b,zeigmon,&help_eins,anzahl);
               help_eins->reihenart=1L;
               initial_reihe(&help_zwei);
               JH_add_reihe(help_eins,help4,help_zwei,anzahl);
               help_zwei->reihenart=1L;
               del_reihe(&help_eins);
               del_reihe(&help4);
               help4=help_zwei;
               help_zwei=NULL;

               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
          while (zeigpoly!=NULL);
   }

   /* initial_reihe(c);  Zeiger nur umhaengen */
   *c=help4;
   (*c)->x=a;
   (*c)->y=b;                /* und noch die alten infos uebertragen */
   (*c)->reihenart=0L;
   (*c)->exist=anzahl;
   (*c)->ope='s';
}


INT add_reihe(a,b,c) OP a,b,c;
/* AK 100393 */
{
   INT erg = OK;
   switch(S_O_K(b))
   {
   case REIHE:
      {
         OBJECTSELF as,bs,cs;
         OP d,e,f,g;

         d = callocobject();
         e = callocobject();
         f = callocobject();
         g = callocobject();
         copy(a,f);
         copy(b,g);
         erg += max_degree_reihe(f,d);
         erg += max_degree_reihe(g,e);
         if (lt(e,d)) 
            copy(d,e);

         erg += init(REIHE,c);
         as = S_O_S(f);
         bs = S_O_S(g);
         cs = S_O_S(c);
         erg += JH_add_reihe(as.ob_reihe,bs.ob_reihe,cs.ob_reihe,S_I_I(e));
         erg += freeall(d);
         erg += freeall(e);
	C_O_K(f,EMPTY);
	C_O_K(g,EMPTY);
         erg += freeall(f);
         erg += freeall(g);
         break;
      }
   case INTEGER:
   case BRUCH:
   case LONGINT:      /* AK 020893 */
      {
         OP d;
         d = callocobject();
         erg += m_scalar_reihe(b,d);
         erg += add_reihe(a,d,c);
         erg += freeall(d);
         break;
      }
   default:
      return WTT("add_reihe",a,b);
   }
   ENDR("add_reihe");
}

static INT JH_add_reihe(a,b,c,anzahl) REIHE_zeiger a,b,c; INT anzahl;
/* JH 0293 */
{
   struct REIHE_mon *zeigmon,*hmon;
   struct REIHE_poly *zeigpoly;

   if (c->ope=='#') c->ope='a';
   c->reihenart=0L;
   if ((c->x==NULL) && (c->y==NULL))
   { 
      c->x=a; 
      c->y=b; 
   }
   else if (((c->x!=a) || (c->y!=b)) && ((c->x!=b) || (c->y!=a)))
   { 
      printf("Falsche Operanden bei der Addition!"); 
      exit(3); 
   }

   if (a->exist<c->exist+anzahl) ergaenze_reihe(&a,c->exist+anzahl-a->exist);
   if (b->exist<c->exist+anzahl) ergaenze_reihe(&b,c->exist+anzahl-b->exist);
   if (a!=NULL)     /* dann ist auch a->infozeig!=NULL wegen initial */
   {
      zeigpoly=a->infozeig;
      if (c->exist!=0)
         while ((zeigpoly->grad<=c->exist) && (zeigpoly->rechts!=NULL))
            zeigpoly=zeigpoly->rechts;

      while ((zeigpoly!=NULL) && (zeigpoly->grad<=c->exist+anzahl))
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               copyy_monom(zeigmon,&hmon);
               einfuegen_in_reihe(hmon,c);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
   }

   if (b!=NULL)
   {
      zeigpoly=b->infozeig;
      if (c->exist!=0)
         while ((zeigpoly->grad<=c->exist) && (zeigpoly->rechts!=NULL))
            zeigpoly=zeigpoly->rechts;

      while ((zeigpoly!=NULL) && (zeigpoly->grad<=c->exist+anzahl))
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               copyy_monom(zeigmon,&hmon);
               einfuegen_in_reihe(hmon,c);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
   }
   c->exist+=anzahl;
   return OK;
}

static int  transform_reihe(a,n,c,anzahl) REIHE_zeiger a,c; INT n,anzahl;
{
   struct REIHE_poly *zeigpoly;
   struct REIHE_mon* zeigmon, *hmon;
   struct REIHE_variablen *zeigvar;

   if (c->ope=='#') c->ope='t';
   c->reihenart=0L;
   if ((c->x==NULL) && (c->z==0))
   { 
      c->x=a; 
      c->z=n; 
   }
   else if ((c->x!=a) || (c->z!=n))
   { 
      return error("internal error:RH8");
   }

   if (a->exist<c->exist+anzahl) ergaenze_reihe(&a,c->exist+anzahl-a->exist);
   if (a!=NULL)     /* dann ist auch a->infozeig!=NULL wegen initial */
   {
      zeigpoly=a->infozeig;
      if (c->exist!=0)
         while ((zeigpoly->grad<=c->exist) 
               && (zeigpoly->rechts!=NULL))
            zeigpoly=zeigpoly->rechts;

      while ((zeigpoly!=NULL) && (zeigpoly->grad<=c->exist+anzahl))
      {
         if (zeigpoly->unten!=NULL)
         {
            zeigmon=zeigpoly->unten;
            do
            {
               copyy_monom(zeigmon,&hmon);
               if (hmon->zeiger!=NULL)
               {
                  zeigvar=hmon->zeiger;
                  do
                  {
                     zeigvar->index*=n;
                     zeigvar=zeigvar->weiter;
                  }     while (zeigvar!=NULL);
               }
               einfuegen_in_reihe(hmon,c);
               zeigmon=zeigmon->ref;
            }      while (zeigmon!=NULL);
         }
         zeigpoly=zeigpoly->rechts;
      }
   }
   c->exist+=anzahl;
}

INT m_perm_reihe(a) OP a;
/* AK 100393 */
{
   INT erg = OK;
   erg += freeself(a);
   erg += make_reihe(& (S_O_S(a)).ob_reihe,Perm_eingabe);
   erg += ergaenze_reihe(& (S_O_S(a)).ob_reihe,5L);
   C_O_K(a,REIHE);
   ENDR("m_perm_reihe");
}

INT m_cosinus_reihe(a) OP a;
/* AK 100393 */
{
   INT erg = OK;
   erg += freeself(a);
   erg += make_reihe(& (S_O_S(a)).ob_reihe,Cosinus_eingabe);
   erg += ergaenze_reihe(& (S_O_S(a)).ob_reihe,5L);
   C_O_K(a,REIHE);
   ENDR("m_cosinus_reihe");
}

INT random_reihe(a) OP a;
/* AK 030893 */
{
   INT erg = OK;
   if (not EMPTYP(a))
      erg += freeself(a);
   erg += make_reihe(& (S_O_S(a)).ob_reihe,Random_eingabe);
   erg += ergaenze_reihe(& (S_O_S(a)).ob_reihe,5L);
   C_O_K(a,REIHE);
   ENDR("random_reihe");
}

INT m_eins_reihe(a) OP a;
/* AK 100393 */
{
   if (not EMPTYP(a))
      freeself(a);
   make_reihe(& (S_O_S(a)).ob_reihe,Eins_eingabe);
   ergaenze_reihe(& (S_O_S(a)).ob_reihe,5L);
   C_O_K(a,REIHE);
   return OK;
}

INT m_sinus_reihe(a) OP a;
/* AK 100393 */
{
	INT erg = OK;
	if (not EMPTYP(a))
	      erg += freeself(a);
	erg += make_reihe(& (S_O_S(a)).ob_reihe,Sinus_eingabe);
	erg += ergaenze_reihe(& (S_O_S(a)).ob_reihe,5L);
	C_O_K(a,REIHE);
	ENDR("m_sinus_reihe");
}


jh_ausgabe_vorbereiten(f, a, r) REIHE_zeiger* a; FILE *f;
	REIHE_zeiger r[];
/* JH 0293 */
{
   int art,x,y,z;
   char operat,was;

   if (*a==NULL)
   {
      printf("Es existiert noch keine Reihe.\n");
      printf("Permutation.........1\n");
      printf("EMenge..............2\n");
      printf("Exponentialreihe....3\n");
      printf("Skalar..............4\n");
      printf("Sinus...............5\n");
      printf("Cosinus.............6\n");
      printf("Verknuepfungen......0\n");
      printf("Uebergehen.........-1\n");
      printf("\nAuswahl:");
      do
         scanf("%i",&art);
      while ((art<-2) || (art>6));

      if (art!=-1)
      {
         if (art>0)
         {
            switch(art)
            {
            case 1:
               make_reihe(a,Perm_eingabe);
               break;
            case 2:
               make_reihe(a,E_eingabe);
               break;
            case 3:
               make_reihe(a,Exp_eingabe);
               break;
            case 4:
               make_skalar_reihe(a);
               break;
            case 5:
               make_reihe(a,Sinus_eingabe);
               break;
            case 6:
               make_reihe(a,Cosinus_eingabe);
               break;


            }
            ergaenze_reihe(a,zuwachs);
         }
         else /* Verknuepfungen */
         {
            initial_reihe(a);
            printf("\nAddition.............a\n");
            printf("Multiplikation.......m\n");
            printf("Potenzieren..........p\n");
            printf("Ableitung............l\n");
            printf("Transformieren.......t\n");
            printf("Substitution.........s\n");
            printf("\nOperation:");
            do
               operat=getchar();
            while(operat!='a' && operat!='m' &&
                operat!='s' && operat!='p' &&
                operat!='t' && operat!='l');
            switch(operat)
            {
            case 'a':
               printf("\n1.Summand:");
               scanf("%i",&x);
               printf("\n2.Summand:");
               scanf("%i",&y);
               JH_add_reihe(r[x],r[y],*a,zuwachs);
               break;

            case 'm':
               printf("\n1.Faktor:");
               scanf("%i",&x);
               printf("\n2.Faktor:");
               scanf("%i",&y);
               JH_mult_reihe(r[x],r[y],*a,zuwachs);
               break;

            case 'p':
               printf("\nBasisreihe :");
               scanf("%i",&x);
               printf("\nPotenz     :");     
               scanf("%i",&z);
               pot_reihe(r[x],z,*a,zuwachs);
               break;

            case 'l':
               printf("\nBasisreihe             :");
               scanf("%i",&x);
               printf("\nAbleitung nach Variable:");
               scanf("%i",&z);
               ableitung_reihe(r[x],z,*a,zuwachs);
               break;

            case 't':
               printf("\nReihe         :");
               scanf("%i",&x);
               printf("\nTransformation:");
               scanf("%i",&z);
               transform_reihe(r[x],z,*a,zuwachs);
               break;

            case 's':
               printf("\n1.Reihe, in die eingesetzt wird:");
               scanf("%i",&x);
               printf("\n2.Reihe, die eingesetzt wird   :");
               scanf("%i",&y);
               subst_reihe(r[x],r[y],a,zuwachs);
               break;
            }    /* switch */
         }      /* else */
      }        /* if art.. */
      ausgabe(f, *a);
   }          /* if */
   else   /* Reihe ist schon definiert */
   {
      if ((*a)->ope!='#')
         printf(" Operator:%c, \n",(*a)->ope);  /* ursprung angeben */
      else printf("\n");

      printf("Ausgabe + Zuwachs...a   ");
      printf("Loeschen............l   ");
      printf("Ausgabe.............A\n");
      printf("Normalisieren.......n   ");
      printf("Symmetrica-Polynom..s   ");
      printf("Cardinalitaet.......c\n");
      printf("Typ-Cardinalitaet...t\n");

      printf("\nAuswahl:");
      do
         was=getchar();
      while(was!='a' && was!='l' &&
          was!='s' && was!='A' &&
          was!='c' && was!='t' && was!='n');
      if (was=='a') { 
         ergaenze_reihe(a,zuwachs);
         ausgabe(f, *a); 
      }
      if (was=='l') del_reihe(a);
      if (was=='c') card_reihe(*a);
      if (was=='t') card_typ_reihe(*a);
      if (was=='n') normalisiere_reihe(*a);
      if (was=='A') ausgabe(f, *a);
      if (was=='s'){ 
	 OP symd;
	 symd = callocobject();
         reihe_zu_sympolynom(*a,symd);
         fprintln(f, symd); 
	 freeall(symd);
      }
   }
}

INT debugprint_reihe(a) OP a;
{
   debugprint_rh(S_O_S(a).ob_reihe);
   return OK;
}

static int debugprint_rh(a) REIHE_zeiger a;
{
   INT i;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"struct reihe:\n");
   if (a==NULL)
      {
      for (i=0L;i<doffset;i++) fputc(' ',stderr);
      return    fprintf(stderr,"struct reihe==NULL\n");
      }
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"exist = %ld\n",a->exist);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"reihenart = %ld\n",a->reihenart);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"z = %ld\n",a->z);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"x = \n"); 
   doffset += 2L;
   debugprint_rh(a->x);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"y = \n"); 
   doffset += 2L;
   debugprint_rh(a->y);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"p = \n"); 
   doffset += 2L;
   debugprint_rh(a->p);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"ope = %c\n",a->ope);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"infozeig = \n"); 
   doffset += 2L;
   debugprint_rh_poly(a->infozeig);
   doffset -= 2L;
}

static int debugprint_rh_poly(a) struct REIHE_poly *a;
{
   INT i;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"struct reihe_poly:\n");
   if (a==NULL)
      {
      for (i=0L;i<doffset;i++) fputc(' ',stderr);
      return    fprintf(stderr,"struct reihe_poly==NULL\n");
      }
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"grad = %ld\n",a->grad);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"unten = \n"); 
   doffset += 2L;
   debugprint_rh_mon(a->unten);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"rechts = \n"); 
   doffset += 2L;
   debugprint_rh_poly(a->rechts);
   doffset -= 2L;
}
static int debugprint_rh_mon(a) struct REIHE_mon *a;
{
   INT i;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"struct reihe_mon:\n");
   if (a==NULL)
      {
      for (i=0L;i<doffset;i++) fputc(' ',stderr);
      return    fprintf(stderr,"struct reihe_mon==NULL\n");
      }
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"coeff = \n"); 
   doffset += 2L;
   debugprint(a->coeff);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"zeiger = \n"); 
   doffset += 2L;
   debugprint_rh_var(a->zeiger);
   doffset -= 2L;
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"ref = \n"); 
   doffset += 2L;
   debugprint_rh_mon(a->ref);
   doffset -= 2L;
}
static int debugprint_rh_var(a) struct REIHE_variablen *a;
{
   INT i;
   extern INT doffset;

   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"struct reihe_var:\n");
   if (a==NULL)
      {
      for (i=0L;i<doffset;i++) fputc(' ',stderr);
      return    fprintf(stderr,"struct reihe_var==NULL\n");
      }
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"index = %ld\n",a->index);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"potenz = %ld\n",a->potenz);
   for (i=0L;i<doffset;i++) fputc(' ',stderr);
   fprintf(stderr,"weiter = \n"); 
   doffset += 2L;
   debugprint_rh_var(a->weiter);
   doffset -= 2L;
}

INT addinvers_reihe(a,b) OP a,b;
/* AK 020893 */
{
   OP c;
   INT erg = OK;
   c = callocobject();
   erg += m_scalar_reihe(cons_negeins,c);
   erg += mult(a,c,b);
   erg += freeall(c);
   if (erg !=  OK)
      EDC("addinvers_reihe");
   return erg;
}


INT mult_apply_reihe(a,b) OP a,b;
/* AK 150393 */
{
   OP c;
   INT erg = OK;
   c = callocobject();
   erg += copy(b,c);
   erg += mult(a,c,b);
   erg += freeall(c);
   if (erg !=  OK)
      EDC("mult_apply_reihe");
   return erg;
}


static INT Eins_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
{
return co_eingabe (root, anzahl, 1L);
}
static INT Random_eingabe(root, anzahl) REIHE_zeiger root; INT anzahl;
{
return co_eingabe (root, anzahl, 2L);
}

static INT co_eingabe(root, anzahl, para ) REIHE_zeiger root; INT anzahl,para;
/* AK 300793 */
{
   INT i,j,l,k;
   INT erg = OK;
   struct REIHE_mon *zeigmon;
   struct REIHE_variablen *zeigvar,*help_drei;

/*
   b=callocobject();
   d=callocobject();
   f=callocobject();
*/
   if (root->exist==0)
   {
      zeigmon=new_zwei();
      zeigmon->coeff=callocobject();
      zeigmon->zeiger=NULL;
      zeigmon->ref=NULL;
      switch(para) 
      {
      case 1:
         erg += M_I_I(1L,zeigmon->coeff);
         break;
      case 2:
         erg += random_integer(zeigmon->coeff,NULL,NULL);
         break;
      default:
         error("internal error:RH3");
      }
      erg += einfuegen_in_reihe(zeigmon,root);
   }
   for (l=root->exist+1L;l<=root->exist+anzahl;l++)
   {
         zeigmon=new_zwei();
         zeigmon->coeff=callocobject();
         zeigmon->ref=NULL;
      switch(para) 
      {
      case 1:
         erg += M_I_I(1L,zeigmon->coeff);
         break;
      case 2:
         erg += random_integer(zeigmon->coeff,NULL,NULL);
         break;
      default:
         error("internal error:RH4");
      }
      
         help_drei=new_drei();
         help_drei->weiter=NULL;
         zeigmon->zeiger=help_drei;
         zeigvar=help_drei;
         zeigvar->index=0;
         zeigvar->potenz=l;
         erg += einfuegen_in_reihe(zeigmon,root);
   }
   root->exist+=anzahl;   /* erhoehen um anzahl */
/*
   erg += freeall(b);
   erg += freeall(d);
   erg += freeall(f);
*/
   if (erg != OK)
         error("internal error:RH5");
   return erg;
}

static INT t_MONOM_REIHE_mon(a,b) OP a;struct REIHE_mon *b;
{
   INT i;
   struct REIHE_variablen *c;
   b->coeff = callocobject();
   copy(S_MO_K(a),b->coeff);
   c = b->zeiger; /* fuer variablen */
   for (i=0L;i<S_MO_SLI(a);i++)
      {
      if (not nullp(S_MO_SI(a,i)))
         {
         /* ein exponent ungleich NULL */
         if (b->zeiger == NULL)
            {
            b->zeiger = new_var();
            c = b->zeiger;
            }
         else   {
            c->weiter = new_var();
            c = c->weiter;
            }
         }
         c->index = i;
         c->potenz = s_i_i(S_MO_SI(a,i));
      }
   return OK;
}


INT select_degree_reihe(a,b,c) OP a,b,c;
/* AK 030893 */
{
   struct REIHE_poly *info;
   REIHE_zeiger z;
   OBJECTSELF d;
   INT erg = OK;

   if (S_O_K(a) != REIHE)
      {
      erg += WTT("select_degree_reihe",a,b);
      goto sdr_ende;
      }
   if (S_O_K(b) != INTEGER)
      {
      erg += WTT("select_degree_reihe",a,b);
      goto sdr_ende;
      }
   if (S_I_I(b) < 0L)
      {
      erg += ERROR;
      goto sdr_ende;
      }

   init(POLYNOM,c);
   d = S_O_S(a);
   z = d.ob_reihe;

   info = z->infozeig;
   while (info != NULL)
      {
      if (S_I_I(b) == info->grad)
         { 
         erg += poly_zu_sympolynom(info,c);
         goto sdr_ende;
         }
      info = info->rechts;
      }
sdr_ende:
   if (erg != OK)
      EDC("select_degree_reihe");
   return erg;
}

INT select_coeff_reihe(a,b,d) OP a,b,d;
/* AK 020893 */
{
   OP c; 
   INT erg = OK;
   
   if (S_O_K(b) != VECTOR)
      return ERROR;
   if (S_O_K(a) != REIHE)
      return ERROR;
      
   c = callocobject();
   erg += t_REIHE_POLYNOM(a,c);
   erg += select_coeff_polynom(c,b,d);
   erg += freeall(c);
   return erg;
}

INT length_reihe(a,b) OP a,b;
/* AK 251093 */
{
	OP c;
	INT erg = OK;
	c = callocobject();
	erg += t_REIHE_POLYNOM(a,c);
	erg += length(c,b);
	erg += freeall(c);
	if (erg != OK)
		EDC("length_reihe");
	return erg;
}

INT rh_test()
{
   OP a,b,c,d,e,f,g,h,h2,x; 
   INT i,j,i1,j1,l; FILE *fp1,*fp2; 

   a=callocobject(); 
   b=callocobject(); 
   c=callocobject(); d=callocobject(); 
   e=callocobject(); 
   f=callocobject(); 
   g=callocobject(); 
   h=callocobject(); 
   h2=callocobject(); 

   m_sinus_reihe(a);
   copy(a,b); println(a); println(b);
   printf("%d\n",comp(a,b));
   inc(a);inc(a); println(a);
   printf("%d\n",comp(a,b));
   inc(b);inc(b); println(b);
   printf("%d\n",comp(a,b));
   inc(b);inc(b); println(b);
   printf("%d\n",comp(a,b));
   inc(a);inc(a); println(a);
   printf("%d\n",comp(a,b));

   m_iindex_iexponent_monom(0L,3L,c);
   println(c);
   select_coeff_reihe(b,S_PO_S(c),d);
   println(d);

   max_degree_reihe(b,c);
   println(c);

   m_perm_reihe(b);
   max_degree_reihe(b,c);
   println(c);
   inc(b); inc(b); println(b);
   max_degree_reihe(b,c);
   println(c);

   m_eins_reihe(a); println(a);
   add(a,cons_eins,b);
   println(b);

   m_cosinus_reihe(a);
   add_apply(a,b);
   println(b);

   addinvers(b,c);
   println(c);
   add(b,c,a);
   println(a);
   if (not nullp(a))
      error("not null");
   random_reihe(a);
   println(a);
   random_reihe(b);
   println(b);
   add(a,b,c);

   m_perm_reihe(b);
   select_degree_reihe(b,cons_null,d);
   println(d); debugprint(d);
   select_degree_reihe(b,cons_eins,d);
   println(d);
   m_i_i(5L,a);
   select_degree_reihe(b,a,d);
   println(d);

   freeall(a); freeall(b); freeall(c); freeall(d); freeall(e);
   freeall(f);freeall(g);freeall(h);freeall(h2);

}
#endif /* REIHETRUE */
#ifdef  REIHETRUE 
INT scan_reihe(a) OP a;
/* AK 221093 */
{
	int i;
	INT erg = OK;
	printeingabe("input of REIHE object");
	printeingabe("sinus[1]  cosinus[2]  identity[3]");
	printeingabe("perm [4]  random [5]             ");
	scanf("%d",&i);
	switch(i)
		{
		case 1: erg += m_sinus_reihe(a); break;
		case 2: erg += m_cosinus_reihe(a); break;
		case 3: erg += m_eins_reihe(a); break;
		case 4: erg += m_perm_reihe(a); break;
		case 5: erg += random_reihe(a); break;
		default: erg += ERROR;
		}
	if (erg != OK)
		EDC("scan_reihe");
	return erg;
}
#endif /* REIHETRUE */
