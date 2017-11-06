/* SYMMETRICA file plet.c */
#include "def.h"
#include "macro.h"

/* CC 240197 */


#ifdef PLETTRUE


#ifdef DGUX
#define signed
#endif  /* DGUX */

#ifdef      sun
#define signed
#endif  /*sun */
#ifdef       hpux
#define signed
#endif 

static INT cmp();
static INT ins_sch_lst();
static INT ins_sc_lst();
/* static INT ins_s_lst(); */
static INT cjg_rv();
static INT cjg_rv_lst();
static INT pl_schur_schur();
static struct liste * proprt();
static INT fct_sch_prt_srt();
static struct liste * pro_lg();
static INT fct_sch_lg_srt();
static INT poids();
static INT free_lst();
static INT free_newton();
static INT shuffle_sig();
/* static INT shuffle_sg(); */
static INT detr();
static INT plth1();
static INT plth2();
static INT plth3();
static INT plth4();
static INT plth5();
static INT cc_plethysm();
static INT calcul();
static INT calcula();
static INT calculi();
static INT operer();
static INT plet_conj();
static INT conjug();
static INT t_list_SYM();
static INT conjugate_apply_schur();
static INT t_list_coef_SYM();



struct  liste {
     INT  coef;
     signed char  *tab;
     struct  liste  *suivant;
         };

struct monomial{
   int degree;
   unsigned indice;
   struct liste *resultat;
   struct monomial *suivant;
   };

/*
struct cel{
        struct cel *prec;
        struct cel *suiv;
        signed char *tab;
        long coef;
};
*/
/*
struct lst{
        struct cel *deb;
};
*/

signed char gv,booo,gvr,lng;
/**/
void voirbuf(bs) register char *bs;
{
    while(*bs)
    {
        printf("%d ",*bs);
        bs++;
    }
}
/**/
/*
prints the double linked list
*/

#ifdef UNDEF
static void voirlst(plst) struct cel *plst;
{
    while(plst!=NULL)
    {
        printf("%ld(",plst->coef);
        voirbuf(plst->tab);
        printf(")\n");
        plst=plst->suiv;
    }
}

static void voirliste(plst) struct liste *plst;
{
    while(plst!=NULL)
    {
        printf("%ld(",plst->coef);
        voirbuf(plst->tab);
        printf(")\n");
        plst=plst->suivant;
    }
}
#endif

static INT cmp(a,b) OP a,b;
{
    OP as=S_MO_S(a);
    OP bs=S_MO_S(b);

    INT i=S_PA_LI(as)-1L;
    INT j=S_PA_LI(bs)-1L;

    for(;i>=0L && j>= 0L;i--,j--)
    {
        if(S_PA_II(as,i) > S_PA_II(bs,j))
            return -1L;
        if(S_PA_II(as,i) < S_PA_II(bs,j))
            return 1L;
    }
    return 0L;
}

INT plethysm(a,b,c) OP a,b,c;
/* AK 180299 */
/*
    input object a
        may be SCHUR, MONOMIAL, ...
    input object b
        may be SCHUR, MONOMIAL, ...
    output object c
        the plethysm  a[b] in the basis of b
*/
{
    INT erg = OK;
    CE3(a,b,c,plethysm);
    if ((S_O_K(a) == SCHUR) && (S_O_K(b) == MONOMIAL))
        {
        erg += plethysm_schur_monomial(a,b,c);
        }
    else if ((S_O_K(a) == SCHUR) && (S_O_K(b) == SCHUR))
                {
                erg += plethysm_schur_schur(a,b,c);
                }
    else {
        erg += WTT("plethysm",a,b);
        }
    ENDR("plethysm");
}

/*
takes a partition, its maximal indice and  conjugates it 
1 1 2, 2 gives  1 3, 1
*/

static INT plet_conj(pt,pj) signed char **pt,*pj;
{
  signed char *btab,*af,*baf,j;
  signed char mid,temp,high,i;

  j= *pj;
  btab = *pt+j;
  mid = *btab;*pj=mid;
  af=(signed char *)SYM_MALLOC(mid+1);
  *(af+mid)=0;
  baf=af;  j++;
  temp = 0;
  while(j >=  0)
  {
    high = 0;
    while(*btab == mid)
    {
      j--;
      high++;
      if(j == 0)
      {
        j--;
        break;
      }
      btab--;
    }
    temp = temp+high;
    if(j == -1)
    {
      for(i=0;i<mid-1;i++)
        *baf++ =temp;
      *baf=temp;
    }
    else
    {
      for(i= *btab;i<mid;i++)
        *baf++ = temp;
      mid= *btab;
    }
  }
  SYM_free(*pt);
  *pt=af;
  return OK;
}


/*takes a partition its length and  conjugates it */

static INT conjug(tab,j,ve)
/* tab is a partition j its length */
    signed char *tab; signed char j; OP  ve;
{
  signed char *btab;
  signed char mid,temp,high,i,k;

  btab = tab+j;
  mid = *btab;
  m_il_v( (INT) mid,ve);
  k = (signed char) 0;
  j++;
  temp = 0;
  while(j >=  (signed char) 0)
  {
    high = 0;
    while(*btab == mid)
    {
      j--;
      high++;
      if(j == 0)
      {
        j--;
        break;
      }
      btab--;
    }
    temp = temp+high;
    if(j == -1)
      i = 0;
    else
      i = *btab;
    for(;i < mid;i++)
    {
      M_I_I( (INT)temp , S_V_I( ve,(INT)k ) );
      k++;
    }
    mid = *btab;
  }
    return OK;
}

int SYM_strlen();


static INT operer(n,ttp,deg,baf,cof,liste,parite)
    signed char n,ttp,deg,*baf,parite;
    struct liste *liste;
    INT cof;

{
  signed char np,cond=0,si,v,tv,k,tp,var,first;
  register signed char j,jn,temp;
  signed char *s,*init,*tabn,*st,*af,*bs,*binit,*btabn,*bab,*bobo;
  static struct liste *liste3p;
  struct liste *liste1,*liste2=NULL,*liste3;
  static signed char obo[128];


/* The succesive "buf" which come are ordered; The search in "liste" begins
 at its first pointed element if buf is the first pointed element of
 "bp" in calcul (gv = 0) or begins in at the element pointed by liste3p if
 not */

  first = (signed char)0;
  if(gv == 0)
  {
    liste3 = liste;
    gv = 1;
  }
  else
    liste3 = liste3p;
  si = sizeof(struct liste);

  /*j is the length of baf; instead of this: strlen(baf)*/

  j = 0;
  bab = baf;
  while(*baf != '\0')
  {
    baf++;
    j++;
  }
  /*The maximal length of the new terms will be less than or equal to np;
    tmp is a useful variable giving the difference of length*/

  tp = ttp - j;
  np = j + (deg * n);

  /*Allocation of four different tableaux*/

  s = (signed char *)SYM_MALLOC(np + 1);
  init = (signed char *)SYM_MALLOC(np + 1);
  af = (signed char *)SYM_MALLOC(np + 1);
  tabn = (signed char *)SYM_MALLOC(deg + 1);

  /*Init is the initial Schur function we want multiply by the monomial
  function indexed by n*/

  binit = init;
  for(jn = 0;jn < np - j;jn++)
    *binit++ =  jn + tp;
  baf = bab;
  for(jn = 0;jn < j;jn++)
    *binit++ =  *baf++ + (deg * n);
  *binit = 0;

  /* s is the tableau result of the product; tab is the tableau giving the
  position of the parts which are incremented*/

  temp = np - 1;

  if(booo == 1)
  {
    binit = init + temp;
    first = 1;
    for(jn = temp; jn >= 0; jn--)
    {
      if(((*binit) + n - tp - temp) <= lng)
        break;
      if(jn != 0)
        binit--;
    }
    binit = init;
    bs = s;
    for(temp = 0; temp <= jn - deg;temp++)
      *bs++ = *binit++;
    for(;temp < jn;temp++)
      *bs++ = *binit++ + n;
    for(; temp < np;temp++)
      *bs++ = *binit++;
    *(tabn + deg - 1) = jn + 1;
    if(j < deg)
      j = deg;
    tp = j;
    var = deg - 1;
    goto et1;
  }
  else
  {
    jn = np - deg;
    binit = init + jn;
    baf = tabn;
    bs = s + jn;

    for(;jn <=  temp;jn++)
    {
      *baf++ =  jn;
      *bs++ =  *binit++ + n;
    }
    *baf = 0;
    *bs = 0;
    bs = s;
    binit = init;
    for(jn = 0;jn < np - deg;jn++)
      *bs++ =  *binit++;
    if(j < deg)
      j = deg;
    tp = j;
    liste2 = liste3->suivant;
    if(liste2 != NULL)
    {

  /*The Schur function result of the product must be put in a structure liste
  which is not empty. The real result is st which is an offset of s*/

      st = (signed char *)SYM_MALLOC(j + 1);
      baf = st;
      temp = np - j;
      bs = s + temp;
      for(jn = temp;jn < np;jn++)
        *baf++ = *bs++ ;
      *baf = 0;

      while(liste2 != NULL)
      {

      /*Is the Schur function in liste? As the cofactor is ordered, the result
      must not be very far in the liste*/

        /* Position on the last part of the partition for the liste: bab
        for the result:bs*/

        temp = -1;
        bab = liste2->tab;
        while(*bab != '\0')
        {
          bab++;
          temp++;
        }

      cond = 0;
      bab = (liste2->tab) + temp;

      bs = st + j - 1;

      /* The comparaison*/

      for(jn = temp;jn >=  0;jn--)
      {
        if(*bs < *bab)
        {
          cond = -1;
          break;
        }
        else if(*bs > *bab)
        {
          cond = 1;
          break;
        }
        bs--;
        bab--;
      }

      /*The result of the comparaison*/

      if(cond > 0)

      /*Stop of the comparaison for insertion*/

        break;

      else if(cond == 0)
      {
      /*The Schur function is already in the liste*/

        liste2->coef += (cof * parite);

        if(liste2->coef == 0L)
        {
        /*the coefficient of the Schur function is null: Supression*/

          liste1 = liste2->suivant;
          SYM_free(liste2->tab);
          SYM_free((signed char *)liste2);
          liste3->suivant = liste1;
          liste2 = liste1;
        }
        else
        {
          liste3 = liste2;
          liste2 = liste2->suivant;
        }
        SYM_free(st);
        /*the comparaison is ended*/

        break;
      }

     /*End of if cond == 0*/

      else
      {
      /*In this case the comparaison go on*/

        liste3 = liste2;
        liste2 = liste2->suivant;
      }
    }

    /*End of while liste2 != NULL*/

    if (cond != 0)
    {
    /*Insertion*/

      liste1 = (struct liste *)SYM_MALLOC(si);
      liste1->tab = st;
      liste1->suivant = liste2;
      liste1->coef = cof * parite;
      liste3->suivant = liste1;
      liste3 = liste1;
    }

    /*The first product from the next cofactor will be after the product st
    in the pointed liste*/

    liste3p = liste3;

    /* Muir's algorithm starts trying to add n to the part indexed by
    tabn[0]-1*/

    *tabn -= 1;
    s[np - deg] = s[np - deg] - n;

    for(;;)
    {
      while((v = tabn[0]) >=  0)
      {
      /*To try to add the leftest part n of the monomial function*/

        if(((np - v) > lng) && (booo == 0))
        /*If the result has its length bigger than lng, go out the loop*/

          break;
        tv = s[v] + n;
        for(jn= v+1;jn< np;jn++)
          if(tv == s[jn])
          /*If two parts are equal, try to put n to another place*/

            break;
        if(jn == np)
        {
        /*Build the vector result in af; af is not ordered*/

          baf = af;
          bs = s;
          for(jn= 0;jn< v;jn++)
            *baf++ =  *bs++;
          *baf++ =  tv;
          bs++;
          for(jn= v+1;jn< np;jn++)
            *baf++ =  *bs++;
          *baf = '\0';

          /*We reorder the vector into a partition*/

          tv = parite;


          for(k = n /2;k > 0;k /= 2)

            for(jn = k;jn< np;jn++)

              for(j = jn-k;((j >=  0) && (af[j] > af[j+k]));j -= k)
              {
                tv = -tv;
                temp = af[j];
                af[j] = af[j+k];
                af[j+k] = temp;
              }
          /*j is the length of the partition less one; v is np-v i.e.
          the number of parts which are null*/

          if(tp < np - v)
            j = np - v - 1;
          else
          {
            v = np - tp;
            j = tp - 1;
          }

            if(first == 1)
            {
              if(gvr == 0)
              {
                gvr = 1;
                liste3 = liste;
              }
              else
              {
                temp = SYM_strlen(obo);
                bobo = obo + (temp - 1);
                baf = af + np - 1;
                if(np < temp)
                  temp = np;
                for(;temp > 1; temp--)
                {
                  if(*bobo > *baf)
                  {
                    liste3 = liste3p;
                    break;
                  }
                  else if(*bobo < *baf)
                  {
                    liste3 = liste;
                    break;
                  }
                  bobo--;
                  baf--;
                }
                if (temp == 1)
                {
                  if(*bobo > *baf)
                    liste3 = liste3p;
                  else
                    liste3 = liste;
                }
/* CC 1/3/97
                SYM_free(obo);
*/
              }
              temp = j + 1;
/* CC 1/3/97
              obo = (signed char *)SYM_MALLOC(temp + 1);
*/
              bobo = obo;
              baf = af + v;
              for(jn = 0;jn < temp;jn++)
                *bobo++ = *baf++;
              *bobo = 0;

              liste2 = liste3->suivant;

            }

          /*It is the same search than before: is the Schur function af in
          the liste*/

          if (liste2 == NULL)
            cond = 1;

          while(liste2 != NULL)
          {
            temp = -1;
            bab = liste2->tab;
            while(*bab != '\0')
            {
              bab++;
              temp++;
            }
            bab = (liste2->tab) + temp;

            baf = af + np - 1;

            cond = 0;

            if(temp > j)
              temp = j;

            for(jn = temp;jn>=  0;jn--)
            {
            /*Comparaison*/

              if(*baf < *bab)
              {
                 cond = -1;
                 break;
              }
              else if(*baf > *bab)
              {
                cond = 1;
                break;
              }
              baf--;
              bab--;
            }
            if(cond > 0)
              break;
            else if(cond == 0)
            {
              if(tv == -1)
                liste2->coef -= cof;
              else
                liste2->coef += cof;

              if(liste2->coef == 0L)
              {
                liste1 = liste2->suivant;
                SYM_free(liste2->tab);
                SYM_free((signed char *)liste2);
                liste3->suivant = liste1;
                liste2 = liste1;
              }
              else
              {
                liste3 = liste2;
                liste2 = liste2->suivant;
              }

              break;
            }

         /*End  of if cond == 0*/

            else
            {
              liste3 = liste2;
              liste2 = liste2->suivant;
            }
          }

          /*End of while liste2 == NULL*/

          if (cond != 0)
          {
          /*Insertion*/

            liste1 = (struct liste *)SYM_MALLOC(si);
            liste3->suivant = liste1;
            j++;

            /*The Schur function is put in the liste*/

            bab = (signed char *)SYM_MALLOC(j+1);
            liste1->tab = bab;
            baf = af + v;
            for(jn= 0;jn< j;jn++)
              *bab++ =  *baf++;
            *bab = '\0';
            liste1->coef = tv * cof;
            liste1->suivant = liste2;
            liste3 = liste1;
          }

          /*End of cond != 0*/
        if(first == 1)
        {
          first = 0;
          liste3p = liste3;
        }

        }
        /*End of jn == np*/

        tabn[0]--;
      }
      /*End of the while tabn[0]>= 0*/
      var = 1;
et1:      for(jn= var;jn< deg;jn++)
      {
      /*To put all the indexes of the monomial function except the
      leftest one*/

        bab = tabn + jn;
        if((v = *bab ) != jn)
        {
        /*Shift left still the jn index of the monomial function which is
        at the position v*/

          binit = init + v;
          baf = s + v;
          *baf = *binit;
          for(j = jn;j >=  0;j--)

          /*Try to put the index j of the monomial function*/

            for(;;)
            {
              v--;
              binit--;
              baf--;
              if((j > v) || ((booo == 0) && ((np + j - v) > lng)))

              /*It is impossible to put the jn leftest indexes of the monomial
               function; try to put more than jn indexes*/

                goto boucle1;
              else
              {
              /*Shift*/

                tv = *binit + n;
                if(np <= v + n)
                  temp = np;
                else
                  temp = v + n + 1;
                bs = s + v;
                for(k = v+1;k < temp;k++)
                {
                  bs++;
                  if(tv == *bs)
                  {
                  /*Impossible to shift the index j at position v:
                   try to put at v-1*/

                    *baf = *binit;
                    break;
                  }
                }
                if(k == temp)
                {
                /*Succeed in shifting*/

                  *bab-- = v;
                  *baf = *binit + n;
                  break;
                }
              }
            }
          /*After succeeding  in shifting, build a new tableau s*/

          bs = s;
          binit = init;
          for(k = 0;k <=  v;k++)
            *bs++ =  *binit++;
          break;
        }
        boucle1: ;
      }
      if(jn== deg)
        break;
    }
    /*End of the loop for(;;) corresponding to Muir's algorithm*/
  }
  else
  {
  /*It seems to the preceeding loop except that there is not ordering*/

    liste2 = (struct liste *)SYM_MALLOC(si);
    liste3->suivant = liste2;
    liste2->suivant = NULL;
    liste2->coef = cof * parite;
    bs = s + (np - j);
    bab = (signed char *)SYM_MALLOC(j + 1);
    liste2->tab = bab;
    for(jn = 0;jn < j;jn++)
      *bab++ = *bs++;
    *bab = 0;
    liste3 = liste2;
    liste2 = NULL;
    liste3p = liste3;

    tabn[0]--;
    s[np - deg] = s[np - deg] - n;

    for(;;)
    {
      while((v = tabn[0]) >=  0)
      {
        if(((np - v) > lng) && (booo == 0))
          break;
        tv = s[v] + n;
        for(jn = v + 1;jn < np;jn++)
          if(tv == s[jn])
            break;
          if(jn == np)
          {
            baf = af;
            bs = s;
            for(jn = 0;jn < v;jn++)
              *baf++ = *bs++;
            *baf++ =  tv;
            bs++;
            for(jn = v+1;jn < np;jn++)
              *baf++ =  *bs++;
            *baf = '\0';
            tv = parite;

            for(k = n /2;k > 0;k /= 2)

              for(jn = k;jn < np;jn++)

                for(j = jn-k;((j >=  0) && (af[j] > af[j+k]));j -= k)
                {
                  tv = -tv;
                  temp = af[j];
                  af[j] = af[j+k];
                  af[j+k] = temp;
                }
            liste2 = (struct liste *)SYM_MALLOC(si);
            if(tp < np - v)
              j = np - v;
            else
            {
              v = np - tp;
              j = tp;
            }

            baf = af + v;
            btabn = (signed char *)SYM_MALLOC(j + 1);

            liste2->tab = btabn;
            while(*baf != '\0')
              *btabn++ =  *baf++;
            *btabn = '\0';
            if(first == 1)
            {
              first = 0;
              liste3p = liste3;
            }
            liste2->coef = tv * cof;
            liste2->suivant = NULL;
            liste3->suivant = liste2;
            liste3 = liste2;

          }
        tabn[0]--;
      }
      for(jn = 1;jn < deg;jn++)
      {
      /*It is the same loop that in the case liste2!= NULL*/

        btabn = tabn + jn;
        if((v = *btabn) != jn)
        {
          binit = init + v;
          baf = s + v;
          *baf = *binit;
          for(j = jn;j >=  0;j--)

            for(;;)
            {
              v--;
              binit--;
              baf--;
              if((j > v) || ((booo == 0) && ((np + j - v) > lng)))
                goto boucle2;
              else
              {
                tv = *binit + n;
                if ( np <= v + n )
                  temp = np;
                else
                  temp = v + n + 1;
                bs = s + v;
                for(k = v+1;k < temp;k++)
                {
                  bs++;
                  if(tv == *bs)
                  {
                    *baf = *binit;
                    break;
                  }
                }
                if(k == temp)
                {
                  *btabn-- = v;
                  *baf = *binit+n;
                  break;
                }
              }
            }
          bs = s;
          binit = init;
          for(k = 0;k <=  v;k++)
            *bs++ =  *binit++;
          break;
        }
        boucle2: ;
      }
      if(jn == deg)
        break;
    }
  }
  }
  SYM_free(s); SYM_free(tabn); SYM_free(af); SYM_free(init);
  return OK;
}



static INT calcul(tab,n,ch,dep,cofe,parite,cond4)
    signed char *tab,*ch,parite,cond4;
    int n;
    INT cofe;
    struct liste *dep;

/*calcul makes the product of the Schur function "ch" by the plethysm
L"tab" J"n" ; the final determinant is in dep
cond4==n && lg(tab)==1 => dep->suivant==NULL*/

{
  signed char mx,boo,boo1,boo2,*btab;
  register int i,j,k;
  INT cof;
    int deg,np; /* from signed int AK 210199 */
  signed char in,jn,v,tv,ttp,tp,tp1=0,var,first;
  signed char si,sim,max;
  signed char *binit,*bs,*s,*init,*tabn,*btabn,*baf,*af;
  signed char lg;
  unsigned vr,av,bvr,tvr,ttvr,tttvr,atvr;
  struct liste *liste,*liste2=NULL,*liste3,*bp;
  struct monomial stmn,*mn,stmn1,*mn1,*bmn=NULL;

  /* lg is the length of the partition tab (strlen(tab))*/

  btab = tab;
  first = 0;
  lg = 0;
  while(*btab != 0)
  {
    btab++;
    lg++;
  }

  /* max (resp. deg) is the weight (resp. length) of the partition ch*/

  max = 0;
  deg = 0;
  btab = ch;
  while(*btab != 0)
  {
    deg++;
    max += *btab++;
  }
  btab = tab;
  mx = *btab;
/*
printf("n %d cond4 %d lg %d booo %d\n",n,cond4,lg,booo);
*/
  if((n != cond4) && (lg == 1))
  {
    gv = 0;

    btab = ch;
    i = max - deg;
    while(*btab != 0)
    {
      *btab += i;
      btab++;
      i++;
    }
    operer(n,max,mx,ch,cofe,dep,parite);
  }
  else
  {
    /*In the stucture monomial, there are the different determinants of order i,
    i between 1 and lg determinants taken on the i first columns*/

    mn = &stmn;
    mn->suivant = NULL;
    si = sizeof(struct liste);
    sim = sizeof(struct monomial);
    vr = 1;

    if(lg != 1)
      boo = 1;
    else
      boo = parite;
    for(k = mx;((k > mx - lg) && (k > 0));k--)
    {
    /*The calculus of all the determinants of the first column, except may be
    the product of the plethysm L0Jn (=1) by ch.*/

      if(lg != 1)

      /*The determinant is of order bigger than 1: the is put in a liste*/

        liste = (struct liste *)SYM_MALLOC(si);
      else

      /*The determinant is of order 1: the result is returned in dep, argument
      of the function calcul*/

        liste = dep;

      /*The program in the loop "for(k = mx;((k > mx - lg) && (k > 0));k--)"
       is the Muir's formula to compute the determinants in the first column:
       see this algorithm in operer*/

      liste->suivant = NULL;
      np = (n * k) + deg;
      tp1 = max - deg;

      s = (signed char *)SYM_MALLOC(np + 1);
      init = (signed char *)SYM_MALLOC(np + 1);
      af = (signed char *)SYM_MALLOC(np + 1);
      tabn = (signed char *)SYM_MALLOC(k + 1);

      baf = ch;
      binit = init;
      for(in = 0;in < np - deg;in++)
          *binit++ = in + tp1;
      for(;in < np ;in++)
        *binit++ = *baf++ + in + tp1;
      *binit = 0;
      if(booo == 1)
      {
        first = 1;
        binit = init + np - 1;
        for(i = np - 1; i >= 0; i--)
        {
          if(((*binit) + n - tp1 - np ) < lng)
            break;
          if(i != 0)
            binit--;
        }
        bs = s;
        binit = init;
        for(jn = 0; jn <= i-k;jn++)
          *bs++ = *binit++;
        for(;jn < i;jn++)
          *bs++ = *binit++ + n;
        for(; jn < np;jn++)
          *bs++ = *binit++;
        *(tabn + k - 1) = i + 1;
        j = deg;
        if(j < k)
          j = k;
        var = k - 1;
        goto et3;
      }
      else
      {
        bs = s ;
        binit = init;
        btabn = tabn;
        for(in = 0;in < np - k; in ++)
          *bs++ = *binit++;
        for(; in < np; in++)
        {
          *bs++ = *binit++ + n;
          *btabn++ = in;
        }
        *btabn = 0;
        *bs = 0;

        j = deg;
        if(j < k)
          j = k;

        liste2 = (struct liste*)SYM_MALLOC(si);
        if(lg != 1)
          liste2->coef = 1L;
        else
          liste2->coef = boo * cofe;
        bs = s + (np - j);
        btabn = (signed char *)SYM_MALLOC(j + 1);
        liste2->tab = btabn;
        while(*bs != 0)
          *btabn++ =  *bs++ ;
        *btabn = '\0';
        liste2->suivant = NULL;
        liste->suivant = liste2;

        tabn[0]--;
        s[np - k] = s[np - k] - n;

        for(;;)
        {
          while((v = tabn[0]) >=  0)
          {
            if(((np - v) > lng) && (booo == 0))
              break;
            tv = s[v] + n;
            for(in = v+1;in < np;in++)
              if(tv == s[in])
                break;
            if(in == np)
            {

              baf = af;
              bs = s;
              for(in = 0;in < v;in++)
                *baf++ = *bs++;
              bs = s + v + 1;
              *baf++ =  tv;
              for(in = v+1;in < np;in++)
                *baf++ =  *bs++;
              *baf = '\0';
              tv = boo;

              for(i = n /2;i > 0;i /= 2)

                for(in = i;in < np;in++)

                  for(jn = in-i;((jn >=  0) && (af[jn] > af[jn+i]));jn -= i)

                  {
                    tv = -tv;
                    ttp = af[jn];
                    af[jn] = af[jn+i];
                    af[jn+i] = ttp;
                  }


              bp = (struct liste *)SYM_MALLOC(si);
              if(j < np - v)
               jn = np - v;
              else
              {
                v = np - j;
                jn = j;
              }

              btabn = (signed char *) SYM_MALLOC(jn + 1);
              bp->tab = btabn;
              baf = af + v;
              while(*baf != 0)
                *btabn++ = *baf++;

              *btabn = '\0';
              if(lg != 1)
                bp->coef = tv;
              else
                bp->coef = tv * cofe;
              bp->suivant = NULL;
              if(first == 1)
              {
                first = 0;
                liste2 = liste;
              }
              liste2->suivant = bp;
              liste2 = bp;

            }
            tabn[0]--;
          }
          var = 1;
et3:

        for(in = var;in < k;in++)
        {
          btabn = tabn + in;
          if((v = *btabn) != in)
          {
            binit = init + v;
            baf = s + v;
            *baf = *binit;
            for(jn = in;jn >=  0;jn--)

              for(;;)
              {
                v--;
                binit--;
                baf--;
                if((jn > v) || ((booo == 0) && ((np + jn - v) > lng)))
                  goto boucle;
                else
                {
                  tv = *binit+n;
                  if ( np <= v + n )
                    ttp = np;
                  else
                    ttp = v + n + 1;
                  bs = s + v;
                  for(i = v+1;i < ttp;i++)
                  {
                    bs++;
                    if(tv == *bs)
                    {
                      *baf = *binit;
                      break;
                    }
                  }
                  if(i == ttp)
                  {
                    *btabn-- = v;
                    *baf = *binit+n;
                    break;
                  }
                }
              }
            bs = s;
            binit = init;
            for(i = 0;i <=  v;i++)
              *bs++ =  *binit++;
            break;
          }
          boucle: ;
        }
        if(in == k)
          break;
      }
    }
    SYM_free(s); SYM_free(tabn); SYM_free(af); SYM_free(init);
    if (lg != 1)
    {
    /*The option is bigger than 0: if the final determinant is not of
    order 1, write the different partial results in the pointed liste of
    type struct monomial: stmn*/

      mn->suivant = (struct monomial *)SYM_MALLOC(sim);
      mn = mn->suivant;
      mn->resultat = liste;

      /*The record indice is used to recognize the different determinants*/

      mn->indice = vr;
      vr = vr << 1;
      mn->degree = k;
      mn->suivant = NULL;
    }

  }
  /*End of the loop for(k = mx;((k > mx - lg) && (k > 0));k--)*/

  if((k == 0) && (k != mx - lg))
  {
  /*To put a determinant of value the partition ch*/

    if(lg != 1)

    /*Not final liste*/

      liste = (struct liste *)SYM_MALLOC(si);
    else

    /*Final liste*/

      liste = dep;
    liste2 = (struct liste *)SYM_MALLOC(si);
    liste->suivant = liste2;

    /*Write the coefficient*/

    if(lg != 1)
      liste2->coef = 1L;
    else
      liste2->coef = boo * cofe;

    /*write the partition*/

    baf = (signed char *)SYM_MALLOC(deg + 1);
    liste2->tab = baf;
    bs = ch;
    for(i = max - deg;i < max ;i++)
      *baf++ = *bs++ + i ;
    *baf = 0;
    liste2->suivant = NULL;

    if(lg != 1)
    {
      mn->suivant = (struct monomial *)SYM_MALLOC(sim);
      mn = mn->suivant;
      mn->resultat = liste;
      mn->indice = vr;
      mn->degree = 0;
      mn->suivant = NULL;
    }

  }
  boo = 1;
  if(lg != 1)
  {
  /*The determinant is of order bigger than 0*/

    vr = 1;
    av = (1 << (lg - 1));

    for(i = 1;i < lg;i++)
    {
    /*The algorithm progresses with columns i+1*/

    /*The option is bigger than i: we will write in the structure monomial*/

      if(boo == 1)
      {
      /*The preceeding determinants (of order i ) are in stmn;
       put the determinants ( of order i+1) we are going to compute
       in stmn1*/

        mn = stmn.suivant;
        mn1 = &stmn1;
      }
      else
      {
      /*The preceeding determinants (of order i ) are in stmn1;
       put the determinants ( of order i+1) we are going to compute
       in stmn*/

        mn = stmn1.suivant;
        mn1 = &stmn;
      }
      mn1->suivant = NULL;

      /*All the variables of type unsigned is used to enumerate
      the determinants: for example the determinants of order 2 have
      for indices the characters 00000011, 00000101, 00001001, ...
      where the position of 1 are the rows of the cofactor*/

      av = av | (1 << (lg - i - 1));
      vr = (1 << i) | vr;

      /*vr will be the index of the first determinant of order i+1 we
      compute; for example for the determinants of order 3, vr is 111*/

      tvr = vr;

      btab++;
      mx = *btab;

      for(;;)
      {
      /*CALCUL of the determinant of index tvr*/

        tp = -1;

        if(i != lg - 1)
        {
        /*Not final liste*/

          liste = (struct liste *)SYM_MALLOC(si);
          liste->suivant = NULL;
        }
        else
        /*Final liste*/

          liste = dep;

        boo1 = 0;
        boo2 = 0;
        tv = -1;

        for(in = lg - 1;in >= 0;in--)
        {
        /*Consider the factor which is in the row in + 1, and on the columns
        i + 1*/

          if(tp == i)

          /*The computation of the determinant indexed by tvr is finished*/

            break;
          ttvr = tvr;
          if(((ttvr >> in) & 1) == 0)

          /*The factor is not used in the computation of the determinant indexed
          by tvr*/

            continue;
          ttvr = (1 << in) ^ tvr;
          tp++;
          deg = mx + i - in;
          if(deg < 0)

          /*The factor is null*/

            continue;
          if((deg > lng) && (booo == 0))
            break;

          else
          {
            tv = -tv;
            if(deg == 0)
            {
            /*The factor is equal to 1*/

            /*Read the cofactor from the monomial structure mn*/

              bmn = mn;
              while(bmn != NULL)
              {
                /*Search of the cofactor*/

                if(bmn->indice == ttvr)
                  break;
                bmn = bmn->suivant;
              }
              if(bmn == NULL)

                /*The cofactor is null; it will be the same for the cofactor
                not yet considered: break */

                break;
              boo1 = 1;
              if(boo2 == 0)
              {
              /*the product 'tp1*n' will be the weight of the Schur function
              indexed by tvr*/

                boo2 = 1;
                tp1 = bmn->degree;
              }
              bp = (bmn->resultat)->suivant;

              liste3 = liste;
              liste2 = liste3->suivant;

              while( bp!= NULL)
              {
              /*Copy in liste the cofactor (the factor is equal to one);
               at the beginning liste2 is null; moreover the cofactor is
               already ordered: it is just a copy*/

                liste2 = (struct liste *)SYM_MALLOC(si);
                baf = bp->tab;
                j = 0;
                while(*baf != 0)
                {
                  baf++;
                  j++;
                }
                bs = (signed char *)SYM_MALLOC(j+1);

                /*Write the partition*/

                baf = bp->tab;
                liste2->tab = bs;
                while(*baf != 0)
                  *bs++ = *baf++;
                *bs = 0;

                /*Write the coefficient*/

                liste2->coef = bp->coef * tv;

                liste2->suivant = NULL;
                liste3->suivant = liste2;
                liste3 = liste2;
                bp = bp->suivant;

              }
            }
            /*End of the if deg == 0*/
            else
            {
              gvr = 0;

            /*It is the product by the monomial function indexed by deg and
            its cofactor indexed by ttvr*/


            /* The preceeding result is in the monomial structure bmn*/

              if(boo1 == 1)
              {

              /* The calculus of a determinant has already begun*/

                bmn = bmn->suivant;
              }
              else
              {
                bmn = mn;
              }
              while(bmn != NULL)
              {

              /* It is the search of the cofactor of the monomial indexed
               by deg*/

                if(bmn->indice == ttvr)
                  break;
                bmn = bmn->suivant;
              }
              if(bmn == NULL)

              /*The cofactor is null*/

                break;

              /*The cofactor is not null; boo1 signals that for the next
               step in the calculus of the determinant a product factor
               by cofactor different from 0 has already been*/

              boo1 = 1;
              if(boo2 == 0)
              {

              /* In the first product (boo2 == 0), '(tp1*n)+max', where max
              is the weight of the second partition entered, is the weight
              of the Schur function we are computing*/

                boo2 = 1;
                tp1 = bmn->degree + deg;
              }

              /* bp is the cofactor*/

              bp = (bmn->resultat)->suivant;

              /*ttp is the degree maxi of the cofactor np1 is the degree
              of the product*/

              ttp = (bmn->degree * n) + max;

              /*gv is a global variable to indicate to operer that the
              product begins*/

              gv = 0;

              while(bp != NULL)
              {

              /* operer which makes the product is called for each term
              of the cofactor*/

                cof = bp->coef * tv;
                if(i == lg - 1)
                {
                  cof = cof * cofe;
                  j = parite;
                }
                else
                  j = 1;
                operer(n,ttp,deg,bp->tab,cof,liste,j);
                bp = bp->suivant;
              }

            }
            /*End of deg > 0*/
          }
          /*End of a product factor by cofactor*/
        }
        /*End of the computation of the determinant indexed by tvr*/

        if(liste->suivant == NULL)
          SYM_free((signed char *)liste);
        else
        {
          if( i != lg - 1)
          {
          /*i < opt: do not use the files; i!=lg-1: put the liste in the
          structure pointed by mn1*/

            bmn = (struct monomial *)SYM_MALLOC(sim);
            mn1->suivant = bmn;
            mn1 = bmn;
            mn1->suivant = NULL;
            mn1->indice = tvr;
            mn1->degree = tp1;
            mn1->resultat = liste;
          }

        }
        if(av == tvr)

        /*The computation of the determinants of order i+1 is finished: break*/

          break;

        /*tvr will be the index of the next determinant: for example for
        lg+1 = 4,and i+1 = 2, the order for the indexes is the following:
        0011,0101,0110,1001,1010,1100*/

        ttvr = tvr;
        atvr = 0xFFFF;
        tp = 0;
        tp1 = 0;
        bvr = 1;
        while((ttvr & 1) == 0)
        {
          ttvr = ttvr >> 1;
          bvr = (bvr << 1) | 1;
          tp++;
        }
        tttvr = 0;
        tp++;
        tp1++;
        bvr = (bvr << 1 ) | 1;
        ttvr = ttvr >> 1;
        while((ttvr & 1) == 1)
        {
          ttvr = ttvr >> 1;
          tttvr = (tttvr << 1) | 1;
          bvr = (bvr << 1) | 1;
          tp++;
          tp1++;
        }
        ttvr = (1 << tp) | tttvr;
        atvr = atvr << tp;
        tvr = atvr & tvr;
        tvr = tvr | ttvr;
      }

      /*Erase the structure having the last results
      (determinants of order i)*/

      if(boo == 1)
        mn = stmn.suivant;
      else
        mn = stmn1.suivant;

      while(mn != NULL)
      {
        bp = (mn->resultat)->suivant;
        while(bp != NULL)
        {
          SYM_free(bp->tab);
          liste = bp;
          bp = bp->suivant;
          SYM_free((signed char *)liste);
        }
        mn1 = mn;
        mn = mn->suivant;
        SYM_free((signed char *)(mn1->resultat));
        SYM_free((signed char *)mn1);
      }

      boo = -boo;
    }
    /* End of the loop for(i = 1 ;i < lg ; i++) */
  }
  /* End of the condition lg != 1 */
}
    return OK;
}

/*
is used by plth3 to compute
product of \psi^outer(S_inner), in the basis of Schur functions,
where outer and inner are partitions. 
*/

static INT calculi(sch,inner,outer,dep)  signed char *outer, *inner, *sch;
struct liste *dep;
{
    struct liste *bp, *entree;
    register signed char *bs, tp;
    signed char pas, tmp,we;

    pas=0;
    bs=inner;
    while(*bs) pas+= *bs++;
    
    tmp= -1;
    bs=sch;
    while(*bs) tmp+= *bs++;
    we=tmp;

    entree=(struct liste *) SYM_MALLOC(sizeof(struct liste));
    entree->coef= 1L;
    entree->tab= sch;
    entree->suivant=NULL;
    while(*outer)
    {
        while(entree!=NULL)
        {
            if(tmp== we)
            {
                gvr=0;
        calcul(inner,(int) *outer,entree->tab,dep,entree->coef,1,*outer+1);
            }
            else
            {
                bs=entree->tab;
                while(*bs) bs++;
                bs--;
                tp=tmp;
                for(;;)
                {
                    *bs -=tp;
                    if(bs==entree->tab) break;
                    bs--; tp--;
                }
                gvr=0;
        calcul(inner,(int) *outer,entree->tab,dep,entree->coef,1,*outer+1);
            }
            SYM_free(entree->tab);
            bp=entree;
            entree=entree->suivant;
            SYM_free((signed char *)bp);
        }
        tmp += ((*outer)*pas);
        entree=dep->suivant;
        dep->suivant=NULL;
        outer++;
    }
    dep->suivant=entree;
    return OK;
}

static INT calcula(inner,np,pa,res)
    signed char *inner,np;
    OP res;
    OP pa;

{
    OP crc,pb,cb,cf,tr;
    register signed char *bs,tp;
    INT i;
    signed char pas,av,tmp,lb,lim,*outer,*bouter;
    struct liste str, *bp, *db,*entree;

    if (S_O_K(res) != SCHUR) error("calcula:res != SCHUR");


    pas=0;
    bs=inner;
    while(*bs) pas+= *bs++;
    if(booo==0) lim= *(bs-1); else lim=bs-inner;

    db=(struct liste *)SYM_MALLOC(sizeof(struct liste));
    db->coef= 1L;
    db->tab= (signed char *)SYM_calloc(1,1);
    db->suivant=NULL;

    str.suivant=NULL;
    cb=callocobject();cf=callocobject();
    crc=callocobject(); m_part_sc(pa,crc);    
    for(i=0L;i<S_SC_PLI(crc);i++)
    {
         pb= S_SC_PI(crc,i);
        lb= S_PA_LI(pb);
        if(S_I_I(S_SC_WI(crc,(INT)i))!=0L
        && lim<=lng)
        {
            bs=(signed char *)SYM_MALLOC(S_PA_LI(pb)+1);
            outer=bs;
            for(tp=0;tp<S_PA_LI(pb);tp++)
                *bs++ =S_PA_II(pb,tp);
            *bs=0;

            entree=db;
            bouter=outer;
            tmp= -1;

            while(*bouter!=0)
            {

                while(entree!=NULL)
                {
                    if(*entree->tab==0)
                    {
                        gvr=0;
    calcul(inner,(int) *bouter,entree->tab,&str,1,1,*bouter);
                        entree=entree->suivant;
                    }/*End of if(*entree->tab==0)*/
                    else
                    {
                        bs=entree->tab;
                        while(*bs) bs++;
                        bs--;
                        tp=tmp;
                        for(;;)
                        {
                            *bs -=tp;
                            if(bs==entree->tab) break;
                            bs--; tp--;
                        }
                        gvr=0;
    calcul(inner,(int) *bouter,entree->tab,&str,entree->coef,1,*bouter+1);
                        SYM_free(entree->tab);
                        bp=entree;
                        entree=entree->suivant;
                        SYM_free((signed char *)bp);
                    }/*End of else of if(*entree->tab==0)*/
                }/*End of while(entree!=NULL)*/
                if(*(bouter+1)!=0)
                {
                    tmp += *bouter*pas;
                    entree=str.suivant;
                }
                else
                {
                    tr=callocobject();
                    bs=outer;
                /*Suppress cb=callocobject(); CC 24/01/97*/
                    M_I_I(1L,cb);av=0;
                    while(*bs)
                    {
                        M_I_I(*bs,cf);
                        mult_apply(cf,cb);
                        if(*bs==av)
                        {
                            tp++;
                            M_I_I(tp,cf);
                            mult_apply(cf,cb);
                        }
                        else tp = 1;
                        av= *bs;
                        bs++;
                    }    
                    div(S_SC_WI(crc,i),cb,cf); 
                    t_list_coef_SYM(&str,cf,np,tr);
/*CC 24/01/97*/                freeself(cb); freeself(cf);
                    if(nullp(res))
                    {
                         copy(tr,res); 
                         freeall(tr); /* CC 24/07/97*/
                    }
                    else
                    {
                        insert(tr,res,add_koeff,cmp);
                    }
                }
                str.suivant=NULL;
                bouter++;
            }/*End of while(*bouter!=0)*/
            SYM_free(outer);
        }/*End of if(S_I_I(S_SC_WI(...)*/
    }/*End of for(i=0L;i<...*/
    SYM_free(db->tab); 
    SYM_free((char *) db);
    freeall(crc);/**/
    freeall(cf); 
    freeall(cb);/* suppress CC 24/01/97 */
    return OK;
}



/*
Input os,on,opsi.
Output ores
make the product of S_os by the plethysm \psi_on(S_psi)
cond3==0=> limits upon length
cond3==1=> limits upon the biggest part
*/

static INT plth1(os,on,opsi,cond3,ores) OP os,on,opsi,ores;char cond3;
{
    register signed char *bs,i,j;
    register struct liste *bp;
    int tmp; /* AK 210199 */
    signed char li,lj,inv,tp,n,*s,*psi;
    struct liste stdep,*dep;
    OP sc,ve,cf,pol,d;
 
    if(S_O_K(os)!=INTEGER && S_O_K(os)!=PARTITION)
        return error("plth1: wrong first type");
    if(S_O_K(opsi)!=INTEGER && S_O_K(opsi)!=PARTITION)
        return error("plth1: wrong third type");
    if(S_O_K(on)!=INTEGER)
        return error("plth1: wrong second type");
    if(lng<0L)
    {
        init(SCHUR,ores);
        return OK;
    }
    n=S_I_I(on);
    if(n<0)
    {
        init(SCHUR,ores);
        return OK;
    }

    if(S_O_K(os)==INTEGER)
    {
        if(S_I_I(os)<0L)
        {
            init(SCHUR,ores); return OK;
        }
        sc=callocobject();
        if(S_I_I(os)==0L) m_il_v(0L,sc);
        else
        {
            m_il_v(1L,sc);
            M_I_I(S_I_I(os),S_V_I(sc,0L));
        }
        freeself(os); b_ks_pa(VECTOR,sc,os);
    }
    if(n==0)
    {
        if(not EMPTYP(ores)) freeself(ores);
        sc=callocobject();
        weight(os,sc);    /*CC 240596 to change with the upon the length of os*/
        if(S_I_I(sc)==0L)
        {
            M_I_I(1L,ores);freeall(sc);
            return OK;
        }
        freeall(sc);
        m_skn_s(os,cons_eins,NULL,ores);
        return OK;
    }
    if(S_O_K(opsi)==INTEGER)
    {
        if(S_I_I(opsi)<0L)
        {
            init(SCHUR,ores);
            return OK;
        }
        sc=callocobject();
        if(S_I_I(opsi)==0L) m_il_v(0L,sc);
        else
        {
            m_il_v(1L,sc);
            M_I_I(S_I_I(opsi),S_V_I(sc,0L));
        }
        freeself(opsi); b_ks_pa(VECTOR,sc,opsi);
    }
    sc=callocobject();
    weight(opsi,sc); /*CC 240596 to change with the upon the length of opsi*/
    if(S_I_I(sc)==0L)
    {
        freeall(sc);
        if(not EMPTYP(ores)) freeself(ores);
        sc=callocobject();
        weight(os,sc);    /*CC 240596 to change with the upon the length of os*/
        if(S_I_I(sc)!=0L)
        {
            m_skn_s(os,cons_eins,NULL,ores);freeall(sc);
            return OK;
        }
        else
        {
            M_I_I(1L,ores);
            freeall(sc);
            return OK;
        }
    }
    freeall(sc);

    dep= &stdep; dep->suivant=NULL;

    li=(signed char)S_PA_LI(os); lj=(signed char)S_PA_LI(opsi);
    if((cond3==1 && (S_PA_II(os,(INT)li-1L)>lng || S_PA_II(opsi,(INT)lj-1L)>lng))||(cond3==0 && (li>lng||lj>lng)))
    {
        init(SCHUR,ores); return OK;
    }
    if(not EMPTYP(ores)) freeself(ores);
    if(n==1)
    {
        sc=callocobject();
        M_I_I(lng,sc);
        l_outerproduct_schur_lrs(sc,os,opsi,ores);
        freeall(sc);
        return OK;
    }

    bs=(signed char *)SYM_MALLOC(li+1);
    s=bs; tp=0;
    for(i=0;i<li;i++,bs++)
        tp += *bs=S_PA_II(os,(INT)i);
    *bs=0;

    bs=(signed char *)SYM_MALLOC(lj+1);
    psi=bs;tmp=0;
    for(i=0;i<lj;i++,bs++)
        tmp += *bs=S_PA_II(opsi,(INT)i);
    *bs-- =0;

    tmp= n*tmp+tp;
    if(tmp>127)
    {
        fprintf(stderr,"Plethysms too big\n");
        SYM_free((signed char*)psi); SYM_free((signed char*)s);
        exit(0);
    }

    if(lj>= *bs)
    {
        lj--;inv=0;
        plet_conj(&psi,&lj);
    }
    else
    {
        inv=1;
        if(*s)
        {
            li--;
            plet_conj(&s,&li);
        }
    }

    gvr=0;
    if(cond3==0) booo=inv;
    else
    {
        if(inv==1) booo=0;
        else booo=1;
    }
    calcul(psi,(int) n,s,dep,1L,1,n);

    bp=dep->suivant;

    init(SCHUR,ores);d=ores;
    while(bp!=NULL)
    {
        bs=bp->tab;
        j= -1;
        while(*bs){ bs++;j++;}
        bs--;
        tp=tmp-1;
        for(i=j;i>=0;i--)
        {
            (*bs--) -=tp;
            tp--;
        }

    /*ALLOCATION OF A NEW MEMORY FOR THE VECTOR ve AND THE SCHUR FUNCTION sc.
    THE RESULT ores */

        sc = callocobject();
            ve = callocobject();
        pol=callocobject();
            init(VECTOR,ve);
            if(inv == 1)
        {
                  conjug( bp->tab , j , ve);
        }
            else
            {
                  bs = bp->tab;
                  m_il_v( (INT)(j+1), ve );
                  for(i = 0; i<=j ;i++)
                  {
                    M_I_I( (INT)(*bs), S_V_I(ve, (INT) i));
                    bs++;
                  }
            }
            SYM_free(bp->tab);
            b_ks_pa(VECTOR,ve,sc);
        cf=callocobject(); M_I_I(bp->coef,cf);
            b_skn_s(sc,cf,NULL,pol);
        c_l_n(d,pol);d=pol;

            dep = bp;
            bp = bp->suivant;
            SYM_free((signed char *)dep);
    }
    if(S_L_N(ores)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(ores);
            c_l_s(ores,S_L_S(S_L_N(ores)));
            c_l_n(ores,S_L_N(S_L_N(ores)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    SYM_free((signed char*)psi); SYM_free((signed char*)s);
    return OK;
}
/*
computes S_m (cond1==0) or \Lambda_m (cond1==1) of S_{tab} (cond2==0)
or \Lambda_tab(cond2==1) restricted upon length (cond3==0)
or upon parts (cond3==1)
*/

static INT plth2(tab,cond1,cond2,cond3,m,newton)
signed char *tab,cond1,cond2,cond3;
int m;
struct liste *newton;
{
  signed char  *s,*bs,*btab,*baf,*af,*bch,*tab1;
  char  condition,parite,mx,np,npt,le,inv;
  INT  cof;
  signed char  n,in;
  signed char  k;
  signed char  cond,high,mid;
  register signed char  i,j,temp;
  struct  liste str,*bp,*liste,*liste1;

  le=0;
  mx=0;
  btab=tab;
  while(*btab!=0)
  {
    le++;
    mx += *btab;
    btab++;
   }
   inv=0;
   if(*(btab - 1) < le)
   {
    inv = 1;
    tab1 = (signed char *)SYM_MALLOC(*(btab - 1) + 1);
    bs = tab1;
    btab = tab;
    af = (signed char *)SYM_MALLOC(le + 1);
    baf = af;
    while(*btab != 0)
      *baf++ = *btab++;
    *baf = 0;

    cond = -1;
    j = le - 1;
    btab = af + j;
    mid = *btab;
    j++;
    temp = 0;
    while(j >=  0)
    {
      high = 0;
      while(*btab == mid)
      {
        j--;
        high++;
        if(j == 0)
        {
          *btab = 0;
          j--;
          break;
        }
        btab--;
      }
      temp = temp+high;
      for(i = *btab;i < mid;i++)
      {
        cond++;
        *bs++ = temp;
      }
      mid = *btab;
    }
    *bs = 0;
    SYM_free(af);
  }
  else
  {
    tab1 = (signed char *)SYM_MALLOC(le + 1);
    btab = tab;
    bch = tab1;
    while(*btab != 0)
      *bch++ = *btab++;
    *bch = 0;
  }

  booo = 0;
  if((( cond2 == 0) && (inv == 0)) || ((cond2 == 1) && (inv == 1)))
    booo = 1;
  if(cond2 == 0)
  {
    if(lng < le)
    {
      fprintf(stderr,"No elements of the length %d in this plethysm\n",m);
      return ERROR;
    }
  }
  else
    if(lng < *(tab + le - 1))
    {
      fprintf(stderr,"No elements of the length %d in this plethysm\n",m);
      return ERROR;
    }


  liste1 = &str;

  if ( cond2 == 0)

    if(cond1 == 0)

      if((mx%2 == 0) || ((mx%2 == 1)&&(inv == 1)))
        condition = 0;
      else

        condition = 1;
    else

      if((mx%2 == 0) || ((mx%2 == 1)&&(inv == 1)))
        condition = 1;
      else
        condition = 0;
  else

    if(cond1 == 0)
      if((inv == 0) || ((inv == 1) && (mx%2 == 0)))
        condition = 0;
      else

        condition = 1;
    else
      if((inv == 0) || ((inv == 1) && (mx%2 == 0)))
        condition = 1;
      else

        condition = 0;
      liste = (struct liste *)SYM_MALLOC(sizeof(struct liste));
      liste->coef = 1L;
      liste->suivant = NULL;
      liste1->suivant = liste;
      bs = (signed char *)SYM_MALLOC(1);
      liste->tab = bs;
      *bs = 0;
      (newton)->suivant = liste1->suivant;


  for(n = 1;n <=  m;n++)
  {
    liste1->suivant = NULL;
    np = n * mx;
    npt = np;
    if( n == 1)
    {
      liste = (struct liste *)SYM_MALLOC(sizeof(struct liste));
      liste->coef = 1L;
      liste->suivant = NULL;
      liste1->suivant = liste;
      if (inv == 0)
      {
        bs = (signed char *)SYM_MALLOC(tab[le - 1] + 1);
        liste->tab = bs;
        btab = tab;
        af = (signed char *)SYM_MALLOC(le + 1);
        baf = af;
        while(*btab != 0)
          *baf++ = *btab++;
        *baf = 0;

        cond = -1;
        j = le - 1;
        btab = af + j;
        mid = *btab;
        j++;
        temp = 0;
        while(j >=  0)
        {
          high = 0;
          while(*btab == mid)
          {
            j--;
            high++;
            if(j == 0)
            {
              *btab = 0;
              j--;
              break;
            }
            btab--;
          }
          temp = temp+high;
          for(i = *btab;i < mid;i++)
          {
            cond++;
            *bs++ = temp;
          }
          mid = *btab;
        }
        *bs = 0;
        temp = mx - 1;
        bs--;
        for(i = 0 ;i <= cond; i++)
        {
          (*bs) += temp;
          temp--;
          if(i != cond)
            bs--;
        }
        if(bs == NULL)
          return OK;
        SYM_free(af);

      }
      else
      {
        liste->tab = (signed char *)SYM_MALLOC(le + 1);
        bs = liste->tab + le;
        *bs-- = 0;
        btab = tab + le - 1;
        temp = mx - 1;
        for(i = 1 ;i <= le; i++)
        {
          *bs  = *btab + temp;
          temp--;
          if(i != le)
          {
            btab--;
            bs--;
          }
        }
      }
    }
    else
    {
      for(in = 0;in < n;in++)
      {
/*
        fprintf(stderr,"\nn = %d,in = %d ",n,in);
*/
        if(condition == 1)
        {
          i = (n+1+in)%2;
          if(i == 0)
            parite = 1;
          else
            parite = -1;
        }
        else
          parite = 1;


        liste = (newton+in)->suivant;

        while(liste != NULL)
        {
          baf = liste->tab;
          temp = np - npt;
          s = (signed char *)SYM_MALLOC(temp + 1);
          if(temp != 0)
          {
            temp--;
            j = 0;
            while(*baf != '\0')
            {
              j++;
              baf++;
            }

            baf--;
            btab = s + j;
            *btab-- = 0;
            for(k = j-1;k >= 0;k--)
            {
              *btab = (*baf) - temp;
              if(k != 0)
              {
                btab--;
                baf--;
                temp--;
              }
            }
          }
          else
            *s  = '\0';

          cof = liste->coef;
          gvr = 0;

          if(cond3==1)
          {
        if(booo==1) booo=0;
        else booo=1;
          }
          calcul(tab1,(int) n - in,s,liste1,cof,parite,n);
          if(cond3==1)
          {
        if(booo==1) booo=0;
        else booo=1;
          }
          SYM_free(s);
          liste = liste->suivant;
        }
        npt = npt - mx;

      }
    /* End of the loop for (in = 0;in < n ;in++) */

    }
    liste = liste1->suivant;

    while(liste != NULL)
    {
      liste->coef = liste->coef/n;
      liste = liste->suivant;
    }

    (newton+n)->suivant = liste1->suivant;

  }

  /* End of the loop with n*/
  liste = newton + 1;

  for(in=1;in<=m;in++)
  {
    bp = liste->suivant;
    k = in * mx;

    /*We read  the Schur functions which are expressions of Sin(Sp),
    to express them by their diagonal indices*/

    while(bp != NULL)
    {
      btab = bp->tab;
      j = -1;
      while(*btab  !=  '\0')
      {
        btab++;
        j++;
      }
      btab--;
      temp = k-1;

      for(i = j;i >  0;i--)
      {
        (*btab--)  -= temp;
        temp--;
      }
      *btab -=temp;
  

      af=(signed char *)SYM_MALLOC(j+2);
      baf=af;
      btab=bp->tab+j;
      for(i=0;i<j;i++)
        *baf++ = *btab--;
      *baf++ = *btab; *baf=0;
      SYM_free(btab);
      bp->tab=af;
      bp = bp->suivant;
    }
    liste++;
  }
  SYM_free(tab1);
  return OK;
}


/*
Puts in c the decomposition of the plethysm
\psi^a(S_b) where a and b are partitions, in the basis of Schur functions
cond3==0=> retriction upon length. cond3==1=> restriction upon parts.
*/

static INT plth3(a,b,cond3,c) OP a,b,c; signed char cond3;
{
    OP sc,d,pol,ve,cf;
    signed char *inner,*outer,*sch;
    signed char tp,la,lb,inv,tmp,j;
    struct liste *dep,str,*bp;
    register signed char i,*bs;

    
    if(S_O_K(a)!=INTEGER && S_O_K(a)!=PARTITION)
        return error("plth3: wrong first type");
    if(S_O_K(b)!=INTEGER && S_O_K(b)!=PARTITION)
        return error("plth3: wrong second type");

    if(S_O_K(b)==INTEGER)
    {
        if(S_I_I(b)<0L)
        {
            init(SCHUR,c);return OK;
        }
        if(S_I_I(b)==0L)
        {
            freeself(c);M_I_I(1L,c);return OK;
        }
        sc=callocobject();
        m_il_v(1L,sc);
        M_I_I(S_I_I(b),S_V_I(sc,0L));
        freeself(b);b_ks_pa(VECTOR,sc,b);
    }

    if(S_O_K(a)==INTEGER)
    {
        if(S_I_I(a)<0L)
        {
            init(SCHUR,c);return OK;
        }
        if(S_I_I(a)==0L)
        {
            freeself(c);M_I_I(1L,c);return OK;
        }
        sc=callocobject();
        M_I_I(0L,sc);
        plth1(sc,a,b,cond3,c);
        freeall(sc); return OK;
    }

    if(S_PA_LI(a)==0L || S_PA_LI(b)==0L)
    {
        freeself(c); M_I_I(1L,c); return OK;
    }
    if(S_PA_LI(a)==1L)
    {
        sc=callocobject();
        M_I_I(0L,sc);
        plth1(sc,S_PA_I(a,0L),b,cond3,c);
        freeall(sc); return OK;
    }

    lb= (signed char)S_PA_LI(b);
    if((cond3==1 && S_PA_II(b,(INT)lb-1L)>lng )||(cond3==0 && lb>lng))
    {
        init(SCHUR,c); return OK;
    }

    bs=(signed char *)SYM_MALLOC(lb+1);
    inner=bs; tp=0;
    for(i=0;i<lb;i++,bs++)
        tp += *bs= S_PA_II(b,(INT)i);

    *bs-- =0; inv=1;
    if(lb>= *bs)
    {
        lb--;inv=0;
        plet_conj(&inner, &lb);
    } 

    la=(signed char ) S_PA_LI(a);
    bs=(signed char *)SYM_MALLOC(la+1);
    outer=bs; tmp=0;
    for(i=0;i<la;i++,bs++)
        tmp += *bs= S_PA_II(a,(INT)i);
    *bs =0;

    tmp *= tp;
/* gcc: comparison is always 0 due to limited range of data type
    if(tmp > 127)
        return error("plth3: plethysm too big");
*/

    if(cond3==0) booo=inv;
    else if(inv==1) booo=0;
        else booo=1;

    dep= &str;
    str.suivant=NULL;
    sch=(signed char *)SYM_calloc(1,1);
    calculi(sch,inner,outer,dep);
    tmp--;

    bp=dep->suivant;

    init(SCHUR,c);d=c;
    while(bp!=NULL)
    {
        bs=bp->tab;
        j= -1;
        while(*bs){ bs++;j++;}
        bs--;
        tp=tmp;
        for(i=j;i>=0;i--)
        {
            (*bs--) -=tp;
            tp--;
        }

    /*ALLOCATION OF A NEW MEMORY FOR THE VECTOR ve AND THE SCHUR FUNCTION sc.
    THE RESULT c */

        sc = callocobject();
            ve = callocobject();
        pol=callocobject();
            init(VECTOR,ve);
            if(inv == 1)
        {
                  conjug( bp->tab , j , ve);
        }
            else
            {
                  bs = bp->tab;
                  m_il_v( (INT)(j+1), ve );
                  for(i = 0; i<=j ;i++)
                  {
                    M_I_I( (INT)(*bs), S_V_I(ve, (INT) i));
                    bs++;
                  }
            }
            SYM_free(bp->tab);
            b_ks_pa(VECTOR,ve,sc);
        cf=callocobject(); M_I_I(bp->coef,cf);
            b_skn_s(sc,cf,NULL,pol);
        c_l_n(d,pol);d=pol;

            dep = bp;
            bp = bp->suivant;
            SYM_free((signed char *)dep);
    }
    if(S_L_N(c)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(c);
            c_l_s(c,S_L_S(S_L_N(c)));
            c_l_n(c,S_L_N(S_L_N(c)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    SYM_free(outer); SYM_free(inner);
    return OK;
}


/*
Puts in c the decomposition of the product
S_os * \psi^a(S_b) where a and b are partitions, in the basis of Schur functions
cond3==0=> retriction upon length. cond3==1=> restriction upon parts.
*/

static INT plth5(os,a,b,cond3,c) OP os,a,b,c; signed char cond3;
{
    OP sc,d,pol,ve,cf;
    signed char *inner,*outer,*sch;
    signed char tp,la,lb,inv,tmp,j,los,pdos;
    struct liste *dep,str,*bp;
    register signed char i,*bs;

    
    if(S_O_K(a)!=INTEGER && S_O_K(a)!=PARTITION)
        return error("plth5: wrong second type");
    if(S_O_K(b)!=INTEGER && S_O_K(b)!=PARTITION)
        return error("plth5: wrong third type");
    if(S_O_K(os)!=INTEGER && S_O_K(os)!=PARTITION)
        return error("plth5: wrong first type");

    if(lng<0){init(SCHUR,c); return OK;}    

    if(S_O_K(os)==INTEGER)
    {
        if(S_I_I(os) <0L)
        {
            init(SCHUR,os); return OK;
        }
        else
        {
            sc=callocobject();
            if(S_I_I(os) == 0L)  m_il_v(0L,sc);
                    else
                       {
                           m_il_v(1L,sc);
                             M_I_I(S_I_I(os),S_V_I(sc,0L));
                    }
                    freeself(os); b_ks_pa(VECTOR,sc,os);

        }    
    }

    if(cond3==0 && S_PA_LI(os) > lng)
    {
        init(SCHUR,c);return OK;
    }
    
    if(S_PA_LI(os) > 0 && (cond3==1 && S_PA_II(os,S_PA_LI(os)-1L)>lng))
    {
        init(SCHUR,c);return OK;
    }

    if(S_O_K(b)==INTEGER)
    {
        if(S_I_I(b)<0L)
        {
            init(SCHUR,c);return OK;
        }
        if(S_I_I(b)==0L)
        {
            freeself(c);m_skn_s(os,cons_eins,NULL,c);return OK;
        }
        sc=callocobject();
        m_il_v(1L,sc);
        M_I_I(S_I_I(b),S_V_I(sc,0L));
        freeself(b);b_ks_pa(VECTOR,sc,b);
    }

    if(S_O_K(a)==INTEGER)
    {
        if(S_I_I(a)<0L)
        {
            init(SCHUR,c);return OK;
        }
        if(S_I_I(a)==0L)
        {
            freeself(c);m_skn_s(os,cons_eins,NULL,c);return OK;
        }
        plth1(os,a,b,cond3,c);
        return OK;
    }

    if(S_PA_LI(a)==0L || S_PA_LI(b)==0L)
    {
        freeself(c);m_skn_s(os,cons_eins,NULL,c); return OK;
    }
    if(S_PA_LI(a)==1L)
    {
        plth1(os,S_PA_I(a,0L),b,cond3,c);
        return OK;
    }

    lb= (signed char)S_PA_LI(b);
    if((cond3==1 && S_PA_II(b,(INT)lb-1L)>lng )||(cond3==0 && lb>lng))
    {
        init(SCHUR,c); return OK;
    }

    los=S_PA_LI(os);
    bs=(signed char *)SYM_MALLOC(los+1);
    sch=bs; pdos=0;
    for(i=0;i<los;i++,bs++)
    {
        *bs= S_PA_II(os,i);
        pdos+= *bs;
    }
    *bs=0;

    bs=(signed char *)SYM_MALLOC(lb+1);
    inner=bs; tp=0;
    for(i=0;i<lb;i++,bs++)
        tp += *bs= S_PA_II(b,(INT)i);

    *bs-- =0;
    if(lb>= *bs)
    {
        lb--;inv=0;
        plet_conj(&inner, &lb);
    } 
    else
    {
        inv=1;
        if(*sch!=0)
        {
            los--; plet_conj(&sch,&los);
        }
    }

    la=(signed char ) S_PA_LI(a);
    bs=(signed char *)SYM_MALLOC(la+1);
    outer=bs; tmp=0;
    for(i=0;i<la;i++,bs++)
        tmp += *bs= S_PA_II(a,(INT)i);
    *bs =0;

    tmp = tmp*tp+pdos;

/*  gcc: comparison is always 0 due to limited range of data type
    if(tmp > 127)
        return error("plth3: plethysm too big");
*/
    if(cond3==0) booo=inv;
    else if(inv==1) booo=0;
        else booo=1;

    dep= &str;
    str.suivant=NULL;
    calculi(sch,inner,outer,dep);
    tmp--;

    bp=dep->suivant;

    init(SCHUR,c);d=c;
    while(bp!=NULL)
    {
        bs=bp->tab;
        j= -1;
        while(*bs){ bs++;j++;}
        bs--;
        tp=tmp;
        for(i=j;i>=0;i--)
        {
            (*bs--) -=tp;
            tp--;
        }

    /*ALLOCATION OF A NEW MEMORY FOR THE VECTOR ve AND THE SCHUR FUNCTION sc.
    THE RESULT c */

        sc = callocobject();
            ve = callocobject();
        pol=callocobject();
            init(VECTOR,ve);
            if(inv == 1)
        {
                  conjug( bp->tab , j , ve);
        }
            else
            {
                  bs = bp->tab;
                  m_il_v( (INT)(j+1), ve );
                  for(i = 0; i<=j ;i++)
                  {
                    M_I_I( (INT)(*bs), S_V_I(ve, (INT) i));
                    bs++;
                  }
            }
            SYM_free(bp->tab);
            b_ks_pa(VECTOR,ve,sc);
        cf=callocobject(); M_I_I(bp->coef,cf);
            b_skn_s(sc,cf,NULL,pol);
        c_l_n(d,pol);d=pol;

            dep = bp;
            bp = bp->suivant;
            SYM_free((signed char *)dep);
    }
    if(S_L_N(c)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(c);
            c_l_s(c,S_L_S(S_L_N(c)));
            c_l_n(c,S_L_N(S_L_N(c)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    SYM_free(outer); SYM_free(inner);    /*Ne pas liberer sch: ca a ete fait dans calculi*/
    return OK;
}


static INT conjugate_apply_schur(a) OP a;
/* afterwards a is no longer ordered */
{
    OP tmp,z;
    if(S_O_K(a)==SCHUR)
    {
        if(not nullp(a))
        {
            z=a;
            while(z!=NULL)
            {
                tmp=callocobject();

                conjugate_partition(S_S_S(z),tmp);
                copy(tmp,S_S_S(z));

                freeall(tmp);
                z=S_L_N(z);
            }    
        }    
    }
    return OK;
}


/*
Puts in c the decomposition of the plethysm
S_a(S_b) where a and b are partitions, in the basis of Schur functions
cond3==0=> retriction upon length. cond3==1=> restriction upon parts.
*/

INT cc_plet_pss_integer_partition(a,b,c,f) OP a,b,c,f;
/* to call from pss_integer_partition */
{
    INT erg = OK;
    OP d;
    CTO(INTEGER,"cc_plet_pss_integer_partition_(1)",a);
    CTO(PARTITION,"cc_plet_pss_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"cc_plet_pss_integer_partition_(3)",c);

    if (S_PA_LI(b) == 0) {
        OP m;
        m = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
        COPY(f,S_MO_K(m));
        COPY(b,S_MO_S(m));
        if (S_O_K(c) == SCHUR)
            insert_list(m,c,add_koeff,comp_monomschur);
        else
            insert_scalar_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        goto ende;
        }

    d = CALLOCOBJECT();
    erg += schur_schur_plet(a,b,d);
    CTO(SCHUR,"cc_plet_pss_integer_partition(i1)",d);
    MULT_APPLY(f,d);
    if (S_O_K(c) == SCHUR)
        insert_list_list(d,c,add_koeff,comp_monomschur);
    else
        insert_schur_hashtable(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);

ende:
    ENDR("cc_plet_pss_integer_partition");
}
INT cc_plet_phs_integer_partition(a,b,c,f) OP a,b,c,f;
/* to call from phs_integer_partition */
/* AK 2002 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"cc_plet_phs_integer_partition_(1)",a);
    CTO(PARTITION,"cc_plet_phs_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"cc_plet_phs_integer_partition_(3)",c);
 
    {
    OP d;
    d = CALLOCOBJECT();
    erg += complete_schur_plet(a,b,d);
    CTO(SCHUR,"cc_plet_phs_integer_partition(i1)",d);
    MULT_APPLY(f,d);
    if (S_O_K(c) == SCHUR)
        insert_list_list(d,c,add_koeff,comp_monomschur);
    else
        insert_schur_hashtable(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
    }
 
    ENDR("cc_plet_phs_integer_partition");
}
INT cc_plet_pes_integer_partition(a,b,c,f) OP a,b,c,f;
/* to call from pes_integer_partition */
{
    INT erg = OK;
    OP d;
    CTO(INTEGER,"cc_plet_pes_integer_partition_(1)",a);
    CTO(PARTITION,"cc_plet_pes_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"cc_plet_pes_integer_partition_(3)",c);
 
    d = CALLOCOBJECT();
    erg += elementary_schur_plet(a,b,d);
    CTO(SCHUR,"cc_plet_phs_integer_partition(i1)",d);
    MULT_APPLY(f,d);
    if (S_O_K(c) == SCHUR)
        insert_list_list(d,c,add_koeff,comp_monomschur);
    else
        insert_schur_hashtable(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
 
    ENDR("cc_plet_pes_integer_partition");
}



INT cc_plet_pss_partition_partition(a,b,c,f) OP a,b,c,f;
/* to call from pss_partition_partition */
{
    INT erg = OK;
    OP d;
    CTO(PARTITION,"cc_plet_pss_partition_partition_(1)",a);
    CTO(PARTITION,"cc_plet_pss_partition_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"cc_plet_pss_partition_partition_(3)",c);
 
    d = CALLOCOBJECT();
    erg += schur_schur_plet(a,b,d);
    CTO(SCHUR,"cc_plet_pss_integer_partition(i1)",d);
    MULT_APPLY(f,d);
    if (S_O_K(c) == SCHUR)
        insert_list_list(d,c,add_koeff,comp_monomschur);
    else
        insert_schur_hashtable(d,c,add_koeff,eq_monomsymfunc,hash_monompartition);
 
    ENDR("cc_plet_pss_partition_partition");
}


/*
Puts in c the decomposition of the plethysm
S_a(S_b) where a and b are partitions, in the basis of Schur functions
cond3==0=> retriction upon length. cond3==1=> restriction upon parts.
*/
static INT plth4(a,b,cond3,c) OP a,b,c; signed char cond3;
{
    OP sc;
    signed char *inner;
    signed char tp,lb,inv,tmp;
    register signed char i,*bs;

    
    if(S_O_K(a)!=INTEGER && S_O_K(a)!=PARTITION)
        return error("plth4: wrong first type");
    if(S_O_K(b)!=INTEGER && S_O_K(b)!=PARTITION)
        return error("plth4: wrong second type");

    if(S_O_K(b)==INTEGER)
    {
        if(S_I_I(b)<0L) { init(SCHUR,c);return OK; }
        if(S_I_I(b)==0L) { freeself(c);M_I_I(1L,c);return OK; }
        sc=callocobject();
        m_il_v(1L,sc);
        M_I_I(S_I_I(b),S_V_I(sc,0L));
        freeself(b);b_ks_pa(VECTOR,sc,b);
    }

    if(S_O_K(a)==INTEGER)
    {
        if(S_I_I(a)<0L) { init(SCHUR,c);return OK; }
        if(S_I_I(a)==0L) { freeself(c);M_I_I(1L,c);return OK; }
        sc=callocobject();
        m_il_v(1L,sc);
        M_I_I(S_I_I(a),S_V_I(sc,0L));
        freeself(a);b_ks_pa(VECTOR,sc,a);
    }

    if(S_PA_LI(a)==0L || S_PA_LI(b)==0L) { freeself(c); M_I_I(1L,c); return OK; }

    lb= (signed char)S_PA_LI(b);
    if((cond3==1 && S_PA_II(b,(INT)lb-1L)>lng )||(cond3==0 && lb>lng))
    {
        init(SCHUR,c); return OK;
    }

    bs=(signed char *)SYM_MALLOC(lb+1);
    inner=bs; tp=0;
    for(i=0;i<lb;i++,bs++)
        tp += *bs= S_PA_II(b,(INT)i);

    *bs-- =0; inv=1;
    if(lb>= *bs)
    {
        lb--;inv=0;
        plet_conj(&inner, &lb);
    } 

    sc=callocobject();
    weight(a,sc);
    
    tmp = tp*(char)S_I_I(sc); 
    freeall(sc);
/* gcc:  comparison is always 0 due to limited range of data type
    if(tmp > 127)
        return error("plth4: plethysm too big");
*/

    if(cond3==0) booo=inv;
    else if(inv==1) booo=0;
        else booo=1;

    init(SCHUR,c);
    calcula(inner,tmp-1,a,c);
    if(inv==1) conjugate_apply_schur(c);
    SYM_free(inner);
    return OK;
}



/*
Insert a Schur function in a sorted list,
the partition being read from the right.
Partition begins at *af
*/
/*
NOT TESTED
*/
#ifdef UNDEF

static INT ins_s_lst(af,coef,plst)
    signed char *af;
    INT coef;
    struct liste **plst;
{
  register struct liste *bp,*bpp;
  struct liste *bc;
  signed char *db;
  register signed char *baf,*btab;

  bpp= *plst;
  bp=bpp->suivant;
  baf=af; while(*baf) baf++;
  db = --baf;
  while(bp!=NULL)
  {
    baf=db;
    btab=bp->tab;
    while(*btab) btab++;
    btab--;
    for(;;)
    {
      if(*baf < *btab)
        goto out1;
      if(*baf > *btab)
        goto out2;
      if(baf==af) goto out3;
      baf--; btab--;
    }
out1:
    bpp=bp;
    bp=bp->suivant;
  }

/*
On sort avec bp==NULL ou avant un plus grand element dans la liste
*/  
out2:
  bc=(struct liste *)SYM_MALLOC(sizeof(struct liste));
  bc->coef=coef;
  bc->suivant=bp;
  btab=(signed char *)SYM_MALLOC(db+2);
  baf=af;
  bc->tab=btab;
  while(*baf)
    *btab++ = *baf++;
  *btab=0;
  bpp->suivant=bc;
  *plst=bpp;
  return OK;

/*
l'element existe deja dans la liste
*/
out3:
  if(coef== -bp->coef)
  {
    bpp->suivant=bp->suivant;
    SYM_free(bp->tab);
    SYM_free((char *)bp);
  }
  else
    bp->coef +=coef;
  *plst=bpp;
  return OK;
}

#endif

/*
list2 est le shuffle des 2 listes triees
a partir de la fin sig*lst1 et lst2
sig*lst1 signifie que le champ coef de toutes les cellules est
multiplie par sig
*/

/*
static INT shuffle_sg(lst1,sig,lst2)
register struct liste *lst1;
struct liste *lst2;
signed char sig;
{
  lst1=lst1->suivant;
  while(lst1!= NULL)
  {
    ins_s_lst(lst1->tab,lst1->coef*sig,&lst2);
    lst1=lst1->suivant;
  }
  return OK;
}
*/


/*
insert a Schur function in a sorted list
Partition begins at *af
*/

static INT ins_sc_lst(af,coef,plst)
    signed char *af;
    INT coef;
    struct liste **plst;
{
  register struct liste *bp,*bpp;
  struct liste *bc;
  register signed char *baf,*btab;

  bpp= *plst;
  bp=bpp->suivant;
  while(bp!=NULL)
  {
    baf=af;
    btab=bp->tab;
    while(*baf!=0)
    {
      if(*baf < *btab)
        goto out1;
      if(*baf > *btab)
        goto out2;
      baf++;btab++;
    }
    goto out3;
out1:
    bpp=bp;
    bp=bp->suivant;
  }

/*
On sort avec bp==NULL ou avant un plus grand element dans la liste
*/  
out2:
  bc=(struct liste *)SYM_MALLOC(sizeof(struct liste));
  bc->coef=coef;
  bc->suivant=bp;
  baf=af;
  while(*baf++);
  btab=(signed char *)SYM_MALLOC(baf-af+1);
  baf=af;
  bc->tab=btab;
  while(*baf)
    *btab++ = *baf++;
  *btab=0;
  bpp->suivant=bc;
  *plst=bpp;
  return OK;

/*
l'element existe deja dans la liste
*/
out3:
  if(coef== -bp->coef)
  {
    bpp->suivant=bp->suivant;
    SYM_free(bp->tab);
    SYM_free((char *)bp);
  }
  else
    bp->coef +=coef;
  *plst=bpp;
  return OK;
}

/*
list2 est le shuffle des 2 listes triees sig*lst1 et lst2
sig*lst1 signifie que le champ coef de toutes les cellules est
multiplie par sig
*/

static INT shuffle_sig(lst1,sig,lst2)
register struct liste *lst1;
struct liste *lst2;
signed char sig;
{
  lst1=lst1->suivant;
  while(lst1!= NULL)
  {
    ins_sc_lst(lst1->tab,lst1->coef*sig,&lst2);
    lst1=lst1->suivant;
  }
  return OK;
}

/*
frees a list
*/

static INT free_lst (lst)
register struct liste *lst;
{
  struct liste *lst1,*bp;
  lst1=lst;
  lst=lst->suivant;
  while(lst!=NULL)
  {
    SYM_free(lst->tab);
    bp=lst;
    lst=lst->suivant;
    SYM_free((signed char *)bp);
  }
  lst1->suivant=NULL;
  return OK;
}

/*
frees a tableau of struct liste tiil the rank n
*/
/* CC 24/01/97 */

static INT free_newton(newton, n)
struct liste *newton; int n;
{
    for(; n>=0; n--)
    {
        free_lst(newton);
        newton++;
    }
    return OK;
}

 
/*
returns the weight of partitions of a  list
*/
static INT poids (lst)
struct liste *lst;
{
  register signed char *btab;
  register signed char tmp=0;

  lst=lst->suivant;
  if(lst!=NULL)
  { 
    btab=lst->tab;
    while(*btab)
    {
      tmp+= *btab;
      btab++;
    }
  }
  return((INT)tmp);
}

/*
insere une fonction de Schur dans une liste
*af est la taille de la partition
*/

static INT ins_sch_lst(af,coef,plst)
    signed char *af;
    INT coef;
    struct liste **plst;
{
  register struct liste *bp,*bpp;
  struct liste *bc;
  register signed char *baf,*btab;

  bpp= *plst;
  bp=bpp->suivant;
  while(bp!=NULL)
  {
    baf=af+1;
    btab=bp->tab;
    while(*baf!=0)
    {
      if(*baf < *btab)
        goto out1;
      if(*baf > *btab)
        goto out2;
      baf++;btab++;
    }
    goto out3;
out1:
    bpp=bp;
    bp=bp->suivant;
  }

/*
On sort avec bp==NULL ou avant un plus grand element dans la liste
*/  
out2:
  bc=(struct liste *)SYM_MALLOC(sizeof(struct liste));
  bc->coef=coef;
  bc->suivant=bp;
  baf=af;
  btab=(signed char *)SYM_MALLOC(*baf+1);
  baf++;
  bc->tab=btab;
  while(*baf)
    *btab++ = *baf++;
  *btab=0;
  bpp->suivant=bc;
  *plst=bpp;
  return OK;

/*
l'element existe deja dans la liste
*/
out3:
  if(coef== -bp->coef)
  {
    bpp->suivant=bp->suivant;
    SYM_free(bp->tab);
    SYM_free((signed char *)bp);
  }
  else
    bp->coef +=coef;
  *plst=bpp;
  return OK;
}


/*
met dans lst le produit de S_fi par S_ev
produit restreint aux partitions dont les parts sont <= mx
lst est une liste a entete et peut ne pas etre vide (lst->suivant!= NULL)
retourne l'adresse de la
cellule precedent la premiere cellule de la liste qui a ete modifie
va plus vite si le poids de fi est superieur que le poids de ev
Algo sophistique
*/

static struct liste * proprt(fi,ev,coef1,coef2,mx,lst)
    signed char *fi,*ev,mx;
    INT coef1,coef2;
    struct liste *lst;
{
  INT cmt;
  INT coef;
  signed char etat,ssetat=0,bas=0,ev_niv,ym;
  signed char nb_lt,lg_fi,lg_tb,lg_tb_dct,lg_old;
  signed char i,j=0,k,tmp,tp,dsp,topc,topd,pds,av,fr=0;
  register signed char niv;
  signed char sz_pcar,sz_plst,sz_lst;
  signed char **tb,**nb_tb,**ctb,**dtb,**etb,**ftb,**gtb,**htb;
  register signed char **btb,**bnb_tb,**byam;
  signed char **yam;
  signed char *af,*bfi,*bev,*pos,*bpos;
  register signed char *baf;
  struct liste **pl,**bpl,*bpc,*lst1;

  cmt=1L;

/*
 Faire un test si il y a des termes ou pas
*/
  if((*fi > mx)|| (*ev > mx)) return lst;
/*
nb_lt nombre de lettres
lg_fi longueur de la forme interieure
*/
  baf=ev;
  nb_lt= 0;
  while(*baf++) nb_lt++;
  baf=fi;
  lg_fi= 0;
  while(*baf++) lg_fi++;
/*

lg_fi=*fi;nb_lt=*ev;
*/
  sz_pcar= sizeof(signed char *);  /* Dimension d'un pointeur sur caractere*/
  sz_plst= sizeof(struct liste *); /*Dimension de pointeur sur structure liste*/
  sz_lst= sizeof(struct liste);  /* Dimension sur structure liste*/
  lg_tb= lg_fi+nb_lt;  /* Longueur maximum des tableaux resultat*/

/*
Creation de 3 tableaux bidimensionnels avec pour nombre de lignes lg_tb
*/

  tb=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  nb_tb=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  yam=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  btb=tb;
  bnb_tb=nb_tb;byam=yam;
  for(i=0;i<=lg_tb+2;i++)
  {
    *btb++ =(signed char *)SYM_calloc(nb_lt+3,1);
    *bnb_tb++ =(signed char *)SYM_calloc(nb_lt+3,1);
    *byam++ =(signed char *)SYM_calloc(nb_lt+3,1);
  }
  *btb=NULL;*bnb_tb =NULL;*byam=NULL;

/*
Construction d'un tableau de taille lg_tb+3
*/

af=(signed char *)SYM_calloc(lg_tb+3,1);

/*
Creation d'un tableau de dimension nb_lt + 2
ou on met les sommes cumulees du vecteur d'evaluation
pds: poids de la partition composee des parts de la partition
*/

  pos=(signed char *)SYM_MALLOC(nb_lt+2);
  bpos=pos;
  *bpos++ =0; bev=ev;av=0;
  for(i=1;i<=nb_lt;i++)
  {
    *bpos = av+ *bev;
    av= *bpos;
    bev++;bpos++;
  }
  pds= *--bpos;


/*
Creation d'un tableau de pointeurs sur struct liste de dimension
pds pour l'insertion d'un tableau dans la liste des tableaux
*/

  pl=(struct liste **)SYM_MALLOC((pds+2)*sz_plst);


/*
Initialisation de tb selon fi
*/
  **tb=mx;
  btb=tb+1;
  bfi=fi;
  for(i=1;i<=lg_fi;i++)
  {
    tmp= *bfi;
    bpos= *btb;
    for(j=0;j<=nb_lt+1;j++)
    {
      *bpos++ = tmp;
    }
    bfi++;btb++;
  }

/* Remplissage des tableaux */
  
  btb=tb; bev=ev;
  bnb_tb=nb_tb+1;
  byam=yam+1;
  dsp = *bev;
  ctb=btb; dtb= btb+1;
  etb= bnb_tb;
  while(dsp!= 0)
  {
    topc= **ctb;
    topd= **dtb;
    tmp= topc-topd;
    if(tmp>=dsp)
    {
/*
dsp etant different de 0, tmp est > 0
*/
      *(*byam+1)=99;
      *(*etb+1)=dsp;
      tmp= **dtb+dsp;
      bpos = *dtb+1;
      for(j=1;j<=nb_lt+1;j++)
        *bpos++ = tmp;
      break;
    }
    *(*byam+1)=99;
    *(*etb+1)=tmp;
    dsp -= tmp;
    tmp= **dtb+tmp;
    bpos= *dtb+1;
    for(j=1;j<=nb_lt+1;j++)
      *bpos++ = tmp;
     ctb++;dtb++;etb++;byam++;
  }/* Fin du while(dsp !=0)*/

  bev++;btb++;
  byam=yam+1;
  for(i=2;i<=nb_lt;i++)
  {
    dsp= *bev;
    ctb=btb; dtb=btb+1;
    etb= bnb_tb; ftb=bnb_tb+1;
    gtb=byam; htb=byam+1;
    k=i;
    while(dsp !=0)
    {
      topc= *(*ctb+i-1);
      topd= *(*dtb+i-1);
      tmp=topc-topd;
      ym= *(*gtb+i) + *(*etb+i-1);
      if(ym<tmp)
        tmp=ym;
      if(tmp>=dsp)
      {
  /*
  dsp etant different de 0, tmp est > 0
  */
        *(*ftb+i)=dsp;
        *(*htb+i)= ym - dsp;
        tmp= *(*dtb+i-1)+dsp;
        bpos= *dtb+i;
        for(j=i;j<=nb_lt+1;j++)
          *bpos++ = tmp;
        break;
      }/* if(tmp>=dsp) */
      *(*ftb+i)=tmp;
      *(*htb+i)= ym - tmp;
      dsp -=tmp;
      tmp= *(*dtb+i-1)+tmp;
      bpos= *dtb+i;
      for(j=i;j<=nb_lt+1;j++)
        *bpos++ = tmp;
      ctb++;dtb++;
      etb++;ftb++;
      gtb++;htb++;
      k++;
    }/*while(dsp != 0)*/
    k++;
    gtb++;htb++;etb++;
    for(;k<=lg_tb;k++)
    {
      *(*htb+i)= *(*gtb+i)+ *(*etb+i-1);
      htb++;gtb++;etb++;
    }
    bev++;btb++;bnb_tb++;byam++;
  }/*for(i=2;i<=nb_lt;i++)*/

  baf=af+1;
  btb=tb+1;
  for(i=1;i<= lg_tb+1;i++)
  {
    tmp= *(*btb+nb_lt);
    *baf= tmp;
    if(tmp==0) break;
    baf++;btb++;
 }
 lg_tb_dct=i-1;


  **tb=0;

  coef=coef1*coef2;
  bpl=pl+1;
  for(i=1;i<=pds;i++)
    *bpl++ =lst;
  *af=lg_tb_dct;
  ins_sch_lst(af,coef,&lst);
  lst1=lst;

/*
Debut de l'algorithme
*/
  niv=nb_lt;
  lg_old=lg_tb_dct;
  etat=0;

  while(niv>0)
  {
    switch(etat)
    {
      case 0:
      
/*
Depilage: Essai de placer les lettres plus haut dans le tableau
*/
      
      ev_niv=ev[niv-1];
      baf=af+lg_tb_dct;
      btb=tb+lg_tb_dct;
      bnb_tb=nb_tb+lg_tb_dct;
      i= ev_niv;j=lg_tb_dct;
      av=lg_tb_dct+1;

      while(i>0)
      {
/*
Chaque lettre i de valeur niv est testee.
*/
        if(*(*bnb_tb+ niv)==0)
        {
          bnb_tb--;btb--;
          j--;baf--;
        }
        else
        {
          ctb=btb;dtb=btb+1;
          
          for(k=j+1;k<=av;k++)
          {
/* On teste ou la mettre plus haut dans le tableau tb*/
            topc= *(*ctb+niv-1);
            topd= *(*dtb+niv);
            if(topc>topd)
            {
/*SUCCES: On enleve cette lettre niv de la ligne j pour la mettre 
plus haut dans le tableau*/
              etat=1;fr=niv;
              (*(*btb+niv))--;
              (*baf)--;(*(*bnb_tb+niv))--;
              byam=yam+j;
              (*(*byam+niv))++;tp= *(*byam+niv);
              byam++;j++;
              for(;j<k;j++)
              {
                tp += *(*bnb_tb+niv-1);
                *(*byam+niv)=tp;bnb_tb++;byam++;
              }
/*bas est le numero de la lettre qu'on va placer*/
              bas=i+pos[niv-1];
              tmp= *(*bnb_tb+niv-1);
              bnb_tb++;
/*
La ieme lettre de valeur niv peut se placer a la ligne j. Ne pas la placer.
Le placement de cette ieme lettre et de ses suivantes se fait dans le case 1
*/
              ssetat=1;btb=tb+j;baf=af+j;
              break;
            }/*if(topc>topd)*/
            ctb++;dtb++;
          }/*for(k=j+1;k<=av;k++)*/
          if(etat==1)break;
          tp= *(*bnb_tb+niv);av=j;i-=tp;
          bnb_tb--;btb--;j--;baf--;
        }/*else du if(*(*bnb_tb+niv)==0)*/
      }/*while(i>0)*/
      if(etat==1)break;
      if(*(*(tb+lg_tb_dct)+niv-1)==0) lg_tb_dct--;
      niv--;
      break;/*Sortie du case 0*/

      case 1:
      
      if(ssetat==0)
      {
/*
On commence a placer la premiere lettre de valeur niv
*/
        i=1;j=niv;    /* premiere lettre niv*/
        btb=tb+j;byam=yam+j;baf=af+j;
        bnb_tb=nb_tb+j;
      }
/*j est forcement > 1*/
/*Essai de placer toutes les lettres niv de i a ev_niv*/
      ev_niv=ev[niv-1]; 
      while((j<=lg_tb_dct)||(i<=ev_niv))
      {
        topc= *(*(btb-1)+niv-1);
        topd= *(*btb+niv-1);
        tmp=topc-topd;
        ym= *(*(byam-1)+niv)+ *(*(bnb_tb-1)+niv-1);
        if((tmp>0)&&(ym>0))
        {
          if(tmp>ym)tmp=ym;
          dsp=ev_niv-i+1;
          if(tmp>dsp)tmp=dsp;
          *(*byam+niv) =ym-tmp;
          *(*bnb_tb+niv)=tmp;
          *(*btb+niv)=topd+tmp;
          *baf=topd+tmp;
          i+=tmp;
          if(j>lg_tb_dct)
          {
            lg_tb_dct++;
          }
        }
        else
        {
          *(*byam+niv)=ym;
          *(*btb+niv) =topd;
          *baf=topd;
          *(*bnb_tb+niv)=0;
        }
        btb++;bnb_tb++;byam++;baf++;j++;
      }

      topd= *(*btb+niv-1);
      for(;j<=lg_old;j++)
      {
        *(*btb+niv)=topd;
    btb++;
      }

      niv++;ssetat=0;
      break;/*Sortie de case 1*/
    }
    if(niv >nb_lt)
    {
      etat=0;
      if(lg_tb_dct<lg_old)
      {
        i=lg_tb_dct+1;
        btb=tb+i;
        bfi=fi+i-1;
        for(;i<=lg_fi;i++)
        {
          bpos= *btb+fr;
          for(j=fr;j<=nb_lt;j++)
            *bpos++ = *bfi;
          bfi++;btb++;
        }
        for(;i<=lg_old;i++)
        {
          bpos= *btb+fr;
          for(j=fr;j<=nb_lt;j++)
            *bpos++ = 0;
          btb++;
        }
      }
      lg_old=lg_tb_dct;
      *(af+lg_tb_dct+1)=0;
      *af=lg_tb_dct;
      niv--;
      bpc=pl[bas];
      ins_sch_lst(af,coef,&bpc);
      bpl=pl+bas;
      for(i=bas;i<=pds;i++)
        *bpl++ =bpc;
      bas=pds+1;cmt++;
    }
  }

  SYM_free(af);SYM_free(pos);
  btb=tb;byam=yam;bnb_tb=nb_tb;
  for(i=0;i<lg_tb+2;i++)
  {
    SYM_free(*byam);SYM_free(*bnb_tb);SYM_free(*btb);
   byam++;bnb_tb++;btb++;
  }
    SYM_free(*byam);SYM_free(*bnb_tb);SYM_free(*btb);
  SYM_free((signed char *)tb);SYM_free((signed char *)nb_tb);SYM_free((signed char *)yam);
/*CC 27/02 */
  SYM_free(pl);
  return lst1;
}


/*
Produit de sommes de fonctions de Schur
lst1 et lst2 sont des liste avec entete triees
lst2 n'est pas vide
Algo sophistique
*/
static INT fct_sch_prt_srt(lst1,lst2,mx,res)
struct liste *lst1,*lst2,*res;
signed char mx;
{
  struct liste *bp,*bnv1,*bnv2;

  lst1=lst1->suivant;
  bnv1=res;
  res->tab=(signed char *)SYM_calloc(2,1);*(res->tab)=99;
  while(lst1!=NULL)
  {
    bp=lst2->suivant;
    if(strcmp((char *) lst1->tab,(char *) bnv1->tab)>0)
      bnv1=proprt(lst1->tab,bp->tab,lst1->coef,bp->coef,mx,bnv1);
    else
      bnv1=proprt(lst1->tab,bp->tab,lst1->coef,bp->coef,mx,res);
    bnv2=bnv1;
    bp=bp->suivant;
    while(bp!=NULL)
    {
      if(strcmp((char *) lst1->tab,(char *) bnv2->tab)>0)
        bnv2=proprt(lst1->tab,bp->tab,lst1->coef,bp->coef,mx,bnv2);
      else
        bnv2=proprt(lst1->tab,bp->tab,lst1->coef,bp->coef,mx,res);
      bp=bp->suivant;
    }
    lst1=lst1->suivant;
  }
  return OK;
}


/*
met dans lst le produit de S_fi par S_ev
produit restreint aux partitions de longueur <=lg
lst est une liste a entete et peut ne pas etre vide (lst->suivant!= NULL)
retourne l'adresse de la
cellule precedent la premiere cellule de la liste qui a ete modifie
va plus vite si le poids de fi est superieur que le poids de ev
*/

static struct liste * pro_lg(fi,ev,coef1,coef2,lg,lst)
    INT coef1,coef2;
    signed char lg;
    signed char *fi,*ev;
    struct liste *lst;
{
  INT cmt;
  INT coef;
  signed char etat,ssetat,bas=0,ev_niv,ym;
  signed char nb_lt,lg_fi,lg_tb,lg_tb_dct,lg_tb_dct0=0,lg_old;
  signed char i,j=0,k,tmp,tp,dsp,topc,topd,pds,av,ttp=0,fr=0,niv0=0;
  register signed char niv;
  signed char sz_pcar,sz_plst,sz_lst;
  signed char **tb,**nb_tb,**ctb,**dtb;
  signed char **yam,**bbyam;
  register signed char **btb,**bnb_tb,**byam;
  signed char *af,*bfi,*bev,*baf,*pos,*bpos;
  struct liste **pl,**bpl,*bpc,*lst1;

  cmt=1L;
  nb_lt= 0;  /* Nombre de lettres*/
  baf=ev;
  while(*baf++) nb_lt++;
  lg_fi= 0;  /* Longueur de la forme interieure*/
  baf=fi;
  while(*baf++) lg_fi++;
  if((lg_fi >lg)||(nb_lt >lg))
  {
    return lst;
  }
  sz_pcar= sizeof(signed char *);  /* Dimension d'un pointeur sur caractere*/
  sz_plst= sizeof(struct liste *); /*Dimension de pointeur sur structure liste*/
  sz_lst= sizeof(struct liste);  /* Dimension sur structure liste*/
  lg_tb= lg_fi+nb_lt;  /* Longueur maximum des tableaux resultat*/

/*
Creation de 3 tableaux bidimensionnels avec pour nombre de lignes lg_tb
*/

  tb=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  nb_tb=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  yam=(signed char **)SYM_MALLOC((lg_tb+4)*sz_pcar);
  btb=tb;
  bnb_tb=nb_tb;byam=yam;
  for(i=0;i<=lg_tb+2;i++)
  {
    *btb++ =(signed char *)SYM_calloc(nb_lt+3,1);
    *bnb_tb++ =(signed char *)SYM_calloc(nb_lt+3,1);
    *byam++ =(signed char *)SYM_calloc(nb_lt+3,1);
  }
  *btb=NULL;*bnb_tb =NULL;*byam=NULL;

/*
Construction d'un tableau de taille lg_tb+3
*/

af=(signed char *)SYM_MALLOC(lg_tb+3);

/*
Creation d'un tableau de dimension nb_lt + 2
ou on met les sommes cumulees du vecteur d'evaluation
pds: poids de la partition composee des parts de la partition
*/

  pos=(signed char *)SYM_MALLOC(nb_lt+2);
  bpos=pos;
  *bpos++ =0; bev=ev;av=0;
  for(i=1;i<=nb_lt;i++)
  {
    *bpos = av+ *bev;
    av= *bpos;
    bev++;bpos++;
  }
  pds= *--bpos;


/*
Creation d'un tableau de pointeurs sur struct liste de dimension
pds pour l'inserion d'un tableau dans la liste des tableaux
*/

  pl=(struct liste **)SYM_MALLOC((pds+2)*sz_plst);


/*
Initialisation avant remplissage des tableaux
*/

  bnb_tb=nb_tb+1;
  bev=ev;
  btb=tb+1;
  byam=yam+1;
  av= *bev;
  if(lg_fi<nb_lt)
    lg_tb_dct=nb_lt;
  else
    lg_tb_dct=lg_fi;

  bfi=fi;
  baf=af+1;

/*
Remplissage des tableaux
*/

  for(i=1;i<=nb_lt;i++)
  {
    tp= *bev;tmp= *bfi;
    *(*bnb_tb+i)=tp;
    bpos= *btb;
    for(j=0;j<i;j++)
      *bpos++ =tmp;
    for(;j<=nb_lt+1;j++)
      *bpos++ =tmp+tp;
    *baf= *(bpos-1);
    if(i!=1)
    {
      bbyam=byam;
      tmp=av- tp;
      for(j=i;j<=lg_tb;j++)
      {
        *(*bbyam+i)=tmp;
        bbyam++;
      }
    }
    av= *bev;
    btb++;baf++;
    byam++;
    bev++;
    bnb_tb++;
    if(i<=lg_fi) bfi++;
  }

  for(; i<= lg_tb_dct;i++)
  {
    tmp= *bfi++;
    *baf++ =tmp;
    bpos= *btb;
    for(j=0;j<=nb_lt+1;j++)
      *bpos++ =tmp;
    btb++;
  }
  *baf=0;
  bpl=pl+1;
  for(i=1;i<=pds;i++)
    *bpl++ =lst;
  coef=coef1*coef2;
  *af=lg_tb_dct;
  ins_sch_lst(af,coef,&lst);
  lst1=lst;

/*
Debut de l'algorithme
*/
  niv=nb_lt;
  lg_old=lg_tb_dct;
  etat=0;ssetat=0;
  while(niv>0)
  {
    switch(etat)
    {
      case 0:
      
/*
Depilage: Essai de placer les lettres plus haut dans le tableau
*/
      
      ev_niv=ev[niv-1];
      if(ssetat==0)
      {
        baf=af+lg_tb_dct;
        btb=tb+lg_tb_dct;
        bnb_tb=nb_tb+lg_tb_dct;
        i= ev_niv;j=lg_tb_dct;
        av=lg_tb_dct+1;
      }
      else
      {
        ssetat=0;
        j=av-1;
        i=ttp;
        lg_tb_dct=lg_tb_dct0;
        baf=af+j;
        bnb_tb=nb_tb+j;
        btb=tb+j;
      }

      while(i>0)
      {
/*
Chaque lettre i de valeur niv est testee.
*/
        if(*(*bnb_tb+ niv)==0)
        {
          bnb_tb--;btb--;
          j--;baf--;
        }
        else
        {
          ctb=btb;dtb=btb+1;
          
          for(k=j+1;k<=av;k++)
          {
/* On teste ou la mettre plus haut dans le tableau tb*/
            topc= *(*ctb+niv-1);
            topd= *(*dtb+niv);
            if(topc>topd)
            {
              if(k >lg)
                break;
              else
              {
/*SUCCES: On enleve cette lettre niv de la ligne j pour la mettre 
plus haut dans le tableau*/
                etat=1;fr=niv;
                av=j;ttp=i- *(*bnb_tb+niv);
                (*(*btb+niv))--;
                lg_tb_dct0=lg_tb_dct;
                niv0=niv;
                (*baf)--;(*(*bnb_tb+niv))--;
                byam=yam+j;
                (*(*byam+niv))++;tp= *(*byam+niv);
                byam++;j++;
                for(;j<k;j++)
                {
                  tp += *(*bnb_tb+niv-1);
                  *(*byam+niv)=tp;bnb_tb++;byam++;
                }
/*bas est le numero de la lettre qu'on va placer*/
                bas=i+pos[niv-1];
                tmp= *(*bnb_tb+niv-1);
                bnb_tb++;
/*
La ieme lettre de valeur niv peut se placer a la ligne j. Ne pas la placer.
Le placement de cette ieme lettre et de ses suivantes se fait dans le case 1
*/
                ssetat=1;btb=tb+j;baf=af+j;
              }/*k>lg*/
              break;
            }/*if(topc>topd)*/
            ctb++;dtb++;
          }/*for(k=j+1;k<=av;k++)*/
          if(etat==1)break;
          tp= *(*bnb_tb+niv);av=j;i-=tp;
          bnb_tb--;btb--;j--;baf--;
        }/*else du if(*(*bnb_tb+niv)==0)*/
      }/*while(i>0)*/
      if(etat==1)break;
      if(*(*(tb+lg_tb_dct)+niv-1)==0) lg_tb_dct--;
      niv--;
      break;/*Sortie du case 0*/

      case 1:
      
      if(ssetat==0)
      {
/*
On commence a placer la premiere lettre de valeur niv
*/
        i=1;j=niv;    /* premiere lettre niv*/
        btb=tb+j;byam=yam+j;baf=af+j;
        bnb_tb=nb_tb+j;
      }
/*j est forcement > 1*/
/*Essai de placer toutes les lettres niv de i a ev_niv*/
      ev_niv=ev[niv-1]; 
      while((j<=lg_tb_dct)||(i<=ev_niv))
      {
        if(j>lg)
        {
          if(ttp>0)
          {
            etat=0;ssetat=1;niv=niv0;
          }
          else
          {
            etat=0; ssetat=0; niv=niv0-1;
            if(*(*(tb+lg_tb_dct0)+niv)==0)
              lg_tb_dct=lg_tb_dct0-1;
            else
              lg_tb_dct=lg_tb_dct0;
          }
          break;
        }
        topc= *(*(btb-1)+niv-1);
        topd= *(*btb+niv-1);
        tmp=topc-topd;
        ym= *(*(byam-1)+niv)+ *(*(bnb_tb-1)+niv-1);
        if((tmp>0)&&(ym>0))
        {
          if(tmp>ym)tmp=ym;
          dsp=ev_niv-i+1;
          if(tmp>dsp)tmp=dsp;
          *(*byam+niv) =ym-tmp;
          *(*bnb_tb+niv)=tmp;
          *(*btb+niv)=topd+tmp;
          *baf=topd+tmp;
          i+=tmp;
          if(j>lg_tb_dct)
          {
            lg_tb_dct++;
          }
        }
        else
        {
          *(*byam+niv)=ym;
          *(*btb+niv) =topd;
          *baf=topd;
          *(*bnb_tb+niv)=0;
        }
        btb++;bnb_tb++;byam++;baf++;j++;
      }/*while((j<=lg_tb_dct)||(i<=ev_niv))*/
      if(etat==0)
        break;

    topd= *(*btb+niv-1);
        for(;j<=lg_old;j++)
        {
        *(*btb+niv)=topd;
        btb++;
    }


      niv++;ssetat=0;
      break;/*Sortie de case 1*/
    }
    if(niv >nb_lt)
    {
      etat=0;
      if(lg_tb_dct<lg_old)
      {
        i=lg_tb_dct+1;
        btb=tb+i;
        bfi=fi+i-1;
        for(;i<=lg_fi;i++)
        {
          bpos= *btb+fr;
          for(j=fr;j<=nb_lt;j++)
            *bpos++ = *bfi;
          bfi++;btb++;
        }
        for(;i<=lg_old;i++)
        {
          bpos= *btb+fr;
          for(j=fr;j<=nb_lt;j++)
            *bpos++ = 0;
          btb++;
        }
      }
      lg_old=lg_tb_dct;
      *(af+lg_tb_dct+1)=0;
      *af=lg_tb_dct;

      niv--;
      bpc=pl[bas];
      ins_sch_lst(af,coef,&bpc);
      bpl=pl+bas;
      for(i=bas;i<=pds;i++)
        *bpl++ =bpc;
      bas=pds+1;cmt++;
    }
  }
  SYM_free(af);SYM_free(pos);
  btb=tb;byam=yam;bnb_tb=nb_tb;
  for(i=0;i<lg_tb+2;i++)
  {
    SYM_free(*byam);SYM_free(*bnb_tb);SYM_free(*btb);
    byam++;bnb_tb++;btb++;
  }
    SYM_free(*byam);SYM_free(*bnb_tb);SYM_free(*btb);
SYM_free((signed char *)tb);SYM_free((signed char *)nb_tb);SYM_free((signed char *)yam);
/*CC 27/02*/
  SYM_free(pl);

  return lst1;
}

/*
Produit de sommes de fonctions de Schur
le resultat res est tronque selon la longueur des partitions
lst1 et lst2 sont triees 
lst2 est non vide
*/

static INT fct_sch_lg_srt(lst1,lst2,lg,res)
struct liste *lst1,*lst2,*res;
signed char lg;
{
  register struct liste *bp;
  struct liste *bnv1,*bnv2;

  lst1=lst1->suivant;
  bnv1=res;
  while(lst1!=NULL)
  {
    bp=lst2->suivant;
    bnv1=pro_lg(lst1->tab,bp->tab,lst1->coef,bp->coef,lg,bnv1);
    bnv2=bnv1;
    bp=bp->suivant;
    while(bp!=NULL)
    {
      bnv2=pro_lg(lst1->tab,bp->tab,lst1->coef,bp->coef,lg,bnv2);
      bp=bp->suivant;
    }
    lst1=lst1->suivant;
  }
  return OK;
}

/*
Product of Schur functions S_{pa}*S_{pb}
pa and pb are partition objects.
*/

INT outerproduct_schur_lrs(pa,pb,c) OP pa,pb,c;
{
    OP prt,tmp,cf,v,d;
    signed char *va,*vb,*baf,*bva,*bvb;
    INT i,na,nb,lg,k;
    struct liste str,*lst,*bp;

    if(S_O_K(pa)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong first type");
    if(S_O_K(pb)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong second type");

    if(S_PA_LI(pa)==0L && S_PA_LI(pb)==0L)
    {
        if(not EMPTYP(c)) freeself(c);
        M_I_I(1L,c); return OK;
    }
    if(S_PA_LI(pa)==0L)
    {
        if(not EMPTYP(c)) freeself(c);
        m_skn_s(pb,cons_eins,NULL,c);
        return OK;
    }
    if(S_PA_LI(pb)==0L)
    {
        if(not EMPTYP(c)) freeself(c);
        m_skn_s(pa,cons_eins,NULL,c);
        return OK;
    }
    init(SCHUR,c);d=c;
    va=(signed char *)SYM_MALLOC(S_PA_LI(pa)+1L);
    vb=(signed char *)SYM_MALLOC(S_PA_LI(pb)+1L);
    na=0L;nb=0L;bva=va;bvb=vb;
    for(i=S_PA_LI(pa)-1L;i>=0L;i--)
    {
        *bva++ =(signed char) S_PA_II(pa,i);
        na++;
    }
    *bva=0;
    for(i=S_PA_LI(pb)-1L;i>=0L;i--)
    {
        *bvb++ =(signed char) S_PA_II(pb,i);
        nb++;
    }
    *bvb=0;
    str.suivant=NULL;
    if(na>nb)
        proprt(va,vb,1L,1L,99L,&str);
    else
        proprt(vb,va,1L,1L,99L,&str);
    lst=str.suivant;
    SYM_free(va); SYM_free(vb);
    while(lst!=NULL)
    {
        cf=callocobject();tmp=callocobject();
        M_I_I(lst->coef,cf);
        prt=callocobject();v=callocobject();
        baf=lst->tab;
        while(*baf)baf++;
        lg=(INT)(baf-lst->tab);
        m_il_v(lg,v);
        baf--;
        for(k=0L;k<lg-1L;k++)
        {
            M_I_I((INT)(*baf),S_V_I(v,k));
            baf--;
        }
        M_I_I((INT)(*baf),S_V_I(v,lg-1L));
        b_ks_pa(VECTOR,v,prt);
        b_skn_s(prt,cf,NULL,tmp);
        /*
        insert(tmp,c,add_koeff,comp_monomvector_monomvector);
        */
        c_l_n(d,tmp);d=tmp;
        /*
        add_apply(tmp,c);
        */
        SYM_free(lst->tab);
        bp=lst;
        lst=lst->suivant;
        SYM_free((char *)bp);
    }
    if(S_L_N(c)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(c);
            c_l_s(c,S_L_S(S_L_N(c)));
            c_l_n(c,S_L_N(S_L_N(c)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    return OK;
}


/*
Product of Schur functions S_{pa}*S_{pb}
restricted with parts <= mx
pa and pb are partition objects.
*/

INT mx_outerproduct_schur_lrs(mx,pa,pb,c) OP pa,pb,c,mx;
{
    OP prt,tmp,cf,v,d;
    signed char *va,*vb,*baf,*bva,*bvb;
    INT i,na,nb,lg,k;
    struct liste str,*lst,*bp;

    if(S_O_K(pa)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong first type");
    if(S_O_K(pb)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong second type");

    if(S_I_I(mx)<0L)
    {
        init(SCHUR,c);
        return OK;
    }
    
    if(S_PA_LI(pa)==0L && S_PA_LI(pb)==0L)
    {
        if(not EMPTYP(c)) freeself(c);
        M_I_I(1L,c); return OK;
    }
    if(S_PA_LI(pa)==0L)
    {
        if(S_PA_II(pb,S_PA_LI(pb)-1L)<=S_I_I(mx))
        {
            if(not EMPTYP(c)) freeself(c);
            m_skn_s(pb,cons_eins,NULL,c);
        }
        else
            init(SCHUR,c);
        return OK;
    }
    if(S_PA_LI(pb)==0L)
    {
        if(S_PA_II(pa,S_PA_LI(pa)-1L)<=S_I_I(mx))
        {
            if(not EMPTYP(c)) freeself(c);
            m_skn_s(pa,cons_eins,NULL,c);
        }
        else
            init(SCHUR,c);
        return OK;
    }
        
    init(SCHUR,c);d=c;
    str.suivant=NULL;
    va=(signed char *)SYM_MALLOC(S_PA_LI(pa)+1L);
    vb=(signed char *)SYM_MALLOC(S_PA_LI(pb)+1L);
    na=0L;nb=0L;bva=va;bvb=vb;
    for(i=S_PA_LI(pa)-1L;i>=0L;i--)
    {
        *bva++ =(signed char) S_PA_II(pa,i);
        na++;
    }
    *bva=0;
    for(i=S_PA_LI(pb)-1L;i>=0L;i--)
    {
        *bvb++ =(signed char) S_PA_II(pb,i);
        nb++;
    }
    *bvb=0;
    if(na>nb)
        proprt(va,vb,1L,1L,(signed char)S_I_I(mx),&str);
    else
        proprt(vb,va,1L,1L,(signed char)S_I_I(mx),&str);
    lst=str.suivant;
    SYM_free(va); SYM_free(vb);
    while(lst!=NULL)
    {
        cf=callocobject();tmp=callocobject();v=callocobject();
        M_I_I(lst->coef,cf);
        prt=callocobject();
        baf=lst->tab;
        while(*baf)baf++;
        lg=(INT)(baf-lst->tab);
        m_il_v(lg,v);
        baf--;
        for(k=0L;k<lg-1L;k++)
        {
            M_I_I((INT)(*baf),S_V_I(v,k));
            baf--;
        }
        M_I_I((INT)(*baf),S_V_I(v,lg-1L));
        b_ks_pa(VECTOR,v,prt);
        b_skn_s(prt,cf,NULL,tmp);
        c_l_n(d,tmp);d=tmp;

        SYM_free(lst->tab);
        bp=lst;
        lst=lst->suivant;
        SYM_free((char *)bp);
    }
    if(S_L_N(c)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(c);
            c_l_s(c,S_L_S(S_L_N(c)));
            c_l_n(c,S_L_N(S_L_N(c)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    return OK;
}


/*
Product of Schur functions S_{pa}*S_{pb}
restricted upon lengths <=le 
pa and pb are partition objects.
*/

INT l_outerproduct_schur_lrs(le,pa,pb,c) OP pa,pb,c,le;
{
    OP prt,tmp,cf,v,d;
    signed char *va,*vb,*baf,*bva,*bvb;
    INT i,na,nb,lg,k;
    struct liste str,*lst,*bp;

    if(S_O_K(pa)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong first type");
    if(S_O_K(pb)!= PARTITION)
        return error("outerproduct_schur_lrs: Wrong second type");

    if(S_I_I(le)<0L)
    {
        init(SCHUR,c);
        return OK;
    }
    
    if(S_PA_LI(pa)==0L && S_PA_LI(pb)==0L)
    {
        if(not EMPTYP(c)) freeself(c);
        M_I_I(1L,c); return OK;
    }
    if(S_PA_LI(pa)==0L)
    {
        if(S_PA_LI(pb)<=S_I_I(le))
        {
            if(not EMPTYP(c)) freeself(c);
            m_skn_s(pb,cons_eins,NULL,c);
        }
        else
            init(SCHUR,c);
        return OK;
    }
    if(S_PA_LI(pb)==0L)
    {
        if(S_PA_LI(pa)<=S_I_I(le))
        {
            if(not EMPTYP(c)) freeself(c);
            m_skn_s(pa,cons_eins,NULL,c);
        }
        else
            init(SCHUR,c);
        return OK;
    }
        
    init(SCHUR,c); d=c;
    str.suivant=NULL;
    va=(signed char *)SYM_MALLOC(S_PA_LI(pa)+1L);
    vb=(signed char *)SYM_MALLOC(S_PA_LI(pb)+1L);
    na=0L;nb=0L;bva=va;bvb=vb;
    for(i=S_PA_LI(pa)-1L;i>=0L;i--)
    {
        *bva++ =(signed char) S_PA_II(pa,i);
        na++;
    }
    *bva=0;
    for(i=S_PA_LI(pb)-1L;i>=0L;i--)
    {
        *bvb++ =(signed char) S_PA_II(pb,i);
        nb++;
    }
    *bvb=0;
    if(na>nb)
        pro_lg(va,vb,1L,1L,(signed char)S_I_I(le),&str);
    else
        pro_lg(vb,va,1L,1L,(signed char)S_I_I(le),&str);
    lst=str.suivant;
    SYM_free(va); SYM_free(vb);
    while(lst!=NULL)
    {
        cf=callocobject();tmp=callocobject();v=callocobject();
        M_I_I(lst->coef,cf);
        prt=callocobject();
        baf=lst->tab;
        while(*baf)baf++;
        lg=(INT)(baf-lst->tab);
        m_il_v(lg,v);
        baf--;
        for(k=0L;k<lg-1L;k++)
        {
            M_I_I((INT)(*baf),S_V_I(v,k));
            baf--;
        }
        M_I_I((INT)(*baf),S_V_I(v,lg-1L));
        b_ks_pa(VECTOR,v,prt);
        b_skn_s(prt,cf,NULL,tmp);
        c_l_n(d,tmp);d=tmp;
        SYM_free(lst->tab);
        bp=lst;
        lst=lst->suivant;
        SYM_free((char *)bp);
    }
    if(S_L_N(c)!=NULL)
    {
/*CC 24/01/97*/
            d=S_L_N(c);
            c_l_s(c,S_L_S(S_L_N(c)));
            c_l_n(c,S_L_N(S_L_N(c)));
            c_l_n(d,NULL);
            c_l_s(d,NULL);
            freeall(d);
    }
    return OK;
}

/*
The plethysmes S_n(S_I) of the different components of the 
Schur functions being in newton,
det computes the plethysm S_I(S_J) 
*/
static INT detr(ext,m,le,newton,boo,lst)
signed char m,le,*boo,*ext;
struct liste *lst,*newton;
{
  signed char i,j,sig,tmp,pds;
  struct liste lst1[1],lst2[1],*bp;

  lst1->suivant=NULL;
  lst2->suivant=NULL;
  i=1;j=1;
  while(i!= m+1)
  {
    if(boo[j]==0)
    {
      if(m==1)
      {
        tmp=le-j+ *(ext+le-1);
        lst->suivant=(newton+tmp)->suivant;
        return OK;
      }
      else
      {
        tmp=le-m+1-j+ *(ext+le-m);
        if(tmp < 0) return OK;
        if(i%2==1) sig=1;
        else sig= -1;
        boo[j]=1;
        detr(ext,m-1,le,newton,boo,lst1);
        boo[j]=0;
        if(tmp==0)
        {
          shuffle_sig(lst1,sig,lst);
          if(m!=2)
            free_lst(lst1);
          else
            lst1->suivant=NULL;
          return OK;
        }
        else
        {
          pds=poids(lst1);
          if(pds!=0)
          {
            if(booo==1)
            {
              if(poids(newton+tmp)< pds)
                fct_sch_prt_srt(lst1,newton+tmp,lng,lst2);
              else
                fct_sch_prt_srt(newton+tmp,lst1,lng,lst2);
            }
            else
            {
              if(poids(newton+tmp)<pds)
                fct_sch_lg_srt(lst1,newton+tmp,lng,lst2);
              else
                fct_sch_lg_srt(newton+tmp,lst1,lng,lst2);
            }

/*CC 04/03/97 */
            if(booo==1) SYM_free(lst2->tab);

            if(m!=2)
              free_lst(lst1);
            else
              lst1->suivant=NULL;
            if(lst->suivant!=NULL)
            {
              shuffle_sig(lst2,sig,lst);
              free_lst(lst2);
            }
            else
            {
              if (sig!=1)
              {
                bp=lst2->suivant;
                while(bp!=NULL)
                {
                  bp->coef= -bp->coef;
                  bp=bp->suivant;
                }
              }
              lst->suivant=lst2->suivant;
              lst2->suivant=NULL;
            }
          }
          i++;
        }
      }/*else du if(m==1)*/
    }/*if(boo[j]==0)*/
    j++;
  }
  return OK;
}

/*
conjugates the partition being in decreasing order (4 3 1 for example
gives  3 2 2 1)
*/

static INT cjg_rv(ttab) signed char **ttab;
{
  signed char *tab,*btab,*af,*baf;
  signed char lg,av,k,tp,j,tmp;

  tab= *ttab;
  lg= *tab;
  af=(signed char *)SYM_MALLOC(lg+1);
  baf=af+lg;
  *baf-- =0;
  btab=tab;
  av = *btab++;
  k=1;tp= *btab;
  while(tp)
  {
    if(av != tp)
    {
      tmp=av-tp;
      for(j=0;j<tmp;j++)
        *baf-- =k;
    }
    av= tp; k++;
    btab++;
    tp= *btab;
  }
  for(j=1;j<av;j++)
    *baf-- =k;
  *baf=k;
  *ttab=af;
  SYM_free(tab);
  return OK;
}

/*
Conjugates all the cells of a list with decreasing partition
*/

static INT cjg_rv_lst(lst)
struct liste *lst;
{
  lst=lst->suivant;
  while(lst!=NULL)
  {
    cjg_rv(&lst->tab);
    lst=lst->suivant;
  }
  return OK;
}

static INT pl_schur_schur(inn,ext,cond1,cond2,cond3,lst)
signed char *inn,*ext,cond1,cond2,cond3;
struct liste *lst;
{
  signed char mx,*bx,le,*boo;
  struct liste *newton;

  le= -1;
  bx=ext;
  while(*bx)
  {
    le++;bx++;
  }
  mx= *(bx-1)+le;
  newton=(struct liste *)SYM_MALLOC((mx+1)*sizeof(struct liste));
  plth2(inn,cond1,cond2,cond3,mx,newton);
  le++;
  boo=(signed char *)SYM_calloc(le+2,1);
  lst->suivant=NULL;
  if(cond3==1)
  {
    if(booo==1) booo=0;
    else booo=1;
  }
  detr(ext,le,le,newton,boo,lst);

/*
printf("booo %d le %d mx %d *(ext) %d\n",booo,le,mx,*ext);
*/

/* CC 24/01/97 */
  if(le==1)
    free_newton(newton, mx-1);
  else
/* CC 27/02/97 */
    free_newton(newton, mx);

  SYM_free(newton);
  if(cond3==1)
  {
    if(booo==1) booo=0;
    else booo=1;
  }
  if(booo==1) cjg_rv_lst(lst);
  SYM_free(boo);
  return OK;
}

static INT cc_plethysm(m,otab,cond1,ores)
    signed char m,cond1; OP  otab,ores;
{
  OP sc,ve,pa,cf;
  signed char  tab[20];
  signed char  *s,*bs,*btab,*baf,*af,*bch,*tab1;
  signed char  condition,parite,mx,np,npt,le,inv;
  INT   cof;
  INT  c;
  signed char  n,in;
  signed char  k;
  signed char  cond,cond2,high,mid;
  register signed char  i,j,temp;
  struct  liste str,*newton,*bp,*liste,*liste1;

for (i=0;i<20;i++) tab[(int)i]=0;

  inv = 0;
  le = (signed char)S_PA_LI(otab);
  if(le > 19)
  {
    fprintf(stderr,"partition too long\n");
    exit(inv);
  }
  btab = tab;
  mx = 0;
  for(c = 0L; c < le; c++)
  {
    *btab = (signed char)S_PA_II(otab,c);
    mx += *btab++;
  }
  if(( le * mx) > 127)
  {
    fprintf(stderr,"too big plethysm for my little structures\n");
    exit(inv);
  }
  *btab = 0;
  cond2 = 0;


  newton = (struct liste *)SYM_MALLOC( (m+1) * sizeof(struct liste) );
  if(*(btab - 1) < le)
  {
    inv = 1;
    tab1 = (signed char *)SYM_MALLOC(*(btab - 1) + 1);
    bs = tab1;
    btab = tab;
    af = (signed char *)SYM_MALLOC(le + 1);
    baf = af;
    while(*btab != 0)
      *baf++ = *btab++;
    *baf = 0;

    cond = -1;
    j = le - 1;
    btab = af + j;
    mid = *btab;
    j++;
    temp = 0;
    while(j >=  0)
    {
      high = 0;
      while(*btab == mid)
      {
        j--;
        high++;
        if(j == 0)
        {
          *btab = 0;
          j--;
          break;
        }
        btab--;
      }
      temp = temp+high;
      for(i = *btab;i < mid;i++)
      {
        cond++;
        *bs++ = temp;
      }
      mid = *btab;
    }
    *bs = 0;
    SYM_free(af);
  }
  else
  {
    tab1 = (signed char *)SYM_MALLOC(le + 1);
    btab = tab;
    bch = tab1;
    while(*btab != 0)
      *bch++ = *btab++;
    *bch = 0;
  }

  booo = 0;
  if((( cond2 == 0) && (inv == 0)) || ((cond2 == 1) && (inv == 1)))
    booo = 1;
  if(cond2 == 0)
  {
    if(lng < le)
    {
      fprintf(stderr,"No elements of the length %d in this plethysm\n",m);
      exit(inv);
    }
  }
  else
    if(lng < *(tab + le - 1))
    {
      fprintf(stderr,"No elements of the length %d in this plethysm\n",m);
      exit(inv);
    }



  liste1 = &str;

  if ( cond2 == 0)

    if(cond1 == 0)

      if((mx%2 == 0) || ((mx%2 == 1)&&(inv == 1)))
        condition = 0;
      else

        condition = 1;
    else

      if((mx%2 == 0) || ((mx%2 == 1)&&(inv == 1)))
        condition = 1;
      else
        condition = 0;
  else

    if(cond1 == 0)
      if((inv == 0) || ((inv == 1) && (mx%2 == 0)))
        condition = 0;
      else

        condition = 1;
    else
      if((inv == 0) || ((inv == 1) && (mx%2 == 0)))
        condition = 1;
      else

        condition = 0;
      liste = (struct liste *)SYM_MALLOC(sizeof(struct liste));
      liste->coef = 1L;
      liste->suivant = NULL;
      liste1->suivant = liste;
      bs = (signed char *)SYM_MALLOC(1);
    if (bs == NULL)
        return no_memory();
      liste->tab = bs;
      *bs = (signed char) 0;
      (newton)->suivant = liste1->suivant;

  for(n = 1;n <=  m;n++)
  {
    liste1->suivant = NULL;
    np = n * mx;
    npt = np;
    if( n == 1)
    {
      liste = (struct liste *)SYM_MALLOC(sizeof(struct liste));
      liste->coef = 1L;
      liste->suivant = NULL;
      liste1->suivant = liste;
      if (inv == 0)
      {
        bs = (signed char *)SYM_calloc(tab[le - 1] + 1,sizeof(char));
        liste->tab = bs;
        btab = tab;
        af = (signed char *)SYM_calloc(le + 1,sizeof(char));
        baf = af;
        while(*btab != (signed char)0)
          *baf++ = *btab++;
        *baf = (signed char)0;

        cond = (signed char)-1;
        j = le - 1;
        btab = af + j;
        mid = *btab;
        j++;
        temp = (signed char)0;
        while(j >=  (signed char)0)
        {
          high = (signed char)0;
          while(*btab == mid)
          {
            j--;
            high++;
            if(j == (signed char)0)
            {
              *btab = (signed char)0;
              j--;
              break;
            }
            btab--;
          }
          temp = temp+high;
          for(i = *btab;i < mid;i++,bs++)
          {
            cond++; 
            *bs = temp; 
          }
          mid = *btab;
        }
        *bs = 0;
        temp = mx - 1;
        bs--;
        for(i = 0 ;i <= cond; i++)
        {
          (*bs) += temp;
          temp--;
          if(i != cond)
            bs--;
        }
        if(bs == NULL)
          return OK;
        SYM_free(af); 

      }
      else
      {
        liste->tab = (signed char *)SYM_MALLOC(le + 1);
        bs = liste->tab + le;
        *bs-- = 0;
        btab = tab + le - 1;
        temp = mx - 1;
        for(i = 1 ;i <= le; i++)
        {
          *bs  = *btab + temp;
          temp--;
          if(i != le)
          {
            btab--;
            bs--;
          }
        }
      }
    }
    else
    {
      for(in = 0;in < n;in++)
      {


        if(condition == 1)
        {
          i = (n+1+in)%2;
          if(i == 0)
            parite = 1;
          else
            parite = -1;
        }
        else
          parite = 1;


        liste = (newton+in)->suivant;

        while(liste != NULL)
        {
          baf = liste->tab;
          temp = np - npt;
          s = (signed char *)SYM_MALLOC(temp + 1);
          if(temp != 0)
          {
            temp--;
            j = 0;
            while(*baf != '\0')
            {
              j++;
              baf++;
            }

            baf--;
            btab = s + j;
            *btab-- = 0;
            for(k = j-1;k >= 0;k--)
            {
              *btab = (*baf) - temp;
              if(k != 0)
              {
                btab--;
                baf--;
                temp--;
              }
            }
          }
          else
            *s  = '\0';

          cof = liste->coef;
          gvr = 0;

          calcul(tab1,(int) n - in,s,liste1,cof,parite,n);


          SYM_free(s); /* AK 181291 */ 
          liste = liste->suivant;
        }
        npt = npt - mx;

      }
    /* End of the loop for (in = 0;in < n ;in++) */

    }
    liste = liste1->suivant;

    while(liste != NULL)
    {
      liste->coef = liste->coef/n;
      liste = liste->suivant;
    }

    (newton + n)->suivant = liste1->suivant;

  }

  /* End of the loop with n*/
  liste = newton + 1;

  /*START  OF  THE  THIRD  PART  WRITING IN THE LIST ores*/

  for(in = 1;in < m;in++)
  {
    bp = liste->suivant;
    while(bp != NULL)
    {
       SYM_free(bp->tab); 
      liste1 = bp;
      bp = bp->suivant;
       SYM_free((signed char *)liste1); 
    }
    /*liste1 = liste; Suppress */
    liste++;
    /* SYM_free((signed char *)liste1);  AK 140192 wg sun */
  }
  bp = liste->suivant;
  k = in * mx;
  init(SCHUR,ores); /* d=ores; */

  while(bp != NULL)
  {
    btab = bp->tab;
    j = -1;
    while(*btab  !=  '\0')
    {
      btab++;
      j++;
    }
    btab--;
    temp = k-1;

    for(i = j;i >=  0;i--)
    {
      (*btab--)  -= temp;
      temp--;
    }

    /*ALLOCATION OF A NEW MEMORY FOR THE VECTOR ve AND THE SCHUR FUNCTION sc.
    THE RESULT ores */

    sc = callocobject(); ve = callocobject();
    pa=callocobject(); cf=callocobject();

    if(booo == 1) 
    conjug( bp->tab , j , ve);
    else
    {
      btab = bp->tab;
      m_il_v( (INT)(j+1), ve );
      for(i = 0; i<=j ;i++)
      {
        M_I_I( (INT)(*btab), S_V_I(ve, (INT) i));
        btab++;
      }
    }
    b_ks_pa(VECTOR,ve,pa);
    M_I_I(bp->coef,cf);
    b_skn_s(pa,cf,NULL,sc);
    insert(sc,ores,NULL,NULL); /* AK 151298 */

    SYM_free(bp->tab);
    liste1 = bp;
    bp = bp->suivant;
    SYM_free((signed char *)liste1);
  }


  SYM_free(tab1);


/*CC 24/01/97*/
  SYM_free(newton->suivant->tab); SYM_free(newton->suivant);
  SYM_free((signed char *)newton);

  return OK;
}

static INT t_list_coef_SYM(lst,cof,np,res)
    struct liste * lst; OP res,cof;signed char np;
{
  signed char lg; 
  register signed char *baf,i;
  struct liste *q;
  OP pol,pa,v,cf,d;

  lst=lst->suivant;
  init(SCHUR,res);
    d=res;
  while(lst!=NULL)
  {
    pol=callocobject(); 
    v=callocobject();
    pa=callocobject();
    cf=callocobject();
    baf=lst->tab;
    while(*baf) baf++;
    lg=(INT)(baf-lst->tab);
    m_il_v((INT)lg,v);
    i=np;
    baf--;
    for(;;)
    {
      *baf -=i;
      if(baf==lst->tab) break;
      i--;baf--;
    }

    for(i=0;i<lg-1L;i++)
    {
      M_I_I((INT)(*baf),S_V_I(v,i));
      baf++;
    }
    M_I_I((INT)(*baf),S_V_I(v,i));
    b_ks_pa(VECTOR,v,pa);
    M_I_I((INT)lst->coef,cf);mult_apply(cof,cf);
    b_skn_s(pa,cf,NULL,pol);
    c_l_n(d,pol);d=pol;
    q=lst;
    lst=lst->suivant;
    SYM_free(q->tab);
    SYM_free((char *)q);
  }
  if(S_L_N(res)!=NULL)
  {
/*CC 24/01/97*/
    d=S_L_N(res);
    c_l_s(res,S_L_S(S_L_N(res)));
    c_l_n(res,S_L_N(S_L_N(res)));
    c_l_n(d,NULL);
    c_l_s(d,NULL);
    freeall(d);
  }
  return OK;
}



static INT t_list_SYM(lst,res)struct liste * lst; OP res;
{
  signed char lg; 
  register signed char *baf,i;
  struct liste *q;
  OP pol,pa,v,cf,d;

  lst=lst->suivant;
  init(SCHUR,res);
    d=res;
  while(lst!=NULL)
  {
    pol=callocobject(); 
    v=callocobject();
    pa=callocobject();
    cf=callocobject();
    baf=lst->tab;
    while(*baf) baf++;
    lg=baf-lst->tab;
    m_il_v((INT)lg,v);
    baf--;

    for(i=0;i<lg-1L;i++)
    {
      M_I_I((INT)(*baf),S_V_I(v,i));
      baf--;
    }
    M_I_I((INT)(*baf),S_V_I(v,i));
    b_ks_pa(VECTOR,v,pa);
    M_I_I((INT)lst->coef,cf);
    b_skn_s(pa,cf,NULL,pol);
    c_l_n(d,pol);d=pol;
    q=lst;
    lst=lst->suivant;
    SYM_free(q->tab);
    SYM_free((char *)q);
  }
  if(S_L_N(res)!=NULL)
  {
/*CC 24/01/97*/
    d=S_L_N(res);
    c_l_s(res,S_L_S(S_L_N(res)));
    c_l_n(res,S_L_N(S_L_N(res)));
    c_l_n(d,NULL);
    c_l_s(d,NULL);
    freeall(d);
  }
  return OK;
}

/*
a= \sum  n_I*S_I => a= \sum n_I*S_I\tilde
*/

/*
The partitions of the a=\sum n_I*S_I
are put in its growing order
*/

INT growingorder_schur(a) OP a;
{
    OP z,ap,b;
    b=callocobject();init(SCHUR,b);
    if(S_O_K(a) == SCHUR)
    {
        if(not nullp(a))
        {
            z=S_L_N(a);
            c_l_s(b,S_L_S(a));
            while(z!=NULL)
            {
                ap=S_L_N(z);
                C_L_N(z,NULL);
                insert(z,b,add_koeff,comp_monomvector_monomvector);
                z=ap;
            }
            c_l_s(a,s_l_s(b));
            c_l_n(a,s_l_n(b));

        }
    }
    return OK;
}


INT l_complete_schur_plet(olng,b,c,res) OP  c,res,olng,b;
/*l_complete_schur_plet COMPUTES THE TERMS OF S_n(S_I) LESS THAN lng.*/
/* result is of type SCHUR */
/* CC 1996 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"l_complete_schur_plet(1)",olng);
    CTO(INTEGER,"l_complete_schur_plet(2)",b);
    CTTO(PARTITION,INTEGER,"l_complete_schur_plet(3)",c);
    {
    OP part_inn,tmp;
    if(S_I_I(olng)<0L)
        {
        init(SCHUR,res);
        }
    else if(S_I_I(b)==0L)
        {
        erg += m_scalar_schur(cons_eins,res);
        }
    else if(S_I_I(b)<0L)
        {
        init(SCHUR,res);
        }
    else if ( (S_O_K(c)==INTEGER)&&(S_I_I(c)<=0L))
        {
        init(SCHUR,res);
        }
    else 
        {
        part_inn=callocobject();
        if(S_O_K(c)==INTEGER)
                {
                erg += m_i_pa(c,part_inn);
                }
        else
                {
                COPY(c,part_inn);
                }

        lng = (signed char)(S_I_I(olng));
        FREESELF(res);
        if(lng<S_PA_LI(part_inn))
                {
                init(SCHUR,res);
                }
        else
                {
                erg += cc_plethysm((signed char)(S_I_I(b)),
                                   part_inn,(signed char)0,res);
                lng = 127;
                }
        FREEALL(part_inn);
        }
    }
    ENDR("l_complete_schur_plet");
}


INT complete_schur_plet(om,otab,res) OP  otab,res,om;
/* CC 220596 */
/* AK 210704 V3.0 */
{
        INT erg = OK;
        CTO(INTEGER,"complete_schur_plet(1)",om);
        CTTO(PARTITION,INTEGER,"complete_schur_plet(2)",otab);
        {
        OP lgo=callocobject();
        M_I_I(127L,lgo);
        erg += l_complete_schur_plet(lgo,om,otab,res);
        FREEALL(lgo);
        }
        ENDR("complete_schur_plet");
}


/*l_elementary_schur_plet COMPUTES THE TERMS OF L_n(S_I)
LESS THAN lng.*/

INT l_elementary_schur_plet(olng,b,c,res) OP  c,res,olng,b;
{
    INT erg = OK;
    OP part_inn,tmp;

    CTO(INTEGER,"l_elementary_schur_plet",olng);
    CTO(INTEGER,"l_elementary_schur_plet",b);
    CTTO(INTEGER,PARTITION,"l_elementary_schur_plet",b);

    if(S_I_I(olng)<0L)
    {
        erg += init(SCHUR,res);
        goto endr_ende;
    }
    if(S_I_I(b)==0L)
    {
        erg += m_i_i(1L,res);
        goto endr_ende;
    }
    if(S_I_I(b)<0L)
    {
        erg += init(SCHUR,res);
        goto endr_ende;
    }

    if(S_O_K(c)==INTEGER)
        {
                if(S_I_I(c)<=0L)
                {
                        erg += init(SCHUR,res); 
            goto endr_ende;
                }
        part_inn=callocobject();
        tmp=callocobject();
        erg += m_il_v(1L,tmp);
        M_I_I(S_I_I(c),S_V_I(tmp,0L));
        erg += b_ks_pa(VECTOR,tmp,part_inn);
    }
        else
        {
                part_inn=callocobject();
                erg += copy(c,part_inn);
        }

      lng = (signed char)(S_I_I(olng));
        if(lng<S_PA_LI(part_inn))
        {
                erg += freeall(part_inn);
                erg += init(SCHUR,res);
                goto endr_ende;
        }
        if(not EMPTYP(res)) 
        erg += freeself(res);

      erg += cc_plethysm((signed char)(S_I_I(b)),part_inn,(signed char)1,res);
    erg += freeall(part_inn);
      lng = 127;
     ENDR("l_elementary_schur_plet");
}


INT elementary_schur_plet(om,otab,ores) OP  otab,ores,om;
/* CC 220596 */
{
        OP lgo;
        lgo=callocobject();
        M_I_I(127L,lgo);
        l_elementary_schur_plet(lgo,om,otab,ores);
        freeall(lgo);
        return OK;
}


INT l_complete_complete_plet(lgo,om,c,ores) OP  lgo,c,ores,om;
/* CC 220596 */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGER,"l_complete_complete_plet(1)",lgo);
    CTO(INTEGER,"l_complete_complete_plet(2)",om);
    CTO(INTEGER,"l_complete_complete_plet(3)",c);
    {
    erg += l_complete_schur_plet(lgo,om,c,ores);
    }
    ENDR("l_complete_complete_plet");
}


INT complete_complete_plet(om,otab,ores) OP  otab,ores,om;
/* CC 220596 */
{
    INT erg = OK;
    OP c,lgo;

    CTO(INTEGER,"complete_complete_plet(1)",om);
    CTO(INTEGER,"complete_complete_plet(2)",otab);
    
    c = callocobject();
    lgo=callocobject();
    erg += m_i_pa(otab,c);
    M_I_I(127L,lgo);
    erg += l_complete_schur_plet(lgo,om,c,ores);
    erg += freeall(c);
    erg += freeall(lgo);
    CTO(SCHUR,"complete_complete_plet(3-ende)",ores);
    ENDR("complete_complete_plet");
}



INT l_schur_schur_plet(a,b,c,res)OP a,b,c,res;
{
    signed char *binn,*bext,*inn,*ext,boo1,cond1;
    OP part_inn, part_ext,tmp;
    char lext,linn,i;
    struct liste lst[1];
    INT erg = OK;
    CTO(INTEGER,"l_schur_schur_plet(1)",a);
    CTTO(PARTITION,INTEGER,"l_schur_schur_plet(2)",b);
    CTTO(PARTITION,INTEGER,"l_schur_schur_plet(3)",c);



    if(S_I_I(a)<0L)
    {
        init(SCHUR,res);
        return OK;
    }

    if ((S_O_K(b) == PARTITION) && (S_PA_LI(b) == 1))
        { 
        return (l_complete_schur_plet(a,S_PA_I(b,0),c,res));
        }

    if(S_O_K(b)==INTEGER)
        return (l_complete_schur_plet(a,b,c,res));

    if(S_O_K(c)==INTEGER)
    {
        if(S_I_I(c)<=0L)
        {
            init(SCHUR,res); return OK;
        }
        part_inn=callocobject();
        tmp=callocobject();
        m_il_v(1L,tmp);
        M_I_I(S_I_I(c),S_V_I(tmp,0L));
        b_ks_pa(VECTOR,tmp,part_inn);
    }
    else
    {
        part_inn=callocobject();
        copy(c,part_inn);
    }
    part_ext=callocobject();
    copy(b,part_ext);
    lng=(signed char)S_I_I(a);    
    linn=(signed char)S_PA_LI(part_inn);
    lext=(signed char)S_PA_LI(part_ext);
    if(lext==0)
    {
        freeall(part_inn);freeall(part_ext);
        m_i_i(1L,res);
        return OK;
    }
    if(lng<linn)
    {
        freeall(part_inn);freeall(part_ext);
        init(SCHUR,res);
        return OK;
    }
    if(linn== 0)
    {
        freeall(part_inn);freeall(part_ext);
        init(SCHUR,res);
        return OK;
    }
    lext=(signed char)S_PA_LI(part_ext);
    ext=(signed char*)SYM_MALLOC(lext+1L);
    bext=ext;
    for(i=0;i<lext;i++)
        *bext++ = (signed char)S_PA_II(part_ext,i);
    *bext=0;

    inn=(signed char*)SYM_MALLOC(linn+1L);
    binn=inn;
    for(i=0;i<linn;i++)
        *binn++ = (signed char)S_PA_II(part_inn,i);
    *binn=0;

      boo1= *(bext-1);
      bext=ext;cond1=0;
      if(boo1<lext)
      {
            lext--;
            cond1=1;
            plet_conj(&bext,&lext);
      }
    if(not EMPTYP(res)) freeself(res);
    pl_schur_schur(inn,bext,cond1,0,0,lst);

    t_list_SYM(lst,res);

    freeall(part_inn);
    freeall(part_ext);
    SYM_free(inn); SYM_free(bext);
    return OK;
    ENDR("l_schur_schur_plet");
}


INT schur_schur_plet(part_ext,part_inn,res) OP part_ext,part_inn,res;
/* CC */
/* AK 251198 V2.0 */
{
    OP lgo;
    INT erg = OK;
    CTTO(INTEGER,PARTITION,"schur_schur_plet(1)",part_ext);
    CTTO(PARTITION,INTEGER,"schur_schur_plet(2)",part_inn);
    lgo=callocobject();
    M_I_I(127,lgo);
    erg += l_schur_schur_plet(lgo,part_ext,part_inn,res);
    erg += freeall(lgo);
    ENDR("schur_schur_plet");
}

/*
computes in res the decomposition of the plethysm
S_b(S_c) for parts <=a.
*/

INT mx_schur_schur_plet(a,b,c,res) OP a,b,c,res;
{
    signed char *binn,*bext,*inn,*ext,boo1,cond1;
    OP part_inn, part_ext,tmp;
    char lext,linn,i;
    struct liste lst[1];

    if(S_O_K(a)!=INTEGER)
        return error("mx_schur_schur_plet: wrong first type");

    if(S_O_K(b)!=INTEGER && S_O_K(b)!=PARTITION)
        return error("mx_schur_schur_plet: wrong second type");

    if(S_O_K(c)!=INTEGER && S_O_K(c)!=PARTITION)
        return error("mx_schur_schur_plet: wrong third type");

    if(S_I_I(a)<0L)
    {
        init(SCHUR,res);
        return OK;
    }
    if(S_O_K(b)==INTEGER)
    {
        if(S_I_I(b)<0L)
        {
            init(SCHUR,res);
            return OK;
        }
        if(S_I_I(b)==0L)
        {
            if(not EMPTYP(res)) freeself(res);
            M_I_I(1L,res);return OK;
        }
    }
    
    if(S_O_K(c)==INTEGER)
    {
        if(S_I_I(c)<=0L)
        {
            init(SCHUR,res); return OK;
        }
        part_inn=callocobject();
        tmp=callocobject();
        m_il_v(1L,tmp);
        M_I_I(S_I_I(c),S_V_I(tmp,0L));
        b_ks_pa(VECTOR,tmp,part_inn);
    }
    else
    {
        part_inn=callocobject();
        copy(c,part_inn);
    }
    part_ext=callocobject();
    copy(b,part_ext);
    lng=(signed char)S_I_I(a);    
    linn=(signed char)S_PA_LI(part_inn);
    lext=(signed char)S_PA_LI(part_ext);
    if(lext==0)
    {
        if(not EMPTYP(res)) freeself(res);
        freeall(part_inn);freeall(part_ext);
        M_I_I(1L,res);
        return OK;
    }
    if(lng<S_PA_II(part_inn,linn-1L))
    {
        freeall(part_inn);freeall(part_ext);
        init(SCHUR,res);
        return OK;
    }
    if(linn== 0)
    {
        freeall(part_inn);freeall(part_ext);
        init(SCHUR,res);
        return OK;
    }
    lext=(signed char)S_PA_LI(part_ext);
    ext=(signed char*)SYM_MALLOC(lext+1L);
    bext=ext;
    for(i=0;i<lext;i++)
        *bext++ = (signed char)S_PA_II(part_ext,i);
    *bext=0;

    inn=(signed char*)SYM_MALLOC(linn+1L);
    binn=inn;
    for(i=0;i<linn;i++)
        *binn++ = (signed char)S_PA_II(part_inn,i);
    *binn=0;

      boo1= *(bext-1);
      bext=ext;cond1=0;
      if(boo1<lext)
      {
            lext--;
            cond1=1;
            plet_conj(&bext,&lext);
      }
    if(not EMPTYP(res)) freeself(res);
    pl_schur_schur(inn,bext,cond1,0,1,lst);

    t_list_SYM(lst,res);

    SYM_free(inn);SYM_free(bext);
    freeall(part_inn);freeall(part_ext);
    return OK;
}

INT mx_power_schur_plet(mx,a,b,c) OP mx,a,b,c;
/*
res is \psi_a(S_b) and restricts the result to partitions which biggest part
is <= mx
*/

{
    OP on,os;
    if(S_O_K(mx)!=INTEGER) return error("mx_power_schur_plet: wrong first type");
    lng=S_I_I(mx);
    on=callocobject(); os=callocobject();
    m_il_v(0L,on); b_ks_pa(VECTOR,on,os);
    plth1(os,a,b,1,c);
    freeall(os); return OK;
}



INT l_power_schur_plet(ol,a,b,c) OP ol,a,b,c;

/*
res is \psi_a(S_b) and restricts the result to partitions of length < ol
*/

{
    OP on,os;
    if(S_O_K(ol)!=INTEGER) return error("l_power_schur_plet: wrong first type");
    lng=S_I_I(ol);
    on=callocobject(); os=callocobject();
    m_il_v(0L,on); b_ks_pa(VECTOR,on,os);
    plth1(os,a,b,0,c);
    freeall(os); return OK;
}

INT power_schur_plet(a,b,c) OP a,b,c;
/* res is \psi_a(S_b) */
{
    OP on,os;
    INT erg = OK;
    CTO(INTEGER,"power_schur_plet",a);

    on=callocobject(); os=callocobject();
    erg += m_il_v(0L,on); 
    erg += b_ks_pa(VECTOR,on,os);
    lng=127;
    plth1(os,a,b,0,c);
    erg += freeall(os); 
    ENDR("power_schur_plet");
}


INT schur_power_schur_plet_mult(a,b,c,d) OP a,b,c,d;

/*
res is S_a* \psi_b(S_c)
*/

{
    lng=127;
    plth1(a,b,c,0,d);
    return OK;
}

INT l_schur_power_schur_plet_mult(ol,a,b,c,d) OP ol,a,b,c,d;

/*
res is S_a* \psi_b(S_c) for length <=a
*/

{
    if(S_O_K(ol)!=INTEGER) return error("l_schur_power_schur_plet: wrong first type");
    lng=S_I_I(ol);
    plth1(a,b,c,0,d);
    return OK;
}

INT mx_schur_power_schur_plet_mult(ol,a,b,c,d) OP ol,a,b,c,d;

/*
res is S_a* \psi_b(S_c) in the basis of Schur functions with parts <=a.
*/

{
    if(S_O_K(ol)!=INTEGER) return error("l_schur_power_schur_plet: wrong first type");
    lng=S_I_I(ol);
    plth5(a,b,c,1,d);
    return OK;
}

INT schur_powerproduct_schur_plet_mult(a,b,c,d) OP a,b,c,d;

/*
res is S_a* \psi_b(S_c) where a,b,c are partitions
*/

{
    lng=127;
    plth5(a,b,c,0,d);
    return OK;
}

INT l_schur_powerproduct_schur_plet_mult(ol,a,b,c,d) OP ol,a,b,c,d;

/*
res is S_a* \psi_b(S_c) for length <=a, with a,b,c partitions
*/

{
    if(S_O_K(ol)!=INTEGER) return error("l_schur_power_schur_plet: wrong first type");
    lng=S_I_I(ol);
    plth5(a,b,c,0,d);
    return OK;
}

INT mx_schur_powerproduct_schur_plet_mult(ol,a,b,c,d) OP ol,a,b,c,d;

/*
res is S_a* \psi_b(S_c) in the basis of Schur functions with parts <=a,
with a,b,c partitions.
*/

{
    if(S_O_K(ol)!=INTEGER) return error("l_schur_power_schur_plet: wrong first type");
    lng=S_I_I(ol);
    plth5(a,b,c,1,d);
    return OK;
}
/*
puts in c the decomposition of the plethysm  \psi^a(s_b)
in the basis of Schur functions.
a and b are partition or integer objects.
*/

INT powerproduct_schur_plet(a,b,c) OP a,b,c;
{
    lng=127;
    return plth3(a,b,0,c);
}

/*
puts in c the decomposition of the plethysm  \psi^a(s_b)
in the basis of Schur functions restricted upon the length <= ol.
a and b are partition or integer objects.
*/

INT l_powerproduct_schur_plet(ol,a,b,c) OP a,b,c,ol;
{
    if(S_O_K(ol) != INTEGER)
        return error ("l_powerproduct_schur_plet: Wrong first type");
    lng=S_I_I(ol);
    plth3(a,b,0,c);
    return OK;
}

/*
puts in c the decomposition of the plethysm  \psi^a(s_b)
in the basis of Schur functions restricted upon the parts <= mx.
a and b are partition or integer objects.
*/

INT mx_powerproduct_schur_plet(mx,a,b,c) OP a,b,c,mx;
{
    if(S_O_K(mx) != INTEGER)
        return error("mx_powerproduct_schur_plet: Wrong first type");
    lng=S_I_I(mx);
    plth3(a,b,1,c);
    return OK;
}

/*
puts in c the decomposition of the plethysm  S_a(s_b)
in the basis of Schur functions.
a and b are partition or integer objects.
*/

INT schur_schur_pletbis(a,b,c) OP a,b,c;
{
    lng=127;
    plth4(a,b,0,c);
    return OK;
}

/*
puts in c the decomposition of the plethysm  S_a(s_b)
in the basis of Schur functions restricted upon the length <= ol.
a and b are partition or integer objects.
*/

INT l_schur_schur_pletbis(ol,a,b,c) OP a,b,c,ol;
{
    if(S_O_K(ol) != INTEGER)
        return error ("l_schur_schur_pletbis: Wrong first type");
    lng=S_I_I(ol);
    plth4(a,b,0,c);
    return OK;
}

/*
puts in c the decomposition of the plethysm  S^a(s_b)
in the basis of Schur functions restricted upon the parts <= mx.
a and b are partition or integer objects.
*/

INT mx_schur_schur_pletbis(mx,a,b,c) OP a,b,c,mx;
{
    if(S_O_K(mx) != INTEGER)
        return error("mx_schur_schur_pletbis: Wrong first type");
    lng=S_I_I(mx);
    plth4(a,b,1,c);
    return OK;
}

INT power_schur_plet_old(jvalu,part,res) OP part,jvalu,res;
/* CC 0589 */ /* AK 181289 V1.1 */
/* AK 200891 V1.3 */
{
    OP a,b,e,f,d,z;
    OP gl = callocobject(); /* global list */

     signed char i, n,temp,max;
     signed char *btab,*baf,*af,tab[50];

    if (not EMPTYP(res)) freeself(res);
    if (einsp(jvalu)) { m_pa_s(part,res); return(OK); }

    for(i=0;i<S_PA_LI(part);i++) tab[(int) i]=( signed char)S_PA_II(part,(INT)i);

    n = ( signed char)S_I_I(jvalu);
    temp = 0; btab = tab;

    temp = ( signed char)S_PA_LI(part);
    max = temp * n;

    btab = tab;
    baf = ( signed char *)SYM_MALLOC(max);
        if (baf == NULL) return no_memory();
    af = baf;

    for(i = 0; i < max - temp ; i++) { *baf = (n*i)-i; baf++; }
    for(; i < max; i++)
    { 
        *baf = (n * ((*btab) + i)) - i; 
        baf++; btab++; 
    }
    baf = af;

    b_skn_s(callocobject(),callocobject(),NULL,gl);
    M_I_I(1L,S_S_K(gl));
    b_ks_pa(VECTOR,callocobject(),S_S_S(gl));

    if (max >1) m_il_v((INT)max-1,S_PA_S(S_S_S(gl)));
    else m_il_v(1L,S_PA_S(S_S_S(gl)));

    baf = af;
    if (max>1)baf++;
    if(max > 1)
        for (i=0;i<max-1;i++)
            M_I_I((INT)(*baf++) ,S_PA_I(S_S_S(gl),(INT)i));
    else M_I_I((INT)(*baf++) ,S_PA_I(S_S_S(gl),0L));

    a = callocobject();    /* part 1 */
    b  = callocobject();   /* part 2*/
    d = callocobject();    /* result */
    e = callocobject();    /*limit*/

    b_ks_pa(VECTOR,callocobject(),a);
    b_ks_pa(VECTOR,callocobject(),b);
    if(max>1)
        m_il_v((INT)max-1,S_PA_S(b));
    else
        m_il_v(1L,S_PA_S(b));
    if(max>1)
        for(i=1;i<max;i++)
            M_I_I((INT)(i*n - i ),S_PA_I(b,(INT)i-1));
    else M_I_I(1L,S_PA_I(b,0L));
marke:
    if (not EMPTYP(gl))
        if (S_L_S(gl) != NULL)
        {
            INT zz,kk;
            z = S_S_S(gl);
            kk = max - S_PA_LI(z);
            for (i=0;i<S_PA_LI(z);i++)
             if (S_PA_II(z,(INT)i) > (INT)(i+kk)*(n-1) ) break;

            m_il_v(S_PA_LI(z)-i,S_PA_S(a));
            for (zz=0;zz<S_PA_LI(a);zz++,i++)
              M_I_I(S_PA_II(z,(INT)i)-(i+kk)*(n-1),S_PA_I(a,zz));

        }
        else goto ende;
    else goto ende;

    M_I_I((INT)max,e);
    outerproduct_schur_limit(a,b,d,e);
    /*Remove the dominant terms */



    mult (d, S_S_K(gl), d);
    f = callocobject();
    m_skn_s(a,S_S_K(gl),NULL,f);
    add_apply(f,res); 
    addinvers(d,f);
    insert(f,gl,add_koeff,comp_colex_schurmonom);
    goto marke;

ende:
    freeall(a); freeall(b); freeall(d); freeall(e); SYM_free(af);
    return OK;
}

#endif /* PLETTRUE */

#ifdef PLETTRUE
INT test_plet()
{
    OP a,b,c;
    a = callocobject();
    b = callocobject();
    c = callocobject();
    printeingabe("test_plet:complete_complete_plet(3L,3L,c)");
    m_i_i(3L,a);
    m_i_i(3L,b);
    complete_complete_plet(a,b,c); 
    println(c);
    printeingabe("test_plet:complete_schur_plet(3L,PARTITION,c)");
    scan(PARTITION,b);
    complete_schur_plet(a,b,c); 
    println(c);
    printeingabe("test_plet:power_schur_plet_old(2L,PARTITION,c)");
    scan(PARTITION,b);
    power_schur_plet_old(cons_zwei,b,c); 
    println(c);
    printeingabe("test_plet:schur_schur_plet(PARTITION,PARTITION,c)");
    scan(PARTITION,a);
    scan(PARTITION,b);
    schur_schur_plet(a,b,c); 
    println(c);
    freeall(a);
    freeall(b);
    freeall(c);
    return OK;
}

INT plethysm_schur_schur(a,b,c) OP a,b,c;
/* AK 190299 */
{
    INT erg = OK;
    CTO(SCHUR,"plethysm_schur_schur",a);
    CTO(SCHUR,"plethysm_schur_schur",b);

    if ((S_S_N(a) != NULL) || (S_S_SLI(a) != 1))
        {
        error("plethysm_schur_schur:for the moment only for outer S_n");
        goto endr_ende;
        }
    if (S_S_N(b) != NULL)
        {
        error("plethysm_schur_schur:for the moment only for inner single S_I");
        goto endr_ende;
        }

    erg += schur_schur_plet(S_S_SI(a,0), S_S_S(b) ,c);
    
    ENDR("plethysm_schur_schur");
}



static INT plet_sn_mI();
static INT plet_sn_MONOMIAL();
static INT inc_weight_monomial();

INT plethysm_schur_monomial(a,b,c) OP a,b,c;
/* AK 190299 */
{
    INT erg = OK;
    CTO(SCHUR,"plethysm_schur_monomial(1)",a);
    CTO(MONOMIAL,"plethysm_schur_monomial(2)",b);

    if ((S_S_N(a) != NULL) || (S_S_SLI(a) != 1))
        {
        error("plethysm_schur_monomial: for the moment only for S_n");
        goto endr_ende;
        }

    erg += plet_sn_MONOMIAL(S_S_SI(a,0), b,c);
    
    ENDR("plethysm_schur_monomial");
}


static INT plet_sn_MONOMIAL(OP n, OP I, OP r)
/* compute s_n[m_I] in the basis of monomial */
{
    INT erg = OK;
    OP l;
        OP n1,n2,h1,h2;
        OP z2 = S_S_N(I);
        OP z1;
        INT i,wi;

    CTO(INTEGER,"plet_sn_MONOMIAL",n);
    CTO(MONOMIAL,"plet_sn_MONOMIAL",I);

    l = callocobject();
    length(I,l);
    if (einsp(l))
        {
        if (einsp(S_S_K(I)))
            plet_sn_mI(n,S_S_S(I),r);    
        else    {
            CTO(INTEGER,"plet_sn_MONOMIAL:non integer coefficient",S_S_K(I));

            init(MONOMIAL,r);
            h1 = callocobject();
            h2 = callocobject(); /* composition */
            n1 = callocobject(); /* faktor = binom */
            z2 = callocobject();
            first_composition(n,n,h2);
                do {
                    z1 = callocobject();
                    m_i_i(0,h1);wi=0;
                    for (i=0;i<S_V_LI(h2);i++)
                        {
                        if (S_V_II(h2,i) != 0) {
                            wi += S_V_II(h2,i);
                            if (S_I_I(h1) == 0)
                                {
                                plet_sn_mI(S_V_I(h2,i), S_S_S(I), z1);
                                }
                            else    {
                                plet_sn_mI(S_V_I(h2,i), S_S_S(I), z2);
                                mult_apply(z2,z1);
                                }
                            INC_INTEGER(h1);
                            }
                        else break;
                        }
                    if (wi == S_I_I(n)) {
                        binom(S_S_K(I),h1,n1);
                        if (nullp(n1)) {
                            freeall(z1);
                            }
                        else    {
                            mult_apply(n1,z1);
                            insert(z1,r,NULL,NULL);
                            }
                        }
                    else freeall(z1);
                } while(next(h2,h2));

            freeall(n1);
            freeall(h1);
            freeall(h2);
            freeall(z2);
            }
        }
    else
        {

        init(MONOMIAL,r);
        h1 = callocobject();
        n1 = callocobject();
        n2 = callocobject();
        z1 = callocobject();
        m_pa_mon(S_S_S(I),z1);
        copy(S_S_K(I),S_S_K(z1));

        for (i=1;i<S_I_I(n);i++)
            {
            h2 = callocobject();
            M_I_I(i,n1);
            M_I_I(S_I_I(n)-i,n2);
            plet_sn_MONOMIAL(n1,z1,h1);
            plet_sn_MONOMIAL(n2,z2,h2);
            mult_apply(h1,h2); 
            insert(h2,r,NULL,NULL);
            }
        plet_sn_MONOMIAL(n,z1,h1); insert(h1,r,NULL,NULL);
        plet_sn_MONOMIAL(n,z2,z1); insert(z1,r,NULL,NULL);

        freeall(n1);
        freeall(n2);
        }
    freeall(l);
    ENDR("plet_sn_MOMOMIAL");
}

INT ak_plet_phm_integer_partition_(a,b,c,f) OP a,b,c,f;
{
    OP m;
    INT erg = OK;
    CTO(INTEGER,"ak_plet_phm_integer_partition_(1)",a);
    CTO(PARTITION,"ak_plet_phm_integer_partition_(2)",b);
    m = CALLOCOBJECT();
    plet_sn_mI(a,b,m);
    MULT_APPLY(f,m);
    if (S_O_K(c) == MONOMIAL)
        insert_list_list(m,c,add_koeff,comp_monommonomial);
    else
        insert_monomial_hashtable(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
    ENDR("ak_plet_phm_integer_partition_");
}

static INT plet_sn_mI(OP n, OP I, OP r)
/* compute s_n[m_I] in the basis of monomial */
{
    INT i,j;
    OP parts,v;
    INT erg = OK;
    static int recdeb=0;
    CTO(INTEGER,"plet_sn_mI(1)",n);
    CTO(PARTITION,"plet_sn_mI(2)",I);
    if (S_I_I(n)< 0) { error("plet_sn_mI: defined for n>=0");goto endr_ende; }
    
    if (S_PA_LI(I) == 0) {
        m_pa_mon(I,r);
        goto ende;
        }
    if (S_I_I(n) == 0) { 
        m_pa_mon(I,r); 
        first_partition(cons_null,S_S_S(r)); 
        M_I_I(1,S_S_K(r)); 
        goto ende;}
    if (S_I_I(n) == 1) { 
         m_pa_mon(I,r); 
         goto ende;
         }
    /* loop over all partitions with parts from I and length <= n */
    j=1;for (i=1;i<S_PA_LI(I);i++) if (S_PA_II(I,i) != S_PA_II(I,i-1)) j++;
    /* is the number of different parts */
    parts = callocobject();m_il_v(j,parts);
    M_I_I(S_PA_II(I,0),S_V_I(parts,0));
    j=1;for (i=1;i<S_PA_LI(I);i++) 
        if (S_PA_II(I,i) != S_PA_II(I,i-1)) 
            { M_I_I(S_PA_II(I,i),S_V_I(parts,j));j++; }
    /* parts is the vector with the different parts, increasing */

    /* first partition */
    v = callocobject();
    m_il_v(S_I_I(n),v);
    for (i=0;i<S_V_LI(v);i++) M_I_I(S_V_LI(parts),S_V_I(v,i));


    init(MONOMIAL,r);
    do {
    INT w;
    OP level = callocobject();
    init(MONOMIAL,level);
        /* check auf gewicht */
        w = 0; for (i=0;i<S_V_LI(v);i++) if (S_V_II(v,i)) w += S_V_II(parts,S_V_II(v,i)-1);
        if (w < S_PA_II(I,S_PA_LI(I)-1)) goto next;
        /* es werden nur solche genommen, wo das gewicht >= maximalen teil */
        
        j = 0;
        for (i=1;i<=S_V_LI(v);i++)
            {
            if ((i == S_V_LI(v)) || (S_V_II(v,i) != S_V_II(v,i-1)))
                {
                INT k;
                OP new_I = callocobject();
                OP new_n = callocobject();
                OP new_r = callocobject();
                /* von j bis i ein block */

                copy(S_PA_S(I),new_I);



                for (k=0;k<S_V_LI(new_I);k++)
                    if (S_V_II(v,i-1)>0) /* AK 121201 */
                    if (S_V_II(new_I,k) == S_V_II(parts,S_V_II(v,i-1)-1))
                        { M_I_I(0,S_V_I(new_I,k)); break; }


                m_v_pa(new_I,new_I);
                /* check ob das gewicht stimmt */
                M_I_I(i-j,new_n);
                recdeb++;
                if ((S_PA_LI(new_I) == 0) || (S_I_I(new_n) == 1) ) { /* AK 121201 */
                    m_pa_mon(new_I,new_r);
                    }
                else
                    plet_sn_mI(new_n,new_I,new_r);
                recdeb--;
                if (j==0) swap(new_r,level); 
                else mult_apply_monomial_monomial(new_r,level);
 

                j = i;
                freeall(new_I);
                freeall(new_n);
                freeall(new_r);
                }
            }
        /* jetzt den level um das teil w erweitern */

        inc_weight_monomial(w,level);

        erg += add_apply(level,r);


        {
        next: /* next */
        for (i=0;i<S_V_LI(v);i++)
            if (S_V_II(v,i) > 0) { DEC_INTEGER(S_V_I(v,i)); j = S_V_II(v,i); i--; break;  }
        for (;i>=0;i--) M_I_I(j,S_V_I(v,i));
        }
    freeall(level);
    } while (not nullp(v));
    erg += freeall(v); freeall(parts);
ende:
    CTO(INTEGER,"plet_sn_mI(1)",n);
    CTO(PARTITION,"plet_sn_mI(2)",I);
    CTO(MONOMIAL,"plet_sn_mI(3-ende)",r);
/*
    {
    OP z,d = callocobject(),w=callocobject(); weight(I,d); mult_apply(n,d);
    FORALL(z,r, {
           weight(S_MO_S(z),w); if (neq(w,d)) error("");
       } );
     freeall(w); freeall(d);
    }
*/
    ENDR("plet_sn_mI");
}

static INT inc_weight_monomial(INT w, OP s)
{
    OP z;
    OP r = callocobject();
    init(MONOMIAL,r);
    FORALL(z,s,{
    if ((S_PA_LI(S_MO_S(z)) == 0) || (S_PA_II(S_MO_S(z), S_PA_LI(S_MO_S(z))-1) <= w))
        {
        OP p = callocobject();
        copy(S_MO_S(z),p);
        inc(p);
        M_I_I(w,S_PA_I(p,S_PA_LI(p)-1));
        m_pa_mon(p,p);
        copy(S_MO_K(z),S_S_K(p));
        insert(p,r,NULL,NULL);
        }
    }); 
    swap(r,s);
    freeall(r);
    return OK;
}

INT p2_schursum();
INT p_schursum(a,b,c,f,schurf,partf,multf)
    OP a,b,c,f;
    INT (*schurf)(), (*partf)(), (*multf)();
/* AK 101201 for the expansion S_I[P+Q] */
{
    return p2_schursum(a,b,c,f,-1,schurf,partf,multf);
#ifdef UNDEF
    INT erg = OK;
/*  loop over all partitions smaller then a */
/*  S_a[b1+b2] = \sum_d<a  S_a/d [b1] * S_d[b2] */
    OP b2,b1;
    INT w=0;
    INT i;

    CTTO(PARTITION,INTEGER,"p_schursum(1)",a);
    CTTO(HASHTABLE,SCHUR,"p_schursum(2)",b);
    SYMCHECK((S_O_K(a)==PARTITION)&&(S_PA_LI(a) == 0), "p_schursum:partion of weight 0 ");

    if (S_O_K(b) == SCHUR) {
        b2 = S_S_N(b);
        C_S_N(b,NULL);
        b1 = b;
        SYMCHECK( ( b2 == NULL) ,"p_schursum(1):no real sum");
        }
    else { /* HASHTABLE */
        SYMCHECK(WEIGHT_HASHTABLE(b) <= 1,"p_schursum(2):no real sum");
        b1 = CALLOCOBJECT();
        b2 = CALLOCOBJECT();
        split_hashtable(b,b1,b2);
        }

    /* both limits to the sum */
    (*partf)(a,b1,c,f);
    (*partf)(a,b2,c,f);

    if (S_O_K(a) == PARTITION) {
        for (i=0;i<S_PA_LI(a);i++) w+= S_PA_II(a,i);
    
        for (i=1;i<w;i++)
            {
            OP h,p;
            h = CALLOCOBJECT(); M_I_I(i,h);
            p = CALLOCOBJECT(); first_partition(h,p);
            do {
                if (contain_comp_part(p,a)) {
                    OP h1,h2,s1;
                    NEW_HASHTABLE(h1);
                    NEW_HASHTABLE(h2);
                    NEW_HASHTABLE(s1);
                    part_part_skewschur(a,p,s1);
                    (*schurf)(s1,b1,h1,cons_eins);
                    (*partf)(p,b2,h2,cons_eins);
                    (*multf)(h1,h2,c,f);
                    FREEALL(h1);
                    FREEALL(h2);
                    FREEALL(s1);
                    }
                } while(next_apply(p));
    
            FREEALL(h);
            FREEALL(p);
            }
        }
    else /* INTEGER */ {
        OP h,p;
        h = CALLOCOBJECT();
        p = CALLOCOBJECT();
        for (i=1;i<S_I_I(a);i++)
            {
            OP h1,h2;
            NEW_HASHTABLE(h1);
            NEW_HASHTABLE(h2);
            M_I_I(i,h);
            M_I_I(S_I_I(a)-i,p);
            (*partf)(p,b1,h1,cons_eins);
            (*partf)(h,b2,h2,cons_eins);
            (*multf)(h1,h2,c,f);
            FREEALL(h1);
            FREEALL(h2);
            }
        FREEALL(h);
        FREEALL(p);
        }

    if (S_O_K(b) == SCHUR) { C_S_N(b,b2); }
    else /* HASHTABLE */ { FREEALL(b1); FREEALL(b2); }
    ENDR("p_schursum");
#endif
}


INT p2_schursum(a,b,c,f,m,schurf,partf,multf)
    OP a,b,c,f; INT m;
    INT (*schurf)(), (*partf)(), (*multf)();
/* AK 101201 for the expansion S_I[P+Q] */
/* wie p_schursum mit INT als limit */
{
    INT erg = OK;
/*  loop over all partitions smaller then a */
/*  S_a[b1+b2] = \sum_d<a  S_a/d [b1] * S_d[b2] */
    OP b2,b1;
    INT w=0;
    INT i;
    INT split_hashtable();

    CTTO(PARTITION,INTEGER,"p2_schursum(1)",a);
    CTTO(HASHTABLE,SCHUR,"p2_schursum(2)",b);
    SYMCHECK((S_O_K(a)==PARTITION)&&(S_PA_LI(a) == 0), "p2_schursum:partion of weight 0 ");

    if (S_O_K(b) == SCHUR) {
        b2 = S_S_N(b);
        C_S_N(b,NULL);
        b1 = b;
        SYMCHECK( ( b2 == NULL) ,"p2_schursum(1):no real sum");
        }
    else { /* HASHTABLE */
        SYMCHECK(WEIGHT_HASHTABLE(b) <= 1,"p2_schursum(2):no real sum");
        b1 = CALLOCOBJECT();
        b2 = CALLOCOBJECT();
        split_hashtable(b,b1,b2);
        }

    /* both limits to the sum */
    (*partf)(a,b1,c,f,m);
    (*partf)(a,b2,c,f,m);

    if (S_O_K(a) == PARTITION) {
        for (i=0;i<S_PA_LI(a);i++) w+= S_PA_II(a,i);
    
        for (i=1;i<w;i++)
            {
            OP h,p;
            h = CALLOCOBJECT(); M_I_I(i,h);
            p = CALLOCOBJECT(); first_partition(h,p);
            do {
                if (contain_comp_part(p,a)) {
                    OP h1,h2,s1;
                    NEW_HASHTABLE(h1);
                    NEW_HASHTABLE(h2);
                    NEW_HASHTABLE(s1);
                    part_part_skewschur(a,p,s1);
                    (*schurf)(s1,b1,h1,cons_eins,m);
                    (*partf)(p,b2,h2,cons_eins,m);
                    (*multf)(h1,h2,c,f,m);
                    FREEALL(h1);
                    FREEALL(h2);
                    FREEALL(s1);
                    }
                } while(next_apply(p));
    
            FREEALL(h);
            FREEALL(p);
            }
        }
    else /* INTEGER */ {
        OP h,p;
        h = CALLOCOBJECT();
        p = CALLOCOBJECT();
        for (i=1;i<S_I_I(a);i++)
            {
            OP h1,h2;
            NEW_HASHTABLE(h1);
            NEW_HASHTABLE(h2);
            M_I_I(i,h);
            M_I_I(S_I_I(a)-i,p);
            (*partf)(p,b1,h1,cons_eins,m);
            (*partf)(h,b2,h2,cons_eins,m);
            (*multf)(h1,h2,c,f,m);
            FREEALL(h1);
            FREEALL(h2);
            }
        FREEALL(h);
        FREEALL(p);
        }

    if (S_O_K(b) == SCHUR) { C_S_N(b,b2); }
    else /* HASHTABLE */ { FREEALL(b1); FREEALL(b2); }
    ENDR("p2_schursum");
}

#endif /* PLETTRUE */
