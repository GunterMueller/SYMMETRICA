/* SYMMETRICA file:lo.c */
#include "def.h"
#include "macro.h"
#include <string.h> /*strcat */


#define EXP 15
#define LO_B 32768           /*              1000000000000000*/
#define BMINUSEINS 32767     /*               111111111111111*/
#define LO_B1 (INT)2147450880/*111111111111111000000000000000*/
#define B2MINUSEINS (INT)2147483647    /*1000000000000000000000000000000 - 1*/
#define Basis 45
#define MSB  16384 
#define MAXNEG (INT)(-2147483647-1) /*1000000000000000000000000000000 */

#ifdef LONGINTTRUE
struct ganzdaten gd; /* a global datastructure */
    static OP rl_o=NULL; /* obere grenze */
    static OP rl_m=NULL; /* modulo */
    static OP rl_x=NULL; /* ergebnis */
    static OP rl_a=NULL; /* multiplier */


#endif

      INT  mult_longint_integer_via_ganzsmul();

static struct longint * calloclongint();
static INT longint_speicher_ende();

static INT nofolgezeichen=0;

INT set_lo_nopoint(para) INT para; { nofolgezeichen=para; }

static INT ganzadd();
static INT ganzanfang();
static INT ganzaus();
static INT ganzdefiniere();
static INT ganzein();
static INT ganzeven();
static INT ganzfziffer();
/* static INT ganzganzdiv(); */
/* static INT ganzhalf(); */
static INT ganzint();
static INT ganzkopiere();
/* static INT ganzloesche(); */
/* static INT ganzmod(); */
static INT ganzmul();
/* static INT ganzneg(); */
static INT ganzodd();
static INT ganzparam();
static INT ganzquores();
/* static INT ganzsignum(); */
static INT ganzsadd();
static INT ganzsmul();
static INT ganzsquores();
static INT ganzvergleich();
static INT ganz1ziffer();
static INT intganz();
static INT locadd();
static INT locdiv();
static INT lochole();
static INT locint();
static INT loclisterette();
static INT locms1();
/* static INT locmul(); */
static INT locneg();
/* static INT locnull(); */
static INT locodd();
static INT locrette();
static INT locrezliste();
static INT locpsl();
static INT locpsr();
static INT locsadd();
static INT locsdiv();
/* static INT locsgn(); */
static INT locsmul();
static INT locssub();
static INT locsub();
static INT locvgl();
static INT retteziffer();

struct loc **loc_speicher = NULL;
INT loc_index = -1;
INT loc_size = 0;
INT loc_counter = 0;

INT mem_counter_loc=0;
INT longint_speicherindex=-1; /* AK 301001 */
INT longint_speichersize=0; /* AK 301001 */
struct longint **longint_speicher=NULL; /* AK 301001 */


#define FREE_LONGINT(v)\
    FREE_MEMMANAGER(struct longint *,longint_speicher,longint_speicherindex,\
                    longint_speichersize,mem_counter_loc,v)
#ifdef UNDEF
do {\
    mem_counter_loc--;\
    if (longint_speicherindex+1 == longint_speichersize) {\
       if (longint_speichersize == 0) {\
           longint_speicher = (struct longint **) \
                  SYM_MALLOC(100 * sizeof(struct longint *));\
           SYMCHECK(longint_speicher == NULL,"no memory");\
           longint_speichersize = 100;\
           }\
       else {\
           longint_speicher = (struct longint **) SYM_realloc (longint_speicher,\
               2 * longint_speichersize * sizeof(struct longint *));\
           SYMCHECK(longint_speicher == NULL,"no memory");\
           longint_speichersize = 2 * longint_speichersize;\
           }\
       }\
    longint_speicher[++longint_speicherindex] = v;\
} while(0)
#endif



/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */

#ifdef LONGINTTRUE
static INT locadd(lx,ly,cy) struct loc *lx,*ly; INT cy;
/* AK 130789 V1.0 */ /* AK 270390 V1.1 */ /* AK 210891 V1.3 */
    {
    static INT hh;
    hh=ly->w0+cy+lx->w0;
    lx->w0=(hh&BMINUSEINS);
    cy = hh >>EXP;
    hh=ly->w1+cy+lx->w1;
    lx->w1=(hh&BMINUSEINS);
    cy = hh >>EXP;
    hh=ly->w2+cy+lx->w2;
    lx->w2=(hh&BMINUSEINS);
    cy = hh >>EXP;
    return((INT)cy);
    }
#endif /* LONGINTTRUE */

#define LOCADD(lx,ly,cy)\
    hh=(ly)->w0+cy+(lx)->w0, (lx)->w0=(hh&BMINUSEINS), cy = hh >>EXP,\
    hh=(ly)->w1+cy+(lx)->w1, (lx)->w1=(hh&BMINUSEINS), cy = hh >>EXP,\
    hh=(ly)->w2+cy+(lx)->w2, (lx)->w2=(hh&BMINUSEINS), cy = hh >>EXP,cy


#define LOCBAS2() Basis
    

#define LOCASS(lx,ly) ((lx)->w2=(ly)->w2,(lx)->w1=(ly)->w1,(lx)->w0=(ly)->w0)

#ifdef LONGINTTRUE
static INT locdiv(qu,rest,dd,dv) struct loc *qu,*rest,*dd,*dv;
/* Division. Bei Eingabe muss gelten: rest<dv.            */
/* (qu,rest) := ((rest*LO_B+dd) DIV dv, (rest*LO_B+dd) MOD dv). */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */
/* AK 210891 V1.3 */
    {
    INT d6,d5,d4,d3,d2,d1,
         h6,h5,h4,h3,h2,h1, 
         m2,m1,m0;


 /* d=rest*B+dd */
 d6=rest->w2; 
 d5=rest->w1; 
 d4=rest->w0; 
 d3=dd->w2; 
 d2=dd->w1; 
 d1=dd->w0;

 /* h=dv */
 h6=0; 
 h5=0; 
 h4=0; 
 h3=dv->w2; 
 h2=dv->w1; 
 h1=dv->w0; 

 /* qu=0 */
 qu->w2=0; 
 qu->w1=0; 
 qu->w0=0;

 /* m=1 */
 m2=0; 
 m1=0; 
 m0=1;

 while /* h<=d */
 (
/* alt
  h6 <d6 ||
  (h6==d6 && h5<d5 ) ||
  (h6==d6 && h5==d5 && h4<d4 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3<d3 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2<d2 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1<d1 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1==d1 )
*/
   h6 < d6
   ||
   (h6 == d6 && (
                h5 < d5 ||
                (h5 == d5 && (
                            h4 < d4 ||
                            (h4 == d4 && (
                                        h3 < d3 ||
                                        (h3 == d3 && (
                                                    h2 < d2 ||
                                                    (h2 == d2 && h1 <= d1)
                                                    )
                                        ))
                            ))
               ))
   )
 )
 {
  /* h=h*2 */
/* alt
  h6=h6<<1; 
  h5=h5<<1; 
  h4=h4<<1; 
  h3=h3<<1; 
  h2=h2<<1; 
  h1=h1<<1; 
*/
      h6 <<= 1;
      h5 <<= 1;
      h4 <<= 1;
      h3 <<= 1;
      h2 <<= 1;
      h1 <<= 1;


  if (h1&LO_B1) {h1&=BMINUSEINS; h2++; };
  if (h2&LO_B1) {h2&=BMINUSEINS; h3++; };
  if (h3&LO_B1) {h3&=BMINUSEINS; h4++; };
  if (h4&LO_B1) {h4&=BMINUSEINS; h5++; };
  if (h5&LO_B1) {h5&=BMINUSEINS; h6++; };

  /* m=m*2 */
/*alt
  m2=m2<<1; 
  m1=m1<<1; 
  m0=m0<<1;
*/
      m2 <<= 1;
      m1 <<= 1;
      m0 <<= 1;

  if (m0&LO_B1) {m0&=BMINUSEINS; m1++; };
  if (m1&LO_B1) {m1&=BMINUSEINS; m2++; };
 }
  while /* d>=dv */
  (
/* alt
    d6 >0 || d5>0  || d4>0  ||
   (d6==0 && d5==0 && d4==0 && d3>dv->w2 ) || 
   (d6==0 && d5==0 && d4==0 && d3==dv->w2 && d2>dv->w1 ) || 
   (d6==0 && d5==0 && d4==0 && d3==dv->w2 && d2==dv->w1 && d1>dv->w0 ) ||
   (d6==0 && d5==0 && d4==0 && d3==dv->w2 && d2==dv->w1 && d1==dv->w0 )
*/
   d6 >0 || d5>0  || d4>0  || (
                              d6==0 && d5==0 && d4==0 && ( d3>dv->w2 ||
                                                           (d3==dv->w2 && (
                                                                      d2 > dv->w1 ||
                                                                      (d2 ==dv->w1 && d1 >= dv->w0)
                                                                      )
                                                           )
                                                         )
                              )
  )
  {
   while /*h>d */
   (
/* alt
     h6 >d6 ||
    (h6==d6 && h5>d5) ||
    (h6==d6 && h5==d5 && h4>d4) ||
    (h6==d6 && h5==d5 && h4==d4 && h3>d3) ||
    (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2>d2) ||
    (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1>d1 )
*/
     h6 > d6
            ||
            (h6 == d6 && (
                         h5 > d5 ||
                         (h5 == d5 && (
                                     h4 > d4 ||
                                     (h4 == d4 && (
                                                 h3 > d3 ||
                                                 (h3 == d3 && (
                                                             h2 > d2 ||
                                                             (h2 == d2 && h1 > d1)
                                                             )
                                                 ))
                                     ))
                        ))
            )
   )
   {
    /* h=h/2 */
    if (h6&1) { h6--; h5=h5|LO_B; };  
    if (h5&1) { h5--; h4=h4|LO_B; }; 
    if (h4&1) { h4--; h3=h3|LO_B; };
    if (h3&1) { h3--; h2=h2|LO_B; };
    if (h2&1) { h2--; h1=h1|LO_B; };
                                   
/* alt
                h6=h6>>1;
                h5=h5>>1;
                h4=h4>>1;
                h3=h3>>1;
                h2=h2>>1;
                h1=h1>>1;
*/
                h6 >>= 1;
                h5 >>= 1;
                h4 >>= 1;
                h3 >>= 1;
                h2 >>= 1;
                h1 >>= 1;
 


    /* m=m/2 */
    if (m2&1) { m2--; m1|=LO_B; }; 
    if (m1&1) { m1--; m0|=LO_B; }; 
                                  
/* alt
                m2=m2>>1;
                m1=m1>>1;
                m0=m0>>1;
*/
                m2 >>= 1;
                m1 >>= 1;
                m0 >>= 1;

   }
   
   /* d=d-h */
   if (h1>d1) { d1+=LO_B; d2--; };  d1-=h1;
   if (h2>d2) { d2+=LO_B; d3--; };  d2-=h2;
   if (h3>d3) { d3+=LO_B; d4--; };  d3-=h3;
   if (h4>d4) { d4+=LO_B; d5--; };  d4-=h4;
   if (h5>d5) { d5+=LO_B; d6--; };  d5-=h5;
                                   d6-=h6;

   /* qu=qu+m */
   qu->w0|=m0; qu->w1|=m1; qu->w2|=m2;
  }
    rest->w2=d3; rest->w1=d2; rest->w0=d1;
    return(OK);
}



static INT locint(lx,i) struct loc *lx; INT    i;
/* Umwandlung Integer in loc: lx:=abs(i); locint:=sgn(i)  */
/* AK 130789 V1.0 */ /* AK 150290 V1.1 */
/* AK 210891 V1.3 */
    {
    INT s;

    if (i<(INT)0)         
        {
        s=(INT)-1; 
        i=0-i;
        }
    else if (i>(INT)0)         
        s=(INT)1;
    else             
        s=(INT)0;

    lx->w0 = i;
    lx->w0 &= BMINUSEINS;
    lx->w1 = i>>EXP;
    lx->w2 = lx->w1 >>EXP;
    lx->w1 &= BMINUSEINS;
    lx->w2 &= BMINUSEINS;
    return(s);
    }



#define LOCMAX(lx) ((lx)->w0=BMINUSEINS,\
    (lx)->w1=BMINUSEINS,(lx)->w2=BMINUSEINS)


static INT locms1(lx) struct loc *lx;
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT j,c,cc;

    c=Basis; cc=(INT)1;
    for (j=(INT)14; (j >=(INT)0) && cc ; j--)
    {
      if ( lx->w2 & ( (INT)1 << j )) 
         cc=(INT)0;
      c--;
    } 
  if (cc) 
    for (j=(INT)14; (j >=(INT)0) && cc ; j--)
    {
      if ( lx->w1 & ( (INT)1 << j )) 
         cc=(INT)0;
      c--;
    }
  if (cc) 
    for (j=(INT)14; (j >=(INT)0) && cc ; j--)
    {
      if ( lx->w0 & ( (INT)1 << j )) 
         cc=(INT)0;
      c--;
    }
  if (cc) 
    {
    fprintf(stderr,"cc=%ld %ld %ld %ld\n",cc,lx->w0,lx->w1,lx->w2);
    error("internal error:LO7");
    }
  return(c);
 }


 
#define teile(z) (hh=(z)>>EXP, (z) &= BMINUSEINS, hh)

#ifdef UNDEF
static INT locmul(ly,lx,la,lb) struct loc *lx,*ly,*la,*lb;
/* AK 130789 V1.0 */ /* AK 260390 V1.1 */ /* AK 210891 V1.3 */
{
static INT hh;
/* AK 260390 */

 lx->w0 =                          la->w0 * lb->w0;
 lx->w1 =          teile(lx->w0) + la->w1 * lb->w0;
 lx->w2 =          teile(lx->w1) + la->w2 * lb->w0;
 ly->w0 =          teile(lx->w2)                  ;
 lx->w1 +=                  la->w0 * lb->w1;
 lx->w2 +=  teile(lx->w1) + la->w1 * lb->w1;
 ly->w0 +=  teile(lx->w2) + la->w2 * lb->w1;
 ly->w1 =          teile(ly->w0)                  ;
 lx->w2 +=                  la->w0 * lb->w2;
 ly->w0 +=  teile(lx->w2) + la->w1 * lb->w2;
 ly->w1 +=  teile(ly->w0) + la->w2 * lb->w2;
 ly->w2 =          teile(ly->w1)                  ;
 return OK;
}
#endif


#define LOCMUL(ly,lx,la,lb) /* hh ist noetig */\
 (lx)->w0 =                          (la)->w0 * (lb)->w0,\
 (lx)->w1 =          teile((lx)->w0) + (la)->w1 * (lb)->w0,\
 (lx)->w2 =          teile((lx)->w1) + (la)->w2 * (lb)->w0,\
 (ly)->w0 =          teile((lx)->w2)                  ,\
 (lx)->w1 +=                  (la)->w0 * (lb)->w1,\
 (lx)->w2 +=  teile((lx)->w1) + (la)->w1 * (lb)->w1,\
 (ly)->w0 +=  teile((lx)->w2) + (la)->w2 * (lb)->w1,\
 (ly)->w1 =          teile((ly)->w0)                  ,\
 (lx)->w2 +=                  (la)->w0 * (lb)->w2,\
 (ly)->w0 +=  teile((lx)->w2) + (la)->w1 * (lb)->w2,\
 (ly)->w1 +=  teile((ly)->w0) + (la)->w2 * (lb)->w2,\
 (ly)->w2 =          teile((ly)->w1)                  


static INT locneg(lx,cy) struct loc *lx; INT cy;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
{
    if ((cy==0)&&(lx->w0==0)&&(lx->w1==0)&&(lx->w2==0)) 
        {
        return((INT)0); 
        }
    else
        {
        lx->w0 ^= BMINUSEINS;
        lx->w1 ^= BMINUSEINS;
        lx->w2 ^= BMINUSEINS;
        if (cy == 0 )
            { 
            ++lx->w0;
            if (lx->w0 & LO_B)
                {
                ++lx->w1;
                lx->w0 &= BMINUSEINS;
                if (lx->w1 & LO_B)
                    { 
                    ++lx->w2; 
                    lx->w1 &= BMINUSEINS; 
                    }
                }
            }
       return(1);
       }
} /* locneg */



#ifdef UNDEF
static INT locnull(lx) struct loc *lx;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */
/* AK 210891 V1.3 */
    {
    lx->w2 =(INT)0; lx->w1 =(INT)0; lx->w0 =(INT)0;
    return OK;
    }  /* Ende von locnull */
#endif




static INT locodd(lx) struct loc *lx;
/*locodd:=lx ist ungerade */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    return (INT) (lx->w0 & 1);
    }

INT bit_longint(a,i) OP a; INT i;
/* AK 180902 */
/* return bit number i, i=0 lsb,
   */ 
{
    INT erg = OK;
    CTO(LONGINT,"bit_longint(1)",a);
    SYMCHECK(i<0,"bit_longint: neg index");    
    {
    struct loc *x;
    x = S_O_S(a).ob_longint->floc;
again:
    if (x == NULL) return 0;
    if (i>=45) 
        {
        x = x->nloc;
        i = i-45;
        goto again;
        }
    if (i>=30)
        {
        i = i -30;
        return (x->w2 >> i) & 1;
        }
    if (i>=15)
        {
        i = i -15;
        return (x->w1 >> i) & 1;
        }
    if (i>=0)
        {
        return (x->w0 >> i) & 1;
        }
    }
    ENDR("bit_longint");
}

static INT locpsl(lx,ly,a) struct loc *lx,*ly; INT a;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
   INT s1,s2,s3,s4,s5,i;
   static struct loc lyy;

   if (a >= 30) {
       lx->w2 = lx->w0;
       lx->w1 = ly->w2;
       lx->w0 = ly->w1;
       lyy.w2 = ly->w0;
       a = a - 30;
       }
   else if (a>=15) {
       lx->w2 = lx->w1;
       lx->w1 = lx->w0;
       lx->w0 = ly->w2;
       lyy.w2 = ly->w1;
       a = a - 15;
       }
   else {
       lyy.w2 = ly->w2;
       }
   /* lyy = *ly; */

   if ( a >= Basis) error("internal error:LO8");
   for (i=(INT)1; i <= a;i++)
   {
     s1= (lyy.w0 & MSB) >> 14;
     s2= (lyy.w1 & MSB) >> 14;
     s3= (lyy.w2 & MSB) >> 14;
     s4= (lx->w0 & MSB) >> 14;
     s5= (lx->w1 & MSB) >> 14;
     lyy.w0 <<= 1;
     lyy.w1 = (lyy.w1 << 1) | s1;
     lyy.w2 = (lyy.w2 << 1) | s2;
     lx->w0 = (lx->w0 << 1) | s3;
     lx->w1 = (lx->w1 << 1) | s4;
     lx->w2 = (lx->w2 << 1) | s5;
   }
   lx->w0 &=  BMINUSEINS;
   lx->w1 &=  BMINUSEINS;
   lx->w2 &=  BMINUSEINS;
   return OK;
 } /* Ende von locpsl */

     

static INT locpsr(lx,ly,a) struct loc *lx,*ly; INT a;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
 {
   INT s1,s2,s3,s4,s5,i;
   static struct loc lxx;

   if (a >= 30) {
       ly->w0 = ly->w2;
       ly->w1 = lx->w0;
       ly->w2 = lx->w1;
       lxx.w0 = lx->w2;
       a = a -30;
       }
   else if (a >= 15) {
       ly->w0 = ly->w1;
       ly->w1 = ly->w2;
       ly->w2 = lx->w0;
       lxx.w0 = lx->w1;
       a = a -15;
       }
   else {
       lxx.w0 = lx->w0;
       }

   /* lxx = *lx; */


   if ( a >= Basis) error("internal error:LO9");
   for (i=(INT)1; i <= a;i++)
   {
     s1= (ly->w1 & 1) << 14;
     s2= (ly->w2 & 1) << 14;
     s3= (lxx.w0 & 1) << 14;
     s4= (lxx.w1 & 1) << 14;
     s5= (lxx.w2 & 1) << 14;
     ly->w0 = (ly->w0 >> 1) | s1;
     ly->w1 = (ly->w1 >> 1) | s2;
     ly->w2 = (ly->w2 >> 1) | s3;
     lxx.w0 = (lxx.w0 >> 1) | s4;
     lxx.w1 = (lxx.w1 >> 1) | s5;
     lxx.w2 = (lxx.w2 >> 1);
   }
   return OK;
 } /* Ende von locpsr */



static INT locsadd(lx,i) struct loc *lx; INT i;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
{
    INT cy,hh;
    if (i<(INT)0) i=(-i);
    hh=lx->w0+(i%LO_B);
    lx->w0=(hh & BMINUSEINS);
    cy = hh >>EXP;
    hh=lx->w1+(i/LO_B)+cy;
    lx->w1=(hh & BMINUSEINS);
    cy = hh >>EXP;
    hh=lx->w2+cy;
    lx->w2=(hh & BMINUSEINS);
    cy = hh >>EXP;
    return(cy);
    }



static INT locsdiv(qu,di,dd,dv) struct loc *qu,*dd; INT di,dv;
/* Division. Bei Eingabe muss gelten: di<dv.             */
/* (locsdiv,qu) := ((di*B+dd) MOD dv, (di*B+dd) DIV dv). */
/* AK 130789 V1.0 */ /* AK 030790 V1.1 */ /* AK 210891 V1.3 */
    {
 INT d6,d5,d4,d3,d2,d1,
     h6,h5,h4,h3,h2,h1, 
     m2,m1,m0,
     dv2,dv1,dv0;

 /* di umwandeln */
 if (di<(INT)0) 
    return error("internal error:LO10");
 d4=di & BMINUSEINS;
 d5=(di & LO_B1)>>EXP; 
 d6=(d5 & LO_B1)>>EXP;
 d5 &= BMINUSEINS;

 /* dv umwandeln */
 if (dv<(INT)0) 
    return error("internal error:LO11");
 dv0=dv & BMINUSEINS;
 dv1=(dv & LO_B1)>>EXP; 
 dv2=(dv1 & LO_B1)>>EXP;
 dv1 &= BMINUSEINS;

 /* d=di*B+dd */
 d3=dd->w2; 
 d2=dd->w1; 
 d1=dd->w0;

 /* h=dv */
    h6=0; 
    h5=0; 
    h4=0; 
    h3=dv2; 
    h2=dv1; 
    h1=dv0; 

 /* qu=0 */
    qu->w2=0;    
    qu->w1=0; 
    qu->w0=0;

 /* m=1 */
    m2=0; 
    m1=0; 
    m0=1;

 while /* h<=d */
 (
/* alt 
   h6 <d6 ||
  (h6==d6 && h5<d5 ) ||
  (h6==d6 && h5==d5 && h4<d4 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3<d3 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2<d2 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1<d1 ) ||
  (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1==d1) 
*/
   h6 < d6 
   || 
   (h6 == d6 && ( 
                h5 < d5 ||
                (h5 == d5 && (
                            h4 < d4 ||
                            (h4 == d4 && (
                                        h3 < d3 ||
                                        (h3 == d3 && (
                                                    h2 < d2 ||
                                                    (h2 == d2 && h1 <= d1)
                                                    )
                                        ))
                            ))
               ))
   )
 )
 {
      /* h=h*2 */

      h6 <<= 1;
      h5 <<= 1;
      h4 <<= 1;
      h3 <<= 1;
      h2 <<= 1;
      h1 <<= 1;

      if (h1&LO_B1) {h1&=BMINUSEINS; h2++; };
      if (h2&LO_B1) {h2&=BMINUSEINS; h3++; };
      if (h3&LO_B1) {h3&=BMINUSEINS; h4++; };
      if (h4&LO_B1) {h4&=BMINUSEINS; h5++; };
      if (h5&LO_B1) {h5&=BMINUSEINS; h6++; };

      /* m=m*2 */
      m2 <<= 1;
      m1 <<= 1;
      m0 <<= 1;

      if (m0&LO_B1) {m0&=BMINUSEINS; m1++; };
      if (m1&LO_B1) {m1&=BMINUSEINS; m2++; };
 }

  while /* d>=dv */
  ( 
/* alt
   d6 >0 || d5>0  || d4>0  ||
   (d6==0 && d5==0 && d4==0 && d3>dv2 ) || 
   (d6==0 && d5==0 && d4==0 && d3==dv2 && d2>dv1 ) || 
   (d6==0 && d5==0 && d4==0 && d3==dv2 && d2==dv1 && d1>dv0 ) ||
   (d6==0 && d5==0 && d4==0 && d3==dv2 && d2==dv1 && d1==dv0 )
*/
   d6 >0 || d5>0  || d4>0  || (
                              d6==0 && d5==0 && d4==0 && ( d3>dv2 ||
                                                           (d3==dv2 && (
                                                                      d2 > dv1 ||
                                                                      (d2 ==dv1 && d1 >= dv0)
                                                                      )
                                                           )
                                                         )
                              )
  )
  {
           while /* h>d */
           (
/* alt
            h6 >d6 ||
            (h6==d6 && h5>d5) ||
            (h6==d6 && h5==d5 && h4>d4) ||
            (h6==d6 && h5==d5 && h4==d4 && h3>d3) ||
            (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2>d2) ||
            (h6==d6 && h5==d5 && h4==d4 && h3==d3 && h2==d2 && h1>d1 )
*/
            h6 > d6 
            || 
            (h6 == d6 && ( 
                         h5 > d5 ||
                         (h5 == d5 && (
                                     h4 > d4 ||
                                     (h4 == d4 && (
                                                 h3 > d3 ||
                                                 (h3 == d3 && (
                                                             h2 > d2 ||
                                                             (h2 == d2 && h1 > d1)
                                                             )
                                                 ))
                                     ))
                        ))
           ))
           {
                /* h=h/2 */
                if (h6&1) { h6--; h5|=LO_B; };  
                if (h5&1) { h5--; h4|=LO_B; }; 
                if (h4&1) { h4--; h3|=LO_B; };
                if (h3&1) { h3--; h2|=LO_B; };
                if (h2&1) { h2--; h1|=LO_B; };

                h6 >>= 1;
                h5 >>= 1;
                h4 >>= 1;
                h3 >>= 1;
                h2 >>= 1;
                h1 >>= 1;

                /* m=m/2 */
                if (m2&1) { m2--; m1|=LO_B; };  
                if (m1&1) { m1--; m0|=LO_B; };  

                m2 >>= 1;
                m1 >>= 1;
                m0 >>= 1;
           }
           
           /* d=d-h */
           if (h1>d1) { d1+=LO_B; d2--; };  d1-=h1;
           if (h2>d2) { d2+=LO_B; d3--; };  d2-=h2;
           if (h3>d3) { d3+=LO_B; d4--; };  d3-=h3;
           if (h4>d4) { d4+=LO_B; d5--; };  d4-=h4;
           if (h5>d5) { d5+=LO_B; d6--; };  d5-=h5;
                         d6-=h6;

           /* qu=qu+m */
           qu->w0|=m0; qu->w1|=m1; qu->w2|=m2;
  }

    d3=d3<<EXP|d2;
    d3=d3<<EXP|d1;
    return(d3);
    }



#ifdef UNDEF
static INT locsgn(lx) struct loc *lx;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
      if (lx->w2 || lx->w1 || lx->w0 ) 
         return (INT) 1;
      else return (INT) 0;
    } /* Ende locsgn */
#endif



static INT locsmul(lx,i,ue) struct loc *lx; INT i,ue;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT cy,h0,h1,h2,i0,i1,i2,u0,u1,u2;

    if (i<0)  {i=~i;++i;}
    if (ue<0) {ue=~ue;++ue;} 

    i0 = i;
    i0 &= BMINUSEINS; 
    i1 = (i>>15);
    i1 &= BMINUSEINS;
    i2 = (i>>30);
    i2 &= BMINUSEINS;

    u0 = ue;
    u0 &= BMINUSEINS; 
    u1 = (ue>>15);
    u1 &= BMINUSEINS;
    u2 = (ue>>30);
    u2 &= BMINUSEINS;


    h0=(lx->w0)*i0;
    h0 += u0;
    cy = (h0 >> 15);
    h0 &= BMINUSEINS;

    h1 =  (lx->w0)*i1;
    h1 += (lx->w1)*i0;
    h1 += cy;
    h1 += u1;
    cy = (h1 >> 15);
    h1 &= BMINUSEINS;

    h2 =  (lx->w0)*i2;
    h2 += (lx->w1)*i1;
    h2 += (lx->w2)*i0;
    h2 += cy;
    h2 += u2;
    cy = (h2 >> 15);
    h2 &= BMINUSEINS;

    cy += (lx->w1)*i2;
    cy += (lx->w2)*i1;
    cy += (((lx->w2)*i2)<<15);

    lx->w0 = h0 ; 
    lx->w1 = h1 ; 
    lx->w2 = h2 ;

    
    return(cy);
    }



static INT locssub(lx,i) struct loc *lx; INT i;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT cy;
    if (i<0) i=(-i);
    lx->w0  -= (i%LO_B);
    if (lx->w0 < 0) { 
              lx->w0 += LO_B;
              cy = (INT)1; 
              }
    else cy =(INT)0;
    lx->w1=lx->w1-((i/LO_B)%LO_B)-cy;
    if (lx->w1 < 0) { 
               lx->w1 += LO_B;
               cy = (INT)1; 
               }
    else cy =(INT)0;
    lx->w2=lx->w2-((i/LO_B)/LO_B) - cy;
    if (lx->w2 < 0) { 
               lx->w2 += LO_B;
               cy = (INT)1; 
               }
    else cy = (INT)0;
    return(cy);
    }



static INT locsub(lx,ly,cy) struct loc *lx,*ly; INT cy;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
{
    lx->w0=lx->w0- ly->w0 -cy;
    if (lx->w0 <(INT)0) { lx->w0 += LO_B;
               cy = (INT)1; }
    else cy =(INT)0;
    lx->w1=lx->w1- ly->w1- cy;
    if (lx->w1 <(INT)0) { lx->w1 += LO_B;
               cy = (INT)1; }
    else cy =(INT)0;
    lx->w2=lx->w2- ly->w2- cy;
    if (lx->w2 <(INT)0) { lx->w2 += LO_B;
               cy = (INT)1; }
    else cy =(INT)0;
    return(cy);
}

static INT locsub_cy;
#define LOCSUB(lx,ly,cy) \
    (lx->w0 -= ly->w0 , lx->w0 -= cy ,\
     locsub_cy = (lx->w0 < 0 ? lx->w0 += LO_B, 1 : 0 ),\
     lx->w1 -= ly->w1 , lx->w1 -= locsub_cy,\
     locsub_cy = (lx->w1 < 0 ? lx->w1 += LO_B, 1 : 0 ),\
     lx->w2 -= ly->w2 , lx->w2 -= locsub_cy,\
     locsub_cy = (lx->w2 < 0 ? lx->w2 += LO_B, 1 : 0 )\
    )

static INT locvgl(lx,ly) struct loc *lx,*ly;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
    {
      if (lx->w2 > ly->w2) return((INT)1);
      else if (lx->w2 < ly->w2 ) return (INT)-1;
      else if (lx->w1 > ly->w1) return((INT)1);
      else if (lx->w1 < ly->w1) return (INT)-1;
      else if (lx->w0 > ly->w0) return((INT)1);
      else if (lx->w0 < ly->w0) return (INT)-1;
      else return((INT)0); 
    }  /* Ende locvgl */



static INT ganzadd(x,y) struct longint *x,*y;
/* AK: Fri Jan 13 07:24:17 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT erg =OK;
    struct loc *alocx, *alocy, *lloc, *plocx, *plocy;
    INT    cy,xl,ll;
    signed char xs,ys;
    INT hh; /* fuer LOCADD */

    xs = x->signum; 
    ys = y->signum; 
    xl = x->laenge;
    if (((xs>=(signed char)0) && (ys>=(signed char)0)) || 
            ((xs<(signed char)0) && (ys<(signed char)0)))
        { alocx = x->floc; alocy = y->floc; cy = 0;
        do    { 
            cy = LOCADD(alocx,alocy,cy);
            plocx = alocx; 
            plocy = alocy; 
            alocx = alocx->nloc;
            alocy = alocy->nloc; 
            }
        while ((alocx != NULL) && (alocy != NULL));

        /* fuege rest an */
        if (alocy != NULL)
            { do     
                { 
                LOCHOLE(&alocx); 
                plocx->nloc = alocx;
                xl++; cy = LOCADD(alocx,alocy,cy);
                plocx = alocx; 
                alocx = NULL; 
                plocy = alocy;
                alocy = alocy->nloc; 
                }
            while (alocy != NULL);
            }
        else    { while ((alocx != NULL) && (cy != 0))
                { cy = locsadd(alocx,cy); plocx = alocx;
                alocx = alocx->nloc; }
            }

        /* noch ein cy? */
        if (cy != 0)
            { LOCHOLE(&alocx);
            plocx->nloc = alocx; locint(alocx,cy); xl++; }
        if (xs == 0) xs = ys;
        } /* end of first if */
    else    {
        alocx = x->floc; alocy = y->floc; cy = 0;
        /* subtract y from x */
        do    { cy = LOCSUB(alocx,alocy,cy); plocx = alocx;
            alocx = alocx->nloc; plocy = alocy; alocy = alocy->nloc;
            }
        while ((alocx != NULL) && (alocy != NULL));

        /* append the remaining part */
        if (alocy != NULL)
            {
            do     { LOCHOLE(&alocx); plocx->nloc = alocx; xl++;
                cy = LOCSUB(alocx,alocy,cy); plocx = alocx;
                alocx = NULL;plocy = alocy;alocy = alocy->nloc;
                }
            while (alocy != NULL);
            }
        else     {
            while    ((alocx != NULL) && (cy != 0))
                { 
                cy = locssub(alocx,cy);
                plocx = alocx; 
                alocx = alocx->nloc; 
                }
            };

        /* normieren  von x */
        if (cy != 0)
            {
            alocx = x->floc; lloc = NULL; ll = 1; cy = 0;
            do     { cy = locneg(alocx,cy);
                if (LOCSGN(alocx) != 0)
                    { lloc = alocx; xl = ll; }
                alocx = alocx->nloc; ll++;
                }
            while (alocx != NULL);
            loclisterette(&(lloc->nloc)); xs = -xs;
            if (xs == 0) xs = -1;
            }
        else    {
            alocx = x->floc; lloc = NULL; ll = 1;
            do    {
                if (LOCSGN(alocx) != 0)
                    { lloc = alocx; xl = ll; }
                alocx = alocx->nloc; ll++;
                }
            while (alocx != NULL);
            if (lloc == NULL)
                /* das ergebnis der addition ist null */
                { loclisterette(&(x->floc->nloc));
                xs = 0; xl =1; }
            else    loclisterette(&(lloc->nloc));
            }
        }
    x->laenge = xl; x->signum = xs;
    ENDR("ganzadd");
    }



static INT ganzsquores(x,rest,y) struct longint *x; INT *rest,y;
/* AK Tue Jan 31 07:48:38 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 200290 V1.1 */ /* AK 210891 V1.3 */
    {

    struct loc *alocx, *blocx, *slocx;
    INT    r;
    signed char sx,sy;

    sx = x->signum;
    if (y>(INT)0) sy=(signed char)1; 
    else if (y<(INT)0) sy = (signed char)-1; 
    else sy=(signed char)0;
    if (y<(INT)0) y = -y;
    blocx = x->floc; x->floc = NULL; locrezliste(&blocx);
    alocx = blocx; slocx = alocx->nloc; r=(INT)0;
    while (slocx != NULL)
        { 
        r = locsdiv(alocx,r,alocx,y); 
        alocx = slocx;
        slocx = alocx->nloc; 
        }


    r = locsdiv(alocx,r,alocx,y);
    *rest = r * sx;
    if (LOCSGN(blocx) !=(INT)0) x->signum = sx*sy;
    else if (x->laenge == (INT)1) x->signum = (signed char)0;
    else    {
        alocx = blocx; 
        blocx = blocx->nloc; 
        alocx->nloc =  NULL;
        locrette(&alocx); 
        x->laenge --; 
        x->signum = sx*sy;
        };

    locrezliste(&blocx);
    x->floc = blocx;
    return(OK);
    }



#ifdef UNDEF
static INT ganzhalf(x) struct longint *x;
/* AK 021294 */
{
    struct loc *alocx, *plocx;
    INT erg = OK;
    alocx = x->floc;
    plocx = NULL;
    while (alocx != NULL)
    {
        alocx->w0 >>=  1;
        alocx->w0 |=  ( (alocx->w1 & 1) << 14);
        alocx->w1 >>=  1;
        alocx->w1 |=  ( (alocx->w2 & 1) << 14);
        alocx->w2 >>=  1;
        if (alocx->nloc != NULL)
            alocx->w2 |=  ( (alocx->nloc->w0 & 1) << 14);
        if (alocx->nloc == NULL)
            {
            if (plocx != NULL)
            if ((alocx->w0 == 0) &&
                (alocx->w1 == 0)&&
                (alocx->w2 == 0))
                {
                FREE_LOC(alocx);
                plocx->nloc = NULL;
                x->laenge --;
                goto ende;
                }
            }
        
        plocx = alocx;
        alocx = alocx->nloc;
    } 
ende:
    ENDR("internal function:ganzhalf");
}
#endif

static INT ganzquores(x,rest,y) struct longint *x, *rest, *y; 
/* AK Mon Mar 13 10:58:11 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
/* x = x/y
   rest = rest */
{
    INT        vgl,cy,cyn,a,i,rl=(INT)0,ql;
    INT erg =OK;
    signed char         sx,sy;
    struct loc     *alocx, *plocx,*slocx,*blocx,*rlocx,*llocx,
            *alocy,*plocy,*blocy,*blocq,
            *locx2,*locx1,*locx0,*locy1,*locy0;

    struct loc    null,q,r,ov,hi,lo;
    INT        fertig;
    INT hh; /* fuer LOCMUL */


    if ((x->floc == y->floc) || (x->floc == rest->floc) || (y->floc == rest->floc))
        error("internal error:LO1");
    
    loclisterette(&rest->floc);
    sx = x->signum;
    sy = y->signum;
    if (y->laenge == (INT)1)    /* einfache divison */
        {
        LOCNULL(&null); 
        LOCASS(&lo,y->floc); 
        blocx = x->floc;
        x->floc = NULL; 
        locrezliste(&blocx); 
        alocx = blocx; 
        slocx = alocx->nloc;
        LOCASS(&r,&null);
        while (slocx != NULL)
            {
            locdiv(alocx,&r,alocx,&lo);
            alocx = slocx;
            slocx = slocx->nloc;
            }
        locdiv(alocx,&r,alocx,&lo);
    
        if (LOCSGN(&r) ==(INT)0) rest->signum = (signed char)0; 
        else rest->signum = sx;
        LOCHOLE(&rest->floc);
        LOCASS(rest->floc,&r);
        rest->laenge = (INT)1;
        if (LOCSGN(blocx) !=(INT)0) x->signum = sx * sy;
        else if (x->laenge == (INT)1) x->signum = (signed char)0;
        else    { alocx = blocx; blocx = blocx->nloc; alocx->nloc = NULL;
            locrette(&alocx); x->laenge --; x->signum = sx * sy;
            }
        locrezliste(&blocx);
        x->floc = blocx;
        } /* ende der einfachen division */
    else    if (x->laenge < y->laenge)    /* trivial */
        {
        *rest = *x; x->floc = NULL; LOCHOLE(&x->floc);
        x->signum = (signed char)0; x->laenge = (INT)1;
        }    /* ende des trivialfalles */
    else    {    /* normalfall x->laenge >= y->laenge >= 2 */
        /* lange division */
        LOCNULL(&null); 
        blocy = y->floc; 
        y->floc = NULL;
        locrezliste(&blocy); 
        locy1 = blocy; 
        locy0 = blocy->nloc;
        a = LOCBAS2() - (INT)1 - locms1(locy1);
        locx1 = x->floc; x->floc = NULL; locrezliste(&locx1);
        locx2 = NULL; LOCHOLE(&locx2); locx2->nloc = locx1;
        locx0 = locx1->nloc;
    
        /* dividend und divisor normieren. dividend zerlegen */
        locpsl(locx2,locx1,a);
        alocy = locy0; plocy = locy1; alocx = locx0; plocx = locx1;
        do    {
            locpsl(plocy,alocy,a); 
            locpsl(plocx,alocx,a);
            plocy = alocy; alocy = alocy->nloc;
            plocx = alocx; alocx = alocx->nloc;
            }
        while (alocy != NULL);
        locpsl(plocy,&null,a);
    
        llocx = plocx;
        rlocx = alocx;
    
        while (alocx != NULL)    /* rest des dividenden normieren */
            {
            locpsl(plocx,alocx,a);
            plocx = alocx; alocx = alocx->nloc;
            }
        locpsl(plocx,&null,a);
    
        llocx->nloc = NULL;     /* dividend getrennt */
    
        /* listen fuer teildividend und divisor umkehren */
        blocx = locx2; locrezliste(&blocx); locrezliste(&blocy);
    
        /* quotientenliste mit laenge */
        blocq = NULL; ql =(INT)0;
    
        do    {    /* divisionsschritt */
            if (locvgl(locx2,locy1) ==(INT)0) LOCMAX(&q);
            else    {
                LOCASS(&r,locx2);
                locdiv(&q,&r,locx1,locy1);
                LOCMUL(&hi,&lo,&q,locy0);
                /* falls (hi,lo) <= (r,locx0):fertig */
                vgl = locvgl(&hi,&r);
                if ((vgl >0) || ((vgl ==(INT)0) && 
                            (locvgl(&lo,locx0) >(INT)0)))
                    {
                    locssub(&q,(INT)1);
                    cy = locadd(&r,locy1,(INT)0);
                    if (cy ==(INT)0)
                        {
                        cy = locsub(&lo,locy0,(INT)0);
                        if (cy == (INT)1) cy = locssub(&hi,(INT)1);
                        vgl = locvgl(&hi,&r);
                        if (
                            (vgl >(INT)0) ||
                         ((vgl ==(INT)0) 
                    && 
        /* bug 050790 */      (locvgl(&lo,locx0) >(INT)0 )))
                            cy = locssub(&q,(INT)1);
                        }
                    }
                };

        /* subtrahiere q*divisor von teildivdend llocx = vorgaenger locx0 */
            alocy = blocy; alocx = blocx; cy = 0; cyn = 0; 
            LOCNULL(&ov);
            llocx = NULL; plocx = NULL;
            do    {
                LOCMUL(&hi,&lo,alocy,&q);
                cy = locadd(&lo,&ov,cy);
                LOCASS(&ov,&hi);
                cyn = locsub(alocx,&lo,cyn);
                plocx = alocx; alocx = alocx->nloc; alocy = alocy->nloc;
                if (alocx == locx0) llocx = plocx;
                }
            while (alocy != NULL);
            cy = locsadd(&ov,cy); cyn = locsub(alocx,&ov,cyn);
            if (cy !=(INT)0) 
                    return error("internal error:LO12");
    
            /* falls differenz negativ, q war um 1zu gross. korrektur */
    
            if (cyn == (INT)1)
                {
                cyn = locssub(&q,(INT)1);
                alocx = blocx; alocy = blocy; cy =(INT)0;
                do    {
                    cy = locadd(alocx,alocy,cy);
                    alocx = alocx->nloc; alocy = alocy->nloc;
                    }
                while (alocy != NULL);
                cy = locsadd(alocx,cy); 
                if (cy != (INT)1)  
                    return error("internal error:LO13");
                }
    
            /* quotientenziffer q abspeichern . locx2 ist frei dafuer */
            locx1->nloc = NULL;
            if ((blocq == NULL) && (LOCSGN(&q) ==(INT)0)) locrette(&locx2);
            else    {
                locx2->nloc = blocq; blocq = locx2; locx2 = NULL;
                LOCASS(blocq,&q); ql ++;
                };
    
            /* neuer teildividend */
            fertig = (rlocx == NULL);
            if (! fertig)
                {
                alocx = blocx; blocx = rlocx; rlocx = rlocx->nloc;
                blocx->nloc = alocx;
                locx2 = locx1; locx1 = locx0; locx0 = llocx;
                if (locx0 == NULL) locx0 = blocx; 
                }
            }
        while (! fertig);    /* ende divisionsschritt */
    
        /* quotient */
        if (blocq == NULL)
            {
            LOCHOLE (&x->floc); x->signum = (signed char)0;
            x->laenge = (INT)1;
            }
        else    {
            x->floc = blocq; blocq = NULL;
            x->signum = sx * sy; x->laenge = ql;
            }
    
        /* rest normierung rueckgaengig machen fuehrende nullen entfernen */
        i =(INT)0; llocx = NULL;
        plocx = blocx; alocx = plocx->nloc; 
        do    {
            i++;
        /* Seite 8 von test.p */
            locpsr(alocx,plocx,a);
            if (LOCSGN(plocx) !=(INT)0) 
                {
                llocx = plocx; rl = i;
                }
            plocx = alocx; alocx = alocx->nloc;
            }
        while (alocx != NULL);
        locpsr(&null,plocx,a);
        if (LOCSGN(plocx) !=(INT)0) { llocx = plocx; rl = i+ (INT)1; }
    
        if (llocx == NULL)    /* rest 0 */
            {
            loclisterette(&blocx->nloc); rest->floc = blocx;
            blocx = NULL; rest->signum = (signed char)0; rest->laenge = (INT)1;
            }
        else    {
            loclisterette(&llocx->nloc); rest->floc = blocx;
            blocx = NULL; rest->signum = sx; rest->laenge = rl;
            }
    
        /* divisor. normierung rueckgaengig machen */
        plocy = blocy; alocy = plocy->nloc;
        do    
            { 
            locpsr(alocy,plocy,a); 
            plocy = alocy; 
            alocy = alocy->nloc; 
            }
        while (alocy != NULL);

        locpsr(&null,plocy,a); 
        y->floc = blocy; 
        blocy = NULL;
        } /* lange divison */
    ENDR("ganzquores");
} /* ende ganzquores */


    
#ifdef UNDEF
static INT ganzganzdiv(x,y) struct longint *x,*y;
/* AK: Tue Mar 14 09:03:44 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 210891 V1.3 */
    {
    struct longint rest;

    rest.floc = NULL; 
    ganzquores(x,&rest,y); 
    ganzloesche(&rest);
    return OK;
    }
#endif

#ifdef UNDEF
static INT ganzmod(x,rest,y) struct longint *x,*y,*rest;
/* AK Tue Mar 14 09:05:54 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */

/* AK 130789 V1.0 *//* AK 250790 V1.1 */ /* AK 210891 V1.3 */
    {
    return ganzquores(x,rest,y);
    }
#endif



static INT ganzein(fp,x) FILE *fp; struct longint *x; 
/* AK 130789 V1.0 *//* AK 250790 V1.1 */ /* AK 270391 V1.2 */
/* AK 210891 V1.3 */
    {
    INT i;
    signed char sgn=(signed char)1;
    char c;
    

    fscanf(fp,"%ld",&i);
    if (i <(INT)0) 
        {
        sgn = (signed char)-1;
        i = i *(INT)-1;
        }
    ganzint(x,  i % gd.basis);
    while ((c=getc(fp)) == (char) gd.folgezeichen)
        {
        fscanf(fp,"%ld",&i);
        if (i <(INT)0) 
            {
            return error("internal error LO14");
            }
        ganzsmul(x,gd.basis);
        ganzsadd(x,i % gd.basis);
        }

    x->signum = sgn;
    return OK;
    }




static INT holeziffer(zd) struct zahldaten *zd;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    struct loc *adez;
    INT zzmod3,erg = OK;

    zd->ziffernzahl --;
    zzmod3 = zd->ziffernzahl % (INT)3;

    if (zzmod3 ==(INT)0) erg=zd->fdez->w0;
    if (zzmod3 ==(INT)1) erg=zd->fdez->w1;
    if (zzmod3 ==(INT)2) erg=zd->fdez->w2;

    if (zzmod3 ==(INT)0) 
        { adez = zd->fdez; zd->fdez = zd->fdez->nloc;
        adez->nloc = NULL; locrette(&adez); }
    
    return(erg);
    }



static INT ganzfziffer(zd) struct zahldaten *zd;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT z,f0;
    char buffer[200];

    if (zd->ziffernzahl == 0)
        { zd->mehr = FALSE; 
          //strcpy(zd->ziffer," "); 
        }
    else    {
        z = holeziffer(zd);
        if (zd->ziffernzahl > 0) zd->mehr=TRUE; else zd->mehr=FALSE;
        sprintf(buffer,"%ld",z);
        f0 = gd.basislaenge-strlen(buffer);
        sprintf(zd->ziffer,"%s","000000000000");
            /* max. 12 Nullen */
        sprintf(zd->ziffer + f0,"%ld",z);
        if (zd->mehr == TRUE)
            {
	    if (nofolgezeichen)
                sprintf(zd->ziffer,"%s", zd->ziffer);
	    else
                sprintf(zd->ziffer,"%s%c", zd->ziffer,gd.folgezeichen);
            }
        else
	    {
	    if (nofolgezeichen)
		    sprintf(zd->ziffer,"%s",zd->ziffer);
	    else
		    sprintf(zd->ziffer,"%s%c",zd->ziffer,' ');
            }
        }
    return(OK);
    }



static INT retteziffer(z,zd) INT    z; struct zahldaten *zd;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    struct loc *adez;
    INT zzmod3;
    INT erg =OK;

    zzmod3 = zd->ziffernzahl % (INT)3;

    if (zzmod3 ==(INT)0) {
        adez = NULL; 
        LOCHOLE(&adez);
        adez ->nloc = zd->fdez; 
        zd->fdez = adez; 
        }
    if (zzmod3 ==(INT)0) zd->fdez->w0 = z;
    if (zzmod3 ==(INT)1) zd->fdez->w1 = z;
    if (zzmod3 ==(INT)2) zd->fdez->w2 = z;

    zd->ziffernzahl ++; 
    ENDR("retteziffer");
    }



static INT ganz1ziffer(zd,x) struct zahldaten *zd; struct longint    *x;
/* AK 130789 V1.0 */ /* AK 030790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT z;
    signed char sgn;
    struct longint xx;

    zd->fdez =  NULL; zd->ziffernzahl =(INT)0; xx.floc = NULL;
    (zd->ziffer)[0] = '\0';
    lochole(&xx.floc); 
    ganzkopiere(&xx,x); 
    sgn = xx.signum;
    if (xx.signum < (signed char)0) xx.signum = -xx.signum;

    while (xx.signum > (signed char)0)
        { ganzsquores(&xx,&z,gd.basis); retteziffer(z,zd); }
    if (zd->ziffernzahl ==(INT)0)
        { zd->mehr = FALSE; 
          // strcpy(zd->ziffer," "); 
        }
    else    {
        z = holeziffer(zd); z = sgn * z;
        zd->mehr = (zd->ziffernzahl >(INT)0);
        if (zd->mehr == TRUE)
            {
	    if (nofolgezeichen)
		  sprintf(zd->ziffer,"%s%ld",zd->ziffer,z);
            else 
		  sprintf(zd->ziffer,"%s%ld%c",zd->ziffer,z,gd.folgezeichen);
            }
        else    
          sprintf(zd->ziffer,"%s%ld",zd->ziffer,z);
        }
    locrette(& xx.floc);
    return(OK);
    }


static INT ganzaus_str(string,x) char *string; struct longint *x; 
/* AK 020295 */
    {
    struct zahldaten zd;
    int i,k;
    string[0]='\0';
    if (x->signum == 0) /* AK 060502 */
        {
        strcat(string," 0 ");
        goto ende;
        }
    ganz1ziffer(&zd,x);
    k = strlen(zd.ziffer);
    if (zd.ziffer[k-1] == gd.folgezeichen)
        {
        zd.ziffer[k-1] = '\0';
        k--;
        }
    strcat(string,zd.ziffer);
    i = k;
    while (zd.mehr == TRUE)
        {
        ganzfziffer(&zd);
        k = strlen(zd.ziffer);
        if (zd.ziffer[k-1] == gd.folgezeichen)
            {
            zd.ziffer[k-1] = '\0';
            k--;
            }
        strcat(string,zd.ziffer);
        i+=k;
        }
ende:
    return OK;
    }

INT mem_size_longint(a) OP a;
/* AK V2.0 080903 */
{
    INT erg = OK, res = 0;
    struct longint *x;
    CTO(LONGINT,"mem_size_longint(1)",a);
    res = sizeof(struct object);
    res += sizeof(struct longint);
    x = S_O_S(a).ob_longint;
    res += ((x->laenge)*sizeof(struct loc));
    return res;
    ENDR("mem_size_longint"); 
}

static INT ganzaus(fp,x) FILE *fp; struct longint *x; 
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    struct zahldaten zd;
    char *blanks = (char *) SYM_calloc(201,sizeof(char));
    char *zeile  = (char *) SYM_calloc(201,sizeof(char));
    INT    i;

    if (x->signum == 0) /* AK 060502 */
        {
        fprintf(fp," 0 ");
        if (fp == stdout) 
            zeilenposition  += 3;
        else if (fp == texout)
            texposition  += 3;
        goto ende;
        }

    for (i=1;i<gd.auspos;i++) blanks[i-1]=' ';
    blanks[(gd.auspos)-1]='\0';

    zd.ziffer[0] = '\0';

    zeile[0]='\0';
    gd.auszz = 0;

    ganz1ziffer(&zd,x);
    strcat(zeile,zd.ziffer);

    while (zd.mehr == TRUE)
        {
        ganzfziffer(&zd);
        if ((INT)strlen(zeile) + (INT)strlen(zd.ziffer) > gd.auslaenge)
            { 
            if (nofolgezeichen)
		    fprintf(fp,"%s",zeile);
            else
		    fprintf(fp,"%s%s\n",blanks,zeile);
            strcpy(zeile,zd.ziffer); gd.auszz++; 
            }
        else    strcat(zeile,zd.ziffer);

        }
    
    if (fp == stdout) {
        zeilenposition  += strlen(zeile); 
        zeilenposition  += strlen(blanks);
        }
    else if (fp == texout)
        {
        texposition  += strlen(zeile); 
        texposition  += strlen(blanks);
        }

            if (nofolgezeichen)
		    fprintf(fp,"%s",zeile);
	    else
		    fprintf(fp,"%s%s",blanks,zeile);
    if (fp == stdout)
        if (zeilenposition >(INT)70)
            { fprintf(fp,"\n"); zeilenposition =(INT)0; }
    if (fp == texout)
        if (texposition >(INT)70)
            { fprintf(fp,"\n"); texposition =(INT)0; }

        
    gd.auszz++; 
    SYM_free(blanks); 
    SYM_free(zeile); 
ende:
    return(OK);
    }



static INT ganzmul(x,y) struct longint *x,*y;
/* AK Mon Jan 16 09:26:56 MEZ 1989 */
/* x = x * y */
/* AK 180789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    struct loc *alocx, *alocy,   *ploca, *floca, *bloca, *aloca;
    struct loc hi,lo,ov;
    INT    cy,cya;
    INT     hh; /* fuer LOCADD,LOCMUL */
    INT erg =OK;



    x->signum = x->signum * y ->signum;
    if (x->signum == (signed char)0)
        { 
        loclisterette(& (x->floc->nloc));
        LOCNULL(x->floc); 
        x->laenge =(INT)1; 
        return OK;
        /* das ergebnis ist null */ 
        }

    /* das ergebnis ist nicht null */
    x->laenge = x->laenge + y->laenge;
    floca = NULL; LOCHOLE(&floca); bloca = floca; alocx = x->floc->nloc;
    ploca = floca; aloca = NULL;
    while (alocx != NULL)
        { LOCHOLE(&aloca); ploca->nloc = aloca;
        ploca = aloca; aloca = NULL; alocx = alocx->nloc; }

    alocy = y->floc;

    do    {
        cya =(INT)0; 
        LOCNULL(&ov); cy =(INT)0; alocx = x->floc; aloca = bloca;
        do    { LOCMUL(&hi,&lo,alocx,alocy); 
            cy = LOCADD(&lo,&ov, cy);
            ov = hi; cya = LOCADD(aloca,&lo,cya);
            alocx=alocx->nloc; ploca=aloca; aloca = aloca->nloc; }
        while (alocx !=  NULL);
        cy = locsadd(&ov, cy+cya);
            /* cy ist jetzt 0 */
            if (cy !=(INT)0) 
                return error("internal error:LO2");
        LOCHOLE(&aloca);
        ploca->nloc = aloca;
        LOCASS(aloca,&ov);
        bloca = bloca->nloc;
        alocy = alocy->nloc;
        }
    while (alocy != NULL);

    if (LOCSGN(aloca ) ==(INT)0)
        {
        locrette(&(ploca->nloc));
        x->laenge --;
        }
    loclisterette(&x->floc);
    x->floc = floca;
    ENDR("ganzmul");
    }



static INT ganzsmul(x,a) struct longint *x; INT    a;
/* AK Mon Mar 13 10:08:51 MEZ 1989 */ /* AK 050790 V1.1 */
/* AK 210891 V1.3 */
{
    struct loc *alocx, *plocx;
    INT    ue,erg =OK;

    if (a==(INT)0)
        {
        loclisterette(&(x->floc->nloc));
        x->signum = (signed char)locint(x->floc,(INT)0);
        x->laenge =(INT)1;
        }
    else if (a ==(INT)1) ;
    else if (a ==(INT)-1) x->signum = - x->signum;
    else    {
        if (a<(INT)0) x->signum = - x->signum;
        alocx = x->floc; 
        plocx = NULL; 
        if (a<(INT)0) a = -a;
        ue =(INT)0;
        do    { 
            ue = locsmul(alocx,a,ue);
            plocx = alocx; 
            alocx = alocx ->nloc; 
            }
        while (alocx != NULL);
        if (ue !=(INT)0)
            { 
            LOCHOLE(&alocx); 
            plocx->nloc = alocx; 
            x->laenge ++;
            ue = locint(alocx,ue); 
            }
        }
    ENDR("ganzsmul");
}




static INT ganzsadd(x,y) struct longint *x; INT y; 
/* AK 180789 V1.0 */ /* AK 070390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT cy,xl,ll;
    INT erg =OK;
    signed char xs,ys;
    struct loc *lloc,*alocx,*plocx=NULL;

    xl = x->laenge; 
    xs = x->signum;
    if (y>(INT)0) 
        ys=(signed char)1; 
    else if (y<(INT)0) 
        ys = (signed char)-1; 
    else 
        ys=(signed char)0;
    if (y<(INT)0) y = -y;

    if (    ((xs>=(signed char)0)&&(ys>=(signed char)0))
        ||
        ((xs<(signed char)0)&&(ys < (signed char)0))
       )
        {
        alocx = x->floc; 
        cy = y;
        while ((alocx != NULL)&&(cy !=(INT)0))
            {
            cy = locsadd(alocx,cy); 
            plocx = alocx;
            alocx = alocx->nloc;
            }
        if (cy !=(INT)0) 
            {
            LOCHOLE(&alocx); 
            plocx->nloc = alocx;
            locint(alocx,cy);
            xl ++;
            }
        if (xs == (signed char)0) 
            xs = ys;
        }
    else    {
        alocx = x->floc;
        cy = y;
        while ((alocx != NULL) && (cy !=(INT)0))
            { 
            cy = locssub(alocx,cy);
            plocx = alocx; 
            alocx = alocx->nloc; 
            }
        if (cy !=(INT)0)
            {
            alocx = x->floc; 
            lloc = NULL; 
            ll = (INT) 1; 
            cy = (INT) 0;
            do    { 
                cy = locneg(alocx,cy);
                if (LOCSGN(alocx) != (INT) 0 )
                    { lloc = alocx; xl = ll; }
                alocx = alocx->nloc;
                ll ++;
                }
            while (alocx != NULL);
            loclisterette(&(lloc->nloc));
            xs = -xs;
            if (xs == (signed char)0) 
                xs = (signed char)-1;
            }
        else     { 
            alocx = x->floc; 
            lloc = NULL; 
            ll = (INT)1;
            do    {
                if (LOCSGN(alocx) !=(INT)0)
                    { 
                    lloc = alocx; 
                    xl = ll; 
                    }
                alocx = alocx->nloc;
                ll ++;
                }
            while (alocx != NULL);
            if (lloc == NULL)
                {
                loclisterette(&(x->floc->nloc));
                xs = (signed char)0; 
                xl = (INT)1;
                }
            else     loclisterette(&(lloc->nloc));
            }
        }
    x->laenge = xl; 
    x->signum = xs;
    ENDR("ganzsadd");
    }
            


static INT ganzvergleich(x,y) struct longint *x,*y;
/* AK Thu Jan 12 09:08:15 MEZ 1989 */
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    struct loc *alocx, *alocy;
    INT    av,lv;
    signed char sx,sy;

    sx = x->signum; 
    sy = y->signum;
    if (sx>sy) 
        return((INT)1);
    if (sx<sy) 
        return (INT) -1;
    /* es gilt nun gleiches vorzeichen */
    if (sx==(signed char)0) 
        return((INT)0);
    if (x->laenge > y->laenge) 
        return((INT)sx);
    if (x->laenge < y->laenge) 
        return((INT)-sy);

    /* es gilt nicht nur gleiches vorzeichen sondern auch
    gleiche laenge */
    alocx = x->floc;
    alocy = y->floc;
    lv = 0;
    do    
        { 
        av = locvgl(alocx,alocy);
        if (av != 0) lv = av;
        alocx = alocx->nloc; 
        alocy = alocy->nloc; 
        }
    while (alocx != NULL);

    if (sx>(signed char)0) 
        return(lv); 
    else 
        return(-lv);
    }



static INT intganz(x) struct longint *x;
/* AK 150290 V1.1 */ /* umwandlung longint to int falls moeglich sonst fehler */
/* AK 210891 V1.3 */
    {
    if ( x->signum < 0) 
        return  - x->floc->w0 - x->floc->w1 * LO_B - x->floc->w2 * LO_B * LO_B ;
    else
        return (x->floc->w0&BMINUSEINS) 
              +(x->floc->w1&BMINUSEINS) * LO_B 
              +(x->floc->w2&BMINUSEINS) * LO_B * LO_B;
    }

static INT ganzint(x,i) struct longint *x; INT    i; 
/* AK Thu Jan 12 13:18:53 MEZ 1989 */
/* AK 130789 V1.0 */ /* AK 150290 V1.1 */ /* AK 210891 V1.3 */
    {
    if (x->floc->nloc != NULL) 
        loclisterette(& x->floc->nloc );

    if (i == MAXNEG) { 
        /* AK 251001 */ 
        /* sonst ist locint fehlerhaft */
        x->laenge = (INT)1;
        x->signum = (signed char)locint(x->floc,i+1);
        ganzsadd(x,(INT)-1);
        }
    else {
        x->laenge = (INT)1;
        x->signum = (signed char)locint(x->floc,i);
        }
    return(OK);
    }


static INT ganzeven(x) struct longint *x;
/* AK 061190 V1.1 */ /* AK 210891 V1.3 */
    {
    return not locodd(x->floc);
    }



static INT ganzodd(x) struct longint *x;
/* AK 061190 V1.1 */ /* AK 210891 V1.3 */
    {
    return locodd(x->floc);
    }



static INT ganzkopiere(x,a) struct longint *x,*a; 
/* x:= a AK umgeschrieben in C Fri Jan 20 07:46:34 MEZ 1989 */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    struct loc *alocx, *plocx, *aloca;
    if (a->floc == NULL) { /* AK 060502 */
        /* a == 0 */
        if (x->floc != NULL) FREE_LOC(x->floc); /* was initialised in init_longint */
        x->laenge = 0;
        x->floc = NULL;
        goto ee;
        }

    SYMCHECK( x->floc == a->floc, "internal error:LO4");

    x->signum = a->signum; 
    x->laenge = a->laenge;
    aloca = a->floc; 
    alocx = x->floc; 
    plocx = NULL;

    do    
        { 
        if (alocx == NULL)
            { 
            LOCHOLE(&alocx); 
            plocx->nloc = alocx; 
            }
        LOCASS(alocx,aloca);
        aloca = aloca->nloc; 
        plocx = alocx; 
        alocx = alocx->nloc;
        }
    while (aloca != NULL);

    /* loclisterette(&(plocx->nloc)); */
    if (plocx->nloc != NULL) {
        FREE_LOC(plocx->nloc);
        plocx->nloc = NULL;
        }
ee:
    ENDR("internal function:ganzkopiere");
    }


INT mult_longint_integer(a,b,c) OP a,b,c;
{
    INT erg = OK,i,j,p,u,s,p2;
    static INT sp[14],sp2[14];
    struct longint *x;
    struct loc *alocx;
 
    CTO(LONGINT,"mult_longint_integer(1)",a);
    CTO(INTEGER,"mult_longint_integer(2)",b);
    CTO(EMPTY,"mult_longint_integer(3)",c);

    if (NULLP_INTEGER(b) || NULLP_LONGINT(a) ) {
        M_I_I(0,c);
        goto ende;
        }

    x = S_O_S(a).ob_longint;
    if (x->laenge > 4) {
        erg += mult_longint_integer_via_ganzsmul(a,b,c);
        goto ende;
        }
    s = x->signum;
    if (S_I_I(b) < 0) { p = -S_I_I(b); s = -s; } else p = S_I_I(b);
 
     if (p > 1073741824) { 
         erg += mult_longint_integer_via_ganzsmul(a,b,c);
         goto ende;
         } 
 
 
    i=0; alocx = x->floc;
xx:
    sp[i++] = alocx->w0;
    sp[i++] = alocx->w1;
    sp[i++] = alocx->w2;
    if (alocx -> nloc) { alocx = alocx->nloc; goto xx; }
    sp[i] = 0; sp[i+1] = 0;

    if (p <= 32768 ) { 
        j = 0;u  = 0;
        while (j <=i)
            {
            sp [j] *= p;
            sp [j] += u;
            u = sp[j] >> 15;
            sp [j] &= BMINUSEINS;
            j++;
            }
        }
    else {
        j = 0; u = 0;p2 = p >> 15;
        while (j <=i)
            {
            sp2 [j] = sp[j] * p2;
            sp2 [j] += u;
            u = sp2[j] >> 15;
            sp2 [j] &= BMINUSEINS;
            j++;
            }
        j = 0;u  = 0; p &= BMINUSEINS;
        while (j <=i)
            {
            sp [j] *= p;
            sp [j] += u;
            if (j>0) sp[j] += sp2[j-1];
            u = sp[j] >> 15;
            sp [j] &= BMINUSEINS;
            j++;
            }
        sp[i+1] = sp2[i]+u; /* AK 030502 +u was missing */
        }
 
    INIT_LONGINT(c);
    x = S_O_S(c).ob_longint;
    alocx = x->floc; j = 0;u=0;
    x ->signum = s;
 
again:
    alocx->w0 = sp[j++];
    alocx->w1 = sp[j++];
    alocx->w2 = sp[j++];
    if ((j==i) && ( (sp[j] != 0) || (sp[j+1] != 0)) ) {
        x->laenge ++;
        LOCHOLE(& alocx->nloc);
        alocx->nloc->w0 = sp[j];
        alocx->nloc->w1 = sp[j+1];
        }
    else if (j < i) {
        x->laenge ++;
        LOCHOLE(& alocx->nloc);
        alocx = alocx->nloc;
        goto again;
        }
 
ende:
    ENDR("mult_longint_integer");
 
}





static INT lochole(aloc) struct loc   **aloc; 
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg =OK;
    CALLOC_MEMMANAGER(struct loc,loc_speicher,loc_index,loc_counter,*aloc);
    LOCNULL(*aloc);
    (*aloc)->nloc = NULL;
    ENDR("lochole");
    }



static INT loclisterette(aloc) struct loc **aloc; 
/* AK 130789 V1.0 */ /* AK 010290 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    struct loc *aloc1, *ploc1;
    if (*aloc != NULL)
        {
        aloc1=   (*aloc);
        do { 
            ploc1 = aloc1->nloc; 
            FREE_LOC(aloc1); 
            aloc1 = ploc1; 
            }
        while     (aloc1 != NULL);
        *aloc = NULL; 
        }
    ENDR("intenal function:loclisterette");
    }



static INT locrette(aloc) struct loc **aloc;
/* AK 130789 V1.0 */ /* AK 100190 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    if (*aloc != NULL)
        {
        FREE_LOC(*aloc);
        *aloc = NULL;
        }
    ENDR("internal function:locrette");
    }



static INT locrezliste(aloc) struct loc **aloc;
/* AK Thu Jan 12 08:06:59 MEZ 1989 */
/* dreht liste um */
/* AK 100190 V1.1 */ /* AK 210891 V1.3 */
    {
    struct loc *lloc,*rloc,*hloc;
    if (*aloc != NULL)
        {
        lloc = NULL; 
        rloc = *aloc;
        while (rloc != NULL)
            {
            hloc = rloc->nloc;
            rloc->nloc=lloc;
            lloc=rloc;
            rloc=hloc;
            }
        *aloc = lloc;
        }
    return(OK);
    }



static INT schon_da =(INT)0;
INT start_longint()
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    OP a,b;
    INT erg = OK;
    INT i;
    SYMCHECK (schon_da == 1, "start_longint: already initialised");
        
    schon_da = 1;

    ANFANG_MEMMANAGER(loc_speicher,loc_index,loc_size,loc_counter);

    ANFANG_MEMMANAGER(longint_speicher,longint_speicherindex,
                      longint_speichersize,mem_counter_loc);

    erg += ganzanfang();
    erg += ganzparam((INT)1000000,(INT)2,(INT)70,'.');
    a = callocobject();
    b = callocobject();
    M_I_I((INT)1000,b);
    for (i=(INT)0;i<(INT)100;i++)
        {
        erg += random_integer(a,NULL,NULL);
        if (S_I_I(a) !=(INT)0)
            MULT_APPLY_INTEGER(a,b);
        }
    erg += random_longint(a,b);
    FREEALL2(a,b);
    ENDR("start_longint");
    }



INT longint_ende()
{
    INT erg = OK;
    schon_da = (INT)0;
    if (rl_o != NULL) { erg += freeall(rl_o); rl_o = NULL; }
    if (rl_m != NULL) { erg += freeall(rl_m); rl_m = NULL; }
    if (rl_a != NULL) { erg += freeall(rl_a); rl_a = NULL; }
    if (rl_x != NULL) { erg += freeall(rl_x); rl_x = NULL; }
    
    ENDE_MEMMANAGER(loc_speicher,loc_index,
                    loc_size,loc_counter,"loc_speicher not freed");
    ENDE_MEMMANAGER(longint_speicher,longint_speicherindex,
                      longint_speichersize,mem_counter_loc,
                      "longint_speicher not freed");

    erg += longint_speicher_ende();
    ENDR("longint_ende");
}


static struct longint * calloclongint()
/* AK 170888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg =OK;
    struct longint *ergebnis;
    CALLOC_MEMMANAGER(struct longint,longint_speicher,
                      longint_speicherindex,mem_counter_loc,ergebnis);
    return ergebnis;
    ENDTYP("calloclongint",struct longint *);
    }





static INT longint_speicher_ende()
/* AK 230101 */
{
    INT i;
 
    for (i=0;i<=longint_speicherindex;i++)
        SYM_free(longint_speicher[i]);
    SYM_free(longint_speicher);
    longint_speicher=NULL;
    longint_speicherindex=-1;
    longint_speichersize=0;
    return OK;
}



static INT ganzparam(basis,auspos,auslaenge,folgezeichen) 
    INT basis,auspos,auslaenge;
    char    folgezeichen;
/* AK Mon Mar 13 10:24:35 MEZ 1989 */
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    if (basis>(INT)1) gd.basis=basis; 
    else return error("internal error:LO5");

    if (auspos>(INT)1) gd.auspos=auspos; else gd.auspos = 2;
    if (basis <= (INT)10) gd.basislaenge = 1; else
    if (basis <= (INT)100) gd.basislaenge = 2; else
    if (basis <= (INT)1000) gd.basislaenge = 3; else
    if (basis <= (INT)10000) gd.basislaenge = 4; else
    if (basis <= (INT)100000) gd.basislaenge = 5; else
    if (basis <= (INT)1000000) gd.basislaenge = 6; else
    if (basis <= (INT)10000000) gd.basislaenge = 7; else
    if (basis <= (INT)100000000) gd.basislaenge = 8; else
    if (basis <= (INT)1000000000) gd.basislaenge = 9; else
                  gd.basislaenge = 10;
    if (auslaenge > gd.basislaenge) gd.auslaenge = auslaenge;
    else gd.auslaenge = gd.basislaenge+1;
    gd.folgezeichen = folgezeichen;return(OK);
    }



static INT ganzanfang() 
/* AK: Tue Mar 14 08:43:55 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    gd.auszz =(INT)0;
    gd.basis = (INT)1000000; gd.basislaenge = (INT)6; 
    gd.folgezeichen = '.';
    gd.auspos =(INT)2; gd.auslaenge = (INT)78; return(OK);
    }



static INT ganzdefiniere(x) struct longint *x;
/* AK: Tue Mar 14 08:47:54 MEZ 1989 */
/* dieser Teil wurde von Peter Hain in Karlsruhe
entworfen. Er schrieb diese Langzahl arithmetik in Pascal und
Assembler. In Bayreuth wurden in Form eines Seminars die
Assemblerteile in C geschrieben und spaeter wurde von
Axel Kohnert die restlichen Pascalteile in C uebersetzt.
Die Ein und Ausgabe routinen wurden vollstaendig in Bayreuth
entworfen */
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    x->signum = (signed char)0; 
    x->laenge = (INT)1; 
    x->floc = NULL;
    lochole(&x->floc);
    return(OK);
    }



INT init_longint(l) OP l;
/* AK 170888 */ /* AK 130789 V1.0 */ /* AK 040790 V1.1 */
/* AK 210891 V1.3 */
    {
    INT erg = OK;
    OBJECTSELF c;

    CTO(EMPTY,"init_longint",l);
   
    c.ob_longint = calloclongint();
    B_KS_O(LONGINT,c,l);
    c = S_O_S(l);
    ganzdefiniere(c.ob_longint);
    ENDR("init_longint");
    }




INT sprint_longint(t,l) char *t; OP l;
/* AK 020295 */
/* AK 240398 V2.0 */
    {
    INT erg=OK;
    OBJECTSELF c;
    CTO(LONGINT,"sprint_longint",l);
    c = S_O_S(l);
    erg += ganzaus_str(t, c.ob_longint);
    ENDR("sprint_longint");
    }

INT fprint_longint(f,l) FILE *f; OP l;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    OBJECTSELF c;

    c = S_O_S(l);
    erg += ganzaus(f, c.ob_longint);
    ENDR("fprint_longint");
    }





INT tex_longint(l) OP l;
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */
/* AK 070291 V1.2 texout instaed of stdout for output */ /* AK 210891 V1.3 */
    {
    INT ts = texmath_yn;
    INT erg = OK;
    CTO(LONGINT,"tex_longint(1)",l);

    if (ts == 0L) fprintf(texout," $ "); else fprintf(texout," ");
    erg += fprint_longint(texout,l); 
    if (ts == 0L) fprintf(texout," $ "); else fprintf(texout," ");
    if (ts == 0L) texposition += (INT)6; else texposition += (INT)2;
    ENDR("tex_longint");
    }



INT copy_longint(a,c) OP a,c;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 030790 V1.1 */
/* AK 210891 V1.3 */
/* AK 010399 V2.0 */
    {
    INT erg = OK;
    CTO(LONGINT,"copy_longint(1)",a);
    CTTO(INTEGER,EMPTY,"copy_longint(2)",c);

    INIT_LONGINT(c);
    erg += ganzkopiere(S_O_S(c).ob_longint,S_O_S(a).ob_longint);
    ENDR("copy_longint");
    }


INT invers_longint(a,c) OP a,c;
/* AK 010399 V2.0 */
    {
    INT erg = OK;
    CTO(LONGINT,"invers_longint(1)",a);
    CTTO(INTEGER,EMPTY,"invers_longint(2)",c);
    erg += m_ou_b(cons_eins,a,c);
    C_B_I(c,GEKUERZT);
    ENDR("invers_longint");
    }




INT freeself_longint(a) OP a;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 030790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    struct longint *x;
    CTO(LONGINT,"freeself_longint(1)",a);

    x = S_O_S(a).ob_longint;
    loclisterette(&x->floc);
    x->laenge =(INT)0; 
    x->signum = (signed char)0;
    FREE_LONGINT(x);

    C_O_K(a,EMPTY);

    ENDR("freeself_longint");
    }


INT add_longint_longint(a,c,l) OP a,c,l;
/* AK 251001 */
{
    INT erg = OK;
    CTO(LONGINT,"add_longint(1)",a);
    CTO(LONGINT,"add_longint(2)",c);
    CTO(EMPTY,"add_longint(3)",l);

    erg += copy_longint(a,l);
    erg += ganzadd(S_O_S(l).ob_longint, S_O_S(c).ob_longint);
    erg += t_longint_int(l);
    ENDR("add_longint_longint");
}

INT intlog_longint(a) OP a;
/* AK 170306 */
{
	struct longint *as;
	as = S_O_S(a).ob_longint;
	return 45 * as->laenge;
}

INT add_longint(a,c,l) OP a,c,l;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"add_longint(1)",a);
    CTO(EMPTY,"add_longint(3)",l);

    switch(S_O_K(c))
        {
#ifdef BRUCHTRUE
        case BRUCH: erg += add_bruch_scalar(c,a,l);
            if (S_O_K(l) == LONGINT)
                erg += t_longint_int(l);
            goto al_ende;
#endif /* BRUCHTRUE */
        case INTEGER: 
            erg += add_longint_integer(a,c,l);
            goto al_ende;
        case LONGINT:
            {
            OBJECTSELF ls,cs;

            erg += copy_longint(a,l);
            ls = S_O_S(l);
            cs = S_O_S(c);
            erg += ganzadd(ls.ob_longint,cs.ob_longint);
                /* longinteger-addition ist x:= x+y */
            erg += t_longint_int(l);
            };
            goto al_ende;

#ifdef SCHURTRUE /* AK 240102 */
        case SCHUR:
            erg += add_schur(c,a,l);
            goto al_ende;
        case HOMSYM:
            erg += add_homsym(c,a,l);
            goto al_ende;
        case POWSYM:
            erg += add_powsym(c,a,l);
            goto al_ende;
        case ELMSYM:
            erg += add_elmsym(c,a,l);
            goto al_ende;
        case MONOMIAL:
            erg += add_monomial(c,a,l);
            goto al_ende;
#endif /* SCHURTRUE */

        default:{
            erg += WTO("add_longint(2)",c);
            goto al_ende;
            }
        };
al_ende:
    ENDR("add_longint");
    }


INT mult_longint(a,c,l) OP a,c,l;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"mult_longint(1)",a);
    CTO(EMPTY,"mult_longint(3)",l);

    switch (S_O_K(c))
        {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg+=mult_bruch_longint(c,a,l);
            goto me;
#endif /* BRUCHTRUE */

#ifdef INTEGERTRUE
        case INTEGER: 
            erg+=mult_longint_integer(a,c,l);
            goto me;
#endif /* INTEGERTRUE */

#ifdef MATRIXTRUE
        case MATRIX: 
            erg+=mult_scalar_matrix(a,c,l);
            goto me;
#endif /* MATRIXTRUE */

#ifdef MONOMTRUE
        case MONOM: 
            erg+=mult_scalar_monom(a,c,l);
            goto me;
#endif /* MONOMTRUE */

        case LONGINT: 
            erg+=mult_longint_longint(a,c,l);
            goto me;

        case POLYNOM: 
            erg+=mult_scalar_polynom(a,c,l);
            goto me;

#ifdef GRALTRUE
        case GRAL: 
            erg+=mult_scalar_gral(a,c,l);
            goto me;
#endif /* GRALTRUE */

#ifdef SCHUBERTTRUE
        case SCHUBERT: 
            erg += mult_scalar_schubert(a,c,l);
            goto me;
#endif /* SCHUBERT */

#ifdef SQRADTRUE
        case SQ_RADICAL:
            erg += mult_scalar_sqrad(a,c,l);
            goto me;
#endif /* SQRADTRUE */

#ifdef SCHURTRUE
        case ELMSYM:
            erg+=mult_elmsym_scalar(c,a,l);
            goto me;
        case HOMSYM:
            erg+=mult_homsym_scalar(c,a,l);
            goto me;
        case POWSYM:
            erg+=mult_powsym_scalar(c,a,l);
            goto me;
        case MONOMIAL:
            erg+=mult_monomial_scalar(c,a,l);
            goto me;
        case SCHUR: 
            erg+=mult_schur_scalar(c,a,l);
            goto me;
#endif /* SCHURTRUE */

#ifdef CHARTRUE
        case SYMCHAR: 
            erg+=mult_scalar_symchar(a,c,l);
            goto me;
#endif /* CHARTRUE */

#ifdef VECTORTRUE
        case COMPOSITION:
        case WORD:
        case INTEGERVECTOR:
        case VECTOR: 
            erg+=mult_scalar_vector(a,c,l);
            goto me;
#endif /* VECTORTRUE */

        default:
            {
            erg += WTO("mult_longint(2)",a);
            break;
            }
        };
me:
    ENDR("mult_longint");
    }



INT mult_longint_longint(a,c,l) OP a ,c,l;
/* AK 310590 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"mult_longint_longint(1)",a);
    CTO(LONGINT,"mult_longint_longint(2)",c);
    CTO(EMPTY,"mult_longint_longint(3)",l);
    erg += copy_longint(a,l);
    erg += ganzmul(S_O_S(l).ob_longint,S_O_S(c).ob_longint);
        /* longinteger-multiplikation ist x:= x*y */
    ENDR("mult_longint_longint");
    }


INT square_apply_longint(a) OP a;
/* AK 271101 */
{
    INT erg = OK;
    OP c;
    CTO(LONGINT,"square_apply_longint(1)",a);
    c = CALLOCOBJECT();
    erg += copy_longint(a,c);
    erg += ganzmul(S_O_S(a).ob_longint,S_O_S(c).ob_longint);
    FREEALL(c);
    ENDR("square_apply_longint");
}


INT absolute_longint(a,b) OP a,b;
/* AK 150393 */
{
    if (negp_longint(a))
        return addinvers_longint(a,b);
    return copy_longint(a,b);
}



INT addinvers_apply_longint(a) OP a;
/* AK 201289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"addinvers_apply_longint(1)",a);
    GANZNEG(S_O_S(a).ob_longint);
    ENDR("addinvers_apply_longint");
    }



INT ggt_longint_longint_sub(a,b,c) OP a,b,c;
/* AK 021101
   fast als mit mod
*/
/* ggt ist immer positiv */
{
    INT erg = OK;
    INT t;
    OP d;

    CTO(LONGINT,"ggt_longint_longint_sub(1)",a);
    CTO(LONGINT,"ggt_longint_longint_sub(2)",b);
    CTO(EMPTY,"ggt_longint_longint_sub(3)",c);

    if (NULLP_LONGINT(a)) 
        { 
        COPY(b,c); 
        if (NEGP(c)) ADDINVERS_APPLY(c);
        goto endr_ende; 
        }
    if (NULLP(b)) 
        { 
        COPY(a,c); 
        if (NEGP(c)) ADDINVERS_APPLY(c);
        goto endr_ende; 
        }

    d = CALLOCOBJECT();
    if (NEGP_LONGINT(a)) 
        erg += addinvers_longint(a,d);
    else
        COPY(a,d);
    if (NEGP(b)) 
        ADDINVERS(b,c);
    else
        COPY(b,c);

   
    while((t=COMP(d,c)) != 0)  {
        if (t == 1) {
            ADDINVERS_APPLY(c);
            ADD_APPLY(c,d);
            ADDINVERS_APPLY(c);
            }
        else {
            ADDINVERS_APPLY(d);
            ADD_APPLY(d,c);
            ADDINVERS_APPLY(d);
            }
        }
    FREEALL(d);
    ENDR("ggt_longint_longint_sub");
}

INT ggt_longint(a,b,c) OP a,b,c;
/* AK 191001 */
/* ggt ist immer positiv */
{
    INT erg = OK;
    CTO(LONGINT,"ggt_longint(1)",a);
    CTO(EMPTY,"ggt_longint(3)",c);

    if (S_O_K(b) == INTEGER) 
        erg += ggt_integer_longint(b,a,c);
    else if (S_O_K(b) == LONGINT) 
        erg += ggt_longint_longint(a,b,c);
    else 
        erg += WTO("ggt_longint(2)",b);

    ENDR("ggt_longint");
}

INT ggt_longint_integer(a,b,c) OP a,b,c;
/* ggt ist immer positiv */
{
    return ggt_integer_longint(b,a,c);
}

INT oddify_longint();

#define ODDIFY(a)\
/* a is even becomes odd */\
/* a is not zero */\
do { \
if (S_O_K(a) == INTEGER) {\
    while (EVEN_INTEGER(a)) HALF_APPLY_INTEGER(a);\
    }\
else if (S_O_K(a) == LONGINT) {\
    oddify_longint(a);\
    }\
else {\
    do HALF_APPLY(a); while (EVEN(a));\
} \
} while(0)

#define ZEROBITS(a,b)\
if (S_O_K(a) == INTEGER) { INT zbi=1;\
    b=0; while (not (zbi&S_I_I(a)) ) { b++; zbi <<=1; }\
}\
else /* LONGINT */ {\
struct loc *alocx;\
INT zbi=1;\
b=0;\
alocx = (S_O_S(a).ob_longint) -> floc;\
do {\
if (alocx -> w0 != 0) {\
    while (not (zbi&alocx -> w0) ) { b++; zbi <<=1; }\
    break;\
    }\
else if (alocx -> w1 != 0) {\
    b+= 15;\
    while (not (zbi&alocx -> w1) ) { b++; zbi <<=1; }\
    break;\
    }\
else if (alocx -> w2 != 0) {\
    b+= 30;\
    while (not (zbi&alocx -> w2) ) { b++; zbi <<=1; }\
    break;\
    }\
else {\
    b += 45;\
    alocx = alocx->nloc;\
    }\
} while(1); \
}


INT ggt_longint_longint(a,b,d) OP a,b,d;
/* AK 010202 */
/* always positive */
{
    INT ah,bh,c,erg = OK;
    OP ac,bc;
    CTTO(LONGINT,INTEGER,"ggt_longint_longint(1)",a);
    CTTO(LONGINT,INTEGER,"ggt_longint_longint(2)",b);
    CTO(EMPTY,"ggt_longint_longint(3)",d);
 
 
    if (NULLP(a)) { COPY(b,d); goto ende; }
    if (NULLP(b)) { COPY(a,d); goto ende; }
 
    ac = d;
    bc = CALLOCOBJECT();
    if (NEGP(a)) ADDINVERS(a,ac); else COPY(a,ac);
    if (NEGP(b)) ADDINVERS(b,bc); else COPY(b,bc);
 
 
/* 
    c =0;
    while (EVEN(ac) && EVEN(bc))
    {
        HALF_APPLY(ac);
        HALF_APPLY(bc);
        c++;
    }
    ODDIFY(ac);
    ODDIFY(bc);
*/
    ZEROBITS(ac,ah);
    ZEROBITS(bc,bh);
    c = ( ah >= bh ? bh : ah);
    if (S_O_K(ac) == INTEGER) psr_apply_i_integer(ac,ah);
    else psr_apply_i_longint(ac,ah);
    if (S_O_K(bc) == INTEGER) psr_apply_i_integer(bc,bh);
    else psr_apply_i_longint(bc,bh);
    
    /* beide ungerade */
 
    while (not EQ(ac,bc))
        if (GT(ac,bc))
        {
            sub_apply(bc,ac);
            ODDIFY(ac);
        }
        else
        {
            sub_apply(ac,bc);
            ODDIFY(bc);
        }
/*
    while (c) { double_apply(ac) ; c--; }
*/
    if (S_O_K(ac) == INTEGER) psl_apply_i_integer(ac,c);
    else psl_apply_i_longint(ac,c);
 
    FREEALL(bc);
 
ende:
    ENDR("ggt_longint_longint");
}
 

INT mod_apply_integer_longint(a,b) OP a,b;
/*  a is  INTEGER
    b is longint
    a:= a mod b */
{
    OP c,d;
    INT erg = OK;
    CTO(INTEGER,"mod_apply_integer_longint(1)",a);
    CTO(LONGINT,"mod_apply_integer_longint(2)",b);

    c = CALLOCOBJECT();
    d = CALLOCOBJECT();
    SWAP(a,c);
    erg += quores_integer(c,b,d,a);
    FREEALL(c);
    FREEALL(d);
    ENDR("mod_apply_integer_longint");
}

INT mod_longint_integer_via_ganzsquores(a,b,c) OP a,b,c;
/* AK 300102 */
/* c = a % b; */
/* the result lies between zero and b , excluding b */
{
    INT erg = OK;
    INT rest;
    OP ac;
    CTO(LONGINT,"mod_longint_integer(1)",a);
    CTO(INTEGER,"mod_longint_integer(2)",b);
    CTTO(INTEGER,EMPTY,"mod_longint_integer(3)",c);
    SYMCHECK(S_I_I(b) == 0,"mod_longint_integer:second parameter == 0");
    SYMCHECK(S_I_I(b) < 0,"mod_longint_integer:second parameter < 0");
    ac = CALLOCOBJECT();
    COPY(a,ac);
    erg += ganzsquores(S_O_S(ac).ob_longint,&rest,S_I_I(b));
    FREEALL(ac);

    if (S_I_I(b) < 0)
        M_I_I(rest+S_I_I(b),c);
    else
        M_I_I(rest,c);
    CTO(INTEGER,"mod_longint_integer(e3)",c);
    ENDR("mod_longint_integer");
}

INT mod_longint_integer(a,b,c) OP a,b,c;
/* AK 050202 */
/* c = a % b; */
/* the result lies between zero and b , excluding b */
{
    INT erg = OK;
    INT rest,i;
    struct longint *x;
    struct loc *alocx;
    static int sp[12];
    CTO(LONGINT,"mod_longint_integer(1)",a);
    CTO(INTEGER,"mod_longint_integer(2)",b);
    CTTO(INTEGER,EMPTY,"mod_longint_integer(3)",c);
    SYMCHECK(S_I_I(b) == 0,"mod_longint_integer:second parameter == 0");
 
    x = S_O_S(a).ob_longint;
    if (x->laenge > 4) {
        erg += mod_longint_integer_via_ganzsquores(a,b,c);
        goto ende;
        }
    if (S_I_I(b) >= 32768) {
        erg += mod_longint_integer_via_ganzsquores(a,b,c);
        goto ende;
        }
    if (S_I_I(b) <= -32768) {
        erg += mod_longint_integer_via_ganzsquores(a,b,c);
        goto ende;
        }
    i=0; alocx = x->floc;
xx:
    sp[i++] = alocx->w0;
    sp[i++] = alocx->w1;
    sp[i++] = alocx->w2;
    if (alocx -> nloc) { alocx = alocx->nloc; goto xx; }
 
    rest = 0;
    while (i--) rest = (rest * 32768 + sp[i]) % S_I_I(b);
 
    if (S_I_I(b) < 0)
        M_I_I(rest+S_I_I(b),c);
    else
        M_I_I(rest,c);
 
ende:
    /* { OP d; d = CALLOCOBJECT();
      mod_longint_integer_via_ganzsquores(a,b,d);
      println(c);
      println(d);
      SYMCHECK(not EQ(c,d),"e2"); 
      FREEALL(d); } */
 
    CTO(INTEGER,"mod_longint_integer(e3)",c);
    ENDR("mod_longint_integer");
}


INT mod_apply_longint(a,b) OP a,b;
/* a is of type LONGINT
   a = a mod b */
/* AK 051001 */
{
    INT erg = OK;
    CTO(LONGINT,"mod_apply_longint(1)",a);

    if (S_O_K(b) == LONGINT)
        {
        OBJECTSELF as,bs,cs;
        OP c;
        c = CALLOCOBJECT();
        *c = *a;
        C_O_K(a,EMPTY);
        INIT_LONGINT(a);
        as = S_O_S(a);
        bs = S_O_S(b);
        cs = S_O_S(c);
        erg += ganzquores(cs.ob_longint, as.ob_longint, bs.ob_longint);
        if (NEGP_LONGINT(a)) 
            if (POSP_LONGINT(b))
                erg += ganzadd(as.ob_longint,bs.ob_longint);
            else 
                {
                GANZNEG(bs.ob_longint);
                erg += ganzadd(as.ob_longint,bs.ob_longint);
                GANZNEG(bs.ob_longint);
                }
        /* now a is positiv */
        t_longint_int(a);
        FREEALL(c);
        }
    else if (S_O_K(b) == INTEGER)
        {
        OBJECTSELF as;
        INT rest;
        as = S_O_S(a);
        erg += ganzsquores(as.ob_longint,&rest,S_I_I(b));
        FREESELF(a);
        if (rest >= 0)
            M_I_I(rest,a);
        else if (S_I_I(b) > 0)
            M_I_I(rest+S_I_I(b),a);
        else
            M_I_I(rest-S_I_I(b),a);
        }
    else
        WTO("mod_apply_longint(2)",b);
    ENDR("mod_apply_longint");
}

INT ganzdiv_apply_longint_integer(a,b) OP a,b;
/* a = a/b 
   a is of type longint */
/* AK 081001 */
{
    INT erg = OK;
    INT rest;
    CTO(LONGINT,"ganzdiv_apply_longint_integer(1)",a);
    CTO(INTEGER,"ganzdiv_apply_longint_integer(2)",b);
    
    erg += ganzsquores(S_O_S(a).ob_longint,&rest,S_I_I(b));
    T_LONGINT_INT(a);
    
    ENDR("ganzdiv_apply_longint_integer");
}

INT ganzdiv_apply_longint_longint(a,b) OP a,b;
/* a = a/b
   a is of type longint */
/* AK 081001 */
{
    INT erg = OK;
    OP c;
    CTO(LONGINT,"ganzdiv_apply_longint_longint(1)",a);
    CTO(LONGINT,"ganzdiv_apply_longint_longint(2)",b);

    c = CALLOCOBJECT();
    INIT_LONGINT(c);
    erg += ganzquores(S_O_S(a).ob_longint, S_O_S(c).ob_longint, S_O_S(b).ob_longint);
    FREEALL(c);
    T_LONGINT_INT(a);
    
    ENDR("ganzdiv_apply_longint_longint");
}


INT ganzdiv_apply_longint(a,b) OP a,b;
/* a = a/b 
   a is of type longint */
/* AK 081001 */
{
    INT erg = OK;
    CTO(LONGINT,"ganzdiv_apply_longint(1)",a);
    if (S_O_K(b) == INTEGER)
        {
        erg += ganzdiv_apply_longint_integer(a,b);
        }
    else if (S_O_K(b) == LONGINT)
        {
        erg += ganzdiv_apply_longint_longint(a,b);
        }
    else
        WTO("ganzdiv_apply_longint",b);
ee:
    ENDR("ganzdiv_apply_longint");
}


INT ganzdiv_longint_longint(a,b,c) OP a,b,c;
/* AK 291001 */
{
    OP d;
    INT erg = OK;
    CTO(LONGINT,"ganzdiv_longint_longint(1)",a);
    CTO(LONGINT,"ganzdiv_longint_longint(2)",b);
    CTO(EMPTY,"ganzdiv_longint_longint(3)",c);

    if (NULLP_LONGINT(a)) { /* AK 060502 */
        M_I_I(0,c);
        goto ee;
        }
    
    erg += copy_longint(a,c); 
    d = CALLOCOBJECT();
    INIT_LONGINT(d);
    erg += ganzquores(S_O_S(c).ob_longint, 
                S_O_S(d).ob_longint,S_O_S(b).ob_longint);
    T_LONGINT_INT(c);
    FREEALL(d);
    
ee:
    ENDR("ganzdiv_longint_longint");
}

INT ganzdiv_longint_integer(a,b,c) OP a,b,c;
/* AK 291001 */
{
    INT d;
    INT erg = OK;
    CTO(LONGINT,"ganzdiv_longint_integer(1)",a);
    CTO(INTEGER,"ganzdiv_longint_integer(2)",b);
    CTO(EMPTY,"ganzdiv_longint_integer(3)",c);

    if (NULLP_LONGINT(a)) { /* AK 060502 */
        M_I_I(0,c);
        goto ee;
        }
 
    erg += copy_longint(a,c);
    erg += ganzsquores(S_O_S(c).ob_longint,&d, S_I_I(b));
    T_LONGINT_INT(c);
 
ee:
    ENDR("ganzdiv_longint_integer");
}

INT ganzdiv_integer_longint(a,b,c) OP a,b,c;
/* AK 291001 */
{
    OP d;
    INT erg = OK;
    CTO(LONGINT,"ganzdiv_longint_integer(2)",b);
    CTO(INTEGER,"ganzdiv_longint_integer(1)",a);
    CTO(EMPTY,"ganzdiv_longint_integer(3)",c);
    d = CALLOCOBJECT();
    erg += m_i_longint(S_I_I(a),d);
    CTO(LONGINT,"ganzdiv_integer_longint(id)",d);
    erg += ganzdiv_longint_longint(d,b,c);
    FREEALL(d);
    
    ENDR("ganzdiv_integer_longint");
}




INT addinvers_longint(a,l) OP a,l;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 201289 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"addinvers_longint(1)",a);
    CTO(EMPTY,"addinvers_longint(2)",l);


    erg += copy_longint(a,l);
    GANZNEG(S_O_S(l).ob_longint);
        /* longinteger-addinvers ist x:= -x */
    ENDR("addinvers_longint");
    }

INT invers_apply_longint(l) OP l;
/* AK 040901 */
{
    OP c;
    INT erg = OK;
    CTO(LONGINT,"invers_apply_longint(1)",l);
    if (einsp_longint(l))
        erg += m_i_i(1L,l);
    else    {
#ifdef BRUCHTRUE
        c = callocobject();
        erg += swap(l,c);
        erg += b_ou_b(callocobject(),c,l);
        M_I_I(1L,S_B_O(l));
#endif /* BRUCHTRUE */
        }
    ENDR("invers_apply_longint");
}



INT add_apply_longint(a,b) OP a,b;
/* AK 120390 V1.1 */ /* AK 190291 V1.2 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"add_apply_longint(1)",a);

    switch (S_O_K(b)) {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += add_apply_scalar_bruch(a,b); 
            break;
#endif /* BRUCHTRUE */
        case INTEGER: 
            erg += add_apply_longint_integer(a,b); 
            break;
        case LONGINT: 
            erg += add_apply_longint_longint(a,b); 
            break;
        default: /* AK 190291 */
            {
            OP c = callocobject();
            *c = *b;
            C_O_K(b,EMPTY);
            erg += add_longint(a,c,b);
            erg += freeall(c);
            }
            break;
        }
    ENDR("add_apply_longint");
    }



#ifdef MATRIXTRUE
INT mult_apply_longint_matrix(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 190291 V1.2 */ /* AK 210891 V1.3 */
    {
    OP z = S_M_S(b);
    INT i;
    INT erg=OK;
    CTO(LONGINT,"mult_apply_longint_matrix(1)",a);
    CTO(MATRIX,"mult_apply_longint_matrix(2)",b);
    i = S_M_HI(b)*S_M_LI(b);
    for(;i>0;i--,z++)
        erg += mult_apply_longint(a,z);
    ENDR("mult_apply_longint_matrix");
    }
#endif /* MATRIXTRUE */



INT mult_apply_longint(a,b) OP a,b;
/* AK 080390 V1.1 */ /* AK 190291 V1.2 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"mult_apply_longint",a);

    switch (S_O_K(b)) {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += mult_apply_longint_bruch(a,b);
            break;
#endif /* BRUCHTRUE */

        case INTEGER: 
            erg += mult_apply_longint_integer(a,b);
            break;

        case LONGINT: 
            erg += mult_apply_longint_longint(a,b);
            break;

#ifdef MATRIXTRUE
        case KRANZTYPUS:
        case MATRIX: 
            erg += mult_apply_longint_matrix(a,b);
            break;
#endif /* MATRIXTRUE */

#ifdef CHARTRUE
        case SYMCHAR:
            erg += mult_apply_scalar_symchar(a,b);
            break;
#endif /* CHARTRUE */

#ifdef POLYTRUE
        case MONOM:
            erg += mult_apply_scalar_monom(a,b);
            break;
        case SCHUR:
        case POW_SYM:
        case ELM_SYM:
        case HOM_SYM:
        case MONOMIAL:
        case SCHUBERT:
        case GRAL:
        case POLYNOM:
        case MONOPOLY:
            erg += mult_apply_longint_polynom(a,b);
            break;
#endif /* POLYTRUE */
 
#ifdef NUMBERTRUE
        case SQ_RADICAL:
            erg +=  mult_apply_scalar_sqrad(a,b);
            break;
        case CYCLOTOMIC:
            erg += mult_apply_scalar_cyclo(a,b);
            break;
#endif /* NUMBERTRUE */
#ifdef VECTORTRUE
        case INTEGERVECTOR:
        case COMPOSITION:
        case WORD:
        case VECTOR:
            erg += mult_apply_scalar_vector(a,b);
            break;
        case HASHTABLE:
            erg += mult_apply_scalar_hashtable(a,b);
            break;
 
#endif /* VECTORTRUE */


        default: /* AK 190291 */
            {
            OP c = callocobject();
            INT erg=OK;
            *c = *b;
            C_O_K(b,EMPTY);
            erg += mult(a,c,b);
            erg += freeall(c);
            }
        }
    ENDR("mult_apply_longint");
    }



INT add_apply_longint_longint(a,b) OP a,b;
/* AK 120390 V1.1 */ /* AK 050791 V1.3 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"add_apply_longint_longint(1)",a);
    CTO(LONGINT,"add_apply_longint_longint(2)",b);
    if (GANZSIGNUM(S_O_S(a).ob_longint) == GANZSIGNUM(S_O_S(b).ob_longint))
        erg += ganzadd(S_O_S(b).ob_longint,S_O_S(a).ob_longint);
    else {
        erg += ganzadd(S_O_S(b).ob_longint,S_O_S(a).ob_longint);
        T_LONGINT_INT(b);
        }
    ENDR("add_apply_longint_longint");
    }



INT mult_apply_longint_longint(a,b) OP a,b;
/* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    OBJECTSELF as,bs;
    CTO(LONGINT,"mult_apply_longint_longint(1)",a);
    CTO(LONGINT,"mult_apply_longint_longint(2)",b);
    as = S_O_S(a);
    bs = S_O_S(b);
    erg += ganzmul(bs.ob_longint,as.ob_longint);
    ENDR("mult_apply_longint_longint");
    }




INT add_apply_longint_integer(a,b) OP a,b;
/* AK 120390 V1.1 */ /* AK 050791 V1.3 */
    {
    INT erg = OK;
    OP c;
    CTO(LONGINT,"add_apply_longint_integer(1)",a);
    CTO(INTEGER,"add_apply_longint_integer(2)",b);

    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += add_longint_integer(a,c,b);
    FREEALL(c);
    ENDR("add_apply_longint_integer");
    }



INT mult_apply_longint_integer(a,b) OP a,b;
/* AK 080390 V1.1 */ /* AK 050791 V1.3 */
    {
    OP c;
    INT erg = OK;
    CTO(INTEGER,"mult_apply_longint_integer(2)",b);
    CTO(LONGINT,"mult_apply_longint_integer(1)",a);

    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += mult_longint_integer(a,c,b);
    FREEALL(c);

    CTTO(LONGINT,INTEGER,"mult_apply_longint_integer(e2)",b);
    /* INTEGER if b==0 */
    ENDR("mult_apply_longint_integer");
    }



INT add_apply_integer_longint(a,b) OP a,b;
/* b = a + b */ /* b ist LONGINT, a ist INTEGER */
/* AK 120390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(INTEGER,"add_apply_integer_longint(1)",a);
    CTO(LONGINT,"add_apply_integer_longint(2)",b);

    erg += ganzsadd(S_O_S(b).ob_longint,S_I_I(a));
    T_LONGINT_INT(b);
 
    ENDR("add_apply_integer_longint");
    }


INT mult_apply_integer_longint(a,b) OP a,b;
/* b = a * b */ /* b ist LONGINT, a ist INTEGER */
/* AK 080290 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(INTEGER,"mult_apply_integer_longint(1)",a);
    CTO(LONGINT,"mult_apply_integer_longint(2)",b);

    erg += ganzsmul(S_O_S(b).ob_longint,S_I_I(a));

    ENDR("mult_apply_integer_longint");
    }



INT mult_longint_integer_via_ganzsmul(a,c,l) OP a,c,l;
/* a ist LONINT c ist INTEGER */ /* AK 180888 */
/* AK 130789 V1.0 */ /* AK 080290 V1.1 */ /* AK 210891 V1.3 */
/* l = a+c */
    {
    INT erg = OK;
    OBJECTSELF ls;
    CTO(INTEGER,"mult_longint_integer(2)",c);
    CTO(LONGINT,"mult_longint_integer(1)",a);
    CTO(EMPTY,"mult_longint_integer(3)",l);
    erg += copy_longint(a,l); 
    ls = S_O_S(l);
    erg += ganzsmul(ls.ob_longint,S_I_I(c));
    ENDR("mult_longint_integer");
    }



INT add_longint_integer(a,c,l) OP a,c,l;
/* a is LONGINT c is INTEGER */ /* AK 180888 */
/* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    OBJECTSELF ls;
    CTO(LONGINT,"add_longint_integer(1)",a);
    CTO(INTEGER,"add_longint_integer(2)",c);
    CTO(EMPTY,"add_longint_integer(3)",l);

    erg += copy_longint(a,l);
    ls = S_O_S(l);
    erg += ganzsadd(ls.ob_longint,S_I_I(c));
        /* longinteger-addition ist x:= x+y */
    erg += t_longint_int(l);

    ENDR("add_longint_integer");
    }


INT dec_longint(a) OP a;
/* AK 230888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as ;
    INT erg = OK;
    CTO(LONGINT,"dec_longint(1)",a);
    as = S_O_S(a);
    erg += ganzsadd(as.ob_longint,(INT)-1);
    ENDR("dec_longint");
    }



INT inc_longint(a) OP a;
/* AK 230888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as;
    INT erg = OK;
    CTO(LONGINT,"inc_longint(1)",a);
    as = S_O_S(a);

    erg += ganzsadd(as.ob_longint,1);
    ENDR("inc_longint");
    }



INT t_longint_int(a) OP a;
/* AK 150290 V1.1 */ /* umwandlung in INTEGER falls moeglich */
/* AK 210891 V1.3 */
    {
    OBJECTSELF cs;
    INT wert;
    INT erg = OK;

    if (S_O_K(a) == INTEGER) return OK;
    CTO(LONGINT,"t_longint_int(1)",a);


    cs = S_O_S(a);
    if (cs.ob_longint ->laenge == (INT)1)
        if (cs.ob_longint ->floc ->w2 <= 1) /* AK 051101 */
        {
        wert = intganz(cs.ob_longint);
        FREESELF(a);
        M_I_I(wert,a);
        }
    ENDR("t_longint_int");
    }



INT einsp_longint(a) OP a;
/* AK 271190 V1.1 */ /* AK 250291 V1.2 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF cs;
    cs = S_O_S(a);
    if (cs.ob_longint ->laenge == 1)
    if (cs.ob_longint ->signum == 1)
    if (cs.ob_longint ->floc ->w2 ==0)
    if (cs.ob_longint ->floc ->w1 ==0)
    if (cs.ob_longint ->floc ->w0 ==1)
            return TRUE;
    return FALSE;
    }

INT negeinsp_longint(a) OP a;
/* AK 070502 */
    {
    OBJECTSELF cs;
    cs = S_O_S(a);
    if (cs.ob_longint ->laenge == 1)
    if (cs.ob_longint ->signum == -1)
    if (cs.ob_longint ->floc ->w2 ==(INT)0)
    if (cs.ob_longint ->floc ->w1 ==(INT)0)
    if (cs.ob_longint ->floc ->w0 == (INT)1)
            return TRUE;
    return FALSE;
    }  

INT t_int_longint(a,c) OP a,c;
/* umwandeln von INTEGER -> LONGINT AK 180888 */
/* AK 130789 V1.0 */ /* AK 150290 V1.1 */ /* AK 250391 V1.2 */
/* AK 210891 V1.3 */
    {
/* it is possible a == c */
    INT erg = OK;
    INT av = S_I_I(a);
    struct longint *x;

    CTO(INTEGER,"t_int_longint(1)",a);
    

    FREESELF(c);
    INIT_LONGINT(c); 
    x = S_O_S(c).ob_longint;
    if (av==0) /* AK 060502 */
        {
        x->laenge = 0;
        x->signum = 0;
        FREE_LOC(x->floc);
        x->floc = NULL;
        goto ee;
        }
    x->laenge = 1;

    if (av == MAXNEG) { 
        x->signum = (signed char)locint(x->floc,av+1);
        ganzsadd(x,(INT)-1);
        }
    else 
        x->signum = (signed char)locint(x->floc,av);

ee:
    CTO(LONGINT,"t_int_longint(e2)",c);
    ENDR("t_int_longint");
    }

INT comp_longint_integer(a,c) OP a,c;
/* AK 011101 */
{
    INT erg = OK;
    CTO(LONGINT,"comp_longint(1)",a);
    CTO(INTEGER,"comp_longint(2)",c);



    if (NEGP_LONGINT(a)) {
        if  (not NEGP_INTEGER(c))  return -1;
        /* beide negativ */
        if (GANZLAENGE(S_O_S(a).ob_longint) > 1) return -1;
        if (GANZLAENGE(S_O_S(a).ob_longint) == 1)
            if ((S_O_S(a).ob_longint) -> floc -> w2  > 1 ) return -1;
        }
    else{
        if (NEGP_INTEGER(c)) return 1;
        /* beide positiv */
        if (GANZLAENGE(S_O_S(a).ob_longint) > 1) return 1;
        if (GANZLAENGE(S_O_S(a).ob_longint) == 1) 
            if ((S_O_S(a).ob_longint) -> floc -> w2  > 1 ) return 1;
        }

    T_LONGINT_INT(a);
    CTO(INTEGER,"comp_longint_integer(i1)",a);
    return COMP_INTEGER_INTEGER(a,c);
    ENDR("comp_longint_integer");
}

INT eq_longint_longint(a,b) OP a,b;
/* AK 010202 */
{
    INT erg = OK;
    struct longint *al, *bl;
    struct loc *locxa, *locxb;

    CTO(LONGINT,"eq_longint_longint(1)",a);
    CTO(LONGINT,"eq_longint_longint(2)",b);
    al = S_O_S(a).ob_longint;
    bl = S_O_S(b).ob_longint;
    if (al -> signum != bl -> signum) return FALSE;
    if (al -> laenge != bl -> laenge) return FALSE;
    locxa = al->floc;
    locxb = bl->floc;


    while (locxa != NULL)
        {
        if ( (locxa->w0)  != (locxb->w0)) return FALSE;
        if ( (locxa->w1)  != (locxb->w1)) return FALSE;
        if ( (locxa->w2)  != (locxb->w2)) return FALSE;
        locxa = locxa ->nloc;
        locxb = locxb ->nloc;
        }

    return TRUE;


    ENDR("eq_longint_longint");
}


INT comp_longint(a,c) OP a,c;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 050790 V1.1 */ /* AK 210891 V1.3 */
    {
    OP d; 
    INT erg=OK;
    CTO(LONGINT,"comp_longint(1)",a);

    switch(S_O_K(c))
        {
        case INTEGER: return comp_longint_integer(a,c);
        case LONGINT:
            {
            OBJECTSELF as,cs;
            as=S_O_S(a); 
            cs=S_O_S(c);
            erg = ganzvergleich(as.ob_longint, cs.ob_longint);
            return(erg);
            }
#ifdef BRUCHTRUE
        case BRUCH:
            {
            d = callocobject(); 
            m_scalar_bruch(a,d);
            erg = comp(d,c);
            freeall(d);
            return erg;
            }
#endif /* BRUCHTRUE */
        default: {
            WTO("comp_longint(2)",c);
            break;
            }
        };
    ENDR("comp_longint");
    }



INT check_longint(a) OP a;
/* AK 071294 */
/* test auf fuehrende Null */
{
    OBJECTSELF cs;
    struct loc *alocx;
    if (S_O_K(a) != LONGINT) return OK;

    cs = S_O_S(a);
    alocx = (cs.ob_longint)->floc;
    while (alocx != NULL)
        {
        if (alocx -> nloc == NULL)
            {
            if ((alocx->w0 == 0) &&
            (alocx->w1 == 0) &&
            (alocx->w2 == 0) )

            error("internal error check_longint:");
            }
        alocx = alocx->nloc;
        }
    return OK;
}

INT half_apply_longint(a) OP a;
{
    INT erg = OK;
    CTO(LONGINT,"half_apply_longint(1)",a);

    /* erg += ganzhalf(S_O_S(a).ob_longint); */
    psr_apply_i_longint(a,1);

    ENDR("half_apply_longint");
}

INT psr_apply_i_integer(a,i) OP a; INT i;
{
    INT erg = OK;
    CTO(INTEGER,"psr_apply_i_integer(1)",a);
    SYMCHECK(i<0,"psr_apply_i_integer:second parameter < 0");
    SYMCHECK(S_I_I(a)<0,"psr_apply_i_integer:first parameter < 0");

    if (i >= 32) M_I_I(0,a);
    else M_I_I(S_I_I(a) >> i, a);
    CTO(INTEGER,"psr_apply_i_integer",a);
    ENDR("psr_apply_i_integer");
}
 

INT psl_apply_i_integer(a,i) OP a; INT i;
{
    INT erg = OK;
    CTO(INTEGER,"psl_apply_i_integer(1)",a);
    SYMCHECK(i<0,"psl_apply_i_integer:second parameter < 0");
    SYMCHECK(S_I_I(a)<0,"psl_apply_i_integer:first parameter < 0");
    if ( (S_I_I(a) < 32768)  /* 2^15 */ &&   ( i < 16) )
        {
        M_I_I(S_I_I(a) << i, a);
        }
    else if ((S_I_I(a) < 8388608)/*2^23*/  &&   ( i < 8) ) { 
        M_I_I(S_I_I(a) << i, a);
        }
    else if ((S_I_I(a) < 134217728)/*2^27*/  &&   ( i < 4) ) { 
        M_I_I(S_I_I(a) << i, a);
        }
    else {
        erg += t_int_longint(a,a);
        erg += psl_apply_i_longint(a,i);
        }
    CTTO(INTEGER,LONGINT,"psl_apply_i_integer",a);
    ENDR("psl_apply_i_integer");
}


INT psl_apply_i_longint(a,i) OP a; INT i;
/* shift left i bits */
/* multiplication by 2^i */
{
    struct longint *l;
    struct loc *alocx;
    INT f,t,c,erg = OK;;
 
    CTO(LONGINT,"psl_apply_i_longint(1)",a);
    SYMCHECK(i<0,"psl_apply_i_longint:second parameter < 0");
 
    l = S_O_S(a).ob_longint;
    
again:
    alocx = l->floc;
    if (i >= 15) {
        t = 0;
zz:
        f = alocx -> w2;
        alocx -> w2 = alocx -> w1;
        alocx -> w1 = alocx -> w0;
        alocx -> w0 = t;
        if (alocx -> nloc == NULL) { 
            if ( f != 0 ) {
                LOCHOLE(& alocx -> nloc );
                alocx -> nloc -> w0 = f;
                l->laenge ++;
                }
            i -= 15;
            goto again;
            }
        alocx = alocx ->nloc;
        t = f;
        goto zz;
        }
/* block shifted */

SYMCHECK(i >= 15,"psl_apply_i_longint(i1)");
    if (i==0) goto ende;
    c = 0;
    for (t=0;t<i;t++) { c>>=1; c|=16384;/* 2^15 */ }
    t=0;

xx:
    f = (alocx -> w2 & c) >> (15-i);;
    
    alocx -> w2 <<=i; 
    alocx -> w2 &= (BMINUSEINS);
    alocx -> w2 |=  (alocx -> w1 & c ) >> (15-i);
    alocx -> w1 <<=i;
    alocx -> w1 &= (BMINUSEINS);
    alocx -> w1 |=  (alocx -> w0 & c ) >> (15-i);
    alocx -> w0 <<=i;
    alocx -> w0 &= (BMINUSEINS);
    alocx -> w0 |=  t;
    if (alocx ->nloc == NULL)
        {
        if ( f != 0 ) {
            LOCHOLE(& alocx -> nloc );
            alocx -> nloc -> w0 = f;
            l->laenge ++;
            }
        }
    else {
        t = f;
        alocx = alocx ->nloc;
        goto xx;
        }
ende:
    CTO(LONGINT,"psl_apply_i_longint(e1)",a);
    ENDR("psl_apply_i_longint");
}


INT psr_apply_i_longint(a,i) OP a; INT i;
{
    struct longint *l;
    struct loc *alocx,*plocx;
    INT f,t,c,erg = OK;;

    CTO(LONGINT,"psr_apply_i_longint(1)",a);
    SYMCHECK(i<0,"psr_apply_i_longint:second parameter < 0");

    l = S_O_S(a).ob_longint;

again:
    alocx = l->floc;
    if (i >= 15) {
zz:
       alocx -> w0 = alocx ->w1;
       alocx -> w1 = alocx ->w2;
       if (alocx -> nloc == NULL)  {
           alocx ->w2 = 0;
           i -= 15;
           goto again;
           }
       else {
            alocx ->w2 = alocx -> nloc -> w0;
            if ( ( alocx -> nloc -> w1 == 0 ) && ( alocx -> nloc -> w2 == 0 )
               && ( alocx -> nloc -> nloc == NULL ) )
                  {
                  l -> laenge --;
                  FREE_LOC(alocx -> nloc);
                  alocx -> nloc = NULL;
                  i -= 15;
                  goto again;
                  }
            alocx = alocx -> nloc;
            goto zz;
            }
       }
/* block shifted */

SYMCHECK(i >= 15,"psr_apply_i_longint(i1)");
    if (i==0) goto ende;
    c = i; t=0; f = 15-i;
    while (i--) {t<<=1; t |=  1;}

/* now i bits shifted to the right */
    alocx -> w0 >>= c;
    alocx -> w0 |= ( ( alocx -> w1  & t ) << f );
    alocx -> w1 >>= c;
    alocx -> w1 |= ( ( alocx -> w2  & t ) << f );
    alocx -> w2 >>= c;
    if (alocx ->nloc != NULL)
        alocx -> w2 |= ( ( alocx ->nloc-> w0  & t ) << f );

    plocx = alocx;
    alocx = alocx ->nloc;
    while (alocx != NULL) {
        alocx -> w0 >>= c;
        alocx -> w0 |= ( ( alocx -> w1  & t ) << f );
        alocx -> w1 >>= c;
        alocx -> w1 |= ( ( alocx -> w2  & t ) << f );
        alocx -> w2 >>= c;
        if (alocx ->nloc != NULL)
            alocx -> w2 |= ( ( alocx ->nloc-> w0  & t ) << f );

 
        if ( (alocx -> nloc == NULL) && (alocx->w0 == 0) &&
             (alocx->w1 == 0)&& (alocx->w2 == 0) )
              {
              l -> laenge --;
              FREE_LOC(alocx);
              plocx->nloc = NULL;
              goto ende;
              }
        plocx = alocx;
        alocx = alocx ->nloc;
        }

ende:
    T_LONGINT_INT(a);
    CTTO(INTEGER,LONGINT,"psr_apply_i_longint(e1)",a);
    ENDR("psr_apply_i_longint");
}

INT oddify_longint(a) OP a;
{
    struct longint *l;
    struct loc *alocx,*plocx;
    INT f,t,c,erg = OK;;
    CTO(LONGINT,"oddify_longint(1)",a);

    l = S_O_S(a).ob_longint;

again:
    alocx = l->floc;

    if (alocx -> w0 == 0) {
zz:
       alocx -> w0 = alocx ->w1;
       alocx -> w1 = alocx ->w2;
       if (alocx -> nloc == NULL)  {
           alocx ->w2 = 0;
           goto again;
           }
       else { 
            alocx ->w2 = alocx -> nloc -> w0;
            if ( ( alocx -> nloc -> w1 == 0 ) && ( alocx -> nloc -> w2 == 0 )
               && ( alocx -> nloc -> nloc == NULL ) ) 
                  {
                  l -> laenge --;
                  FREE_LOC(alocx -> nloc);
                  alocx -> nloc = NULL;
                  goto again;
                  }
            alocx = alocx -> nloc;
            goto zz;
            }
       }
    

    c = 0; t=0; f=15;
/* max 14 bits */     
    while ( not (alocx -> w0 & 1) ) { c++; alocx -> w0 >>= 1; t<<=1; t |=  1; f--;}

    if (c == 0) goto ende;

    alocx -> w0 |= ( ( alocx -> w1  & t ) << f );
    alocx -> w1 >>= c;
    alocx -> w1 |= ( ( alocx -> w2  & t ) << f );
    alocx -> w2 >>= c;
    if (alocx ->nloc != NULL)
        alocx -> w2 |= ( ( alocx ->nloc-> w0  & t ) << f );

    plocx = alocx;
    alocx = alocx ->nloc;
    while (alocx != NULL) {
        alocx -> w0 >>= c;
        alocx -> w0 |= ( ( alocx -> w1  & t ) << f );
        alocx -> w1 >>= c;
        alocx -> w1 |= ( ( alocx -> w2  & t ) << f );
        alocx -> w2 >>= c;
        if (alocx ->nloc != NULL)
            alocx -> w2 |= ( ( alocx ->nloc-> w0  & t ) << f );

        if ( (alocx -> nloc == NULL) && (alocx->w0 == 0) && 
             (alocx->w1 == 0)&& (alocx->w2 == 0) )
              {
              l -> laenge --;
              FREE_LOC(alocx);
              plocx->nloc = NULL;
              goto ende;
              }
        plocx = alocx;
        alocx = alocx ->nloc;
        }

ende:
    t_longint_int(a);
    SYMCHECK(EVEN(a),"oddify_longint(e1)");
    CTTO(INTEGER,LONGINT,"oddify_longint(e1)",a);
    ENDR("oddify_longint");
}


INT psl_apply_longint(a) OP a; /* double */
{
    INT erg = OK;
    CTO(LONGINT,"psl_apply_longint(1)",a);
    erg += psl_apply_i_longint(a,1);
    CTO(LONGINT,"psl_apply_longint(e1)",a);
    ENDR("psl_apply_longint");
}


INT double_apply_longint(a) OP a;
/* AK 010202 */
{
    INT erg = OK;
    CTO(LONGINT,"double_apply_longint(1)",a);
    erg += psl_apply_longint(a);
    ENDR("double_apply_longint");
}


INT quores_longint(a,e,c,d) OP a,e,c,d;
/* ganzdiv AK 220888 */ /* c = a / e */
/* d ist rest */
/* AK 130789 V1.0 */ /* AK 150290 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    CTO(LONGINT,"quores_longint(1)",a);
    CTO(EMPTY,"quores_longint(3)",c);
    CTO(EMPTY,"quores_longint(4)",d);
    switch (S_O_K(e))
        {
        case INTEGER:
            {
            OBJECTSELF cs;
            INT    rest;
            erg += copy_longint(a,c);
            cs = S_O_S(c); 
            erg += ganzsquores(cs.ob_longint,&rest,S_I_I(e));
            erg += t_longint_int(c);
            M_I_I(rest,d);
            goto ql_040393;
            }
        case LONGINT:
            {
            OBJECTSELF es,cs,ds;
            erg += copy_longint(a,c); 
            INIT_LONGINT(d);
            cs = S_O_S(c); 
            es = S_O_S(e); 
            ds = S_O_S(d);
            erg += ganzquores(cs.ob_longint, 
                ds.ob_longint,es.ob_longint);
            erg += t_longint_int(c);
            erg += t_longint_int(d);
            goto ql_040393;
            }
        default: 
            {
            WTO("quores_longint(2)",e);
            goto ende;
            }
        };
ql_040393:
    if (negp(d))
        if (posp(e))
            {
            erg += add_apply(e,d);
            erg += dec(c);
            }
        else if (negp(e))
            {
            erg += sub(d,e,d);
            erg += inc(c);
            }
ende:
    ENDR("quores_longint");
    }




INT scan_longint(a) OP a;
/* AK 180888 */ /* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as;
    
    printeingabe("longint:");
    init(LONGINT,a);as=S_O_S(a);
    ganzein(stdin,as.ob_longint);
    if (nullp_longint(a) ) { /* AK 020889 V1.0 */
        M_I_I((INT)0,a); 
        }
    return(OK);
    }



INT posp_longint(a) OP a;
/* AK 190888 */ /* AK 280689 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
/* true if a > 0 */
    {
    OBJECTSELF as;
    as=S_O_S(a);
    return  GANZSIGNUM(as.ob_longint) == (INT)1;
    }



INT odd_longint(a) OP a;
/* AK 061190 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as;
    as=S_O_S(a);
    return ganzodd(as.ob_longint);
    }



INT even_longint(a) OP a;
/* AK 061190 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as;
    as=S_O_S(a);
    return ganzeven(as.ob_longint);
    }


INT nullp_longint(a) OP a;
/* AK 190888 */ /* AK 280689 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT s;
    INT erg = OK;
    OBJECTSELF as;
    CTO(LONGINT,"nullp_longint(1)",a);
    as=S_O_S(a);
    s = GANZSIGNUM(as.ob_longint);
    if (s != 0) return FALSE;
    SYMCHECK ((as.ob_longint)->laenge != 0,"nullp_longint:zero wioth wrong length");
    return TRUE;
    ENDR("nullp_longint");
    }




INT negp_longint(a) OP a;
/* AK 190888 */ /* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF as;
    as=S_O_S(a);
    return(GANZSIGNUM(as.ob_longint) == -1);
    }



INT objectread_longint(f,l) FILE *f; OP l;
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    OBJECTSELF ls;
    INT erg = OK;
    COP("objectread_longint(1)",f);
    CTO(EMPTY,"objectread_longint(2)",l);

    erg += init(LONGINT,l);
    ls=S_O_S(l);
    erg += ganzein(f, ls.ob_longint);
    ENDR("objectread_longint");
    }



INT objectwrite_longint(f,l) FILE *f; OP l;
/* AK 130789 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    INT erg = OK;
    OBJECTSELF ls;

    COP("objectwrite_longint(1)",f);
    CTO(LONGINT,"objectwrite_longint(2)",l);

    if (nullp_longint(l)) { /* AK 020889 V1.0 */
        erg += m_i_i((INT)0,l);
        erg += objectwrite_integer(f,l);
        goto owlende;
        }

    fprintf(f," %ld ",LONGINT);
    ls=S_O_S(l);
    erg += ganzaus(f, ls.ob_longint); 
    fprintf(f,"\n"); 
owlende:
    ENDR("objectwrite_longint");
    }



INT m_i_longint(a,b) OP b;INT a;
/* AK 180888 */ /* AK 270689 V1.0 */ /* AK 080390 V1.1 */ /* AK 210891 V1.3 */
    {
    OP c;
    INT erg = OK;
    COP("m_i_longint(2)",b);
    c = CALLOCOBJECT();
    M_I_I(a,c);        /* make INT --> INTEGER */
    erg += t_int_longint(c,b); /* transform INTEGER --> LONGINT */
    FREEALL(c); 
    CTO(LONGINT,"m_i_longint(e2)",b);
    ENDR("m_i_longint");
    }



INT debugprint_longint(a) OP a;
/* AK 020390 V1.1 */ /* AK 210891 V1.3 */
{
    OBJECTSELF c;
    INT k;
    struct loc *alocx;
    c = s_o_s(a);
    for (k=0L;k<doffset;k++) fprintf(stderr," ");
    fprintf(stderr,"kind:22=longint\n");
    for (k=0L;k<doffset;k++) fprintf(stderr," ");
    fprintf(stderr,"laenge = %ld\n",
        c.ob_longint->laenge);
    for (k=0L;k<doffset;k++) fprintf(stderr," ");
    fprintf(stderr,"signum = %d\n",
        c.ob_longint->signum);
    alocx = c.ob_longint->floc; /* AK 071294 */
    while (alocx != NULL)
        {
        for (k=0L;k<doffset;k++) fprintf(stderr," ");
        fprintf(stderr,"%ld %ld %ld\n",alocx->w0,alocx->w1,alocx->w2);
        alocx= alocx->nloc;
        }
    return(OK);
}

INT sscan_longint(t,a) char *t; OP a;
{
    INT erg = OK;
    INT vz=(INT)1;
    char c;
    OP zehn, faktor;
    int SYM_isdigit();

    COP("sscan_longint(1)",t);
    CTO(EMPTY,"sscan_longint(2)",a);

    zehn = callocobject(); 
    M_I_I((INT)10,zehn);
    faktor = callocobject();
    m_i_i((INT)0,a);
slagain:
    c = *t++;
    if (c == '\0') 
        {
        erg = ERROR;
        goto sle;
        }
    if (c == ' ')
        goto slagain;
    if (c == '-')
        {
        if (vz == (INT)-1) { erg = ERROR; goto sle; }
        vz = (INT)-1;
        goto slagain;
        }
    if (not SYM_isdigit(c))
        {
        erg = ERROR;
        goto sle;
        }    
slb:
    erg += mult_apply(zehn,a);
    erg += m_i_i((INT)9-('9'-c),faktor);
    erg += add_apply(faktor,a);
    c = *t++;
    if (c == '\0') 
        {
        goto sle;
        }
    if (not SYM_isdigit(c))
        {
        erg = ERROR;
        goto sle;
        }    
    goto slb;
sle:
    erg += freeall(zehn);
    erg += freeall(faktor);
    if (vz == (INT)-1) 
        erg += addinvers_apply(a);
    ENDR("sscan_longint");
}




INT test_longint() {
/* AK 020390 V1.1 */ /* AK 210891 V1.3 */
    OP a = callocobject();
    OP b = callocobject();
    OP c = callocobject();

    start_longint();
    printf("test_longint:scan(a)"); scan(LONGINT,a);println(a);
    printf("test_longint:add(a,a,b)"); add(a,a,b); println(b);
    printf("test_longint:mult(a,b,b)"); mult(a,b,b); println(b);
    printf("test_longint:m_i_i((INT)-1,c);mult(c,b,b)");
    m_i_i((INT)-1,c); mult(c,b,b); println(b);
    printf("test_longint:m_i_i((INT)-1,c);add(c,b,b)");
    m_i_i((INT)-1,c); add(c,b,b); println(b);
#ifdef BRUCHTRUE
    printf("test_longint:invers(b,a)"); invers(b,a); println(a);
#endif /* BRUCHTRUE */
    printf("test_longint:mult(b,a,a)"); mult(b,a,a); println(a);

    printf("test_longint:m_i_i((INT)3,c);div(a,c,b)");
    m_i_i((INT)3,c); div(a,c,b); println(b);
    printf("test_longint:m_i_i((INT)100,c);fakul(c,b)");
    m_i_i((INT)100,c); fakul(c,b); println(b);

    freeall(a);freeall(b);freeall(c);
    return(OK);
    }
    
INT random_longint(res,ober) OP res,ober;
/* AK 080390 V1.1 */
/* ober ist beim ersten aufruf die obere grenze, spater NULL */
/* AK 210891 V1.3 */
    {
    INT l,i;
    INT erg = OK; /* AK 030893 */
    OP h1,h2,h3;

    COP("random_longint(1)",res);

    if (ober == NULL) {
        if (rl_o == NULL) return(
                error("random_longint: no initialisation"));
        }
    else    {
        CTO(LONGINT,"random_longint(2)",ober);
        if (rl_o == NULL) {
            rl_o=callocobject(); 
            rl_a=callocobject();
            rl_x=callocobject(); 
            rl_m=callocobject();
            }
        else     {
            erg += freeself(rl_o); 
            erg += freeself(rl_a); 
            erg += freeself(rl_x); 
            erg += freeself(rl_m);
            }
        erg += copy(ober,rl_o);
        h1 = callocobject(); 
        h2 = callocobject();
        h3 = callocobject();
        l = (S_O_S(ober).ob_longint->laenge) * 3 ; /* laenge */
        erg += m_i_i((INT)10,rl_m);
        erg += m_i_i(l*(INT)6,h1);
        erg += hoch(rl_m,h1,rl_m);
        erg += m_i_i((INT)222222,rl_a);
        erg += m_i_i((INT)1000000,h2);
        erg += m_i_i((INT)222222,h1);
        erg += m_i_i((INT)0,rl_x);
        for (i=1;i<=l;i++)
            {
            MULT_APPLY(h2,rl_a);
            ADD_APPLY(h1,rl_a);
            erg += random_integer(h3,NULL,h2);
            MULT_APPLY(h2,rl_x);
            ADD_APPLY(h3,rl_x);
            }
        erg += mod(rl_x,rl_o,res); 
        erg += freeall(h1); 
        erg += freeall(h2); 
        erg += freeall(h3);
        goto rl_ende;
        }
    /* dies ist der fall dass initialisiert ist */
    h1 = callocobject();
    erg += mult(rl_x,rl_a,h1);
    erg += mod(h1,rl_m,rl_x);
    erg += mod(rl_x,rl_o,res); 
    FREEALL(h1);
rl_ende:
    ENDR("random_longint");
    }

#endif /* LONGINTTRUE */
