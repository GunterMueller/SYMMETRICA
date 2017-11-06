/* CLASSICAL.C module:

   Symmetrica routines to calculate dimensions, standard tableaux and
   characters for the classical groups GL(n), Sp(n), O(n) and SO(n);
   including the spin representations of the orthogonal groups.
   In each case, the user supplies the n and the partition (in certain
   SO(n) cases, an extra parameter is needed).
   In each case the partition is checked to be valid for the group
   concerned. See the DIMENSION.DOC file for a full description.

   Each dimension routine uses a variant of the hook length formula.
   For the GL(n)/SL(n) case, this was given by Robinson (1958).
   For the Sp(2r)/O(n) and their spin cases this was given by 
   El-Samra and King (1979).
   Efforts are made here to allow n (the size of the matrices which
   define the group) to be an INTEGER or a LONGINT object,
   although the number of parts and the length of each part are
   assumed to fit comfortably in an INTEGER (reasonable, I feel).

   The standard tableaux which are generated were first described by:
   King for Sp(2r) and spin O(n) and SO(n) cases and by King and Welsh
   for ordinary O(n) and SO(n) cases. The standard tableaux for GL(n)
   are the well-known "semi-standard" tableaux.

   The characters are obtained in each case by first enumerating
   the standard tableaux, forming a monomial from each, and
   summing over all the standard tableaux. In the spin cases
   the exponents are twice their actual values, since in general
   they are half integer values.

   All the above aspects of the representation theory of the classical
   groups is described in detail in my PhD thesis (Southampton 1992).

   Trevor Welsh, Bayreuth, April 1996 
*/


#include <stdio.h>

#include "def.h"
#include "macro.h"


static INT gl_generate();
static INT sp_generate ();
static INT or_generate ();
static INT pn_generate ();

/*************************************************************************
 Routines to calculate dimensions of the classical groups
*************************************************************************/


INT gl_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* general linear group */ 

{  
    INT i,j,no_rows,no_cols;
    INT erg = OK;
   OP part,conj;
   OP top,bot,nc,nob,hook;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("gl_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   if (!no_rows)
   {  m_i_i(1L,dim);
      return(OK);
   }
   no_cols=s_pa_ii(partition,no_rows-1);

   if (no_rows > s_i_i(n))
   {  printf("The partition passed to gl_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   /* put the parts in decreasing order and construct the conjugate */

   m_il_v(no_rows,part=callocobject());
   m_il_v(no_cols,conj=callocobject());

   for (i=0;i<no_rows;i++)
      m_i_i(s_pa_ii(partition,no_rows-1-i),s_v_i(part,i));

   for (j=no_cols-1,i=1;j>=0;j--)
     {  while (i<no_rows && s_v_ii(part,i)>j) i++;
        m_i_i(i,s_v_i(conj,j));
     }

   /* initialise a few things for the hook length calculation */

   m_i_i(1L,top=callocobject());
   m_i_i(1L,bot=callocobject());
   m_i_i(0L,hook=callocobject());
   nob=callocobject();
   copy(n,nc=callocobject());
   
   /* visit all the boxes of Young diagram, accumulating hook
      length factors and numerator factors */

   for (i=0;i<no_rows;i++)
   {  copy(nc,nob);

      for (j=0;j<s_v_ii(part,i);j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);
     
     mult_apply(nob,top);
         inc(nob);
      }
      dec(nc);
   }

   div(top,bot,dim);

   freeall(part); freeall(conj);
   freeall(nob); freeall(hook); freeall(nc);
   freeall(top); freeall(bot);

   ENDR("gl_dimension");
}


INT sp_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* symplectic group */ 

{  INT i,j,no_rows,no_cols,square,first,last;
   OP r,res,dum;
   OP part,conj;
   OP top,bot,nob,hook;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("sp_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   if (!no_rows)
   {  m_i_i(1L,dim);
      return(OK);
   }
   no_cols=s_pa_ii(partition,no_rows-1);
   m_i_i(2L,dum=callocobject());
   quores(n,dum,r=callocobject(),res=callocobject());
   
   if (no_rows > s_i_i(r)+(nullp(res)?0:1) )
      /* allow one extra part for odd dimensions! */
   {  printf("The partition passed to sp_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   if (!nullp(res))
   {  printf("Warning! sp_dimension received odd group specification!\n");
   }

   freeall(r); freeall(res);

   /* put the parts in decreasing order and construct the conjugate:
      we need to make them longer with enough zeros. */

   square=no_rows>no_cols?no_rows:no_cols;
   m_il_v(square,part=callocobject());
   m_il_v(square,conj=callocobject());

   for (i=0;i<no_rows;i++)
      m_i_i(s_pa_ii(partition,no_rows-1-i),s_v_i(part,i));
   for (;i<square;i++)
      m_i_i(0,s_v_i(part,i));

   for (j=square-1;j>=no_cols;j--)
      m_i_i(0,s_v_i(conj,j));
   for (i=1;j>=0;j--)
     {  while (i<no_rows && s_v_ii(part,i)>j) i++;
        m_i_i(i,s_v_i(conj,j));
     }

   /* initialise a few things for the hook length calculation */

   m_i_i(1L,top=callocobject());
   m_i_i(1L,bot=callocobject());
   m_i_i(0L,hook=callocobject());
   nob=callocobject();

   /* visit all the boxes of Young diagram, accumulating hook
      length factors and numerator factors */

   for (i=0;i<no_rows;i++)
   {  last=s_v_ii(part,i);
      first=last<i ? last : i;

      for (j=0;j<first;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(n,nob);
     c_i_i(dum,-i-j);
     add_apply(dum,nob);
     add_apply(s_v_i(part,i),nob);
     add_apply(s_v_i(part,j),nob);
     mult_apply(nob,top);
      }
      
      for (;j<last;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(n,nob);
     c_i_i(dum,i+j+2);
     add_apply(dum,nob);
     copy(s_v_i(conj,i),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     copy(s_v_i(conj,j),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     mult_apply(nob,top);
      }
   }

   div(top,bot,dim);

   freeall(part); freeall(conj);
   freeall(nob); freeall(hook); freeall(dum);
   freeall(top); freeall(bot);

   return(OK);
}


INT or_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* orthogonal group */ 

{  INT i,j,no_rows,no_cols,bal,square,first,last;
   OP dum;
   OP part,conj;
   OP top,bot,nob,hook;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("or_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   if (!no_rows)
   {  m_i_i(1L,dim);
      return(OK);
   }
   no_cols=s_pa_ii(partition,no_rows-1);
   m_i_i(no_rows,dum=callocobject());
   addinvers_apply(dum);
   add_apply(n,dum);
   if (s_o_k(dum)==INTEGER)
      bal=s_i_i(dum);

   if (s_o_k(dum)==INTEGER && (bal<0 ||
       (bal<no_rows && s_pa_ii(partition,no_rows-1-bal)>1)) )
   {  printf("The partition passed to or_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   /* put the parts in decreasing order and construct the conjugate:
      we need to make them longer with enough zeros. */

   if (s_o_k(dum)!=INTEGER || bal>no_rows)
      bal=no_rows;
      
   square=bal>no_cols?bal:no_cols;
   m_il_v(square,part=callocobject());
   m_il_v(square,conj=callocobject());

   for (i=0;i<bal;i++)
      m_i_i(s_pa_ii(partition,no_rows-1-i),s_v_i(part,i));
   for (;i<square;i++)
      m_i_i(0,s_v_i(part,i));

   for (j=square-1;j>=no_cols;j--)
      m_i_i(0,s_v_i(conj,j));
   for (i=1;j>=0;j--)
     {  while (i<bal && s_v_ii(part,i)>j) i++;
        m_i_i(i,s_v_i(conj,j));
     }

   /* initialise a few things for the hook length calculation */

   m_i_i(1L,top=callocobject());
   m_i_i(1L,bot=callocobject());
   m_i_i(0L,hook=callocobject());
   nob=callocobject();

   /* visit all the boxes of Young diagram, accumulating hook
      length factors and numerator factors */

   for (i=0;i<bal;i++)
   {  last=s_v_ii(part,i);
      first=last<i ? last : i;

      for (j=0;j<first;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(n,nob);
     c_i_i(dum,i+j);
     add_apply(dum,nob);
     copy(s_v_i(conj,i),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     copy(s_v_i(conj,j),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     mult_apply(nob,top);
      }
      
      for (;j<last;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(n,nob);
     c_i_i(dum,-i-j-2);
     add_apply(dum,nob);
     add_apply(s_v_i(part,i),nob);
     add_apply(s_v_i(part,j),nob);
     mult_apply(nob,top);
      }
   }

   div(top,bot,dim);

   freeall(part); freeall(conj);
   freeall(nob); freeall(hook); freeall(dum);
   freeall(top); freeall(bot);

   return(OK);
}



INT so_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* special orthogonal group */ 

{  INT no_rows,bal;
   OP dum;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("so_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   if (!no_rows)
   {  m_i_i(1L,dim);
      return(OK);
   }
   m_i_i(no_rows,dum=callocobject());
   addinvers_apply(dum);
   add_apply(n,dum);
   if (s_o_k(dum)==INTEGER)
      bal=s_i_i(dum);

   if (s_o_k(dum)==INTEGER && bal<no_rows )
   {  printf("The partition passed to so_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   or_dimension(n,partition,dim);
   if (s_o_k(dum)==INTEGER && bal==no_rows)
   {  c_i_i(dum,2L);
      div(dim,dum,dim);
   }

   freeall(dum);

   return(OK);
}


INT pn_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* spin orthogonal group (pin group) */ 

{  INT i,j,no_rows,no_cols,bal,square,first,last;
   OP dum,nm;
   OP part,conj;
   OP top,bot,nob,hook;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("or_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   if (!no_rows)            /* empty partition: need to return 2^rank */
   {  m_i_i(1L,dim);
      copy(n,nm=callocobject());
      m_i_i(2L,dum=callocobject());
      ganzdiv_apply(dum,nm);
      for (;!nullp(nm);dec(nm))
         mult_apply(dum,dim);
      freeall(nm); freeall(dum);
      return(OK);
   }
   no_cols=s_pa_ii(partition,no_rows-1);
   m_i_i(no_rows,dum=callocobject());
   addinvers_apply(dum);
   add_apply(n,dum);
   if (s_o_k(dum)==INTEGER)
      bal=s_i_i(dum);

   if (s_o_k(dum)==INTEGER && bal<no_rows )
   {  printf("The partition passed to pn_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   /* put the parts in decreasing order and construct the conjugate:
      we need to make them longer with enough zeros. */

   if (s_o_k(dum)!=INTEGER || bal>no_rows)
      bal=no_rows;
      
   square=bal>no_cols?bal:no_cols;
   m_il_v(square,part=callocobject());
   m_il_v(square,conj=callocobject());

   for (i=0;i<bal;i++)
      m_i_i(s_pa_ii(partition,no_rows-1-i),s_v_i(part,i));
   for (;i<square;i++)
      m_i_i(0,s_v_i(part,i));

   for (j=square-1;j>=no_cols;j--)
      m_i_i(0,s_v_i(conj,j));
   for (i=1;j>=0;j--)
     {  while (i<bal && s_v_ii(part,i)>j) i++;
        m_i_i(i,s_v_i(conj,j));
     }

   /* initialise a few things for the hook length calculation */

   m_i_i(1L,top=callocobject());
   m_i_i(1L,bot=callocobject());
   m_i_i(0L,hook=callocobject());
   nob=callocobject();
   copy(n,nm=callocobject());
   dec(nm);

   /* visit all the boxes of Young diagram, accumulating hook
      length factors and numerator factors.
      for spin cases, use symplectic formula! */

   for (i=0;i<bal;i++)
   {  last=s_v_ii(part,i);
      first=last<i ? last : i;

      for (j=0;j<first;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(nm,nob);
     c_i_i(dum,-i-j);
     add_apply(dum,nob);
     add_apply(s_v_i(part,i),nob);
     add_apply(s_v_i(part,j),nob);
     mult_apply(nob,top);
      }
      
      for (;j<last;j++)
      {
         c_i_i(hook,s_v_ii(part,i)+s_v_ii(conj,j)-i-j-1);
     mult_apply(hook,bot);

     copy(nm,nob);
     c_i_i(dum,i+j+2);
     add_apply(dum,nob);
     copy(s_v_i(conj,i),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     copy(s_v_i(conj,j),dum);
     addinvers_apply(dum);
     add_apply(dum,nob);
     mult_apply(nob,top);
      }
   }

   div(top,bot,dim);
   
   /* now multiply by a power of 2 */

   inc(nm);
   c_i_i(dum,2L);
   ganzdiv_apply(dum,nm);
   for (;!nullp(nm);dec(nm))
      mult_apply(dum,dim);

   freeall(part); freeall(conj);
   freeall(nob); freeall(hook); freeall(dum);
   freeall(top); freeall(bot); freeall(nm);

   return(OK);
}


INT sn_dimension (n,partition,dim) OP n; OP partition; OP dim;

   /* spin special orthogonal group (spin group) */ 

{  INT no_rows,bal;
   OP dum,r,res;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("sn_dimension() did not receive the correct objects!\n");
         m_i_i(0L,dim);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   m_i_i(no_rows,dum=callocobject());
   addinvers_apply(dum);
   add_apply(n,dum);
   if (s_o_k(dum)==INTEGER)
      bal=s_i_i(dum);

   if (s_o_k(dum)==INTEGER && bal<no_rows )
   {  printf("The partition passed to sn_dimension() has tooo many parts!\n");
      m_i_i(0L,dim);
      return(ERROR);
   }

   pn_dimension(n,partition,dim);

   /* must divide by two if n is even */

   c_i_i(dum,2L);
   quores(n,dum,r=callocobject(),res=callocobject());
   if (nullp(res))
      div(dim,dum,dim);

   freeall(dum); freeall(r); freeall(res);

   return(OK);
}


/*************************************************************************
 Routines to calculate standard tableaux for the classical groups
*************************************************************************/


static OP standard;
static OP spin;
static INT ni,ri,no_rows,no_cols,level,count;
static INT *part;


INT gl_tableaux (n,partition,list) OP n; OP partition; OP list;

   /* generates standard tableaux for the general linear group GL(n) */ 

{  INT i;
   INT *filling;
   OP empty_tab;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("gl_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);

   if (!no_rows)         /* If the partition is 0, then create a single
                1x1 tableau with entry 0. */
   {  OP vec,par,tab;
      m_il_v(1L,vec=callocobject());
      m_i_i(1L,s_v_i(vec,0L));
      b_ks_pa(VECTOR,vec,par=callocobject());
      m_u_t(par,tab=callocobject());
      m_i_i(0L,s_t_ij(tab,0L,0L));
      b_sn_l(tab,NULL,list);
      freeall(par);
      return(1L);
   }
   
   if (no_rows > s_i_i(n))
   {  printf("The partition passed to gl_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   /* put the parts in decreasing order: append a zero part */

   part=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
   filling=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

   for (i=0;i<no_rows;i++)
      part[i]=s_pa_ii(partition,no_rows-1-i);
   part[i]=0;

   /* start the recursive tableaux generation process */

   m_u_t(partition,empty_tab=callocobject());
   standard=NULL;
   count=level=0;
   gl_generate(empty_tab,part,filling,s_i_i(n),no_rows-1);

   /* put the tableaux list into the argument to this routine */

   if (standard==NULL)
      init(LIST,list);
   else
   {  b_ks_o(s_o_k(standard),s_o_s(standard),list);
      SYM_free(standard);
   }

   SYM_free(part);
   SYM_free(filling);

   freeall(empty_tab);

   return(count);
}


static INT gl_generate (skew_tab,un_part,filling,entry,row)
    OP skew_tab; INT *un_part; INT *filling; INT entry; INT row;

/* recursive function to generate standard tableaux for the general linear 
   group GL(n). skew_tab is a partially filled tableaux. One iteration
   of this function puts a number of _entry into the row _row.
   un_part gives the shape of the unfilled part of the tableau before
   ANY _entry was placed. filling is the changed unfilled part after
   _entry s are included, but only for rows below that currently
   being considered.
*/

{  INT j,i;
   INT *new_fill;
   OP new_tab,new_part,ext;

   copy_tableaux(skew_tab,new_tab=callocobject());

   if (row==entry-1)  /* fill up the current row */
   {  for (j=0;j<un_part[row];j++)
     m_i_i(entry,s_t_ij(new_tab,row,j));
      filling[row]=0;

      if (row==0) /* store completely filled tableau in list */
      {  b_sn_l(new_tab,standard,ext=callocobject());
     standard=ext;
     count++;
      }
      else /* resubmit, filling a higher row */
      {
         gl_generate (new_tab,un_part,filling,entry,row-1);
     freeall(new_tab);
      }
   }
   else  /* there is a range of the number of entries to fill */
   {  
      filling[row]=un_part[row];
      for (j=un_part[row];j>=un_part[row+1];j--)
      {  
     /* start with 0 of entry in the current row - up to
        up_part[row+1]-up_part[row] */

     if (j<un_part[row])
     {  m_i_i(entry,s_t_ij(new_tab,row,j));
        filling[row]--;
         }

         /* and now resubmit to recursion */

         if (row>0)
            gl_generate(new_tab,un_part,filling,entry,row-1);
         else 
            /* start putting in a different entry: 
           must update the unfilled bit */
         {
        /* find lowest unfilled row */

        for (i=no_rows-1;filling[i]==0;i--);
        if (i>=0)
        {  new_fill=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
               gl_generate(new_tab,filling,new_fill,entry-1,i);
               SYM_free(new_fill);
            }
        else  /* tableau is full: need to store it. */
        {
               b_sn_l(new_tab,standard,ext=callocobject());
               standard=ext;
               count++;
               return(OK);
        }
         }   
      }

      freeall(new_tab);
   }

   return(OK);
}


INT sp_tableaux (n,partition,list) OP n; OP partition; OP list;

   /* generates standard tableaux for the symplectic group Sp(n) */ 

{  INT i;
   INT *filling;
   OP empty_tab;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || !(s_o_k(n)==INTEGER || s_o_k(n)==LONGINT) )
      {  printf("sp_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   ni=s_i_i(n);
   ri=ni/2;
   no_rows=s_pa_li(partition);

   if (!no_rows)         /* If the partition is 0, then create a single
                1x1 tableau with entry 0. */
   {  OP vec,par,tab;
      m_il_v(1L,vec=callocobject());
      m_i_i(1L,s_v_i(vec,0L));
      b_ks_pa(VECTOR,vec,par=callocobject());
      m_u_t(par,tab=callocobject());
      m_i_i(0L,s_t_ij(tab,0L,0L));
      b_sn_l(tab,NULL,list);
      freeall(par);
      return(1L);
   }

   if (no_rows > ri+(ni&1))
      /* allow one extra part for odd dimensions! */
   {  printf("The partition passed to sp_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   if (ni&1)
   {  printf("Warning! sp_tableaux received odd group specification!\n");
   }

   /* put the parts in decreasing order: append a zero part */

   part=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
   filling=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

   for (i=0;i<no_rows;i++)
      part[i]=s_pa_ii(partition,no_rows-1-i);
   part[i]=0;

   /* start the recursive tableaux generation process - if n is
      even then the first entrys are r. Otherwise 0. */

   m_u_t(partition,empty_tab=callocobject());
   standard=NULL;
   count=level=0;
   sp_generate(empty_tab,part,filling,ni&1?0:ri,no_rows-1);

   /* put the tableaux list into the argument to this routine */

   if (standard==NULL)
      init(LIST,list);
   else
   {  b_ks_o(s_o_k(standard),s_o_s(standard),list);
      SYM_free(standard);
   }

   SYM_free(part);
   SYM_free(filling);

   freeall(empty_tab);

   return(count);
}


static INT sp_generate (skew_tab,un_part,filling,entry,row)
    OP skew_tab; INT *un_part; INT *filling; INT entry; INT row;

/* recursive function to generate standard tableaux for the symplectic
   group Sp(n). skew_tab is a partially filled tableaux. One iteration
   of this function puts a number of _entry into the row _row.
   un_part gives the shape of the unfilled part of the tableau before
   ANY _entry was placed. filling is the changed unfilled part after
   _entry s are included, but only for rows below that currently
   being considered.
*/

{  INT j,i;
   INT *new_fill;
   OP new_tab,new_part,ext;

   copy_tableaux(skew_tab,new_tab=callocobject());

   if (row+entry+1==0 || row==ri)  /* fill up the current row */
   {  for (j=0;j<un_part[row];j++)
     m_i_i(entry,s_t_ij(new_tab,row,j));
      filling[row]=0;

      if (row==0) /* store completely filled tableau in list */
      {  b_sn_l(new_tab,standard,ext=callocobject());
     standard=ext;
     count++;
      }
      else /* resubmit, filling a higher row */
      {
         sp_generate (new_tab,un_part,filling,entry,row-1);
     freeall(new_tab);
      }
   }
   else  /* there is a range of the number of entries to fill */
   {  
      filling[row]=un_part[row];
      for (j=un_part[row];j>=un_part[row+1];j--)
      {  
     /* start with 0 of entry in the current row - up to
        up_part[row+1]-up_part[row] */

     if (j<un_part[row])
     {  m_i_i(entry,s_t_ij(new_tab,row,j));
        filling[row]--;
         }

         /* and now resubmit to recursion */

         if (row>0)
            sp_generate(new_tab,un_part,filling,entry,row-1);
         else 
            /* start putting in a different entry: 
           must update the unfilled bit */
         {
        /* find lowest unfilled row */

        for (i=no_rows-1;filling[i]==0;i--);
        if (i>=0)
        {  new_fill=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
               if (entry>0)
                  sp_generate(new_tab,filling,new_fill,-entry,i);
               else if (entry<0)
                  sp_generate(new_tab,filling,new_fill,-entry-1,i);
           else
          sp_generate(new_tab,filling,new_fill,ri,i);
               SYM_free(new_fill);
            }
        else  /* tableau is full: need to store it. */
        {
               b_sn_l(new_tab,standard,ext=callocobject());
               standard=ext;
               count++;
               return(OK);
        }
         }   
      }

      freeall(new_tab);
   }

   return(OK);
}


INT or_tableaux (n,partition,list) OP n; OP partition; OP list;

   /* generates standard tableaux for the orthogonal group O(n) */ 

{  INT i;
   INT *filling;
   OP empty_tab;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || s_o_k(n)!=INTEGER )
      {  printf("or_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   ni=s_i_i(n);
   ri=ni/2;
   no_rows=s_pa_li(partition);

   if (!no_rows)         /* If the partition is 0, then create a single
                1x1 tableau with entry 0. */
   {  OP vec,par,tab;
      m_il_v(1L,vec=callocobject());
      m_i_i(1L,s_v_i(vec,0L));
      b_ks_pa(VECTOR,vec,par=callocobject());
      m_u_t(par,tab=callocobject());
      m_i_i(0L,s_t_ij(tab,0L,0L));
      b_sn_l(tab,NULL,list);
      freeall(par);
      return(1L);
   }

   if (ni<no_rows 
       || (ni<2*no_rows && s_pa_ii(partition,2*no_rows-ni-1)>1) )
   {  printf("The partition passed to or_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   /* put the parts in decreasing order: append a zero part */

   part=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
   filling=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

   for (i=0;i<no_rows;i++)
      filling[i]=part[i]=s_pa_ii(partition,no_rows-1-i);
   part[i]=0;

   /* find length of second column */ 

   for (i=no_rows-1;i>=0 && part[i]<2;i--);

   /* start the recursive tableaux generation process - if n is
      even then the first entrys are 0. Otherwise ri. */

   m_u_t(partition,empty_tab=callocobject());
   standard=NULL;
   count=level=0;
   or_generate(empty_tab,part,filling,ni&1?0:ri,no_rows-1,no_rows,++i);

   /* put the tableaux list into the argument to this routine */

   if (standard==NULL)
      init(LIST,list);
   else
   {  b_ks_o(s_o_k(standard),s_o_s(standard),list);
      SYM_free(standard);
   }

   freeall(empty_tab);

   SYM_free(part);
   SYM_free(filling);

   return(count);
}



static INT or_generate (skew_tab, un_part, filling,  entry,  row, alpha,  beta)
    OP skew_tab; INT *un_part; INT *filling; INT entry; INT row;
                 INT alpha; INT beta;

/* recursive function to generate standard tableaux for the orthogonal 
   group O(n). skew_tab is a partially filled tableaux. One iteration
   of this function puts a number of _entry into the row _row.
   un_part gives the shape of the unfilled part of the tableau before
   ANY _entry was placed. filling is the changed unfilled part after
   _entry s are included, but only for rows below that currently
   being considered.
*/

{  INT j,j_start;
   INT *new_fill;
   OP new_tab,new_part,ext;

   copy_tableaux(skew_tab,new_tab=callocobject());

   /* if we are entering a 1 or -1 then we need special consideration */

   if (entry==1) 
   {
      /* first fill the top row with -1 */

      for (j=0;j<un_part[0];j++)
         m_i_i(-entry,s_t_ij(new_tab,0,j));

      if (row==0)
      {
         b_sn_l(new_tab,standard,ext=callocobject());
         standard=ext;
         count++;

     /* we need another tableaux for the 1 filling of the top row */

         copy_tableaux(skew_tab,new_tab=callocobject());
      }
      
      for (j=0;j<un_part[row];j++)
         m_i_i(entry,s_t_ij(new_tab,row,j));

      b_sn_l(new_tab,standard,ext=callocobject());
      standard=ext;
      count++;
   }

   else
     /* there is a range of the number of entries to fill:
        j_start is set to be the leftmost that must be filled. */
   {
      j_start=un_part[row];      /* this is the default case */

      if (entry<0)
      {  if (row==alpha-1)
           /* the following code deals with both alpha>=beta */

        {  if (alpha+beta==-2*entry
          || (alpha+beta==-1-2*entry && (beta==0
             || (alpha<no_rows && s_t_iji(skew_tab,alpha,0)==-entry
            && (part[beta]<2 || s_t_iji(skew_tab,beta,1)!=-entry)
                        ))))
          j_start=0;
           else if (alpha==beta && alpha==-1-entry
               && un_part[alpha]>0 && filling[alpha]==0
               && un_part[alpha]<part[alpha]
               && s_t_iji(skew_tab,alpha,un_part[alpha])==-entry)
          j_start=un_part[alpha];  /* protection condition for = rows */
            }
         else if (row==beta-1)
        {  if (alpha+beta==-1-2*entry)
          j_start=1;
            }

      }
      else if (entry>0)
      {  if (row==alpha-1 && beta==0 && alpha==2*entry)
        j_start=0;
      }
      else if (alpha+beta==ni)        /* here entry is 0 and ni is odd */
      {  if (row==alpha-1 && beta==0)
        j_start=0;
         else if (row==beta-1)
        j_start=1;
      }

      /* now place the entries that are forced */

      for (j=j_start;j<un_part[row];j++)
         m_i_i(entry,s_t_ij(new_tab,row,j));
      filling[row]=j_start;


      if (j_start==0 && un_part[row]>0)
         alpha--;

      if (j_start<=1 && un_part[row]>1)
         beta--;

      /* now loop between 0 and as many as possible in current row */

      for (j=j_start;j>=un_part[row+1];j--)
      {  
         if (j<j_start)
     {  m_i_i(entry,s_t_ij(new_tab,row,j));
        filling[row]--;

            if (j==0)
           alpha--;
        else if (j==1)
           beta--;
     }

     /* and now resubmit to recursion */

         if (row>0)
            or_generate(new_tab,un_part,filling,entry,row-1,alpha,beta);
         else      /* just done the top row */ 
         {
        if (filling[row]==0)   /* tableau is now full */
        {
               b_sn_l(new_tab,standard,ext=callocobject());
               standard=ext;
               count++;
               level--;
               return(OK);
        }
        else      /* start putting in a different entry: 
                     must update the unfilled bit */

        {  new_fill=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
               memcpy(new_fill,filling,(no_rows+1)*sizeof(INT));

               if (entry>0)
                  or_generate(new_tab,filling,new_fill,-entry,
                           alpha-1,alpha,beta);
               else if (entry<0)
                  or_generate(new_tab,filling,new_fill,-entry-1,
                           alpha-1,alpha,beta);
               else 
                  or_generate(new_tab,filling,new_fill,ri,
                           alpha-1,alpha,beta);

               SYM_free(new_fill);
        }
         }   
      }

      freeall(new_tab);
   }
   level--;
   return(OK);
}


INT so_tableaux (n,partition,flag,list) INT flag;OP n; OP partition; OP list;

/* generates standard tableaux for the special orthogonal group SO(n).
   First generates tableaux for O(n) and if relevant (n even
   AND no. parts equal to n/2) extracts the required tableaux from
   this set. flag=-1 selects the - representation and if +1 selects
   the + representation.
*/

{  INT i,e,c,f,count;
   OP trawl,back;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || s_o_k(n)!=INTEGER )
      {  printf("so_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   no_rows=s_pa_li(partition);
   ni=s_i_i(n);
   ri=ni/2;

   if (ri<no_rows)
   {  printf("The partition passed to so_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   count=or_tableaux(n,partition,list);

   if (!(ni&1) && ri==no_rows) /* O(n) rep reduces on restriction to SO(n) */
   {  count=0;

      if (flag<0)
     f=1;
      else if (flag>0)
     f=0;
      else                     /* undocumented option! */
     f=(ri&1)?1:0;

      for (trawl=list,back=NULL;trawl!=NULL;)
      {
         for (i=c=0;i<ri;i++)
     {  
        e=s_t_iji(s_l_s(trawl),i,0L);
        if (e==i+1)       /* count number of positive entries in 1st col */
           c++;
            else if (e!=-i-1)
           break;         /* halt loop if entry not i+1 or -(i+1) */
         }

     /* now test whether this tableau should be excluded */

         if ( (i==ri && (f^c)&1)    /* test after e==i+1 all down tableau */ 
           || (i<ri && e>=-i && e<=i) )      /* entry tooo small here */
     {  
        if (back!=NULL)
        {  c_l_n(back,s_l_n(trawl));
           c_l_n(trawl,NULL);
           freeall(trawl);
           trawl=s_l_n(back);
            }
        else              /* at top of list */
        {  trawl=s_l_n(trawl); 
           c_l_n(list,NULL);
           freeself(list);
               b_ks_o(LIST,s_o_s(trawl),list);
           SYM_free(trawl);
           trawl=list;
            }
         }
         else
     {  trawl=s_l_n(back=trawl);
        count++;
     }
      }
   }

   return(count);
}


INT pn_tableaux (n,partition,list) OP n; OP partition; OP list;

   /* generates standard spin tableaux for the spin orthogonal group O(n) */ 

{  INT i;
   INT *filling;
   OP empty_tab,r,hafling;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || s_o_k(n)!=INTEGER )
      {  printf("or_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   ni=s_i_i(n);
   ri=ni/2;
   no_rows=s_pa_li(partition);

   if (ri<no_rows)
   {  printf("The partition passed to pn_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   /* put the parts in decreasing order: append a zero part */

   part=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
   filling=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

   for (i=0;i<no_rows;i++)
      filling[i]=part[i]=s_pa_ii(partition,no_rows-1-i);
   part[i]=0;

   standard=NULL;
   count=level=0;

   /* we consider the half boxes as a separate tableau. They will
      be generated in the outer loop here.
      Then, all tableaux of the given shape which has that
      particular half box configuration, are generated.
      First create a half box column with all barred entries.
   */

   m_i_i(ri,r=callocobject());
   last_partition(r,hafling=callocobject());
   m_u_t(hafling,spin=callocobject());
   freeall(r);
   freeall(hafling);
   for (i=0;i<ri;i++)
      m_i_i(-i-1,s_t_ij(spin,i,0));

   if (no_rows)        /* treat 0 partition differently */
   {
      while (1) 
      {  /* start the recursive tableaux generation process - if n is
            even then the first entrys are 0. Otherwise ri. */

         m_u_t(partition,empty_tab=callocobject());
         pn_generate(empty_tab,part,filling,ni&1?0:ri,no_rows-1);
         freeall(empty_tab);

         /* find the lowermost barred entry in the spin boxes
        and change it */

         for (i=ri-1;i>=0 && s_t_iji(spin,i,0)>0;i--);
         if (i>=0)
         {
            c_i_i(s_t_ij(spin,i,0),i+1);
        for (i++;i<ri;i++)
           c_i_i(s_t_ij(spin,i,0),-i-1);
         }
         else
        break;
      }
   }
   else             
   {  OP vec,par,tab,spin_cop,mon,ext;

      while (1) 
      {  
         m_il_v(1L,vec=callocobject());
         m_i_i(1L,s_v_i(vec,0L));
         b_ks_pa(VECTOR,vec,par=callocobject());
         m_u_t(par,tab=callocobject());
         m_i_i(0L,s_t_ij(tab,0L,0L));

         copy_tableaux(spin,spin_cop=callocobject());
     b_sk_mo(tab,spin_cop,mon=callocobject());
     b_sn_l(mon,standard,ext=callocobject());
         standard=ext;
         count++;
         freeall(par);

         /* find the lowermost barred entry in the spin boxes
        and change it */

         for (i=ri-1;i>=0 && s_t_iji(spin,i,0)>0;i--);
         if (i>=0)
         {
            c_i_i(s_t_ij(spin,i,0),i+1);
        for (i++;i<ri;i++)
           c_i_i(s_t_ij(spin,i,0),-i-1);
         }
         else
        break;
      }
   }

   freeall(spin);

   /* put the tableaux list into the argument to this routine */

   if (standard==NULL)
      init(LIST,list);
   else
   {  b_ks_o(s_o_k(standard),s_o_s(standard),list);
      SYM_free(standard);
   }

   SYM_free(part);
   SYM_free(filling);

   return(count);
}


static INT pn_generate (skew_tab, un_part, filling,  entry,  row)
OP skew_tab; INT *un_part; INT *filling; INT entry; INT row;

/* recursive function to generate spin standard tableaux for the orthogonal 
   group O(n). skew_tab is a partially filled tableaux. One iteration
   of this function puts a number of _entry into the row _row.
   un_part gives the shape of the unfilled part of the tableau before
   ANY _entry was placed. filling is the changed unfilled part after
   _entry s are included, but only for rows below that currently
   being considered.
*/

{  INT j,j_start,i;
   INT *new_fill;
   OP new_tab,new_part,ext,spin_cop,mon;

   copy_tableaux(skew_tab,new_tab=callocobject());

   if (entry==1 || entry==-1)
   {
      entry=s_t_iji(spin,row,0L);

      for (j=0;j<un_part[row];j++)
         m_i_i(entry,s_t_ij(new_tab,row,j));

      copy_tableaux(spin,spin_cop=callocobject());
      b_sk_mo(new_tab,spin_cop,mon=callocobject());
      b_sn_l(mon,standard,ext=callocobject());
      standard=ext;
      count++;
   }

   else
     /* there is a range of the number of entries to fill:
        j_start is set to be the leftmost that must be filled. */
   {
      j_start=un_part[row];      /* this is the default case */

      if (entry<0)
      {  if (row+entry==-1)
            j_start=0;
         else if (row+entry==-2 && s_t_iji(spin,row+1,0L)==entry
           && un_part[row+1]<part[row+1]
           && s_t_iji(skew_tab,row+1,un_part[row+1])==-entry)
        j_start=un_part[row+1];   /* protection condition for = rows */
      }
      else if (entry==row+1 && s_t_iji(spin,row,0L)==entry)
         j_start=0;
      else if (row==ri)    /* here entry can only be 0 */
     j_start=0;

      /* now place the entries that are forced */

      for (j=j_start;j<un_part[row];j++)
         m_i_i(entry,s_t_ij(new_tab,row,j));
      filling[row]=j_start;

      /* now loop between 0 and as many as possible in current row */

      for (j=j_start;j>=un_part[row+1];j--)
      {  

         if (j<j_start)
     {  m_i_i(entry,s_t_ij(new_tab,row,j));
        filling[row]--;
     }

     /* and now resubmit to recursion */

         if (row>0)
            pn_generate(new_tab,un_part,filling,entry,row-1);
         else      /* just done the top row */ 
         {
        /* find lowest unfilled row */

        for (i=no_rows-1;filling[i]==0;i--);
        if (i>=0)
        {  new_fill=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
               if (entry>0)
                  pn_generate(new_tab,filling,new_fill,-entry,i);
               else if (entry<0)
                  pn_generate(new_tab,filling,new_fill,-entry-1,i);
           else
                  pn_generate(new_tab,filling,new_fill,ri,i);
               SYM_free(new_fill);
            }
        else  /* tableau is full: need to store it. */
        {
               copy_tableaux(spin,spin_cop=callocobject());
           b_sk_mo(new_tab,spin_cop,mon=callocobject());
           b_sn_l(mon,standard,ext=callocobject());
               standard=ext;
               count++;
               return(OK);
        }
         }   
      }

      freeall(new_tab);
   }
   level--;
   return(OK);
}


INT sn_tableaux ( n,  partition,  flag,  list)
    OP n; OP partition; INT flag; OP list;

/* generates standard spin tableaux for the spin orthogonal group SO(n).
   If relevant (n is even), flag=-1 selects the - representation and 
   flag=+1 selects the + representation.
*/ 

{  INT i,f;
   INT *filling;
   OP empty_tab,r,hafling;

   if (partition==NULL || s_o_k(partition)!=PARTITION
     || n==NULL || s_o_k(n)!=INTEGER )
      {  printf("sn_tableaux() did not receive the correct objects!\n");
         init(LIST,list);
     return(ERROR);
      }

   ni=s_i_i(n);
   ri=ni/2;
   no_rows=s_pa_li(partition);

   if (ri<no_rows)
   {  printf("The partition passed to sn_tableaux() has tooo many parts!\n");
      init(LIST,list);
      return(ERROR);
   }

   if (ni&1)         /* same tableaux as for O(n) case */
      return(pn_tableaux(n,partition,list));

   if (flag>0)
     f=0;
   else if (flag<0)
     f=1;
   else
     f=ri&1;        /* undocumented: includes tableau with all spins barred */

   /* put the parts in decreasing order: append a zero part */

   part=(INT*)SYM_calloc(no_rows+1,sizeof(INT));
   filling=(INT*)SYM_calloc(no_rows+1,sizeof(INT));

   for (i=0;i<no_rows;i++)
      filling[i]=part[i]=s_pa_ii(partition,no_rows-1-i);
   part[i]=0;

   standard=NULL;
   count=level=0;

   /* we consider the half boxes as a separate tableau. They will
      be generated in the outer loop here.
      Then, all tableaux of the given shape which has that
      particular half box configuration, are generated.
      First create a half box column with all barred entries.
      For SO(2r) the lowermost spin entry is determined by the others.
   */

   m_i_i(ri,r=callocobject());
   last_partition(r,hafling=callocobject());
   m_u_t(hafling,spin=callocobject());
   freeall(r);
   freeall(hafling);
   for (i=0;i<ri-1;i++)
      m_i_i(-i-1,s_t_ij(spin,i,0));
   m_i_i((f^ri)&1?ri:-ri,s_t_ij(spin,ri-1,0));

   if (no_rows)            /* treat 0 partition differently */
   {
      while (1) 
      {  /* start the recursive tableaux generation process - if n is
            even then the first entrys are 0. Otherwise ri. */

         m_u_t(partition,empty_tab=callocobject());
         pn_generate(empty_tab,part,filling,ni&1?0:ri,no_rows-1);
         freeall(empty_tab);

         /* find the lowermost barred entry in the spin boxes
        (except the last) and change it */

         for (i=ri-2;i>=0 && s_t_iji(spin,i,0)>0;i--);
         if (i>=0)
         {
            c_i_i(s_t_ij(spin,i,0),i+1);
        if ( !((ri-i)&1) )  /* need to change last entry */
           addinvers_apply_integer(s_t_ij(spin,ri-1,0));
        for (i++;i<ri-1;i++)
           c_i_i(s_t_ij(spin,i,0),-i-1);
         }
         else
        break;
      }
   }
   else             
   {  OP vec,par,tab,spin_cop,mon,ext;

      while (1) 
      {  
         m_il_v(1L,vec=callocobject());
         m_i_i(1L,s_v_i(vec,0L));
         b_ks_pa(VECTOR,vec,par=callocobject());
         m_u_t(par,tab=callocobject());
         m_i_i(0L,s_t_ij(tab,0L,0L));

         copy_tableaux(spin,spin_cop=callocobject());
     b_sk_mo(tab,spin_cop,mon=callocobject());
     b_sn_l(mon,standard,ext=callocobject());
         standard=ext;
         count++;
         freeall(par);

         /* find the lowermost barred entry in the spin boxes
        (except the last) and change it */

         for (i=ri-2;i>=0 && s_t_iji(spin,i,0)>0;i--);
         if (i>=0)
         {
            c_i_i(s_t_ij(spin,i,0),i+1);
        if ( !((ri-i)&1) )  /* need to change last entry */
           addinvers_apply_integer(s_t_ij(spin,ri-1,0));
        for (i++;i<ri-1;i++)
           c_i_i(s_t_ij(spin,i,0),-i-1);
         }
         else
        break;
      }

   }

   freeall(spin);

   /* put the tableaux list into the argument to this routine */

   if (standard==NULL)
      init(LIST,list);
   else
   {  b_ks_o(s_o_k(standard),s_o_s(standard),list);
      SYM_free(standard);
   }

   SYM_free(part);
   SYM_free(filling);

   return(count);
}


INT tableaux_character ( list,  r,  character)
    OP list; OP r; OP character;

/* Takes a list of standard tableaux (maximum entry r) and computes
   the corresponding character by summing over all tableaux, the
   monomial formed by multplying indeterminants for each entry
   (negative entries give the indeterminant to the negative power).
*/

{  INT i,j,e;
   OP trawl,term,pol;

   if (s_o_k(list)!=LIST || s_o_k(r)!=INTEGER
         || (!empty_listp(list) && s_o_k(s_l_s(list))!=TABLEAUX))
   {  printf("tableaux_character() did not receive correct arguments!");
      return(ERROR);
   }

   if (empty_listp(list))
   {  init(POLYNOM,character);
      return(OK);
   }

   if (!emptyp(character))
      freeself(character);

   /* get the shape of the first tableau and assume the others are
      of the same shape. */

   no_rows=s_pa_li(s_t_u(s_l_s(list)));
   
   /* put the parts in decreasing order: */

   part=(INT*)SYM_calloc(no_rows,sizeof(INT));

   for (i=0;i<no_rows;i++)
      part[i]=s_pa_ii(s_t_u(s_l_s(list)),no_rows-1-i);

   /* go through the list and form a monomial for each tableau */

   for (trawl=list;trawl!=NULL;trawl=s_l_n(trawl))
   {
      m_il_nv(s_i_i(r),term=callocobject());

      for (i=0;i<no_rows;i++)
      for (j=0;j<part[i];j++)
      {  if ((e=s_t_iji(s_l_s(trawl),i,j))>0)
        inc(S_V_I(term,e-1));
     else if (e<0)
        dec(S_V_I(term,-e-1));
      }

      b_skn_po(term,callocobject(),NULL,pol=callocobject());
      m_i_i(1L,s_po_k(pol));
      insert(pol,character,NULL,NULL);
   }

   SYM_free(part);
   return(OK);
}


INT spin_tableaux_character ( list,  r,  character) OP list; OP r; OP character;

/* Takes a list of standard spin-tableaux (maximum entry r) and computes
   the corresponding character by summing over all such tableaux, the
   monomial formed by multplying indeterminants for each entry
   (negative entries give the indeterminant to the negative power)
   in the spin part and the square of the indeterminants for each
   entry in the tensor part. Thus, in the resulting polynomial,
   each exponent is twice the value it should be (to accommodate
   half odd integer values). A spin-tableau is regarded as a pair
   of tableaux (in a MONOM object), the koeff part is a single column
   of height the rank (r) giving the spin indices, the self part is
   the set of usual tensor indices.
*/

{  INT i,j,e;
   OP trawl,term,pol;

   if (s_o_k(list)!=LIST || s_o_k(r)!=INTEGER
         || (!empty_listp(list) && (s_o_k(s_l_s(list))!=MONOM 
         || s_o_k(s_mo_k(s_l_s(list)))!=TABLEAUX
         || s_o_k(s_mo_s(s_l_s(list)))!=TABLEAUX)))
   {  printf("spin_tableaux_character() did not receive correct arguments!");
      return(ERROR);
   }

   if (empty_listp(list))
   {  init(POLYNOM,character);
      return(OK);
   }

   if (!emptyp(character))
      freeself(character);

   /* get the shape of the first tableau and assume the others are
      of the same shape. */

   no_rows=s_pa_li(s_t_u(s_mo_s(s_l_s(list))));
   ri=s_i_i(r);      /* length of spin column */

   /* put the parts in decreasing order: */

   part=(INT*)SYM_calloc(no_rows,sizeof(INT));

   for (i=0;i<no_rows;i++)
      part[i]=s_pa_ii(s_t_u(s_mo_s(s_l_s(list))),no_rows-1-i);

   /* go through the list and form a monomial for each tableau */

   for (trawl=list;trawl!=NULL;trawl=s_l_n(trawl))
   {
      m_il_nv(ri,term=callocobject());

      for (i=0;i<no_rows;i++)
      for (j=0;j<part[i];j++)
      {  if ((e=s_t_iji(s_mo_s(s_l_s(trawl)),i,j))>0)
     {  inc(S_V_I(term,e-1));
        inc(S_V_I(term,e-1));
     }
     else if (e<0)
     {  dec(S_V_I(term,-e-1));
        dec(S_V_I(term,-e-1));
         }
      }

      for (i=0;i<ri;i++)
      {  if ((e=s_t_iji(s_mo_k(s_l_s(trawl)),i,0L))>0)
     {  inc(S_V_I(term,e-1));
     }
     else if (e<0)
     {  dec(S_V_I(term,-e-1));
         }
      }

      b_skn_po(term,callocobject(),NULL,pol=callocobject());
      m_i_i(1L,s_po_k(pol));
      insert(pol,character,NULL,NULL);
   }

   SYM_free(part);
   return(OK);
}


INT gl_character ( n,  partition,  character) OP n; OP partition; OP character;

/* calculates the character (in n indeterminants) of the representation 
   of GL(n) labelled by partition. This is the Schur function.
*/

{  INT erg;
   OP t_list;

   if (s_pa_li(partition)==0)      /* null partition => char=1 */
      erg=m_i_i(1L,character);
   else
   {  erg=gl_tableaux(n,partition,t_list=callocobject());
      if (erg>=0)
         erg=tableaux_character(t_list,n,character);
      freeall(t_list);
   }

   return(erg);
}


INT sp_character ( n,  partition,  character)OP n; OP partition; OP character;

/* calculates the character (in [n/2] indeterminants) of the representation 
   of Sp(n) labelled by partition.
*/

{  INT erg;
   OP t_list,r;

   if (s_pa_li(partition)==0)
      erg=m_i_i(1L,character);
   else
   {  erg=sp_tableaux(n,partition,t_list=callocobject());
      m_i_i(s_i_i(n)/2L,r=callocobject());
      if (erg>=0)
         erg=tableaux_character(t_list,r,character);
      freeall(t_list);
      freeall(r);
   }

   return(erg);
}


INT or_character ( n,   partition,  character) OP n,partition,character;

/* calculates the character (in [n/2] indeterminants) of the ordinary
   representation of O(n) labelled by partition.
*/

{  INT erg;
   OP t_list,r;

   if (s_pa_li(partition)==0)
      erg=m_i_i(1L,character);
   else
   {  erg=or_tableaux(n,partition,t_list=callocobject());
      m_i_i(s_i_i(n)/2L,r=callocobject());
      if (erg>=0)
         erg=tableaux_character(t_list,r,character);
      freeall(t_list);
      freeall(r);
   }

   return(erg);
}


INT so_character ( n,  partition,  flag,  character) 
    OP n,partition,character; INT flag;

/* calculates the character (in [n/2] indeterminants) of the ordinary
   representation of SO(n) labelled by partition.
   In the case where n is even AND no. parts equal to n/2, we need
   to specify the + or - representation: flag=-1 selects the -
   representation and if +1 selects the + representation.
*/

{  INT erg;
   OP t_list,r;

   if (s_pa_li(partition)==0)
      erg=m_i_i(1L,character);
   else
   {  erg=so_tableaux(n,partition,flag,t_list=callocobject());
      m_i_i(s_i_i(n)/2L,r=callocobject());
      if (erg>=0)
         erg=tableaux_character(t_list,r,character);
      freeall(t_list);
      freeall(r);
   }

   return(erg);
}


INT pn_character ( n,  partition,  character)OP n; OP partition; OP character;

/* calculates the character (in [n/2] indeterminants) of the spin
   representation of O(n) labelled by partition.
*/

{  INT erg;
   OP t_list,r;

   erg=pn_tableaux(n,partition,t_list=callocobject());
   m_i_i(s_i_i(n)/2L,r=callocobject());
   if (erg>=0)
      erg=spin_tableaux_character(t_list,r,character);
   freeall(t_list);
   freeall(r);

   return(erg);
}


INT sn_character ( n,  partition,  flag,  character)
    OP n; OP partition; INT flag; OP character;

/* calculates the character (in [n/2] indeterminants) of the spin
   representation of SO(n) labelled by partition.
   If relevant (n is even), flag=-1 selects the - representation and 
   flag=+1 selects the + representation.
*/

{  INT erg;
   OP t_list,r;

   erg=sn_tableaux(n,partition,flag,t_list=callocobject());
   m_i_i(s_i_i(n)/2L,r=callocobject());
   if (erg>=0)
      erg=spin_tableaux_character(t_list,r,character);
   freeall(t_list);
   freeall(r);

   return(erg);
}



