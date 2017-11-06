
#include "def.h"
#include "macro.h"

static INT l_schur_monomial_mult_new();

INT cc_muir_mms_partition_partition_(a,b,c,f) OP a,b,c,f;
/* AK 071201 called from mms_partition_partition_ */
{
    INT erg = OK;
    OP wa,wb;
    CTO(PARTITION,"cc_muir_mms_partition_partition_(1)",a);
    CTO(PARTITION,"cc_muir_mms_partition_partition_(2)",b);
    CTO(HASHTABLE,"cc_muir_mms_partition_partition_(3)",c);
    wa = CALLOCOBJECT();
    weight_partition(a,wa);
    wb = CALLOCOBJECT();
    weight_partition(b,wb);
    add_apply(wa,wb);
    l_schur_monomial_mult_new(wb,b,a,c,f);
    FREEALL2(wa,wb);
    ENDR("cc_muir_mms_partition_partition_");
}

typedef INT PLETCHAR; 

struct cel{
        struct cel *prec;
        struct cel *suiv;
        PLETCHAR *tab;
        long coef;
};
 
struct lst{ struct cel *deb; };
 



static INT muir_lim_new(limit,cond,s,psi,plst) 
   PLETCHAR limit,cond,*s,*psi;
   struct lst *plst;
/* CC */
{
    PLETCHAR lg_s,  avv=0, lg_psi, sig, sigav=0, j, bl=0, max,mv;
    PLETCHAR *uu, *av, *def, *pos, *tb, *bav, *bdef, *bpos, *btb;
    register PLETCHAR *buu,*bs;
    register PLETCHAR k,tp,tmp;
    struct cel *pcrt,*q=NULL,*ins;
    long lp;


    bs=s+1; 
    while(*bs) bs++; 
    tmp=bs-(s+1);
    lg_s=tmp; tp=0;
    bs=psi+1; 
    while(*bs) tp+= *bs++;
    lg_psi=bs-(psi+1); 
    tmp=lg_s+tp;

    s=(PLETCHAR *) SYM_realloc(s,(tmp+20)*sizeof(PLETCHAR));
    buu=s+lg_s+2;
    for(k=0;k<= tp;k++,buu++) *buu=0;

    uu=(PLETCHAR *)SYM_calloc(tmp+2,sizeof(PLETCHAR));
    av=(PLETCHAR *)SYM_calloc(tmp+2,sizeof(PLETCHAR));
    def=(PLETCHAR *)SYM_calloc(tmp+2,sizeof(PLETCHAR));
    tb=(PLETCHAR *)SYM_MALLOC((lg_psi+2)*sizeof(PLETCHAR));
    pos=(PLETCHAR *)SYM_MALLOC((lg_psi+2)*sizeof(PLETCHAR));

    pcrt=(struct cel *)SYM_MALLOC(sizeof(struct cel));
    pcrt->prec=pcrt->suiv=NULL;
    plst->deb=pcrt;
    mv=0;
    pcrt->coef=1L;

    if(cond==0 || (cond==1 && limit >= *(s+1) + *(psi+1)))
    {
        pcrt->coef=1L;
        bav=av+1; bdef=def+1; buu=s+1;
         while(*buu)    
        {
            *bav=*bdef=*buu;     buu++;bav++,bdef++;
        }
    
        bpos=pos+1; btb=tb+1; bdef=def+1; bav= av+1; buu= psi+1;
        for(k=1; k<=lg_psi; bpos++,btb++,bdef++,bav++,k++,buu++)
        {
            *bpos=k; 
            *btb= *buu; 
            *bdef += *buu; 
            *bav += *buu; 
        }
        *bpos=0; *btb=0;
    
        avv=lg_psi-1; *(bav-1)=0;
        if(lg_psi>lg_s)
        {
            buu=(PLETCHAR *)SYM_MALLOC((lg_psi+1)*sizeof(PLETCHAR));
            *bdef=0;
        }
        else
        {
            buu=(PLETCHAR *)SYM_MALLOC((lg_s+1)*sizeof(PLETCHAR));
            *(def+lg_s+1)=0;
        }
    
        bs=def+1; pcrt->tab=buu;
        while(*bs) *buu++ = *bs++;
        *buu=0;
    
        sigav=1; j=lg_psi;
        bpos=pos+lg_psi; btb=tb+lg_psi;
    }
    
    else
    {
        if(lg_psi> lg_s)
        {
            buu=(PLETCHAR *)SYM_MALLOC((lg_psi+1)*sizeof(PLETCHAR));
            pcrt->tab=buu;
            bs=s+1;bdef=psi+1;
            for(k=0;k<lg_s;k++,bdef++,bs++,buu++)
                *buu= *bs+ *bdef;
            for(;k<lg_psi;k++,bdef++,buu++) *buu= *bdef;
            *buu=0;
        }
        else
        {
            buu=(PLETCHAR *)SYM_MALLOC((lg_s+1)*sizeof(PLETCHAR));
            pcrt->tab=buu;
            bs=s+1;bdef=psi+1;
            for(k=0;k<lg_psi;k++,bdef++,bs++,buu++)
                *buu= *bs+ *bdef;
            for(;k<lg_s;k++,bs++,buu++) *buu= *bs;
            *buu=0;
        }

        bs=tb+1; 
        buu=psi+1;
        while(*buu) *bs++ = *buu++;
        *bs=0;

        bs=s+1; buu=uu+1; bdef=def+1;
        while(*bs) *buu++ = *bdef++ = *bs++;
        *buu=0;

        bdef=def+1; btb=tb+1; buu=uu+1; bpos=pos+1;
        sig=1;
        for(j=1;j<=tmp;j++,bdef++,buu++)
        {
            tp= *bdef + *btb -1; bs=buu-1; bl=0;
            for(k=j-1;k>=1;k--,tp--,bs--)
            {
                if(*bs==tp){bl=1;break;}
                if(*bs>tp){bl=2;break;}
            }

            if(bl==1) continue;
            if(bl==0 && *bdef+ *btb -(j-1) > limit) continue;
            if(btb-tb==lg_psi)
            {
                avv=j-1;
                bs=av+1;
                sigav=sig;
                buu= uu+1;
                for(k=1;k<=avv;k++,bs++,buu++)
                    *bs= *buu;
                *bs=0;
            }
            *bpos++ =j; *bdef += *btb++;
            *buu = *bdef; bs=buu;
            for(tp=j;tp>k+1;tp--,bs--)
            {
                mv= *bs; *bs= *(bs-1)+1;
                *(bs-1)=mv-1; sig= -sig;
            }    
            if(btb-tb==lg_psi+1) break;
        }

        ins=(struct cel *)SYM_MALLOC(sizeof(struct cel));
        ins->prec=pcrt;pcrt->suiv=ins; ins->suiv=NULL;
        ins->coef=sig;
        if (j>lg_s) bs=(PLETCHAR *)SYM_MALLOC((j+1)*sizeof(PLETCHAR));
        else bs=(PLETCHAR *)SYM_MALLOC((lg_s+1)*sizeof(PLETCHAR));
        ins->tab=bs;
        buu=uu+1;
        while(*buu) *bs++ = *buu++;
        *bs=0;
        pcrt=ins;

        *bpos-- =0;
        *btb-- =0;
        mv=0;bl=1;
        j=lg_psi;
    }
aa:        
    for(;j>=1;j--,btb--,bpos--)
    {
        bdef=def+ *bpos; bs=s+ *bpos;
        while(1)
        {
            tp= *bpos+1- *btb;
            if(
                  (
                       (tp>lg_s)
                        &&
                       (  (j>1&&tp> *(bpos-1)) || (j==1))
                  )
                  || 
                  (    
                       (cond==0) && (*bpos+1+lg_psi-j>limit)
                  )
              )
            {    /*Shift is finished*/

                tmp=*btb; max= -1; buu=btb+1;
                for(k=j+1;k<=lg_psi;k++,buu++)
                    if(*buu<tmp && *buu>max)
                    {
                        max= *buu;tp=k;
                    }

                if(max!= -1)
                {    /*Can put *buu at the position *bpos*/
                    *btb=max;tb[tp]=tmp;
                    if(j>1) *bpos= *(bpos-1)+1;
                    else *bpos= 1;
                    bdef= def+ *bpos; bs=s+ *bpos;
                    *bdef= *btb+ *bs;

                    tp= *bpos>*btb+1? *bpos- *btb:1;
                    tmp= *bdef-1; buu=bdef-1;
                    for(k= *bpos-1;k>=tp;k--,tmp--,buu--)
                        if(*buu==tmp)break;

                    if(k==tp-1)
                    {    /*Succeed*/
                        j++;bpos++;btb++;
                        bs++;bdef++;
                        goto bb;
                    }
                }/*End of if(max!= -1)*/
                else break;
            }/*End of if(tp>lg_s&&(j>1&&tp> *(bpos-1)||j==1))*/
             else
            {    /*Shift*/
                (*bpos)++; bdef++;bs++;
                *bdef= *btb+ *bs;
                *(bdef-1) -= *btb;

                tp= *bpos>*btb+1? *bpos- *btb:1;
                tmp= *bdef-1; buu=bdef-1;
                for(k= *bpos-1;k>=tp;k--,tmp--,buu--)
                    if(*buu==tmp)break;

                if(k==tp-1)
                {    /*Succeed*/
                    j++;bpos++;btb++;
                    bs++;bdef++;
                    goto bb;
                }
            }/*End of else if(tp>lg_s&&(j>1&&tp> *(bpos-1)||j==1))*/
        }/*End of while(1)*/
    }/*End of for(;j>=1;...)*/

    goto cc;

bb:    for(;j<=lg_psi;j++,bpos++,btb++,bs++,bdef++)
    {
        bl=1;
        if(j!=lg_psi)
        {
            max= -1; buu=btb;
            for(k=j;k<=lg_psi;k++,buu++)
                if(max< *buu)
                {
                    max= *buu;tp=k;
                }
            /*max must be different from -1*/
            tmp= *btb; *btb=max; tb[tp]=tmp;
        }
        /*not else because nothing changes if(j==lg_psi)*/
        *bpos= *(bpos-1)+1;    /*j must be >1*/
        *bdef= *btb+ *bs;

        tp= *bpos>*btb+1? *bpos- *btb:1;
        tmp= *bdef-1; buu=bdef-1;
        for(k= *bpos-1;k>=tp;k--,tmp--,buu--)
            if(*buu==tmp)break;

        if(k!=tp-1) goto aa;
    }/* End of for(;j<=lg_psi;...*/


    bpos--;btb--;j--;

    if(cond==0)
    {
        if(bl==1)
        {    /*bs is free*/
            bdef=def+1; buu=uu+1;
            for(k=1;k<= *bpos;k++,bdef++,buu++) *buu= *bdef;    
    
            sig=1; bs=uu+2;
            for(k=2;k<= *(bpos-1);k++,bs++)
            {
                buu=bs;
                for(tp=k;tp>1;tp--,buu--)
                {
                    if(*buu> *(buu-1))
                    {
                        tmp= *buu; *buu= *(buu-1)+1;
                        *(buu-1)=tmp-1; sig= -sig;
                    }
                    else break;
                }
            }
            sigav=sig;
    
            bav=av+1;buu=uu+1;avv= *bpos-1;
            for(k=1;k<=avv;k++,buu++,bav++) *bav= *buu;
        }
        else
        {
    
            sig=sigav;
    
            buu=uu+1;bav=av+1;
            for(k=1;k<=avv;k++,buu++,bav++) *buu= *bav;
    
            bs=s+avv+1;
            for(;k<= *bpos-1;k++,buu++,bs++,bav++) *bav= *buu= *bs;
    
            *buu= *btb+ *bs; avv= *bpos-1;
        }
    
        /*buu is equal to uu + *bpos*/
        for(k= *bpos;k>1;k--,buu--)
            if(*buu> *(buu-1))
            {
                tmp= *buu; *buu= *(buu-1)+1;
                *(buu-1)=tmp-1; sig= -sig;
            }
            else break;
    }
    else
    {

        if(bl==1)
        {    /*bs is free*/
            bdef=def+1;
            if(*bdef>limit){ goto aa;}
             buu=uu+1;
            for(k=1;k<= *bpos;k++,bdef++,buu++) *buu= *bdef;    
    
            sig=1; bs=uu+2;
            for(k=2;k<= *bpos-1;k++,bs++)
            {
                buu=bs;
                for(tp=k;tp>1;tp--,buu--)
                {
                    if(*buu> *(buu-1))
                    {
                        tmp= *buu; *buu= *(buu-1)+1;
                        *(buu-1)=tmp-1; sig= -sig;
                    }
                    else break;
                }
                if(tp==1 && tmp-1 >limit){ goto aa;}
            }
            sigav=sig;
    
            bav=av+1;buu=uu+1;avv= *bpos-1;
            for(k=1;k<=avv;k++,buu++,bav++) *bav= *buu;
            for(k= *bpos;k>1;k--,buu--)
                if(*buu> *(buu-1))
                {
                    tmp= *buu; *buu= *(buu-1)+1;
                    *(buu-1)=tmp-1; sig= -sig;
                }
                else break;
            if(tp==1 && tmp-1 >limit) goto aa;
        }
        else
        {
            if(*(def+1)>limit){bl=1;goto aa;}    
            sig=sigav;
    
            buu=uu+1;bav=av+1;
            for(k=1;k<=avv;k++,buu++,bav++) *buu= *bav;
    
            bs=s+avv+1;
            for(;k<= *bpos-1;k++,buu++,bs++,bav++) *bav= *buu= *bs;
    
            *buu= *btb+ *bs; avv= *bpos-1;
    
            /*buu is equal to uu + *bpos*/
            for(k= *bpos;k>1;k--,buu--)
                if(*buu> *(buu-1))
                {
                    tmp= *buu; *buu= *(buu-1)+1;
                    *(buu-1)=tmp-1; sig= -sig;
                }
                else break;

        }

    }

    bs=s+ *bpos+1; buu=uu+ *bpos+1;
    while(*bs) *buu++ = *bs++;
    *buu=0;
    tmp=buu-uu;
    if(bl==1)
    {
        buu=uu+1; bs=pcrt->tab;
        while(*buu)
        {
            if(*buu< *bs)
            {
                q=pcrt;pcrt=pcrt->suiv;
                if(pcrt==NULL)
                {
                    pcrt=(struct cel *)SYM_MALLOC(sizeof(struct cel));
                    pcrt->prec=q; pcrt->suiv=NULL;
                    q->suiv=pcrt;
                    bs=(PLETCHAR *)SYM_MALLOC(tmp*sizeof(PLETCHAR)); 
                    pcrt->tab=bs;
                    buu=uu+1;
                    while(*buu) *bs++ = *buu++;
                    *bs=0;
                    pcrt->coef= sig;
                    bl=0;goto aa;
                }/*End of if(pcrt==NULL)*/
                else
                {
                    mv=1;    /*to right*/
                    break;
                }
            }/*End of if(*buu < *bs*/
            else if (*buu > *bs)
            {
                q=pcrt; pcrt=pcrt->prec;
                mv= -1;    /*to left*/
                break;
            }
            bs++; buu++;
        }/*End of while(*buu)*/

        if(*buu==0)
        {
            lp=pcrt->coef+sig;
            if(lp==0L)
            {
                pcrt->prec->suiv=pcrt->suiv;    /*Always a preceeding term*/
                if(pcrt->suiv !=NULL) pcrt->suiv->prec=pcrt->prec;
                q=pcrt->prec;
                SYM_free((char *)pcrt->tab); 
                SYM_free((char *)pcrt);
                pcrt=q;
            }
            else pcrt->coef=lp;
            bl=0;goto aa;
        }
    }/*End of if(bl==1)*/
    else
    {
        mv=1;
        q=pcrt; pcrt=pcrt->suiv;
    }
    if(mv==1)
    {
        while(pcrt!=NULL)
        {
            buu=uu+1; bs=pcrt->tab;
            while(*bs)    /*buu==0 => *bs==0*/
            {
                if(*buu< *bs)
                {
                    q=pcrt; pcrt=pcrt->suiv; break;
                }
                else if(*buu>*bs)
                {
                    ins=(struct cel *)SYM_MALLOC(sizeof(struct cel));
                    ins->prec=q; ins->suiv=pcrt;
                    q->suiv=ins; pcrt->prec=ins;

                    bs=(PLETCHAR *)SYM_MALLOC(tmp*sizeof(PLETCHAR));ins->tab=bs;
                    buu=uu+1;
                    while(*buu) *bs++= *buu++;
                    *bs=0;
                    ins->coef=sig;
                    pcrt=ins;mv=0;bl=0;goto aa;
                }
                buu++; bs++;
            }/*End of while(*buu)*/

            if(*bs==0)
            {
                lp=pcrt->coef+sig;
                if(lp==0L)
                {
                    q->suiv=pcrt->suiv;
                    if(pcrt->suiv != NULL) pcrt->suiv->prec=q;
                    SYM_free((char *)pcrt->tab); 
                    SYM_free((char *)pcrt);
                    pcrt=q;
                }
                else pcrt->coef=lp;
                mv=0;bl=0;goto aa;
            }
        }/*End of while pcrt!=NULL*/
        if(pcrt==NULL)
        {
            pcrt=(struct cel *)SYM_MALLOC(sizeof(struct cel));
            pcrt->prec=q; pcrt->suiv=NULL;
            q->suiv=pcrt;
            bs=(PLETCHAR *)SYM_MALLOC(tmp*sizeof(PLETCHAR)); pcrt->tab=bs;
            buu=uu+1;
            while(*buu) *bs++ = *buu++;
            *bs=0;
            pcrt->coef= sig;
            mv=0;bl=0;goto aa;
        }
    }/*End of if(mv==1)*/
    
    else if(mv== -1)
    {
        while(pcrt!=NULL)
        {
            buu=uu+1; bs=pcrt->tab;
            while(*buu)
            {
                if(*buu> *bs)
                {
                    q=pcrt;pcrt=pcrt->prec;break;
                }
                else if(*buu<*bs)
                {
                    ins=(struct cel *)SYM_MALLOC(sizeof(struct cel));
                    ins->prec=pcrt; ins->suiv=q;
                    q->prec=ins; pcrt->suiv=ins;

                    bs=(PLETCHAR *)SYM_MALLOC(tmp*sizeof(PLETCHAR));
                    ins->tab=bs;
                    buu=uu+1;
                    while(*buu) *bs++= *buu++;
                    *bs=0;
                    ins->coef=sig;
                    pcrt=ins;mv=0;bl=0;goto aa;
                }
                buu++; bs++;
            }/*End of while(*buu)*/

            if(*buu==0)
            {
                lp=pcrt->coef+sig;
                if(lp==0L)
                {
                    pcrt->prec->suiv=q;
                    q->prec=pcrt->prec;
                    SYM_free((char *)pcrt->tab);
                    SYM_free((char *)pcrt);
                    pcrt=q->prec;
                }
                else pcrt->coef=lp;
                mv=0; bl=0;goto aa;
            }
        }/*End of while pcrt!=NULL*/
        /*Never pcrt==NULL => pg never in this part*/
    }/*End of if(mv==-1)*/

cc:
    if(cond==1 && plst->deb->suiv!=NULL && limit < *(s+1)+ *(psi+1)) plst->deb=plst->deb->suiv;
    SYM_free((char *)pos);
    SYM_free((char *)av);
    SYM_free((char *)s); 
    SYM_free((char *)def); 
    SYM_free((char *)tb); 
    SYM_free((char *)uu); 
    return OK;
}

static INT t_lst_SYM_new(lst,res,f)struct cel * lst; 
      OP res; OP f;
{
    INT erg = OK;
    register PLETCHAR *baf,i; 
    PLETCHAR lg;
    struct cel *q;
    OP pol,pa,v,cf;
    COP("t_lst_SYM_new(2)",res);

    if(lst==NULL) { return OK;}
    while(lst!=NULL)
    {
        pol=CALLOCOBJECT();
        v=CALLOCOBJECT();
        pa=CALLOCOBJECT();
        cf=CALLOCOBJECT();

            baf=lst->tab;

            while(*baf) baf++;
            lg=baf-lst->tab;
            m_il_v((INT)lg,v);
            baf--;

            for(i=0L;i<lg-1L;i++)
            {
                  M_I_I((INT)(*baf),S_V_I(v,i));
                  baf--;
            }
            M_I_I((INT)(*baf),S_V_I(v,i));
            b_ks_pa(VECTOR,v,pa);
        M_I_I((INT)lst->coef,cf); /* coeff must be int */
        MULT_APPLY(f,cf);
        b_sk_mo(pa,cf,pol); 
        insert_scalar_hashtable(pol,res,add_koeff,eq_monomsymfunc,hash_monompartition);
                 /* AK 031001 wrong order otherwise */
        q=lst;
        lst=lst->suiv;
        SYM_free(q->tab); 
        SYM_free((char *)q);
    }
    
    ENDR("plet.c:internal");
}

static INT l_schur_monomial_mult_new(lg,a,b,c,f) OP lg,a,b,c,f;
{
    INT i;
    register PLETCHAR *bs;
    PLETCHAR *s,*psi;
    struct lst lst;

    lst.deb=NULL;
    bs=(PLETCHAR *)SYM_MALLOC((S_PA_LI(a)+2)*sizeof(PLETCHAR));
    s=bs++;
    for(i=S_PA_LI(a)-1L;i>=0L;i--,bs++)
        *bs=(PLETCHAR)S_PA_II(a,i);
    *bs=(PLETCHAR)0;

    bs=(PLETCHAR *)SYM_MALLOC((S_PA_LI(b)+2)*sizeof(PLETCHAR));
    psi=bs++;
    for(i=S_PA_LI(b)-1L;i>=0L;i--,bs++)
        *bs=(PLETCHAR)S_PA_II(b,i);
    *bs=(PLETCHAR)0;

    muir_lim_new((PLETCHAR)S_I_I(lg),(PLETCHAR)0,s,psi,&lst);
    t_lst_SYM_new(lst.deb,c,f);
    SYM_free(psi);
    return OK;
}

