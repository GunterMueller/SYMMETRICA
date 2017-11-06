#include "def.h"
#include "macro.h"
INT tem_integer__faktor();
INT mes_integer_partition_();
INT binom_small();

static OP mip_cc=NULL;
INT mem_ende()
{
    INT erg = OK;
    if (mip_cc != NULL)
        {
        FREEALL(mip_cc);
        mip_cc = NULL;
        }
    ENDR("mem_ende");
}

INT mem_integer_partition_(a,b,c,f) OP a,b,c; OP f;
/*
a is integer
b is partition
*/
{
    INT erg = OK,i,j,m,il,jl;
    OP l,p,bn,oben,unten;
    OP mo,zi,zj,zm,ilz;

    CTO(INTEGER,"mem_integer_partition_(1)",a);
    CTO(PARTITION,"mem_integer_partition_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mem_integer_partition_(3)",c);

    if (mip_cc == NULL) {
        mip_cc = CALLOCOBJECT();
        erg += init_hashtable(mip_cc);
        }

    erg += mes_integer_partition_(a,b,mip_cc,cons_eins); /* pieri rule */
    CTO(HASHTABLE,"mem_integer_partition_(mip-cc)",mip_cc);

    bn = CALLOCOBJECT();
    oben = CALLOCOBJECT();
    unten = CALLOCOBJECT();

   
    for (il=0,ilz=S_V_S(mip_cc);il<S_V_LI(mip_cc);il++,ilz++)
            if (not EMPTYP(ilz))
                {
                for(jl=0,l=S_V_S(ilz);jl<S_V_LI(ilz);jl++,l++)
                     if (not EMPTYP(l))

    /*FORALL(l,mip_cc, */{
            
            p = S_MO_S(l);
            
            for (zi = S_PA_I(p, S_PA_LI(p) -1),i=1,
                 zj = S_PA_I(p, S_PA_LI(p) -1),j=1; i<=S_PA_LI(p); i++,zi--)
                {
                if ( S_I_I(zi) == S_I_I(zj) ) continue;
                else {  /* A */
                    /* abstieg in der partition gefunden , es sind i-j gleiche teile */
                    for (m=j,zm=S_PA_I(b,S_PA_LI(b)-j); m <= S_PA_LI(b); m++,zm--)
                        if (S_I_I(zm) < S_I_I(zj)) break;
                    /* es gibt m-j teile dieser groese schon in b */
                    /* es ist zu berechnen  binom(i-j, m-j) */
                    M_I_I(i-j,oben);
                    M_I_I(m-j,unten);
                    if ((i-j)<=12) {
                        erg += binom_small(oben,unten,bn);
                        MULT_APPLY_INTEGER(bn,S_MO_K(l));
                        C_O_K(bn,EMPTY);
                        }
                    else {
                        erg += binom(oben,unten,bn);
                        MULT_APPLY(bn,S_MO_K(l));
                        FREESELF(bn);
                        }
                    j = i;
                    zj = zi;
                    }   /* A */
                }
            /* der letzte teil, fuer die einsen */
                    {
                    /* abstieg in der partition gefunden , es sind i-j gleiche teile */
                    for (m=j,zm=S_PA_I(b,S_PA_LI(b)-j); m <= S_PA_LI(b); m++,zm--)
                        if (S_I_I(zm) < S_I_I(zj)) break;
                    /* es gibt m-j teile dieser groese schon in b */
                    /* es ist zu berechnen  binom(i-j, m-j) */
                    M_I_I(i-j,oben);
                    M_I_I(m-j,unten);
                    if ((i-j)<=12) {
                        erg += binom_small(oben,unten,bn);
                        MULT_APPLY_INTEGER(bn,S_MO_K(l));
                        C_O_K(bn,EMPTY);
                        }
                    else {
                        erg += binom(oben,unten,bn);
                        MULT_APPLY(bn,S_MO_K(l));
                        FREESELF(bn);
                        }
                    }
        
                 mo = CALLOCOBJECT();
                 SWAP(mo,l);
                 if (not EINSP(f))
                     MULT_APPLY(f,S_MO_K(mo));

                 if (S_O_K(c) == MONOMIAL)
                     INSERT_LIST(mo,c,add_koeff,comp_monommonomial);
                 else
                     {
                     C_PA_HASH(S_MO_S(mo),-1);
                     INSERT_HASHTABLE(mo,c,add_koeff,eq_monomsymfunc,hash_monompartition);
                     }
                 
                 } /*); */
              FREESELF_INTEGERVECTOR(ilz);
              C_I_I(ilz,-1);
              }
        else if (S_I_I(ilz) == -1) break;
        else { il = S_I_I(ilz)-1; ilz=S_V_I(mip_cc,il); }
    
    M_I_I(0,S_V_I(mip_cc,S_V_LI(mip_cc)));
    FREEALL(bn);
    FREEALL(oben);
    FREEALL(unten);
    /* CLEAR_HASHTABLE(mip_cc); */
/*
    for (i=0,zi = S_V_S(mip_cc);i<S_V_LI(mip_cc);i++,zi++)
        {
        if (not EMPTYP(zi) )
            FREESELF_INTEGERVECTOR(zi);
        C_I_I(zi,-1);
        }
    C_I_I(S_V_L(mip_cc),1009);
    M_I_I(0,S_V_I(mip_cc,1009));
*/
    ENDR("mem_integer_partition");
}

INT mem_integer_hashtable_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(INTEGER,"mem_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,MONOMIAL,"mem_integer_hashtable_(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mem_integer_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mem_integer_partition_);
    CTTO(HASHTABLE,MONOMIAL,"mem_integer_hashtable_(e3)",c);
    ENDR("mem_integer_hashtable_");
}

INT mem_integer__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(INTEGER,"mem_integer__(1)",a);
    CTTTO(PARTITION,HASHTABLE,MONOMIAL,"mem_integer__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mem_integer__(3)",c);

    if (S_O_K(b) == PARTITION) 
        {
        erg += mem_integer_partition_(a,b,c,f);
        goto ende;
        }
    else 
        {
        erg += mem_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    CTTO(HASHTABLE,MONOMIAL,"mem_integer__(e3)",c);
    ENDR("mem_integer__");
}

INT mem_partition__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"mem_partition__(1)",a);
    CTTTO(PARTITION,HASHTABLE,MONOMIAL,"mem_partition__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mem_partition__(3)",c);
 
    if (S_PA_LI(a) == 0)
        {
        if (S_O_K(b) == PARTITION) {
            _NULL_PARTITION_(b,c,f);
            }
        else {
            OP m;
            m = CALLOCOBJECT();
            COPY(b,m);
            if (not EINSP(f))
                {
                MULT_APPLY(f,m);
                }
            if (S_O_K(c) == MONOMIAL)
                INSERT_LIST(m,c,add_koeff,comp_monommonomial);
            else
                INSERT_HASHTABLE(m,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }
        goto ende;
        }

    else if (S_PA_LI(a) == 1)
        {
        erg += mem_integer__(S_PA_I(a,0),b,c,f);
        goto ende;
        }
    else {
        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();
 
        erg += init_hashtable(e);
        erg += tem_integer__faktor(S_PA_I(a,0),e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mem_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
 
        mult_monomial_monomial(e,b,c);
        FREEALL(e);

        }
ende:
    ENDR("mem_partition__");
}

INT mem_elmsym__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTO(ELMSYM,HASHTABLE,"mem_elmsym__(1)",a);
    CTTTO(PARTITION,HASHTABLE,MONOMIAL,"mem_elmsym__(2)",b);
    CTTO(HASHTABLE,MONOMIAL,"mem_elmsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mem_partition__);
    ENDR("mem_elmsym__");
}




INT mult_elmsym_monomial(a,b,c) OP a,b,c;
/* a is elementary,partition,integer
   b is monomial,partition
*/
/* AK 270901 */
{
    INT erg = OK;
    INT t=0;
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"mult_elmsym_monomial",a);
    CTTTO(HASHTABLE,PARTITION,MONOMIAL,"mult_elmsym_monomial",b);

    if ((S_O_K(c) != HASHTABLE) &&  (S_O_K(c) != MONOMIAL) )
        {
        CE3(a,b,c,mult_elmsym_monomial);
        }

    if (S_O_K(c) == EMPTY) 
        {
        erg += init_hashtable(c);
        t=1;
        }
    CTTO(MONOMIAL,HASHTABLE,"mult_elmsym_monomial(3)",c);

    if (S_O_K(a) == INTEGER) 
        erg += mem_integer__(a,b,c,cons_eins);
    else if (S_O_K(a) == PARTITION)
        erg += mem_partition__(a,b,c,cons_eins);
    else
        erg += mem_elmsym__(a,b,c,cons_eins);

    if (t==1) 
        erg += t_HASHTABLE_MONOMIAL(c,c);
    ENDR("mult_elmsym_monomial");
}

