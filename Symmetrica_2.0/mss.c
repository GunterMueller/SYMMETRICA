#include "def.h"
#include "macro.h"


#ifdef SCHURTRUE
#define SR_LENGTH 1000
#define SR_DEPTH 1000

static char (* ps)[SR_LENGTH] = NULL;/* permutationen */
static short (* ms)[4]   = NULL;     
/* maximal place  at 0 */
/* end of first increasing part at 1 */
/* length of the perm at 2 */
/* maximal entry as schur partition at 3 */
static short stacklevel;         /* the actuell level */
static short permlength;        /* the length of the permutation */

typedef  char axk[SR_LENGTH] ;
typedef  short axl[4] ;
static INT newtrans_main();
static INT newtrans_main_hashtable();
static INT newtrans_main_limitfunction();
static INT newtrans_main_limit_limitfunction();
static INT newtrans_nextstep();
static INT newtrans_printstack();
static INT newtrans_start();
INT newtrans_maxpart_maxlength(OP,OP,INT,INT);
INT mult_schur_schur_maxpart_maxlength(OP,OP,OP,OP,OP);

static OP newtrans_koeff = NULL;
static OP nmh_ent = NULL;

INT mss_ende()
{
    INT erg = OK;
    if (ps != NULL) { SYM_free(ps); ps = NULL; }
    if (ms != NULL) { SYM_free(ms); ms = NULL; }
    if (nmh_ent != NULL) { FREEALL(nmh_ent); nmh_ent=NULL; }
    ENDR("mss_ende");
}



static INT newtrans_main(perm,e,maxpart,maxlength)OP perm,e; INT maxpart; INT maxlength;
/* AK 020290 V1.1 AK 200891 V1.3 */
/* AK 211201 maxpart is the maximal partsize in the result, -1 if no limit */
/* AK 120603 maxlength is the maximal partlength in the result, -1 if no limit */
{
    INT erg = OK;
    short i,j;
    INT koeff=0;
    CTTTO(HASHTABLE,SCHUR,BINTREE,"newtrans_main(2)",e);
    SYMCHECK(maxpart < -1, "newtrans_main:wrong value maxpart");
    SYMCHECK(maxlength < -1, "newtrans_main:wrong value maxlength");

    if (ps == NULL) {
        ps = (axk * )  SYM_calloc(SR_DEPTH,sizeof(axk));
        if (ps == NULL) 
            return no_memory();
        }
    if (ms == NULL) {
        ms = (axl *) SYM_calloc(SR_DEPTH,sizeof(axl));
        if (ms == NULL) 
            return no_memory();
        }

    if (S_O_K(e) == HASHTABLE) {
        erg += newtrans_main_hashtable(perm,e,maxpart,maxlength);
        goto ende;
        }
    if (newtrans_koeff)
        {
        if (S_O_K(newtrans_koeff) == INTEGER)
             koeff = S_I_I(newtrans_koeff); 
        }
    else koeff = 1;


    newtrans_start(perm);
mainaa:
    if ( (maxpart >= 0) && ( maxpart < ms[stacklevel][3]))
        stacklevel--;
    else if (ms[stacklevel][1] == ms[stacklevel][0])
    /* this means it is grassmanian */
    {
           OP ent=CALLOCOBJECT(); /* eintrag */
        
           b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),ent);
           b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(ent));
           m_il_integervector((INT) ms[stacklevel][1] + 1, S_PA_S(S_MO_S(ent)));
           if (koeff != 0) M_I_I(koeff,S_MO_K(ent));
           else COPY(newtrans_koeff,S_MO_K(ent));
   
           for (i=(short)0,j=(short)0; i<= ms[stacklevel][1]; i++)
               if (  (ps[stacklevel] [i]) - i - 1 > 0 ) {
               M_I_I((INT) (ps[stacklevel] [i]) - i - (INT)1,
                   S_PA_I(S_MO_S(ent),j)); j++; }
           if (j>1)
               M_I_I((INT)j, S_PA_L(S_MO_S(ent))); /* j eingefuegt AK 170790 */
           else if (j==1) /* AK 121093 */
               /* noetig da ein vector der laenge 1 ein object ist */
               {
               i = S_PA_II(S_MO_S(ent),(INT)0);
               m_il_integervector((INT)1,S_PA_S(S_MO_S(ent)));
               M_I_I(i,S_PA_I(S_MO_S(ent),(INT)0));
               } 
           if ( (maxlength == -1)   && (maxpart == -1) )
               INSERT_SCHURMONOM_(ent,e);
           else if ( (maxlength == -1) || (MAXPARTI(S_MO_S(ent)) <=maxpart) )
               INSERT_SCHURMONOM_(ent,e);
           else if ( (maxpart == -1) || (S_PA_LI(S_MO_S(ent)) <= maxlength) )
               INSERT_SCHURMONOM_(ent,e);
           else 
               FREEALL(ent);
           stacklevel--;
    }
    else newtrans_nextstep();
    /* compute next level from last entry in stack */
    if (stacklevel != -1) goto mainaa;
ende:
    ENDR("newtrans_main");
}

static INT newtrans_main_hashtable(perm,e,maxpart,maxlength)OP perm,e; INT maxpart; INT maxlength;

{
    INT erg = OK;
    short i,j;
    INT koeff=0,k;
    OP ent;

    CTO(HASHTABLE,"newtrans_main_hashtable(2)",e);
    SYMCHECK(maxpart < -1, "newtrans_main_hashtable:wrong value maxpart");
    SYMCHECK(maxlength < -1, "newtrans_main_hashtable:wrong value maxlength");

    if (newtrans_koeff)
        {
        if (S_O_K(newtrans_koeff) == INTEGER) 
            koeff = S_I_I(newtrans_koeff); 
        }
    else koeff = 1;

    if (nmh_ent == NULL) {
        nmh_ent = CALLOCOBJECT();
        b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),nmh_ent);
        b_ks_pa(VECTOR,CALLOCOBJECT(),S_MO_S(nmh_ent));
        m_il_integervector(SR_LENGTH,S_PA_S(S_MO_S(nmh_ent)));
        }

    ent = nmh_ent;

    newtrans_start(perm);
mainaa:
    if ( (maxpart >= 0) && ( maxpart < ms[stacklevel][3]))
        stacklevel--;
    else if (ms[stacklevel][1] == ms[stacklevel][0])
    /* this means it is grassmanian */
    {
        INT w=0;
        M_I_I((INT) ms[stacklevel][1] + 1, S_PA_L(S_MO_S(ent)));
        FREESELF(S_MO_K(ent));
        if (koeff != 0)
            M_I_I(koeff,S_MO_K(ent));
        else
            COPY(newtrans_koeff,S_MO_K(ent));
        for (i=(short)0,j=(short)0; i<= ms[stacklevel][1]; i++)
            if (  (ps[stacklevel] [i]) - i - 1 > 0 ) {
                M_I_I((INT) (ps[stacklevel] [i]) - i - (INT)1,
                S_PA_I(S_MO_S(ent),j)); 
                w += S_PA_II(S_MO_S(ent),j);
                j++; 
                }
        if (j>1)
            M_I_I((INT)j, S_PA_L(S_MO_S(ent))); /* j eingefuegt AK 170790 */
        else if (j==1) /* AK 121093 */
            /* noetig da ein vector der laenge 1 ein object ist */
            {
            i = S_PA_II(S_MO_S(ent),(INT)0);
            M_I_I(1,S_PA_L(S_MO_S(ent)));
            M_I_I(i,S_PA_I(S_MO_S(ent),(INT)0));
            } 

        if (
           ( (maxpart == -1) || (MAXPARTI(S_MO_S(ent)) <=maxpart) )
           &&
           ( (maxlength == -1) || (S_PA_LI(S_MO_S(ent)) <=maxlength) )
           )
        {
        INT eq_monomsymfunchash();
   
        HASH_INTEGERVECTOR(S_PA_S(S_MO_S(ent)),k);
        C_PA_HASH(S_MO_S(ent),k);
        if ( w < 70 ) 
            add_apply_hashtable(ent,e,add_koeff,eq_monomsymfunchash,hash_monompartition);
        else
            add_apply_hashtable(ent,e,add_koeff,eq_monomsymfunc,hash_monompartition);
        }
        stacklevel--;
    }
    else newtrans_nextstep();
    /* compute next level from last entry in stack */
    if (stacklevel != -1) goto mainaa;

    ENDR("newtrans_main_hashtable");
}



static INT newtrans_nextstep() /* AK 200891 V1.3 */
{

    short i,j;
    short maxplace =  ms [stacklevel][0];
    /* the position before the last decrease */
    char maxentry = ps  [stacklevel][ms [stacklevel][0]];
    /* this is the entry at the maximal place */
    char rightlessvalue,h;
    /* this is the value on this place */
    char minimalleftvalue;
    /* the minimal value to the left which is allowed
    to be exchanged with entry on the maxplace */
    short startloop;
    /* first we look whether we could reduce the length of the perm */
    char *pss = ps[stacklevel];
    char *pssp;
    short *mss = ms[stacklevel];

    for (i=mss[2] -1; i>0; i--)
        if (pss[i] == (char)i+1) mss[2]--;
        else break;
    /* now we have reduced the length of the alphabet */

    /* now we compute these rightvalues */
    for (i=mss[2] - 1; i> 0 ; i--)
        if ( pss[i] < maxentry) break;
    /* i is now the required place */
    rightlessvalue =  pss[i];
    /* now we have to exchange */
    pss[i] =  maxentry;
    pss[maxplace] =  rightlessvalue;

    /* you must look whether rightlessvalue == 1
because this means you have to enlarge the permutation */

    startloop = maxplace-1;
    if (rightlessvalue == 1)
    {
        mss[2]++;
        for (i=mss[2]-1; i>0 ; i--)
            pss[i]=pss[i-1]+1;
        pss[0]=(char)1;
        mss[0]++;
        mss[1]++;
        rightlessvalue=2;
        maxplace++;
        startloop=0;
    }

    /* now we have to compute all possible changes to the left */
    minimalleftvalue = 0;
    for (pssp=pss+startloop,i=startloop; i>=0; i--,pssp--)
    {
        /* if (( pss[i] < rightlessvalue)
            && ( pss[i] > minimalleftvalue)) */
        if (( *pssp < rightlessvalue)
            && ( *pssp > minimalleftvalue))
        {
            /* now these things have to be copied and to be exchanged */
            if (stacklevel+1 == SR_DEPTH)
            /* this means the stack is to small */
                error("newtrans:stackoverflow");/* AK 121192 */
            /* you generate a copy of the upper stack-entry */

            if (i>0)
            {
                memcpy(    ps[stacklevel+1], pss, (int)(mss[2]));
                memcpy(    ms[stacklevel+1], mss,8); 
            }
            /* you got a copy */


            pss[maxplace]=pss[i];
            pss[i]=rightlessvalue;
            minimalleftvalue = pss[maxplace];


/*
            pss[maxplace] = *pssp;
            *pssp = rightlessvalue;
            minimalleftvalue  =  pss[maxplace];
*/

            /* new value for maximal schur part *//* AK 211201 */
            if ((h=(rightlessvalue - i - 1)) > mss[3]) 
                mss[3] = h;

            /* we have now to compute the new values for minstack and ms */
            for (j=mss[1]+1;j<mss[2];j++)
                if (pss[j] < pss[j-1])
                    break;
            mss[1] = j-1;
            /* this is the new value of the minstackentry */

            for (j=mss[0];j>=0;j--)
                if (pss[j] > pss[j+1])
                    break;
            mss[0] = j;
            /* this is the new value of the msentry */
            if (minimalleftvalue == (rightlessvalue - 1)) return(0);
            else {
                 stacklevel++;
                 pss=ps[stacklevel];
                 mss=ms[stacklevel];
                 }
        }
        if ((i==0)&&(minimalleftvalue==0))
        /* you have to enlarge the permutation */
        {
            mss[2]++;
            for (i=mss[2]-1; i>0 ; i--)
                pss[i]=pss[i-1]+1;
            pss[0]=(char)1;
            mss[1]++;
            mss[0]++;
            rightlessvalue++;
            maxplace++;
            pss[maxplace]=pss[i];
            pss[i]=rightlessvalue;
            minimalleftvalue = pss[maxplace];
            /* we have now to compute the new values for
        minstack and ms */
            for (j=mss[1]+1;j<mss[2];j++)
                if (pss[j] < pss[j-1])
                    break;
            mss[1] = j-1;
            /* this is the new value of the minstackentry */

            for (j=mss[0];j>=0;j--)
                if (pss[j] > pss[j+1])
                    break;
            mss[0] = j;
            /* this is the new value of the msentry */
            return(0);
        }
    }
    stacklevel--;
    return OK;
}

#ifdef UNDEF
static INT newtrans_printstack()
/* AK 200891 V1.3 */
{
    /* the routine prints the stack */
    short i,j;
    for (i=0;i<=stacklevel;i++)
    {
        char *pss = ps[i];
        for (j=0;j<ms[i][2];j++)
            {
            printf(" %d ",(short)pss[j]);
            }
        printf(":%d %d %d %d\n",ms[i][0],ms[i][1],ms[i][2],ms[i][3]);
    };
    printf("-------------------------------------------\n");
    return(OK);
}
#endif



static INT newtrans_start(perm) OP perm; /* AK 221289 V1.1 AK 200891 V1.3 */
{
    short i;
    INT erg = OK;

    permlength = S_P_LI(perm);
    if (permlength > SR_LENGTH)
    /* the error condition the perm do not fit into the stack */
    {
        fprintln(stderr,perm);
        fprintf(stderr,
    "please enter a permutation of a length <= %d\n",SR_LENGTH);
        erg += error("newtrans_start:internal error");
        goto endr_ende;
    }
    ms[0][2]=permlength;
    ms[0][3]=0;

    for (i=0; i<permlength ; i++)
    {
        ps  [0][i] = (char)S_P_II(perm,i);
        if ((S_P_II(perm,i) - i - 1) > ms[0][3]) 
            ms[0][3]=(S_P_II(perm,i) - i - 1);
    }
    /* now we are looking for the first and the last decrease */
    for (i=1; i<permlength ; i++)
        if (ps [0][i] < ps [0][i-1]) break;
    /* now i is the index of the first decrease */
    ms [0][1] = i-1;


    for (i=permlength-2 ;i>=0; i--)
        if (ps [0][i] > ps [0][i+1]) break;
    /* now i+1 is the index of the last decrease */
    ms [0][0] = i;

    stacklevel=0;
    ENDR("newtrans_start:internal function");
}

INT newtrans_lehmer(perm,c) OP perm,c;
/* perm und c may be equal */
{
    OP d;
    INT erg = OK;
    CTTO(VECTOR,INTEGERVECTOR,"newtrans_lehmer(1)",perm);
    erg += lehmercode(perm,d = CALLOCOBJECT());
    erg += newtrans_maxpart_maxlength(d,c,-1,-1);
    FREEALL(d);
    ENDR("newtrans_lehmer");
}

INT newtrans_eins(c) OP c;
/* AK 211201 */
{
    INT erg = OK;
    OP m;
    CTTTO(SCHUR,HASHTABLE,BINTREE,"newtrans_eins(1)",c);
    m  = CALLOCOBJECT();
    erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),m);
    erg += first_partition(cons_null,S_MO_S(m));
    if (newtrans_koeff != NULL)
        COPY(newtrans_koeff,S_MO_K(m));
    else
        M_I_I(1,S_MO_K(m));
    INSERT_SCHURMONOM_(m,c);
    ENDR("newtrans_eins");
}


INT newtrans(perm,c) OP perm,c;
/* AK 221289 V1.1 */ /* AK 130891 V1.3 */
/* AK 180598 V2.0 */
/* perm and c may be equal */
/* is c a HASHTABLE,BINTREE,SCHUR it will be used for inserting */
/* die globale variable newtrans_koeff may be used for faktor */
    { 
    INT erg = OK;
    CTO(PERMUTATION,"newtrans(1)",perm);
    newtrans_maxpart_maxlength(perm,c,-1,-1);
    CTTTO(SCHUR,HASHTABLE,BINTREE,"newtrans(res)",c);
    ENDR("newtrans");
    }

INT newtrans_maxpart(perm,e,maxpart) OP perm,e; INT maxpart;
{
    return newtrans_maxpart_maxlength(perm,e,maxpart,-1);
}

INT newtrans_maxpart_maxlength(perm,e,maxpart,maxlength) OP perm,e; INT maxpart;INT maxlength;
/* AK 211201
   there is a limit on the maximal size of the parts in the result
   -1 is no limit */
/* AK 120603
   there is a limit on the maximal length of the parts in the result
   -1 is no limit */
{
    INT erg = OK;
    CTO(PERMUTATION,"newtrans_maxpart_maxlength(1)",perm);
    SYMCHECK(maxpart < -1,"newtrans_maxpart_maxlength:wrong value for maxpart");
    SYMCHECK(maxlength < -1,"newtrans_maxpart_maxlength:wrong value for maxlength");
    if (
        (S_O_K(e) == BINTREE) ||
        (S_O_K(e) == SCHUR) ||
        (S_O_K(e) == HASHTABLE)
       )
        {
        if (einsp_permutation(perm))
            {
            erg += newtrans_eins(e);
            goto ende;
            }
        else {
            erg += newtrans_main(perm,e,maxpart,maxlength);
            goto ende;
            }
        }
    else {
        if (einsp_permutation(perm))
            {
            erg += m_scalar_schur(cons_eins,e);
            if (newtrans_koeff != NULL)
                erg += copy(newtrans_koeff,S_S_K(e));
            goto ende;
            }
        SYMCHECK(perm == e, "newtrans_maxpart:identical parameters");
        erg += init(BINTREE,e);
        erg += newtrans_main(perm,e,maxpart,maxlength);
        erg += t_BINTREE_SCHUR(e,e);
        goto ende;
        }
       
ende:
    CTTTO(SCHUR,HASHTABLE,BINTREE,"newtrans(res)",e);
    ENDR("newtrans_maxpart");
}

INT newtrans_limit_limitfunction(perm,c,d,f,limit) OP perm,c,d,limit; INT (*f)();
/* AK 221289 V1.1 */ /* AK 200891 V1.3 */
{ 
    INT erg = OK;
    CTO(PERMUTATION,"newtrans_limit_limitfunction(1)",perm);
    erg += init(BINTREE,c);
    erg += newtrans_main_limit_limitfunction(perm,c,d,f,limit); 
    erg += t_BINTREE_SCHUR(c,c);
    ENDR("newtrans_limit_limitfunction");
}


INT newtrans_limitfunction(perm,c,f,limit) OP perm,c,limit; INT (*f)();
/* AK 221289 V1.1 */ /* AK 200891 V1.3 */
{ 
    INT erg = OK;
    CTO(PERMUTATION,"newtrans_limitfunction(1)",perm);
    erg += init(BINTREE,c);
    erg += newtrans_main_limitfunction(perm,c,f,limit); 
    erg += t_BINTREE_SCHUR(c,c);
    ENDR("newtrans_limitfunction");
}


static INT newtrans_main_limit_limitfunction(perm,c,d,f,limit) OP d,perm,c,limit;
    INT (*f)();
/* d is a limit on the length of the partitions */
/* AK 221289 V1.1 */ /* AK 200891 V1.3 */
{
    short i,j;

    if (ps == NULL) {
        ps= (axk * ) SYM_calloc( SR_DEPTH,sizeof(axk));
        if (ps== NULL) 
            return no_memory();
        }
    if (ms == NULL) {
        ms = (axl *) SYM_calloc( SR_DEPTH,sizeof(axl));
        if (ms == NULL) 
            return no_memory();
        }
    newtrans_start(perm);
mainaa:
    if (ms[stacklevel][1] == ms[stacklevel][0])
    /* this means it is grassmanian */
    {
        OP ent; /* eintrag */
        if ((INT)ms[stacklevel][1] + 1 <= S_I_I(d))
                {
                        /* partition ist kurz genug */
        ent = callocobject();
        init(MONOM,ent);
                init(PARTITION,S_MO_S(ent));
                m_il_integervector((INT) ms[stacklevel][1] + 1, S_PA_S(S_MO_S(ent)));
                M_I_I((INT)1,S_MO_K(ent));
                for (i=(short)0,j=(short)0; i<= ms[stacklevel][1]; i++)
                    if (  (ps[stacklevel] [i]) - i - 1 > 0 ) {
                        M_I_I((INT) (ps[stacklevel] [i]) - i - (INT)1,
                            S_PA_I(S_MO_S(ent),j)); j++; }
                if (j>1)
            M_I_I((INT)j, S_PA_L(S_MO_S(ent)));
                else if (j==1) /* AK 121093 */
                        {
                        i = S_PA_II(S_MO_S(ent),(INT)0);
                        m_il_integervector((INT)1,S_PA_S(S_MO_S(ent)));
                        M_I_I(i,S_PA_I(S_MO_S(ent),(INT)0));
                        }

        if ((*f)(S_MO_S(ent),limit) == TRUE)
        {
            insert(ent,c, add_koeff,comp_monomvector_monomvector);
        }
        else freeall(ent);
         }
        stacklevel--;
    }
    else newtrans_nextstep();
    /* compute next level from last entry in stack */
    if (stacklevel != -1) goto mainaa;
    return(OK);
}


static INT newtrans_main_limitfunction(perm,c,f,limit) OP perm,c,limit;
    INT (*f)();
/* limit is a limit on the length of the partitions */
/* AK 221289 V1.1 */ /* AK 200891 V1.3 */
{
    short i,j;

    if (ps == NULL) {
        ps= (axk * ) SYM_calloc( SR_DEPTH,sizeof(axk));
        if (ps== NULL) 
            return no_memory();
        }
    if (ms == NULL) {
        ms = (axl *) SYM_calloc( SR_DEPTH,sizeof(axl));
        if (ms == NULL) 
            return no_memory();
        }
    newtrans_start(perm);
mainaa:
    if (ms[stacklevel][1] == ms[stacklevel][0])
    /* this means it is grassmanian */
    {
        OP ent; /* eintrag */
        ent = callocobject();
        init(MONOM,ent);
        init(PARTITION,S_MO_S(ent));
        m_il_integervector((INT) ms[stacklevel][1] + 1, S_PA_S(S_MO_S(ent)));
        M_I_I((INT)1,S_MO_K(ent));
        for (i=(short)0,j=(short)0; i<= ms[stacklevel][1]; i++)
            if (  (ps[stacklevel] [i]) - i - 1 > 0 ) {
                M_I_I((INT) (ps[stacklevel] [i]) - i - (INT)1,
                    S_PA_I(S_MO_S(ent),j)); j++; }
        if (j>1)
            M_I_I((INT)j, S_PA_L(S_MO_S(ent)));
        else if (j==1) /* AK 121093 */
            {
            i = S_PA_II(S_MO_S(ent),(INT)0);
            m_il_integervector(1,S_PA_S(S_MO_S(ent)));
            M_I_I(i,S_PA_I(S_MO_S(ent),(INT)0));
            }

        if ((*f)(S_MO_S(ent),limit) == TRUE)
            insert(ent,c, add_koeff,comp_monomschur);
        else freeall(ent);
        
        stacklevel--;
    }
    else newtrans_nextstep();
    /* compute next level from last entry in stack */
    if (stacklevel != -1) goto mainaa;
    return(OK);
}



INT mss_partition_partition_maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
{
    INT erg = OK;
    OP d;
    CTO(PARTITION,"mss_partition_partition_maxpart_maxlength(1)",a);
    CTO(PARTITION,"mss_partition_partition_maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_partition_partition_maxpart_maxlength(3)",c);
    SYMCHECK(m < -1,"mss_partition_partition_maxpart_maxlength:maxpart < -1");
    SYMCHECK(l < -1,"mss_partition_partition_maxpart_maxlength:maxlength < -1");

    d=CALLOCOBJECT();
    newtrans_koeff=f;
    erg += m_part_part_perm(a,b,d);
    erg += newtrans_maxpart_maxlength(d,c,m,l);
    newtrans_koeff=NULL;
    FREEALL(d); 

    CTTO(HASHTABLE,SCHUR,"mss_partition_partition_maxpart_maxlength(3-end)",c);
    ENDR("mss_partition_partition_maxpart_maxlength");
}
INT mss_partition_partition_(a,b,c,f) OP a,b,c,f; { return mss_partition_partition_maxpart_maxlength(a,b,c,f,-1,-1); }

INT mss_partition__maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
{
    INT erg = OK;
    CTO(PARTITION,"mss_partition__maxpart_maxlength(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_partition__maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_partition__maxpart_maxlength(3)",c);
    SYMCHECK(m < -1,"mss_partition__maxpart_maxlength:maxpart < -1");
    if (S_O_K(b) == PARTITION)
        {
        erg += mss_partition_partition_maxpart_maxlength(a,b,c,f,m,l);
        goto ende; 
        }
    else if (S_O_K(b) == HASHTABLE)
        {
        M3_FORALL_MONOMIALS_IN_B(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
        goto ende; 
        }
    else if (S_O_K(b) == SCHUR)
        {
        M3_FORALL_MONOMIALS_IN_B(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
        goto ende; 
        }
    else{
        WTO("mss_partition__maxpart_maxlength(2)",b);
        goto ende;
        }
ende:
    ENDR("mss_partition__maxpart_maxlength");
}

INT mss_partition__(a,b,c,f) OP a,b,c,f; 
{ 
    return mss_partition__maxpart_maxlength(a,b,c,f,-1,-1); 
}


INT mss_schur__maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
{
    INT erg = OK;
    CTTO(SCHUR,HASHTABLE,"mss_schur__maxpart_maxlength(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_schur__maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_schur__maxpart_maxlength(3)",c);
    SYMCHECK(m < -1,"mss_schur__maxpart:maxpart < -1");
    SYMCHECK(l < -1,"mss_schur__maxpart:maxlength < -1");

    if (S_O_K(b) == PARTITION)
        {
        M3_FORALL_MONOMIALS_IN_A(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
        goto ende;
        }
    else if (S_O_K(b) == HASHTABLE)
        {
        M3_FORALL_MONOMIALS_IN_AB(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
        goto ende;
        }
    else if (S_O_K(b) == SCHUR)
        {
        M3_FORALL_MONOMIALS_IN_AB(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
        goto ende;
        }
    else{
        WTO("mss_schur__maxpart_maxlength(2)",b);
        goto ende;
        }

ende:
    ENDR("mss_schur__maxpart_maxlength");
}

INT mss_schur__(a,b,c,f) OP a,b,c,f; 
{ 
    return mss_schur__maxpart_maxlength(a,b,c,f,-1,-1); 
}

INT mss_hashtable__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTO(SCHUR,HASHTABLE,"mss_hashtable__(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_hashtable__(3)",c);
    erg += mss_schur__(a,b,c,f);

    ENDR("mss_hashtable__");
}

INT mss_hashtable_hashtable_(a,b,c,f) OP a,b,c,f;
/* AK 071201 */
/* from pss_..*/
{
    INT erg = OK;
    CTTO(SCHUR,HASHTABLE,"mss_hashtable_hashtable_(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_hashtable_hashtable_(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_hashtable_hashtable_(3)",c);
    M_FORALL_MONOMIALS_IN_AB(a,b,c,f,mss_partition_partition_);

    ENDR("mss_hashtable_hashtable_");
}
INT mss_hashtable__maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
{
    INT erg = OK;
    CTTO(SCHUR,HASHTABLE,"mss_hashtable__maxpart_maxlength(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_hashtable__maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_hashtable__maxpart_maxlength(3)",c);
    erg += mss_schur__maxpart_maxlength(a,b,c,f,m,l);
 
    ENDR("mss_hashtable__maxpart_maxlength");
}
 
INT mss_hashtable_hashtable_maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
/* AK 071201 */
{
    INT erg = OK;
    CTTO(SCHUR,HASHTABLE,"mss_hashtable_hashtable_maxpart_maxlength(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss_hashtable_hashtable_maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss_hashtable_hashtable_maxpart_maxlength(3)",c);
    M3_FORALL_MONOMIALS_IN_AB(a,b,c,f,m,l,mss_partition_partition_maxpart_maxlength);
 
    ENDR("mss_hashtable_hashtable_maxpart_maxlength");
}




INT mss___maxpart_maxlength(a,b,c,f,m,l) OP a,b,c,f; INT m,l;
{
    INT erg = OK;
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss___maxpart_maxlength(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mss___maxpart_maxlength(2)",b);
    CTTO(HASHTABLE,SCHUR,"mss___maxpart_maxlength(3)",c);
    SYMCHECK(m < -1,"mss___maxpart_maxlength:maxpart < -1");
    SYMCHECK(l < -1,"mss___maxpart_maxlength:maxlength < -1");
    if (S_O_K(a) == PARTITION) 
        {
        erg += mss_partition__maxpart_maxlength(a,b,c,f,m,l);
        goto ende;
        }
    else if (S_O_K(a) == SCHUR) 
        {
        erg += mss_schur__maxpart_maxlength(a,b,c,f,m,l);
        goto ende;
        }
    else if (S_O_K(a) == HASHTABLE) 
        {
        erg += mss_hashtable__maxpart_maxlength(a,b,c,f,m,l);
        goto ende;
        }
    else{
        WTO("mss___maxpart_maxlength(1)",a);
        goto ende;
        }
ende:
    ENDR("mss___maxpart_maxlength");
}

INT mss___(a,b,c,f) OP a,b,c,f; 
{ 
    return  mss___maxpart_maxlength(a,b,c,f,-1,-1); 
}

INT mult_schur_schur(a,b,c) OP a, b, c;
/* 221086 */ /* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 050891 V1.3 */
/* AK 170298 V2.0 */
{
    INT erg = OK;
    INT t=0;
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_schur_schur(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_schur_schur(2)",b);
    CTTTO(EMPTY,SCHUR,HASHTABLE,"mult_schur_schur(3)",c);

    if (S_O_K(c) == EMPTY)  
        {
        t=1; init_hashtable(c);
        }
    erg += mss___maxpart_maxlength(a,b,c,cons_eins,-1,-1);
    if (t == 1) { erg += t_HASHTABLE_SCHUR(c,c); }

    CTTO(SCHUR,HASHTABLE,"mult_schur_schur(3-end)",c);
    ENDR("mult_schur_schur");
}

INT mult_schur_schur_maxlength(a,b,c,l) OP a, b, c,l;
{
    return mult_schur_schur_maxpart_maxlength(a,b,c,cons_negeins,l);
}

INT mult_schur_schur_maxpart_maxlength(a,b,c,m,l) OP a, b, c,m,l;
/* 221086 */ /* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 050891 V1.3 */
/* AK 170298 V2.0 */
/* if c is HASHTABLE or SCHUR the result will be added */
{
    INT erg = OK;
    INT t=0;
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_schur_schur_maxpart_maxlength(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_schur_schur_maxpart_maxlength(2)",b);
    CTTTO(EMPTY,SCHUR,HASHTABLE,"mult_schur_schur_maxpart_maxlength(3)",c);
    CTO(INTEGER,"mult_schur_schur_maxpart_maxlength(4)",m);
    CTO(INTEGER,"mult_schur_schur_maxpart_maxlength(5)",l);
    SYMCHECK((S_I_I(m) < -1),"mult_schur_schur_maxpart_maxlength:maxpart < -1");
    SYMCHECK((S_I_I(l) < -1),"mult_schur_schur_maxpart_maxlength:maxlength < -1");
 
    if (S_O_K(c) == EMPTY)
        {
        t=1; init_hashtable(c);
        }
    erg += mss___maxpart_maxlength(a,b,c,cons_eins,S_I_I(m),S_I_I(l));
    if (t == 1) { erg += t_HASHTABLE_SCHUR(c,c); }
 
    CTTO(SCHUR,HASHTABLE,"mult_schur_schur(3-end)",c);
    ENDR("mult_schur_schur");
}



INT m_part_part_perm(a,b,c) OP a,b,c;
/* input: two partition objects
   output: starting permutation for transition for multiplication */
/* AK 050988 */
/* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK 060498 V2.0 */
/* a,b,c may be equal */
{
    OP d;
    OP z;
    INT i,j,erg = OK;
    CTO(PARTITION,"m_part_part_perm(1)",a);
    CTO(PARTITION,"m_part_part_perm(2)",b);

    NEW_VECTOR(d, S_PA_LI(a) + S_PA_LI(b) + MAXPARTI(a) + MAXPARTI(b) );
    z = S_V_S(d);
    for (i=(INT)0; i< S_PA_LI(a); i++,z++) M_I_I(S_PA_II(a,i),z);
    for (j=(INT)0 ; j < MAXPARTI(a); j++,i++,z++) M_I_I((INT)0,z);
    for (j=(INT)0; j < S_PA_LI(b); j++,i++,z++) M_I_I(S_PA_II(b,j),z);
    for (j=(INT)0 ; j< MAXPARTI(b); j++,i++,z++) M_I_I((INT)0,z);
    erg += lehmercode_vector(d,c);
    erg += freeall(d);
    ENDR("m_part_part_perm");
}


INT outerproduct_schur(a,b,c) OP a, b, c;
/* AK 071086 */ /* AK 110789 V1.0 */ /* AK 181289 V1.1 */
/* AK 050891 V1.3 */
/* a:  PARTITION b: PARTITION 
c: BINTREE,SCHUR,HASHTABLE result will be inserted */
{
    INT erg = OK;
    OP   d;
    CTO(PARTITION,"outerproduct_schur(1)",a);
    CTO(PARTITION,"outerproduct_schur(2)",b);
    CTTTTO(EMPTY,HASHTABLE,SCHUR,BINTREE,"outerproduct_schur(3)",c);
   
    if (S_O_K(c) == EMPTY) init(SCHUR,c); /* AK 250402 */


    d=CALLOCOBJECT();
    erg += m_part_part_perm(a,b,d);
    erg += newtrans_maxpart_maxlength(d,c,-1,-1);
    FREEALL(d); 

    ENDR("outerproduct_schur");
}


INT m_perm_schur(a,b) OP a,b;
/* AK 270788 */
/* zerlegt das Schubertpolynom X_a  in eine Summe
von Schurpolynomen */
/* AK 110789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
{
    INT erg = OK;
    CTO(PERMUTATION,"m_perm_schur",a);
    erg += newtrans_maxpart_maxlength(a,b,-1,-1); 
    ENDR("m_perm_schur");
}

INT outerproduct_schur_limit_limitfunction(a,b,c,k,f,l) OP k, a, b, c,l;
    INT (*f)();
/* 071086 */ /* a b sind partitionen */ /* AK 071189  */
/* AK 181289 V1.1 */ /* AK 180391 V1.2 */ /* AK 200891 V1.3 */
/* k ist ein limit fuer die groesse */
{
    OP   d;
    INT erg = OK;
    CTO(PARTITION,"outerproduct_schur_limit_limitfunction(1)",a);
    CTO(PARTITION,"outerproduct_schur_limit_limitfunction(2)",b);
    d=callocobject();
    if (not EMPTYP(c)) 
        erg += freeself(c);
    erg += m_part_part_perm(a,b,d);
    erg += newtrans_limit_limitfunction(d,c,k,f,l);
    erg += freeall(d);
    ENDR("outerproduct_schur_limit_limitfunction");
}

INT outerproduct_schur_limitfunction(a,b,c,f,l) OP a, b, c,l;
    INT (*f)();
/* 071086 */ /* a b sind partitionen */ /* AK 071189  */
/* AK 181289 V1.1 */ /* AK 180391 V1.2 */ /* AK 200891 V1.3 */
{
    OP   d;
    INT erg = OK;
    CTO(PARTITION,"outerproduct_schur_limitfunction(1)",a);
    CTO(PARTITION,"outerproduct_schur_limitfunction(2)",b);
    d=callocobject();
    if (not EMPTYP(c)) 
        erg += freeself(c);
    erg += m_part_part_perm(a,b,d);
    erg += newtrans_limitfunction(d,c,f,l);
    erg += freeall(d);
    ENDR("outerproduct_schur_limitfunction");
}

INT outerproduct_schur_limit(a,b,c,l) OP a, b, c,l;
/* 071086 */ /* a b sind partitionen */ /* AK 071189  */
/* AK 181289 V1.1 */ /* AK 180391 V1.2 */ /* AK 200891 V1.3 */
{
    OP   d=callocobject();
    if (not EMPTYP(c)) 
        freeself(c);
    m_part_part_perm(a,b,d);
    newtrans_limitfunction(d,c,neqparts_partition,l);
    freeall(d);
    return(OK);
}





#ifdef SKEWPARTTRUE

INT m_skewpart_skewperm(a,b) OP a,b;
/* AK 221289 V1.1 */ /* AK 010791 V1.2 */
/* es wird die permutation fuer die berechnung der skew schur funktion
berechnet */
/* vgl. m_part_part_perm() */
/* AK 130891 V1.3 */
/* a and b may be equal */
{
    OP d ; /* d wird der code vector */
    INT k,i,j,h;
    INT lg = S_SPA_GLI(a);
    INT lk = S_SPA_KLI(a); /* die laengen der beiden partitionen */
    INT erg = OK;
    CTO(SKEWPARTITION,"m_skewpart_skewperm(1)",a);

    d = CALLOCOBJECT();

    for (i=0,j=0;i<lk;i++) j += S_SPA_KII(a,i); /* AK 121101 */
    /* is the weight of the smaller partition */
    k = S_PA_II(S_SPA_G(a),lg-(INT)1);
    /* k ist der letzte eintrag in der groesseren partition */
    erg += m_il_v(j+ k + S_PA_LI(S_SPA_G(a)),d);

    for (i=(INT)0;i<lg-lk;i++) M_I_I(S_SPA_GII(a,i),S_V_I(d,i));
    /* zuerst werden die teile aus der grossen partition kopiert */
    h = i; /* h ist laufindex durch vector */
    /* i ist laufindex durch grosse partition j durch kleine */
    for (j=(INT)0;j<lk;j++,i++,h++)
    {
        if (j==(INT)0) /* error in version < 010791 */
            for (k=(INT)0;k<S_SPA_KII(a,j);k++,h++)
                M_I_I((INT)0,S_V_I(d,h));
        else
            for (k=(INT)0;k<S_SPA_KII(a,j)-S_SPA_KII(a,j-(INT)1);k++,h++)
                M_I_I((INT)0,S_V_I(d,h));
        M_I_I(S_SPA_GII(a,i)-S_SPA_KII(a,j),S_V_I(d,h));
    }
    for (;h<S_V_LI(d);h++) 
        M_I_I((INT)0,S_V_I(d,h));
    erg += lehmercode_vector(d,b);
    FREEALL(d);
    ENDR("m_skewpart_skewperm");
}

static OP part_part_skewschur_koeff=NULL;
INT schur_part_skewschur(a,b,c) OP a,b,c;
/* AK 140199 */
/* input SCHUR or HASHTABLE object a,
         PARTITION object b
   or    INTEGER object b
   result is the skew schur function a/b 
         this is a object of the same type as a, so
         SCHUR or HASHTABLE.
   if the parameter c for the result is a SCHUR or HASHTABLE the result will
   be inserted. 
   if not it is initialised at the beginning
*/
{
    INT erg = OK,t=0;
    OP z;
    CTTO(HASHTABLE,SCHUR,"schur_part_skewschur(1)",a);
    CTTO(INTEGER,PARTITION,"schur_part_skewschur(2)",b);

    if (S_O_K(b) == INTEGER) {
            OP d = CALLOCOBJECT();
            erg += m_i_pa(b,d);
            erg += schur_part_skewschur(a,d,c);
            FREEALL(d);
            goto ende;
            }

    if (
        (S_O_K(c) != HASHTABLE) &&
        (S_O_K(c) != SCHUR)
       )
        CE3(a,b,c,schur_part_skewschur);

    CTTTO(HASHTABLE,SCHUR,EMPTY,"schur_part_skewschur(3)",c);
    if (S_O_K(c) == EMPTY) {
        if (S_O_K(a) == SCHUR) t=1;
        init_hashtable(c);
        }
    
    FORALL(z,a,{
            part_part_skewschur_koeff=S_MO_K(z);
            erg += part_part_skewschur(S_MO_S(z),b,c);
            part_part_skewschur_koeff=NULL;
            });

    if (t==1) t_HASHTABLE_SCHUR(c,c);
ende:
    CTTO(HASHTABLE,SCHUR,"schur_part_skewschur(res)",c);
    ENDR("schur_part_skewschur");
}


INT part_part_skewschur(a,b,c) OP a,b,c;
/* AK 221289 V1.1 */ /* AK 010791 V1.2 */
/* a ist die groessere partition */
/* AK 130891 V1.3 */
/* AK 170298 V2.0 */
/* input PARTITION object a
         PARTITION object b
   output c : there are four posibilities
              c is empty object at the beginning --> it will become schur object
              c is schur object -> result will inserted into c
              c is hashtable object -> result will be inserted
              c is an other object, it will become schur object

   the result is the expansion of the skew schur function a/b in the basis of
   schur functions

   the global object part_part_skewschur_koeff may be used as a faktor to be inserted
*/
{
    OP d,e;
    INT i,j,t=0;
    INT erg = OK;
 
    CTO(PARTITION,"part_part_skewschur(1)",a);
    CTO(PARTITION,"part_part_skewschur(2)",b);

    if (
        (S_O_K(c) != HASHTABLE) && 
        (S_O_K(c) != SCHUR)
       )
        CE3(a,b,c,part_part_skewschur);

    CTTTO(EMPTY,SCHUR,HASHTABLE,"part_part_skewschur(3)",c);


    

    i = S_PA_LI(a)-1;
    j = S_PA_LI(b)-1;
    if (j > i) {
            /* result is 0 */
            if (S_O_K(c)==EMPTY) init_schur(c);
            goto ende;
            }
    for(;j>=0;j--,i--)
        if (S_PA_II(a,i) < S_PA_II(b,j)) 
            {
            /* result is 0 */
            if (S_O_K(c)==EMPTY) init_schur(c);
            goto ende;
            }
    /* zuerst test ob b kleiner a */
    /* falls nicht ist das ergebnis ein leeres schur object */

    if (S_O_K(c) == EMPTY) {
        erg += init_hashtable(c);
        t = 1;
        }


    d = CALLOCOBJECT();
    e = CALLOCOBJECT();
    erg += b_gk_spa(CALLOCOBJECT(),CALLOCOBJECT(),d);
    erg += copy_partition(a,S_SPA_G(d));
    erg += copy_partition(b,S_SPA_K(d));
    erg += m_skewpart_skewperm(d,e);
    FREEALL(d); 

    newtrans_koeff = part_part_skewschur_koeff;
    erg += newtrans_maxpart_maxlength(e,c,-1,-1);
    newtrans_koeff = NULL;
    FREEALL(e); 

    if (t==1) t_HASHTABLE_SCHUR(c,c);
ende:
    CTTO(SCHUR,HASHTABLE,"part_part_skewschur(res)",c);
    ENDR("part_part_skewschur");
}




#endif /* SKEWPARTTRUE */

INT mult_apply_schur_schur(a,b) OP a,b;
/* platzhalter */
/* b = b*a */
{
    INT erg = OK;
    OP c;
    CTTO(HASHTABLE,SCHUR,"mult_apply_schur_schur",a);
    CTTO(HASHTABLE,SCHUR,"mult_apply_schur_schur",b);
 
    c = CALLOCOBJECT();
    if (S_O_K(b) == HASHTABLE) erg += init_hashtable(c);
    erg += mult_schur_schur(a,b,c);
    SWAP(c,b);
    FREEALL(c);
 
    ENDR("mult_apply_schur_schur");
}


#endif /* SCHURTRUE */
