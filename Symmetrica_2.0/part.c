/* SYMMETRICA V2.0 260298 */
/* file: part.c */

#include "def.h"
#include "macro.h"


static struct partition * callocpartition();
static void utiliser();
static void repartir();
static INT ordcon_char();
static INT m060588();
static INT m060588b();
INT mem_counter_part=(INT)0; /* AK 100893 */


INT partition_speicherindex=-1; /* AK 301001 */
INT partition_speichersize=0; /* AK 301001 */
struct partition **partition_speicher=NULL; /* AK 301001 */
static OP nb_e = NULL; /* result in number of part */






#ifdef PARTTRUE
    INT t_CHARPARTITION_PARTITION();

static char * part_kind_to_text(k) OBJECTKIND k;
{
    switch(k)
        {
        case EXPONENT:    return "exponent";
        case VECTOR:    return "vector";
        case BITVECTOR:    return "bitvector";
        case FROBENIUS:    return "frobenius";
        default:    return "unknown";
        }
}

static INT wrong_kind_part(t,a,b) char *t; OP a; OBJECTKIND b;
{
    char s[200];
    sprintf(s,"%s: wrong kind of partition, should be %s but it was %s",
        t,part_kind_to_text(b),part_kind_to_text(S_PA_K(a)));
    error(s);
    return ERROR;
}

INT hookp(a) OP a;
/* AK 110888 */ /* AK 280689 V1.0 */ /* AK 160890 V1.1 */ /* AK 180391 V1.2 */
/* AK 210891 V1.3 */ /* AK V2.0 160698 */
    {
    INT erg = OK;
    PART_CHECK_KIND("hookp",a,VECTOR);
    if (S_PA_LI (a) <= 1) 
    return(TRUE);
    if (S_PA_II (a, S_PA_LI(a) - 2) == 1) 
    return(TRUE);
    return(FALSE);
    ENDR("hookp");
    }

INT inc_partition(a) OP a;
/* AK 2.0 090298 */
    {
    INT erg  = OK;
    CTO(PARTITION,"inc_partition(1)",a);
    erg += inc_vector(S_PA_S(a));
    ENDR("inc_partition");
    }

INT m_i_staircase(a,b) OP a,b;
/* AK 2.0 090298 */
/* input: INTEGER object a
   output: PARTITION object 1,2,3,4,...,a */
{
    INT i;
    INT erg = OK;
    CTO(INTEGER,"m_i_staircase",a);
    if (S_I_I(a) <= (INT)0)
        {
        erg += error("m_i_staircase:input <= 0");
        goto endr_ende;
        }
    CE2(a,b,m_i_staircase);

    erg += b_ks_pa(VECTOR,callocobject(),b);
    erg += m_l_v(a,S_PA_S(b));
    C_O_K(S_PA_S(b),INTEGERVECTOR);
    for (i=0;i<S_PA_LI(b);i++)
        M_I_I(i+1,S_PA_I(b,i));
    ENDR("m_i_staircase");
}

INT partitionp(a) OP a;
/* AK 170692 */
/* AK 2.0 090298 */
{
    INT i;
    if ( S_O_K(a) == CHARPARTITION) /* AK 170593 */
        {
        INT m=1;
        for (i=(INT)0;i<S_PA_CL(a); i++)
            {
            if (S_PA_CII(a,i) < m) return FALSE;
            m = S_PA_CII(a,i);
            }
        return TRUE;
        }
    if ( S_O_K(a) != PARTITION ) return FALSE;
    if ( S_PA_K(a) == VECTOR )
        {
        INT m=1;
        for (i=(INT)0;i<S_PA_LI(a); i++)
            {
            if (S_O_K(S_PA_I(a,i)) != INTEGER) return FALSE;
            if (S_PA_II(a,i) < m) return FALSE;
            m = S_PA_II(a,i);
            }
        return TRUE;
        }
    if ( S_PA_K(a) == EXPONENT )
        {
        for (i=(INT)0;i<S_PA_LI(a); i++)
            {
            if (S_O_K(S_PA_I(a,i)) != INTEGER) return FALSE;
            if (S_PA_II(a,i) < (INT)0) return FALSE;
            }
        return TRUE;
        }
    if (S_PA_K(a) == BITVECTOR )
        return TRUE;
    return FALSE;
}



INT neqparts_partition(a) OP a; { return strictp(a); }

INT strictp(a) OP a;
/* AK 300792   true if no equal parts */
/* AK 2.0 090298 */
{
    INT i;    
    INT erg = OK;
    CTO(PARTITION,"strictp(1)",a);
    if (S_PA_K(a) == VECTOR)
        {
        for (i=1;i<S_PA_LI(a);i++)
            if (S_PA_II(a,i) == S_PA_II(a,i-1))
                return FALSE;
        return TRUE;
        }
    else if (S_PA_K(a) == EXPONENT)
        {
        for (i=(INT)0;i<S_PA_LI(a);i++)
            if (S_PA_II(a,i) > 1) return FALSE;
        return TRUE;
        }
    else
        {
        debugprint(a);
        return error("strictp:wrong type of partiton");
        }
    ENDR("strictp");
}

INT oddpartsp(a) OP a;
/* AK 080306 V3.0 true if all parts odd */
{
	INT i;
	INT erg =OK;
	CTO(PARTITION,"oddpartsp(1)",a);
	if (S_PA_K(a) == VECTOR)
		{
		for (i=0;i<S_PA_LI(a);i++)
			if (S_PA_II(a,i) %2 == 0) return FALSE;
		return TRUE;
		}
	else
		NYI("oddpartsp");
	ENDR("oddpartsp");
}



INT sub_part_part(a,b,c) OP a,b,c;
/* c = a - b */ 
/* component wise subtraction */
/* AK 100603 */
{
    INT erg = OK;
    INT i,j,l;
    PART_CHECK_KIND("sub_part_part",a,VECTOR);
    PART_CHECK_KIND("sub_part_part",b,VECTOR);
    SYMCHECK(S_PA_LI(b) > S_PA_LI(a), "sub_part_part:second partition too big");
    CE3(a,b,c,sub_part_part);
    if (S_PA_LI(a) == S_PA_LI(b))
        {
        for (i=0;i<S_PA_LI(a);i++) if (S_PA_II(a,i) != S_PA_II(b,i)) break;
        if (i==S_PA_LI(a)) {
            m_il_pa(0,c);  /* 0 missing in first parameter AK 100206 */
            goto ende;   /* it was a = b */
            }
        j = i;
        m_il_pa(S_PA_LI(a)-i,c);
        l=0;
        }
    else { 
         i = S_PA_LI(a)-S_PA_LI(b); j=0; 
         copy_partition(a,c);
         l = i;
         }
    for (;j<S_PA_LI(b);j++,i++,l++)
        M_I_I(S_PA_II(a,i)-S_PA_II(b,j),S_PA_I(c,l));
    l=S_PA_II(c,0);
    /* check the result wether partition */
    for (i=1;i<S_PA_LI(c);i++)
        if (S_PA_II(c,i) < l) {
             erg += error("sub_part_part: second parameter not contained in the first parameter ");
             FREESELF(c);
             goto ende;
             }
        else l=S_PA_II(c,i);

ende:;
    ENDR("sub_part_part");
}

INT add_part_part(a,b,c) OP a,b,c;
/* c = a + b */ 
/* component wise addidtion */
/* AK 071189 */ /* AK 181289 V1.1 */ /* AK090891 V1.3 */
/* AK 2.0 090298 */
{
    INT i,j;
    INT erg = OK;
    PART_CHECK_KIND("add_part_part",a,VECTOR);
    PART_CHECK_KIND("add_part_part",b,VECTOR);
    CE3(a,b,c,add_part_part);

    if (S_PA_LI(a) <= S_PA_LI(b)) 
        {
        erg += copy_partition(b,c);
        for (i=S_PA_LI(a)-1,j=S_PA_LI(b)-1;i>=(INT)0;i--,j--)
            M_I_I(S_PA_II(a,i) + S_PA_II(b,j),S_PA_I(c,j));
        }
    else    {
        erg += copy_partition(a,c);
        for (i=S_PA_LI(a)-1,j=S_PA_LI(b)-1;j>=(INT)0;i--,j--)
            M_I_I(S_PA_II(a,i) + S_PA_II(b,j),S_PA_I(c,i));
        }
    ENDR("add_part_part");
}

INT remove_part_integer(a,b,c) OP a,b,c;
/* AK 100202 */
/* 234,2 --> 34 */
{
    INT erg = OK;
    OP d;
    CTO(PARTITION,"remove_part_integer(1)",a);
    CTO(INTEGER,"remove_part_integer(2)",b);
    CTO(EMPTY,"remove_part_integer(3)",c);
    d = CALLOCOBJECT();
    erg += m_i_pa(b,d);
    erg += remove_part_part(a,d,c);
    FREEALL(d);
    CTO(PARTITION,"remove_part_integer(e3)",c);
    ENDR("remove_part_integer");
}

INT remove_part_part(a,b,c) OP a,b,c;
/* AK 070995 */
/* 23344 , 24 ->> 334 */
/* AK 2.0 090298 */
{
    INT erg = OK;
    INT i,j,k;
    OP d;

    CTO(PARTITION,"remove_part_part(1)",a);
    CTO(PARTITION,"remove_part_part(2)",b);
    CTO(EMPTY,"remove_part_part(3)",c);
    
    if (S_PA_K(a) != S_PA_K(b))
        {
        erg += error("remove_part_part entered different kind of partitions");
        goto endr_ende;
        }
    else if (S_PA_K(a) == VECTOR)
        {
        d = CALLOCOBJECT();
        erg += m_il_nv(S_PA_LI(a),d);
        for (i=0,j=0,k=0;i<S_PA_LI(a);i++)
            {
aaa:
            if (j==S_PA_LI(b))
                {
                M_I_I(S_PA_II(a,i), S_V_I(d,k));
                k++;
                }
            else if (S_PA_II(a,i) == S_PA_II(b,j)) 
                {
                j++;
                }
            else if (S_PA_II(a,i) < S_PA_II(b,j))
                {
                M_I_I(S_PA_II(a,i), S_V_I(d,k));
                k++;
                }
            else    {
                j++;
                goto aaa;
                }
            }
        erg += m_v_pa(d,c);
        FREEALL(d);
        }
    else if (S_PA_K(a) == EXPONENT)
        {
        erg += b_ks_pa(EXPONENT,callocobject(),c);
        erg += sub(S_PA_S(a), S_PA_S(b), S_PA_S(c));
        for (i = 0; i<S_PA_LI(c); i++)
            if (S_PA_II(c,i) < (INT)0)
                M_I_I(0,S_PA_I(c,i));
        }
    else
        {
        erg += error("remove_part_part works only with EXPONENT, VECTOR storage method");
        goto endr_ende;
        }
    C_O_K(S_PA_S(c),INTEGERVECTOR);
    ENDR("remove_part_part");
}

INT append_apply_part(a,b) OP a,b;
/* AK 060901 */
/* a := new partition from sorted parts */
{
    INT erg = OK;
    CTO(PARTITION,"append_apply_part(1)",a);
    CTTO(INTEGER,PARTITION,"append_apply_part(2)",b);

    if (a == b) { /* a := a+a */
        if (S_PA_K(a) == VECTOR) {
            erg += append_apply_vector(S_PA_S(a),S_PA_S(b));
            erg += sort(S_PA_S(a));
            goto endr_ende;
        }
        else if (S_PA_K(a) == EXPONENT) {
            INT i;
            for (i=0;i<S_PA_LI(a);i++)
                M_I_I(S_PA_II(a,i)+S_PA_II(a,i), S_PA_I(a,i));
            }
        else {
            erg += error("append_apply_part(a,a): only working for VECTOR or EXPONENT type partitions");
            goto endr_ende;
            }
        }
    else { /* a := a+b */
        if (S_O_K(b) == INTEGER) {
            SYMCHECK(S_I_I(b) < 0,"append_apply_part:arg 2 integer < 0");
            if (S_I_I(b) == 0) goto ende;

            if (S_PA_K(a) == VECTOR) {
                INT i;
                inc_vector_co(S_PA_S(a),1);
                for (i=S_PA_LI(a)-2;i>=0;i--)
                    if( S_PA_II(a,i) > S_I_I(b) ) 
                        M_I_I(S_PA_II(a,i),S_PA_I(a,i+1));
                    else
                        {
                        M_I_I(S_I_I(b),S_PA_I(a,i+1));
                        goto ende;
                        }
                M_I_I(S_I_I(b),S_PA_I(a,0));
                goto ende;
                }
            else if (S_PA_K(a) == EXPONENT) {
                if (S_PA_LI(a) >= S_I_I(b)) 
                    { INC_INTEGER(S_PA_I(a,S_I_I(b)-1)); }
                else {
                    INT l;
                    l = S_PA_LI(a);
                    inc_vector_co(S_PA_S(a), S_I_I(b) - S_PA_LI(a) );
                    for (;l<S_PA_LI(a);l++) M_I_I(0,S_PA_I(a,l)); 
                    INC_INTEGER(S_PA_I(a,S_I_I(b)-1));
                    }
                goto ende;
                }
            else {
                erg += error("append_apply_part(a,INTEGER): only working for partitions of VECTOR,EXPONENT  type");
                goto endr_ende;
                }
            }
        if (S_PA_K(a) != S_PA_K(b)) {
            erg += error("append_apply_part(a,b): only working for partitions of equal type");
            goto endr_ende;
            }
        if (S_PA_K(a) == VECTOR) {
            INT i,j,k;
            i=S_PA_LI(a)-1;
            k=S_PA_LI(b)-1;
/*
            erg += append_apply_vector(S_PA_S(a),S_PA_S(b));
            erg += sort(S_PA_S(a));
*/
            inc_vector_co(S_PA_S(a),S_PA_LI(b));
            for (j=S_PA_LI(a)-1;j>=0;j--)
                 if (k == -1) goto ende;
                 else if (i == -1) { M_I_I(S_PA_II(b,k), S_PA_I(a,j)); k--; }
                 else if (S_PA_II(b,k) > S_PA_II(a,i)) { M_I_I(S_PA_II(b,k), S_PA_I(a,j)); k--; }
                 else { M_I_I(S_PA_II(a,i), S_PA_I(a,j)); i--; }
            
            goto ende;
        }
        else if (S_PA_K(a) == EXPONENT) {
            INT i,l,ol;
            l = (S_PA_LI(a) > S_PA_LI(b) ? S_PA_LI(a) :  S_PA_LI(b) );
            /* l is the maximum of lengthes */
            ol = S_PA_LI(a);
            if (l > S_PA_LI(a)) 
                erg += inc_vector_co(S_PA_S(a), l - S_PA_LI(a) );
            for (i=0;i<l;i++)
                if ( (l < ol) && (l <S_PA_LI(b) ))
                    M_I_I(S_PA_II(a,i)+S_PA_II(b,i), S_PA_I(a,i));
                else if (l <S_PA_LI(b) )
                    M_I_I(S_PA_II(b,i),S_PA_I(a,i));
            goto endr_ende;
            }
        else {
            erg += error("append_apply_part(a,a): only working for VECTOR or EXPONENT type partitions");
            goto endr_ende;
            }
        }
ende:
    ENDR("append_apply_part");
}
INT append_part_part(a,b,c) OP a,b,c;
/* AK 090891 V1.3 */
/* join the parts to one partition */
/* e.g. 233, 1224 --> 1222334 */
/* AK 2.0 090298 */
{
    OP d;
    INT erg = OK;
    CTO(PARTITION,"append_part_part(1)",a);

    if (S_O_K(b) == INTEGER) 
        {
        d = callocobject();
        erg += first_partition(b,d);
        erg += append_part_part(a,d,c);
        erg += freeall(d);
        goto endr_ende;
        }
    else if (S_O_K(b) == VECTOR) 
        {
        erg += copy(b,c);
        erg += inc(c);
        erg += copy_partition(a,S_V_I(c,S_V_LI(c)-1));
        goto endr_ende;
        }
    else if (S_O_K(b) == EMPTY)
        {
        erg += copy_partition(a,c);
        goto endr_ende;
        }
    CTO(PARTITION,"append_part_part(2)",b);
    if (S_PA_K(a) != S_PA_K(b))
        {
        erg += error("append_part_part: different kind of partitions");
        }
    else if (S_PA_K(a) == VECTOR)
        {
/*
        d = callocobject();
        erg += append(S_PA_S(a),S_PA_S(b),d);
        erg += m_v_pa(d,c);
        erg += freeall(d);
*/
/* the following is faster */
/* AK 260901 */
        INT i,j,k;
        B_KS_PA(VECTOR,CALLOCOBJECT(),c);
        erg += m_il_v(S_PA_LI(a)+S_PA_LI(b),S_PA_S(c));
        C_O_K(S_PA_S(c),INTEGERVECTOR); /* AK 011101 */
        for (i=0,j=0,k=0;i<S_PA_LI(c);i++)
             if (j==S_PA_LI(a)) 
                 { M_I_I(S_PA_II(b,k),S_PA_I(c,i)); k++; }
             else if (k==S_PA_LI(b)) 
                 { M_I_I(S_PA_II(a,j),S_PA_I(c,i)); j++; }
             else if (S_PA_II(a,j) < S_PA_II(b,k)) 
                 { M_I_I(S_PA_II(a,j),S_PA_I(c,i)); j++; }
             else 
                 { M_I_I(S_PA_II(b,k),S_PA_I(c,i)); k++; }
        }
    else if (S_PA_K(a) == EXPONENT)
        {
        B_KS_PA(EXPONENT,CALLOCOBJECT(),c);
        erg += add_integervector(S_PA_S(a), S_PA_S(b), S_PA_S(c));
        }
    else    {
        erg += error("append_part_part works only for VECTOR,EXPONENT partitions");
        }
    ENDR("append_part_part");
}


INT add_partition(a,b,c) OP a,b,c;
/* AK 060789 V1.0 */ /* AK 280590 V1.1 */ /* AK 200891 V1.3 */
/* AK 2.0 090298 */
{
    INT erg = OK; /* AK 040292 */
    CTO(PARTITION,"add_partition(1)",a);
    CTO(EMPTY,"add_partition(3)",c);

    switch(S_O_K(b))
    {
    case PARTITION : 
        erg += add_part_part(a,b,c); 
        break;

#ifdef SCHURTRUE
    case SCHUR : 
        erg += m_pa_s(a,c); 
        erg += add_apply(b,c); 
        break;
#endif /* SCHURTRUE */

    default : 
        erg +=  WTO("add_partition(2)",b);
    }

    ENDR("add_partition");
}



INT first_composition(w,parts,c) OP parts, w, c;
/* AK 090487 */ /* AK 201189 V1.1 */ /* AK 150591 V1.2 */ /* AK 200891 V1.3 */
/* AK 2.0 090298 */
/* parameter may be equal */
/* AK 170206 V3.0 */
{
    INT i,erg=OK,wp,ww;
    CTO(INTEGER,"first_composition",w);ww=S_I_I(w);
    CTO(INTEGER,"first_composition",parts);wp=S_I_I(parts);
    SYMCHECK(wp <= 0,"first_composition:number of parts <= 0");
    SYMCHECK(ww <= 0,"first_composition:weight <= 0");
    erg += m_il_nv(wp,c);
    M_I_I(ww,S_V_I(c,0));
    C_O_K(c,COMPOSITION);
    ENDR("first_composition");
}

INT first_subset(n,k,c) OP n,k,c;
/* AK 220997 */
/* AK V2.0 090298 */
/* AK V2.1 100902 */ /* AK 3.1 081106 */

/* computes the first k-element subset of a n-element set */
/* result is of type subset */
{
    INT erg = OK;
    CTO(INTEGER,"first_subset(1)",n);
    CTO(INTEGER,"first_subset(2)",k);
    SYMCHECK( S_I_I(n) <= 0, "first_subset:input variable n <= 0");
    SYMCHECK( S_I_I(k) < 0, "first_subset:input variable k < 0");
    SYMCHECK (S_I_I(k) > S_I_I(n) ,"first_subset:input variable k > n");
    CE3(n,k,c,first_subset);
    {
    INT i;
    erg += m_l_nv(n,c);
    for (i=0;i<S_I_I(k); i++)
        M_I_I(1,S_V_I(c,i));
    C_O_K(c,SUBSET);
    }
    CTO(SUBSET,"first_subset(e3)",c);
    ENDR("first_subset");
}

INT next_subset(c,d) OP c,d;
/* AK 220997 */
/* AK 2.0 090298 */
{
    INT i,m;
    copy(c,d);
    m=0;
    for (i=S_V_LI(c)-1;i>=0;i--)
        {
        if (S_V_II(c,i) == 0) break;
        else m++;
        }
    /* m ist die anzahl der gelesenen 1en bis zur 0 */
    for (; i>=0 ;i--)
        {
        if (S_V_II(c,i) == 1)  break;
        }
    if (i == -1) return LAST_SUBSET;
    M_I_I(0, S_V_I(d,i));
    M_I_I(1,S_V_I(d,i+1));

    for (i=i+2; m>0 ; i++,m--)
        M_I_I(1,S_V_I(d,i));
    for (; i<S_V_LI(d); i++)
        M_I_I(0,S_V_I(d,i));
    return OK;
}

INT next_apply_subset(c) OP c;
/* AK 281097 */
/* AK V2.0 200298 */ /* AK 090107 V3. 1*/
{
    INT i,m;
    m=0;
    for (i=S_V_LI(c)-1;i>=0;i--)
        {
        if (S_V_II(c,i) == 0) break;
        else m++;
        }
    /* m ist die anzahl der gelesenen 1en bis zur 0 */
    for (; i>=0 ;i--)
        {
        if (S_V_II(c,i) == 1)  break;
        }
    if (i == -1) return LAST_SUBSET;
    M_I_I(0, S_V_I(c,i));
    M_I_I(1,S_V_I(c,i+1));

    for (i=i+2; m>0 ; i++,m--)
        M_I_I(1,S_V_I(c,i));
    for (; i<S_V_LI(c); i++)
        M_I_I(0,S_V_I(c,i));
    return OK;
}


INT next_composition(c,newcomp) OP c, newcomp;
/* AK V2.0 100298 */
{
    INT erg = OK;
    CTO(COMPOSITION,"next_composition(1)",c);
    copy_composition(c,newcomp);
    return next_apply_composition(newcomp);
    ENDR("next_composition");
}

INT next_apply_composition(newcomp) OP newcomp;
/* AK 300889 */ /* AK 201189 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 100298 */
{
    INT i,j,rest;
    for (i=S_V_LI(newcomp)-2L,j=i+1,rest=(INT)0; i>=(INT)0; i--,j--)
        if (S_V_II(newcomp,i) == (INT)0)
        {
            rest += S_V_II(newcomp,j);
            C_I_I(S_V_I(newcomp,j),(INT)0);
        }
        else if (S_V_II(newcomp,i) > (INT)0)
        {
            DEC_INTEGER(S_V_I(newcomp,i));
            C_I_I(S_V_I(newcomp,j),S_V_II(newcomp,j)+1+rest);
            return(OK);
        };
    return(LASTCOMP);
}


INT is_selfconjugate(part) OP part;
/* AK 180703 */
{
    INT erg = OK,res;
    OP c;
    CTO(PARTITION,"is_selfconjugate(1)",part);

    c = CALLOCOBJECT();
    conjugate_partition(part,c);
    res = EQ(c,part);
    FREEALL(c);
    return res;
    ENDR("is_selfconjugate");
}

INT conjugate_partition(part,b) OP part, b;
/* AK 220587 */
/* AK 060789 V1.0 */ /* AK 240490 V1.1 */ /* AK 200891 V1.3 */
/* AK 200298 V2.0 */
{
    INT i,j,k=(INT)0,m;
    /* k ist die adresse an der geschrieben wird im b */
    INT erg = OK;

    CTO(PARTITION,"conjugate_partition",part);
    CE2(part,b,conjugate_partition);

    if (S_PA_K(part) == EXPONENT)  /* AK 170692 */
        {
        OP c = callocobject();
        erg += t_EXPONENT_VECTOR(part,c);
        erg += conjugate_partition(c,b);
        erg += freeall(c);
        erg += t_VECTOR_EXPONENT(b,b);
        goto endr_ende;
        }
    else if  (S_PA_K(part) == BITVECTOR) /* AK 090703 */
        {
        COPY(part,b);
        erg += reverse_bitvector(S_PA_S(b),S_PA_S(b));
        erg += invers_bitvector(S_PA_S(b),S_PA_S(b));
        goto endr_ende;
        }
    else if  (S_PA_K(part) == FROBENIUS) 
                {
        B_KS_PA(FROBENIUS,callocobject(),b);
        erg += m_il_v((INT)2,S_PA_S(b));
        erg += copy_integervector(S_V_I(S_PA_S(part),0),
                S_V_I(S_PA_S(b),1) );
        erg += copy_integervector(S_V_I(S_PA_S(part),1),
                S_V_I(S_PA_S(b),0) );
        goto endr_ende;
        }
    else if (S_PA_K(part) != VECTOR) 
        {
        erg += error("conjugate_partition: works only for VECTOR,EXPONENT,FROBENIUS type");
        goto endr_ende;
        }

    if (S_PA_LI(part) == (INT)0)
        {
        erg += copy_partition(part,b);
        goto endr_ende;
        }
    erg += m_il_pa(S_PA_II(part,S_PA_LI(part)-1),b);

    j = S_PA_LI(part) - 1;
    /* dies sind die adressen in den beiden partitionen */
    m = S_PA_LI(b)+S_PA_LI(part)+1;
    /* dies ist die laenge der permutation + 1 */
    for(    i=m-1; i > (INT)0 ; i--)
    {
        if (j>=0)
            if (i == S_PA_II(part,j)+j+1 ) j-- ;
            else {
                M_I_I(m-i- k - 1,S_PA_I(b,k));
                k++ ;
            }
        else    {
            M_I_I(m-i- k - 1,S_PA_I(b,k));
            k++ ;
        }
    }
    ENDR("conjugate_partition");
}



INT ferrers_partition(part) OP part;
/* AK 060789 V1.0 */ /* AK 150690 V1.1 */ /* AK 200891 V1.3 */
/* AK 240298 V2.0 */
{
    INT i,j;
    INT erg = OK;
    OP z;
    CTO(PARTITION,"ferrers_partition",part);
    if (S_PA_K(part) == EXPONENT)
        {
        z = callocobject();
        erg += t_EXPONENT_VECTOR(part,z);
        erg += ferrers_partition(z);
        erg += freeall(z);
        goto endr_ende;
        }
    PART_CHECK_KIND("ferrers_partition",part,VECTOR);

    printf("\n");
    for (i=(INT)0; i<S_PA_LI(part);i++)
    {
        for (j=(INT)0;j<S_PA_II(part,i);j++) printf("**** ");
        printf("\n");
        for (j=(INT)0;j<S_PA_II(part,i);j++) printf("**** ");
        printf("\n\n");
    };
    zeilenposition = (INT)0;
    ENDR("ferrers_partition");
}



INT fprint_partition(f,partobj) FILE    *f; OP partobj;
/* AK 140587 */ /* AK 060789 V1.0 */ /* AK 290890 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT i;
    INT erg = OK;
    if (S_PA_K(partobj) == FROBENIUS) /* AK 101292 */
        {
        fprint(f,S_PA_S(partobj));
        goto endr_ende;
        }
    else if (S_PA_K(partobj) == BITVECTOR)
                {
        fprint(f,S_PA_S(partobj));
        goto endr_ende;
        }
    else if (S_PA_LI(partobj) == (INT)0)
        {
        fprintf(f,"[]");
        if (f == stdout) zeilenposition+=2;
        goto endr_ende;
        }
    
    for(    i = (INT)0; i<S_PA_LI(partobj); i++)
        if (S_PA_II(partobj,i)<10)
        /*AK partitionsteile kleiner 10 werden als Zahlen geschrieben */
        { 
            fprintf(f,"%ld",S_PA_II(partobj,i));
            if (f == stdout) zeilenposition++; 
        }
        else if (S_PA_II(partobj,i)<16)
        /* A.K. partitionsteile von 10 bis 15 werden als 
            A,B,C,D,E,F geschrieben */
        { 
            fprintf(f,"%c",(int)S_PA_II(partobj,i)+55);
            if (f == stdout) zeilenposition++; 
        }
        else    {
            /* A.K. sonst werden die Teile als zahl mit 
            abschliessenden senkrechten Strich geschrieben */
            fprintf(f,"%c%ld",'|',S_PA_II(partobj,i));
            if(f==stdout) 
                zeilenposition+=(1+intlog(S_PA_I(partobj,i)));
            };
    if ((f == stdout)&&(zeilenposition>row_length))
    { 
        fprintf(f,"\n"); 
        zeilenposition = (INT)0; 
    }
    ENDR("fprint_partition");
}

INT sprint_partition(f,partobj) char    *f; OP partobj;
/* AK V2.0 200298 */
{
    INT i;
    INT erg = OK;
    CTO(PARTITION,"sprint_partition",partobj);
    if (S_PA_K(partobj) == FROBENIUS) /* AK 101292 */
        {
        erg += sprint(f,S_PA_S(partobj));
        goto endr_ende;
        }
    else if (S_PA_K(partobj) == BITVECTOR)
                {
        erg+= sprint(f,S_PA_S(partobj));
        goto endr_ende;
        }
    
    f[0]='\0'; /* AK 151298 to handle zero partition */
    for(    i = (INT)0; i<S_PA_LI(partobj); i++)
        if (S_PA_II(partobj,i)<10)
        /*AK partitionsteile kleiner 10 werden als Zahlen geschrieben */
        { 
            sprintf(f,"%ld",S_PA_II(partobj,i));
            f++; 
        }
        else if (S_PA_II(partobj,i)<16)
        /* A.K. partitionsteile von 10 bis 15 werden als 
            A,B,C,D,E,F geschrieben */
        { 
            sprintf(f,"%c",(int)S_PA_II(partobj,i)+55);
            f++; 
        }
        else    {
            /* A.K. sonst werden die Teile als zahl mit 
            abschliessenden senkrechten Strich geschrieben */
            sprintf(f,"%c%ld",'|',S_PA_II(partobj,i));
            f+=(1+intlog(S_PA_I(partobj,i)));
            };
    ENDR("sprint_partition");
}




INT gupta_nm(n,m,res) OP n,m,res;
/* AK 220888 
    vgl. Hansraj Gupta Proc London Math Soc 2 (39)
    1935 142-149 dort werden die Anzahlen der Partitionen von n
    bis n=300 aufgelistet. Zur Berechnung mittels einer
    Rekurssion werden die Zahlen (n,m) = Anzahl der Partitionen
    von n mit dem kleinsten Teil = m benoetigt
    Diese werden rekursiv berechnet, diese Zahlen 
    werden auch von dieser Prozedur berechnet
    */
/* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    OP i,j,zw;
    INT erg = OK;


    CTO(INTEGER,"gupta_nm",n);
    CTO(INTEGER,"gupta_nm",m);
    CE3(n,m,res,gupta_nm);

    if (S_I_I(n) == S_I_I(m)) 
        {
        erg += m_i_i(1,res);
        }
    else if (S_I_I(m) > S_I_I(n)/2L) 
        {
        erg += m_i_i((INT)0,res);
        }
    else    {
        i = callocobject(); 
        j = callocobject(); 
        zw = callocobject();
        /* initialisieren i = n-m, j = m, res = 0 */
        M_I_I(S_I_I(n)-S_I_I(m),i); 
        COPY_INTEGER(m,j); 
        erg += m_i_i((INT)0,res);
        
        while(S_I_I(j) <= S_I_I(i) )
        { 
            erg += gupta_nm(i,j,zw); 
            if (S_O_K(zw) != INTEGER) add_apply(zw,res); 
            else if (not NULLP_INTEGER(zw)) add_apply(zw,res); 
            /* nicht aufrufen falls 0 */
            INC_INTEGER(j); 
        }

        erg += freeall(zw); 
        erg += freeall(i); 
        erg += freeall(j);
        }
    ENDR("gupta_nm");
}

#ifdef MATRIXTRUE
INT gupta_tafel(mx,mat) OP mx,mat;
/* AK 220888 */
/* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 200891 V1.3 */
/* AK 200298 V2.0 */
/* mx and mat may be equal */
{
    INT erg = OK;
    CTO(INTEGER,"gupta_tafel(1)",mx);
    {


    INT i,j,k;
    OP h,l;
    h = callocobject();
    l = callocobject();

    M_I_I(S_I_I(mx),h); 
    M_I_I((S_I_I(mx) / 2L)+1,l);

    erg += b_lh_nm(l,h,mat);

    for (i=0; i< S_I_I(mx); i++)
        for (j=0;j<=i/2L;j++)
        {
            for (k=(INT)0; j+k < (i-j)/2L ; k++)
            /* die rekursion */
                ADD_APPLY(S_M_IJ(mat,i-j-1,j+k),S_M_IJ(mat,i,j));
            INC(S_M_IJ(mat,i,j));
        };
    }
    ENDR("gupta_tafel");
}

INT gupta_nm_speicher(n,m,res) OP n,m,res;
/* AK 120390 V1.1 */ /* AK 200891 V1.3 */
/* AK 200298 V2.0 */
/* n,m,res may be equal */
{
    OP mat;
    INT erg = OK;
    CTO(INTEGER,"gupta_nm_speicher",n);
    CTO(INTEGER,"gupta_nm_speicher",m);
    if (S_I_I(n) <= 0)
        {
        erg += error("gupta_nm_speicher;input <= 0");
        goto endr_ende;
        }

    if (S_I_I(n) == S_I_I(m)) 
        {
        M_I_I(1,res);
        goto endr_ende;
        }
    if (S_I_I(m) > S_I_I(n)/2L) 
        {
        M_I_I(0,res);
        goto endr_ende;
        }

    mat = callocobject();
    erg += gupta_tafel(n,mat);
    erg += copy(S_M_IJ(mat,S_I_I(n)-1,S_I_I(m)-1),res);
    erg += freeall(mat);
    ENDR("gupta_nm_speicher");
}

#endif /* MATRIXTRUE */



INT hook_length_augpart(p,i,j,res) OP p,res; INT i,j;
/* AK 060988 hakenlaenge */ 
/* AK 060789 V1.0 */ /* AK 080290 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* p and res may be equal */
{
    INT e,k;
    INT erg = OK;
    OP z;
    CTO(AUG_PART,"hook_length_augpart(1)",p);
    FREESELF(res);

    if (i >= S_PA_LI(p)) 
        {
        M_I_I(0,res);
        goto ende;
        }
    z = S_PA_I(p,i);
    if (j >= S_I_I(z)-i) 
        {
        M_I_I(0,res);
        goto ende;
        }
    else    {
        e = S_I_I(z) - j - i;
        /* nun noch die zeilen dazu */
        for (z--,k=i-1; k>= 0; k--,z--)
            if (S_I_I(z) -1 -k >= j) 
                e++;
            else break;
        M_I_I(e,res);
        goto ende;
        }
ende:
    CTO(INTEGER,"hook_length_augpart(e4)",res);
    ENDR("hook_length_augpart");
}



INT hook_diagramm(p,m) OP p,m;
/* AK 010295 */
/* AK V2.0 100298 */
/* input:  PARTITION object
   output: MATRIX object with hooklength */
{
    INT erg = OK, i,j;
    
    PART_CHECK_KIND("hook_diagramm(1)",p, VECTOR);
    CE2(p,m,hook_diagramm);
        
    erg += m_ilih_m(S_PA_II(p,S_PA_LI(p)-1), S_PA_LI(p), m);
    for (i=0;i<S_M_HI(m);i++)
    for (j=0;j<S_M_LI(m);j++)
        erg += hook_length(p,i,j,S_M_IJ(m,i,j));
    CTO(MATRIX,"hook_diagramm(2e)",m);
    ENDR("hook_diagramm");
}

INT hook_length(p,i,j,b) OP p,b; INT i,j;
/* AK 060988 hakenlaenge */ 
/* AK 060789 V1.0 */ /* AK 150690 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 100298 */
{
    INT e,k;
    INT erg = OK;
    CTO(PARTITION,"hook_length(1)",p);

    if (S_PA_K(p) == EXPONENT)  /* AK 170692 */
        {
        OP c = callocobject();
        e = t_EXPONENT_VECTOR(p,c);
        e += hook_length(c,i,j,b);
        e += freeall(c);
        return e;
        }

    SYMCHECK( S_PA_K(p) != VECTOR,"hook_length:only for vector or exponent type");

    FREESELF(b);

    if (i >= S_PA_LI(p)) 
        { M_I_I(0,b); goto ende; }
    if (j >= S_PA_II(p,S_PA_LI(p)-1-i)) 
        { M_I_I(0,b); goto ende; }
    e = S_PA_II(p,S_PA_LI(p)-1-i) - j;
    /* nun noch die zeilen dazu */
    for (k=i+1; k<S_PA_LI(p); k++) 
        if (S_PA_II(p,S_PA_LI(p)-1-k) -1 >= j) e++;
        else break;
    M_I_I(e,b);
ende:
    ENDR("hook_length");
}



INT dimension_partition(a,b) OP a,b;
/* AK 150988 */
/* AK 060789 V1.0 */ /* AK 080290 V1.1 */ /* AK 050391 V1.2 */ 
/* AK 200891 V1.3 */
/* AK 200298 V2.0 */
/* input:    PARTITION object
   ouput:    dimension of corresponding irreducible Sn character
            INTEGER object or LONGINT object */
/* a and b may be equal */
{
    OP zaehler, nenner,  zw;
    INT i,j;
    INT erg = OK;

    CTO(PARTITION,"dimension_partition(1)",a);

    if (S_PA_K(a) == EXPONENT) /* AK 170692 */
        {
        zw = callocobject();
        erg += t_EXPONENT_VECTOR(a,zw);
        erg += dimension_partition(zw,b);
        erg += freeall(zw);
        }
    else if (S_PA_K(a)  != VECTOR) 
        {
        error("dimension_partition: wrong kind of partition");
        erg = ERROR;
        }
    else    {
        zw = callocobject();
        zaehler = callocobject();
        erg = weight(a,zw);

        erg += fakul(zw,zaehler);
        FREESELF(zw);
        NEW_INTEGER(nenner,1);
        for (i=(INT)0;i<S_PA_LI(a);i++)
            for (j=(INT)0;j<S_PA_II(a,S_PA_LI(a)-1-i);j++)
            {
                erg += hook_length(a,i,j,zw);
                MULT_APPLY(zw,nenner);
            };
        FREEALL(zw);
        FREESELF(b);
        GANZDIV(zaehler,nenner,b);
        FREEALL(zaehler);
        FREEALL(nenner);
        }
    ENDR("dimension_partition");
}



INT dimension_augpart(a,b) OP a,b;
/* a ist an object of type AUGPART
   b becomes the dimension of the corresponding irred representation */
/* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 250291 V1.2 */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    OP nenner;
    OP zw;
    
    INT i,j,erg = OK;
    CTO(AUG_PART,"dimension_augpart(1)",a);

    FREESELF(b);

    if (S_PA_LI(a) == 1)
        { M_I_I(1,b); goto ende; }
    if (S_PA_II(a,S_PA_LI(a)-1) == S_PA_LI(a)) /* 1^n */
        { M_I_I(1,b); goto ende; }
    if (S_PA_II(a,S_PA_LI(a)-2L) == S_PA_LI(a)-2L) /* n */
        { M_I_I(1,b); goto ende; }

    if (S_PA_LI(a)==2)
        {
        if (S_PA_II(a,0)==1)
            { M_I_I(S_PA_II(a,1)-1,b); goto ende; }
        }


    nenner = CALLOCOBJECT();
    zw = CALLOCOBJECT();


    erg += weight_augpart(a,zw);

    erg += fakul(zw,b);

    FREESELF(zw);
    M_I_I(1,nenner);
    for (i=(INT)0;i<S_PA_LI(a);i++)
        for (j=(INT)0;j<S_PA_II(a,i)-i;j++)
        {
            erg += hook_length_augpart(a,i,j,zw);
            if (S_I_I(zw) != 1)
                MULT_APPLY_INTEGER(zw,nenner);
        };

    FREEALL(zw); 
    GANZDIV_APPLY(b,nenner);
    FREEALL(nenner); 
ende:
    ENDR("dimension_augpart");
}



INT last_part_EXPONENT(n,part) OP n,part;
/* AK 150888 */ /* AK 060789 V1.0 */ /* AK 281189 V1.1 */
/* AK 200891 V1.3 */
/* AK 120298 V2.0 */
/* input: INTEGER object
   output:  last PARTITION object of EXPONENT kind */
{
    INT erg = OK;
    CTO(INTEGER,"last_part_EXPONENT",n);
    if (S_I_I(n) < (INT)0)
        {
        erg += error("last_part_EXPONENT:input < 0");
        goto endr_ende;
        }

    B_KS_PA(EXPONENT,CALLOCOBJECT(),part);
    erg += m_il_nv(S_I_I(n),S_PA_S(part));
    C_O_K(S_PA_S(part),INTEGERVECTOR);

    if (S_I_I(n) > (INT)0)
        M_I_I(S_PA_LI(part), S_PA_I(part,(INT)0));
    ENDR("last_part_EXPONENT");
}



INT first_part_VECTOR(n,part) OP n,part; 
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
    {
    return first_partition(n,part);
    }


INT last_part_VECTOR(n,part) OP n,part; 
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
    {
    return last_partition(n,part);
    }



INT first_part_EXPONENT(n,part) OP n,part;
/* AK 170298 V2.0 */
/* input: n = INTEGER object >= 0
   output: PARTITION-EXPONENT object  00000...00001 
           of given weight n */
/* n and part may be equal */
{
    INT i;
    INT erg = OK; 
    CTO(INTEGER,"first_part_EXPONENT",n);

    i = S_I_I(n);
    SYMCHECK((i < 0) ,"first_part_EXPONENT:input < 0");

    B_KS_PA(EXPONENT,callocobject(),part);
    erg += m_il_nv(i,S_PA_S(part));

    if (i > 0)
        M_I_I(1, S_PA_I(part,S_PA_LI(part)-1));
    C_O_K(S_PA_S(part), INTEGERVECTOR);
    ENDR("first_part_EXPONENT");
}



INT last_partition(n,part) OP n,part;
/* AK 190587 */
/* die prozedur erzeugt aus der Zahl n die Partition
[1^n], die letzte Partition bezueglich nextpartition
bzgl. Dominanzordnung und auch lexikographisch */
/* n wird nicht verwendet */
/* AK 060789 V1.0 */ /* AK 300590 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT i;
    INT erg = OK; /* AK 020692 */

    CTO(INTEGER,"last_partition",n);
    SYMCHECK((S_I_I(n) < 0) ,"last_partition:input < 0");

    CE2(n,part,last_partition);

    B_KS_PA(VECTOR,CALLOCOBJECT(),part);
    erg += m_l_v(n,S_PA_S(part));
    for (i=0;i<S_I_I(n);i++) 
        M_I_I(1,S_PA_I(part,i));
    C_O_K(S_PA_S(part), INTEGERVECTOR);
    ENDR("last_partition");
}



INT first_partition(n,part) OP n,part;
/* AK 190587 */ /* AK 060789 V1.0 */ /* AK 261190 V1.1 */ /* AK 200891 V1.3 */
/* AK 230298 V2.0 */
/* input: INTEGER object n
   output: PARTITION [n] */
/* n and part may be equal objects */
{
    INT erg = OK;
    COP("first_partition",part);
    CTO(INTEGER,"first_partition",n);

    if (S_I_I(n) < (INT)0) /* AK 020692 */
        {
        fprintf(stderr,"input = %ld\n",S_I_I(n));
        erg += error("first_partition:input < 0");
        }
    else if (S_I_I(n) == (INT)0) /* AK 020692 */
        { 
        B_KS_PA(VECTOR,CALLOCOBJECT(),part);
        erg += m_il_v((INT)0,S_PA_S(part));
        C_O_K(S_PA_S(part), INTEGERVECTOR);
        }
    else
        erg += m_i_pa(n,part); /* AK 020692 */
    ENDR("first_partition");
}



INT next_partition(part,next) OP part,next;
/* AK 060789 V1.0 */ /* AK 300590 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* the order of transversal of the set of all partitions
   is equal if we use VECTOR or EXPONENT */
{
    INT erg = OK;
    switch(S_PA_K(part))
    {
    case EXPONENT:  
        erg = next_part_EXPONENT(part,next);
        break;
    case VECTOR: 
        erg = next_part_VECTOR(part,next);
        break;
    default: 
        erg = error("next_partition:wrong type of partition");
        goto endr_ende;
    };
    return erg;
    ENDR("next_partition");
}

INT next_part_VECTOR_apply(part) OP part;
/* AK 211100 */
{
    INT erg=OK;
    INT res;
/* NYI */
    OP c;
    CTO(PARTITION,"next_part_VECTOR_apply(1)",part);
    c = CALLOCOBJECT();
    SWAP(c,part);
    res = next_part_VECTOR(c,part);
    if (res == LASTPARTITION) { SWAP(c,part); } /* AK 211201 */
    CTO(PARTITION,"next_part_VECTOR_apply(e1)",part);
    FREEALL(c);
    return res;
    ENDR("next_part_VECTOR_apply");
}

INT next_partition_apply(part) OP part;
/* compability */
{
    return next_apply_partition(part);
}

INT next_apply_partition(part) OP part;
/* AK V2.0 211100 */
{
    INT erg = OK;
    CTO(PARTITION,"next_apply_partition(1)",part);

    switch(S_PA_K(part))
    {
    case EXPONENT:  
        erg = next_part_EXPONENT_apply(part);
        break;
    case VECTOR: 
        erg = next_part_VECTOR_apply(part);
        break;
    default: 
        erg = error("next_apply_partition:wrong type of partition");
        goto endr_ende;
    };
    return erg;
    ENDR("next_apply_partition");
}



INT next_part_VECTOR(part,next) OP part, next;
/* AK 091086 */ /* Nijenhuis ch. 9 */ 
/* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    OP length;
    INT i,j,m,o;
    INT n,k;
    INT erg = OK;
    INT res;
    CTO(PARTITION,"next_part_VECTOR(1)",part);

    if (S_PA_LI(part) < (INT)1)
        {    
        res = LASTPARTITION;
        goto ende;
        }
    if (S_PA_II(part,(INT)0) > 1)
    /* bsp: 2345 --> 11345 */
    {
        NEW_INTEGER(length,S_PA_LI(part)+1);
        B_KL_PA(VECTOR,length,next);
        M_I_I(1,S_PA_I(next,(INT)0));
        M_I_I(S_PA_II(part,(INT)0)-1,S_PA_I(next,1));
        for (i=2L;i<S_I_I(length);i++)
            M_I_I(S_PA_II(part,(i-1)),S_PA_I(next,i));
        res = OK;
        goto ende;
    };
    for (i=(INT)0;i<S_PA_LI(part);i++)
        if (S_PA_II(part,i) > 1) break;

    if (i == S_PA_LI(part)) {
        res = LASTPARTITION;
        goto ende;
        }


    k = S_PA_LI(part) -i; /* restlaenge */
    m = S_PA_II(part,i);
    n = m - 1 ; /* neuer wert in next */
    j = (i + m)  / n;
    o =(i + m)  % n ;

    if (o == (INT)0) j--;
    length = CALLOCOBJECT();
    M_I_I(    j+k, length);

    B_KL_PA(VECTOR,length,next);
    if (o != (INT)0)
    { 
        M_I_I(o ,S_PA_I(next,(INT)0)); 
        o=1; 
    };

    for (m=o;m<=j;m++) M_I_I(n, S_PA_I(next,m));

    for (;m<S_I_I(length);m++,i++)
        M_I_I(S_PA_II(part,i+1),S_PA_I(next,m));
    res = OK;
ende:
    return res;
    ENDR("next_part_VECTOR");
}

INT next_part_EXPONENT(part,next) OP part,next;
/* AK 150888 */ /* AK 060789 V1.0 */ /* AK 121190 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT l = S_PA_LI(part);
    INT i,index=(INT)0,k;
    INT summe;
    INT value;
    INT erg =OK;
    if (l == (INT)0)
        return(LASTPARTITION);

    if (S_PA_II(part,(INT)0) == l)
        return(LASTPARTITION);
    /* part = n 0 0 0 0 0 0 ... */

    B_KS_PA(EXPONENT,CALLOCOBJECT(),next);
    m_il_v(l--,S_PA_S(next));
    C_O_K(S_PA_S(next),INTEGERVECTOR);

    M_I_I(0,S_PA_I(next,(INT)0));
    for (i=1;i<=l;i++)
    {
        k = S_PA_II(part,i);
        M_I_I(k,S_PA_I(next,i));
        if (k>(INT)0) {
            index=i++;
            break;
        };
    }
    memcpy(    (char *)S_PA_I(next,i),
        (char *)S_PA_I(part,i),
        (int) (l-i+1)*sizeof(struct object) );

    summe = S_PA_II(part,(INT)0);

    /* an der stelle index wird der index um eins decrementiert */
    summe = summe + index + 1;
    M_I_I(S_PA_II(part,index)-1, S_PA_I(next,index));
    /* nun nach rechts wieder aufbauen */
    for (i=index-1;i>=(INT)0;i--)
    {
        value = summe / (i+1);
        M_I_I(value,S_PA_I(next,i));
        summe = summe % (i+1);

        if (summe == (INT)0) break;
        i = summe;
    }
    ENDR("next_part_EXPONENT");
}

INT next_part_EXPONENT_apply(part) OP part;
/* AK V2.0 211100 */
{
    INT l = S_PA_LI(part);
    INT i,index=(INT)0,k;
    INT summe;
    INT value;
    if (l == (INT)0)
        return(LASTPARTITION);

    if (S_PA_II(part,(INT)0) == l)
        return(LASTPARTITION);
    /* part = n 0 0 0 0 0 0 ... */

    for (i=1;i<=l;i++)
    {
        k = S_PA_II(part,i);
        if (k>(INT)0) {
            index=i++;
            break;
        };
    }

    summe = S_PA_II(part,(INT)0);
    M_I_I(0,S_PA_I(part,(INT)0));

    /* an der stelle index wird der index um eins decrementiert */
    summe = summe + index + 1;
    M_I_I(S_PA_II(part,index)-1, S_PA_I(part,index));
    /* nun nach rechts wieder aufbauen */
    for (i=index-1;i>=(INT)0;i--)
    {
        value = summe / (i+1);
        M_I_I(value,S_PA_I(part,i));
        summe = summe % (i+1);

        if (summe == (INT)0) break;
        i = summe;
    }
    return(OK);
}



INT numberofpart_i(n) OP n;
/* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/*  return the number of partitions 
    as an INT */
{
    OP zw;
    INT i;
    INT erg = OK;

    CTO(INTEGER,"numberofpart_i(1)",n);
    SYMCHECK(S_I_I(n) < 0,"numberofpart_i: parameter < 0");
    
    zw=CALLOCOBJECT();
    erg += numberofpart(n,zw);
    SYMCHECK(S_O_K(zw)!=INTEGER,"numberofpart_i:result too big");
    i=S_I_I(zw);
    FREEALL(zw);
    return(i);

    ENDR("numberofpart_i");
}


INT numberofselfconjugatepart(a,c) OP a,c;
/* AK 231202 */
/* computes the number of self conjugate partitions
   using the fact that his number is equal to the number of partitions with
   distinct odd parts
*/
/* using generating function */
{
    INT erg =OK,ai;
    CTO(INTEGER,"numberofselfconjugatepart(1)",a);
    ai = S_I_I(a);
    if (ai <0) erg += m_i_i(0,c);
    else if (ai <= 1) erg += m_i_i(1,c);  
    else if (ai == 2) erg += m_i_i(0,c);  
    else {
        OP v = CALLOCOBJECT();
        INT i,j;
        m_il_nv(ai+1,v);
        M_I_I(1,S_V_I(v,0));
        M_I_I(1,S_V_I(v,1));
        for (i=3;i<=ai;i+=2)
            {
            for (j=S_V_LI(v)-1;j>=i;j--)
                ADD_APPLY(S_V_I(v,j-i),S_V_I(v,j));
            }
    
        SWAP(S_V_I(v,ai),c);
        FREEALL(v);
        }
    ENDR("numberofselfconjugatepart");
}

INT numberofparts_ge(a,b,c) OP a,b,c;
/* number of partitions of a with maximal part >=b */
/* AK 180803 */
{
    INT erg = OK;
    CTO(INTEGER,"numberofparts_ge(1)",a);
    CTO(INTEGER,"numberofparts_ge(2)",b);
    SYMCHECK(S_I_I(a) < 0,"numberofparts_ge(1>=0)");
    if (S_I_I(b)<=0) 
        erg += numberofpart(a,c);
    else if (GT(b,a)) 
        erg += m_i_i(0,c);
    else {
        OP ai,bi,ci;
        CALLOCOBJECT3(ai,bi,ci);
        COPY(b,bi);
        COPY(a,ai);
        erg += m_i_i(0,c);
        while (LE(bi,ai)) {
            numberofparts_exact_parts(ai,bi,ci);
            ADD_APPLY(ci,c);
            INC(bi);    
            }
        FREEALL3(ai,bi,ci);
        }
    ENDR("numberofparts_ge");
}


INT numberofparts_le_parts(a,b,c) OP a,b,c;
/* number of partitions of a with maximal b parts */
/* using generating function */
/* AK 230103 */
{
    INT erg = OK;
    CTO(INTEGER,"numberofparts_le_parts(1)",a);
    CTO(INTEGER,"numberofparts_le_parts(2)",b);
    SYMCHECK(S_I_I(a) < 0,"numberofparts_le_parts(1>=0)");
    SYMCHECK(S_I_I(b) <0,"numberofparts_le_parts(2>=0)");
    {
    if (EQ(a,b) ) numberofpart(a,c);
    else if (NULLP(b)) m_i_i(0,c);
    else if (EINSP(b)) m_i_i(1,c);
    else {
        OP v,v2;
        INT i,j,k,ai = S_I_I(a), bi=S_I_I(b);
        if (nb_e == NULL) 
            {
            nb_e = CALLOCOBJECT();
            m_il_v(bi+1,nb_e);
            }
        else if (S_V_LI(nb_e) > bi) 
            {
            OP nv = S_V_I(nb_e,bi);
            if (not EMPTYP(nv))
                {
                if (S_V_LI(nv) > ai) { CLEVER_COPY(S_V_I(nv,ai),c); goto endr_ende; }
                else FREESELF(nv); 
                }
            }
        else  
            {
            inc_vector_co(nb_e,bi);
            }
        v = CALLOCOBJECT();
        v2 = CALLOCOBJECT();
        m_il_nv(ai+1,v);
        m_il_v(ai+1,v2);
        for (i=0;i<=ai;i++) 
            M_I_I(1,S_V_I(v,i));
        for (i=2;i<=bi;i++)  
            {
            m_il_nv(ai+1,v2);
            for (j=i;j<=ai;j+=i)
                for (k=ai;k>=j;k--)
                    ADD_APPLY(S_V_I(v,k-j),S_V_I(v2,k));
            ADD_APPLY(v2,v);
            }
        CLEVER_COPY(S_V_I(v,ai),c);
        SWAP(v,S_V_I(nb_e,bi));
        FREEALL(v);
        FREEALL(v2);
        }
    }
    ENDR("numberofparts_le_parts");
}

INT numberofparts_exact_parts(a,b,c) OP a,b,c; 
/* number of partitions of a with exact b parts */
/* using generating function */
/* AK 230103 */
{
    INT erg = OK;
    CTO(INTEGER,"numberofparts_exact_parts(1)",a);
    CTO(INTEGER,"numberofparts_exact_parts(2)",b);
    SYMCHECK(S_I_I(a) < 0,"numberofparts_exact_parts(1>=0)");
    SYMCHECK(S_I_I(b) <0,"numberofparts_exact_parts(2>=0)");
    {
    if (EQ(a,b) ) m_i_i(1,c);
    else if (NULLP(b)) m_i_i(0,c);
    else if (LT(a,b)) m_i_i(0,c);
    else {
         INT ai=S_I_I(a),bi=S_I_I(b),i;
         M_I_I(ai-bi,a);
         numberofparts_le_parts(a,b,c);
         M_I_I(ai,a);
         }
    }
    ENDR("numberofparts_exact_parts");
}


static int rec01();
INT numberofpart(n, res) OP n,res;
/* AK 191202 */
/* bressoud: proofs and confirmations p.37 */
/* input INTEGER n
   output: number of partitions INTEGER or LONGINT */
{
    INT erg = OK;
    OP v;
    CTO(INTEGER,"numberofpart(1)",n);
    if (S_I_I(n) < 0) erg += m_i_i(0,res);
    else {
        INT i;
        v = CALLOCOBJECT();
        erg += m_il_v(S_I_I(n)+1,v);
        for (i=0;i<=S_I_I(n);i++) rec01(i,v);
        SWAP(res,S_V_I(v,S_I_I(n)));
        FREEALL(v);
        }
    ENDR("numberofpart");
}

static int rec01(INT ni, OP vec)
/* to compute number of partitions */
{
    INT erg = OK;
    if (ni<0) return;
    if (not EMPTYP(S_V_I(vec,ni))) return;
    else if (ni<=1) M_I_I(1,S_V_I(vec,ni));
    else {
     
        INT m,og;
        og = ni/3+3;
        m_i_i(0,S_V_I(vec,ni));
     
        for (m=1;m<og;m++)
        {
            INT j;
            j = ni-m*(3*m-1)/2;
            if (j<0) break;
            if (m%2==0) { ADDINVERS_APPLY(S_V_I(vec,j));
                          ADD_APPLY(S_V_I(vec,j),S_V_I(vec,ni));
                          ADDINVERS_APPLY(S_V_I(vec,j));
                        }
            else          ADD_APPLY(S_V_I(vec,j),S_V_I(vec,ni));
            j = ni-m*(3*m+1)/2;
            if (j<0) break;
            if (m%2==0) { ADDINVERS_APPLY(S_V_I(vec,j));
                          ADD_APPLY(S_V_I(vec,j),S_V_I(vec,ni));
                          ADDINVERS_APPLY(S_V_I(vec,j));
                        }
            else          ADD_APPLY(S_V_I(vec,j),S_V_I(vec,ni));
            }
        }
    ENDR("internal:rec01");
}


INT indexofpart(part) OP part;
/* AK 190587 */ 
/* AK 060789 V1.0 */ /* AK 260690 V1.1 */ /* AK 200891 V1.3 */
/* AK 200298 V2.0 */ /* AK 161006 V3.1 */
{
    OP b,a;
    INT i=(INT)-1,erg=OK,comperg;
    CTO(PARTITION,"indexofpart(1)",part);

    a = CALLOCOBJECT();

    if (S_PA_K(part) != VECTOR)
        {
        if (S_PA_K(part) != EXPONENT) 
            {
            erg +=  error("indexofpart:wrong kind of part");
            goto endr_ende;
            }
        erg += t_EXPONENT_VECTOR(part,a);
        i = indexofpart(a);
        erg += freeall(a);
        if (erg != OK) 
            goto endr_ende;
        return i;
        }

    erg += weight_partition(part,a);
    b = CALLOCOBJECT();
    erg += first_partition(a,b);
    i=(INT)0;
    while ((comperg = comp_partition_partition(b,part)) != 0)
        { 
          i++; 
          if (not next_apply(b)) 
            {
            debugprint(b);
            erg += error("indexofpart:ERROR");
            }
        };

    erg += freeall(b);
    erg += freeall(a);
    if (erg != OK) 
        goto endr_ende;
    return(i);
    ENDR("indexofpart");
}



INT ordcen(part,res) OP part, res;
/* AK 010888 ordnung der konjugiertenklasse ist der index des zentralisators */
/* AK 060789 V1.0 */ /* AK 071289 V1.1 */ /* AK 150591 V1.2 */ 
/* AK 200891 V1.3 */
/* AK 200298 V2.0 */ /* AK 161006 V3.1 */
{
    OP h1,h2,zw;
    INT erg = OK;

    CTO(PARTITION,"ordcen",part);

    zw = CALLOCOBJECT();
    h1 = CALLOCOBJECT();
    h2 = CALLOCOBJECT();
    erg += ordcon(part,h2); 
    erg += weight_partition(part,zw);
    erg += fakul(zw,h1);
    erg += ganzdiv(h1,h2,res);  /* ist ganzzahlig */
    erg += freeall(zw); 
    erg += freeall(h2); 
    erg += freeall(h1); 
    ENDR("ordcen");
}


#ifdef TABLEAUXTRUE
INT m_tableaux_polynom(a,c) OP a, c;
/* AK 250789 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */ /* AK 161006 V3.1 */
{
    /* a ist poly of tableaux c wird poly of monom */
    /* AK 060588 */
    OP zeiger;
    INT erg = OK;
    COP("m_tableaux_polynom(2)",c);

    zeiger = a;
    erg += init(POLYNOM,c);
    while( zeiger != NULL)
    {
        OP b = callocobject();
        erg += b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,b);
        M_I_I(1,S_PO_K(b));
        erg += content_tableaux(S_PO_S(zeiger),S_PO_S(b));
        insert(b,c,add_koeff,comp_monomvector_monomvector); 
        zeiger = S_PO_N(zeiger); 
    };
    ENDR("m_tableaux_polynom");
}


INT m_part_tableaux(part,alph,res) OP part,alph,res;
/* AK 070588 */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    return(m_umriss_tableaux(part,alph,res));
}


INT m_umriss_tableaux(umriss,alph,res) OP umriss,alph,res;
/* AK 070588 */
/* erzeugt aus umriss eine liste der tableaus von diesen umriss 
    mit eintraegen 1,2,..,alph */
/* ergebnis ist polynom */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* input: PARTITION object umriss
          INTEGER object alph
   output:
*/
{
    OP a,b;
    OP start; 
    INT i,j; 
    INT erg = OK; 

    CTO(INTEGER,"m_umriss_tableaux",alph);
    PART_CHECK_KIND("m_umriss_tableaux",umriss,VECTOR);

    CE3(umriss,alph,res,m_umriss_tableaux);
    
    erg += init(LIST,res);

    if (S_I_I(alph) < S_PA_LI(umriss)) return(OK);


    a = CALLOCOBJECT();
    b = CALLOCOBJECT();
    erg += copy(umriss,a); 
    erg += m_u_t(a,b);
    /* damit haben wird das tablaux */

    j = zeilenanfang(b,0);
    start = S_T_IJ(b,0,j);


    /* start ist die linke untere ecke */


    for (i= (INT)0; i< S_I_I(alph); i++)
    {
        M_I_I(i+1,start); /* initialisieren */
        erg += m060588(b,alph,res);
    }
    erg += freeall(a);
    erg += freeall(b);
    ENDR("m_umriss_tableaux");
}

static INT m060588(tab,alph,res) OP tab,alph,res;
/* alph ist maximaler eintrag */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    OP b,c;
    INT i,j;
    INT grenze;
    INT lasti,lastj;


again:
    for (i=S_T_HI(tab)-1;i>= 0;i--)
    {
        j=zeilenanfang(tab,i);  /* erster erlaubter index */
        if (not EMPTYP(S_T_IJ(tab,i,j))) break;
    };

    lasti = i;
    /* lasti ist zeile in der letzter eintrag */

    grenze = zeilenende(tab,lasti);

    for (    j=zeilenanfang(tab,lasti);  /* erster erlaubter index */
    j<= grenze; 
        j++)
        if (EMPTYP(S_T_IJ(tab,lasti,j))) break;

    lastj = j;
    /* lastj ist letzter eintrag + 1 */


    if (lastj <=   grenze)  { /* d.h. in der zeile kann noch eingetragen
                    werden */
        INT m;
        m = S_T_IJI(tab,lasti,lastj-1);
        /* m = der letzte eintrag */

        if (lasti == /* s_t_hi(tab)-1*/ 0)  /* letzte zeile */
            M_I_I(m,S_T_IJ(tab,lasti,lastj));
            /* rechts anfuegen der gleichen zahl */
        else if (EMPTYP(S_T_IJ(tab,lasti-1,lastj)))
            /* bei schief unterhalb leer */
            M_I_I(m,S_T_IJ(tab,lasti,lastj));
            /* rechts anfuegen der gleichen zahl */

        else {
            /* schauen ob unterhalb groesserer eintrag */
            m = 
                (S_T_IJI(tab,lasti-1,lastj) >= m ? 
                S_T_IJI(tab,lasti-1,lastj)+1 : m);

            if (m > S_I_I(alph)) goto m060588nein;
            /* kann nicht einsetzen */

            M_I_I(m,S_T_IJ(tab,lasti,lastj));
        };
        goto again;
        /* return(m060588(tab,alph,res)); */
    };

    /* falls in der zeile nicht mehr eingetragen werden kann */

    i = i+1; /* neue zeilenzahl */

    if (i < S_T_HI(tab)) {
        j = zeilenanfang(tab,i);
        /* neue spaltenzahl */

        if (not EMPTYP(s_t_ij(tab,i-1,j)))
        /* unterhalb der neuen
            position ist ein eintrag */
        {
            if (S_T_IJI(tab,i-1,j)+1 > S_I_I(alph))
                goto m060588nein;
            M_I_I(s_t_iji(tab,i-1,j)+1,s_t_ij(tab,i,j));
            return(m060588(tab,alph,res));
        }
        else M_I_I(1,s_t_ij(tab,i,j));
    };
    /* nun sind wir am ende */
    b = CALLOCOBJECT();
    c = CALLOCOBJECT();
    copy(tab,b);
    b_s_po(b,c);
    insert(c,res,NULL,NULL);
    /* jetzt muss versucht werden das naechste tableaux 
    zu bekommen */
m060588nein:
    if (m060588b(tab,alph) == TRUE) /* m060588(tab,alph,res); */ goto again;
    /* d.h noch nicht letztes tableaux */
    return(OK);
}


static INT m060588b(tab,alph) OP tab,alph;
/* es wird versucht das naechste tableaux zu bekommen */
/* AK 200891 V1.3 */ /* AK V2.0 200298 */
{
    INT i,j;
    INT lastj = zeilenanfang(tab,0);
    INT erg = OK;
    for (i=S_T_HI(tab)-1; i>=0 ;i--)
        for (j= S_T_LI(tab)-1;j >= (INT)0; j--)
            if (not EMPTYP(S_T_IJ(tab,i,j)))
                /* es gibt einen eintrag */
                if (i == 0  && j == lastj)
                    return(FALSE);
                    /* wir sind am ende */
                else if (S_T_IJI(tab,i,j) < S_I_I(alph))
                {
                    INC(S_T_IJ(tab,i,j));
                    return(TRUE);
                }
                else 
                {
                    FREESELF(S_T_IJ(tab,i,j));
                    return(m060588b(tab,alph));
                }
    return(FALSE);
    ENDR("m060588b");
}
#endif /* TABLEAUXTRUE */


INT t_augpart_part(a,b) OP a,b;
/* AK 150988 */ /* AK 060789 V1.0 */ /* AK 170190 V1.1 */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT i,s=0;
    INT erg = OK;
    CTO(AUG_PART,"t_augpart_part(1)",a);

    copy(a,b);
    C_O_K(b,PARTITION);
    for (i=(INT)0;i<S_PA_LI(b);i++)
    { 
        M_I_I(S_PA_II(b,i)-i,s_pa_i(b,i));
        if (S_PA_II(b,i)==(INT)0) s++; 
    }
    if (s != (INT)0) /* d.h. 0 am anfang */
    {
        OP nv = callocobject();
        m_il_v(S_PA_LI(b)-s,nv);
        for (i=(INT)0; i<S_V_LI(nv); i++)
            M_I_I(S_PA_II(b,i+s),S_V_I(nv,i));
        freeall(S_PA_S(b)); 
        C_PA_S(b,nv);
    }
    ENDR("t_augpart_part");
}

INT eq_partition_partition(a,b) OP a,b;
/* AK 040202 */
{
    INT erg = OK,l,i;
    char *ac,*bc;
    OP ap,bp;
    CTO(PARTITION,"eq_partition_partition(1)",a);
    CTO(PARTITION,"eq_partition_partition(2)",b);
    if (S_PA_K(a) != S_PA_K(b)) return FALSE;
 
    if (S_PA_K(a) == VECTOR)
        {
        if (S_PA_LI(a) != S_PA_LI(b))
            return FALSE;
        ac = (char *) S_V_S(S_PA_S(a));
        bc = (char *) S_V_S(S_PA_S(b));
        if (memcmp(ac,bc,  sizeof(struct object) * S_PA_LI(a) ) == 0)
            return TRUE;
        else
            return FALSE;
        }
    if (S_PA_K(a) == EXPONENT)
        {
        if (S_PA_LI(a) > S_PA_LI(b)) l=S_PA_LI(b);
        else l = S_PA_LI(a);

/*    this code is slower 
        ac = (char *) S_V_S(S_PA_S(a));
        bc = (char *) S_V_S(S_PA_S(b));
        if (memcmp(ac,bc,  sizeof(struct object) * l ) != 0) return FALSE;
*/
        ap = S_V_S(S_PA_S(a));
        bp = S_V_S(S_PA_S(b));

        for (i=0;i<l;i++,ap++,bp++)
            if (S_I_I(ap) != S_I_I(bp)) return FALSE;
        if (S_PA_LI(a) > l) {
            for (;l<S_PA_LI(a);l++)
                if (S_PA_II(a,l) != 0) return FALSE;
            return TRUE;
            }
        if (S_PA_LI(b) > l) {
            for (;l<S_PA_LI(b);l++)
                if (S_PA_II(b,l) != 0) return FALSE;
            return TRUE;
            }
        return TRUE;
        }
    else
        return (comp_partition_partition(a,b) == 0);
    ENDR("eq_partition_partition");
}

INT eq_partition(a,b) OP a,b;
/* AK 291001 */
{
    INT erg = OK;
    CTO(PARTITION,"eq_partition(1)",a);

    if (S_O_K(b) != PARTITION) return FALSE;
    return eq_partition_partition(a,b);
    ENDR("eq_partition");
}


INT comp_partition_partition(a,b) OP a,b;
/* AK 110488*/ /* AK 060789 V1.0 */ /* AK 191289 V1.1 */
/* AK 070891 V1.3 */
/* AK V2.0 200298 */
{
    INT i;
    INT erg=OK;
    char *ac, *bc;
    CTO(PARTITION,"comp_partition_partition(1)",a);
    CTO(PARTITION,"comp_partition_partition(2)",b);
        
    if (S_PA_K(a) != S_PA_K(b)) 
        {
        erg = error("comp_partition:different kind of partitions");
        goto endr_ende;
        }

    if (S_PA_K(a) == VECTOR )
        {
#ifdef __alpha
        erg =  comp_integervector(S_PA_S(a), S_PA_S(b));
        goto cpende;
#endif /* __alpha */
        ac = (char *) S_V_S(S_PA_S(a));
        bc = (char *) S_V_S(S_PA_S(b));
        if (S_PA_LI(a) == S_PA_LI(b))
            {
            erg =  (INT)memcmp(ac,bc,
                ( sizeof(struct object) * S_PA_LI(a) ));
            goto cpende;
            }
        if (S_PA_LI(a) < S_PA_LI(b))
            {
            erg = (INT) memcmp(ac,bc,
                (sizeof(struct object) * S_PA_LI(a) ));
            if (erg == (INT)0)  erg = (INT)-1;
            goto cpende;
            }
        if (S_PA_LI(a) > S_PA_LI(b))
            {
            erg = (INT)memcmp(ac,bc,
                (sizeof(struct object) * S_PA_LI(b) ));
            if (erg == (INT)0)  erg = (INT)1;
            goto cpende;
            }

        }
    else if (S_PA_K(a) == EXPONENT)
        {
        if (S_PA_LI(a) == S_PA_LI(b)) /* AK 011097 */
            {
            erg =  (INT)memcmp(
                (char *) S_V_S(S_PA_S(a)),
                (char *) S_V_S(S_PA_S(b)),
                                ( sizeof(struct object) * S_PA_LI(a) ));
            goto cpende;
            }
        for (    i=(INT)0; i<S_PA_LI(a); i++)
            {
            if (i >=  S_PA_LI(b) ) 
                {
                if (S_PA_II(a,i) != (INT)0) 
                    {
                    erg = (INT)1;
                    goto cpende;
                    }
                }
            else if (S_PA_II(a,i) > S_PA_II(b,i)) 
                {
                erg = (INT)1;
                goto cpende;
                }
            else if (S_PA_II(a,i) < S_PA_II(b,i)) 
                {
                erg = (INT)-1;
                goto cpende;
                }
            }
        
        for (    ; i<S_PA_LI(b); i++)
            if (S_PA_II(b,i) != (INT)0) 
                {
                erg = (INT)-1; 
                goto cpende;
                }
        }
    erg = (INT)0; goto cpende;
cpende:
    return erg;

    ENDR("comp_partition_partition");
}

INT comp_partition(a,b) OP a,b;
{
    INT erg=OK;
    CTO(PARTITION,"comp_partition(1)",a);
    if (S_O_K(b) == PARTITION)
        return comp_partition_partition(a,b);
    else
        WTO("comp_partition(2)",b);
    ENDR("comp_partition");
}

OP t_exp_vec_app_c = NULL;
INT part_anfang()
/* AK V2.0 040903 */
    {
    INT erg =OK;
    ANFANG_MEMMANAGER(partition_speicher,
                    partition_speicherindex,
                    partition_speichersize,
                    mem_counter_part);
    ENDR("part_anfang");
    }
INT part_ende()
/* AK V2.0 200298 */
    {
    INT erg = OK;
    if (t_exp_vec_app_c!=NULL)
        {
        CTO(INTEGERVECTOR,"part_ende(i1)",t_exp_vec_app_c);
        FREEALL(t_exp_vec_app_c);
        t_exp_vec_app_c=NULL;
        }
    if (nb_e != NULL) { FREEALL(nb_e); nb_e=NULL; }

    ENDE_MEMMANAGER(partition_speicher,
                    partition_speicherindex,
                    partition_speichersize,
                    mem_counter_part,"part speicher not freed");

    if (no_banner != TRUE)
    if (mem_counter_part != (INT)0)
        {
        fprintf(stderr,"mem_counter_part = %ld\n",mem_counter_part);
        erg += error("memory problem with partitions");
        }

    ENDR("part_ende");
    }

INT freepartition(d) struct partition *d;
/* AK 020102 */
{
    INT erg = OK;
    FREE_MEMMANAGER(struct partition *,
                    partition_speicher,
                    partition_speicherindex,
                    partition_speichersize,
                    mem_counter_part,
                    d);
    ENDR("freepartition");
}

INT freeself_partition(a) OP a;
/* AK 110488 */ /* AK 060789 V1.0 */ /* AK 211189 V1.1 */
/* AK 120691 V1.2 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTTO(PARTITION,CHARPARTITION,"freeself_partition(1)",a);

    if (S_O_K(a) == CHARPARTITION) SYM_free(S_PA_S(a));
    else if (S_PA_K(a) == FROBENIUS) FREEALL(S_PA_S(a)); 
    else if (S_PA_K(a) == BITVECTOR) FREEALL(S_PA_S(a)); 
    else /* VECTOR, EXPONENT */
        {
        if (S_PA_S(a) != NULL)
            {
            CTO(INTEGERVECTOR,"freeself_partition(i)",S_PA_S(a));
            FREEALL_INTEGERVECTOR(S_PA_S(a));
            }
        }

    FREEPARTITION(S_O_S(a).ob_partition);
    C_O_K(a,EMPTY);
    ENDR("freeself_partition");
}

INT copy_partition(a,b) OP a,b;
/* AK 060789 V1.0 */ /* AK 191289 V1.1 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTTO(PARTITION,AUG_PART,"copy_partition(1)",a);
    CTO(EMPTY,"copy_partition(2)",b);

    if (S_PA_K(a) == FROBENIUS) {
        B_KS_PA(S_PA_K(a),CALLOCOBJECT(),b);
        COPY(S_PA_S(a), S_PA_S(b));
        goto ende;
        }
    else if (S_PA_K(a) == BITVECTOR)
        {
        B_KS_PA(S_PA_K(a),CALLOCOBJECT(),b);
        COPY(S_PA_S(a), S_PA_S(b));
        goto ende;
        }

    B_KS_PA(S_PA_K(a),CALLOCOBJECT(),b);
    erg += m_il_integervector(S_PA_LI(a),S_PA_S(b));
    memcpy(
        (char *) S_V_S(S_PA_S(b)),
        (char *) S_V_S(S_PA_S(a)),
        (int)(S_PA_LI(a)*sizeof(struct object)) );

    C_O_K(b,S_O_K(a)); /* copy of AUG_PART e.g. */
    C_PA_HASH(b,S_PA_HASH(a)); /* AK 061101 */

ende:
    ENDR("copy_partition");
}


INT tex_partition(part) OP part;
/* AK 101187 */ 
/* output of a PARTITIONobject in format for TeX */
/* AK 060789 V1.0 */ /* AK 170190 V1.1 */
/* AK 070291 V1.2 texout for output */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTO(PARTITION,"tex_partition(1)",part);
    COP("tex_partition:texout",texout);

    if (texmath_yn == 0) /* if not in math mode */
        fprintf(texout,"\\ $ "); 
    
    erg += fprint(texout,part);
    texposition = (INT)0;
    if (texmath_yn == 0) /* if not in math mode */
        fprintf(texout," $\\ ");
    ENDR("tex_partition");
}



static struct partition * callocpartition()
/* AK 060789 V1.0 */ /* AK 170889 malloc statt calloc */ /* AK 170190 V1.1 */
/* AK 070891 V1.3 */
/* AK V2.0 200298 */
{
    struct partition * res;
    INT erg = OK;
    CALLOC_MEMMANAGER(struct partition,
                      partition_speicher,
                      partition_speicherindex,
                      mem_counter_part,
                      res);
    return(res);
    ENDTYP("callocpartition", struct partition * ); 
}



INT inversordcen(part,ergeb) OP part, ergeb;
/* AK 210387 */
/* AK 060789 V1.0 */ /* AK 170190 V1.1 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
/* input: PARTITION object
   output: BRUCH object giving invers order of centraliser of S_n 
           labeled by the partition */
{
    INT i;
    INT erg = OK; /* AK 090692 */
    OP sp;

    PART_CHECK_KIND("inversordcen(1)",part,VECTOR);
    CE2(part,ergeb,inversordcen);

    M_I_I(1,ergeb);
    NEW_INTEGER(sp,1);

    for (i=(INT)0; i<S_PA_LI(part);i++)
    { 
        if (i>(INT)0)
        { 
            if (S_PA_II(part,i) == S_PA_II(part,(i-1)))
                { 
                INC_INTEGER(sp); 
                MULT_APPLY_INTEGER(sp,ergeb); 
                }
            else M_I_I(1,sp); 
        };
        MULT_APPLY_INTEGER(S_PA_I(part,i),ergeb);
    };


    erg += invers_apply(ergeb);
    FREEALL(sp);
    ENDR("inversordcen");
}

INT ordcon(part,res) OP part, res;
/* AK 200387 */ /* AK 060789 */
/* AK 060789 V1.0 */ /* AK 081289 V1.1 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
/* AK V3.1 300306 */
/* input: PARTITION object or
          PERMUTATION object
   output: INTEGER or LONGINT object giving
       the size of the conjugacy class in S_n labled by
       the partition or 
	the size of the class containing the permutation */
{
    INT i;
    INT erg = OK;
    OP ergebnis,sp;
    OP  h1;
    if (S_O_K(part) == CHARPARTITION) /* AK 170593 */
	{
        erg+= ordcon_char(part,res);
	goto endr_ende;
	}
    else if (S_O_K(part)==PERMUTATION) /* AK 300306 */
	{
	OP p;
	p = CALLOCOBJECT();
	erg += zykeltyp_permutation(part,p);
	erg += ordcon(p,res);
	FREEALL(p);
	goto endr_ende;
	}
    PART_CHECK_KIND("ordcon(1)",part,VECTOR);
    CE2(part,res,ordcon);

    NEW_INTEGER(sp,1);
    NEW_INTEGER(ergebnis,1);
    for (i=(INT)0; i<S_PA_LI(part);i++)
    {
        if (i>(INT)0)
        { 
            if (S_PA_II(part,i) == S_PA_II(part,(i-1)))
            {
                INC_INTEGER(sp);
                erg += mult_apply_integer(sp,ergebnis);
            }
            else M_I_I(1,sp);
        };
        erg += mult_apply_integer(S_PA_I(part,i),ergebnis);
    };

    h1 = callocobject();
    erg += weight_partition(part,h1); 
    erg += fakul(h1,sp);
    erg += freeall(h1); 
    erg += ganzdiv(sp,ergebnis,res); /* diese division ist ganzzahlig */

    erg += freeall(sp); 
    erg += freeall(ergebnis); 
    ENDR("ordcon");
}



static INT ordcon_char(part,res) OP part, res;
/* AK V2.0 200298 */
{
    INT i;
    INT erg = OK;
    OP ergebnis,sp;
    OP  h1,h2;
    CTO(CHARPARTITION,"ordcon_char(1)",part);

    if (S_PA_K(part) != VECTOR)
        return ERROR;

    h1 = callocobject();
    h2 = callocobject(); 
    sp=callocobject();
    M_I_I(1,sp);
    ergebnis=callocobject();
    M_I_I(1,ergebnis);
    if (not EMPTYP(res)) 
        if (S_O_K(res) != INTEGER) 
            erg += freeself(res);
    for (i=(INT)0; i<S_PA_CL(part);i++)
    {
        if (i>(INT)0)
        { 
            if (S_PA_CII(part,i) == S_PA_CII(part,(i-1)))
            {
                INC_INTEGER(sp);
                erg += mult_apply_integer(sp,ergebnis);
            }
            else M_I_I(1,sp);
        };
        M_I_I(S_PA_CII(part,i),h2); /* AK 170593 */
        erg += mult_apply_integer(h2,ergebnis);
    };
    erg += weight_partition(part,h1); 
    erg += fakul(h1,sp);
        erg += freeall(h1); 
    erg += ganzdiv(sp,ergebnis,res); /* diese division ist ganzzahlig */

    erg += freeall(sp); 
    erg += freeall(ergebnis); 

    erg += freeall(h2);
    ENDR("ordcon_char");
}



static int mycc(a,b) OP a,b; { return (int)(S_I_I(a)-S_I_I(b)); }

INT m_v_pa(vec,part) OP vec, part;
/* AK 060789 V1.0 */ /* AK 240490 V1.1 */ /* AK 150591 V1.2 */ 
/* AK 070891 V1.3 */
/* AK V2.0 200298 */
/* input: VECTOR object with INTEGER entries >= 0
   output: PARTITION object got by ordering the entries 
           and removinf the zeros */
{
    INT i,j, erg=OK;
    OP self;

    CE2(vec,part,m_v_pa);
    CTTO(VECTOR,INTEGERVECTOR,"m_v_pa",vec);

    if (S_V_LI(vec) == 0) {
null:
        erg += m_il_pa(0,part);
        goto ende;
        }

    self = CALLOCOBJECT(); 
    
    
    if (S_O_K(vec) == VECTOR)
        {
        C_O_K(vec,INTEGERVECTOR);
        erg += copy_integervector(vec,self); 
        C_O_K(vec,VECTOR); /* AK 080502 */
        }
    else
        erg += copy_integervector(vec,self); 

    qsort(S_V_S(self), S_V_LI(self), sizeof(struct object), mycc);

    if (S_V_II(self,0) < 0) { 
        INT err;
        FREEALL(self);
        err=error("m_v_pa: negativ entries"); 
        if (err == ERROR_EXPLAIN) {
            fprintf(stderr,"the wrong input vector was ");
            fprintln(stderr,vec);
            }
        }

    i = 0;
    while ((i<S_V_LI(self)) && (S_V_II(self,i) == 0)) i++;      
    /* eintraege = 0 werden ueberlesen */

    if (i == S_V_LI(self)) 
        { 
        FREEALL(self); 
        goto null;  /* nur nullen */
        }

    
/* die laenge der ergebnis-partition vectorlaenge - anzahl der nullen   */
    if ((S_V_LI(self)-i) == 1)  /* AK 121093 */
        {
        j = S_V_II(self,i);
        erg += m_il_v(1,self);
        M_I_I(j,S_V_I(self,(INT)0));
        }
    else    {
        for (j=0;i<S_V_LI(self);j++,i++)
            M_I_I(S_V_II(self,i),S_V_I(self,j));
        M_I_I(j,S_V_L(self));
        }

    C_O_K(self,INTEGERVECTOR);
    B_KS_PA(VECTOR,self,part);    /* part is the resulting partition object  */
ende:
    ENDR("m_v_pa");
}

INT m_int_pa(i,result) INT i; OP result;
/* AK V2.0 200298 */
{
    OP c;
    INT erg = OK;
    COP("m_int_pa(2)",result);
    SYMCHECK((i < 0),"m_int_pa:integer < 0");
    c=CALLOCOBJECT();
    M_I_I(i,c);
    erg += b_i_pa(c,result);
    ENDR("m_int_pa");
}

INT m_i_pa(i,result) OP i,result;
/* AK 280890 V1.1 */ /* AK 150591 V1.2 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
/* input: INTEGER object i
   output: PARTITION object [i] in VECTOR notation */
/* i and result may be equal */
/* i >= 0 */
/* i == 0 ==> part = [] */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    COP("m_i_pa(2)",result);
    CTO(INTEGER,"m_i_pa(1)",i);
    SYMCHECK((S_I_I(i) < 0),"m_i_pa:integer < 0");
    {
    OP c;
    c = CALLOCOBJECT();
    M_I_I(S_I_I(i),c);
    erg += b_i_pa(c,result);
    }
    ENDR("m_i_pa");
}


INT b_i_pa(integer,res) OP integer,res;
/* AK 140687 */ /* Bsp: 5 --> [5] */
/* AK 060789 V1.0 */ /* AK 280890 V1.1 */ /* AK 070891 V1.3 */
/* AK 200298 V2.0 */
/* input: INTEGER object integer
   output: PARTITION object [i] in VECTOR notation */
/* integer becomes a part of res */
/* integer >= 0 */
/* integer == 0 ==> part = [] */
/* AK 210704 V3.0 */
{
    INT erg = OK;
    COP("b_i_pa(2)",res);
    CTO(INTEGER,"b_i_pa(1)",integer);
    SYMCHECK((S_I_I(integer) < 0),"b_i_pa(1):integer < 0");
    SYMCHECK((integer == res),"b_i_pa(1,2):identical objects");
        
    {
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),res);
    if (S_I_I(integer) > 0)
        erg += b_o_v(integer,S_PA_S(res));
    else
        {
        erg += m_il_v(0,S_PA_S(res));
        FREEALL(integer);
        }
    C_O_K(S_PA_S(res),INTEGERVECTOR);
    }

    ENDR("b_i_pa");
}



INT m_ks_pa(kind,self,ergebnis) OP self,ergebnis; OBJECTKIND kind;
/* make_kind.self_partition */
/* AK 300590 V1.1 */ /* AK 070891 V1.3 */
/* AK V2.0 200298 */
/* self and ergebnis may be equal */
{
    OP s = NULL;
    INT erg = OK;
    COP("m_ks_pa(3)",ergebnis);
    if (self != NULL) { 
        s = CALLOCOBJECT();
        erg += copy(self,s); 
        }
    erg += b_ks_pa(kind,s,ergebnis);
    ENDR("m_ks_pa");
}

INT b_ks_pa(kind,self,c) OP self,c; OBJECTKIND kind;
/* build_kind_self_partition */ /* AK 060789 V1.0 */ /* AK 300590 V1.1 */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    OBJECTSELF d;
    INT erg = OK;
    COP("b_ks_pa(3)",c);
    
    d.ob_partition = callocpartition();
    erg += b_ks_o(PARTITION, d, c);
    C_PA_K(c,kind); 
    C_PA_S(c,self); 
    C_PA_HASH(c,-1);
    if (kind == VECTOR) 
        { 
        if (VECTORP(self)) C_O_K(self,INTEGERVECTOR); /* AK 011101 */
        }
    else if (kind == EXPONENT) 
        { 
        if (VECTORP(self)) C_O_K(self,INTEGERVECTOR); /* AK 011101 */
        }
    
    ENDR("b_ks_pa");
}


INT m_kl_pa(a,b,c) OBJECTKIND a; OP b,c;
/* AK 060789 V1.0 */ /* AK 280890 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTO(INTEGER,"m_kl_pa(2)",b);
    erg += b_ks_pa(a,callocobject(),c) ;
    erg += m_l_v(b,S_PA_S(c));
    C_O_K(S_PA_S(c), INTEGERVECTOR);
    ENDR("m_kl_pa");
}

INT b_kl_pa(a,b,c) OBJECTKIND a; OP b,c;
/* AK 180893 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTO(INTEGER,"b_kl_pa(2)",b);
    erg += b_ks_pa(a,callocobject(),c) ;
    erg += b_l_v(b,S_PA_S(c));
    if (a == VECTOR)
        C_O_K(S_PA_S(c),INTEGERVECTOR);
    else if (a == EXPONENT)
        C_O_K(S_PA_S(c),INTEGERVECTOR);
    ENDR("b_kl_pa");
}


INT dec_partition(a) OP a;
/* AK 060789 V1.0 */ /* AK 261190 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* removes the biggest part of the partition */
/* stops if length = 0 */
{
    INT i;
    INT erg = OK;
    CTO(PARTITION,"dec_partition",a);
    if (S_PA_K(a) == VECTOR) 
        {
        if (S_PA_LI(a) > (INT)0) 
            erg += dec_integervector(S_PA_S(a));
        }
    else if (S_PA_K(a) == EXPONENT)
        {
        for(i=S_PA_LI(a)-1;i>=(INT)0;i--)
            if (S_PA_II(a,i) > (INT)0) 
                {
                M_I_I(S_PA_II(a,i)-1,S_PA_I(a,i));    
                goto endr_ende;
                }
        }
    else
        {
        erg += error("dec_partition:works only for VECTOR, EXPONENT");
        } 
    ENDR("dec_partition");
}

INT lastof_partition(a,b) OP a,b;
/* returns the biggest part of the partition */
/* zero if partition of length 0 */
/* AK 060789 V1.0 */ /* AK 261190 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    CTO(PARTITION,"lastof_partition(1)",a);
    CTO(EMPTY,"lastof_partition(2)",b);

    if (S_PA_K(a) == VECTOR)
        {
        if (S_PA_LI(a) == 0) M_I_I(0,b);
        else M_I_I(S_PA_II(a,S_PA_LI(a)-1),b);
        }
    else if (S_PA_K(a) == EXPONENT)
        {
        INT i;
        M_I_I(0,b);
        for (i=S_PA_LI(a)-1; i>=0; i--)
            if (S_PA_II(a,i) > 0) { M_I_I(i+1,b); break; }
        }
    else    
        {
        erg += error("lastof_partition works only with VECTOR or EXPONENT type partitions");
        }
    ENDR("lastof_partition");
}



INT length_partition(a,b) OP a,b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* AK 140901 */
/* input: PARTITION object
   output: INTEGER object = number of parts of the partition */
{
    INT erg = OK;
    CTO(PARTITION,"length_partition(1)",a);
    CTO(EMPTY,"length_partition(2)",b);
    
    switch(S_PA_K(a)) {
        case VECTOR:
            erg += length_vector(S_PA_S(a),b);
            break;
        case EXPONENT:
            erg += sum_integervector(S_PA_S(a),b);
            break;
        case FROBENIUS: /* AK 140901 */
            if (S_V_LI(S_V_I(S_PA_S(a),0)) == 0)
                M_I_I(0,b);
            else 
                M_I_I(S_V_II(S_V_I(S_PA_S(a),0),0) +1, b);
            break;
        default:
            erg += error("length_partition: wrong kind of part");
            break;
        }
    ENDR("length_partition");
}



INT weight_partition(a,b) OP a,b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* input: PARTITION object
   output: INTEGER object */
{
    INT i ,res=(INT)0;
    INT erg = OK;
    CTO(EMPTY,"weight_partition(2)",b);
    CTTO(CHARPARTITION,PARTITION,"weight_partition(1)",a);

    if (S_O_K(a) == CHARPARTITION)
        if (S_PA_K(a) == VECTOR) {
            for (i=S_PA_CL(a)-1;i>=(INT)0;i--) 
                res += S_PA_CII(a,i);
            M_I_I(res,b); 
            goto endr_ende;
            }
    
    if (S_PA_K(a) == VECTOR) {
        for (i=S_PA_LI(a)-1;i>=(INT)0;i--) res += S_PA_II(a,i);
        M_I_I(res,b); 
        }
    else if (S_PA_K(a) == EXPONENT) {
        for (i=S_PA_LI(a)-1;i>=(INT)0;i--) res += (i+1) * S_PA_II(a,i);
        M_I_I(res,b); 
        }
    else if (S_PA_K(a) == FROBENIUS)
        {
        OP c = callocobject();
        erg += sum_integervector(S_V_I(S_PA_S(a),0),b);
        erg += sum_integervector(S_V_I(S_PA_S(a),1),c);
        erg += add_apply_integer(c,b);
        erg += freeall(c);
        erg += add_apply_integer(S_V_L(S_V_I(S_PA_S(a),0)),b);
        }
    else     {
        erg += error("weight_partition: wrong kind of part");
        }
    ENDR("weight_partition");
}



INT scan_exponentpartition(c) OP c;
/* AK V2.0 200298 */
{
    INT erg=OK;
    COP("scan_exponentpartition(1)",c);
spa:
    erg += b_ks_pa(EXPONENT,callocobject(),c);
    erg += printeingabe("Please input a partition as vector");
    erg += printeingabe("of integers (multiplicities) >= 0.");
    erg += scan(INTEGERVECTOR,S_PA_S(c));
    if (partitionp(c) != TRUE) /* AK 170692 */
        {
        erg += printeingabe("Sorry, you did not enter a partition");
        erg += printeingabe("please try again.");
        erg += freeself(c);
        goto spa;
        }
    ENDR("scan_exponentpartition");
}


INT scan_partition(c) OP c;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 250291 V1.2 */
/* AK 200891 V1.3 */ 
/* AK V2.0 200298 */
{
    INT erg=OK;
    COP("scan_partition(1)",c);
spa:
    erg += b_ks_pa(VECTOR,callocobject(),c);
    erg += printeingabe("Please input a partition as increasing vector");
    erg += printeingabe("of integers > 0.");
    erg += scan(INTEGERVECTOR,S_PA_S(c));
    if (partitionp(c) != TRUE) /* AK 170692 */
        {
        erg += printeingabe("Sorry, you did not enter a partition");
        erg += printeingabe("please try again.");
        erg += freeself(c);
        goto spa;
        }
    ENDR("scan_partition");
}


INT scan_reversepartition(c) OP c;
/* AK 150703 */
{
    INT erg=OK;
    OP d;
    COP("scan_reversepartition(1)",c);
spa:
    d = CALLOCOBJECT();
    erg += printeingabe("Please input a partition as decreasing vector");
    erg += printeingabe("of integers > 0.");
    erg += scan(INTEGERVECTOR,d);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),c);
    erg += reverse_vector(d,S_PA_S(c));
    FREEALL(d);
    if (partitionp(c) != TRUE) /* AK 170692 */
        {
        erg += printeingabe("Sorry, you did not enter a partition");
        erg += printeingabe("please try again.");
        FREESELF(c);
        goto spa;
        }
    ENDR("scan_partition");
}




OP s_pa_s(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_partition->pa_self); 
    }

INT s_pa_hash(a) OP a;
/* AK 240901 */
    {
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_partition->pa_hash); 
    }

OBJECTKIND s_pa_k(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_partition->pa_kind); 
    }

OP s_pa_i(a,i) OP a; INT i;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    return(s_v_i(s_pa_s(a),i)); 
    }

INT s_pa_ii(a,i) OP a; INT i;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    INT erg = OK;
    CTO(PARTITION,"s_pa_ii",a);
    return(s_v_ii(s_pa_s(a),i)); 
    ENDR("s_pa_ii");
    }

OP s_pa_l(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    INT erg = OK;
    CTO(PARTITION,"s_pa_l",a);
    return(s_v_l(s_pa_s(a))); 
    ENDO("s_pa_l");
    }

INT s_pa_li(a) OP a;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
    { 
    INT erg = OK;
    CTO(PARTITION,"s_pa_li",a);
    return(s_v_li(s_pa_s(a))); 
    ENDR("s_pa_li");
    }

INT c_pa_k(a,b) OP a; OBJECTKIND b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_partition->pa_kind = b; 
    return(OK); 
    }

INT c_pa_s(a,b) OP a,b;
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_partition->pa_self = b; 
    return(OK); 
    }

INT c_pa_hash(a,b) OP a; INT b;
/* AK 240901 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    c.ob_partition->pa_hash = b; 
    return(OK); 
    }
   





INT objectread_partition(filename,part) OP part; FILE *filename;
/* AK 291086 zum einlesen einer partition von einem file */
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT kind;
    INT erg = OK;
    COP("objectread_partition(1)",filename);
    COP("objectread_partition(2)",part);
    fscanf(filename,"%ld",&kind);
    erg += b_ks_pa((OBJECTKIND)kind, callocobject(),part);
    erg += objectread(filename,S_PA_S(part));
    if (S_PA_K(part) == VECTOR) 
        C_O_K(S_PA_S(part),INTEGERVECTOR); 
        /* AK 030502 to be compatible with old data */
    ENDR("objectread_partition");
}

INT objectwrite_partition(filename,part) FILE *filename; OP part;
/* AK 291086 */ /* zum schreiben einer partition auf einen file */
/* AK 060789 V1.0 */ /* AK 200690 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    COP("objectwrite_partition(1)",filename);
    COP("objectwrite_partition(2)",part);
    fprintf(filename,"%ld\n",(INT)PARTITION);
    fprintf(filename,"%ld\n",(INT)S_PA_K(part));
    erg += objectwrite(filename,S_PA_S(part));
    ENDR("objectwrite_partition");
}


INT m_il_pa(i,p) INT i; OP p;
/* AK 130803 */
/* partition object of kind VECTOR of given length with undefined entries
*/
{
    INT erg =OK;
    SYMCHECK(i<0,"m_il_pa: negative length");
    B_KS_PA(VECTOR,CALLOCOBJECT(),p);
    erg += m_il_integervector(i,S_PA_S(p));
    ENDR("m_il_pa");
}

INT t_VECTOR_EXPONENT(von,nach) OP von,nach;
/* AK 190588 */
/* AK 060789 V1.0 */ /* AK 200690 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 020698 */
/* in the exponent noattion the i-th entry of the vector
   contains the number of parts of size i+1


   e.g. 234 --> 011100000  
*/
{
    INT i,w;
    OP l;
    INT erg = OK; 
    PART_CHECK_KIND("t_VECTOR_EXPONENT",von,VECTOR);
    CE2(von,nach,t_VECTOR_EXPONENT);

    l=CALLOCOBJECT();
    PARTITION_WEIGHT(von,w);
    M_I_I(w,l);
    erg += b_ks_pa(EXPONENT,CALLOCOBJECT(),nach);
    erg += b_l_nv(l,S_PA_S(nach));
    C_O_K(S_PA_S(nach),INTEGERVECTOR);

    for (i=(INT)0;i<S_PA_LI(von);i++)
        INC_INTEGER(S_PA_I(nach,S_PA_II(von,i) -(INT)1));

    ENDR("t_VECTOR_EXPONENT");
}

INT t_EXPONENT_VECTOR_apply(a) OP a;
/* AK 051201 */
{
    INT erg = OK;
    INT i,j,ba,s;
    OP c,l,z;
    PART_CHECK_KIND("t_EXPONENT_VECTOR_apply(1)",a,EXPONENT);


    j=(INT)0;ba=0;
    for (i=0,l=S_V_S(S_PA_S(a));i<S_PA_LI(a);i++,l++)
        if (S_I_I(l)>0) { j += S_I_I(l); ba=i; }

/* ba is the last non zero entry in a */
    if (t_exp_vec_app_c==NULL)
        {
        NEW_INTEGERVECTOR(c,j);
        t_exp_vec_app_c = c;
        }
    else {
        c = t_exp_vec_app_c;
        if (j > S_V_LI(c)) 
            erg += inc_vector_co(c,j-S_V_LI(c)+5);
        }
    s=j;
    for (i=0,z=S_V_S(c);i<=ba;i++)
        if (S_PA_II(a,i)>0)
            for (j=(INT)0;j<S_PA_II(a,i);j++)
                {
                M_I_I(i+1,z);
                z++;
                }

    C_PA_K(a,VECTOR);
    if (S_PA_LI(a) < s) 
        inc_vector_co(S_PA_S(a), s - S_PA_LI(a));
        
    memcpy(S_V_S(S_PA_S(a)),S_V_S(c), s * sizeof(struct object));
    M_I_I(s,S_PA_L(a));
    ENDR("t_EXPONENT_VECTOR_apply");
}


INT t_EXPONENT_VECTOR(a,b) OP a,b;
/* AK 160988 */ /* AK 060789 V1.0 */ /* AK 200690 V1.1 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
{

    INT i,j,z=(INT)0,ba;
    INT erg = OK;
    OP l;
    PART_CHECK_KIND("t_EXPONENT_VECTOR(1)",a,EXPONENT);
    if (a==b) {
        erg += t_EXPONENT_VECTOR_apply(a); 
        goto ende;
        }

    j=(INT)0;ba=0; 
    for (i=(INT)0;i<S_PA_LI(a);i++) 
        if (S_PA_II(a,i)>0) { j += S_PA_II(a,i); ba=i; }
/* ba is the last non zero entry in a */
    l = CALLOCOBJECT();
    M_I_I(j,l);
    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),b);
    erg += b_l_v(l,S_PA_S(b));
    C_O_K(S_PA_S(b), INTEGERVECTOR);
    for (i=(INT)0;i<=ba;i++)
        if (S_PA_II(a,i)>0) 
            for (j=(INT)0;j<S_PA_II(a,i);j++)
            {
                M_I_I(i+(INT)1,S_PA_I(b,z));
                z++;
            };
ende:
    ENDR("t_EXPONENT_VECTOR");
}



INT makevectorofpart(n,vec) OP n,vec;
/* AK 200587 */ /* AK 060789 V1.0 */ /* AK 081289 V1.1 */ /* AK 130691 V1.2 */
/* AK 200891 V1.3 */ /* AK V2.0 200298 */
/* input: INTEGER object n
   output: VECTOR object with PARTITION objects of weight n */
/* n and vec may be equal */
{
    INT i,erg =OK;
    OP l;
    CTO(INTEGER,"makevectorofpart(1)",n);
    SYMCHECK((S_I_I(n) < (INT)0),"makevectorofpart:input < 0");

    CE2(n,vec,makevectorofpart);
    l=callocobject();
    erg += numberofpart(n,l);
    erg += b_l_v(l,vec);
    erg += first_partition(n,S_V_I(vec,(INT)0));
    for (i=(INT)1;i<S_V_LI(vec);i++)
        erg += next_part_VECTOR(S_V_I(vec,(i-1)),S_V_I(vec,i));

    ENDR("makevectorofpart");
}

INT makevectorofpart_EXPONENT(n,vec) OP n,vec;
/* AK 211100 */
/* input: INTEGER object n
   output: VECTOR object with PARTITION objects of weight n of type EXPONENT*/
/* n and vec may be equal */
{
    INT i,erg =OK;
    OP l;
    CTO(INTEGER,"makevectorofpart_EXPONENT(1)",n);
    SYMCHECK(S_I_I(n) < 0,"makevectorofpart_EXPONENT:input < 0");
    CE2(n,vec,makevectorofpart_EXPONENT);

    l=CALLOCOBJECT();
    erg += numberofpart(n,l);
    erg += b_l_v(l,vec);
    erg += first_part_EXPONENT(n,S_V_I(vec,(INT)0));
    for (i=1;i<S_V_LI(vec);i++)
        erg += next_part_EXPONENT(S_V_I(vec,(i-1)),S_V_I(vec,i));


    ENDR("makevectorofpart_EXPONENT");
}





INT weight_augpart(a,b) OP a,b;
/* AK 160988 */ /* AK 060789 V1.0 */ /* AK 120390 V1.1 */ /* AK 130691 V1.2 */
/* AK 200891 V1.3 */
/* AK V2.0 200298 */
{
    INT i,k=(INT)0;
    INT erg = OK;
    CTO(AUG_PART,"weight_augpart(1)",a);
    
    for (i=S_PA_LI(a)-1;i>=(INT)0;i--) k = k + S_PA_II(a,i) - i;

    M_I_I(k,b);
    ENDR("weight_augpart");
}



INT contain_comp_part(a,b) OP a,b;
/* AK V2.0 090298 */
/* true if a sub b */
{
    INT i;
    if (S_PA_LI(a) > S_PA_LI(b)) return FALSE;
    for (i=0;i<S_PA_LI(a);i++)
        {
        if (S_PA_II(a,S_PA_LI(a)-1-i) > S_PA_II(b,S_PA_LI(b)-1-i)) return FALSE;
        }
    return TRUE;
}

INT length_comp_part(a,b) OP a,b;
/* returns 0 if equal length
   returns >0 if length(a) > length(b)
   returns <0 if length(a) < length(b)
*/
/* AK 161001 */
{
    INT erg = OK;
    PART_CHECK_KIND("length_comp_part(1)",a,VECTOR);
    PART_CHECK_KIND("length_comp_part(2)",b,VECTOR);
    return S_PA_LI(a) - S_PA_LI(b);
    ENDR("length_comp_part");
}

INT maxpart_comp_part(a,b) OP a,b;
/* returns 0 if equal maximal part
   returns >0 if maximal part(a) > maximal part(b)
   returns <0 if maximal part(a) < maximal part(b)
*/
/* AK 191001 */
{
    INT erg = OK;
    PART_CHECK_KIND("maxpart_comp_part(1)",a,VECTOR);
    PART_CHECK_KIND("maxpart_comp_part(2)",b,VECTOR);
    if (S_PA_LI(a) == 0)
        {
        if (S_PA_LI(b) == 0) return 0;
        else return -1;
        }
    if (S_PA_LI(b) == 0) return 1;
    return S_PA_II(a,S_PA_LI(a)-1)  - S_PA_II(b,S_PA_LI(b)-1);
    ENDR("maxpart_comp_part");
}


INT sub_comp_part(a,b) OP a,b;
/* returns 0 on equal
           1 if a bigger according to containment
      -1 if smaller
          NONCOMPARABLE else 
*/
/* AK V2.0 250298 */
/* a and b may be equal */
{
    INT erg=0,i,j;
    PART_CHECK_KIND("sub_comp_part",a,VECTOR);
    PART_CHECK_KIND("sub_comp_part",b,VECTOR);

    for (i=S_PA_LI(a)-1, j=S_PA_LI(b)-1;i>=0;i--,j--)
        {
        if (j<(INT)0) /* length of a > length of b */
            {
            if (erg == -1) return NONCOMPARABLE;
            return 1;
            }
        if (S_PA_II(a,i) > S_PA_II(b,j))
            {
            if (erg == -1) return NONCOMPARABLE;
            erg = 1;
            continue;
            }
         if (S_PA_II(a,i) < S_PA_II(b,j))
            {
            if (erg == 1) return NONCOMPARABLE;
            erg = -1;
            continue;
            }
        } 
    if (j >= 0)
        {
            return -1;
        }
    return erg;
    ENDR("sub_comp_part");
}

INT dom_comp_part(a,b) OP a,b;
/* returns 0 on equal
           1 if a bigger according dominance
           -1     smaller
           NONCOMPARABLE if not comparable */
/* AK 140591 V1.2 */ /* AK 200891 V1.3 */
/* AK V2.0 200298 */
/* a and b may be equal */
/* AK V3.1 131006 */
{
    INT i,j,s1,s2;
    INT l,erg = (INT)0;    
    PART_CHECK_KIND("dom_comp_part",a,VECTOR);
    PART_CHECK_KIND("dom_comp_part",b,VECTOR);

    l = (S_PA_LI(a) > S_PA_LI(b)) ?  S_PA_LI(a) : S_PA_LI(b) ;
    /* l is the length of the longer partition */
    for (i=(INT)0; i<l ; i++)
        /* all partial sums */
        {
        s1 = s2 = (INT)0;
        for (j=(INT)0;j<=i;j++)
            {
            if (j < S_PA_LI(a)) s1 += S_PA_II(a,S_PA_LI(a)-1-j);
            if (j < S_PA_LI(b)) s2 += S_PA_II(b,S_PA_LI(b)-1-j);
            }
    /* s1 is partialsum of a 
           s2 is partialsum of b */
        if (erg == (INT)0) 
            {
            if (s1 > s2) erg = (INT)1;
            if (s1 < s2) erg = (INT)-1;
            }
        else if ( erg == 1 )
            {
            if (s1 < s2) return NONCOMPARABLE; /* not comparable */
            }
        else if ( erg == -1 )
            {
            if (s1 > s2) return NONCOMPARABLE; /* not comparable */
            }
        else    {
            erg = error("dom_comp_part:internal error");
            goto endr_ende;
            }
        }
    return erg;
    ENDR("dom_comp_part");
    }




INT even_partition(a,b) OP a,b;
/* AK V2.0 200298 */
/* AK V3.1 131006 */
{
    OP c;
    INT erg;
    c = callocobject();
    weight(a,c);
    sub(c,S_PA_L(a),c);
    erg = even(c);
    freeall(c);
    return erg;
}

INT random_part_EXPONENT(n,b) OP n,b;
/* AK V2.0 250298 */
{
    return  random_partition_exponent(n,b);
}

INT random_partition_exponent(n,b) OP n,b;
/* new random partition nijnhuis wilf p.76 */
/* AK 151092 also for longint */
/* AK V2.0 200298 */
/* input: INTEGER object 
   output: PARTITION object of given weight in EXPONENT notation */
/* AK V3.1 131006 */
{
    OP k,z,multi,p,d,m,i,isum,is,i1,j;
    INT nlast;
    INT erg = OK;

    CTO(INTEGER,"random_partition_exponent",n);
    CE2(n,b,random_partition_exponent);

    if (S_I_I(n) < (INT)0) 
        {
        erg +=  error("random_partition_exponent: n < 0");
        goto endr_ende;
        }
    else if (S_I_I(n) == (INT)0)
        {
        erg += first_part_EXPONENT(n,b);
        goto endr_ende;
        }

    CALLOCOBJECT5(z,k,m,p,i);
    CALLOCOBJECT6(i1,j,is,isum,d,multi);

    nlast = 0;
    
    erg += m_l_nv(n,multi);
    erg += m_l_v(n,p);
    /* l10: */ if (S_I_I(n) <= nlast) goto l30;
    /* l20:*/ erg += m_i_i(1,S_V_I(p,(INT)0));
    erg += m_i_i(nlast + (INT)1, m);
    /* erg += add(nlast,cons_eins,m); */
    /* erg += copy_integer(n,nlast); */
    nlast = S_I_I(n);
    if (S_I_I(n) == (INT)1) goto l30;
    for(copy(m,i); le(i,n); inc(i))
        {
        erg += m_i_i((INT)0,isum);
        for (m_i_i(1,d); le(d,i); inc_integer(d) )
            {
            erg += m_i_i((INT)0,is);
            erg += copy(i,i1);
    l24:        erg += sub(i1,d,i1);
            if (lt(i1,cons_null) ) goto l22;
            if (eq(i1,cons_null) ) goto l25;
            erg += add_apply(S_V_I(p,S_I_I(i1)-1),is);
            goto l24;
    l25:        erg += inc(is);
    l22:        erg += mult_apply(d,is);
            erg += add_apply(is,isum);
            }
        erg += ganzdiv(isum,i,S_V_I(p,S_I_I(i)-1));
        }
    l30:     erg += copy(n,m);
        erg += m_i_i((INT)0,k);
    l40:     erg += mult(m,S_V_I(p,S_I_I(m)-1),d);
        erg += random_integer(z,cons_eins,d);
        erg += m_i_i((INT)0,d);
    l110:    erg += inc(d);
    /*l60:*/    erg += copy(m,i1);
        erg += m_i_i((INT)0,j);
    l150:    erg += inc(j);
    /*l70:*/    erg += sub(i1,d,i1);
    /*l80:*/    if (lt(i1,cons_null)) goto l110;
        if (eq(i1,cons_null)) goto l90;
        erg += mult(d,S_V_I(p,S_I_I(i1)-1),is);
        erg += sub(z,is,z); 
    /* l130: */    if (le(z,cons_null)) goto l145;
        goto l150;
    l90:    erg += sub(z,d,z);
    /* l100: */    if (le(z,cons_null)) goto l145;
        goto l110;
    l145:    erg += add_apply(j,S_V_I(multi,S_I_I(d)-1));
        erg += add_apply(j,k);
    /* l160:*/    erg += copy(i1,m);
    /*l170:*/    if (neq(m,cons_null)) goto l40;

    FREEALL5(z,k,m,p,i);
    FREEALL5(i1,j,is,isum,d);

    erg += b_ks_pa(EXPONENT,multi,b); /* do not free multi */
    ENDR("random_partition_exponent");
}


INT random_partition(n,p) OP n,p;
/* AK 230298 V2.0 */
/* input: INTEGER object n
   output: PARTITION object of given weight in VECTOR notation */
/* n and p may be equal */
{
    OP c;
    INT erg = OK;
    CTO(INTEGER,"random_partition(1)",n);
    SYMCHECK(S_I_I(n)<0, "random_partition(1)<0");

    if (S_I_I(n) < 2)
        erg += first_partition(n,p);
    else 
        {
        c = CALLOCOBJECT();
        erg += random_partition_exponent(n,c);
        erg += t_EXPONENT_VECTOR(c,p);
        FREEALL(c);
        }
    ENDR("random_partition");
}


INT t_FROBENIUS_VECTOR(a,b) OP a,b;
/* AK 270603 V2.0 */
{
    INT erg =OK;
    OP l,r;
    INT d,i,k;
    PART_CHECK_KIND("t_FROBENIUS_VECTOR",a,FROBENIUS);
    CE2(a,b,t_FROBENIUS_VECTOR);
    r = S_V_I(S_PA_S(a),0); /* right of main dia */
    l = S_V_I(S_PA_S(a),1); /* left of main dia */
    d = S_V_LI(l); /* durfee size */

    if (d == 0) {
        first_partition(cons_null,b);
        goto endr_ende;
        }
    erg += m_il_pa(S_V_II(l,0)+1, b);

    for (i=0;i<d;i++) m_i_i(S_V_II(r,i)+1+i, S_PA_I(b,S_PA_LI(b)-1-i));


    for (; i<S_PA_LI(b);i++)
        {
        for (k=0;k<d;k++)
            if (S_V_II(l,k)-(d-k-1) <  (i-d+1)) break;
        M_I_I(k, S_PA_I(b,S_PA_LI(b)-1-i));
        }
    
    ENDR("t_FROBENIUS_VECTOR");
}

INT t_VECTOR_FROBENIUS(a,b) OP a,b;
/* AK V2.0 250298 */
{
    return t_VECTOR_FROB(a,b);
}
INT t_VECTOR_FROB(a,b) OP a,b;
/* AK 101292 */
/* AK V2.0 200298 */
{
    INT i,j;
    INT erg = OK;
    OP c;
    PART_CHECK_KIND("t_VECTOR_FROB",a,VECTOR);
    CE2(a,b,t_VECTOR_FROB);

    erg += b_ks_pa(FROBENIUS,callocobject(),b);
    erg += m_il_v(2L,S_PA_S(b));
    if (S_PA_LI(a) == (INT)0)
        {
        erg += m_il_v((INT)0,S_V_I(S_PA_S(b),(INT)0));
        erg += m_il_v((INT)0,S_V_I(S_PA_S(b),1));
        goto endr_ende;
        }
    for (i=(INT)0, j=S_PA_LI(a)-1;(j>=0)&&(S_PA_II(a,j) > i); i++,j--) ;
    erg += m_il_v(i,S_V_I(S_PA_S(b),(INT)0));
    erg += m_il_v(i,S_V_I(S_PA_S(b),1));
    c = callocobject();
    erg += conjugate(a,c);
    for (j=(INT)0;j<S_V_LI(S_V_I(S_PA_S(b),(INT)0));j++)
        {
        erg += m_i_i(S_PA_II(a,S_PA_LI(a)-1-j)-1-j, S_V_I(S_V_I(S_PA_S(b),(INT)0),j));
        erg += m_i_i(S_PA_II(c,S_PA_LI(c)-1-j)-1-j, S_V_I(S_V_I(S_PA_S(b),1),j));
        }
    FREEALL(c);
    ENDR("t_VECTOR_FROB");
}


/* offset necessary */    INT t_PARTITION_CHARPARTITION(a,b) OP a,b;
    /* only for internal use */
    /* AK V2.0 200298 */
{
    INT erg = OK;
    char *v;
    if (a == b) 
        return ERROR;
    if (S_PA_K(a) == FROBENIUS)
        return ERROR;
    erg += freeself(b);
    erg += b_ks_pa(S_PA_K(a), NULL, b);
    erg += t_INTVECTOR_UCHAR(S_PA_S(a), &v);
    C_PA_S(b,(OP)v);
    C_O_K(b,CHARPARTITION);
    return erg;
}


    INT c_PARTITION_CHARPARTITION(a) OP a;
    /* only for internal use */
    /* AK 170593 */
    /* AK V2.0 200298 */
{
    INT erg = OK;
    OP c = callocobject();
    *c = *a;
    C_O_K(a,EMPTY);
    erg += t_PARTITION_CHARPARTITION(c,a);
    erg += freeall(c);
    return erg;
}

    INT c_CHARPARTITION_PARTITION(a) OP a;
    /* only for internal use */
    /* AK 170593 */
{
    INT erg = OK;
    OP c = callocobject();
    *c = *a;
    C_O_K(a,EMPTY);
    erg += t_CHARPARTITION_PARTITION(c,a);
    erg += freeall(c);
    return erg;
}

    INT t_CHARPARTITION_PARTITION(a,b) OP a,b;
    /* only for internal use */
{
    INT erg = OK;
    if (a == b) 
        return ERROR;
    if (S_PA_K(a) == FROBENIUS)
        return ERROR;
    erg += freeself(b);
    erg += b_ks_pa(S_PA_K(a), callocobject(), b);
    erg += t_UCHAR_INTVECTOR(S_PA_S(a),  S_PA_S(b));
    C_O_K(S_PA_S(b),INTEGERVECTOR);
    return erg;
}


INT t_PARTITION_AUGPART(a,b) OP a,b;
/* AK 170593 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    INT i;
    CTO(PARTITION,"t_PARTITION_AUGPART(1)",a);
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    erg += copy(a,b);
    for (i=(INT)0;i<S_PA_LI(a);i++)
        M_I_I(S_PA_II(a,i)+i,S_PA_I(b,i));
    C_O_K(b,AUG_PART);
    ENDR("t_PARTITION_AUGPART");
}

INT c_CHARAUGPART_CHARPARTITION(a) OP a;
/* AK 170593 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    INT i;
    if (S_O_K(a) != CHAR_AUG_PART)
        return ERROR;
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    for (i=(INT)0;i<S_PA_CL(a);i++)
         S_PA_CII(a,i) = S_PA_CII(a,i)-i;
    C_O_K(a,CHARPARTITION);
    return erg;
}

INT c_CHARPARTITION_CHARAUGPART(a) OP a;
/* AK 170593 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    INT i;
    if (S_O_K(a) != CHARPARTITION)
        return ERROR;
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    for (i=(INT)0;i<S_PA_CL(a);i++)
         S_PA_CII(a,i) = S_PA_CII(a,i)+i;
    C_O_K(a,CHAR_AUG_PART);
    return erg;
}
INT c_AUGPART_PARTITION(a) OP a;
/* AK 170593 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    INT i;
    if (S_O_K(a) != AUG_PART)
        return ERROR;
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    for (i=(INT)0;i<S_PA_LI(a);i++)
        M_I_I(S_PA_II(a,i)-i, S_PA_I(a,i));
    C_O_K(a,PARTITION);
    C_O_K(S_PA_S(a),INTEGERVECTOR);
    return erg;
}

INT c_PARTITION_AUGPART(a) OP a;
/* AK 170593 */
/* AK V2.0 200298 */
{
    INT erg = OK;
    INT i;
    if (S_O_K(a) != PARTITION)
        return ERROR;
    if (S_PA_K(a) != VECTOR)
        return ERROR;
    for (i=(INT)0;i<S_PA_LI(a);i++)
        M_I_I(S_PA_II(a,i)+i, S_PA_I(a,i));
    C_O_K(a,AUG_PART);
    return erg;
}




struct axelclaude {
    int  nbl, nbc, contrib,rang;
    int *pdl, *pdc;
    int *mat;
    int *ligne_mat; 
};


INT row_column_matrices(a,c,e) OP a,c,e;
/* AK 131093 CP 031293 */
/* AK V2.0 200298 */
{
    int i;
    OP d;
    INT erg = OK;
    struct axelclaude aa;

    if (S_O_K(a) == PARTITION)
        {
    if (S_PA_K(a) != VECTOR)
        return error("row_column_matrices requires VECTOR partitions");
        a = S_PA_S(a);
        }
    if (S_O_K(c) == PARTITION)
        {
    if (S_PA_K(c) != VECTOR)
        return error("row_column_matrices requires VECTOR partitions");
        c = S_PA_S(c);
        }

    if ((not VECTORP(a)) || (not VECTORP(c)))
        {
        WTT("row_column_matrices",a,c);
        goto endr_ende;
        }

    d = callocobject();
    aa.nbl=S_V_LI(a)+1; 
    aa.nbc=S_V_LI(c)+1;
    aa.pdl = (int *) SYM_calloc(aa.nbl, sizeof(int));
    aa.pdc = (int *) SYM_calloc(aa.nbc, sizeof(int));
    aa.ligne_mat = (int *) SYM_calloc(aa.nbc, sizeof(int));
    aa.mat = (int *) SYM_calloc(aa.nbc * aa.nbl, sizeof(int));

    for(i=0;i<S_V_LI(a);i++)  aa.pdl[i+1]= S_V_II(a,i);
    for(i=0;i<S_V_LI(c);i++)  aa.pdc[i+1]= S_V_II(c,i);
    erg += m_ilih_m(aa.nbc-1,aa.nbl-1,d);
    erg += m_il_v((INT)0,e);
    aa.contrib=aa.pdl[1];
    aa.rang=1;
    repartir(&aa,aa.rang,aa.contrib,aa.pdc,aa.ligne_mat,aa.nbc,d,e);
    SYM_free(aa.pdl);
    SYM_free(aa.pdc);
    SYM_free(aa.ligne_mat);
    SYM_free(aa.mat);
    FREEALL(d);
    ENDR("row_column_matrices");
}

/******************************************************************
 *          passage de aaaaaa a abbbbbb                           *
 ******************************************************************/
static int remplir(contrib,pdc,v,d,l) int contrib, d, l, pdc[], v[];
{
    int i, x;
    for(i=d;i<=l;i++) v[i] = 0;
    i = l; 
    x = contrib;
    while(x>0) {
        if(i==d-1) return 0;
        if(x>=pdc[i]) { 
            v[i]=pdc[i]; 
            x -= pdc[i--];
        }
        else { 
            v[i] = x; 
            x = 0;
        }
    }
    return 1;
}

/**********************************************************************
 *        partitions avec contraintes                                 *
 **********************************************************************/
static void repartir(aa,rang,contrib,pdc,v,lv,dd,e)  OP dd,e;
    int rang, contrib, lv, pdc[], v[];
    struct axelclaude *aa;
{
    int d,l,i;
    int *w, *pdcv;
    pdcv = (int *) SYM_calloc(lv,sizeof(int));
    w = (int *) SYM_calloc(lv,sizeof(int));
    d=1; 
    l=lv-1;
    while(1) {
        remplir(contrib,pdc,v,d,l);
        utiliser(aa,rang,v,lv,dd,e);
        if(rang<aa->nbl-1) {
            for(i=1;i<=l;i++) pdcv[i]=pdc[i]-v[i];
            repartir(aa,rang+1,aa->pdl[rang+1],pdcv,w,lv,dd,e);
        }
        i=l-1; 
        contrib = v[l];
        while(i>0) if(v[i]==pdc[i]) contrib += v[i--];
        else if(contrib==0) contrib=v[i--]; 
        else break;
        if(i>0) { 
            v[i]++; 
            contrib--; 
            d=i+1; 
            continue; 
        }
        else break;
    }
    SYM_free(pdcv);
    SYM_free(w);
}

/*******************************************************************
 *         exploitation d'une ligne construite                     *
 *******************************************************************/
static void utiliser(aa,rang,v,lv,d,e)  OP d,e; struct axelclaude *aa; int rang,v[], lv;
{
    int i, j;
    /* for(i=1;i<lv;i++) aa->mat[rang][i]=v[i]; */
    for(i=1;i<lv;i++) aa->mat[(rang*aa->nbc) +i]=v[i];

    if(rang==aa->nbl-1) {
        inc(e);
        for(i=1;i<aa->nbl;i++) {
        for(j=1;j<lv;j++)   
            M_I_I(aa->mat[(i*aa->nbc) +j],S_M_IJ(d,i-1,j-1) );
        }
        copy(d,S_V_I(e,S_V_LI(e)-1));

    }
}


static INT sscan_partition_co();
INT sscan_reversepartition(t,a) OP a; char *t;
{   
    INT erg = OK;
    OP d;
    sscan_partition_co(t,a);
    d=CALLOCOBJECT();
    reverse_vector(S_PA_S(a),d);
    COPY(d,S_PA_S(a));
    FREEALL(d);
    SYMCHECK (not partitionp(a),"sscan_reversepartition:no partition entered");
    ENDR("sscan_reversepartition");
}
INT sscan_partition(t,a) OP a; char *t;
{   
    INT erg = OK;
    sscan_partition_co(t,a);
    SYMCHECK (not partitionp(a),"sscan_reversepartition:no partition entered");
    ENDR("sscan_partition");
}

static INT sscan_partition_co(t,a) OP a; char *t;
/* AK 050194 to read partition from string
    format [1,2,3,23,23,33]
*/
/* AK 230298 V2.0 */
{
    INT i,n,erg = OK;
    int SYM_isdigit();
    char *v,*w;

    COP("sscan_partition(1)",t);
    COP("sscan_partition(2)",a);
    v = t;
    while (*v == ' ') v++;
    if (*v != '[')
        {erg = ERROR; goto spe;}
    w = v; n = (INT)1;
    /* now we count the number of parts */
    w++;
    while (*w != ']')
        {
        if (*w == ',') n++;
        else if (not SYM_isdigit(*w))
            {erg = ERROR; goto spe;}
        w++;
        }
    /* n is the number of parts */
    b_ks_pa(VECTOR,callocobject(),a);
    m_il_v(n,S_PA_S(a));
    C_O_K(S_PA_S(a),INTEGERVECTOR);
    w = v;
    w++;
    for (i=(INT)0; i<n; i++)
        {
        erg += sscan(w,INTEGER,S_PA_I(a,i));
        if (erg != OK) goto spe;

        while (SYM_isdigit(*w)) w++;
        w++;
        }
    spe:
    if (erg != OK)
        fprintf(stderr,"string = %s\n",t);
    ENDR("sscan_partition");
}


INT cast_apply_part(a) OP a;
/* AK 280294 */
/* AK 230298 V2.0 */
{
    INT erg = OK;
    COP("cast_apply_part(1)",a);
    switch(S_O_K(a))
        {
        case INTEGER:
            erg += m_i_pa(a,a);
            break;
        case VECTOR:
            erg += m_v_pa(a,a);
            break;
        default:
            printobjectkind(a);
            erg += error("cast_apply_part: can not cast");
            break;
        }
    ENDR("cast_apply_part");
}

INT equal_parts(a,b) OP a,b;
/* return TRUE if PART a has >= b equal parts */
/* AK 230298 V2.0 */
{
    INT erg = OK;
    INT i,j=0,k=0;
    CTO( PARTITION,"equal_parts",a);
    CTO( INTEGER,"equal_parts",b);
    if (S_I_I(b) <= (INT)0) 
        {
        erg +=  error("equal_parts:integer object not bigger 0");
        goto endr_ende;
        }

    if (S_PA_K(a) == EXPONENT)
        {
        for (i=0;i<S_PA_LI(a);i++)
            if (S_PA_II(a,i) >= S_I_I(b)) return TRUE;
        return FALSE;
        }
    if (S_PA_K(a) != VECTOR)
        {
        erg +=  error("equal_parts: partition object not VECTOR kind");
        goto endr_ende;
        }

    for (i=0;i<S_PA_LI(a);i++)
        {
        if (S_PA_II(a,i) == k) j++;
        else { k = S_PA_II(a,i); j= 1; }
        if (j == S_I_I(b)) return TRUE;
        }
    return FALSE;
    ENDR("equal_parts");
}

INT q_core(a,b,d) OP a,b,d;
/* computes the remaining partition after 
   removal of all hooks of length q */
{
    INT erg = OK;
    OP e;
    e = CALLOCOBJECT();
    q_core_sign(a,b,d,e);
    FREEALL(e);
    ENDR("q_core");
}

INT q_core_sign(a,b,d,si) OP a,b,d; OP si;
/* computes the remaining partition after 
   removal of all hooks of length q */
/* sign = +/- 1 according to the parity of the sum of li lengths */
/* AK 301095 */
/* AK 230298 V2.0 */
/* AK 090703 sign added */
{
    INT erg = OK,i,j,bi,hi,li;
    OP e;
    PART_CHECK_KIND("q_core_sign(1)",a,VECTOR);
    CTO(INTEGER,"q_core_sign(2)",b);
    SYMCHECK(S_I_I(b)<1,"q_core_sign:q<1");
    if ( (a == d) || (a==si) ) {
        e = CALLOCOBJECT();
        COPY(a,e);
        erg += q_core_sign(e,b,d,si);
        goto endr_ende;
        }
    else if ( (b == d) || (b==si) ) {
        e = CALLOCOBJECT();
        COPY(b,e);
        erg += q_core_sign(a,e,d,si);
        goto endr_ende;
        }
    else {
        FREESELF(d);
        FREESELF(si);
        }

    e = CALLOCOBJECT();
    M_I_I(1,si);
    erg += copy_partition(a,d);
    bi = S_I_I(b);
aa:
    for (i=0;i<S_PA_LI(d);i++)
    for (j=0;j<S_PA_II(d,S_PA_LI(d)-1-i);j++)
        {
        /* erg += hook_length(d,i,j,e); */
        hi = S_PA_II(d,S_PA_LI(d)-1-i)-j; /* arm length +1 */
        li = 0;
        do {
        if ( S_PA_LI(d)-1-i-li < 0) { li--; break;}
        if ( S_PA_II(d, S_PA_LI(d)-1-i-li) < j+1) { li--; break;}
        li ++;
        } while (1);
        /* li = leg lenth  */
        if ((li+hi) == bi)
            { 
              if ((li % 2) == 1) M_I_I(-S_I_I(si),si);
              
              erg += remove_hook(d,i,j,d); 
              if (EMPTYP(d)) goto bb;
              goto aa; }
        }
bb:
    erg += freeall(e);
    ENDR("q_core_sign");
}


INT remove_hook(a,i,j,c) OP a,c; INT i,j;
/* AK 301095 */
/* AK 230298 V2.0 */
/* a may be identical to c */
{
    INT erg =OK,k;
    OP d;
    CTO (PARTITION ,"remove_hook(1)",a);
    SYMCHECK(S_PA_K(a) != VECTOR,
        "remove_hook(1):only vector partition type");
    
    if (i >= S_PA_LI(a))
        {
        if (a!= c) COPY(a,c);
        }
    else if (j >= S_PA_II(a,S_PA_LI(a)-1-i))
        {
        if (a!= c) COPY(a,c);
        }
   else {
        d = CALLOCOBJECT();
        COPY(S_PA_S(a),d);
        M_I_I(j,S_V_I(d,S_PA_LI(a)-i-1));
        for (k=i+1; k<S_PA_LI(a); k++)
            if (S_PA_II(a,S_PA_LI(a)-1-k) -1 >= j) 
                {
                DEC_INTEGER(S_V_I(d,S_PA_LI(a)-1-k));
                COPY_INTEGER(S_V_I(d,S_PA_LI(a)-1-k),S_V_I(d,S_PA_LI(a)-k));
                }
            else {
                m_i_i(j,S_V_I(d,S_PA_LI(a)-k));
                break;
            }     
        if (k == S_PA_LI(a))
            M_I_I(j,S_V_I(d,0)); 
        erg += m_v_pa(d,c);
        FREEALL(d);
        }
    ENDR("remove_hook");
  
}

INT p_hook_diagramm(a,b,c) OP a,b,c;
/* AK 010295 */
/* AK 230298 V2.0 */
/* input: PARTITION object a
          INTEGER object b
   output: hook diagramm with entry = hooklength mod b */
{
    INT erg=OK,i,j,k,l;

    CTO(INTEGER,"p_hook_diagramm(2)",b);
    PART_CHECK_KIND("p_hook_diagramm(1)",a,VECTOR);
    CE3(a,b,c,p_hook_diagramm);


    if (S_I_I(b) < (INT) 0) 
        {
        erg += error("p_hook_diagramm: second parameter < 0");
        goto endr_ende;
        }
    erg += hook_diagramm(a,c);
    if (S_I_I(b) == (INT)0) goto ee;
    if (S_I_I(b) == (INT)1) goto ee;
    for (i=0;i<S_M_HI(c);i++)
    for (j=0;j<S_M_LI(c);j++)
        {
        if (S_M_IJI(c,i,j) == (INT)0) 
            {
            C_O_K(S_M_IJ(c,i,j),EMPTY);
            }
        else     
            {
            k = S_I_I(b); 
            l = 1;
            while  (S_M_IJI(c,i,j)%k == 0) 
                {l++;k *= S_I_I(b);
                }
            M_I_I(l-1,S_M_IJ(c,i,j));
            }
        }
        
ee:
    CTTO(INTEGERMATRIX,MATRIX,"p_hook_diagramm(3e)",c);
    ENDR("p_hook_diagramm");
}


INT odd_to_strict_part(a,b) OP a,b;
/* AK 020196 */
/* AK V2.0 090298 */
/* input: odd PARTITION object
   output: corresponding strict PARTITION object */

/* a and b may be the same object */
{
    INT erg = OK;
    OP c,d;
    INT i,j,k,l;
    CTO(PARTITION,"odd_to_strict_part(1)",a);

    c = callocobject();
    d = callocobject();
    erg += t_VECTOR_EXPONENT(a,c);
    erg += weight(a,d);
    erg += m_il_nv(S_I_I(d),d);
    l = 0;
    for (i=0;i<S_PA_LI(c);i++)
        {
        if (S_PA_II(c,i) != 0)
            {
            j=1;k=S_PA_II(c,i);
    aa:
            if (k % 2) {
                erg += m_i_i((i+1)*j,S_V_I(d,l));
                l++;
                }
            k /=2 ;
            j *= 2;
            if (j <= S_PA_II(c,i)) goto aa;
            }
        }
    erg += m_v_pa(d,b);
    erg += freeall(c);
    erg += freeall(d);
    ENDR("odd_to_strict_part");
}

INT strict_to_odd_part(a,b) OP a,b;
/* AK 020196 */
/* AK V2.0 090298 */
/* input: strict PARTITION object
   output: corresponding PARTITION object with odd parts */

/* a and b may be the same object */
{
    INT erg = OK;
    INT i,k,l=0,j;
    OP c;
    CTO(PARTITION,"strict_to_odd_part(1)",a);
    c = callocobject();
    erg += weight(a,c);
    erg += m_il_nv(S_I_I(c),c);
    for (i=0;i<S_PA_LI(a);i++)
        {
        k = S_PA_II(a,i);
        if ((k%2) == 1)
            {
            erg += m_i_i(k,S_V_I(c,l)); l++;
            }
        else    {
            j=4;
    aa:
            if ((k%j) == 0) {j *= 2; goto aa;}
            j /= 2;  /* j ist die hoechste 2er potenz die passt */
            k = k/j;
            for (;j>0;j--)
                {
                erg += m_i_i(k,S_V_I(c,l)); l++;
                }
            }
        }
    erg += m_v_pa(c,b);
    erg += freeall(c);
    ENDR("strict_to_odd_part");
}



INT nachfolger_young(a,b) OP a,b;
/* input: PARTITION object a
   output: VECTOR object of PARTITION objects, which are
       bigger neighbours in the Young poset */
/* AK V2.0 170298 */
/* a and b may be equal */
{
        INT erg = OK,k;
        OP c,z;
        CTO(PARTITION,"nachfolger_young",a);
        c = callocobject();
        erg += first_partition(cons_eins,c);
        erg += outerproduct_schur(c,a,c);
        k=0; z = c;
        while (z != NULL) { k++; z = S_L_N(z); }
        erg += m_il_v(k,b);
        k=0; z = c;
        while (z != NULL) { 
        erg += copy_partition(S_S_S(z), S_V_I(b,k)); k++; z = S_L_N(z); }
        erg += freeall(c);
        ENDR("nachfolger_young");
}



INT vorgaenger_young(a,b) OP a,b;
/* input: PARTITION object a
   output: VECTOR object of PARTITION objects,
           which are smaller neighbours in the Young poset */
/* AK V2.0 170298 */
/* a and b may be equal */
{
    INT erg = OK,k;
    OP c,z;
    CTTO(SKEWPARTITION,PARTITION,"vorgaenger_young(1)",a);
    if (S_O_K(a) == SKEWPARTITION)
        {
        CE2(a,b,vorgaenger_young_skewpartition);
        erg += vorgaenger_young_skewpartition(a,b);
        goto ende;
        }
    SYMCHECK (S_PA_LI(a) == 0, "vorgaenger_young: partition of weight 0 not allowed");
    c = CALLOCOBJECT();
    erg += first_partition(cons_eins,c);
    erg += part_part_skewschur(a,c,c);
    k=0; z = c;
    while (z != NULL) { k++; z = S_L_N(z); }
    erg += m_il_v(k,b);
    k=0; z = c;
    while (z != NULL) { 
        erg += copy_partition(S_S_S(z), S_V_I(b,k)); 
        k++; 
        z = S_L_N(z); 
        }
    FREEALL(c);
ende:
    ENDR("vorgaenger_young");
}

INT vorgaenger_young_skewpartition(a,b) OP a,b;
/* input: SKEWPART object a
          EMPTY object b
   output: VECTOR object b of SKEWPART objects, 
           which are smaller neighbours in the Young poset */
/* AK V2.0 280602 */
{
    INT erg = OK,i,kl;
    OP g,k;
    CTO(SKEWPARTITION,"vorgaenger_young_skewpartition(1)",a);
    CTO(EMPTY,"vorgaenger_young_skewpartition(2)",b);
    g = S_SPA_G(a);
    k = S_SPA_K(a);

    SYMCHECK( EQ(g,k), "vorgaenger_young_skewpartition: partition of weight 0 not allowed");  

    erg += init(BINTREE,b);

    if (S_PA_LI(g) == 1)
        {
        OP c;
        c = CALLOCOBJECT();
        m_gk_spa(g,k,c);
        DEC_INTEGER(S_SPA_GI(c,0));
        insert(c,b,NULL,NULL);
        goto ende;
        }

/* in der ersten zeile kann evtl ein stein entfernt werden */

    if (S_PA_LI(k) < S_PA_LI(g)) {
        OP c;
        c = CALLOCOBJECT();
        m_gk_spa(g,k,c);
        if (S_PA_II(g,0) == 1)
            {
            FREESELF(S_SPA_G(c));
            remove_part_integer(S_SPA_G(a),cons_eins,S_SPA_G(c));
            }
        else
            DEC_INTEGER(S_SPA_GI(c,0));
        insert(c,b,NULL,NULL);
        }
    else 
        if (S_PA_II(g,0) > S_PA_II(k,0))
            {
            OP c;
            c = CALLOCOBJECT();
            m_gk_spa(g,k,c);
            DEC_INTEGER(S_SPA_GI(c,0));
            insert(c,b,NULL,NULL);
            }


    for (i=1;i<S_PA_LI(g);i++)
	if (S_PA_II(g,i) > S_PA_II(g,i-1)) {
            kl = S_PA_LI(k) - (S_PA_LI(g)-i);
            if (kl < 0)
                {
                OP c;
                c = CALLOCOBJECT();
                m_gk_spa(g,k,c);println(c);
                DEC_INTEGER(S_SPA_GI(c,i));println(c);
                insert(c,b,NULL,NULL);
                }
            else if (S_PA_II(g,i) > S_PA_II(k,i-(S_PA_LI(g)-S_PA_LI(k)) ))
                {
                OP c;
                c = CALLOCOBJECT();
                m_gk_spa(g,k,c);println(c);
                DEC_INTEGER(S_SPA_GI(c,i));println(c);
                insert(c,b,NULL,NULL);
                }
            }
ende:
    t_BINTREE_VECTOR(b,b);
    ENDR("vorgaenger_young_skewpartition");
}


INT character_polynom(a,b) OP a,b;
/* AK 040892 */
/* AK 161006 V3.1 */
{
    INT erg = OK;
    INT i,wi=0;
    OP l,lp,p,res,v;
    PART_CHECK_KIND("character_polynom(1)",a,VECTOR);
     
    if (S_PA_LI(a) == (INT)0)
        {
        erg += m_scalar_polynom(cons_eins,b);
        goto endr_ende;
        }
    
    CE2(a,b,character_polynom);
    C1R(a,"character_polynom",b);


    CALLOCOBJECT4(l,lp,p,v);
    
    COPY(S_PA_L(a),l); 
    INC(l);
    COPY(a,lp);
    erg += first_permutation(l,p);
    erg += young_polynom(a,b);
    while (next_apply(p))
        {
        CLEVER_COPY(S_PA_S(a),v);
        for (i=1;i<S_P_LI(p);i++)
            {
            wi=S_V_II(v,S_V_LI(v)-i)+S_P_II(p,i)-i-1;
            if (wi<(INT)0) break;
            erg += m_i_i(    wi,
                S_V_I(v,S_V_LI(v)-i)
                 );
            }
        if (wi<(INT)0) continue;
        erg += m_v_pa(v,lp);
        res = callocobject();
        erg += young_polynom(lp,res);
        if (oddp(p)) 
            erg += addinvers_apply(res);
        insert(res,b,NULL,NULL);

        }
    FREEALL4(l,lp,p,v);	

    S1R(a,"character_polynom",b);
    ENDR("character_polynom");
}

INT young_polynom(a,l) OP a,l;
/* AK 040892 */
/* AK 16106 V3.1 */
{    
    OP b , c ,e , d , n,m ,f;
    INT i,j,k,wi,ii;
    INT erg = OK;
    PART_CHECK_KIND("young_polynom(1)",a,VECTOR);
    if (S_PA_LI(a) == 0)
        {
        erg +=  m_scalar_polynom(cons_eins,l);
        goto endr_ende;
        }
    C1R(a,"young_polynom",l);

    CALLOCOBJECT7(b,f,d,n,c,e,m);

    erg += weight(a,b); wi = S_I_I(b);
    erg += m_il_v(S_PA_LI(a),b);
    erg += m_i_i((INT)0,l);
    for (i=(INT)0;i<S_V_LI(b);i++)
        erg += first_part_EXPONENT(S_PA_I(a,i),S_V_I(b,i));
    do {
       erg += m_i_i(1,n);
       for (i=(INT)0;i<wi;i++)
        {
        erg += m_il_nv(S_PA_LI(a),c);
        k=(INT)0;
        for (ii=(INT)0;ii<S_PA_LI(a);ii++)
            {
            if (i<S_PA_II(a,ii)) 
                m_i_i(S_PA_II(S_V_I(b,ii),i),S_V_I(c,ii));
            if (i<S_PA_II(a,ii)) 
                k+=S_PA_II(S_V_I(b,ii),i);
            }
        if (k>(INT)0) 
            {
            erg += m_i_i(k,d);
            erg += multinom(d,c,e);
            erg += m_iindex_monom(i,f);
            erg += binom(f,d,m); 
            MULT_APPLY(e,m); 
            MULT_APPLY(m,n); 
            }
        }
       ADD_APPLY(n,l); 
       j=(INT)0;
       if (S_V_LI(b) == 0) break; /* AK 060498 */
       while (not next(S_V_I(b,j),S_V_I(b,j))) 
            {
            j++;
            if (j==S_V_LI(b)) break;
            }
       if (j == S_V_LI(b)) break;
   /* links von der stelle wo erhoeht wurd muss auf null gesetzt werden */
       for (j--;j>=(INT)0;j--)
        erg += first_part_EXPONENT(S_PA_I(a,j),S_V_I(b,j));
       } while(1);
    /* alle partitionen durchlaufen */

    FREEALL7(b,f,d,n,c,e,m);

    S1R(a,"young_polynom",l);
    ENDR("young_polynom");
}


INT is_graphical(a) OP a;
/* return TRUE if graphical partition */
/* i.e. a vertex degree sequence of a simple
   undirected graph, uses the criterion of haesselbarth
   see: barnes, savage: a reucrrence for counting graphical partitions
*/
/* AK 161006 V3.1 */
{
    INT erg = OK,r;
    CTO(PARTITION,"is_graphical(1)",a);
    SYMCHECK(S_PA_K(a) != VECTOR,"is_graphical no vector type");
    {
    INT i,j=0;
    OP b;
    INT res = TRUE;
     
    for (i=0; i<S_PA_LI(a);i++) j+=S_PA_II(a,i);
    if (j%2 == 1) { res=FALSE; goto ff; } /* AK 111006 */

    for (i=1; i<=S_PA_LI(a);i++)
        if (S_PA_II(a,S_PA_LI(a)-i) <i) break;
    i--;
    /* i is the size of the durfee square */
     
    /* printf("durfee size = %d\n",i);  */
     
    b=CALLOCOBJECT();
    conjugate(a,b);

#ifdef UNDEF
    for (j=1; j<=i;j++)
        {
        INT k,r;
        r = 0;
        for (k=1;k<=j;k++)
            r += (S_PA_II(b,S_PA_LI(b)-k) -  S_PA_II(a,S_PA_LI(a)-k));
        if (r < j) { res = FALSE; goto ee; }
        }
#endif
    r=0;
    for (j=1; j<=i;j++)
	{
	r+= (S_PA_II(a,S_PA_LI(a)-j) - S_PA_II(b,S_PA_LI(b)-j));
	/* printf("r= %d ",r); */
	if (r> -j) { res = FALSE; goto ee; }
	}
    ee:
    FREEALL(b);
    ff:
    return res;
    }
    ENDR("is_graphical");
}           

INT multiplicity_part(part,i) OP part; INT i;
/* AK 210503 */
/* return the multiplicty of part i in the partition part */
{
    INT erg = OK;
    CTO(PARTITION,"multiplicity_part",part);
    SYMCHECK(i<=0,"multiplicity_part: checked part must be > 0");
    if (S_PA_K(part) == VECTOR)
         {
         OP z;
         INT j=S_PA_LI(part)-1;
         do {
             z = S_PA_I(part,j);
             if (S_I_I(z) < i) return 0;
             else if (S_I_I(z) == i) 
                 {
                 erg = 1; 
                 j--;
                 while (j>=0) { z = S_PA_I(part,j); if (S_I_I(z) != i) return erg; 
                                j--; erg ++; } 
                 return erg; 
                 }
             else j--;
             } while (j>=0);
         return 0;
         }
    else if (S_PA_K(part) == EXPONENT)
         {
         if (i > S_PA_LI(part)) return 0;
         return S_PA_II(part,i-1);
         }
    else {
         error("multiplicity_part: wrong kind of partition");
         }

    ENDR("multiplicity_part");
}

INT durfee_size_part(a,b) OP a,b;
/* AK 260603 */
{
    INT erg =OK;
    CTO(PARTITION,"durfee_size_part(1)",a);
    if (S_PA_K(a)==VECTOR)
        {
        INT i,j;
        for (i=1; i<=S_PA_LI(a);i++)
            if (S_PA_II(a,S_PA_LI(a)-i) <i) break;
        m_i_i(--i,b);
        }
    else {
        erg += error("durfee_size_part:wrong type of partition");
        }
    ENDR("durfee_size_part");
}

INT hook_partition(a,i,j,b) OP a,b; INT i,j;
/* AK 260603 */
/* computes the hook at position (i,j) of the diagram */
{
    INT erg = OK;
    CTO(PARTITION,"hook_partition(1)",a);
    SYMCHECK(i<0,"hook_partition(2)<0");
    SYMCHECK(j<0,"hook_partition(3)<0");
    if (S_PA_K(a)==VECTOR)
        {
        if (i>=S_PA_LI(a)) first_partition(cons_null,b);
        else if (j>=S_PA_II(a,S_PA_LI(a)-1-i)) first_partition(cons_null,b);
        else {
             INT armlength, footlength;
             OP c;
             armlength=S_PA_II(a,S_PA_LI(a)-1-i)-1-j;
             for (footlength = 0; footlength < S_PA_LI(a)-1-i; footlength++)
                 if (S_PA_II(a,S_PA_LI(a)- i-1-footlength) <= j) {footlength--;break;}
    
             c=CALLOCOBJECT();
             m_il_v(footlength+1,c);
             for (;footlength>=0;footlength--)
                  M_I_I(1,S_V_I(c,footlength));
             M_I_I(armlength+1,S_V_I(c,S_V_LI(c)-1));
             C_O_K(c,INTEGERVECTOR);
             b_ks_pa(VECTOR,c,b);
             }
        }
    else {
        erg += error("hook_partition:wrong type of partition");
        }
    ENDR("hook_partition");
}


INT ribbon_partition(a,i,j,b) INT i,j; OP a,b;
/* AK 270603 */
/* computes the ribbon = skew partition
   corresponding to the hook at position i,j
*/
{
    INT erg = OK;
    CTO(PARTITION,"ribbon_partition(1)",a);
    SYMCHECK(i<0,"ribbon_partition(2):<0");
    SYMCHECK(j<0,"ribbon_partition(3):<0");
    if (S_PA_K(a) == VECTOR)
        {
        OP d;
        SYMCHECK(i>=S_PA_LI(a),"ribbon_partition(2):> length of partition");
        SYMCHECK(j>=S_PA_II(a,S_PA_LI(a)-1-i),"ribbon_partition(3):> size of part");
        d = CALLOCOBJECT();
        t_VECTOR_FROBENIUS(a,d);
        delete_entry_vector(S_V_I(S_PA_S(d),0),i,S_V_I(S_PA_S(d),0));
        delete_entry_vector(S_V_I(S_PA_S(d),1),j,S_V_I(S_PA_S(d),1));
        t_FROBENIUS_VECTOR(d,d);
        m_gk_spa(a,d,b);
        FREEALL(d);
        }
    else
        erg += error("ribbon_partition(1): wrong type of partition");
    ENDR("ribbon_partition");
}


INT young_ideal(a,b) OP a,b;
/* input: PARTITION object
   output: VECTOR object, i-th entry = i-th level in young ideal */
/* AK 130803 */
{
    INT i,j,k;
    OP c,d,e,z,f;
    INT erg = OK;
    CTO(PARTITION,"young_ideal(1)",a);
    if (S_PA_K(a) == EXPONENT)
        {
        CALLOCOBJECT2(c,d);
        erg += t_EXPONENT_VECTOR(a,c);
        erg += young_ideal(c,d);
        m_il_v(S_V_LI(d), b);
        for (i=0;i<S_V_LI(b);i++)
                {
                z = S_V_I(b,i); f = S_V_I(d,i);
                m_il_v(S_V_LI(f), z);
                for (j=0;j<S_V_LI(f);j++)
                        t_VECTOR_EXPONENT(S_V_I(f,j), S_V_I(z,j));
                }
        FREEALL2(c,d);
        goto endr_ende;
        }
    C1R(a,"young_ideal",b);
    c = callocobject();
    d = callocobject();
    e = callocobject();
    weight_partition(a,c); inc(c);
    b_l_v(c,b);
    m_o_v(a,S_V_I(b,0));
    for (i=0;i<S_V_LI(b)-1;i++)
        {
        init(BINTREE,d);
        for (j=0;j<S_V_LI(S_V_I(b,i));j++)
                {
                z = S_V_I(S_V_I(b,i),j);
                vorgaenger_young(z,e);
                for(k=0;k<S_V_LI(e);k++)
                        {
                        f = callocobject();
                        swap(f,S_V_I(e,k));
                        insert(f,d,NULL,NULL);
                        }
                }
        t_BINTREE_VECTOR(d,S_V_I(b,i+1));
        }
    freeall(d);
    freeall(e);
    S1R(a,"young_ideal",b);
    ENDR("young_ideal");
}



#endif /* PARTTRUE */
