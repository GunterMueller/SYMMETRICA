#include "def.h"
#include "macro.h"



INT mxx_null__();
INT mps_integer_partition_();
INT cc_muir_mms_partition_partition_();

INT mms_null__(b,c,f) OP b,c,f;
/* c = c +  s_b * f */
{
    INT erg = OK;
    CTTTTO(INTEGER,HASHTABLE,PARTITION,SCHUR,"mms_null__(1)",b);
    CTTO(SCHUR,HASHTABLE,"mms_null__(2)",c);
    erg += mxx_null__(b,c,f);
    ENDR("mms_null");
}

INT mms_integer_partition_(a,b,c,f) OP a,b,c,f;
/* AK 071201 */
{
    INT erg = OK;
    CTO(INTEGER,"mms_integer_partition_(1)",a);
    CTO(PARTITION,"mms_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_integer_partition_(3)",c);
    erg += mps_integer_partition_(a,b,c,f);
    ENDR("mms_integer_partition_");
}

INT mms_integer__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(INTEGER,"mms_integer__(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms_integer__(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_integer__(3)",c);

    if (S_I_I(a) == 0)
        erg += mms_null__(b,c,f);
    else if (S_O_K(b) == INTEGER) {
        OP ff;
        ff = CALLOCOBJECT();
        erg += first_partition(b,ff);
        erg += mms_integer_partition_(ff,b,c,f);
        FREEALL(ff);
        }
    else if (S_O_K(b) == PARTITION) {
        erg += mms_integer_partition_(a,b,c,f);
        }
    else /* SCHUR   HASHTABLE */ {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mms_integer_partition_);
        }

    ENDR("mms_integer__");
}

INT mms_partition_partition_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"mms_partition_partition_(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms_partition_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_partition_partition_(3)",c);
    if (S_PA_LI(a) == 0) {
        erg += mms_null__(b,c,f);
        }
    else if  (S_PA_LI(a) == 1) {
        erg += mms_integer_partition_(S_PA_I(a,0),b,c,f);
        }
    else {
        if (S_O_K(c) == HASHTABLE) 
            {
            erg += cc_muir_mms_partition_partition_(a,b,c,f);
            }
        else {
            OP d;
            d = CALLOCOBJECT();
            init_hashtable(d);
            erg += cc_muir_mms_partition_partition_(a,b,d,f);
            t_HASHTABLE_SCHUR(d,d);
            insert_list(d,c,add_koeff,comp_monomschur);
            }
#ifdef UNDEF
        INT w,i,j;
        INT l;
        OP subset,v,perm,iperm;

        for (i=0,w=0;i<S_PA_LI(a);i++) w+= S_PA_II(a,i);
        l = w + S_PA_LI(b);
        /* this is the length of the composition */
        v = callocobject();
        erg += m_il_nv(l,v);C_O_K(v,INTEGERVECTOR);
        subset = callocobject();
        perm = callocobject();
        iperm = callocobject();
        m_l_v(S_PA_L(a),iperm);
    	/* innerhalb des subsets nun alle vers permutationen */
        erg += first_permutation(S_PA_L(a),perm);
        do {
    	    erg += first_subset(S_V_L(v),S_PA_L(a),subset);
    	    for (i=0;i<S_V_LI(iperm);i++) M_I_I(0,S_V_I(iperm,i));
    	    do {
    	        OP d,s;
                M_I_I(l,S_V_L(v)); /* wird in reorder_vector_apply geaendert */
    	        for (i=S_V_LI(v)-1,j=S_PA_LI(b)-1;i>=0;i--,j--) 
    		    if (j>=0) M_I_I(S_PA_II(b,j),S_V_I(v,i));
    		    else M_I_I(0,S_V_I(v,i));
    	        /* vector v is filled with partition b */
    
    	        for(i=0,j=0;i<S_P_LI(perm);i++)
    		    {
    		    /* um verschiedene permutationen zu bekommen, testen */
    
    		    if (S_P_II(perm,i) > 1)
    		       if (S_PA_II(a,S_P_II(perm,i)-1) == S_PA_II(a,S_P_II(perm,i)-2) )
    		          if (S_V_II(iperm,S_P_II(perm,i)-2) == 0) goto next_perm;
    
    		    while (S_V_II(subset,j) == 0) j++;
    		    /* an der stelle j ist ein eintrag */
    		    M_I_I(S_V_II(v,j)+S_PA_II(a,S_P_II(perm,i)-1),S_V_I(v,j));
    		    M_I_I(i+1,S_V_I(iperm,S_P_II(perm,i)-1));
    		    j++;
    		    }
    
    	        i = reorder_vector_apply(v);

    	        if (i==0) { goto next_subset; }
    	        /* summand gefunden */
    
    	        d = CALLOCOBJECT();
    	        s = callocobject();
                COPY(v,d);
    
                erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),s);
                if (i==1) COPY(f,S_MO_K(s));
                else ADDINVERS(f,S_MO_K(s));
    	        erg += b_ks_pa(VECTOR,d,S_MO_S(s));
    
                if (S_O_K(c) == HASHTABLE)
    	            insert_scalar_hashtable(s,c,add_koeff,eq_monomsymfunc,hash_monompartition);
                else /* SCHUR */
    	            insert_list(s,c,add_koeff,comp_monomschur);
                    
            next_subset: ;
    	    } while(next_apply(subset));
        next_perm:	;
    	     /* print(iperm);print(v);println(perm); */
        } while (next_apply(perm));

        erg += freeall(perm);
        erg += freeall(iperm);
        erg += freeall(v);
        erg += freeall(subset);
#endif
        }
    ENDR("mms_partition_partition_");
}


INT mms_partition__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(PARTITION,"mms_partition__(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms_partition__(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_partition__(3)",c);
    if (S_O_K(b) == PARTITION)
        erg += mms_partition_partition_(a,b,c,f);
    else {
        M_FORALL_MONOMIALS_IN_B(a,b,c,f,mms_partition_partition_);
        }
    ENDR("mms_partition__");
}

INT mms_hashtable__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"mms_hashtable__(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms_hashtable__(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mms_partition__);
    ENDR("mms_hashtable__");
}

INT mms_hashtable_partition_(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(HASHTABLE,"mms_hashtable_partition_(1)",a);
    CTO(PARTITION,"mms_hashtable_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_hashtable_partition_(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mms_partition_partition_);
    ENDR("mms_hashtable_partition_");
}


INT mms_monomial__(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTO(MONOMIAL,"mms_monomial__(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms_monomial__(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms_monomial__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mms_partition__);
    ENDR("mms_monomial__");
}


INT mms___(a,b,c,f) OP a,b,c,f;
{
    INT erg = OK;
    CTTTTO(INTEGER,PARTITION,MONOMIAL,HASHTABLE,"mms___(1)",a);
    CTTTO(PARTITION,SCHUR,HASHTABLE,"mms___(2)",b);
    CTTO(SCHUR,HASHTABLE,"mms___(3)",c);
    if (S_O_K(a) == INTEGER)
        {
        erg += mms_integer__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == PARTITION)
        {
        erg += mms_partition__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == HASHTABLE)
        {
        erg += mms_hashtable__(a,b,c,f);
        goto ende;
        }
    else if (S_O_K(a) == MONOMIAL)
        {
        erg += mms_monomial__(a,b,c,f);
        goto ende;
        }
ende:       
    ENDR("mms___");
}


INT mult_monomial_schur(a,b,c) OP a,b,c;
{
    INT erg = OK;
    INT t=0;
    CTTTTO(INTEGER,MONOMIAL,PARTITION,HASHTABLE,"mult_monomial_schur(1)",a);
    CTTTTO(INTEGER,SCHUR,PARTITION,HASHTABLE,"mult_monomial_schur(2)",b);
    CTTTO(EMPTY,SCHUR,HASHTABLE,"mult_monomial_schur(3)",c);

    if (S_O_K(c) == EMPTY) {
        t=1;
        init_hashtable(c);
        }
    erg += mms___(a,b,c,cons_eins);

    if (t==1) erg += t_HASHTABLE_SCHUR(c,c);

    CTTO(SCHUR,HASHTABLE,"mult_monomial_schur(3-ende)",c);
    ENDR("mult_monomial_schur");
}
