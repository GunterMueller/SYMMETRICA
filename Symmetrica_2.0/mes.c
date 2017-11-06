#include "def.h"
#include "macro.h"

INT mes_integer_partition_();

static OP mes_ip_limit = NULL;
static INT mes_ip_limit_length = 5;
static OP mes_ip_s = NULL;
static INT mes_ip_s_length = 5;
static OP mes_ip_v = NULL;
static INT mes_ip_v_length = 5;
INT mes_ende()
{
    INT erg = OK;
    if (mes_ip_limit != NULL) {
        FREEALL(mes_ip_limit);
        mes_ip_limit = NULL;
        mes_ip_limit_length = 5;
        }
    if (mes_ip_s != NULL) {
        FREEALL(mes_ip_s);
        mes_ip_s = NULL;
        mes_ip_s_length = 5;
        }
    if (mes_ip_v != NULL) {
        FREEALL(mes_ip_v);
        mes_ip_v = NULL;
        mes_ip_v_length = 5;
        }

    return OK;
    ENDR("mes_ende");
}

INT mes_integer_hashtable_(a,b,c,f) OP a,b,c; OP f;
{
    INT erg = OK;
    CTO(INTEGER,"mes_integer_hashtable_(1)",a);
    CTTO(HASHTABLE,SCHUR,"mes_integer_hashtable_(2)",b);
    CTTO(HASHTABLE,SCHUR,"mes_integer_hashtable_(3)",c);
    SYMCHECK((S_I_I(a) < 0), "mes_integer_hashtable_:parameter <0");

    M_FORALL_MONOMIALS_IN_B(a,b,c,f,mes_integer_partition_);

    ENDR("mes_integer_hashtable_");
}

INT mes_integer__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;

    CTO(INTEGER,"mes_integer__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mes_integer__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mes_integer__(3)",c);
    SYMCHECK((S_I_I(a) < 0), "mes_integer__:parameter <0");

    if (S_O_K(b) == PARTITION) {
        erg += mes_integer_partition_(a,b,c,f);
        goto ende;
        }
    else {
        erg += mes_integer_hashtable_(a,b,c,f);
        goto ende;
        }
ende:
    ENDR("mes_integer__");
}

INT mes_partition__(a,b,c,f) OP a,b,c; OP f;
/* AK 311001 */
{
    INT erg = OK;
    CTO(PARTITION,"mes_partition__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mes_partition__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mes_partition__(3)",c);

    if (S_PA_LI(a) == 0) {
        if (S_O_K(b) == PARTITION) {
            OP d;
            d = CALLOCOBJECT();
            erg += m_sk_mo(b,f,d);
            INSERT_SCHURMONOM_(d,c);
            }
        else /* schur or hashtable */
            {
            OP z;
            FORALL(z,b,{
                OP d;
                d = CALLOCOBJECT();
                erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),d);
                erg += copy_partition(S_MO_S(z),S_MO_S(d));
                if (not EINSP(f))
                    MULT(f,S_MO_K(z),S_MO_K(d));
                else
                    COPY(S_MO_K(z),S_MO_K(d));
                INSERT_SCHURMONOM_(d,c);
                });
            }
        goto endr_ende;
        }
    else { /* partition of length >= 1 */
        INT i; OP d,e;
 
        d=CALLOCOBJECT();
        e=CALLOCOBJECT();

        erg += init_hashtable(e);
        erg += mes_integer__(S_PA_I(a,0),b,e,f);
        for (i=1;i<S_PA_LI(a);i++)
           {
           FREESELF(d);
           erg += init_hashtable(d);
           SWAP(d,e);
           erg += mes_integer__(S_PA_I(a,i),d,e,cons_eins);
           }
        FREEALL(d);
        if (S_O_K(c) == SCHUR)
            INSERT_LIST(e,c,add_koeff,comp_monomschur);
        else
            INSERT_HASHTABLE(e,c,add_koeff,eq_monomsymfunc,hash_monompartition);
        }


    ENDR("mes_partition__");
}

INT mes_elmsym__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(ELMSYM,"mes_elmsym__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mes_elmsym__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mes_elmsym__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mes_partition__);
    ENDR("mes_elmsym__");
}

INT mes_hashtable__(a,b,c,f) OP a,b,c,f;
/* AK 061101 */
/* c += h_a \times s_b  \times f */
{
    INT erg = OK;
    CTO(HASHTABLE,"mes_hashtable__(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mes_hashtable__(2)",b);
    CTTO(HASHTABLE,SCHUR,"mes_hashtable__(3)",c);
    M_FORALL_MONOMIALS_IN_A(a,b,c,f,mes_partition__);
    ENDR("mes_elmsym__");
}


INT mult_elmsym_schur(a,b,c) OP a,b,c;
/* AK 111001
   with pieri rule
*/
/* is the result=c empty the result will be a SCHUR object
   is the result a HASHTABLE or SCHUR object will be the result inserted
*/
{
    INT erg = OK;
    INT t=0; /* is 1 if transfer HASHTABLE->SCHUR necessary */
    CTTTTO(HASHTABLE,INTEGER,PARTITION,ELMSYM,"mult_elmsym_schur(1)",a);
    CTTTO(HASHTABLE,PARTITION,SCHUR,"mult_elmsym_schur(2)",b);
    CTTTO(EMPTY,HASHTABLE,SCHUR,"mult_elmsym_schur(3)",c);

    if (S_O_K(a) == INTEGER)        
        {
        if (S_O_K(c) == EMPTY) {
           if (S_O_K(b) == PARTITION) init_schur(c);
           else { t=1; init_hashtable(c); }
           }
        erg += mes_integer__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == PARTITION)  
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mes_partition__(a,b,c,cons_eins);
        }
    else if (S_O_K(a) == ELMSYM)
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); } 
        erg += mes_elmsym__(a,b,c,cons_eins);
        }
    else /* if (S_O_K(a) == HASHTABLE) */
        {
        if (S_O_K(c) == EMPTY)
            { t=1; init_hashtable(c); }
        erg += mes_hashtable__(a,b,c,cons_eins);
        }

    if (t==1) t_HASHTABLE_SCHUR(c,c);
    ENDR("mult_elmsym_schur");
}



static INT mes_first_pieri(a,b,c) OP a,b,c;
{
    INT i;
/*
    m_il_nv(S_V_LI(b),c);
*/
    if (S_V_LI(b) > mes_ip_v_length) {
        inc_vector_co(c,S_V_LI(b) -  mes_ip_v_length);
        mes_ip_v_length = S_V_LI(c);
        }
    M_I_I(S_V_LI(b),S_V_L(c));
    for (i=1;i<S_V_LI(c);i++) M_I_I(0,S_V_I(c,i));
    M_I_I(S_I_I(a),S_V_I(c,0));
    return OK;
}

static INT mes_next_pieri_limit_apply(limit,v) OP limit,v;
{
    INT i,w=0,g=0;

    for (i=S_V_LI(v)-1; i>=0;i--) 
        {
        if (S_V_II(v,i) > 0) 
        if (w > 0) break;
        else 
            g+=S_V_II(v,i);
        if (S_V_II(limit,i) > 0) 
            w+=S_V_II(limit,i)-S_V_II(v,i);

        M_I_I(0,S_V_I(v,i));
        }
    /* an der stelle i kann nach rechts geschoben werden */
    if (i== -1) return FALSE;

    g++;
    M_I_I(S_V_II(v,i)-1, S_V_I(v,i));
    for (i++; ;i++)
        {
        if (S_V_II(limit,i) >= g)
            {
            M_I_I(g,S_V_I(v,i));
            return TRUE;
            }
        else {
            M_I_I(S_V_II(limit,i),S_V_I(v,i));
            g = g - S_V_II(limit,i);
            }
        }
}


INT mes_integer_partition_(a,b,c,f) OP a,b,c,f;
/* c += e_a \times s_b \times f*/
/* c is already initialised */
{
    INT erg = OK;
    /* pieri rule */
    OP limit;
    OP v;
    INT i,j,k;
    OP ps,s;

    CTO(INTEGER,"mes_integer_partition_(1)",a);
    CTO(PARTITION,"mes_integer_partition_(2)",b);
    CTTO(SCHUR,HASHTABLE,"mes_integer_partition_(3)",c);
    SYMCHECK(S_I_I(a) < 0,"mes_integer_partition_:integer < 0");


    if (S_PA_LI(b) == 0) {
        OP s;
        s = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),s);
        COPY(f,S_MO_K(s));
        erg += last_partition(a,S_MO_S(s));

        INSERT_SCHURMONOM_(s,c);
        goto ende;
        }
    if (S_I_I(a) == 0) {
        OP s;
        s = CALLOCOBJECT();
        erg += m_sk_mo(b,f,s);
        INSERT_SCHURMONOM_(s,c);
        goto ende;
        }

    if (mes_ip_limit == NULL) {
        mes_ip_limit=CALLOCOBJECT();
        m_il_integervector(mes_ip_limit_length,mes_ip_limit);
        limit = mes_ip_limit;
        }
    else {
        M_I_I(mes_ip_limit_length,S_V_L(mes_ip_limit));
        limit = mes_ip_limit;
        }
    if ((S_PA_II(b,S_PA_LI(b)-1)+1) > mes_ip_limit_length)
        {  
        inc_vector_co(limit, (S_PA_II(b,S_PA_LI(b)-1)+1) - mes_ip_limit_length);
        mes_ip_limit_length = S_V_LI(limit);
        CTO(INTEGERVECTOR,"mes_integer_partition_(i1)",limit);
        }
    M_I_I((S_PA_II(b,S_PA_LI(b)-1)+1),S_V_L(mes_ip_limit));


    M_I_I(S_I_I(a),S_V_I(limit,0));
    for (i=1;i<S_V_LI(limit);i++) 
        M_I_I(0,S_V_I(limit,i));
    for (i=0;i<S_PA_LI(b);i++) 
        INC_INTEGER(S_V_I(limit,S_PA_II(b,i)));
    

    if (mes_ip_s == NULL) {
        ps = CALLOCOBJECT();
        erg += m_il_integervector(mes_ip_s_length,ps);
        mes_ip_s = CALLOCOBJECT();
        erg += b_sk_mo(CALLOCOBJECT(),CALLOCOBJECT(),mes_ip_s);
        erg += b_ks_pa(VECTOR,ps,S_MO_S(mes_ip_s));
        s = mes_ip_s;
        }
    else {
        M_I_I(mes_ip_s_length,S_PA_L(S_MO_S(mes_ip_s)));
        s = mes_ip_s;
        ps = S_PA_S(S_MO_S(s));
        }

    if (S_PA_LI(b)+S_I_I(a) > mes_ip_s_length) 
        {
        inc_vector_co(S_PA_S(S_MO_S(s)), (S_PA_LI(b)+S_I_I(a)) - mes_ip_s_length);
        mes_ip_s_length = S_PA_LI(S_MO_S(s));
        }

    M_I_I(S_PA_LI(b)+S_I_I(a),S_PA_L(S_MO_S(s)));
    for (i=0;i<S_PA_LI(S_MO_S(s));i++) M_I_I(0,S_PA_I(S_MO_S(s),i));
    FREESELF(S_MO_K(s));
    COPY(f,S_MO_K(s));

    /* v = CALLOCOBJECT(); */
    if (mes_ip_v == NULL)
        {
        mes_ip_v = CALLOCOBJECT();
        erg += m_il_integervector(mes_ip_v_length,mes_ip_v);
        v = mes_ip_v;
        }
    else {
        M_I_I(mes_ip_v_length,S_V_L(mes_ip_v));
        v = mes_ip_v;
        }

    erg += mes_first_pieri(a,limit,v); 
    do {

        for (i=0;i<S_V_II(v,0);i++)
            M_I_I(1,S_V_I(ps,i));

        for (j=0;j<S_PA_LI(b);j++,i++)
            M_I_I(S_PA_II(b,j), S_V_I(ps,i));

        M_I_I(S_PA_LI(b)+S_V_II(v,0), S_V_L(ps));
        
        for (j=S_V_LI(ps)-1,i=S_V_LI(v)-1; i>0;i--)
            if (S_V_II(v,i) > 0)
                {
                while(S_V_II(ps,j) > i) j--;
                if (S_V_II(ps,j) != i) error("");
                for (k=0;k<S_V_II(v,i);k++)   
                    INC_INTEGER(S_V_I(ps,j-k));
                j = j - S_V_II(v,i);
                }
 
            
            
        if (S_O_K(c) == SCHUR)
            {
            OP ss = CALLOCOBJECT();
            erg += copy_monom(s,ss);
            insert_list(ss,c,add_koeff,comp_monomschur);
            }
        else
            {
            HASH_INTEGERVECTOR(S_PA_S(S_MO_S(s)),j);
            C_PA_HASH(S_MO_S(s),j);
            erg += add_apply_hashtable(s,c,add_koeff,eq_monomsymfunc,hash_monompartition);
            }


    } while (mes_next_pieri_limit_apply(limit,v) == TRUE);

ende:
    ENDR("mes_integer_partition_");
}

