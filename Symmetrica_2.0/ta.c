/* SYMMETRICA file:ta.c */
#include "def.h"
#include "macro.h"

static struct tableaux * calloctableaux();
static INT inhaltcoroutine();
static INT free_tableaux();

static INT mem_counter_tab;

#ifdef TABLEAUXTRUE
#define ZEILENENDE(tab,zn)/* AK 100902 */\
(\
 S_O_K(S_T_U(tab)) == PARTITION ?\
(zn >= S_PA_LI(S_T_U(tab)) ? -1 :S_PA_II(S_T_U(tab),S_PA_LI(S_T_U(tab))-1-zn) -1 ):\
(zn >=   S_T_UGLI(tab) ? -1 :S_PA_II(S_T_UG(tab),S_T_UGLI(tab)-zn-1)-1)\
)

INT tab_anfang()
/* AK 100893 */
    {
    mem_counter_tab=0L;
    return OK;
    }

INT tab_ende()
/* AK 100893 */
    {
    INT erg = OK;
    if (mem_counter_tab != 0L)
        {
        fprintf(stderr,"mem_counter_tab = %ld\n",mem_counter_tab);
        erg += error("tab memory not freed");
        }
    return erg;
    }

INT cast_apply_tableaux(a) OP a;
/* AK 270295 */
/* AK 260398 V2.0 */
/* tries to make the object a into a TABLEAUX object */
{
    INT erg = OK;
    EOP("cast_apply_tableaux(1)",a);
    if (MATRIXP(a))
        {
        erg += m_matrix_tableaux(a,a);
        }
    else if (VECTORP(a))
        {
        erg += cast_apply_matrix(a);
        erg += m_matrix_tableaux(a,a);
        }
    else {
        WTO("cast_apply_tableaux(1)",a);
        }
    SYMCHECK(a == S_T_S(a), "cast_apply_tableaux(i1)");
    ENDR("cast_apply_tableaux");
}

INT conjugate_tableaux(a,b) OP a,b;
/* AK 040398 V2.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"conjugate_tableaux",a);
    CE2(a,b,conjugate_tableaux);
    erg += b_us_t(callocobject(),callocobject(),b);
    erg += conjugate(S_T_U(a), S_T_U(b));
    erg += transpose(S_T_S(a), S_T_S(b));
    ENDR("conjugate_tableaux");
}


#endif /* TABLEAUXTRUE */

INT tableauxp(a) OP a;
/* AK 040398 V2.0 */
{
    OP z;
    if (S_O_K(a) != TABLEAUX) 
        return FALSE;
    if (not matrixp(S_T_S(a)))
        return FALSE;
    z = S_T_U(a);

    switch(S_O_K(z)) {
        case PARTITION:
            if (not partitionp(z)) return FALSE;
            return TRUE;
        case SKEWPARTITION:
            if (not skewpartitionp(z)) return FALSE;
            return TRUE;
        }

    return FALSE;
}

#ifdef TABLEAUXTRUE
INT charge_tableaux(a,b) OP a,b;
/* AK 141196 */
/* AK 040398 V2.0 */
/* a and b may be equal */
{
    INT erg = OK;
    OP c;
    CTO(TABLEAUX,"charge_tableaux(1)",a);
    c = CALLOCOBJECT();
    erg += rowwordoftableaux(a,c);
    erg += charge_word(c,b);
    FREEALL(c);
    ENDR("charge_tableaux");
}


static INT free_tableaux(a) char *a;
{
    SYM_free(a);
    mem_counter_tab--;
    return OK;
}

INT freeself_tableaux(a) OP a;
/* AK 260789 */ /* AK 281289 V1.1 */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"freeself_tableaux(1)",a);
    FREEALL(S_T_S(a)); 
    FREEALL(S_T_U(a));
    free_tableaux((char *) S_O_S(a).ob_tableaux); 
    C_O_K(a,EMPTY);
    ENDR("freeself_tableaux");
}



INT copy_tableaux(a,b) OP a,b;
/* AK 260789 */ /* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"copy_tableaux(1)",a);
    CTO(EMPTY,"copy_tableaux(2)",b);

    erg += b_us_t(callocobject(),callocobject(),b);
    if (S_O_K(S_T_S(a)) == INTEGERMATRIX)
        erg += copy_integermatrix(S_T_S(a),S_T_S(b));
    else
        erg += copy_matrix(S_T_S(a),S_T_S(b)); /* self ist immer matrix */
    if (S_O_K(S_T_U(a)) == PARTITION)
        erg += copy_partition(S_T_U(a),S_T_U(b));
    else
        erg += copy(S_T_U(a),S_T_U(b));
    ENDR("copy_tableaux");
}

    


static struct tableaux * calloctableaux()
/* 020488 AK erste prozedur beim einfuehren eines neuen datentyps */
/* AK 010889 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    struct  tableaux *erg
    = (struct tableaux *) SYM_calloc((int)1,sizeof(struct tableaux));
    if (erg == NULL) 
        error("calloctableaux:no memory");
    mem_counter_tab++;
    return(erg);
    }

/* CONSTRUCTORS */
    INT m_us_t();
    INT b_us_t();
    INT b_u_t();
    INT m_u_t();
    INT b_matrix_tableaux();
    INT m_matrix_tableaux();


INT b_matrix_tableaux(mat,tab) OP mat,tab;
/* AK 010988 */ /* AK 010889 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    OP u;
    INT erg = OK;
    if (not MATRIXP(mat))
        WTO("b_matrix_tableaux",mat);
    CE2(mat,tab,b_matrix_tableaux);

    u = callocobject(); 
    erg += m_matrix_umriss(mat,u); 
    erg += b_us_t(u,mat,tab);
    ENDR("b_matrix_tableaux");
    }

INT m_matrix_tableaux(mat,tab) OP mat,tab;
/* AK 010988 */ /* AK 010889 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    OP u;
    INT erg = OK;
    if (not MATRIXP(mat))
        WTO("m_matrix_tableaux",mat);

    CE2(mat,tab,m_matrix_tableaux);

    u = callocobject(); 
    erg += m_matrix_umriss(mat,u); 
    erg += m_us_t(u,mat,tab);
    erg += freeall(u);
    ENDR("m_matrix_tableaux");
    }

INT m_u_t(umriss,res) OP umriss,res;
/* AK 020488 */
/* AK 281289 V1.1 */ /* AK 240791 V1.3 */
/* AK 020398 V2.0 */
/* umriss and res may be equal */
{
    OP l,h;
    INT erg = OK;
    CTTO(PARTITION,SKEWPARTITION,"m_u_t(1)",umriss);
        
    CE2(umriss,res,m_u_t);

    l= callocobject(); 
    h= callocobject(); 

    erg += b_us_t(CALLOCOBJECT(),CALLOCOBJECT(),res);
    COPY(umriss,S_T_U(res));

    erg += length(umriss,h);
    erg += lastof(umriss,l);
    erg += b_lh_m(l,h,S_T_S(res)); 

    CTO(TABLEAUX,"m_u_t(res)",res);
    ENDR("m_u_t");
}

INT b_u_t(umriss,res) OP umriss,res;
/* AK 020398 V2.0 */
{
    OP l,h;
    INT erg = OK;
    COP("b_u_t(2)",res);

    l= callocobject();
    h= callocobject();

    erg += length(umriss,h);
            /* bsp umriss = 1234 ==> height = 4
            umriss = 23456789/3456 ==> height = 8 */

    erg += lastof(umriss,l);

    erg += b_us_t(umriss,callocobject(),res);
    erg += b_lh_m(l,h,S_T_S(res));
    ENDR("b_u_t");
}

INT m_us_t(umriss,self,res) OP umriss,self,res;
/* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT erg = OK;
    COP("m_us_t(3)",res);
    erg += b_us_t(callocobject(),callocobject(),res);
    erg += copy(umriss,S_T_U(res)); 
    erg += copy_matrix(self,S_T_S(res)); 
    ENDR("m_us_t");
    }


INT b_us_t(umriss,self,res) OP umriss,self,res;
/* AK 010889 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    OBJECTSELF d;
    INT erg = OK;
    COP("b_us_t(3)",res);

    d.ob_tableaux = calloctableaux();
    erg += b_ks_o(TABLEAUX, d, res);

    erg += c_t_u(res,umriss);
    erg += c_t_s(res,self);
    ENDR("b_us_t");
    }



INT objectread_tableaux(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
{
    INT erg = OK;
    CTO(EMPTY,"objectread_tableaux(2)",a);
    COP("objectread_tableaux(1)",f);
    erg += b_us_t(callocobject(),callocobject(),a);
    erg += objectread(f,S_T_U(a));
    erg += objectread(f,S_T_S(a));
    ENDR("objectread_tableaux");
}



INT objectwrite_tableaux(f,a) FILE *f; OP a;
/* AK 210690 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"objectwrite_tableaux(2)",a);
    COP("objectwrite_tableaux(1)",f);
    fprintf(f,"%ld ",(INT)S_O_K(a));
    erg += objectwrite(f,S_T_U(a));
    erg += objectwrite(f,S_T_S(a));
    ENDR("objectwrite_tableaux");
}

INT m_matrix_umriss(mat,umr) OP mat,umr;
/* AK 080688 */
/* AK 010989 V1.0 */ /* AK 110790 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
/* mat and umr may be equal */
    {
    INT i,j,k,schalter;
    INT erg = OK;

    if (not MATRIXP(mat))
        {
        WTO("m_matrix_umriss",mat);
        goto endr_ende;
        }
    CE2(mat,umr,m_matrix_umriss);

    /* zuerst die laenge der partition */
    for (i=0L;i<S_M_HI(mat);i++) 
        if (EMPTYP(S_M_IJ(mat,i,0L))) break;

    if (i==0L) {
        /* SKEWPARTITION */
        /* AK 110790 V1.1 */
        OP a = callocobject(), b = callocobject();
        erg += m_il_integervector(S_M_HI(mat),a); 
        erg += m_il_integervector(S_M_HI(mat),b);
        for (i=0L;i<S_M_HI(mat); i++)
        {
        schalter = 0L;
        for (j=0L;j<S_M_LI(mat); j++)
            {
            if (schalter == 0L) {
                /* noch im linken leeren teil */
                if (not EMPTYP(S_M_IJ(mat,i,j))) {
                    M_I_I(j,S_V_I(b,i));
                    schalter=1L;
                    }
                else if (j == S_M_LI(mat)-1L) {
                    /* d.h. am ende */
                    M_I_I(S_M_LI(mat),S_V_I(a,i));
                    M_I_I(S_M_LI(mat),S_V_I(b,i));
                    }
                }
            if (schalter == 1L) {
                /* im teil mit eintraegen */
                if (EMPTYP(S_M_IJ(mat,i,j))) {
                    M_I_I(j,S_V_I(a,i));
                    schalter=2L;
                    }
                else
                if (j == S_M_LI(mat)-1L) {
                    /* d.h. am ende */
                    M_I_I(S_M_LI(mat),S_V_I(a,i));}
                }
            else
            if (schalter == 2L) {
                if (not EMPTYP(S_M_IJ(mat,i,j))) {
                    freeall(a); freeall(b);
                    debugprint(mat);
                    return
                     error("m_matrix_umriss:no MATRIX");
                    }
                }
            }
        }
        for (i=S_M_HI(mat)-1L; i>=0L; i--)
            {
            if (S_V_II(b,i) == S_M_LI(mat)) 
                {
                M_I_I(0L,S_V_I(b,i));
                M_I_I(0L,S_V_I(a,i));
                }
            else    break;
            }
        /* nun sind die nullen am ende */
        /* das umdrehen */ 
        erg += b_gk_spa(callocobject(),callocobject(),umr);
        erg += m_v_pa(a,S_SPA_G(umr)); 
        erg += m_v_pa(b,S_SPA_K(umr));
        erg += freeall(a);
        erg += freeall(b); 

        if (EMPTYP(S_SPA_G(umr))) /* no real entry in the matrix */
            {
            erg += freeself(umr);
            }
        goto endr_ende;
        }

    erg += b_ks_pa(VECTOR,CALLOCOBJECT(),umr); 
    erg += m_il_integervector(i,S_PA_S(umr));
    /* die laenge wurde berechnet */

    k = S_M_LI(mat);
    for (i=0L;i<S_PA_LI(umr);i++)
        {
        for (j=0L;j<S_M_LI(mat);j++) 
            if (EMPTYP(S_M_IJ(mat,i,j))) break;
        if (j==0L) 
            {
            erg += error("0 in m_matrix_umriss");
            goto endr_ende;
            }
        if (j > k)
            {
            erg += error("m_matrix_umriss:no partition shape");
            goto endr_ende;
            }
        M_I_I(j,S_PA_I(umr,S_PA_LI(umr)-1-i));
        k = j;
        };
    ENDR("m_matrix_umriss");
    }


INT tex_tableaux(a) OP a;
/* AK 060588 */ /* AK 230790 V1.1 */
/* AK 070291 V1.2 prints to texout */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */
    {
    INT i,j;
    INT erg = OK;
    CTO(TABLEAUX,"tex_tableaux(1)",a);

    if (S_O_K(S_T_U(a)) != PARTITION) /* AK 310892 */
        {
        return error("tex_tableaux: only for PARTITION shape");
        }
    fprintf(texout,"\\hbox { \\vbox {\n");
    for (i=0L; i< S_PA_LI(S_T_U(a)); i++)
            {
            fprintf(texout,"\\hrule width %ldpt\n",
                S_PA_II(S_T_U(a),i)*13-1L);
            fprintf(texout,"\\vskip 0pt\n\\hbox {\n");
            for (j=0L; j< S_PA_II(S_T_U(a),i); j++)
                {
                fprintf(texout,
                    "\\kern -3.5pt\n\\hbox to 13pt{");
                fprintf(texout,"\\vrule height10pt depth3pt$");
/* s_t_iji statt S_T_IJI */
            if (s_t_iji(a,S_PA_LI(S_T_U(a))-1-i,j) < 10L)
                fprintf(texout,"\\ %ld",
/* s_t_iji statt S_T_IJI */
                    s_t_iji(a,S_PA_LI(S_T_U(a))-1-i,j));
/* s_t_iji statt S_T_IJI */
            else if (s_t_iji(a,S_PA_LI(S_T_U(a))-1-i,j) < 100L)
                fprintf(texout,"%ld",
/* s_t_iji statt S_T_IJI */
                    s_t_iji(a,S_PA_LI(S_T_U(a))-1-i,j));
            else return
            error("tex_tableaux:entry too big in tableaux");
                    
                fprintf(texout,
                    "$ \\vrule height10pt depth3pt}\n");
                }
            fprintf(texout,"}\n\\vskip 0pt\n");
            if (i== S_PA_LI(S_T_U(a)) -1L)
            fprintf(texout,
            "\\hrule width %ldpt\n",S_PA_II(S_T_U(a),i)*13-1L);
            }

    fprintf(texout,"} } ");
    ENDR("tex_tableaux");
    }


INT comp_tableaux(a,b)    OP a,b;
/* AK 060588 */ /* AK 281289 V1.1 */ /* AK 200891 V1.3 */
/* AK 221097 */
/* AK 260398 V2.0 */
    {
    INT erg=OK,i,j,k;
    CTO(TABLEAUX,"comp_tableaux",a);
    CTO(TABLEAUX,"comp_tableaux",b);
    erg = comp(S_T_U(a), S_T_U(b));
    if (erg != (INT)0) return erg;
    for (i=0;i<S_T_HI(a) ; i++)
        {
        k = ZEILENENDE(a,i);
        for (j=zeilenanfang(a,i);j<=k;j++)
            {
            erg = comp(S_T_IJ(a,i,j), S_T_IJ(b,i,j));
            if (erg != (INT)0) return erg;
            }
        }
    return (INT)0;
    ENDR("comp_tableaux");
    }


INT inc_tableaux(tab) OP tab;
/* AK 250488 */ /* AK 291289 V1.1 */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */

/* the new self part will have a new empty row and a new empty 
   column */
    {
    OP a,b; 
    INT i,j;
    INT erg = OK;
    CTO(TABLEAUX,"inc_tableaux(1)",tab);

    a = S_T_S(tab);

    b = CALLOCOBJECT();
    erg += m_ilih_m(S_M_LI(a)+1,S_M_HI(a)+1,b);

    for (i=0L;i<S_M_HI(a);i++)
        for (j=0L;j<S_M_LI(a);j++)
            {
            C_O_S(S_M_IJ(b,i+1L,j),S_O_S(S_M_IJ(a,i,j)));
            C_O_K(S_M_IJ(b,i+1L,j),S_O_K(S_M_IJ(a,i,j)));
            }
    erg += freeall(S_M_H(a)); 
    erg += freeall(S_M_L(a));
    *a = *b;
    ENDR("inc_tableaux");
    }


INT weight_tableaux(a,b) OP a,b;
/* subroutine of weight in the case of a tableau object */
/* weight of a tableau is the number of entries */
/* AK 170790 V1.1 */ 
/* AK 200891 V1.3 */
/* AK 260398 V2.0 */
    {
    INT erg = OK;
    CTO(TABLEAUX,"weight_tableaux(1)",a);
    CTO(EMPTY,"weight_tableaux(2)",b);
    erg += weight(S_T_U(a),b);
    ENDR("weight_tableaux");
    }


#define CO_CO_FPT \
        if (S_O_K(S_T_U(a)) == PARTITION)\
            {if (i >= S_T_ULI(a)) continue;}\
        else if (S_O_K(S_T_U(a)) == SKEWPARTITION)\
            {if (i >= S_T_UGLI(a)) continue;}\
/*empty matrix*/else if (S_O_K(S_T_U(a)) == EMPTY)\
            continue;\
\
                fprintf(fp,"\n");\
                if (fp == stdout) zeilenposition = 0L;\
                schalter=1L;\
                for (j=0L; j<S_T_LI(a); j++)\
                        if (EMPTYP(S_T_IJ(a,i,j)))\
                                {\
                        if (schalter==2L)/*fprintf(fp,"  ")*/;\
                        else if (schalter==1L)fprintf(fp,"# ");\
                                }\
                        else {\
                                schalter=2L;\
                                fprint(fp,S_T_IJ(a,i,j));\
                                fprintf(fp," ");\
                                }\

INT fprint_tableaux(fp,a) FILE *fp; OP a;
/* AK 020488 */ /* AK 281289 V1.1 */ /* AK 200891 V1.3 */
/* AK 020398 V2.0 */
    {
    INT i,j,schalter;
    INT erg = OK;
    CTO(TABLEAUX,"fprint_tableaux",a);
    if ((S_T_HI(a)*S_T_LI(a)) == (INT)0) /* empty tableaux, shape = [] */
        {
        fprintf(fp,"[]");
        }
    else
    {
    if (english_tableau != TRUE)
        {
        for (i=S_T_HI(a)-1L;i >= 0L; i--)
            {
            CO_CO_FPT
            };
        }
    else
        {
        for (i=0L; i < S_T_HI(a);i++)
            {
            CO_CO_FPT
            };
        }
    }
    fprintf(fp,"\n");
    if (fp == stdout) {
        zeilenposition = (INT)0;
        }
    ENDR("fprint_tableaux");
    }


/* SELECTORS */
OP s_t_s(a) OP a; 
/* AK 200891 V1.3 */ /* AK 040398 V2.0 */
    { 
    OBJECTSELF c; 
    c = s_o_s(a); 
    return(c.ob_tableaux->t_self); 
    }

OP s_t_u(a) OP a; 
/* AK 200891 V1.3 */ /* AK 040398 V2.0 */
    {
    OBJECTSELF c;
    c=s_o_s(a); 
    return(c.ob_tableaux->t_umriss); 
    }

OP s_t_ug(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_g(s_t_u(a))); }

OP s_t_l(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_m_l(s_t_s(a))); }

INT s_t_li(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_m_li(s_t_s(a))); }

INT s_t_hi(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_m_hi(s_t_s(a))); }

INT s_t_iji(a,i,j) OP a;INT i,j; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_i_i(s_t_ij(a,i,j))); }

OP s_t_ij(a,i,j) OP a;INT i,j; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_m_ij(s_t_s(a),i,j)); }

OP s_t_h(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_m_h(s_t_s(a))); }

INT c_t_s(a,b) OP a,b; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { OBJECTSELF c; c = s_o_s(a); c.ob_tableaux->t_self = b;
    return(OK); }

INT c_t_u(a,b) OP a,b;
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { OBJECTSELF c; c = s_o_s(a); c.ob_tableaux->t_umriss = b; return(OK); }

OP s_t_uk(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_k(s_t_u(a))); }

OP s_t_us(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_pa_s(s_t_u(a))); }

INT s_t_uli(a) OP a; 
/* AK 040398 V2.0 */
    { 
    INT erg = OK;
    CTO(TABLEAUX,"s_t_uli",a);
    CTO(PARTITION,"s_t_uli:shape of the tableau",s_t_u(a));
    return(s_pa_li(s_t_u(a))); 
    ENDR("s_t_uli");
    }

OP s_t_ul(a) OP a; 
/* AK 040398 V2.0 */
    { 
    OP umriss = s_t_u(a);
    if (s_o_k(umriss) != PARTITION)
        {
        printobjectkind(umriss);
        error("s_t_ul: not a partition shape tableau");
        return NULL;
        }
    return(s_pa_l(s_t_u(a))); }

OP s_t_ui(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { 
    OP umriss = s_t_u(a);
    if (s_o_k(umriss) != PARTITION)
        {
        printobjectkind(umriss);
        error("s_t_ui: not a partition shape tableau");
        return NULL;
        }
    return(s_pa_i(s_t_u(a),i)); }

INT s_t_uii(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { 
    OP umriss = s_t_u(a);
    if (s_o_k(umriss) != PARTITION)
        {
        printobjectkind(umriss);
        error("s_t_uii: not a partition shape tableau");
        return ERROR;
        }
    return(s_pa_ii(s_t_u(a),i)); }

INT s_t_ukii(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_kii(s_t_u(a),i)); }

INT s_t_ukli(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_kli(s_t_u(a))); }

INT s_t_ugii(a,i) OP a;INT i; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_gii(s_t_u(a),i)); }

INT s_t_ugli(a) OP a; 
/* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    { return(s_spa_gli(s_t_u(a))); }



INT content_tableaux(a,content) OP a,content;
/* AK 250488 */ /* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT i,j,an,en;
    INT erg = OK;
    CTO(TABLEAUX,"content_tableaux(1)",a);
    CE2(a,content,content_tableaux);

    erg += m_il_nv(1L,content);

    for (i=S_T_HI(a)-1L;i>=0L;i--)
        {
        an = zeilenanfang(a,i);
        en = ZEILENENDE(a,i);
        for (j=an;j<=en;j++)
            erg += inhaltcoroutine(S_T_IJI(a,i,j),content);
        }
    ENDR("content_tableaux");
    }


static INT inhaltcoroutine(zahl,content) INT zahl; OP content;
/* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT erg = OK;
    CTO(VECTOR,"internal routine:inhaltcoroutine(2)",content);
    if (zahl <= S_V_LI(content)) 
        INC_INTEGER(S_V_I(content,zahl-1L));
    else {
        OP b=callocobject(); 
        INT k,m=S_V_LI(content); 
        erg += m_il_v(zahl,b);
        for (k=0L;k<m;k++)
            M_I_I(S_V_II(content,k),S_V_I(b,k));
        for (k=m;k<zahl;k++)
            M_I_I(0L,S_V_I(b,k));
        M_I_I(1L,S_V_I(b,zahl-1L));
        erg += freeself(content);
        *content =  *b;
        C_O_K(b,EMPTY);
        erg += freeall(b);
        };
    ENDR("internal routine:inhaltcoroutine");
    }



INT scan_tableaux(a) OP a;
/* 020488 AK */ /* AK 010889 V1.1 */ 
/* AK 200691 V1.2 */ /* AK 200891 V1.3 */
/* AK 040398 V2.0 */
    {
    INT erg = OK;
    char c[2];
    CTO(EMPTY,"scan_tableaux(1)",a);
again:
    printeingabe("Please enter (S)kewpartition or (P)artition for the shape of the tableau");
    scanf("%s",&c[0]);

    if (c[0] == 'P')
        { erg += scan_parttableaux(a); }
    else if (c[0] == 'S')
        { erg += scan_skewtableaux(a); }
    else 
        { goto again; }
    ENDR("scan_tableaux");
    }

INT scan_skewtableaux(a) OP a;
/* AK 020398 V2.0 */
{
    INT k,m;
    INT i,j;
    INT erg = OK;
    OP umriss;
    char c[100];

    CTO(EMPTY,"scan_skewtableaux(1)",a);

    umriss = callocobject();

    printeingabe("Please enter a tableau of skewpartition shape\n");
    erg += scan(SKEWPARTITION,umriss);
    erg += b_u_t(umriss,a);
    printeingabe("Now please enter the tableau\n");
    m = S_T_UKLI(a); /* ab diesen index ist nur noch
                    die groessere Partition */
    for (i=0L; i<S_T_HI(a); i++)
        { 
/* s_t_ukii statt S_T_UKII */
        if (i<m) k=s_t_ukii(a,S_T_UKLI(a)-1-i);
        else k=0L;
                /* in spalte k wird eingetragen */
        sprintf(c,"row nr %ld \n",(i+1L)); /* AK 020792 */
        printeingabe(c); /* AK 020792 */
        for (j=k;j<S_PA_II(s_t_ug(a),S_T_UGLI(a)-1-i);j++)
            erg += scan(INTEGER,S_T_IJ(a,i,j)); 
        };
    ENDR("scan_skewtableaux");
}

INT scan_parttableaux(a) OP a;
/* AK 020398 V2.0 */
{
    INT i,j,erg = OK;
    char c[100];
    OP umriss;
    CTO(EMPTY,"scan_parttableaux(1)",a);

    printeingabe("Please enter a tableau of partition shape\n");
    umriss = callocobject();
    erg += scan(PARTITION,umriss);

    erg += b_u_t(umriss,a);
    printeingabe("Now please enter the tableau\n");
    for (i=0L; i<S_T_HI(a); i++)
        { 
        sprintf(c,"row nr %ld \n",(i+1L)); /* AK 020792 */
        printeingabe(c); /* AK 020792 */
        for (j=0L;j<S_PA_II(S_T_U(a),S_T_HI(a)-1-i);j++)
            erg += scan(INTEGER,S_T_IJ(a,i,j)); 
        };
    ENDR("scan_parttableaux");
}




INT wordoftableaux(a,b) OP a,b;
/* AK 200891 V1.3 */
/* AK 260398 V2.0 */
    { 
    INT erg = OK;
    CTO(TABLEAUX,"wordoftableaux(1)",a);
    erg +=  columnwordoftableaux(a,b);
    ENDR("wordoftableaux");
    }    



INT rowwordoftableaux(a,b) OP a,b;
/* berechnet das zu einem Tableaux gehoerende word */
/* MD p.68 */ /* AK 281289 V1.1 */ /* AK 200891 V1.3 */
/* AK 230398 V2.0 */
    {
    OP l = callocobject();
    INT i,j,k;
    INT index=0L; /* der index im word */
    INT erg = OK;  /* AK 300792 */

    CTO(TABLEAUX,"rowwordoftableaux",a);
    CE2(a,b,rowwordoftableaux);

    erg += weight_tableaux(a,l);
    /* die laenge des wortes ist das gewicht des tableaus */

    erg += m_il_w(S_I_I(l),b);

    for (i=0;i<S_T_HI(a);i++) 
        {
        k = zeilenanfang(a,i);
        for(j=ZEILENENDE(a,i);j>=k;j--)
            { M_I_I(S_T_IJI(a,i,j),S_W_I(b,index));index++; }
            
        }
    erg += freeall(l); 
    ENDR("rowwordoftableaux");
    }



INT columnwordoftableaux(a,b) OP a,b;
/* berechnet das zu einem Tableaux gehoerende word */
/* AK 020290 V1.1 */ /* AK 200891 V1.3 */
/* AK 230398 V2.0 */
    {
    OP l;
    INT i,j,k,erg=OK;
    INT index=0L; /* der index im word */
    CTO(TABLEAUX,"columnwordoftableaux(1)",a);

    l = callocobject();
    erg += weight_tableaux(a,l);
    /* die laenge des wortes ist das gewicht des tableaus */

    erg += m_il_w(S_I_I(l),b);

    for (j=0L;j<S_T_LI(a);j++)
        {
        k = spaltenanfang(a,j);
        for(i=spaltenende(a,j);i>=k;i--)
            { M_I_I(S_T_IJI(a,i,j),S_W_I(b,index));index++; }
            
        }
    erg += freeall(l); 
    ENDR("columnwordoftableaux");
    }


INT spaltenanfang(a,b) OP a; INT b;
/* AK 020290 V1.1 */ /* AK 180691 V1.2 */ /* Ak 200891 V1.3 */
/* AK 230398 V2.0 */
{
    OP z = S_T_U(a);
    INT j;
    if (b <0L) 
        return error("spaltenanfang:index < 0");
    if (S_O_K(z) == PARTITION) 
        {
        if (b >= S_PA_II(z,S_PA_LI(z)-1L)) return(S_T_HI(a));
        else return(0L);
        }
    else if (S_O_K(z) == SKEWPARTITION)
        {
/* s_t_ugii statt S_T_UGII */
        if (b >= s_t_ugii(a,S_T_UGLI(a)-1L)) return(S_T_HI(a));
/* s_t_ukii statt S_T_UKII */
        else if (b>=s_t_ukii(a,S_T_UKLI(a)-1L)) return(0L);
        else 
            {
            for (j=S_T_UKLI(a)-1L;j>=0L;j--) 
                if (S_T_UKII(a,j) <=  b) break;
            return(S_T_UKLI(a) - 1L - j);
            }
        }
    else error("spaltenanfang: wrong shape");
    return OK;
}

INT spaltenende(a,b) OP a; INT b;
/* AK 020290 V1.1 */ /* AK 180691 V1.2 */ /* Ak 200891 V1.3 */
/* AK 230398 V2.0 */
{
    OP z = S_T_U(a);
    INT j;
    if (b <0L) 
        return error("spaltenende:index < 0");
    if (S_O_K(z) == PARTITION) 
        {
        if (b >= S_PA_II(z,S_PA_LI(z)-1L)) return(-1L);
        else {
            for (j=S_PA_LI(z)-1L;j>=0L;j--) 
                if (S_PA_II(z,j) <=  b) break;
            return(S_PA_LI(z) - 2L - j);
             }
        }
    else if (S_O_K(z) == SKEWPARTITION)
        {
/* s_t_ugii statt S_T_UGII */
        if (b >= s_t_ugii(a,S_T_UGLI(a)-1L)) return(-1L);
        else {
            for (j=S_T_UGLI(a)-1L;j>=0L;j--) 
                if (S_T_UGII(a,j) <=  b) break;
            return(S_T_UGLI(a) - 2L - j);
             }
        }
    else return error("spaltenende: wrong shape");
}

INT zeilenanfang(tab,zn) OP tab; INT zn;
/* AK 090688 */
/* gibt index ersten eintrag in zeile zn */
/* falls zn keine besetzte zeile ist, dann ist das ergebnis die breite der
matrix */
/* AK 281289 V1.1 */ /* AK 180691 V1.2 */ /* Ak 200891 V1.3 */
/* AK 230398 V2.0 */
    {
    INT erg = OK;
    CTO(TABLEAUX,"zeilenanfang",tab);
    if (zn <0L) 
        {
        erg += error("zeilenanfang:index < 0");
        goto endr_ende;
        }
    if (S_O_K(S_T_U(tab)) == PARTITION) { /* ein tableau */
        if (zn < S_PA_LI(S_T_U(tab)) ) return(0L);
        else return(S_T_LI(tab));
        }
    else if (S_O_K(S_T_U(tab)) == SKEWPARTITION) /* ein schieftableau */
        {
        if (zn >=  S_T_UGLI(tab)) return(S_T_LI(tab));
        else if (zn >=  S_T_UKLI(tab)) return(0L);
        else return( S_T_UKII(tab,S_T_UKLI(tab)-zn-1L));
        }
    else {
        printobjectkind(S_T_U(tab));
        erg += error("zeilenanfang: wrong umriss");
        }
    ENDR("zeilenanfang");
    }

INT zeilenende(tab,zn) OP tab; INT zn; 
/* letzter erlaubter index */
/* AK 281289 V1.1 */ /* AK 180691 V1.2 */ /* Ak 200891 V1.3 */
/* AK 230398 V2.0 */
/* AK 100902 V2.1 */
    {
    OP u = S_T_U(tab);
    INT erg = OK;
    CTO(TABLEAUX,"zeilenende(1)",tab);
    CTTO(PARTITION,SKEWPARTITION,"zeilenende(1.shape)",S_T_U(tab));
    SYMCHECK(zn<0,"zeilenende:index < 0");

    if (S_O_K(u) == PARTITION) 
        {
        if (zn >= S_PA_LI(u)) 
            return -1;
        else 
            return(S_PA_II(u,S_PA_LI(u)-1L-zn) -1);
        }
    else 
        {
        if (zn >=   S_T_UGLI(tab)) 
            return -1;
        else 
            return(S_PA_II(S_T_UG(tab),S_T_UGLI(tab)-zn-1L)-1);
        }
    ENDR("zeilenende");
    }



INT skewplane_plane(a,b) OP a,b;
/* AK 010889 */
/* Jeu de Taquin auf a wird b . a ist schiefplanepartition
 und wird eine planepartition b */
/* AK 010889 V1.1 */ /* Ak 200891 V1.3 */
/* AK 230398 V2.0 */
    {
    OP self = callocobject(); 
    OP umriss;
    OP unten,rechts;
    INT i,j; 
    INT posi,posj;  /* aktuelle position des jokers */
    INT nexti,nextj;  /* naechste position des jokers */
    INT si=0,sj=0; /* start of joker */

    copy (S_T_S(a),self);
m0108893: /* ein neues spiel */
    i = 0L;
    for (j=0L;j<S_M_LI(self);j++)
        if (not EMPTYP(S_M_IJ(self,i,j)))
            {
            if (j == 0L) goto m010889stop1; /* ende */
                    /* man hat ein tableaux */


            /* spalte mit eintrag */
            j = j - 1L; 
            for (i=0L;i<S_M_HI(self);i++)
                if (not EMPTYP(S_M_IJ(self,i,j)))
                    { si=i-1L;sj=j;goto m0108891;}
            };
m0108891:    /* si,sj die position des jokers */
    posi = si; posj = sj;
m0108892:     /* next step */
        /* nach richtung kleineres element, bei gleich nach unten */
    unten = NULL; rechts = NULL;
    if (posi+1 < S_M_HI(self)) /* joker nicht in unterste zeile */
        {
        unten = S_M_IJ(self,posi+1L,posj);
        if (EMPTYP(unten)) unten = NULL;
        };
    if (posj+1 < S_M_LI(self)) /* joker nicht in letzter spalte */
        {
        rechts = S_M_IJ(self,posi,posj+1L);
        if (EMPTYP(rechts)) rechts = NULL;
        };
    if ( (unten == NULL) && (rechts == NULL) ) 
        /* ende ein neues spiel */ goto m0108893;
    if ( (unten == NULL))  /* nach rechts */
        { nexti = posi; nextj=posj+1L; }
    else if ( (rechts == NULL))  /* nach unten */
        { nexti = posi+1L; nextj=posj; }
    else /* in beide richtungen ist noch ein eintrag */
        {
        if (gt(rechts,unten))
            { nexti = posi; nextj=posj+1L; }
        else    { nexti = posi+1L; nextj=posj; };
        };

    copy(S_M_IJ(self,nexti,nextj),S_M_IJ(self,posi,posj));
    freeself(S_M_IJ(self,nexti,nextj));
    posi=nexti; posj=nextj;
    goto m0108892; /* noch eine runde */
m010889stop1: /* wir sind fertig,aus der matrix wird ein tableau */
    umriss = callocobject(); 
    m_matrix_umriss(self,umriss);
    return b_us_t(umriss,self,b);
    }




INT plane_tableau(a,b) OP a,b;
/* AK 010889 */
/* Jeu de Taquin auf a wird b . a ist planepartition
 und wird ein tableau b */
/* AK 010889 V1.1 */ /* AK 200891 V1.3 */
    {
    OP self = callocobject(); 
    OP unten,rechts;
    INT startwert; 
    INT posi,posj;  /* aktuelle position des jokers */
    INT nexti,nextj;  /* naechste position des jokers */

    copy(a,b);
    copy (S_T_S(a),self);
n0108893: /* ein neues spiel */
    /* posi,posj die position des jokers */
    posi = 0L; posj = 0L;
    if (EMPTYP(S_M_IJ(self,posi,posj)))
        goto n010889stop1;
    startwert=S_M_IJI(self,posi,posj);
n0108892:     /* next step */
        /* nach richtung kleineres element, bei gleich nach unten */
    unten = NULL; rechts = NULL;
    if (posi+1 < S_M_HI(self)) /* joker nicht in unterste zeile */
        {
        unten = S_M_IJ(self,posi+1L,posj);
        if (EMPTYP(unten)) unten = NULL;
        };
    if (posj+1 < S_M_LI(self)) /* joker nicht in letzter spalte */
        {
        rechts = S_M_IJ(self,posi,posj+1L);
        if (EMPTYP(rechts)) rechts = NULL;
        };
    if ( (unten == NULL) && (rechts == NULL) ) 
        /* ende ein neues spiel */ {
        freeself(S_M_IJ(self,posi,posj));
        M_I_I(startwert,S_T_IJ(b,posi,posj));
        goto n0108893; }
    if ( (unten == NULL))  /* nach rechts */
        { nexti = posi; nextj=posj+1L; }
    else if ( (rechts == NULL))  /* nach unten */
        { nexti = posi+1L; nextj=posj; }
    else /* in beide richtungen ist noch ein eintrag */
        {
        if (gt(rechts,unten))
            { nexti = posi; nextj=posj+1L; }
        else    { nexti = posi+1L; nextj=posj; };
        };

    copy(S_M_IJ(self,nexti,nextj),S_M_IJ(self,posi,posj));
    freeself(S_M_IJ(self,nexti,nextj));
    posi=nexti; posj=nextj;
    goto n0108892; /* noch eine runde */
n010889stop1: /* wir sind fertig */
    freeall(self);
    return(OK);
    }

INT apply_INJDT(a,l,k,anz) OP a,l;INT k,anz;
/* a ist tableau, l ist liste, hier werden die ergebnisse eingefuegt */
/* k ist die mindestspalte */
/* AK 160790 V1.1 */ /* AK 200891 V1.3 */
{    
    OP b ;
    INT i,j,oj,obergrenze=0;
    INT erg = OK;
    CTO(TABLEAUX,"apply_INJDT(1)",a);

    if (anz == 0L) return OK;
    oj = S_T_LI(a)+1L;
    if (S_O_K(S_T_U(a)) == PARTITION) obergrenze=S_T_ULI(a);
    if (S_O_K(S_T_U(a)) == SKEWPARTITION) obergrenze=S_T_UGLI(a);
    for (i=0; i<=obergrenze ; i++)
        {
        j=ZEILENENDE(a,i)+1;
        if (j == -1) break;
        if (j == oj) continue; /* keine ecke */
        if (j < k) continue;
        b = callocobject();
        inverse_nilplactic_jeudetaquin_tableaux(a,i,j,b);
        oj = j;
        if (anz == 1L)insert(b,l,NULL,NULL);
        else { apply_INJDT(b,l,j+1L,anz-1L); freeall(b); }
        }
    ENDR("apply_INJDT");
}

INT perm_tableaux(a,b) OP a,b;
/* a ist permutation
   b wird liste von tableaux, die reduzierte Zerlegung sind */
/* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */
/* a and b may be equal */
{
    INT erg = OK;
    OP c;
    CTO(PERMUTATION,"perm_tableaux(1)",a);
    c= callocobject();
    erg += lehmercode(a,c);
    erg += lehmercode_tableaux(c,b);
    erg += freeall(c);
    ENDR("perm_tableaux");
}


INT lehmercode_tableaux(a,b) OP a,b;
/* a ist lehmercode
   b wird liste von tableaux, die reduzierte Zerlegung sind */
/* AK 230790 V1.1 */ /* AK 200891 V1.3 */
/* AK 260398 V2.0 */
{
    INT i,j,za,k;
    OP zz,c,d,z,e;
    INT erg = OK;

    CTTO(INTEGERVECTOR,VECTOR,"lehmercode_tableaux(1)",a);
    CE2(a,b,lehmercode_tableaux);

    for (i=0L; i<S_V_LI(a); i++) if (S_V_II(a,i) != 0L) break;
        /* i ist der erste index eines 
            eintrags ungleich 0 im lehmercode */
    if (i==S_V_LI(a)) return OK;  /* lehmercode == 0-Vektor */

    /* nun haben wir einen lehmercode mit inversionen */
    c = callocobject(); copy(a,c); M_I_I(0L,S_V_I(c,i)); 
    /* c ist der gleiche lehmercode wie a nur 
        mit einer 0 an der ersten stelle
    einer inversion */

    d = callocobject(); 
    erg += lehmercode_tableaux(c,d);
    erg += init(LIST,b); /* b ist list-object mit NULL self und next */
    if (EMPTYP(d)) {
        /* c war 0-Vektor */
        erg += b_us_t(callocobject(),callocobject(),c);
        erg += m_ilih_m(S_V_II(a,i),1L,S_T_S(c));
        for (j=0;j<S_T_LI(c);j++) M_I_I(j+1+i,S_T_IJ(c,0L,j));
        erg += m_matrix_umriss(S_T_S(c),S_T_U(c));
        insert(c,b,NULL,NULL);
        erg += freeall(d);
        goto endr_ende;
        }
    erg += freeall(c);
    z=d;
    e = callocobject(); init(LIST,e);
    while (z != NULL)
        {
        apply_INJDT(S_L_S(z),e,0L,S_V_II(a,i));
        z = S_L_N(z);
        }    
    erg += freeall(d);
    /* jetzt muss diese liste durch sucht werden ob man in der untersten
    zeile einfuegen kann */
    z = e;
    while (z != NULL) 
        {
        zz = S_L_S(z);
        if (S_T_UKLI(zz) != 1L) freeself(zz);
    /* s_t_ukii statt S_T_UKII wg MSC */
    /* s_t_ugii statt S_T_UGII wg MSC */
        else if ( s_t_ukii(zz,S_T_UKLI(zz)-1L) == 
              s_t_ugii(zz,S_T_UGLI(zz)-1L) ) 
            {
            za = S_V_II(a,i);
            for (j=S_V_II(a,i),k=1L;j>0L; j--,k++) 
                m_i_i(j+i,S_T_IJ(zz,0L,za-k));
            erg += m_matrix_umriss(S_T_S(zz),S_T_U(zz));
            insert(zz,b,NULL,NULL);
            C_L_S(z,NULL);
            }
        else if (
            S_T_IJI(zz,0L,zeilenanfang(zz,0L)) <=
            S_V_II(a,i) + i + 1L
            )  freeself(zz);
        else {
            za = zeilenanfang(zz,0L);
            for (j=S_V_II(a,i),k=1L;j>0L; j--,k++) 
                m_i_i(j+i,S_T_IJ(zz,0L,za-k));
            erg += m_matrix_umriss(S_T_S(zz),S_T_U(zz));
            insert(zz,b,NULL,NULL);
            C_L_S(z,NULL);
            }
        z = S_L_N(z);
        }
    erg += freeall(e);
    ENDR("lehmercode_tableaux");
}




INT umriss_tableaux(a,b) OP a,b;
/* AK 300792 */
/* AK 040398 V2.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"umriss_tableaux",a);
    CE2(a,b,umriss_tableaux);

    erg += copy(S_T_U(a),b);
    ENDR("umriss_tableaux");
}



INT standardp(a) OP a;
/* AK 300792 */
/* true if weakly increasing in rows
        and strictly in columns */
/* AK 040398 V2.0 */
{
    INT i,j;
    INT erg = OK;
    CTO(TABLEAUX,"standardp",a);
    for (i=0L; i<S_T_HI(a); i++)
    for (j=0L; j<S_T_LI(a); j++)
        if (not EMPTYP(S_T_IJ(a,i,j)))
        {
            if (i>0L)
            if (not EMPTYP(S_T_IJ(a,i-1L,j)))
            if (S_T_IJI(a,i,j) <= S_T_IJI(a,i-1L,j)) 
                return FALSE;
            if (j>0L)
            if (not EMPTYP(S_T_IJ(a,i,j-1L)))
            if (S_T_IJI(a,i,j) < S_T_IJI(a,i,j-1L)) 
                return FALSE;
        }
    return TRUE;
    ENDR("standardp");
}


INT planep(a) OP a;
/* true if strictly decreasing in rows and columns */
/* AK 260398 V2.0 */
{
    INT i,j;
    INT erg = OK;
    CTO(TABLEAUX,"planep",a);
    for (i=0L; i<S_T_HI(a); i++)
    for (j=0L; j<S_T_LI(a); j++)
        if (not EMPTYP(S_T_IJ(a,i,j)))
        {
            if (i>0L)
            if (not EMPTYP(S_T_IJ(a,i-1L,j)))
            if (S_T_IJI(a,i,j) > S_T_IJI(a,i-1L,j)) 
                return FALSE;
            if (j>0L)
            if (not EMPTYP(S_T_IJ(a,i,j-1L)))
            if (S_T_IJI(a,i,j) > S_T_IJI(a,i,j-1L)) 
                return FALSE;
        }
    return TRUE;
    ENDR("planep");
}


INT youngp(a) OP a;
/* AK 160992 */
/* TRUE if entries 1,2,3,....n,
   each exactly one time */
/* AK 040398 V2.0 */
{
    OP c;
    INT res,erg = OK;
    CTO(TABLEAUX,"youngp",a);
    c = callocobject();
    erg += inhalt_tableaux(a,c);
    if (not einsp_integervector(c)) res=FALSE;
    else res=TRUE;
    erg += freeall(c);
    if (erg != OK) 
        goto endr_ende;
    return res;
    ENDR("youngp");
}


INT sort_rows_tableaux_apply(b) OP b;
/* AK 070295 */
{
    INT erg = OK;
    INT i,j,k;
    CTO(TABLEAUX,"sort_rows_tableaux_apply(1)",b);

    for (i=0;i<S_T_HI(b);i++)
        {
        k = zeilenanfang(b,i);
        j = ZEILENENDE(b,i);
        
        qsort(S_T_IJ(b,i,k),j-k+1,sizeof(struct object),comp_integer);
        }
    ENDR("sort_rows_tableaux_apply");    
}
    

INT select_row_tableaux(a,i,b) OP a,b; INT i;
/* AK 280193 */
/* AK 091204 V3.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"select_row_tableaux(1)",a);
    {
    INT za,ze;
    INT j;
    za = zeilenanfang(a,i);
    ze = ZEILENENDE(a,i);

    FREESELF(b);
    if (za == S_T_LI(a)) 
        return OK; /* no entry in this row */
    erg += m_il_v(ze-za+1L,b);
    for (j=za; j <= ze; j++)
        COPY(S_T_IJ(a,i,j), S_V_I(b, j-za));
    }
    ENDR("select_row_tableaux");
}

INT select_column_tableaux(a,i,b) OP a,b; INT i;
/* AK 280193 */
{
    INT za,ze;
    INT erg = OK;
    INT j;

    CTO(TABLEAUX,"select_column_tableaux(1)",a);


    za = spaltenanfang(a,i);
    ze = spaltenende(a,i);
    erg += freeself(b);
    if (za == S_T_HI(a)) 
        return OK; /* no entry in this column */
    erg += m_il_v(ze-za+1L,b);
    for (j=za; j <= ze; j++)
        erg += copy(S_T_IJ(a,j,i), S_V_I(b, j-za));
    
    ENDR("select_column_tableaux");
}




#ifdef PERMTRUE
INT operate_perm_tableaux(b,a,c) OP a,b,c;
/* AK 110593 */
/* AK 240398 V2.0 */
/* AK 100902 V2.1 */
{
    INT erg=OK;
    CTO(TABLEAUX,"operate_perm_tableaux",a);
    CTO(PERMUTATION,"operate_perm_tableaux",b);
    SYMCHECK(S_P_K(b) != VECTOR,"operate_perm_tableaux: only for vector permutations");
    CE3(b,a,c,operate_perm_tableaux);
    {   
    INT i,j;
    erg  += copy_tableaux(a,c);
    for (i=0L;i<S_T_HI(a);i++)
    for (j=ZEILENENDE(a,i);j>=0;j--)
        {
        if (not EMPTYP(S_T_IJ(a,i,j)))
            {
            if (S_T_IJI(a,i,j) <= S_P_LI(b))
                M_I_I(S_P_II(b,S_T_IJI(a,i,j)-1L), S_T_IJ(c,i,j));
            }
        }
    }
    ENDR("operate_perm_tableaux");
}
#endif /* PERMTRUE */



INT first_tableaux(a,b) OP a,b;
/* AK 040693 */ /* a is umriss */ /* b first tableau according lex order
on column word */
{
    INT erg = OK;
    INT i,j,k=1,sa,se;
    CTTO(PARTITION,SKEWPARTITION,"first_tableaux",a);
    erg += m_u_t(a,b);
    for (j=0L;j<S_T_LI(b);j++)
        {
        sa = spaltenanfang(b,j); se=spaltenende(b,j);
        for (i=sa;i<=se;i++,k++)
            M_I_I(k,S_T_IJ(b,i,j));
        }
    
    ENDR("first_tableaux");
}

INT makevectorofSYT(shape,c) OP shape,c;
/* AK 100902 */
/* generates a vector with all SYT of a given shape */
/* AK 090804 V3.0 */
{
    INT erg = OK;
    CTTO(SKEWPARTITION,PARTITION,"makevectorofSYT(1)",shape);
    CE2(shape,c,makevectorofSYT);
    {
    OP d,e;
    INT i;
    d = CALLOCOBJECT();
    e = CALLOCOBJECT();
    weight(shape,d);
    erg += m_il_v(S_I_I(d),e);
    C_O_K(e,INTEGERVECTOR);
    for (i=0;i<S_V_LI(e);i++) M_I_I(1,S_V_I(e,i));
    erg += makevectoroftableaux(shape,e,c);
    FREEALL2(e,d);
    }
    ENDR("makevectorofSYT");
}

INT makevectoroftableaux(shape,content,c) OP shape,content,c;
/* AK 080295 */
/* AK 240398 V2.0 */
/* AK 100902 V2.1 */
{
    INT erg = OK;
    CTTO(SKEWPARTITION,PARTITION,"makevectoroftableaux(1)",shape);
    if (S_O_K(content) == PARTITION)
        {
        }
    else if (S_O_K(content) == INTEGERVECTOR)
        {
        }
    else if (S_O_K(content) == VECTOR)
        {
        INT i;
        for (i=0;i<S_V_LI(content);i++)
            if (S_O_K(S_V_I(content,i)) != INTEGER)
                goto aaa;
        }
    else    {
aaa:
        WTO("makevectoroftableaux(2)",content);
        goto endr_ende;
        }
    CE3(shape,content,c,makevectoroftableaux);
    C2R(shape,content,"makevectoroftableaux",c);
    {
    OP d,e;
    e = CALLOCOBJECT();
    erg += sum(content,e); /* AK 271098 */
    d = CALLOCOBJECT();
    erg += weight(shape,d);
    if (NEQ(d,e))
        {
        erg += error("makevectoroftableaux: different weight of input partitions");
        goto aa;
        }
    erg += kostka_tab(shape,content,d);
    erg += t_LIST_VECTOR(d,c);
aa:
    FREEALL(d);
    FREEALL(e);
    }
    S2R(shape,content,"makevectoroftableaux",c);
    ENDR("makevectoroftableaux");
}

INT max_tableaux(a,b) OP a,b;
/* AK 211097 */
/* AK 090804 V3.0 */
{
    INT erg = OK;
    CTO(TABLEAUX,"max_tableaux(1)",a);
    {
    erg += max_matrix(S_T_S(a),b);
    }
    ENDR("max_tableaux");
}

INT min_tableaux(a,b) OP a,b;
/* AK 140703 */
{
    INT erg = OK;
    CTO(TABLEAUX,"min_tableaux(1)",a);
    erg += min_matrix(S_T_S(a),b);
    ENDR("min_tableaux");
}


INT ym_min(form,res) OP form,res;
{
    INT lg_part,i,j,db,ind;
    OP wght,form1;
    INT erg = OK;
    CTO(PARTITION,"ym_min(1)",form);

    wght=callocobject();
    form1=callocobject();
    erg += conjugate(form,form1);
    erg += weight(form,wght);
    erg += m_l_v(wght,res);
    lg_part=S_PA_LI(form1);
    ind=0L;
    for(i=0L;i<lg_part;i++)
    {
        db=S_PA_II(form1,i)-1L;
        for(j=db;j>=0L;j--)
        {
            M_I_I(j,S_V_I(res,ind));
            ind++;
        }
    }
    erg += freeall(wght);
    erg += freeall(form1);
    ENDR("ym_min");
}




INT nxt_ym(ym1,ym2)    OP ym1,ym2;
{
    INT i,j,l,ind_max,av,pres=0,crt,tp;
    char *tab;

    ind_max=S_V_LI(ym1)-1L; av=S_V_II(ym1,ind_max);
    for(i=ind_max-1L;i>=0L;i--)
    {
        pres=S_V_II(ym1,i);
        if(pres<av) break;
        av=pres;
    }
    if(i== -1L) return FALSE;
    if(ym1!=ym2)
    {
        m_il_v(ind_max+1L,ym2);
        for(j=0L;j<i;j++)
            M_I_I(S_V_II(ym1,j),S_V_I(ym2,j));
    }
    av=pres;tp=0L;
    while(tp<=0L)
    {
        tp=0L;av++;l=0L;
        for(j=ind_max;(j>i)&&(l<av+2L);j--)
        {
            l=S_V_II(ym1,j);
            if(l==av) tp++;
            else if(l==av+1L) tp--;
        }
    }

    tp=i; pres=S_V_II(ym1,i+1L);
    tab=(char *)SYM_calloc(pres+1L,1);
    for(;i<=ind_max;i++)
        (*(tab+S_V_II(ym1,i)))++;
    (*(tab+av))--;
    M_I_I(av,S_V_I(ym2,tp));
    crt=ind_max;i=0L;
    for(j=pres;j>0L;j--)
        for(;i<*(tab+j);i++)
            for(l=0L;l<=j;l++,crt--)
                M_I_I(l,S_V_I(ym2,crt));
    for(;crt>tp;crt--)
        M_I_I(0L,S_V_I(ym2,crt));
    SYM_free(tab);
    return(TRUE);
}


    
INT find_tab_entry(tab,b,i,j) OP tab,b; INT *i, *j;
/* place of b in tab */
/* FALSE if not */
{
    INT k,l;
    for (k=0;k<S_T_HI(tab);k++)
    for (l=0;l<S_T_LI(tab);l++)
        if (eq(b,S_T_IJ(tab,k,l)))
            { *i = k; *j = l; return TRUE; }
    *i = -1; *j = -1; 
    return FALSE;
}

INT find_knuth_tab_entry(P,Q,b,i,j) OP P,Q,b; INT *i, *j;
/* findet groessten eintrag in P, wobei in Q an der stelle ein b
steht */
/* FALSE if not */
/* P und Q haben gleichen umriss */
{
    INT k,l;
    
    *i = -1; *j = -1; 
    for (k=0;k<S_T_HI(P);k++)
    for (l=0;l<S_T_LI(P);l++)
        if (eq(b,S_T_IJ(Q,k,l)))
            if (l > *j)
                {
                *i = k; 
                *j = l; 
                }
            
    if (*i == -1) return FALSE;
    else return TRUE;
}

INT word_tableaux(a,b) OP a,b;
{
    INT erg = OK;
    CE2(a,b,word_tableaux);
    erg += word_schen(a,b,NULL);
    ENDR("word_tableaux");
}

INT word_schen(a,p_symbol,q_symbol) OP a,p_symbol,q_symbol;
{
        INT i;
    INT erg = OK;
    CE3(a,p_symbol,q_symbol,word_schen);
    if (S_O_K(a) == PERMUTATION)
        erg += word_schen(S_P_S(a),p_symbol,q_symbol);
    else    {
        erg += freeself(p_symbol);
        if (q_symbol != NULL)
            erg += freeself(q_symbol);
        
        for (i=0;i<S_V_LI(a);i++)
            erg += schensted_row_insert_step(S_V_I(a,i),p_symbol,q_symbol);
        }
        ENDR("word_schen");
}

INT matrix_knuth(m,p_symbol,q_symbol) OP m,p_symbol,q_symbol;
{
    OP a,b;
    INT erg = OK;
    CTO(MATRIX,"matrix_knuth(1)",m);

    a = callocobject();
    b = callocobject();
    erg += matrix_twoword(m,a,b);
    erg += twoword_knuth(a,b,p_symbol,q_symbol);
    erg += freeall(a);
    erg += freeall(b);
    ENDR("matrix_knuth");
}

INT twoword_knuth(a,b,p_symbol,q_symbol) OP a,b,p_symbol,q_symbol;
/* bijection 0-1 matrix (a,b) nach (p_symbol,q_symbol) */
{
    INT i;
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"twoword_knuth(1)",a);
    CTTO(INTEGERVECTOR,VECTOR,"twoword_knuth(2)",b);
    erg += freeself(p_symbol);
    if (q_symbol != NULL)
    erg += freeself(q_symbol);
    
    for (i=0;i<S_V_LI(a);i++)
        erg += knuth_row_insert_step(S_V_I(a,i),S_V_I(b,i),p_symbol,q_symbol);

    conjugate(p_symbol,p_symbol);

    ENDR("twoword_knuth");
}

INT matrix_twoword(matrix, column_index, row_index) 
    OP matrix, column_index, row_index;
/* bijektion matrix mit zahlen >= 0 zu paar von integer vektoren */
{
    INT erg = OK,i,j,k,l;
    OP c;
    CE3(matrix, column_index, row_index,matrix_twoword);
    c = callocobject();
    erg += zeilen_summe(matrix,c);
    erg += sum(c,c);
    erg += m_l_v(c,column_index);
    erg += m_l_v(c,row_index);
    for(i=0,l=0;i<S_M_HI(matrix);i++)
    for(j=0;j<S_M_LI(matrix);j++)
    for(k=0;k<S_M_IJI(matrix,i,j);k++)
        {
        M_I_I(j+1,S_V_I(column_index,l));
        M_I_I(i+1,S_V_I(row_index,l));
        l++;
        }
    erg += freeall(c);
    ENDR("matrix_twoword");
}

INT twoword_matrix( c_index, row_index, matrix)
    OP matrix, c_index, row_index;
{
    INT erg = OK,i;
    OP c;
    CE3(c_index, row_index, matrix,twoword_matrix);
    CTTO(VECTOR,WORD,"twoword_matrix",c_index);
    CTTO(VECTOR,WORD,"twoword_matrix",row_index); 
    c = callocobject();
    erg += max(c_index,c);
    m_ilih_nm(S_I_I(c),S_V_II(row_index,S_V_LI(row_index)-1),matrix);
    for(i=0;i<S_V_LI(row_index);i++)
        inc_integer(S_M_IJ(matrix,S_V_II(row_index,i)-1,
                    S_V_II(c_index,i)-1));
    erg += freeall(c);
    ENDR("twoword_matrix");
}

INT knuth_twoword(a,b,cc,dd) OP a,b,cc,dd;
/* b wird fuer das q symbol verwendet = zeilennummern der 0 -1 matrix */
/* dd wird q -symbol */

{
    INT i;
    INT erg = OK;
    OP c,d;
    CTTO(INTEGERVECTOR,VECTOR,"knuth_twoword(1)",a);
    CTTO(INTEGERVECTOR,VECTOR,"knuth_twoword(2)",b);

    c = callocobject();
    d = callocobject();
    erg += conjugate(cc,c);
    erg += copy(dd,d);
    erg += weight(cc,a);
    erg += m_il_w(S_I_I(a),b);
    erg += m_il_w(S_I_I(a),a);
    for (i=S_V_LI(a)-1;i>=0;i--)
        erg += knuth_row_delete_step(S_V_I(a,i),S_V_I(b,i),c,d);
    erg += freeall(d);
    erg += freeall(c);
    ENDR("knuth_twoword");
}

INT schen_word(a,bb,cb) OP a,bb,cb;
/* input are the two tableaux
    bb and cc
   a becomes the result a word */
{
    INT i;
    INT erg = OK;
    OP c,b;
    CTO(TABLEAUX,"schen_word(2)",bb);
    CTO(TABLEAUX,"schen_word(3)",cb);
    c = callocobject();
    b = callocobject();
    erg += copy(bb,b);
    erg += copy(cb,c);
    erg += weight(b,a);
    erg += m_il_w(S_I_I(a),a);
    for (i=S_V_LI(a)-1;i>=0;i--)
        {
        erg += schensted_row_delete_step(S_V_I(a,i),b,c);
        }
    erg += freeall(b);
    erg += freeall(c);
    CTO(WORD,"schen_word(e1)",a);
    ENDR("schen_word");
}

INT knuth_row_insert_step(rein,qrein,P,Q) OP qrein,rein,P,Q;
/* for 01 matrices */
{
    INT erg = OK,i,j,k;
    OP c,z;
    CTTO(EMPTY,TABLEAUX,"knuth_row_insert_step(3)",P);
    c = callocobject();
    if (emptyp(P))  /* anfang */
        {
        m_ilih_m(10L,10L,c);
        if (Q != NULL)
            {
            copy(qrein,S_M_IJ(c,0,0));
            m_matrix_tableaux(c,Q);
            }
        copy(rein,S_M_IJ(c,0,0));
        b_matrix_tableaux(c,P);
        goto sk;
        }
    z = callocobject();
    i=0;copy(rein,z);
aa:
    k = ZEILENENDE(P,i);
    for (j=0;j<=k;j++)
        if (le(z,S_T_IJ(P,i,j))) break;
    if (j <= k)  /* d.h. im tableau */
        {
        if (
        (S_O_K(S_T_IJ(P,i,j)) == INTEGER) &&
        (S_O_K(z) == INTEGER)
        ) {
            M_I_I(S_T_IJI(P,i,j),c);
            M_I_I(S_I_I(z),S_T_IJ(P,i,j));
            M_I_I(S_I_I(c),z);
            }
        else {
        copy(S_T_IJ(P,i,j),c);
        copy(z,S_T_IJ(P,i,j));
        copy(c,z);
        }
        i++;
        if (i == S_T_ULI(P))
            {
            /* neue zeile */
            j=0;
            goto kk;
            }
        else goto aa;
        }
    else /* anhaengen */
        {
kk:
        freeself(c);
        swap(S_T_S(P),c); 
        if ((i >= S_M_HI(c)) || (j>= S_M_LI(c)) )
            {
            inc(c);
            }
        if (i < S_T_ULI(P))
            {
            if (S_O_K(z) == INTEGER)
                M_I_I(S_I_I(z),S_M_IJ(c,i,j));
            else
                copy(z,S_M_IJ(c,i,j));
            INC_INTEGER(S_T_UI(P,S_T_ULI(P)-1-i));
            swap(S_T_S(P),c); 
            freeall(c); /* AK 130297 */
            }
        else {
            copy(z,S_M_IJ(c,i,j));
            b_matrix_tableaux(c,P);
            }
        if (Q == NULL)
            {
            freeall(z);
            goto sk; /* nicht freigeben */
            }

        freeself(z);
        swap(S_T_S(Q),z);
        if ((i >= S_M_HI(z)) || (j>= S_M_LI(z)) )
            {
            inc(z);
            }
        if (i < S_T_ULI(Q))
            {
            copy(qrein,S_M_IJ(z,i,j));
            INC_INTEGER(S_T_UI(Q,S_T_ULI(Q)-1-i));
            swap(S_T_S(Q),z); 
            freeall(z);
            }
        else {
            copy(qrein,S_M_IJ(z,i,j));
            b_matrix_tableaux(z,Q);
            }
        goto sk;
        }
sk:
    ENDR("knuth_row_insert_step");
}

INT schensted_row_insert_step(rein,P,Q) OP rein,P,Q;
{
    INT erg = OK,i,j,k;
    OP c,z;
    CTTO(EMPTY,TABLEAUX,"schensted_row_insert_step(2)",P);
    c = callocobject();
    if (emptyp(P))  /* anfang */
        {
        m_ilih_m(10L,10L,c);
        if (Q != NULL)
            {
            m_i_i(1L,S_M_IJ(c,0,0));
            m_matrix_tableaux(c,Q);
            }
        copy(rein,S_M_IJ(c,0,0));
        b_matrix_tableaux(c,P);
        goto sk;
        }
    z = callocobject();
    i=0;copy(rein,z);
aa:
    k = ZEILENENDE(P,i);
    for (j=0;j<=k;j++)
        if (lt(z,S_T_IJ(P,i,j))) break;
    if (j <= k)  /* d.h. im tableau */
        {
        if (
        (S_O_K(S_T_IJ(P,i,j)) == INTEGER) &&
        (S_O_K(z) == INTEGER)
        ) {
            M_I_I(S_T_IJI(P,i,j),c);
            M_I_I(S_I_I(z),S_T_IJ(P,i,j));
            M_I_I(S_I_I(c),z);
            }
        else {
        copy(S_T_IJ(P,i,j),c);
        copy(z,S_T_IJ(P,i,j));
        copy(c,z);
        }
        i++;
        if (i == S_T_ULI(P))
            {
            /* neue zeile */
            j=0;
            goto kk;
            }
        else goto aa;
        }
    else /* anhaengen */
        {
kk:
        freeself(c);
        swap(S_T_S(P),c); 
        if ((i >= S_M_HI(c)) || (j>= S_M_LI(c)) )
            {
            inc(c);
            }
        if (i < S_T_ULI(P))
            {
            if (S_O_K(z) == INTEGER)
                M_I_I(S_I_I(z),S_M_IJ(c,i,j));
            else
                copy(z,S_M_IJ(c,i,j));
            INC_INTEGER(S_T_UI(P,S_T_ULI(P)-1-i));
            swap(S_T_S(P),c); 
            freeall(c); /* AK 130297 */
            }
        else {
            copy(z,S_M_IJ(c,i,j));
            b_matrix_tableaux(c,P);
            }
        if (Q == NULL)
            {
            freeall(z);
            goto sk; /* nicht freigeben */
            }
        weight(Q,z); k = S_I_I(z); /* gewicht */
        freeself(z);
        swap(S_T_S(Q),z);
        if ((i >= S_M_HI(z)) || (j>= S_M_LI(z)) )
            {
            inc(z);
            }
        if (i < S_T_ULI(Q))
            {
            M_I_I(k+1,S_M_IJ(z,i,j));
            INC_INTEGER(S_T_UI(Q,S_T_ULI(Q)-1-i));
            swap(S_T_S(Q),z); 
            freeall(z);
            }
        else {
            m_i_i(k+1,S_M_IJ(z,i,j));
            b_matrix_tableaux(z,Q);
            }
        goto sk;
        }
sk:
    ENDR("schensted_row_insert_step");
}


INT knuth_row_delete_step(raus,qraus,P,Q) OP raus,qraus,P,Q;
{
    INT i,j,l,k,erg = OK;
    OP c;
    CTO(TABLEAUX,"knuth_row_delete_step(3)",P);
    CTO(TABLEAUX,"knuth_row_delete_step(4)",Q);
    if (S_T_ULI(P) == 1)
        {
        i = ZEILENENDE(P,0);
        erg += copy_integer(S_T_IJ(P,0L,i),raus);
        erg += copy_integer(S_T_IJ(Q,0L,i),qraus);
        if (i==0) {
            erg += freeself(P);
            erg += freeself(Q);
            goto sre;
            }
        erg += dec_integer(S_T_UI(P,0));
        erg += dec_integer(S_T_UI(Q,0));
        erg += freeself_integer(S_T_IJ(P,0L,i));
        erg += freeself_integer(S_T_IJ(Q,0L,i));
        goto sre;
        }
    /* richtiges tableau */
    c = callocobject();
    max(Q,c);
    copy(c,qraus);
    /* jetzt suchen wo das max in Q vorkommt, davon aber dann den groessten wert in P*/
    find_knuth_tab_entry(P,Q,c,&i,&j);
    if (i == -1) 
        error("internal error:");    
    copy(S_T_IJ(P,i,j),c);
    freeself(S_T_IJ(P,i,j));
    freeself(S_T_IJ(Q,i,j));
    for (l=i-1;l>=0;l--)
        {
        i = ZEILENENDE(P,l);
        for (k=0;k<= i;k++)
            if (gt(S_T_IJ(P,l,k),c)) {
                break;
                }
            else if (eq(S_T_IJ(P,l,k),c)) {
                k++;
                break;
                }
        k--;
        /* nun an k setzen */
        swap(S_T_IJ(P,l,k),c);
        }
    copy(c,raus);
    copy(S_T_S(P),c);
    m_matrix_tableaux(c,P);
    copy(S_T_S(Q),c);
    b_matrix_tableaux(c,Q);
sre:
    ENDR("knuth_row_delete_step");
}

INT schensted_row_delete_step(raus,P,Q) OP raus,P,Q;
{
    INT i,j,l,k,erg = OK;
    OP c;
    CTO(TABLEAUX,"schensted_row_delete_step(2)",P);
    CTO(TABLEAUX,"schensted_row_delete_step(3)",Q);
    if (S_T_ULI(P) == 1)
        {
        i = ZEILENENDE(P,0);
        erg += copy(S_T_IJ(P,0L,i),raus);
        if (i==0) {
            erg += freeself(P);
            erg += freeself(Q);
            goto sre;
            }
        erg += dec(S_T_UI(P,0));
        erg += dec(S_T_UI(Q,0));
        erg += freeself(S_T_IJ(P,0L,i));
        erg += freeself(S_T_IJ(Q,0L,i));
        goto sre;
        }
    /* richtiges tableau */
    c = callocobject();
    weight(Q,c);
    find_tab_entry(Q,c,&i,&j);
    if (i == -1) error("internal error:");    
    copy(S_T_IJ(P,i,j),c);
    freeself(S_T_IJ(P,i,j));
    freeself(S_T_IJ(Q,i,j));
    for (l=i-1;l>=0;l--)
        {
        i = ZEILENENDE(P,l);
        for (k=0;k<= i;k++)
            if (ge(S_T_IJ(P,l,k),c)) break;
        k--;
        /* nun an k setzen */
        swap(S_T_IJ(P,l,k),c);
        }
    copy(c,raus);
    copy(S_T_S(P),c);
    m_matrix_tableaux(c,P);
    copy(S_T_S(Q),c);
    b_matrix_tableaux(c,Q);
    sre:
    ENDR("schensted_row_delete_step");
}


                      
INT all_plactic_word(w,c) OP w,c;
/* AK 211195 */
/* enter a word return all plactic equivalent words */
/* using Schensted */
/* AK 240398 V2.0 */
{
    OP a,b,d;
    INT i, erg = OK;
    CTO(WORD,"all_plactic_word(1)",w);
    a = callocobject();
    b = callocobject();
    d = callocobject();
    erg += word_schen(w,a,b);
    erg += last_partition(S_V_L(w),b);
    erg += kostka_tab(S_T_U(a),b,d);
    erg += t_LIST_VECTOR(d,b);
    erg += m_il_v(S_V_LI(b),c);
    for (i=0;i<S_V_LI(b);i++)
        erg += schen_word(S_V_I(c,i),a,S_V_I(b,i));
    FREEALL3(a,b,d);
    ENDR("all_plactic_word");
}

INT inverse_nilplactic_jeudetaquin_tableaux(a,si,sj,b) OP a,b;INT si,sj;
/* AK 120790 V1.1 */ /* AK 200691 V1.2 */ /* AK 200891 V1.3 */
    {
    OP self,umriss;
    INT posi,posj; /* aktuelle position des jokers */
    OP unten, links;
    if (not EMPTYP(b) ) freeself(b);
    if (sj != ZEILENENDE(a,si)+1L)
        return error("INV_NILJDT: illegel index");
    if (S_O_K(S_T_U(a)) == PARTITION)
        if (si > S_T_ULI(a))
            return error("INV_NILJDT: illegel index");
    if (S_O_K(S_T_U(a)) == SKEWPARTITION)
        if (si > S_T_UGLI(a))
            return error("INV_NILJDT: illegel index");
    self = callocobject();
    copy(S_T_S(a),self);
    if (sj == S_M_LI(self)) inc(self);
    if (si == S_M_HI(self)) inc(self);
    posi = si; posj = sj;
m120790again:
    unten = NULL; links = NULL;
    if (posj > 0L) {
        links = S_M_IJ(self, posi, posj-1L);
        if (EMPTYP(links)) links = NULL;}
    if (posi > 0L) {
        unten = S_M_IJ(self, posi-1L, posj);
        if (EMPTYP(unten)) unten = NULL;}

    if ((links == NULL) && (unten == NULL))
        {
        /* Abbruchbedingung */
        C_O_K(S_M_IJ(self,posi,posj),EMPTY);
        umriss = callocobject(); 
        m_matrix_umriss(self,umriss);
        return b_us_t(umriss,self,b); 
        }

    if (links == NULL) 
        { M_I_I(S_I_I(unten), S_M_IJ(self,posi,posj));
        posi--; goto m120790again; }
    if (unten == NULL) 
        { M_I_I(S_I_I(links), S_M_IJ(self,posi,posj));
        posj--; goto m120790again; }
    if (S_I_I(unten) == S_I_I(links))
        {
        if ( not emptyp(S_M_IJ(self,posi-1L,posj-1L)))
        if ( S_M_IJI(self,posi-1L,posj-1L) == S_I_I(links)-1L )
            {
            /* jetzt anwenden der nilplactic relationen */
            INT i;
            M_I_I(S_M_IJI(self,posi,posj-1L),
                  S_M_IJ(self,posi,posj));
            for (i=1L; i <= posi ; i++)
                {
                if (
                    (S_M_IJI(self,posi-i,posj-1L) 
                    != S_I_I(links)-i)  ||
                    (S_M_IJI(self,posi-i,posj) 
                    != S_I_I(links)-i+1L)  
                   ) break;
                M_I_I(S_M_IJI(self,posi-i,posj-1L),
                      S_M_IJ(self,posi-i,posj));
                }
            posj--;
            goto m120790again;
            }
        }
    if (S_I_I(unten) >= S_I_I(links))
        { M_I_I(S_I_I(unten), S_M_IJ(self,posi,posj));
        posi--; goto m120790again; }
    else
        { M_I_I(S_I_I(links), S_M_IJ(self,posi,posj));
        posj--; goto m120790again; }
    
    }


INT inverse_jeudetaquin_tableaux(a,si,sj,b) OP a,b;INT si,sj;
/* AK 100790 V1.1 */ /* AK 200891 V1.3 */
    {
    OP self,umriss;
    INT posi,posj; /* aktuelle position des jokers */
    OP unten, links;
    if (not EMPTYP(b) ) freeself(b);
    if (sj != ZEILENENDE(a,si)+1L)
        return error("inverse_jeudetaquin_tableaux: illegel index");
    self = callocobject();
    copy(S_T_S(a),self);
    if (sj == S_M_LI(self)) inc(self);
    if (si == S_M_HI(self)) inc(self);
    posi = si; posj = sj;
m100790again:
    unten = NULL; links = NULL;
    if (posj > 0L) {
        links = S_M_IJ(self, posi, posj-1L);
        if (EMPTYP(links)) links = NULL;}
    if (posi > 0L) {
        unten = S_M_IJ(self, posi-1L, posj);
        if (EMPTYP(unten)) unten = NULL;}

    if ((links == NULL) && (unten == NULL))
        {
        /* Abbruchbedingung */
        C_O_K(S_M_IJ(self,posi,posj),EMPTY);
        umriss = callocobject(); 
        m_matrix_umriss(self,umriss);
        b_us_t(umriss,self,b); return(OK);
        }
    if (links == NULL) 
        { M_I_I(S_I_I(unten), S_M_IJ(self,posi,posj));
        posi--; goto m100790again; }
    if (unten == NULL) 
        { M_I_I(S_I_I(links), S_M_IJ(self,posi,posj));
        posj--; goto m100790again; }
    if (S_I_I(unten) >= S_I_I(links))
        { M_I_I(S_I_I(unten), S_M_IJ(self,posi,posj));
        posi--; goto m100790again; }
    else
        { M_I_I(S_I_I(links), S_M_IJ(self,posi,posj));
        posj--; goto m100790again; }
    
    }

INT jeudetaquin_tableaux(a,b) OP a,b;
/* AK 080688 */
/* Jeu de Taquin auf a wird b . a ist schieftableau und wird ein tableau b */
/* AK 010889 V1.1 */ /* AK 200891 V1.3 */
    {
    OP self,umriss,unten,rechts;
    INT i,j; 
    INT posi,posj;  /* aktuelle position des jokers */
    INT nexti,nextj;  /* naechste position des jokers */
    INT si= -1,sj= -1; /* start of joker */

    if (S_O_K(S_T_U(a)) == PARTITION) return copy(a,b);

    self = callocobject(); 
    copy (S_T_S(a),self);
m0806883: /* ein neues spiel */
    i = 0L;
    for (j=0L;j<S_M_LI(self);j++)
        if (not EMPTYP(S_M_IJ(self,i,j)))
            {
            if (j == 0L) goto m080688stop1; /* ende */
                    /* man hat ein tableaux */


            /* spalte mit eintrag */
            j = j - 1L; 
            for (i=0L;i<S_M_HI(self);i++)
                if (not EMPTYP(S_M_IJ(self,i,j)))
                    { si=i-1L;sj=j;goto m0806881;}
            };
m0806881:    /* si,sj die position des jokers */
    posi = si; posj = sj;
m0806882:     /* next step */
        /* nach richtung kleineres element, bei gleich nach unten */
    unten = NULL; rechts = NULL;
    if (posi+1 < S_M_HI(self)) /* joker nicht in unterste zeile */
        {
        unten = S_M_IJ(self,posi+1L,posj);
        if (EMPTYP(unten)) unten = NULL;
        };
    if (posj+1 < S_M_LI(self)) /* joker nicht in letzter spalte */
        {
        rechts = S_M_IJ(self,posi,posj+1L);
        if (EMPTYP(rechts)) rechts = NULL;
        };
    if ( (unten == NULL) && (rechts == NULL) ) 
        /* ende ein neues spiel */ goto m0806883;
    if ( (unten == NULL))  /* nach rechts */
        { nexti = posi; nextj=posj+1L; }
    else if ( (rechts == NULL))  /* nach unten */
        { nexti = posi+1L; nextj=posj; }
    else /* in beide richtungen ist noch ein eintrag */
        {
        if (lt(rechts,unten))
            { nexti = posi; nextj=posj+1L; }
        else    { nexti = posi+1L; nextj=posj; };
        };

    copy(S_M_IJ(self,nexti,nextj),S_M_IJ(self,posi,posj));
    freeself(S_M_IJ(self,nexti,nextj));
    posi=nexti; posj=nextj;
    goto m0806882; /* noch eine runde */
m080688stop1: /* wir sind fertig,aus der matrix wird ein tableau */
    umriss = callocobject(); 
    m_matrix_umriss(self,umriss);
    b_us_t(umriss,self,b); 
    return(OK);
    }

INT next_lex_tableaux(a,b) OP a,b;
/* computes the next row equivalent tableau */
/* input tableau of partition shape 
   output lexicographic next row equivalent tableau 
          i.e. in general a non standard tableau
   return TRUE if there is a next tableau
          FALSE else
*/
/* AK 060802 */
{
    INT erg = OK;
    CTO(TABLEAUX,"next_lex_tableaux(1)",a);
    CTO(PARTITION,"next_lex_tableaux(1-shape)",S_T_U(a));
    {
    INT i,res,j;
    OP v;
    v = CALLOCOBJECT();
    m_il_v(S_T_HI(a),v);
    for (i=0;i<S_V_LI(v);i++) select_row(a,i,S_V_I(v,i));
    for (i=S_V_LI(v)-1;i>=0;i--)
        {
        res = next_lex_vector(S_V_I(v,i),S_V_I(v,i));
        if (res != FALSE) break;
        }
    if (i==-1) res = FALSE; else res=TRUE;
    if (res ==TRUE)
        {
        for (i++;i<S_V_LI(v);i++)
             erg += qsort_vector(S_V_I(v,i));
        }
     
    if (a !=b) erg += copy(a,b);
    for (i=0;i<S_V_LI(v);i++)
    for (j=0;j<S_V_LI(S_V_I(v,i)); j++)
         M_I_I(S_V_II(S_V_I(v,i),j), S_T_IJ(b,i,j));
    FREEALL(v);
    return res;
    }
    ENDR("next_lex_tableaux");
} 

INT first_lex_tableaux(a,b) OP a,b;
/* computes the first row equivalent tableau */
/* input tableau of partition shape
   output lexicographic first row equivalent tableau
          i.e. ordering in the rows
*/
/* AK 060802 */
{
    INT erg = OK;
    CTO(TABLEAUX,"first_lex_tableaux(1)",a);
    CTO(PARTITION,"first_lex_tableaux(1-shape)",S_T_U(a));
    {
    INT i,res,j;
    OP v;
    v = CALLOCOBJECT();
    m_il_v(S_T_HI(a),v);
    for (i=0;i<S_V_LI(v);i++) select_row(a,i,S_V_I(v,i));
    for (i=S_V_LI(v)-1;i>=0;i--)
        erg+= qsort_vector(S_V_I(v,i));
 
    if (a !=b) erg += copy(a,b);
    for (i=0;i<S_V_LI(v);i++)
    for (j=0;j<S_V_LI(S_V_I(v,i)); j++)
         M_I_I(S_V_II(S_V_I(v,i),j), S_T_IJ(b,i,j));
    FREEALL(v);
    }
    ENDR("first_lex_tableaux");
}   
#endif /* TABLEAUXTRUE */

