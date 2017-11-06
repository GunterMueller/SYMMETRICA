/* file: matrix.c */ /* AK 091086 */
#include "def.h"
#include "macro.h"

#ifdef MATRIXTRUE
static struct matrix * callocmatrix();
static INT scan_matrix_co();

static INT transform_matrix(a,f,b) OP a,b; INT (*f)();
{
    INT e = 0L;
    INT i,j,erg = OK;
    CTO(MATRIX,"transform_matrix(1)",a);

    if (a==b)
        {    
        OP c = callocobject();
        *c = *a;
        C_O_K(b,EMPTY);
        e = 1L;
        a = c;
        }
    m_ilih_m(S_M_LI(a),S_M_HI(a),b);
    for (i=0L;i<S_M_HI(b);i++)
        for (j=0L;j<S_M_LI(b);j++)
            erg += (*f)(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
    if (e==1L)
        erg += freeall(a);
    ENDR("internal function:transform_matrix");
}

INT cast_apply_matrix(a) OP a;
/* AK 270295 */
{
    INT i,ml,erg = OK,j;
    OP b;
    EOP("cast_apply_matrix(1)",a);

    if (S_O_K(a) == MATRIX)
        goto camb;
    else if (S_O_K(a) == KOSTKA)
        goto camb;
    else if (S_O_K(a) == VECTOR)
        {
        ml = 0;
        for (i=(INT)0;i<S_V_LI(a);i++)
            {
            if (not VECTORP(S_V_I(a,i)))
                goto came;
            if (S_V_LI(S_V_I(a,i)) > ml)
                ml = S_V_LI(S_V_I(a,i));
            }
            
        /* now vector of vector == we can cast */
        b = callocobject();
        *b = *a;
        C_O_K(a,EMPTY);
        erg += m_ilih_m(ml,S_V_LI(b),a);
        for (i=0;i<S_M_HI(a);i++)
        for (j=0;j<S_V_LI(S_V_I(b,i));j++)
            {
            * S_M_IJ(a,i,j) = * S_V_I(S_V_I(b,i),j);
            C_O_K(S_V_I(S_V_I(b,i),j),EMPTY);
            }
        erg += freeall(b);
        goto camb;
        }
came:
    printobjectkind(a);
    erg += error("cast_apply_matrix: transfer not possible");
camb:
    ENDR("cast_apply_matrix");
}

INT mem_size_matrix(a) OP a;
/* AK 150295 */
{
    INT erg = 0,i,j;
    OP z;
    if (a == NULL) return 0;
   
    if (not MATRIXP(a)) WTO("mem_size_matrix",a);
    erg += sizeof(struct object);
    erg += sizeof(struct matrix);
    erg += mem_size(S_M_H(a));
    erg += mem_size(S_M_L(a));
    for (i=S_M_HI(a)*S_M_LI(a)-1,z=S_M_S(a);i>=0;i--,z++)
        erg += mem_size(z);
    return erg;
}



INT mod_matrix(a,b,c) OP a,b,c;
/* AK 300793 */
{
    INT erg = OK;
    INT i,j;
    CTO(MATRIX,"mod_matrix(1)",a);
    CTO(INTEGER,"mod_matrix(2)",b);
    CTO(EMPTY,"mod_matrix(3)",c);

    erg += m_ilih_m(S_M_LI(a),S_M_HI(a),c);
    for (i=0L;i<S_M_HI(a);i++)
    for (j=0L;j<S_M_LI(a);j++)
        erg += mod(S_M_IJ(a,i,j),b,S_M_IJ(c,i,j));
    ENDR("mod_matrix");
}

INT matrixp(a) OP a;
/* AK 280193 */
{
    if (S_O_K(a) == MATRIX)     return TRUE;
    if (S_O_K(a) == KRANZTYPUS)     return TRUE;
    if (S_O_K(a) == INTEGERMATRIX)     return TRUE;
    return FALSE;
}



INT addinvers_matrix(a,b) OP a,b;
/* AK 240293 */
/* AK 060704 V3.0 */
{
    return transform_matrix(a,addinvers,b);
}

INT absolute_matrix(a,b) OP a,b;
/* AK 240293 */
/* AK 060704 V3.0 */
{
    return transform_matrix(a,absolute,b);
}

INT sum_matrix(a,b) OP a,b;
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGERMATRIX,MATRIX,"sum_matrix(1)",a);
        {
        INT i;
        OP z = S_M_S(a);
        CLEVER_COPY(S_M_IJ(a,S_M_HI(a)-1,S_M_LI(a)-1),b);
        for (i=S_M_HI(a)*S_M_LI(a);i>1;i--,z++)
            ADD_APPLY(z, b);
        }
    ENDR("sum_matrix");
}
    

INT nullp_integermatrix(a) OP a;
/* AK 150802 */
/* AK 060704 V3.0 */
{
    INT erg = OK;
    CTO(INTEGERMATRIX,"nullp_integermatrix(1)",a);
        {
        INT i,j;
        for (i=0L;i<S_M_HI(a);i++)
            for (j=0L;j<S_M_LI(a);j++)
                if (not NULLP_INTEGER(S_M_IJ(a,i,j))) return FALSE;
        return TRUE;
        }
    ENDR("nullp_integermatrix");
}


INT nullp_matrix(a) OP a;
/* AK 110992 */
{
    INT i,j;
    for (i=0L;i<S_M_HI(a);i++)
        for (j=0L;j<S_M_LI(a);j++)
            if (not NULLP(S_M_IJ(a,i,j))) return FALSE;
    return TRUE;
}




INT einsp_matrix(a) OP a;
/* AK 110992 */
{
    INT i,j;
    INT erg = OK;
    CTTO(INTEGERMATRIX,MATRIX,"einsp_matrix(1)",a);
    if (S_M_HI(a) != S_M_LI(a)) return FALSE;
    for (i=0L;i<S_M_HI(a);i++)
        for (j=0L;j<S_M_HI(a);j++)
            if (i==j) 
                {
                if (not EINSP(S_M_IJ(a,i,j))) return FALSE;
                }
            else    {
                if (not NULLP(S_M_IJ(a,i,j))) return FALSE;
                }
    return TRUE;
    ENDR("einsp_matrix");
}


INT delete_row_matrix(a,index,b) INT index; OP a,b;
/* AK 270789 */ /* AK 111289 V1.1 */ /* AK 110691 V1.2 */ 
/* AK 070891 V1.3 */ /* AK 201204 V3.0 */
/* AK 021106 V3.1 */
{
    INT i,j;
    INT erg = OK;
    SYMCHECK(index >= S_M_HI(a), "delete_row_matrix: index too big");
    SYMCHECK(index < 0,"delete_row_matrix: index < 0");

    
    if (a==b) {  /* AK 201204 */
        OP z,w;
        for (z=S_M_IJ(a,index,0),i=0;i<S_M_LI(a);i++,z++)
            FREESELF(z);
        z = S_M_IJ(a,index,0);
        w = S_M_IJ(a,index+1,0);
        for (i=index+1;i<S_M_HI(a);i++)
        for (j=0;j<S_M_LI(a);j++,z++,w++) SWAP(z,w);
        // now there is a row with empty objects at the end
        C_M_S(a, (OP) SYM_realloc((char*)S_M_S(a), 
                             (int) (S_M_HI(a)-1)*S_M_LI(a)*sizeof(struct object)
                            )
             );
        C_M_HASH(a,-1);
        M_I_I(S_M_HI(a)-1,S_M_H(a));
        goto endr_ende;
    }

    erg += m_ilih_m(S_M_LI(a),S_M_HI(a)-1L,b);
    C_O_K(b,S_O_K(a));
    for (i=0;i<index;i++)
        for (j=0;j<S_M_LI(a);j++)
            COPY(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
    for (i=index+1;i<S_M_HI(a);i++)
        for (j=0;j<S_M_LI(a);j++)
            COPY(S_M_IJ(a,i,j),S_M_IJ(b,i-1L,j));
    ENDR("delete_row_matrix");
}



INT append_column_matrix(a,b,c) OP a,b,c;
/* AK 240206 V3.0 */
/* appends the vector object b as a last column to the matrix a */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"append_column_matrix(1)",a);
    CTTO(VECTOR,INTEGERVECTOR,"append_column_matrix(2)",b);
    SYMCHECK(S_M_HI(a) != S_V_LI(b),"append_column_matrix: vector of wrong length");
    {
    INT i,j;
    if (a==c) {
        OP d = CALLOCOBJECT();
        *d = *a; 
        C_O_K(c,EMPTY);
        erg += append_column_matrix(d,b,c);
        FREEALL(d);
        goto endr_ende;
        }
    erg += m_ilih_m(S_M_LI(a)+1L,S_M_HI(a),c);
    C_O_K(c,S_O_K(a));
    for (i=0;i<S_M_HI(a);i++)
    for (j=0;j<S_M_LI(a);j++) COPY(S_M_IJ(a,i,j),S_M_IJ(c,i,j));
    for (i=0;i<S_M_HI(a);i++) COPY(S_V_I(b,i),S_M_IJ(c,i,S_M_LI(c)-1));
    }
    ENDR("append_column_matrix");
}

INT delete_column_matrix(a,index,b) INT index; OP a,b;
/* deletes the column with index i
   the result b is of the same type like a */
/* AK 270789 */ /* AK 310790 V1.1 */ /* AK 110691 V1.2 */ 
/* AK 070891 V1.3 */
/* AK 240206 V3.0 */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"delete_column_matrix(1)",a);
    SYMCHECK(index >= S_M_LI(a),"delete_column_matrix: index too big");
    SYMCHECK(index <0,"delete_column_matrix: index < 0");
    {
    INT i,j;


    if (a==b) {
        OP c = CALLOCOBJECT();
        *c = *b; 
        C_O_K(b,EMPTY);
        erg += delete_column_matrix(c,index,b);
        FREEALL(c);
        goto endr_ende;
    }

    erg += m_ilih_m(S_M_LI(a)-1L,S_M_HI(a),b);
    C_O_K(b,S_O_K(a));
    for (j=0;j<index;j++)
        for (i=0;i<S_M_HI(a);i++)
            COPY(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
    for (j=index+1;j<S_M_LI(a);j++)
        for (i=0;i<S_M_HI(a);i++)
            COPY(S_M_IJ(a,i,j),S_M_IJ(b,i,j-1));
    }

    ENDR("delete_column_matrix");
}



INT det_matrix(a,b) OP a,b; 
/* AK 151289 V1.1 */ /* AK 110691 V1.2 */
/* hier wird zum konkreten algorithmus geschaltet */
/* AK 210891 V1.3 */
/* AK 141098 V2.0 */
{ 
    if (not quadraticp(a))
        { 
        error("det_matrix: not quadratic matrix"); 
        return(ERROR); 
        }
    return det_mat_tri(a,b); 
}



INT det_mat_tri(a,res) OP a,res;
/* AK Fri Jan 20 12:29:58 MEZ 1989
algorithmus zur berechnung der determinante einer matrix a
mittels triangulation
ergebnis in res
algorithmus 41 in CACM */
/* verbessert 1963 */
/* immer noch fehler bei zeilenvertauschung */
/* AK 310790 V1.1 */ /* AK 110691 V1.2 */
/* AK 210891 V1.3 */
{
    INT r,i,j,y,count,sign=1L,n;
    INT erg = OK;
    OP  b,  factor,temp;

    CTO(MATRIX,"det_mat_tri(1)",a);

    n = S_M_LI(a);
    b = callocobject(); 

    erg += m_i_i(1L,res);
    factor = callocobject(); 
    temp = callocobject();

    erg += copy(a,b);

    for (r=1;r < n;r++)
    {
        count = r-1;
        if (not nullp(S_M_IJ(b,r-1L,r-1))) goto det_mat_tri_resume;
det_mat_tri_zerocheck:
        if (count < (n-1)) count++;
        else goto det_mat_tri_zero;

        if (not nullp(S_M_IJ(b,count,r-1))) {
        for (y=r; y<=n; y++)
            {
            erg += swap(S_M_IJ(b,count,y-1),S_M_IJ(b,r-1L,y-1));
            }
        sign = -sign; goto det_mat_tri_resume;
        }


        goto det_mat_tri_zerocheck;
det_mat_tri_zero:
        erg += m_i_i((INT)0,res); 
        goto det_mat_tri_return;
det_mat_tri_resume:
        for (i=r+1; i<=n; i++)
        {
                
            erg += div(S_M_IJ(b,i-1L,r-1),S_M_IJ(b,r-1L,r-1),factor);
            for (j=r+1;j<=n;j++)
            {
                erg += mult(factor,S_M_IJ(b,r-1L,j-1),temp);
                erg += addinvers_apply(temp);
                erg += add_apply(temp,S_M_IJ(b,i-1L,j-1L));
            }
        }
    }

    for (i=1;i<=n;i++)
        erg += mult_apply(S_M_IJ(b,i-1L,i-1),res);


    if (sign == -1L) 
        erg += addinvers_apply(res);
    
det_mat_tri_return:
    FREEALL3(temp,factor,b);
    ENDR("det_mat_tri");
}



INT m_ilih_nm(l,h,m) OP m; INT l,h;
/* mit 0 vorbesetzen */
/* make_intlength_intheight_null_matrix */
{
    INT i,erg = OK;
    OP z;
    SYMCHECK(l < 0,"m_ilih_nm:l<0");
    SYMCHECK(h < 0,"m_ilih_nm:h<0");

    erg += m_ilih_m(l,h,m);
    for (z=S_M_S(m), i=S_M_HI(m) * S_M_LI(m); i>0L; i--,z++)
        M_I_I(0L,z);
    ENDR("m_ilih_nm");
}

INT m_lh_nm(l,h,m) OP l,h,m;
/* AK 110691 V1.2 */ /* mit 0 vorbesetzen */
/* make_length_height_null_matrix */
/* AK 210891 V1.3 */
{
    INT i,erg = OK;
    OP z;
    CTO(INTEGER,"m_lh_nm(1)",l);
    CTO(INTEGER,"m_lh_nm(2)",h);
    SYMCHECK(S_I_I(l) < 0,"m_lh_nm:l<0");
    SYMCHECK(S_I_I(h) < 0,"m_lh_nm:h<0");

    erg += m_lh_m(l,h,m);
    for (z=S_M_S(m), i=S_M_HI(m) * S_M_LI(m); i>0L; i--,z++)
        M_I_I(0L,z);
    ENDR("m_lh_nm");
}


INT b_lh_nm(l,h,m) OP l,h,m;
/* AK 110691 V1.2 */
/* mit 0 vorbesetzen */
/* build_length_height_null_matrix */
/* AK 210891 V1.3 */
{
    INT i,erg = OK;
    OP z;
    CTO(INTEGER,"b_lh_nm",l);
    CTO(INTEGER,"b_lh_nm",h);
    erg += b_lh_m(l,h,m);
    for (z=S_M_S(m), i=S_M_HI(m) * S_M_LI(m); i>0L; i--,z++)
        M_I_I(0L,z);
    ENDR("b_lh_nm");
}


INT b_lh_m(l,h,m) OP l,h,m;
/* build_length_height_matrix */
/* height und length werden nicht kopiert */
/* AK 250590 V1.1 */ /* AK 110691 V1.2 */
/* AK 210891 V1.3 */
{
    OP s;
    INT i;
    INT erg = OK;
    CTO(INTEGER,"b_lh_m",l);
    CTO(INTEGER,"b_lh_m",h);
    i = S_I_I(l)*S_I_I(h);
    if (i < 0)
        {
        erg += error("b_lh_m:negative values for dimension of a matrix");
        }
    else if (i==0)
        {
        erg += b_lhs_m(l,h,NULL,m);
        }
    else
        {
        s = (OP) SYM_malloc(S_I_I(l)*S_I_I(h)*sizeof(struct object));
        for (i=0L;i<S_I_I(l)*S_I_I(h); i++) C_O_K(s+i,EMPTY);
        erg += b_lhs_m(l,h,s,m);
        }
    ENDR("b_lh_m");
}



INT m_lh_m(len,height,matrix) OP height, len, matrix;
/* make_length_height_matrix */
/* height und length werden kopiert */
/* AK 041286 */ /* AK 070789 V1.0 */ /* AK 310790 V1.1 */
/* AK 260291 V1.2 */ /* AK 210891 V1.3 */
/* AK 250398 V2.0 */ /* AK 140205 V3.0 */
/* parameter may be equal */
{
    INT erg = OK;
    INT li,hi;
    CTO(INTEGER,"m_lh_m",len);
    CTO(INTEGER,"m_lh_m",height);
    hi = S_I_I(height);
    li = S_I_I(len);
    SYMCHECK(li<0,"m_lh_m:negative length");
    SYMCHECK(hi<0,"m_lh_m:negative height");
    SYMCHECK(hi*li<0,"m_lh_m:size too large");

    erg += b_lhs_m(
        callocobject(), 
        callocobject(),
            (struct object *) SYM_calloc((int)(hi*li),
            sizeof(struct object)),
        matrix);
    M_I_I(li,S_M_L(matrix)); 
    M_I_I(hi,S_M_H(matrix));
    ENDR("m_lh_m");
}


INT b_lhs_m(len,height,self,res) OP len, height, self, res;
/* AK 060789 V1.0 */ /* AK 081289 V1.1 */ /* AK 110691 V1.2 */
/* AK 210891 V1.3 */
{
    OBJECTSELF d;

    d.ob_matrix = callocmatrix();
    b_ks_o(MATRIX, d, res);
    C_M_L(res,len); 
    C_M_H(res,height);
    C_M_S(res,self);
    C_M_HASH(res,-1);
    return(OK);
}

INT hash_matrix(a) OP a;
/* AK 110703 */
{
    INT erg = OK;
    INT i,j;
    SYMCHECK(not MATRIXP(a),"hash_matrix: no matrix object");
    if (S_M_HI(a) == 0) return 4711;
    if (S_M_LI(a) == 0) return 4711;
    if (S_M_HASH(a) == -1)
        {
        INT res = 1;
        OP z;
        FORALL(z,a,
            {
            res *=  4711;
            res += HASH(z);
            });
        C_M_HASH(a,res);
        }
    return (S_M_HASH(a)); 
  
    ENDR("hash_matrix");
}

INT eq_matrix(a,b) OP a,b;
/* AK 110703 */
{
    INT erg = OK;
    INT i,j; OP za,zb;
    SYMCHECK(!MATRIXP(a),"eq_matrix(1): no matrix");
    if (! MATRIXP(b)) return FALSE;
    if (S_M_HI(a) != S_M_HI(b)) return FALSE;
    if (S_M_LI(a) != S_M_LI(b)) return FALSE;
    if (S_M_HASH(a) != -1)
    if (S_M_HASH(b) != -1)
    if (S_M_HASH(a) != S_M_HASH(b)) 
        {
        return FALSE;
        }

    if (S_O_K(a) == INTEGERMATRIX)
    if (S_O_K(b) == INTEGERMATRIX)
    return (comp_integermatrix(a,b)==0);

    for (i=0,za=S_M_S(a),zb=S_M_S(b); i<S_M_HI(a); i++) /* AK 210104 */
    for (j=0;j<S_M_LI(a);j++,za++,zb++)
        if (not EQ(za,zb)) return FALSE;
    return TRUE;
    ENDR("eq_matrix");
}




INT m_ilih_m(len,height,matrix) INT height, len; OP matrix;
/* AK 090988 */ /* AK 070789 V1.0 */ /* AK 310790 V1.1 */
/* AK 210891 V1.3 */
{
    INT erg=OK;
    SYMCHECK(len < 0, "m_ilih_m:length < 0");
    SYMCHECK(height < 0, "m_ilih_m:height < 0");
    if (len*height == 0) /* AK 210802 */
        {
        erg += b_lhs_m(    CALLOCOBJECT(),
                           CALLOCOBJECT(),
                           NULL,
                           matrix
                      );
        }
    
    else {   
ma:     erg = OK;
        erg += b_lhs_m(    CALLOCOBJECT(),
                           CALLOCOBJECT(),
                           (struct object *) SYM_calloc( (int) (height*len),
                                                         sizeof(struct object)
                                                       ),
                           matrix
                      );

        if (S_M_S(matrix) == NULL) 
            {
            INT err;
            err = error("m_ilih_m:self == NULL ");
            if (err==ERROR_EXPLAIN) 
                fprintf(stderr,
                        "I wanted a %ld  x %ld matrix", 
                        len,
                        height
                       ); 
            if (err==ERROR_RETRY) 
                goto ma;
            }
        }
    M_I_I(len,S_M_L(matrix));
    M_I_I(height,S_M_H(matrix));
    ENDR("m_ilih_m");
}


INT quadraticp(mat) OP mat;
/* AK 060789 V1.0 */ /* AK 310790 V1.1 */
/* AK 210891 V1.3 */
{
    return(S_M_LI(mat) == S_M_HI(mat));
}




#ifdef PERMTRUE
static INT det050995(mat,perm,c) OP mat,perm,c;
/* brechnet aus Matrix (a_ij) und der Permutation p_1,..,p_n
den wert p_1,p_2 * p_3,p_4 * .. */
{
    INT i,erg = OK;
    CTO(MATRIX,"det050995(1)",mat);
    CTO(PERMUTATION,"det050995(2)",perm);

    if (neq(S_M_L(mat),S_P_L(perm)))
        return error("det050995:wrong lengthes");

    erg += copy(S_M_IJ(mat,S_P_II(perm,0L)-1,S_P_II(perm,1L)-1L),c);

    for (i=2L;i<S_P_LI(perm);i+=2)
        {
        erg += mult_apply(S_M_IJ(mat,S_P_II(perm,i)-1L,S_P_II(perm,i+1)-1L),c);
        }

    ENDR("internal routine:det050995");
}
INT det270588(mat,perm,c) OP mat,perm,c;
/* AK270588 */
/* brechnet aus Matrix (a_ij) und der Permutation p_1,..,p_n
den wert a_1,p_1 * a_2,p_2 * .. a_n,p_n */
/* damit kann z.b. die determinante berechnet werden */
/* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 180691 V1.2 */
/* AK 210891 V1.3 */
{
    INT i,erg = OK;
    CTO(MATRIX,"det270588(1)",mat);
    CTO(PERMUTATION,"det270588(2)",perm);
    SYMCHECK(S_M_HI(mat) != S_M_LI(mat), "det270588:not quadratic");
    SYMCHECK(S_M_LI(mat) != S_P_LI(perm), "det270588:wrong lengthes");

    FREESELF(c);
    COPY(S_M_IJ(mat,0L,S_P_II(perm,0L)-1L),c);

    for (i=1L;i<S_P_LI(perm);i++)
        {
        MULT_APPLY(S_M_IJ(mat,i,S_P_II(perm,i)-1L),c);
        if (NULLP(c)) break;
        }

    CTO(ANYTYPE,"det270588(e)",c);
    ENDR("det270588");
}



#ifdef CHARTRUE
INT det_mat_imm(mat,erg) OP mat,erg; 
    { 
    return det_imm_matrix(mat,erg); 
    }

INT det_imm_matrix(mat,b) OP mat,b;
/* AK 270588 neue version mit immanente */
/* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 180691 V1.2 */
/* AK 210891 V1.3 */
/* AK 260603 V2.0 */
{
    OP part;
    INT erg = OK; /* AK 301292 */
    CTTO(MATRIX,INTEGERMATRIX,"det_imm_matrix(1)",mat);
    SYMCHECK(S_M_HI(mat)!=S_M_LI(mat),"det_imm_matrix:not quadratic matrix");
    CE2(mat,b,det_imm_matrix);


    if (S_M_HI(mat) == 1L)  /* AK 301292 */
        {
        COPY(S_M_IJ(mat,0L,0L),b);
        }
    else {
        part = CALLOCOBJECT();
        erg += last_partition(S_M_H(mat),part); 
        /* = 1,1,1,1,1,..,1 */
        erg += immanente_matrix(mat,part,b);
        /* der zugehoerige Charakter ist das signum */
        FREEALL(part);
        }
    ENDR("det_imm_matrix");
}

static INT co_050995(a) OP a;
{
    INT i;
    for (i=0; i< S_P_LI(a) ; i+= 2)
        {
        if (S_P_II(a,i) > S_P_II(a,i+1)) return FALSE;
        if (i > 0)
            if (S_P_II(a,i) < S_P_II(a,i-2)) return FALSE;
        }
    return TRUE;
}

INT pfaffian_matrix(mat,res) OP mat,res;
/* berechnet pfaffian */
/* AK 050995 */
{
    OP perm,zwerg,zzerg;
    INT erg = OK;
    CTO(MATRIX,"pfaffian_matrix(1)",mat);

    SYMCHECK(not quadraticp(mat),"pfaffian:not quadratic matrix");
    SYMCHECK(not evenp(S_M_H(mat)),"pfaffian:size of matrix not even");

    perm = callocobject(); 
    zwerg = callocobject(); 
    zzerg = callocobject();
    erg += first_permutation(S_M_H(mat),perm);

    erg += det050995(mat,perm,res);
    erg += signum(perm,zwerg);
    erg += mult_apply(zwerg,res);

    while (next(perm,perm))
    {
        if (co_050995(perm) == TRUE)
        {
        erg += det050995(mat,perm,zwerg);
        erg += signum(perm,zzerg);
        erg += mult_apply(zwerg,zzerg);
        erg += add_apply(zzerg,res);
        }
    }; 
    FREEALL3(perm,zwerg,zzerg);
    ENDR("pfaffian_matrix");
}

INT immanente_matrix(mat,part,res) OP mat,part,res;
/* berechnet immanente */
/* AK270588 */ /* AK 060789 V1.0 */ /* AK 090790 V1.1 */ /* AK 180691 V1.2 */
/* AK 210891 V1.3 */
/* AK 161098 V2.0 */
/* AK 130603 */
{
    OP perm,nextperm,zwerg,zzerg;
    INT i,erg = OK;
    
    CTTO(MATRIX,INTEGERMATRIX,"immanente_matrix(1)",mat);
    CTO(PARTITION,"immanente_matrix(2)",part);
    SYMCHECK(S_M_HI(mat) != S_M_LI(mat),"immanente_matrix:not quadratic matrix");
    PARTITION_WEIGHT(part,i); /* AK 130603 */
    SYMCHECK(i != S_M_HI(mat),"immanente_matrix:wrong weight of partition");

    CE3(mat,part,res,immanente_matrix);

    perm = CALLOCOBJECT(); 
    zwerg = CALLOCOBJECT(); 
    zzerg = CALLOCOBJECT();
    nextperm = CALLOCOBJECT();
    erg += first_permutation(S_M_H(mat),perm);

    erg += det270588(mat,perm,res);
    erg += charvalue(part,perm,zwerg,NULL);
    MULT_APPLY(zwerg,res);

    while (next_apply(perm))
    {
        erg += det270588(mat,perm,zwerg);
        erg += charvalue(part,perm,zzerg,NULL);
        MULT_APPLY(zzerg,zwerg);
        ADD_APPLY(zwerg,res);
    };

    FREEALL4(zzerg,zwerg,perm,nextperm);
    ENDR("immanente_matrix");
}
#endif  /* CHARTRUE */
#endif  /* PERMTRUE */



INT inc_matrix(a) OP a;
/* 250488 */ /* AK 060789 V1.0 *//* AK 130790 V1.1 */ /* AK 180691 V1.2 */
/* AK 210891 V1.3 */
/* AK 240804 V3.0 */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"inc_matrix(1)",a);
    {
    OP l,h;
    OP b; /* die neue matrix */
    INT i,j;


    CALLOCOBJECT3(l,h,b);

    COPY_INTEGER(S_M_H(a),h); INC_INTEGER(h); 
    COPY_INTEGER(S_M_L(a),l); INC_INTEGER(l);
    b_lh_m(l,h,b);C_O_K(b,S_O_K(a));

    for (i=0L;i<S_M_HI(a);i++) for (j=0L;j<S_M_LI(a);j++)
            *(S_M_IJ(b,i,j)) =  *(S_M_IJ(a,i,j));
    for (i=0L;i<S_M_HI(b);i++) C_O_K(S_M_IJ(b,i,S_M_LI(a)),EMPTY);
    for (j=0L;j<S_M_LI(b);j++) C_O_K(S_M_IJ(b,S_M_HI(a),j),EMPTY);

    SYM_free(S_M_S(a)); 
    FREEALL2(S_M_H(a),S_M_L(a));
    SYM_free(S_O_S(a).ob_matrix);

    *a = *b;
    C_O_K(b,EMPTY); FREEALL(b); 
    }
    ENDR("inc_matrix");
}

INT inc_matrix_row_co(a,k) OP a; INT k;
/* 080304 AK */ /* increase matrix by k empty row */
/* AK 240904 V3.0 */
{   
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"inc_matrix_row_co(1)",a);
    SYMCHECK(k<=0,"inc_matrix_row_co:parameter <0");
    {
    OP b; /* the new matrix */
    OP l,h;
    INT i,j;


    CALLOCOBJECT3(l,h,b);

    M_I_I(S_M_HI(a)+k,h); 
    M_I_I(S_M_LI(a),l); 
    b_lh_m(l,h,b);C_O_K(b,S_O_K(a));

    for (i=0L;i<S_M_HI(a);i++) for (j=0L;j<S_M_LI(a);j++)
            *(S_M_IJ(b,i,j)) =  *(S_M_IJ(a,i,j));
    for (i=0L;i<k;i++) for (j=0L;j<S_M_LI(a);j++)
            C_O_K(S_M_IJ(b,i+S_M_HI(a),j),EMPTY);

    SYM_free(S_M_S(a));
    FREEALL2(S_M_H(a),S_M_L(a));
    SYM_free(S_O_S(a).ob_matrix);

    *a = *b;
    C_O_K(b,EMPTY); FREEALL(b);
    }
    ENDR("inc_matrix_row_co");
}

INT inc_matrix_column_co(a,k) OP a; INT k;
/* 080304 AK */ 
/* increase matrix by k empty columns at the end */
/* AK 240904 V3.0 */
/* AK 180607 V3.1 */
{   
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"inc_matrix_column_co(1)",a);
    SYMCHECK(k<=0,"inc_matrix_column_co:parameter <0");
    {
    OP l,h;
    OP b; /* die neue matrix */
    INT i,j;


    CALLOCOBJECT3(l,h,b);

    M_I_I(S_M_LI(a)+k,l);
    M_I_I(S_M_HI(a),h);
    erg += b_lh_m(l,h,b);
    C_O_K(b,S_O_K(a));

    for (i=0L;i<S_M_HI(a);i++) for (j=0L;j<S_M_LI(a);j++)
            *(S_M_IJ(b,i,j)) =  *(S_M_IJ(a,i,j));
    for (i=0L;i<S_M_HI(a);i++) for (j=0L;j<k;j++)
            C_O_K(S_M_IJ(b,i,j+S_M_LI(a)),EMPTY);

    SYM_free(S_M_S(a));
    FREEALL2(S_M_H(a),S_M_L(a));
    SYM_free(S_O_S(a).ob_matrix);

    *a = *b;
    C_O_K(b,EMPTY); FREEALL(b);
    }
    ENDR("inc_matrix_column_co");
}


INT singularp(a) OP a;
/* AK 020304 */
/* return TRUE 
   if matrix singualar i.e row rank != number of rows  */
/* AK 021106 V3.1 */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"singularp(1)",a);
    SYMCHECK(not quadraticp(a),"singularp:not quadratic");
    {
    OP b;INT res;
    b=CALLOCOBJECT();
    erg += rank(a,b); 
    if (EQ(b,S_M_H(a))) res = FALSE;
    else res = TRUE;
    FREEALL(b);
    return res;
    }
    ENDR("singularp");
}

INT invers_matrix(a,b) OP a,b;
/* AK 290388 nach stoer (dietmar) */
/* umgewandelt aus pascal */
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 150591 V1.2 */
/* AK 220791 V1.3 */ /* AK 081204 V3.0 */
/* AK 021206 V3.1 */
{
    INT erg=OK;
    CTO(MATRIX,"invers_matrix(1)",a);
    CTO(EMPTY,"invers_matrix(2)",b);
    SYMCHECK(not quadraticp(a),"invers_matrix:not quadratic");
    {
    INT i,j,k,r;
    /* r ist die selectierte spalte */
    /* r = 0 ... n */
    INT n=S_M_LI(a)-1L;
    INT singulaer = FALSE;
    OP p,hr,hs,hv;
    CALLOCOBJECT4(p,hr,hs,hv);


    erg += m_il_v(n+1L,p);

    for(j=0L;j<=n;j++) M_I_I(j,S_V_I(p,j));

    j= -1L;
    CLEVER_COPY(a,b);
    while ((j++ <n) && (! singulaer))
    {
        /*pivotsuche*/
        for(r=j;r<=n;r++)
	    {
	    if (S_O_K(S_M_IJ(b,r,j))==GALOISRING)  // non field
                {
		if (unitp_galois(S_M_IJ(b,r,j))) goto im290388;
		}
            else if (not NULLP(S_M_IJ(b,r,j))) goto im290388;
	    }

im290388:
        if (r == n+1L)/* nur nullen in der spalte j */ singulaer = TRUE;
        else {
            /*zeilentausch*/
            if (r>j){
                for (k=0L;k<=n;k++) 
                    SWAP(S_M_IJ(b,j,k),S_M_IJ(b,r,k));
                SWAP(S_V_I(p,j),S_V_I(p,r));
            };
            /*transformation*/
	    FREESELF(hr);
            INVERS(S_M_IJ(b,j,j),hr);
            for (i=0L;i<=n;i++) MULT_APPLY(hr,S_M_IJ(b,i,j));
            CLEVER_COPY(hr,S_M_IJ(b,j,j));
            ADDINVERS_APPLY(hr);
            for (k=0L;k<=n;k++)
            {
                if (k==j) k++; /* spalte j nicht anwenden */
                if (k>n) break;
                for (i=0L;i<=n;i++)
                    {
                    if (i==j) i++; /* auf zeile j nicht anwenden */
                    if (i>n) break;
                    MULT(S_M_IJ(b,i,j),S_M_IJ(b,j,k),hs);
                    ADDINVERS_APPLY(hs);
                    ADD_APPLY(hs,S_M_IJ(b,i,k));
		    FREESELF(hs);
                    };
                MULT_APPLY(hr,S_M_IJ(b,j,k));
            };
        }; /* end else */
    }; /* end while */
    // if (erg != OK) goto endr_ende;
    FREEALL2(hr,hs);

    erg+=m_il_v(n+1L,hv);
    if (not singulaer)
        /*spaltentausch*/
        for (i=0L;i<=n;i++)
            {
            OP z;
            z = S_M_IJ(b,i,0);
            for (k=0;k<=n;k++,z++) CLEVER_COPY(z, S_V_I(hv,S_V_II(p,k)));
            z = S_M_IJ(b,i,0);
            for (k=0L;k<=n;k++,z++) CLEVER_COPY(S_V_I(hv,k), z);
            }

    FREEALL2(p,hv);
    if (singulaer)    { 
        freeself(b);
        error("invers_matrix: singulary");
        return(SINGULAER); 
    };
    }
    ENDR("invers_matrix");

}


INT transpose_matrix(a,b) OP a,b;
/* AK 280388 */ /* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 210891 V1.3 */
/* AK 081204 V3.0 */
/* AK 021106 V3.1 */
{
    INT erg = OK;
    CTO(MATRIX,"transpose_matrix(1)",a);
    CTO(EMPTY,"transpose_matrix(2)",b);
    {

    INT i,j;
    erg += m_ilih_m(S_M_HI(a),S_M_LI(a),b);
    C_O_K(b,S_O_K(a));

    for (i=0;i<S_M_HI(b);i++)
        for (j=0;j<S_M_LI(b);j++)
            COPY(S_M_IJ(a,j,i),S_M_IJ(b,i,j));
    }
    ENDR("transpose_matrix");
}

INT transpose_second_matrix(a,b) OP a,b;
/* AK 280388 */ /* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 210891 V1.3 */
/* not on the main diagonal */
/* AK 021106 V3.1 */
{
        INT i,j;
        INT erg = OK;
    CE2(a,b,transpose_second_matrix);

        erg += m_ilih_m(S_M_HI(a),S_M_LI(a),b);
        C_O_K(b,S_O_K(a));

        for (i=0;i<S_M_HI(b);i++)
                for (j=0;j<S_M_LI(b);j++)
                        erg += copy(S_M_IJ(a,j,i),S_M_IJ(b,S_M_HI(a)-1-i,j));

        ENDR("transpose_second_matrix");
}


INT comp_kranztafel(a,b) OP a, b;
/* AK 280390 V1.1 */ /* AK 210891 V1.3 */
{
    INT i,j,res;
    OP x,y;
    
    x = S_M_S(a);
    y = S_M_S(b);    
    for (i=0L;i<S_M_HI(a);i++)
        {
        if     (i >= S_M_HI(b)) return(1L);
        else    {
            for (j=0;j<S_M_LI(a);j++)
                {
                if (j>=S_M_LI(b)) return(1L);
                else {
                    res=COMP_INTEGER_INTEGER(x,y);
                    if (res != 0) return(res);
                    x++;y++;
                    };
                }
            }
        }
    if ( S_M_HI(b) > S_M_HI(a) ) return -1; 
    if ( S_M_LI(b) > S_M_LI(a) ) return -1; 
    return 0;
}

INT comp_integermatrix(a,b) OP a, b;
/* AK 150802 */
/* in case of equal dimensions lexicographic */
{
    INT erg = OK;
    CTO(INTEGERMATRIX,"comp_integermatrix(1)",a);
    CTO(INTEGERMATRIX,"comp_integermatrix(2)",b);
    {
    INT i,j,res;
    OP x,y;
 
    x = S_M_S(a);
    y = S_M_S(b);
    for (i=0L;i<S_M_HI(a);i++)
        {
        if     (i >= S_M_HI(b)) return(1L);
        else    {
            for (j=(INT)0;j<S_M_LI(a);j++)
                {
                if (j>=S_M_LI(b)) return(1L);
                else {
                    res=COMP_INTEGER_INTEGER(x,y);
                    if (res != 0) return(res);
                    x++;y++;
                    };
                }
            }
        }
    if ( S_M_HI(b) > S_M_HI(a) ) return -1;
    if ( S_M_LI(b) > S_M_LI(a) ) return -1;
    return 0;
    }
    ENDR("comp_integermatrix");
}                                                                                             



INT comp_matrix(a,b) OP a, b;
/* AK 060789 V1.0 */ /* AK 070290 V1.1 */ /* AK 210891 V1.3 */
{
    INT i,j,res;
    OP x,y;
    
    x = S_M_S(a);
    y = S_M_S(b);    
    for (i=(INT)0;i<S_M_HI(a);i++)
        {
        if     (i >= S_M_HI(b)) return(1L);
        else    {
            for (j=(INT)0;j<S_M_LI(a);j++)
                {
                if (j>=S_M_LI(b)) return(1L);
                else {
                    res=COMP(x,y);
                    if (res != 0) return(res);
                    x++;
                    y++;
                    };
                }
            }
        }
    if ( S_M_HI(b) > S_M_HI(a) ) return(-1L); /* AK 170790 */
    if ( S_M_LI(b) > S_M_LI(a) ) return(-1L); /* AK 241195 */
    return((INT)0); /* matrizen sind gleich */
}



INT add_apply_matrix_matrix(a,b) OP a,b;
/* AK 220390 V1.1 */ /* AK 090891 V1.3 */
/* AK 210891 V1.3 */
/* b:= b += a */
{
    OP c,d;
    INT erg = OK;
    CTTTO(MATRIX,INTEGERMATRIX,KRANZTYPUS,"add_apply_matrix_matrix(1)",a);
    CTTTO(MATRIX,INTEGERMATRIX,KRANZTYPUS,"add_apply_matrix_matrix(2)",b);

    C_M_HASH(b,-1);
    if (
        (S_M_HI(a) == S_M_HI(b))&&
        (S_M_LI(a) == S_M_LI(b))
        )
        {
        INT i;
        i = S_M_HI(a)*S_M_LI(a);
        c = S_M_S(a);
        d=S_M_S(b);
        while (i-- > 0)
            {
            ADD_APPLY(c,d);
            c++;
            d++;
            }
        }
    else if (         
             (S_M_HI(a) < S_M_HI(b)) &&         
             (S_M_LI(a) < S_M_LI(b))         
            )         
            {         
            INT i,j;
            for (i=0;i<S_M_HI(a);i++)
            for (j=0;j<S_M_LI(a);j++)
                ADD_APPLY(S_M_IJ(a,i,j),S_M_IJ(b,i,j));
            }
    else    {
        c = CALLOCOBJECT();
        *c = *b;
        C_O_K(b,EMPTY);
        erg += add_matrix_matrix(a,c,b);
        FREEALL(c);
        }
    ENDR("add_apply_matrix_matrix");
}



INT add_apply_matrix(a,b) OP a,b;
/* AK 220390 V1.1 */
/* AK 210891 V1.3 */
{
    INT erg = OK;
    CTTTO(MATRIX,INTEGERMATRIX,KRANZTYPUS,"add_apply_matrix(1)",a);
    EOP("add_apply_matrix(2)",b);
    
   
    switch (S_O_K(b)){
        case KRANZTYPUS:
        case INTEGERMATRIX:
        case MATRIX:
            erg += add_apply_matrix_matrix(a,b);
            break;
        default:
            WTO("add_apply_matrix(2)",b);
            break;
    }
    ENDR("add_apply_matrix");
}



INT add_matrix(a,b,c) OP a,b,c;
{
    INT erg=OK;
    if (not MATRIXP(a))
        { erg += WTO("add_matrix",a);goto endr_ende; }
    if (MATRIXP(b))
        erg += add_matrix_matrix(a,b,c);
    else
        erg += WTO("add_matrix",b);
    ENDR("add_matrix");
}

INT add_matrix_matrix(a,b,ergeb) OP a,b,ergeb;
/* AK 041186 */ /* AK 171186 */ /* AK 060789 V1.0 */ /* AK 081289 V1.1 */
/* AK 090891 V1.3 */
/* a and b may have different sizes */
{
    INT i,j;
    OP     len,height;
    OP z;
    INT erg = OK;

    CTTO(INTEGERMATRIX,MATRIX,"add_matrix_matrix(1)",a);
    CTTO(INTEGERMATRIX,MATRIX,"add_matrix_matrix(2)",b);
    CTO(EMPTY,"add_matrix_matrix(3)",ergeb);

    len = CALLOCOBJECT(),
    height = CALLOCOBJECT();
    if     (S_M_LI(a) >=S_M_LI(b))
        COPY_INTEGER(S_M_L(a),len);
    else    COPY_INTEGER(S_M_L(b),len);
    if     (S_M_HI(a) >=S_M_HI(b))
        COPY_INTEGER(S_M_H(a),height);
    else    COPY_INTEGER(S_M_H(b),height);

    erg += b_lh_m(len,height,ergeb);
    C_O_K(ergeb,S_O_K(a));

    z = S_M_S(ergeb);
    for (i=0;i<S_M_HI(ergeb);i++)
        for (j=0;j<S_M_LI(ergeb);j++,z++)
        {
            if (
                (i<S_M_HI(a))&&(i<S_M_HI(b))&&
                (j<S_M_LI(a))&&(j<S_M_LI(b))
                )

            { 
            ADD(S_M_IJ(a,i,j), S_M_IJ(b,i,j), z); 
            }

            else if ( (i<S_M_HI(a))&&(j<S_M_LI(a)))
                COPY(S_M_IJ(a,i,j),z); 
            else if ( (i<S_M_HI(b))&&(j<S_M_LI(b)))
                COPY(S_M_IJ(b,i,j),z); 
            else { /* for the multiplication of matrix labelled polynomials */
                if (S_O_K(S_M_IJ(a,0,0)) == INTEGER) 
                    M_I_I(0,z);
                }
        }
    ENDR("add_matrix_matrix");
}



INT copy_integermatrix(a,b) OP a,b;
    {
    INT erg = OK;
    CTO(INTEGERMATRIX,"copy_integermatrix(1)",a);
    CTO(EMPTY,"copy_integermatrix(2)",b);

    erg += m_ilih_m(S_M_LI(a),S_M_HI(a),b);
    C_O_K(b,S_O_K(a));
    C_M_HASH(b,S_M_HASH(a));
    memcpy((char *) S_M_S(b),(char *) S_M_S(a),
            S_M_LI(a)*S_M_HI(a)*sizeof(struct object));
    ENDR("copy_integermatrix");
    }

INT freeself_integermatrix(a) OP a;
/* AK 281098 V2.0 */
    {
    INT erg = OK;
    CTO(INTEGERMATRIX,"freeself_integermatrix(1)",a);
    {
    OBJECTSELF d;
    d=S_O_S(a);
    SYM_free(S_M_S(a)); 
    FREEALL(S_M_L(a)); 
    FREEALL(S_M_H(a));
    SYM_free(d.ob_matrix);
    C_O_K(a,EMPTY);
    }
    ENDR("freeself_integermatrix");
    }




INT copy_kranztypus(a,b) OP a,b;
/* AK 270390 V1.1 */ /* AK 210891 V1.3 */
/* AK 040392 cast to char * */
    {
    m_ilih_m(S_M_LI(a),S_M_HI(a),b);
    C_O_K(b,S_O_K(a));
    memcpy((char *) S_M_S(b),(char *) S_M_S(a),
            S_M_LI(a)*S_M_HI(a)*sizeof(struct object));
    return(OK);
    }



INT copy_matrix(von,b) OP von , b;
/* AK 051186 */ /* AK 021286 */ /* AK 060789 V1.0 */ /* AK 071289 V1.1 */
/* AK 210891 V1.3 */
{
    INT k;
    OP z,w;
    INT erg = OK;
    CTTO(INTEGERMATRIX,MATRIX,"copy_matrix(1)",von);
    CTO(EMPTY,"copy_matrix(2)",b);

    erg += m_ilih_m(S_M_LI(von),S_M_HI(von),b);
    C_O_K(b,S_O_K(von));
    C_M_HASH(b,S_M_HASH(von));


    z = S_M_IJ(von,S_M_HI(von)-1L,S_M_LI(von)-1L);
    w = S_M_IJ(b,S_M_HI(von)-1L,S_M_LI(von)-1L);
    k = S_M_HI(von) * S_M_LI(von);
    for (;k>0;k--,z--,w--) 
            COPY(z,w);

    ENDR("copy_matrix");
}



INT freeself_kranztypus(a) OP a;
/* AK 270390 V1.1 */ /* AK 210891 V1.3 */
/* AK 281098 V2.0 */
    {
    INT erg = OK;
    CTO(KRANZTYPUS,"freeself_kranztypus(1)",a);
    {
    OBJECTSELF d;
    d=S_O_S(a);
    SYM_free(S_M_S(a)); 
    FREEALL(S_M_L(a)); 
    FREEALL(S_M_H(a));
    SYM_free(d.ob_matrix);
    C_O_K(a,EMPTY);
    }
    ENDR("freeself_kranztypus");
    }



INT freeself_matrix(matrix) OP matrix;
/* AK 060789 V1.0 */ /* AK 071289 V1.1 */ /* AK 100691 V1.2 */ 
/* AK 160891 V1.3 */
{
    INT k;
    OBJECTSELF d;
    OP z;
    INT erg = OK;
    CTO(MATRIX,"freeself_matrix(1)",matrix);

    d=S_O_S(matrix);

    z = S_M_IJ(matrix,S_M_HI(matrix)-1L,S_M_LI(matrix)-1L);
    k = S_M_HI(matrix) * S_M_LI(matrix);
    for (;k>(INT)0;k--,z--) 
            if (S_O_K(z) == INTEGER) ;
            else if (EMPTYP(z));
            else 
                erg += freeself(z);
    
    SYM_free(S_M_S(matrix)); 
    erg += freeall(S_M_L(matrix)); 
    erg += freeall(S_M_H(matrix));
    SYM_free(d.ob_matrix);
    C_O_K(matrix,EMPTY);
    ENDR("freeself_matrix");
}



static struct matrix * callocmatrix()
/* AK 060789 V1.0 */ /* AK 220390 V1.1 */ /* AK 160891 V1.3 */
{
    struct matrix *ergebnis;

    ergebnis = (struct matrix *) SYM_calloc((int)1,sizeof(struct matrix));
    if (ergebnis == NULL)
        no_memory();
    return(ergebnis);
}



INT scan_integermatrix(ergebnis) OP ergebnis;
/* AK 141293 */
{
    return scan_matrix_co(ergebnis, INTEGER);
}

INT scan_matrix(ergebnis) OP ergebnis;
/* AK 141293 */
{
    return scan_matrix_co(ergebnis, EMPTY);
}


INT scan_skewsymmetric_matrix(ergebnis) OP ergebnis;
/* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 080891 V1.3 */
{
    OP len, height;
    INT i,j;
    char a[20];  /* AK 080891 */
    OBJECTKIND kind;

    len = callocobject();
    height = callocobject();
aaa:
    printeingabe("height of skew symmetric matrix"); 
    scan(INTEGER,height);
    copy(height,len);
    printeingabe("enter kind of matrix elements");
    kind=scanobjectkind();
    if (S_I_I(len) <= (INT)0) /* AK 170795 */
        {
        printeingabe("you entered wrong length (<=0), do it again");
        goto aaa;
        }
    if (S_I_I(height) <= (INT)0) /* AK 170795 */
        {
        printeingabe("you entered wrong height (<=0), do it again");
        goto aaa;
        }
    b_lh_m(len,height,ergebnis);
    for (i=0; i<S_I_I(height); i++)
        m_i_i(0L,S_M_IJ(ergebnis,i,i));
    for (i=0; i<S_I_I(height); i++)
    {
        sprintf(a,"row nr %ld \n",(i+1L));  /* AK 080891 */
        printeingabe(a);  /* AK 080891 */
        for (j=i+1;j<S_I_I(len);j++)
            {
            scan(kind,S_M_IJ(ergebnis,i,j));
            addinvers(S_M_IJ(ergebnis,i,j), S_M_IJ(ergebnis,j,i));
            }
    };
    return(OK);
}

static INT scan_matrix_co(ergebnis,kind) OP ergebnis; OBJECTKIND kind;
/* AK 060789 V1.0 */ /* AK 310790 V1.1 */ /* AK 080891 V1.3 */
{
    OP len, height;
    INT i,j;
    char a[20];  /* AK 080891 */

    len = callocobject();
    height = callocobject();
aaa:
    printeingabe("height of matrix"); 
    scan(INTEGER,height);
    printeingabe("length of matrix"); 
    scan(INTEGER,len);
    if (kind == EMPTY)
        {
        printeingabe("enter kind of matrix elements");
        kind=scanobjectkind();
        }
    if (S_I_I(len) <= (INT)0) /* AK 170795 */
        {
        printeingabe("you entered wrong length (<=0), do it again");
        goto aaa;
        }
    if (S_I_I(height) <= (INT)0) /* AK 170795 */
        {
        printeingabe("you entered wrong height (<=0), do it again");
        goto aaa;
        }
    b_lh_m(len,height,ergebnis);
    for (i=0; i<S_I_I(height); i++)
    {
        sprintf(a,"row nr %ld \n",(i+1L));  /* AK 080891 */
        printeingabe(a);  /* AK 080891 */
        for (j=0;j<S_I_I(len);j++)
            scan(kind,S_M_IJ(ergebnis,i,j));
    };
    return(OK);
}



INT change_column_ij(a,i,j) OP a; INT i,j;
/* AK 301288 vertauscht spalten i und j dabei kein copy */
/* AK 060789 V1.0 */ /* AK 050390 V1.1 */ /* AK 160891 V1.3 */
{
    INT k,erg = OK;
    CTO(MATRIX,"change_column_ij(1)",a);
    SYMCHECK(i<0,"change_column_ij:i<0");
    SYMCHECK(j<0,"change_column_ij:j<0");
    SYMCHECK(i>=S_M_LI(a),"change_column_ij:i too big ");
    SYMCHECK(j>=S_M_LI(a),"change_column_ij:j too big ");
    if (i==j) goto endr_ende; /* AK 190802 */

    for (k=0; k<S_M_HI(a); k++) 
        SWAP(S_M_IJ(a,k,i),S_M_IJ(a,k,j));
    ENDR("change_column_ij");
}


INT change_row_ij(a,i,j) OP a; INT i,j;
/* AK 301288 vertauscht zeilen i und j dabei kein copy */
/* AK 060789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{
    INT k,erg = OK;
    CTO(MATRIX,"change_row_ij(1)",a);
    SYMCHECK(i<0,"change_row_ij:i<0");
    SYMCHECK(j<0,"change_row_ij:j<0");
    SYMCHECK(i>=S_M_HI(a),"change_row_ij:i too big ");
    SYMCHECK(j>=S_M_HI(a),"change_row_ij:j too big ");
    if (i==j) goto endr_ende; /* AK 190802 */

    for (k=(INT)0; k<S_M_LI(a); k++) 
        SWAP(S_M_IJ(a,i,k),S_M_IJ(a,j,k));
    ENDR("change_row_ij");
}


OP s_m_s(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); return(c.ob_matrix->m_self); }

OP s_m_h(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); return(c.ob_matrix->m_height); }

OP s_m_l(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); return(c.ob_matrix->m_length); }

INT s_m_hash(a) OP a;
/* AK 110703 */
{ OBJECTSELF c; c = s_o_s(a); return(c.ob_matrix->m_hash); }

INT s_m_hi(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ return(s_i_i(s_m_h(a))); }

INT s_m_li(a) OP a;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ return(s_i_i(s_m_l(a))); }

INT c_m_s(a,b) OP a,b;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); c.ob_matrix->m_self = b; return(OK); }


INT c_m_h(a,b) OP a,b;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); c.ob_matrix->m_height = b; return(OK); }

INT c_m_hash(a,b) OP a; INT b;
/* AK 110703 */
{ OBJECTSELF c; c = s_o_s(a); c.ob_matrix->m_hash = b; return(OK); }


INT c_m_l(a,b) OP a,b;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ OBJECTSELF c; c = s_o_s(a); c.ob_matrix->m_length = b; return(OK); }

OP s_m_ij(a,i,j) OP a; INT i,j;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ 
    if (not MATRIXP(a))
        {
        printobjectkind(a);
        error("s_m_ij:no matrix object");
        }
    if (i < (INT)0)
        {
        debugprint(a);
        fprintf(stderr,"index = %ld\n",i);
        error("s_m_ij:row index too small");
        }
    if (i >= s_m_hi(a))
        {
        debugprint(a);
        fprintf(stderr,"index = %ld\n",i);
        error("s_m_ij:row index too big");
        }
    if (j >= s_m_li(a))
        {
        debugprint(a);
        fprintf(stderr,"index = %ld\n",j);
        error("s_m_ij:column index too big");
        }
    if (j < (INT)0)
        {
        debugprint(a);
        fprintf(stderr,"index = %ld\n",j);
        error("s_m_ij:column index too small");
        }
    return(s_m_s(a) + (s_m_li(a)*i+j) ); 
}

INT s_m_iji(a,i,j) OP a; INT i,j;
/* AK 070789 V1.0 */ /* AK 181289 V1.1 */ /* AK 160891 V1.3 */
{ return(s_i_i(s_m_ij(a,i,j))); }



INT fprint_matrix(f,obj) FILE  *f; OP obj;
/* AK 211186 */ /* AK 070789 V1.0 */ /* AK 181289 V1.1 */
/* AK 210891 V1.3 */
{
    INT i,j;
    for (i=0;i<S_M_HI(obj);i++)
    {
        fprintf(f,"\n[");
        if (f == stdout) zeilenposition=0;
        for (j=0;j<S_M_LI(obj);j++)
        {
            fprint(f,S_M_IJ(obj,i,j));
            if (j+1 < S_M_LI(obj))
                {
                fprintf(f,":");
                if (f == stdout) zeilenposition++;
                }
            if ((f == stdout)&&(zeilenposition>70L))
                {fprintf(stdout,"\n");zeilenposition = 0L;}
        };
        fprintf(f,"]");
    };
    fprintf(f,"\n");
    if (f == stdout) zeilenposition=0L;
    return(OK);
}

INT tex_matrix(obj) OP obj;
{
    return tex_matrix_co(obj,tex);
}

INT tex_matrix_co(obj,f) OP obj; INT (*f)();
/* AK 150988 */ /* AK 310790 V1.1 */
/* AK 070291 V1.2 texout for output */ /* AK 210891 V1.3 */
{
    INT i,j;
    INT ts = texmath_yn; /* AK 190892 */
    INT erg = OK;
    CTO(MATRIX,"tex_matrix_co(1)",obj);

    fprintf(texout,"\n");
    if (texmath_yn == 0L)  /* d.h. not in math mode */
        {
        fprintf(texout,"$");
        texmath_yn=1L;
        }
    fprintf(texout,"\\matrix { \n");
    texposition = 0L;
    for (i=0;i<S_M_HI(obj);i++)
    {
        for (j=0L;j<S_M_LI(obj);j++)
        {
            (*f)(S_M_IJ(obj,i,j));
            fprintf(texout," & "); 
            texposition += 3L;
        }
        fprintf(texout," \\cr\n");
        texposition=0L;
    };
    fprintf(texout," }");
    if (ts == 0L) 
        {
        fprintf(texout,"$");
        texmath_yn=0L;
        }
    fprintf(texout," \n");
    texposition=0L;
    ENDR("tex_matrix_co");
}


INT mult_scalar_matrix(scalar,mat,res) OP scalar , mat,res;
/* AK 310588 */ 
/* AK 010889 V1.0 */ /* AK 081289 V1.1 */ /* AK 210891 V1.3 */
{
    INT i,j,erg = OK;
    OP height,len;
    SYMCHECK( S_M_S(mat) == NULL,"mult_scalar_matrix:self == NULL");

    height = callocobject();
    len = callocobject();

    COPY_INTEGER(S_M_L(mat), len); 
    COPY_INTEGER(S_M_H(mat), height);
    erg += b_lh_m(len,height,res);
    for (i=0L;i<S_I_I(height);i++) 
        for(j=0L;j<S_I_I(len);j++)
            MULT(scalar,S_M_IJ(mat,i,j),S_M_IJ(res,i,j));
    ENDR("mult_scalar_matrix");
}

INT mult_apply_scalar_matrix(a,b) OP a,b;
/* AK 150290 V1.1 */ /* AK 210891 V1.3 */
{
    OP z = S_M_S(b);
    INT grenze = S_M_LI(b)*S_M_HI(b);
    INT erg = OK;
    INT i;
    CTO(MATRIX,"mult_apply_scalar_matrix(2)",b);
    C_M_HASH(b,-1);
    for (i=0L;i<grenze;i++,z++) 
        erg += mult_apply(a,z);
    ENDR("mult_apply_scalar_matrix");
}

INT mult_apply_matrix_matrix(a,b) OP a,b;
/* AK 131190 V1.1 */ /* b =  a * b */
/* AK 210891 V1.3 */
{
    OP c = callocobject();
    INT erg = OK; /* AK 200192 */
    CTO(MATRIX,"mult_apply_matrix_matrix(1)",a);
    CTO(MATRIX,"mult_apply_matrix_matrix(2)",b);
    *c = *b;
    C_O_K(b,EMPTY);
    erg += mult_matrix_matrix(a,c,b);
    erg += freeall(c);
    ENDR("mult_apply_matrix_matrix");
}


INT mult_matrix_matrix(a,b,c) OP a,b,c;
/* AK 280388 */ /* AK 060789 V1.0 */ /* AK 111289 V1.1 */
/* c = a * b */
/* AK 210891 V1.3 */
/* AK 221104 V3.0 c may be non empty */
{
    INT erg = OK;
    CTO(MATRIX,"mult_matrix_matrix(1)",a);
    CTO(MATRIX,"mult_matrix_matrix(2)",b);
    {
    INT i,j,k,al,bl;
    OP z; /* zwischen ergebnis bei matrix-multiplikation */
    OP cp,ap,ap2,bp,bp2;
    al = S_M_LI(a);
    bl = S_M_HI(b);
    SYMCHECK( bl != al, "mult_matrix_matrix:different sizes");
    bl = S_M_LI(b);

        

    erg += m_ilih_m(S_M_LI(b),S_M_HI(a),c);
    z=CALLOCOBJECT(); /* zwischensumme*/
    for (i=0,cp=S_M_S(c),ap=S_M_S(a);
         i<S_M_HI(a);i++,ap+=al)    /* ueber zeilen der linken Matrix */
        for (j=0,bp=S_M_S(b);j<S_M_LI(b);
             j++,cp++,bp++) /* ueber spalten der rechten Matrix */
            {
            ap2 = ap;
            bp2 = bp;
            MULT(ap2,bp2,cp);
            ap2++;
            bp2 += bl;
            for (k=1;k<al;k++,ap2++,bp2+=bl)
                { 
                FREESELF(z);  
                MULT(ap2,bp2,z);
                ADD_APPLY(z,cp);
                };
            }
    FREEALL(z); 
    }
    ENDR("mult_matrix_matrix");
}


INT mult_matrix(a,b,d) OP a,b,d;
/* AK 070789 V1.0 */ /* AK 310790 V1.1 */ /* AK 210891 V1.3 */
{
    INT erg = OK;
    CTO(MATRIX,"mult_matrix(1)",a);
    EOP("mult_matrix(2)",b);
    CTO(EMPTY,"mult_matrix(3)",d);

    switch(S_O_K(b))
    {
    case BRUCH:
    case INTEGER:
    case LONGINT: 
        erg += mult_scalar_matrix(b,a,d);
        break;

    case MATRIX: 
        erg += mult_matrix_matrix(a,b,d);
        break;
    case VECTOR: 
        erg += mult_matrix_vector(a,b,d); /* AK 200192 */
        break;
    default:
        WTO("mult_matrix(2)",b);
        break;
    }
    ENDR("mult_matrix");
}


#ifdef VECTORTRUE
INT mult_matrix_vector(b,a,c) OP a, b, c;
/* AK 200192 */
/* AK 221104 V3.0 */
{
    INT erg = OK;
    CTTO(INTEGERVECTOR,VECTOR,"mult_matrix_vector(2)",a);
    CTO(MATRIX,"mult_matrix_vector(1)",b);
    {
    INT i,j;
    OP d,h;

    SYMCHECK (S_V_LI(a) != S_M_LI(b),"mult_matrix_vector:wrong size");

    erg += m_il_v(S_M_HI(b),c);
    CALLOCOBJECT2(d,h);
    // erg += null(S_V_I(a,0),h);
    for (i=0;i<S_V_LI(c);i++)
        {
        // COPY(h,S_V_I(c,i));
	MULT(S_M_IJ(b,i,0),S_V_I(a,0),S_V_I(c,i));
        for (j=1;j<S_V_LI(a);j++)
            {
	    erg += multadd_apply(S_M_IJ(b,i,j),S_V_I(a,j),S_V_I(c,i));
/*
	    FREESELF(d);
            MULT(S_M_IJ(b,i,j),S_V_I(a,j),d);
            ADD_APPLY(d,S_V_I(c,i));
*/
            }
        }
    FREEALL2(d,h);
    }
    ENDR("mult_matrix_vector");
}
#endif /* VECTORTRUE */



INT mult_apply_matrix(a,b) OP a,b;
/* AK 131190 V1.1 */ /* AK 210891 V1.3 */
{
    switch(S_O_K(b))
    {
    case MATRIX: return(mult_apply_matrix_matrix(a,b));
    default:
        {
            printobjectkind(b);
            error("mult_apply_matrix:wrong second type"); 
            return(ERROR);
        }
    }
}




INT objectread_matrix(fp,matrix) FILE *fp; OP matrix;
/* AK 300888 */ /* AK 070789 V1.0 */ /* AK 310790 V1.1 */
/* AK 210891 V1.3 */
{
    INT i,j;
    OP l= callocobject();
    OP h = callocobject();
    objectread(fp,h);
    objectread(fp,l);
    b_lh_m(l,h,matrix);
    for (i=0;i<S_M_HI(matrix); i++)
        for (j=0;j<S_M_LI(matrix); j++)
            objectread(fp,S_M_IJ(matrix,i,j));
    return(OK);
}



INT objectwrite_matrix(fp,matrix) FILE *fp; OP matrix;
/* AK 300888 */ /* AK 070789 V1.0 */ /* AK 310790 V1.1 */
/* AK 210891 V1.3 */
{
    INT i,j;

    fprintf(fp, " %ld ",MATRIX);
    objectwrite(fp,S_M_H(matrix));
    /* zuerst die hoehe */
    objectwrite(fp,S_M_L(matrix));
    /* dann die laenge */

    for (i=0;i<S_M_HI(matrix); i++)
        for (j=0;j<S_M_LI(matrix); j++)
            objectwrite(fp,S_M_IJ(matrix,i,j));
    return(OK);
}



INT test_matrix() 
/* AK 181289 V1.1 */
/* AK 120891 V1.3 */
{
    OP a = callocobject();
    OP b = callocobject();

    printf("test_matrix:scan(a)");
    scan(MATRIX,a);
    println(a);
    printf("test_matrix:add(a,a,b)");
    add(a,a,b);
    println(b);
    printf("test_matrix:mult(a,b,b)"); 
    mult(a,b,b); 
    println(b);
    printf("test_matrix:kronecker_product(a,b,b)"); 
    kronecker_product(a,b,b); 
    println(b);
#ifdef BRUCHTRUE
    printf("test_matrix:invers(b,a)"); 
    invers(b,a); 
    println(a);
#endif /* BRUCHTRUE */
    printf("test_matrix:delete_row_matrix(a,1L,b)");
    delete_row_matrix(a,1L,b); 
    println(b);
    printf("test_matrix:delete_column_matrix(b,1L,b)");
    delete_column_matrix(b,1L,b); 
    println(b);


    freeall(a);
    freeall(b);
    return(OK);
}



INT trace_matrix(a,b) OP a,b;
/* AK 131289 spur einer matrix */
/* AK 131289 V1.1 */ /* AK 270291 V1.2 */ /* AK 210891 V1.3 */
{
    INT i,erg=OK;
    CTO(MATRIX,"trace_matrix(1)",a);
    CTO(EMPTY,"trace_matrix(2)",b);
    SYMCHECK (not quadraticp(a) ,"trace_matrix: matrix not quadratic");

    null(S_M_S(a),b);
    for (i=S_M_HI(a)-1L; i>=0L; i--)
        ADD_APPLY(S_M_IJ(a,i,i),b);
    ENDR("trace_matrix");
}



INT symmetricp_matrix(a) OP a;
/* AK 150296 */
{
    INT i,j;
    if (S_M_HI(a) != S_M_LI(a)) return FALSE;
    for (i=0L;i<S_M_HI(a) ; i++)
    for (j=0L;j<i;j++)
        if (neq(S_M_IJ(a,i,j),S_M_IJ(a,j,i))) return FALSE;
    return TRUE;
}

#ifdef VECTORTRUE
INT spalten_summe(a,b) OP a,b;
/* AK 281289 summe ueber die Spalten, ergebnis ist vector */
/* AK 281289 V1.1 */ /* AK 240791 V1.3 */
{
    INT i,j;
    INT erg = OK;
    CTTO(INTEGERMATRIX,MATRIX,"spalten_summe(1)",a);

    erg += m_il_v(S_M_LI(a),b);
    for (j=0;j<S_M_LI(a);j++)
	{
	COPY(S_M_IJ(a,0,j),S_V_I(b,j));
        for (i=1;i<S_M_HI(a);i++)
           ADD_APPLY(S_M_IJ(a,i,j),S_V_I(b,j));
	}
    ENDR("spalten_summe");
}
#endif /* VECTORTRUE */


char * t_INTMATRIX_charvektor(a) OP a;
/* AK 210891 V1.3 */
{
    INT i,j,k=0;
    char *erg = (char *) 
        SYM_malloc(S_M_HI(a)*S_M_LI(a)*sizeof(char));
    if(erg == NULL) error("t_INTMATRIX_charvektor:no memory");
    else {
        for (i=0;i<S_M_HI(a);i++)
                for (j=0;j<S_M_LI(a);j++,k++)
                    erg[k] =(char)S_M_IJI(a,i,j);
        }
    return(erg);
}


#ifdef VECTORTRUE
INT m_vector_diagonalmatrix(a,b) OP a,b;
/* AK 171290 V1.1 */ /* AK 110691 V1.2 */ /* AK 210891 V1.3 */
{
    INT i;
    m_lh_nm(S_V_L(a),S_V_L(a),b);
    for (i=0L; i<S_M_HI(b);i++)
            copy(S_V_I(a,i),S_M_IJ(b,i,i));
    return OK;
}
#endif /* VECTORTRUE */


INT max_matrix(a,b) OP a,b;
/* b becomes copy of the maximum entry */
/* a and b may be equal */
/* empty objects are not used for comparision */
/* AK 110691 V1.2 */ /* AK 210891 V1.3 */
/* AK 090804 V3.0 */
{
    OP z = S_M_S(a),zb = S_M_S(a);
    INT i;

    for (i=S_M_HI(a)*S_M_LI(a); i>0L; i--, z++)
        if (not EMPTYP(z))
            {
            if (EMPTYP(zb)) zb = z;
            else if (GR(z,zb)) zb = z;
            }
    return copy(zb,b);
}

INT min_matrix(a,b) OP a,b;
/* b becomes copy of the minimum entry */
/* a and b may be equal */
/* AK 140703 */
/* AK 061207 */
{
    OP z = S_M_S(a),zb = NULL;
    INT i;

    for (i=S_M_HI(a)*S_M_LI(a); i>0L; i--, z++)
	{
        if (not EMPTYP(z))
	    {
	    if (zb==NULL) zb = z;
            else if (LT(z,zb)) zb = z;
            }
	}
    if (zb==NULL) return error("min_matrix: no entries");        
    else return copy(zb,b);
}

INT zeilen_summe(a,b) OP a,b;
/* AK 281289 summe ueber die Zeilen, ergebnis ist vector */
/* AK 281289 V1.1 */ /* AK 210891 V1.3 */
{
    INT i,j;
    INT erg = OK;
    CTTO(INTEGERMATRIX,MATRIX,"zeilen_summe(1)",a);
    
    erg += m_il_nv(S_M_HI(a),b);
    for (j=0;j<S_M_HI(a);j++)
        for (i=0;i<S_M_LI(a);i++)
            ADD_APPLY(S_M_IJ(a,j,i),S_V_I(b,j));
    ENDR("zeilen_summe");
}


INT n_fold_kronecker_product(n,a,b) OP    n; OP    a; OP    b;
/* RH 080891 V1.3 */
{
    INT    i;

    if(S_I_I(n)>= 2L)     kronecker_product(a,a,b);
    for(i=2;i<S_I_I(n);++i) kronecker_product(a,b,b);
    return OK;
}


INT kronecker_product(a,b,c) OP a,b,c;
/* RH 080891 V1.3 */
{
    INT    i;
    INT    j;
    INT    k;
    INT    l,erg=OK;

    OP    H,dim;

    CTTO(INTEGERMATRIX,MATRIX,"kronecker_product(1)",a);
    CTTO(INTEGERMATRIX,MATRIX,"kronecker_product(2)",b);
    CE3(a,b,c,kronecker_product);

    H     =    callocobject();
    dim    =    callocobject();

    MULT(S_M_L(a),S_M_L(b),dim);

    erg += m_lh_m(dim,dim,c);
    erg += m_lh_m(S_M_L(a),S_M_L(b),H);

    for(i=0L;i<S_M_LI(a);++i)
    {
        for(j=0L;j<S_M_HI(a);++j)
        {
            erg += mult(S_M_IJ(a,i,j),b,H);
            for(k=0L;k<S_M_LI(H);++k)
                for(l=0L;l<S_M_HI(H);++l)
                    COPY(S_M_IJ(H,k,l), S_M_IJ(c,i*S_M_HI(b)+k,j*S_M_LI(H)+l));
        }
    }

    FREEALL2(H,dim);
    ENDR("kronecker_product");
}

INT select_row(a,index,b) OP a,b; INT index;
/* transfer one row to vector object  */
/* AK 110592 */
{
    INT erg = OK;
    CTTTO(INTEGERMATRIX,MATRIX,TABLEAUX,"select_row(1)",a);
    SYMCHECK(index < 0,"select_row: negative index");
    if (a == b) /* AK 210802 */
        {
        OP c;
        c = CALLOCOBJECT();
        SWAP(a,c);
        erg += select_row(c,index,b);
        FREEALL(c);
        }
    else if (TABLEAUXP(a)) /* AK 280193 */
        {
        erg += select_row_tableaux(a,index,b);
        }
    else
        {
        INT j;
        SYMCHECK(index >= S_M_HI(a), "select_row: index >= height");
        erg += m_il_v(S_M_LI(a),b);
        for (j=0L;j<S_M_LI(a);j++)
            COPY(S_M_IJ(a,index,j),S_V_I(b,j));
        }
    ENDR("select_row");
}


INT select_column(a,index,b) OP a,b; INT index;
/* transfer one column to vector object  */
/* AK 110592 */
/* AK 090107 V3.1 */
{
    INT erg = OK;
    CTTTO(INTEGERMATRIX,MATRIX,TABLEAUX,"select_column(1)",a);
    SYMCHECK(index < 0,"select_column: negative index");

    if (a == b) /* AK 210802 */
        {
        OP c;
        c = CALLOCOBJECT();
        SWAP(a,c);
        erg += select_column(c,index,b);
        FREEALL(c);
        }
    else if (TABLEAUXP(a)) /* AK 280193 */
        {
        erg += select_column_tableaux(a,index,b);
        }
    else {
        INT j;
        SYMCHECK(index >= S_M_LI(a), "select_column: index >= length");
        erg += m_il_v(S_M_HI(a),b);
        for (j=0;j<S_M_HI(a);j++)
            COPY(S_M_IJ(a,j,index),S_V_I(b,j));
        }
    ENDR("select_column");
}


INT rank(a,b) OP a,b;
/* AK 220294 */
/* rank of a matrix */
/* a and b may be equal */
/* AK 141204 V3.0 */
/* AK 2221106 V3.1 */
{
    INT erg = OK;
    CTTO(MATRIX,INTEGERMATRIX,"rank(1)",a);
    {
    INT i,j,k,l,z=0;
    INT res = 0;
    OP e,c,d;
    CALLOCOBJECT3(c,d,e);
    COPY(a,e);
    a = e;
    j=0;
a2:
    for (i=0;i<S_M_HI(a);i++)
        {
        if (not NULLP(S_M_IJ(a,i,j))) 
            goto a1;
        }
    j++;
    if (j == S_M_LI(a))
        goto a3;
    goto a2;
a1:
    /* i , j ist nicht null */
    if (i != z) 
        erg += change_row_ij(a,i,z); /* AK 080394 */
    i = z++;

    res ++;
    for (k = 0;k<S_M_HI(a);k++)
        if (k != i)
            {
	    if (S_O_K(S_M_IJ(a,k,j))==GALOISRING) /* kein invers */
	         {
		 OP f1=callocobject();
		 OP f2=callocobject();
		 copy(S_M_IJ(a,k,j),f1); copy(S_M_IJ(a,i,j),f2);
		 /* zeile k soll null werden in der spalte i */
		 /* dazu f1*zeile_i  -  f2*zeile_k   in spalte k schreiben */
	         for (l=0;l<S_M_LI(a);l++)
			{
			CLEVER_MULT(S_M_IJ(a,i,l),f1,c);
			CLEVER_MULT(S_M_IJ(a,k,l),f2,d); ADDINVERS_APPLY(d);
			ADD(c,d,S_M_IJ(a,k,l));
			}
	         FREEALL2(f1,f2);
                 }
	    else {
		    erg += div(S_M_IJ(a,k,j),S_M_IJ(a,i,j),c);
		    for (l=0;l<S_M_LI(a);l++)
			{
			CLEVER_MULT(c,S_M_IJ(a,i,l),d);
			ADDINVERS_APPLY(d);
			ADD_APPLY(d,S_M_IJ(a,k,l));
			}
		  }
            }
    for (l=j+1;l<S_M_LI(a);l++)
	{
	if (S_O_K(S_M_IJ(a,i,0))==INTEGER) M_I_I(0,S_M_IJ(a,i,l));
	else null(S_M_IJ(a,i,0), S_M_IJ(a,i,l));
	}
    j++;
    if (j != S_M_LI(a))
        goto a2;
a3:
    erg += m_i_i(res,b);
    FREEALL3(c,d,a);    
    }
    ENDR("rank");
}

INT bideterminant_vector(a,b,c) OP a,b,c;
/* AK 010802 */
{
    INT i,erg=OK;
    CTO(VECTOR,"bideterminant_vector(1)",a);
    CTO(VECTOR,"bideterminant_vector(2)",b);
    SYMCHECK( NEQ(S_V_L(a),S_V_L(b)), "bideterminant_vector:vector of different length");
     
        {
        OP res;
        INT i,j;
        res = CALLOCOBJECT();
        erg += m_ilih_m(S_V_LI(a),S_V_LI(b),res);
        for (i=0;i<S_M_HI(res);i++)
        for (j=0;j<S_M_HI(res);j++)
            {
            OP poly;
            poly = S_M_IJ(res,i,j);
            erg += b_skn_po(CALLOCOBJECT(),CALLOCOBJECT(),NULL,poly);
            M_I_I(1,S_PO_K(poly));
            erg += m_ilih_nm( S_V_II(b,j)+1, S_V_II(a,i)+1,S_PO_S(poly));
            C_O_K(S_PO_S(poly),INTEGERMATRIX);
            M_I_I(1,S_M_IJ(S_PO_S(poly),S_V_II(a,i), S_V_II(b,j)));
            }
        erg += det_mat_imm(res,c);
        FREEALL(res);
        }
     
    ENDR("bideterminant_vector");
}  
 
INT bideterminant_tableaux(a,b,c) OP a,b,c;
/* AK 010802 */
{
    INT i,erg=OK;
    CTO(TABLEAUX,"bideterminant_tableaux(1)",a);
    CTO(TABLEAUX,"bideterminant_tableaux(2)",b);
    SYMCHECK( NEQ(S_T_U(a),S_T_U(b)), "bideterminant_tableaux:tableaux of different shape");
     
    erg += m_i_i(1,c);
    for (i=0;i<S_T_LI(a);i++)
        {
        OP row1,row2;
        OP res;
        row1 = CALLOCOBJECT();
        row2 = CALLOCOBJECT();
        erg += select_column(a,i,row1);
        erg += select_column(b,i,row2);
        res = CALLOCOBJECT();
        erg += bideterminant_vector(row1,row2,res);
        FREEALL(row1);
        FREEALL(row2);
        MULT_APPLY(res,c);
        FREEALL(res);
        }
    ENDR("bideterminant_tableaux");
}                                                                                                        

INT bideterminant(a,b,c) OP a,b,c;
/* AK 010802 */
{
    INT erg=OK;
    switch(S_O_K(a)){
        case TABLEAUX:erg += bideterminant_tableaux(a,b,c);break;
        case VECTOR:erg += bideterminant_vector(a,b,c);break;
        default:WTO("bideterminant(1)",a);break;
        }
    ENDR("bideterminant");
} 

INT P_symmetrized_bideterminant(a,b,c) OP a,b,c;
/* a and b tableaux of the same shape */
/* c becomes P-symmetrized bideterminant */
/* AK 060802 */
/* cf. Golembiowski Bayreuther Mathematische Schriften  */
{
    INT erg = OK;
    CTO(TABLEAUX,"P_symmetrized_bideterminant(1)",a);
    CTO(TABLEAUX,"P_symmetrized_bideterminant(2)",b);
    SYMCHECK(NEQ(S_T_U(a),S_T_U(b)),"P_symmetrized_bideterminant:different shapes of tableaux");
    {
    OP d,e;
    d = CALLOCOBJECT();
    e = CALLOCOBJECT();
    first_lex_tableaux(b,e);
    init(POLYNOM,c);
    do {
       OP f;
       f = CALLOCOBJECT();
       erg += bideterminant(a,e,f);
       insert(f,c,NULL,NULL);
       erg += copy(e,d);
       } while(next_lex_tableaux(d,e) == TRUE);
    FREEALL(d);
    FREEALL(e);
    }
    CTO(POLYNOM,"P_symmetrized_bideterminant(3-end)",c);
    ENDR("P_symmetrized_bideterminant");
} 

INT operate_perm_spaltenmatrix(a,b,c) OP a,b,c;
/* vertausch spalten gemaess der permutation */
/* spalte 0 nur wenn permutation auch 0 enthaelt */
/* AK 080802 */
{
    INT erg = OK;
    INT i,j;
    CTO(PERMUTATION,"operate_perm_spaltenmatrix(1)",a);
    CTTO(INTEGERMATRIX,MATRIX,"operate_perm_spaltenmatrix(2)",b);
    CE3(a,b,c,operate_perm_spaltenmatrix);
    SYMCHECK(S_P_LI(a) >= S_M_LI(b),
        "operate_perm_spaltenmatrix: permutation degree too big");
    COPY(b,c);
    for (j=0;j<S_P_LI(a);j++)
    for (i=0;i<S_M_HI(b);i++)
        CLEVER_COPY(S_M_IJ(b,i,j+1), S_M_IJ(c,i,S_P_II(a,j)));
    ENDR("operate_perm_spaltenmatrix");
} 

INT operate_perm_bideterminant(a,b,c) OP a,b,c; 
/* AK 080802 */
/* permutation operates on the bideterminant by exchanging columns */
{
    INT erg = OK; 
    OP z,m; 
    CTO(PERMUTATION,"operate_perm_bideterminant(1)",a); 
    CTO(POLYNOM,"operate_perm_bideterminant(2)",b); 
    CE3(a,b,c,operate_perm_bideterminant);
    if (NULLP(b)) { erg += copy(b,c); goto endr_ende; } 
    CTTO(INTEGERMATRIX,MATRIX,"operate_perm_bideterminant(2-self)",S_PO_S(b)); 
    SYMCHECK(S_P_LI(a) >= S_M_LI(S_PO_S(b)), 
          "operate_perm_bideterminant: permutation degree too big"); 

    {
    OP d;
    INT i;
    d = CALLOCOBJECT();
    t_LIST_VECTOR(b,d);
    for(i=0;i<S_V_LI(d);i++) 
        erg += operate_perm_spaltenmatrix(
                        a,S_MO_S(S_V_I(d,i)),S_MO_S(S_V_I(d,i)));
    qsort_vector(d);
    erg += t_VECTOR_POLYNOM(d,c);
    FREEALL(d);
    }
    ENDR("operate_perm_bideterminant"); 
} 


INT append_behind_matrix_matrix(OP a, OP b, OP c)
/* AK 030406 V3.1 */
/* a and b have same height */
{
	INT erg = OK;
	CTO(MATRIX,"append_behind_matrix_matrix(1)",a);
	CTO(MATRIX,"append_behind_matrix_matrix(2)",b);
	SYMCHECK(S_M_HI(a)!=S_M_HI(b),"append_behind_matrix_matrix: different sizes");
	CE3(a,b,c,append_behind_matrix_matrix);
	{
	INT i,j;
	erg += m_ilih_m(S_M_LI(a)+S_M_LI(b),S_M_HI(a),c);
	for (i=0;i<S_M_HI(c);i++)
	for (j=0;j<S_M_LI(a);j++)
		COPY(S_M_IJ(a,i,j),S_M_IJ(c,i,j));
	for (i=0;i<S_M_HI(c);i++)
	for (j=0;j<S_M_LI(b);j++)
		COPY(S_M_IJ(b,i,j),S_M_IJ(c,i,j+S_M_LI(a)));
	}
	ENDR("append_behind_matrix_matrix");
}

INT append_below_matrix_matrix(OP a, OP b, OP c)
/* AK 120406 V3.1 */
/* a and b have same length */
{
        INT erg = OK;
        CTO(MATRIX,"append_below_matrix_matrix(1)",a);
        CTO(MATRIX,"append_below_matrix_matrix(2)",b);
        SYMCHECK(S_M_LI(a)!=S_M_LI(b),"append_below_matrix_matrix: different sizes");
        CE3(a,b,c,append_below_matrix_matrix);
        {
        INT i,j;
        erg += m_ilih_m(S_M_LI(a) , S_M_HI(a)+S_M_HI(b),c);
        for (i=0;i<S_M_HI(a);i++)
        for (j=0;j<S_M_LI(a);j++)
                COPY(S_M_IJ(a,i,j),S_M_IJ(c,i,j));
        for (i=0;i<S_M_HI(b);i++)
        for (j=0;j<S_M_LI(b);j++)
                COPY(S_M_IJ(b,i,j),S_M_IJ(c,i+S_M_HI(a),j));
        }
        ENDR("append_below_matrix_matrix");
}

INT m_matrix_column_vector(OP a, OP b)
/* AK 231107 */
/* becomes vector of columns = vector of vector */
{
	INT erg = OK;
        CTO(MATRIX,"m_matrix_column_vector(1)",a)
	CE2(a,b,m_matrix_column_vector);
	{
	INT i;
	erg += m_il_v(S_M_LI(a),b);
	for (i=0;i<S_V_LI(b);i++) erg += select_column(a,i,S_V_I(b,i));
	}
	ENDR("m_matrix_column_vector");
}

#endif /* MATRIXTRUE */
