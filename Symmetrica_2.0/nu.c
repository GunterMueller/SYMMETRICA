/* FILE:nu.c */
#include "def.h"
#include "macro.h"


#ifdef SQRADTRUE
INT squareroot(a,b) OP a,b;
/* AK 040291 V1.2 */ /* AK 140891 V1.3 */
/* b becomes the squareroot of a */
{
    INT erg=OK;
    COP("squareroot(1)",a);
    COP("squareroot(2)",b);
    CE2(a,b,squareroot);
    CTO(EMPTY,"squareroot(i2)",b);

    switch (S_O_K(a))
    {
#ifdef BRUCHTRUE 
    case BRUCH:  
        erg += squareroot_bruch(a,b); 
        goto sqende;
#endif /* BRUCHTRUE */

#ifdef INTEGERTRUE 
    case INTEGER:  
        erg += squareroot_integer(a,b); 
        goto sqende;
#endif /* INTEGERTRUE */

#ifdef LONGINTTRUE 
    case LONGINT:  
        erg += squareroot_longint(a,b); 
        goto sqende;
#endif /* LONGINTTRUE */
    default:
        erg += WTO("squareroot(1)",a); 
        goto sqende;
    }
sqende:
    ENDR("squareroot");

}



INT ganzsquareroot(a,b) OP a,b;
/* AK 040291 V1.2 */ 
/* b becomes the integer squareroot of a ,
   i.e. the largest integer with b^2 <= a */
/* AK 140891 V1.3 */
/* AK 290704 V3.0 */
{
    INT erg = OK;
    COP("ganzsquareroot(1)",a);
    COP("ganzsquareroot(2)",b);
    CE2(a,b,ganzsquareroot);
    CTO(EMPTY,"ganzsquareroot(i2)",b);

    switch (S_O_K(a))
    {
#ifdef INTEGERTRUE 
    case INTEGER:  
        erg+= ganzsquareroot_integer(a,b);
        goto endr_ende;
#endif /* INTEGERTRUE */

#ifdef LONGINTTRUE
    case LONGINT:
        erg += ganzsquareroot_longint(a,b);
        goto endr_ende;
#endif /* LONGINTTRUE */

    default: 
        erg+=  WTO("ganzsquareroot(1)",a); 
        goto endr_ende;
    }
    ENDR("ganzsquareroot");
}
#endif /* SQRADTRUE */


INT max(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 010290 V1.1 */
/* b is a copy of the maximum element */

/* AK 140891 V1.3 */
{
    INT erg = OK;
    COP("max(1)",a);
    COP("max(2)",b);
    CE2(a,b,max);
    CTO(EMPTY,"max(i2)",b);

    switch (S_O_K(a))
    {

#ifdef MATRIXTRUE
    case MATRIX: 
        erg += max_matrix(a,b);
        goto ende;
#endif /* MATRIXTRUE */

#ifdef TABLEAUXTRUE
    case TABLEAUX:
        erg += max_tableaux(a,b);
        goto ende;
#endif /* TABLEAUXTRUE */

#ifdef VECTORTRUE
    case WORD:
    case INTEGERVECTOR:
        erg += max_integervector(a,b);
        goto ende;
    case VECTOR: 
        erg += max_vector(a,b); 
        goto ende;
#endif  /* VECTORTRUE */

    default:
        erg += WTO("max(1)",a); 
        goto ende;
    };
ende:
    ENDR("max");
}

INT min(a,b) OP a,b;
/* AK 140703 */
/* b is a copy of the minimum element */

/* AK 140891 V1.3 */
{
    INT erg = OK;
    COP("min(1)",a);
    COP("min(2)",b);
    CE2(a,b,min);
    CTO(EMPTY,"min(i2)",b);

    switch (S_O_K(a))
    {

#ifdef MATRIXTRUE
    case MATRIX: 
        erg += min_matrix(a,b);
        goto ende;
#endif /* MATRIXTRUE */

#ifdef TABLEAUXTRUE
    case TABLEAUX:
        erg += min_tableaux(a,b);
        goto ende;
#endif /* TABLEAUXTRUE */

#ifdef VECTORTRUE
    case WORD:
    case INTEGERVECTOR:
        erg += min_integervector(a,b);
        goto ende;
    case VECTOR: 
        erg += min_vector(a,b); 
        goto ende;
#endif  /* VECTORTRUE */

    default:
        erg += WTO("min(1)",a); 
        goto ende;
    };
ende:
    ENDR("max");
}

INT absolute(a,c) OP a,c;
/* AK 100888 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */
{
    INT erg=OK;
    COP("absolute(1)",a);
    COP("absolute(2)",c);
    CE2(a,c,absolute);
    CTO(EMPTY,"absolute(i2)",c);

    switch(S_O_K(a))
    {
#ifdef BRUCHTRUE
    case BRUCH: 
        erg += absolute_bruch(a,c); 
        goto ende;
#endif /* BRUCHTRUE */
#ifdef INTEGERTRUE
    case INTEGER: 
        M_I_I((S_I_I(a) > 0 ? S_I_I(a): - S_I_I(a)),c);
        goto ende;
#endif /* INTEGERTRUE */
#ifdef LONGINTTRUE
    case LONGINT: 
        erg +=  absolute_longint(a,c); 
        goto ende;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
    case MATRIX: 
        erg +=  absolute_matrix(a,c); 
        goto ende;
#endif /* MATRIXTRUE */
#ifdef VECTORTRUE
    case WORD:
    case COMPOSITION:
    case VECTOR: 
        erg += absolute_vector(a,c); 
        goto ende;
    case INTEGERVECTOR: 
        erg += absolute_integervector(a,c); 
        goto ende;
#endif /* VECTORTRUE */
    default:
        erg += WTO("absolute(1)",a); 
        goto ende;
    }
ende:
    ENDR("absolute");
}

INT transpose(a,b) OP a,b;
/* AK 280388 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */
{
    INT erg=OK;
    COP("transpose(1)",a);
    COP("transpose(2)",b);
    CE2(a,b,transpose);

    switch (S_O_K(a))
    {
#ifdef MATRIXTRUE
    case KOSTKA:
    case KRANZTYPUS:
    case MATRIX: 
        erg += transpose_matrix(a,b);
        goto ende;
#endif /* MATRIXTRUE */
    default:
        WTO("transpose(1)",a);
        goto ende;
    };
ende:
    ENDR("transpose");
}

INT sub(a,b,c)    OP a,b,c;
/* AK 300388 */ /* c = a - b */ /* AK 280689 V1.0 */ /* AK 131289 V1.1 */
/* AK 270291 V1.2 */ /* AK 140891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg = OK; 
    EOP("sub(1)",a);
    EOP("sub(2)",b);
    COP("sub(3)",c);
    CE3(a,b,c,sub);
    switch(S_O_K(a)) {
        default:
            erg += sub_default(a,b,c);
            break;
        }
    ENDR("sub");
}

INT sub_default(a,b,c) OP a,b,c;
/* AK 220202 */
{
    OP d;
    INT erg = OK;
    CTO(EMPTY,"sub_default(3)",c);
    CTO(ANYTYPE,"sub_default(1)",a);
    CTO(ANYTYPE,"sub_default(2)",b);
    d=CALLOCOBJECT();
    ADDINVERS(b,d);
    ADD(a,d,c);
    FREEALL(d);
    CTO(ANYTYPE,"sub_default(e3)",c);
    ENDR("sub_default");
}

INT sub_apply(a,b) OP a,b;
/* AK 300102 */
/* b := b-a; */
{
    INT erg = OK;
    EOP("sub_apply(1)",a);
    EOP("sub_apply(2)",b);
    if (a == b) {
        erg += m_i_i(0,a);
        }
    else {
        ADDINVERS_APPLY(a);
        ADD_APPLY(a,b);
        ADDINVERS_APPLY(a);
        }
    ENDR("sub_apply");
}

INT kgv(p1,second,d) OP p1, second, d;
/* 031186 */ /* d = kgv(p1,second) */
/* AK 280689 V1.0 */ /* AK 131289 V1.1 */ /* AK 290591 V1.2 */
/* AK 140891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg = OK;
    OP a,b;
    EOP("kgv(1)",p1);
    EOP("kgv(2)",second);
    COP("kgv(3)",d);
     
    a=callocobject();
    b=callocobject();
    erg += mult(p1,second,a);
    erg += ggt(p1,second,b);
    erg += div(a,b,d);
    erg += freeall(a);
    erg += freeall(b);
    ENDR("kgv");
}

INT signum(a,c) OP a,c;
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 140891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg=OK;
    EOP("signum(1)",a);
    COP("signum(2)",c);
    CE2(a,c,signum);
    switch (S_O_K(a))
    {
#ifdef PERMTRUE
    case PERMUTATION: 
        erg += signum_permutation(a,c);break;
#endif /* PERMTRUE */
    default:
        erg += WTO("signum",a); break;
    };
    ENDR("signum");
}


INT lehmercode(a,b) OP a,b;
/* berechnet den lehmercode entweder einer permuation oder eines vectors
AK 270787 */
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 140891 V1.3 */
/* AK 260398 V2.0 */
{
    INT erg=OK;
    CE2(a,b,lehmercode);
    switch (S_O_K(a))
    {
#ifdef PERMTRUE
    case PERMUTATION: 
        erg += lehmercode_permutation(a,b);
        break;
    case VECTOR: 
    case INTEGERVECTOR: 
        erg += lehmercode_vector(a,b);
        break;
#endif /* PERMTRUE */
    default: 
        WTO("lehmercode",a); break;
    };
    ENDR("lehmercode");
}

INT add(a,b,d) OP a,b,d;
/* AK 160986 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 270291 V1.2 */ /* AK 070891 V1.3 */
/* d = a+b */
{
    INT erg=OK;
    EOP("add(1)",a);
    EOP("add(2)",b);
    COP("add(3)",d);
    CE3(a,b,d,add);


    switch(S_O_K(a))
    {
#ifdef    MONOPOLYTRUE
    case MONOPOLY: 
        erg += add_monopoly (a,b,d);
        goto add_ende;
#endif /* MONOPOLYTRUE */
#ifdef    CYCLOTRUE
    case CYCLOTOMIC: 
        erg += add_cyclo (a,b,d);
        goto add_ende;
#endif /* CYCLOTRUE */
#ifdef    SQRADTRUE
    case SQ_RADICAL: 
        erg += add_sqrad (a,b,d);
        goto add_ende;
#endif /* SQRADTRUE */
    case INTEGER :     
        erg += add_integer(a,b,d); 
        break;
    case LAURENT :     
        erg += add_laurent(a,b,d); 
        break;
#ifdef FFTRUE
    case FF: 
        erg += add_ff(a,b,d);
        break;
#endif  /* FFTRUE */



#ifdef GRTRUE
    case GALOISRING: 
        erg += add_galois(a,b,d);
        break;
#endif  /* GRTRUE */


#ifdef REIHETRUE
    case REIHE: 
        erg += add_reihe(a,b,d);
        break;
#endif  /* REIHETRUE */
#ifdef PARTTRUE
    case PARTITION: 
        erg += add_partition(a,b,d);
        break;
#endif  /* PARTTRUE */
#ifdef POLYTRUE
    case GRAL:
    case POLYNOM : 
        erg += add_polynom(a,b,d);
        break;
    case MONOM : 
        erg += add_monom(a,b,d);
        break;
#endif /* POLYTRUE */
#ifdef VECTORTRUE
    case INTEGERVECTOR:
        erg += add_integervector(a,b,d);
        break;
    case VECTOR : 
        erg += add_vector(a,b,d);
        break;
#endif /* VECTORTRUE */
#ifdef SCHURTRUE
    case SCHUR : 
        erg += add_schur(a,b,d); 
        break;
#endif  /* SCHURTRUE */
#ifdef LONGINTTRUE
    case LONGINT : 
        erg += add_longint(a,b,d);
        break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case INTEGERMATRIX:
    case MATRIX : 
        erg += add_matrix(a,b,d);
        break;
#endif /* MATRIXTRUE */
#ifdef MONOMIALTRUE
    case MONOMIAL : 
        erg += add_monomial(a,b,d);
        break;
#endif /* MONOMIALTRUE */
#ifdef ELMSYMTRUE
    case ELM_SYM : 
        erg += add_elmsym(a,b,d);
        break;
#endif /* ELMSYMTRUE */
#ifdef HOMSYMTRUE
    case HOM_SYM : 
        erg += add_homsym(a,b,d);
        break;
#endif /* HOMSYMTRUE */
#ifdef POWSYMTRUE
    case POW_SYM : 
        erg += add_powsym(a,b,d);
        break;
#endif /* POWSYMTRUE */
#ifdef SCHUBERTTRUE
    case SCHUBERT:
        erg += add_schubert(a,b,d);
        break;
#ifdef UNDEF
        {
            switch(S_O_K(b))
            {
            case SCHUBERT : 
                erg += add_schubert_schubert(
                    a,b,d);
                break;
            default :
                { 
                printobjectkind(b);
                return error("add_schubert:wrong second type");
                }
            };
            break;
        }
#endif
#endif /* SCHUBERTTRUE */
#ifdef CHARTRUE
    case SYMCHAR: 
        erg += add_symchar(a,b,d);
        break;
#endif
#ifdef BRUCHTRUE
    case BRUCH : 
        erg += add_bruch (a,b,d);
        break;
#endif /* BRUCHTRUE */
    default:
        {
            if (nullp(a)) {
                erg += copy(b,d); 
                break; 
            }
            if (nullp(b)) {
                erg += copy(a,d); 
                break; 
            }
            printobjectkind(a);
            printobjectkind(b);
            return error("add: wrong types");
        }
    };
add_ende:
    ENDR("add");
}

INT sort(a) OP a;
/* sortiert das object in aufsteigender reihenfolge AK 270787 */
/* AK 160986 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 070891 V1.3 */
{
    INT erg = OK;
    EOP("sort(1)",a);

    switch(S_O_K(a))
    {
#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case VECTOR : 
        erg += sort_vector(a);break;
#endif /* VECTORTRUE */
    default:
        erg += WTO("sort",a); break;
    };
    ENDR("sort");
}

INT length(a,d) OP a,d;
/* 160986 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */
/* AK 240398 V2.0 */
{
    INT erg = OK;
    EOP("length(1)",a);
    COP("length(2)",d);
    CE2(a,d,length);

    switch(S_O_K(a))
    {
#ifdef BINTREETRUE
    case BINTREE : 
        erg += length_bintree(a,d);
        break;
#endif /* PARTTRUE */
#ifdef LISTTRUE
    case GRAL:
    case HOM_SYM:
    case POW_SYM:
    case ELM_SYM:
    case MONOMIAL:
    case LIST:
    case POLYNOM:
    case MONOPOLY:  /* MD */
    case SCHUBERT:
    case SCHUR: 
        erg += length_list(a,d);
        break;
#endif /* LISTTRUE */
#ifdef PARTTRUE
    case PARTITION : 
        erg += length_partition(a,d);
        break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
    case PERMUTATION : 
        erg += length_permutation(a,d);
        break;
#endif /* PERMTRUE */
#ifdef REIHETRUE
    case REIHE : 
        erg += length_reihe(a,d);
        break;
#endif /* REIHETRUE */
#ifdef SKEWPARTTRUE
    case SKEWPARTITION : 
        erg += length_skewpartition(a,d);
        break;
#endif /* SKEWPARTTRUE */
#ifdef VECTORTRUE
    case WORD:
    case COMPOSITION:
    case INTEGERVECTOR:
    case VECTOR : 
        erg += length_vector(a,d);
        break;
#endif /* VECTORTRUE */
    default:
        erg += WTO("length",a); break;
    };
    ENDR("length");
}

INT content(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 050390 V1.1 */ /* AK 140891 V1.3 */
/* AK 240398 V2.0 */
{
    INT erg=OK;
    CE2(a,b,content);
    switch(S_O_K(a))
    {
#ifdef TABLEAUXTRUE
    case TABLEAUX : 
        erg +=  content_tableaux(a,b );
        break;
#endif /* TABLEAUXTRUE */
#ifdef WORDTRUE  
    case WORD : 
        erg +=  content_word(a,b);
        break;
#endif /* WORDTRUE */
    default:
        erg += WTO("content",a); break;
    };
    ENDR("content");
}

INT sum(a,res) OP a,res;
/* AK 280689 V1.0 */ /* AK 050390 V1.1 */ /* AK 120391 V1.2 */
/* AK 140891 V1.3 */
/* AK 170298 V2.0 */
{
    INT erg = OK;
    COP("sum(1)",a);
    COP("sum(2)",res);
    CE2(a,res,sum);

    switch(S_O_K(a))
    {
#ifdef VECTORTRUE 
    case INTEGERVECTOR:
    case SUBSET:
    case COMPOSITION :
        erg += sum_integervector(a,res);
        break;
    case VECTOR : 
        erg += sum_vector(a,res); 
        break;
#endif /* VECTORTRUE */
#ifdef PARTTRUE
    case PARTITION:
        erg += weight_partition(a,res);
        break;
#endif /* PARTTRUE */
#ifdef MATRIXTRUE
    case MATRIX :
    case KOSTKA :
    case KRANZTYPUS :
    case INTEGERMATRIX :
        erg += sum_matrix(a,res); 
        break;
#endif /* MATRIXTRUE */
    default:
        erg += WTO("sum",a); break;
    };

    ENDR("sum");
}


INT conjugate(a,res) OP a,res;
/* AK 280689 V1.0 */ /* AK 281289 V1.1 */ /* AK 120891 V1.3 */
/* AK V2.0 170298 */
{
    INT erg = OK;
    COP("conjugate(1)",a);
    COP("conjugate(2)",res);

    CE2(a,res,conjugate);
    switch(S_O_K(a))
    {
#ifdef PARTTRUE
    case PARTITION: 
        erg += conjugate_partition(a,res); 
        break; 
#endif /* PARTTRUE */

#ifdef SKEWPARTTRUE
    case SKEWPARTITION :  /* AK 020890 V1.1 */
        erg += b_gk_spa(
            callocobject(), callocobject(), res);
        erg += conjugate_partition(S_SPA_G(a),S_SPA_G(res));
        erg += conjugate_partition(S_SPA_K(a),S_SPA_K(res));
        break;
#endif /* SKEWPARTTRUE */

#ifdef MONOMTRUE
    case MONOM:    
        erg += b_sk_mo(callocobject(),callocobject(),res);
        erg += copy(S_MO_K(a),S_MO_K(res));
        erg += conjugate(S_MO_S(a),S_MO_S(res));
        break;
#endif /* MONOMTRUE */

#ifdef SCHURTRUE
    case SCHUR: 
        erg += conjugate_schur(a,res); 
        break;
    case MONOMIAL: 
        erg += conjugate_monomial(a,res); 
        break;
    case HOM_SYM: 
        erg += conjugate_homsym(a,res); 
        break;
    case ELM_SYM:
        erg += conjugate_elmsym(a,res); 
        break;
    case POW_SYM: 
        erg += conjugate_powsym(a,res); 
        break;
#endif /* SCHURTRUE */

#ifdef TABLEAUXTRUE
    case TABLEAUX:
        erg += conjugate_tableaux(a,res,conjugate);
        break;
#endif /* TABLEAUXTRUE */
    default:
        erg +=  WTO("conjugate",a); 
        break;
    };

    ENDR("conjugate");
}


INT addinvers(a,res) OP a,res;
/* AK 280689 V1.0 */ /* AK 131289 V1.1 */ /* AK 270291 V1.2 */
/* AK 140891 V1.3 */
{
    INT erg = OK;
    COP("addinvers(1)",a);
    COP("addinvers(2)",res);
    CE2(a,res,addinvers);

    switch(S_O_K(a))
    {
#ifdef BRUCHTRUE
    case BRUCH :     
        erg += addinvers_bruch(a,res);
        break;
#endif /* BRUCHTRUE */
#ifdef CYCLOTRUE
    case CYCLOTOMIC: 
        erg +=  addinvers_cyclo (a,res);
        break;
#endif /* CYCLOTRUE */
#ifdef FFTRUE
    case FF :     
        erg += addinvers_ff(a,res);
        break;
#endif /* FFTRUE */
#ifdef INTEGERTRUE
    case INTEGER :       
        erg+= addinvers_integer(a,res);
        break;
#endif /* INTEGERTRUE */    
#ifdef LONGINTTRUE
    case LONGINT :      
        erg+= addinvers_longint(a,res);
        break;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
    case MATRIX :       
        erg+= addinvers_matrix(a,res);
        break;
#endif /* MATRIXTRUE */    
#ifdef MONOMTRUE
    case MONOM :  
        erg+= addinvers_monom(a,res);
        break;
#endif /* MONOMTRUE */
#ifdef MONOPOLYTRUE
    case MONOPOLY: 
        erg+= addinvers_monopoly (a,res);
        break;
#endif /* MONOPOLYTRUE */
#ifdef POLYTRUE
    case ELM_SYM:
    case POW_SYM:
    case MONOMIAL:
    case HOM_SYM:
    case SCHUR:
    case SCHUBERT:
    case GRAL:
    case POLYNOM :     
        erg += addinvers_polynom(a,res);
        break;
#endif /* POLYTRUE */
#ifdef REIHETRUE /* AK 020893 */
    case REIHE :    
        erg += addinvers_reihe(a,res);
        break;
#endif /* REIHETRUE */
#ifdef SQRADTRUE
    case SQ_RADICAL: 
        erg+=  addinvers_sqrad (a,res);
        break;
#endif /* SQRADTRUE */
#ifdef CHARTRUE
    case SYMCHAR :     
        erg += addinvers_symchar(a,res);
        break;
#endif /* CHARTRUE */
#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case VECTOR :      
        erg += addinvers_vector(a,res);
        break;
#endif /* VECTORTRUE */
    default:
        erg +=  WTO("addinvers(1)",a); break;
    };
    ENDR("addinvers");
}




INT binom_values[BINOMLIMIT][BINOMLIMIT] = {
{1, 0, 0,  0,  0,  0,  0,  0,  0,  0, 0, 0,0},
{1, 1, 0,  0,  0,  0,  0,  0,  0,  0, 0, 0,0},
{1, 2, 1,  0,  0,  0,  0,  0,  0,  0, 0, 0,0},
{1, 3, 3,  1,  0,  0,  0,  0,  0,  0, 0, 0,0},
{1, 4, 6,  4,  1,  0,  0,  0,  0,  0, 0, 0,0},
{1, 5,10, 10,  5,  1,  0,  0,  0,  0, 0, 0,0},
{1, 6,15, 20, 15,  6,  1,  0,  0,  0, 0, 0,0},
{1, 7,21, 35, 35, 21,  7,  1,  0,  0, 0, 0,0},
{1, 8,28, 56, 70, 56, 28,  8,  1,  0, 0, 0,0},
{1, 9,36, 84,126,126, 84, 36,  9,  1, 0, 0,0},
{1,10,45,120,210,252,210,120, 45, 10, 1, 0,0},
{1,11,55,165,330,462,462,330,165, 55,11, 1,0},
{1,12,66,220,495,792,924,792,495,220,66,12,1} };

INT binom_small(oben,unten,d) OP oben, unten, d;
/* we know  0<= oben <= BINOMLIMIT
            0<= unten 
   all three a different, d is freed */
{
    INT erg = OK;
    CTO(INTEGER,"binom_small",oben);
    CTO(INTEGER,"binom_small",unten);
    CTO(EMPTY,"binom_small",d);
    SYMCHECK(S_I_I(oben) < 0 ,"binom_small:oben <0");
    SYMCHECK(S_I_I(oben) > BINOMLIMIT ,"binom_small:oben > BINOMLIMIT");
    SYMCHECK(S_I_I(unten) < 0 ,"binom_small:unten <0");

    if (S_I_I(unten) > S_I_I(oben))
        M_I_I(0,d);
    else
        M_I_I( binom_values [ S_I_I(oben) ] [S_I_I(unten)] ,d);
    ENDR("binom_small");
}

INT binom(oben , unten, d) OP oben, unten, d;
/* AK 041186 */
/* d = oben ! / unten ! * (oben -unten)! */
/* auf integer umgestellt am 120187 */
/* AK 280689 V1.0 */ /* AK 010290 V1.1 */
/* AK 140891 V1.3 */
/* AK 030892 oben may be POLYNOM */
/* AK 160703 oben or unten may be equal to d */
{
    OP a,b,c;
    INT i,ui;
    INT erg = OK;
    CTO(INTEGER,"binom(2)",unten);
    SYMCHECK(S_I_I(unten) < 0,"binom:unten < 0");
    ui = S_I_I(unten);

    if (unten == d) /* AK160703 */
        {
        a = CALLOCOBJECT();
        SWAP(a,d);
        erg += binom(oben,a,d);
        FREEALL(a);
        goto ende;
        }
    if (oben == d) /* AK160703 */
        {
        a = CALLOCOBJECT();
        SWAP(a,d);
        erg += binom(a,unten,d);
        FREEALL(a);
        goto ende;
        }

    if (S_O_K(oben) == POLYNOM) /* AK 030892 */
    {
        CALLOCOBJECT2(c,b);
        COPY(oben,c);
        M_I_I(-1,b);
        CLEVER_COPY(oben,d);
        for (i=1;i<ui;i++)
        {
            ADD_APPLY(b,c);
            MULT_APPLY(c,d);
        }
        erg += fakul(unten,c);
        erg += invers_apply(c);
        MULT_APPLY(c,d);
        FREEALL2(c,b);
        goto ende;
    }

    CTO(INTEGER,"binom(i1)",oben);

    if (oben == d)
    {
        c = callocobject();
        *c = *oben;
        C_O_K(d,EMPTY);
        erg += binom(c,unten,d);
        erg += freeall(c);
        goto ende;
    }

    if (unten == d)
    {
        c = callocobject();
        *c = *unten;
        C_O_K(d,EMPTY);
        erg += binom(oben,c,d);
        erg += freeall(c);
        goto ende;
    }

    if (not EMPTYP(d))
        freeself(d);

    if (S_I_I(oben) == (-1L))
    {
        (S_I_I(unten) % 2L == 0L ?
            M_I_I(1L,d) :
            M_I_I(-1L,d));
        goto ende;
    }

    if (S_I_I(oben)<0)
    {
        INT schalter = 0L;
        b = callocobject();
        c = callocobject();
        a = callocobject();
        COPY_INTEGER(unten,b); 
        COPY_INTEGER(oben,a);
        INC_INTEGER(a);
        while(S_I_I(b) >= 0L)
        {
            binom(a,b,c);
            (schalter++ % 2L == 0L ? add(c,d,d):
                sub(d,c,d));
            dec(b);
        };
        FREEALL(c);
        goto binomende;
    }



    if (S_I_I(oben)==S_I_I(unten)) { M_I_I(1L,d); goto ende;}
    if (S_I_I(oben)<S_I_I(unten)) { M_I_I(0L,d); goto ende;}


    a = CALLOCOBJECT();
    b = CALLOCOBJECT();
    M_I_I(S_I_I(oben) - S_I_I(unten),a);
    erg += fakul(a,b);
    /* now multiplying the remaining part */
    FREESELF(d);
    M_I_I(1,d);
    for (i=S_I_I(oben);i>S_I_I(unten);i--)
        {
        M_I_I(i,a);
        MULT_APPLY_INTEGER(a,d);
        }
    GANZDIV_APPLY(d,b); /* d = d/b */
binomende:
    FREEALL(a); 
    FREEALL(b); 
ende:
    ENDR("binom");
}


INT inc(a) OP a;
/* AK 280689 V1.0 */ /* AK 081289 V1.1 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("inc(1)",a);
    switch(S_O_K(a))
    {
#ifdef INTEGERTRUE
    case INTEGER : 
        INC_INTEGER(a);
        break;
#endif /* INTEGERTRUE */    

#ifdef LONGINTTRUE
    case LONGINT : 
        erg += inc_longint(a);
        break;
#endif /* LONGINTTRUE */

#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case INTEGERMATRIX:
    case MATRIX : 
        erg += inc_matrix(a);
        break;
#endif /* MATRIXTRUE */

#ifdef PARTTRUE
    case PARTITION : 
        INC_PARTITION(a);
        break;
#endif /* PARTTRUE */

#ifdef PERMTRUE
    case PERMUTATION : 
        erg += inc_permutation(a);
        break;
#endif /* PERMTRUE */

#ifdef REIHETRUE
    case REIHE : 
        erg += inc_reihe(a);
        break;
#endif /* REIHETRUE */    

#ifdef TABLEAUXTRUE
    case TABLEAUX : 
        erg += inc_tableaux(a);
        break;
#endif /* TABLEAUXTRUE */

#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case SUBSET:
    case COMPOSITION:
    case VECTOR : 
        erg += inc_vector(a);
        break;
    case BITVECTOR:
        erg += inc_bitvector(a); 
        break;
#endif /* VECTORTRUE */

    default: 
        erg += WTO("inc(1)",a);
        break;
    };
    ENDR("inc");
}

INT dec(a) OP a;
/* AK 280689 V1.0 */ /* AK 131289 V1.1 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("dec(1)",a);
    switch(S_O_K(a))
    {
#ifdef INTEGERTRUE
    case INTEGER : 
        erg += dec_integer(a);
        break;
#endif /* INTEGERTRUE */    
#ifdef LONGINTTRUE
    case LONGINT : 
        erg += dec_longint(a);
        break;
#endif /* LONGINTTRUE */
#ifdef PARTTRUE
    case PARTITION : 
        erg += dec_partition(a);
        break;
#endif /* PARTTRUE */
#ifdef PERMTRUE
    case PERMUTATION : 
        erg += dec_permutation(a);
        break;
#endif /* PERMTRUE */
#ifdef VECTORTRUE
    case INTEGERVECTOR:
        erg += dec_integervector(a);
        break;
    case VECTOR : 
        erg += dec_vector(a);
        break;
#endif /* VECTORTRUE */
    default: 
        erg += WTO("dec(1)",a); break;
    };
    ENDR("dec");
}


INT qdimension(n,d) OP n, d;
/* AL 180393 */
{
    INT erg = OK;
    EOP("qdimension(1)",n);
    COP("qdimension(2)",d);
    CE2(n,d,qdimension);

    switch (S_O_K(n))
    {
#ifdef SCHUBERTTRUE /* AL 180393 */
    case SCHUBERT: 
        erg +=  dimension_schubert(n,d); 
        break;
#endif /* SCHUBERTTRUE */
    default: 
        WTO("qdimension(1)",n); 
        break;
    }
    ENDR("qdimension");
}


INT dimension(n,d) OP n, d;
/* AK 011288 */ /* AK 060789 V1.0 */ /* AK 131289 V1.1 */
/* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("dimension(1)",n);
    COP("dimension(2)",d);
    CE2(n,d,dimension);

    switch (S_O_K(n))
    {
#ifdef PARTTRUE
    case AUG_PART: 
        erg +=  dimension_augpart(n,d);
        break;
    case PARTITION: 
        erg +=  dimension_partition(n,d);
        break;
#endif /* PARTTRUE */
#ifdef SCHUBERTTRUE /* AL 180393 */
    case SCHUBERT: 
        erg +=  dimension_schubert(n,d);
        break;
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE /* AK 020890 V1.1 */
    case SCHUR: 
        erg +=  dimension_schur(n,d);
        break;
#endif /* SCHURTRUE */
#ifdef SKEWPARTTRUE /* AK 020890 V1.1 */
    case SKEWPARTITION: 
        erg +=  dimension_skewpartition(n,d);
        break;
#endif /* SKEWPARTTRUE */
    default: 
        erg += WTO("dimension",n); break;
    }
    ENDR("dimension");
}


INT div(a,b,c) OP a,b,c;
/* exact division */
{
    INT erg = OK;
    EOP("div(1)",a);
    EOP("div(2)",b);
    COP("div(3)",c);
    CE3(a,b,c,div);
    switch(S_O_K(a)) {
        default:
            erg += div_default(a,b,c);
            break;
        }
    ENDR("div");
}

INT div_default(a,b,d) OP a,b,d;
/* AK 280689 V1.0 */ /* AK 071289 V1.1 */ /* AK 250391 V1.2 */
/* AK 140891 V1.3 */
/* d := a/b */
{
    /* AK 031286 als invers*mult */
    INT erg = OK;
    OP c;
    CTO(ANYTYPE,"div_default(1)",a);
    CTO(ANYTYPE,"div_default(2)",b);
    CTO(EMPTY,"div_default(3)",d);
    c = CALLOCOBJECT();
    INVERS(b,c);
    MULT(a,c,d);
    FREEALL(c);

    CTO(ANYTYPE,"div_default(e3)",d);
    ENDR("div_default");
}


INT quores(a,b,c,d) OP a,b,c,d;
/* c = ganzdiv(a,b)  d = mod(a,b) */
/* AK 050291 V1.2 */ /* AK 140891 V1.3 */
{
    OP e;
    INT erg=OK;
    SYMCHECK( c == d ,"quores: two result in one variable");

    if (a == c)
    { 
        e =CALLOCOBJECT(); 
        *e = *a; 
        C_O_K(c,EMPTY); 
        erg +=quores(e,b,c,d);
        FREEALL(e); 
        goto quoresende;
    }
    if (a == d)
    { 
        e =CALLOCOBJECT(); 
        *e = *a; 
        C_O_K(d,EMPTY); 
        erg +=quores(e,b,c,d);
        FREEALL(e); 
        goto quoresende;
    }
    if (b == c)
    { 
        e =CALLOCOBJECT(); 
        *e = *b; 
        C_O_K(c,EMPTY); 
        erg +=quores(a,e,c,d);
        FREEALL(e); 
        goto quoresende;
    }
    if (b == d)
    { 
        e =CALLOCOBJECT(); 
        *e = *b; 
        C_O_K(d,EMPTY); 
        erg +=quores(a,e,c,d);
        FREEALL(e); 
        goto quoresende;
    }
    if (not EMPTYP(d)) 
        erg += freeself(d);
    if (not EMPTYP(c)) 
        erg += freeself(c);
    if (EMPTYP(a) || EMPTYP(b)) 
        goto quoresende;

    if (nullp(b))    
        {
        debugprint(a);
        debugprint(b);
        error("quores:null division");
        goto endr_ende;
        }
    if (einsp(b)) 
        {
        erg += copy(a,c);
        erg += null(a,d); /* AK 170206 */
        goto quoresende;
        }


    switch(S_O_K(a))
    {
#ifdef INTEGERTRUE
    case INTEGER :      
        erg += quores_integer(a,b,c,d);break;
#endif /* INTEGERTRUE */    
#ifdef LONGINTTRUE
    case LONGINT :     
        erg += quores_longint(a,b,c,d);break;
#endif /* LONGINTTRUE */
#ifdef MONOPOLYTRUE
    case MONOPOLY :     
        erg += quores_monopoly(a,b,c,d);break;
    case POLYNOM:
        {
        OP aa,bb,cc,dd;
        aa = CALLOCOBJECT();
        bb = CALLOCOBJECT();
        cc = CALLOCOBJECT();
        dd = CALLOCOBJECT();
        t_POLYNOM_MONOPOLY(a,aa);
        t_POLYNOM_MONOPOLY(b,bb);
        erg += quores_monopoly(aa,bb,cc,dd);
        t_MONOPOLY_POLYNOM(cc,c);
        t_MONOPOLY_POLYNOM(dd,d);
        FREEALL4(aa,bb,cc,dd);
        break;
        }
#endif /* MONOPOLYTRUE */
    default:
        erg +=  WTT("quores",a,b);
        break;
    }
quoresende:
    ENDR("quores");
}

INT mod(a,b,c) OP a,b,c;
/* AK 040393 */
/* AK 030498 V2.0 */
/* c := a % b; */
{
    OP d;
    INT erg = OK;
    EOP("mod(1)",a);
    EOP("mod(2)",b);
    SYMCHECK(NULLP(b),"mod: second parameter = zero");

    CE3(a,b,c,mod);

    if (matrixp(a)) /* AK 300793 */
        {
        if (S_O_K(b) == INTEGER)
            {
            erg +=  mod_matrix(a,b,c);
            goto endr_ende;
            }
        }
    else if (vectorp(a)) /* AK 101198 */
        {
        if (S_O_K(b) == INTEGER)
            {
            erg +=  mod_vector(a,b,c);
            goto endr_ende;
            }
        }
    else if (S_O_K(a)==MONOM)
        {
        erg += mod_monom(a,b,c);
        goto endr_ende;
        }
    else if (S_O_K(a)==POLYNOM)
        {
        erg += mod_polynom(a,b,c);
        goto endr_ende;
        }
    else if (LISTP(a))
        {
        OP s,k,z;
        erg += init(S_O_K(a),c);
        FORALL(z,a,{
            k = CALLOCOBJECT();
            erg += mod(S_MO_K(z),b,k);
            if (NULLP(k) ) FREEALL(k);
            else {
                s = CALLOCOBJECT();
                b_sk_mo(CALLOCOBJECT(),k,s);
                COPY(S_MO_S(z),S_MO_S(s));
                insert(s,c,NULL,NULL);
                }
            });
        goto endr_ende;
        }

    d = CALLOCOBJECT();
    if (S_O_K(a) == INTEGER) 
        erg += quores_integer(a,b,d,c);
    else if (S_O_K(a) == LONGINT)
        erg += quores_longint(a,b,d,c);
    else if (S_O_K(a) == MONOPOLY)
        erg += quores_monopoly(a,b,d,c);
    else
        erg += WTO("mod",a);

    FREEALL(d);
    ENDR("mod");
}

INT ganzdiv(a,b,c) OP a,b,c;
/*AK 040393 */
/* c := a/b */
{
    OP d ;
    INT erg = OK;

    if (a == b) { m_i_i(1,c); goto endr_ende; }
    CE3(a,b,c,ganzdiv);
    
    d = callocobject();
    if (S_O_K(a) == INTEGER)
        erg += quores_integer(a,b,c,d);
    else if (S_O_K(a) == LONGINT)
        erg += quores_longint(a,b,c,d);
    else if (S_O_K(a) == MONOPOLY)
        erg += quores_monopoly(a,b,c,d);
    else
        WTO("ganzdiv",a);
    erg += freeall(d);
    ENDR("ganzdiv");
}

INT ganzdiv_longint(a,b,c) OP a,b,c;
/* AK 051001 */
/* c = a/b */
{
    INT erg = OK;
    OP d;
    CTO(LONGINT,"ganzdiv_longint(1)",a);
    CTO(EMPTY,"ganzdiv_longint(3)",c);

    d = callocobject();
    erg += quores_longint(a,b,c,d);
    erg += freeall(d);

    ENDR("ganzdiv_longint");
}

INT ganzdiv_integer_integer(a,b,c) OP a,b,c;
/* AK 291001 */
{
    INT erg = OK;
    CTO(INTEGER,"ganzdiv_integer_integer(1)",a);
    CTO(INTEGER,"ganzdiv_integer_integer(2)",b);
    CTO(EMPTY,"ganzdiv_integer_integer(3)",c);
    M_I_I(S_I_I(a) / S_I_I(b),c);
    ENDR("ganzdiv_integer_integer");
}

INT ganzdiv_integer(a,b,c) OP a,b,c;
/* AK 051001 */
/* a is INTEGER */
{
    INT erg = OK;
    OP d;
    CTO(INTEGER,"ganzdiv_integer(1)",a);
    CTO(EMPTY,"ganzdiv_integer(2)",c);

    if (S_O_K(b) == INTEGER) {
        M_I_I(S_I_I(a) / S_I_I(b),c);
        }
 
    else { 
        d = CALLOCOBJECT();
        erg += quores_integer(a,b,c,d);
        FREEALL(d);
        }
    ENDR("ganzdiv_integer");
}

INT mod_apply_integer(a,b) OP a,b;
/* AK 011101 */
/* a = a mod b */
{
    INT erg = OK;
    CTO(INTEGER,"mod_apply_integer(1)",a);
    switch(S_O_K(b)) {
        case INTEGER:
            M_I_I(S_I_I(a) % S_I_I(b), a);
            break;
        case LONGINT:
            erg += mod_apply_integer_longint(a,b);
            break;
        default:
            erg += WTO("mod_apply_integer(2)",b);
            break;
        }
    ENDR("mod_apply_integer");
}


INT mod_apply(a,b) OP a,b;
/* AK 051001 */
/* a := a mod b */
/* a and b may be identic */
{
    INT erg = OK;
    OP c;
    EOP("mod_apply(1)",a);
    EOP("mod_apply(2)",b);

    if (a == b) {
        erg += m_i_i(0,a);
        goto endr_ende;
        }
    switch(S_O_K(a)) {
        case INTEGER:
            erg += mod_apply_integer(a,b);
            goto endr_ende;
        case LONGINT:
            erg += mod_apply_longint(a,b);
            goto endr_ende;
        default: 
            break;
        }

    c = callocobject();
    erg += swap(a,c);
    erg += mod(c,b,a);
    erg += freeall(c);
    ENDR("mod_apply");
}

INT ganzdiv_apply_integer(a,b) OP a,b;
/* AK 011101 */
/* a := a/b */
{
    INT erg = OK;
    CTO(INTEGER,"ganzdiv_apply_integer(1)",a);
    switch (S_O_K(b) ) 
        {
        case INTEGER:
            M_I_I(S_I_I(a)/S_I_I(b),a); 
            break;
        default: {
            OP c;
            c = CALLOCOBJECT();
            *c = *a;
            C_O_K(a,EMPTY);
            erg += ganzdiv_integer(c,b,a);
            FREEALL(c);
            }
            break;
        }
    ENDR("ganzdiv_apply_integer");
}


INT div_apply_integer(a,b) OP a,b;
/* AK 011101 */
/* a = a / b */
{
    INT erg = OK;
    CTO(INTEGER,"div_apply_integer(1)",a);
    switch (S_O_K(b) )
        {
        case INTEGER:
            if (S_I_I(b) == 1);
            else if (S_I_I(b) == -1)
                ADDINVERS_APPLY(a);
            else if ((S_I_I(a) % S_I_I(b)) == 0)
                M_I_I(S_I_I(a)/S_I_I(b),a);
            else
                {
                erg += m_ioiu_b(S_I_I(a),S_I_I(b),a);
                erg += kuerzen(a);
                }
            break;
        default: {
            OP c;
            c = CALLOCOBJECT();
            *c = *a;
            C_O_K(a,EMPTY);
            erg += div(c,b,a);
            FREEALL(c);
            }
            break;
        }
    ENDR("div_apply_integer");
}
 


INT ganzdiv_apply(a,b) OP a,b;
/* AK 151294 */
/* a := a/b */
/* a and b may be identic */
{
    INT erg = OK;
    EOP("ganzdiv_apply",a);
    EOP("ganzdiv_apply",b);

    if (a == b)
        {
        erg += m_i_i((INT)1,a);
        goto endr_ende;
        }

    switch(S_O_K(a))
        {
        case INTEGER:
            erg += ganzdiv_apply_integer(a,b);
            break;
        case LONGINT:
            erg += ganzdiv_apply_longint(a,b);
            break;
        default:
            {
            OP c;
            c = CALLOCOBJECT();
            *c = *a;
            C_O_K(a,EMPTY);
            erg += ganzdiv(c,b,a);
            FREEALL(c);
            }
            break;
        }
    ENDR("ganzdiv_apply");
}

INT div_apply(a,b) OP a,b;
/* AK 151294 */
/* a := a/b */
/* a and b may be identic */
/* AK 291104 V3.0 */
{
    INT erg = OK;
    EOP("div_apply(1)",a);
    EOP("div_apply(2)",b);
 
    if (a == b)
        erg += eins(a,a);
    else {
        switch(S_O_K(a))
            {
            case INTEGER:
                erg += div_apply_integer(a,b);
                break;
            default:
                {
                OP c;
                c = CALLOCOBJECT();
                *c = *a;
                C_O_K(a,EMPTY);
                erg += div(c,b,a);
                FREEALL(c);
                }
                break;
            }
        }
    ENDR("div_apply");
}
 



INT fakul(n,d) OP n, d;
/* AK 081086 */ /* d = n! */ /* auf integer umgestellt 120187 */
/* AK 280689 V1.0 */ /* AK 181289 V1.1 */ /* AK 060391 V1.2 */
/* AK 140891 V1.3 */
/* n and d may be identic */
{
    INT erg = OK;
    EOP("fakul(1)",n);
    COP("fakul(2)",d);
    CTO(INTEGER,"fakul(1)",n);

    SYMCHECK(S_I_I(n) < 0,"fakul:negativ INTEGER");

    if (S_I_I(n) > (INT)12)   {
#ifdef LONGINTTRUE
        erg+=fakul_longintresult(n,d);
        goto endr_ende;
#else /* LONGINTTRUE */
        erg += error("fakul:overflow no LONGINT available");
        goto endr_ende;
#endif /* LONGINTTRUE */
    }

    if (d != n) 
        FREESELF(d);
    switch(S_I_I(n))
        {
        case 0:
        case 1:     M_I_I(1L,d);break;
        case 2:     M_I_I(2L,d);break;
        case 3:     M_I_I(6L,d);break;
        case 4:     M_I_I(24L,d);break;
        case 5:     M_I_I(120L,d);break;
        case 6:     M_I_I(720L,d);break;
        case 7:     M_I_I(5040L,d);break;
        case 8:     M_I_I(40320L,d);break;
        case 9:     M_I_I(362880,d);break;
        case 10:     M_I_I(3628800L,d);break;
        case 11:     M_I_I(39916800L,d);break;
        case 12:     M_I_I(479001600L,d);break;
        }
    ENDR("fakul");
}


#ifdef LONGINTTRUE
INT fakul_longintresult(n,res) OP n,res;
/* AK 180888 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140591 V1.2 */ /* AK 140891 V1.3 */
/* n is of type INTEGER and > 12 */
/* n and res may be identic */
{
    OP i = callocobject();
    OP s = callocobject();
    INT erg = OK,ni;
    CTO(INTEGER,"fakul_longintresult",n);

    ni = S_I_I(n);
    erg += m_i_longint(479001600L,res); /* 12! */
    M_I_I(13L,i);
    while (S_I_I(i) <= ni)
    {
        if ((S_I_I(i)+4) > ni)
	    {
	    erg += mult_apply_integer_longint(i,res);
	    INC_INTEGER(i);
            }
        else {
            if (S_I_I(i) < 120) {
		    M_I_I((S_I_I(i)*(S_I_I(i)+1)*
                          (S_I_I(i)+2)*(S_I_I(i)+3)),s);
		    erg += mult_apply_integer_longint(s,res);
		    M_I_I(S_I_I(i)+4,i); }
            else if (S_I_I(i) < 700) {
                    M_I_I((S_I_I(i)*(S_I_I(i)+1)*(S_I_I(i)+2)),s);
                    erg += mult_apply_integer_longint(s,res);
                    M_I_I(S_I_I(i)+3,i); }
            else if (S_I_I(i) < 20000) {
                    M_I_I((S_I_I(i)*(S_I_I(i)+1)),s);
                    erg += mult_apply_integer_longint(s,res);
                    M_I_I(S_I_I(i)+2,i); }
            else {
                    erg += mult_apply_integer_longint(i,res);
                    INC_INTEGER(i);}
            }
    }
    FREEALL2(i,s);
    ENDR("fakul_longint");
}
#endif /* LONGINTTRUE */

#define GGT_INT_INT(ai,bi,res)\
    do { \
    INT c;\
    if (ai < 0) ai = -ai;\
    if (bi < 0) bi = -bi;\
    if (ai == 0) {\
        res = bi;\
        }\
    else if (bi == 0) {\
        res = ai;\
        }\
    else if ( ai == 1 || bi == 1) {\
        res = 1;\
        }\
    else if (ai == bi) {\
        res = ai;\
        }\
    else {\
        c =0;\
        while ((ai & 1) == 0 && (bi & 1) == 0)\
        {\
            ai >>= 1;\
            bi >>= 1;\
            c++;\
        }\
        while ((ai & 1) == 0)\
            ai >>= 1;\
        while ((bi & 1) == 0)\
            bi >>= 1;\
        /* beide ungerade */\
 \
        while (ai != bi)\
            if (ai > bi)\
            {\
                ai -= bi;\
                do\
                    ai >>= 1;\
                while ((ai & 1) == 0);\
            }\
            else\
            {\
                bi -= ai;\
                do\
                    bi >>= 1;\
                while ((bi & 1) == 0);\
            }\
        res = ai << c;\
        }\
    } while (0)



INT ggt_integer_integer(a,b,d) OP a,b,d;
/* AK 300102 */
/* always positive */
{
    INT res,ai,bi,erg = OK;
    CTO(INTEGER,"ggt_integer_integer(1)",a);
    CTO(INTEGER,"ggt_integer_integer(2)",b);
    CTTO(EMPTY,INTEGER,"ggt_integer_integer(3)",d);
    ai = S_I_I(a); 
    bi = S_I_I(b); 
    GGT_INT_INT(ai,bi,res);
    M_I_I(res,d);
    ENDR("ggt_integer_integer");
}


INT ggt_integer(a,b,c) OP a,b,c;
{
    INT erg = OK;
    CTO(INTEGER,"ggt_integer(1)",a);
    CTO(EMPTY,"ggt_integer(3)",c);

    switch(S_O_K(b)) {
        case INTEGER: erg += ggt_integer_integer(a,b,c);
            goto endr_ende;
        case LONGINT: erg += ggt_integer_longint(a,b,c);
            goto endr_ende;
        default:
            erg += WTO("ggt_integer(2)",b); 
            goto endr_ende;
        }
    ENDR("ggt_integer");
}


 
INT ggt_integer_longint(a,b,d) OP a,b,d;
/* always positive */
/* AK 300102 */
{
    INT erg = OK;
    OP ac;
    CTO(INTEGER,"ggt_integer_longint(1)",a);
    CTO(LONGINT,"ggt_integer_longint(2)",b);
    CTTO(INTEGER,EMPTY,"ggt_integer_longint(3)",d);
    if (S_I_I(a) == 0) {
        C_O_K(d,EMPTY); 
        erg += copy_longint(b,d);
        }
    else {
        INT t=0;
        ac = CALLOCOBJECT();
        if (NEGP_INTEGER(a)) { ADDINVERS_APPLY_INTEGER(a); t=1; }
        erg += mod_longint_integer(b,a,ac);
        erg += ggt_integer_integer(ac,a,d);
        if (t==1) { ADDINVERS_APPLY_INTEGER(a); t=0; }
        FREEALL(ac);
        }
    ENDR("ggt_integer_longint");
}


INT ggt_i(i,j) INT i, j;
/* AK 010202 */
{
    INT res;
    GGT_INT_INT(i,j,res);
    return res;
}



INT ggt_integer_integer_slow(a,b,c) OP a,b,c;
{
    return ggt_integer(a,b,c);
}

INT ggt_integer_slow(a,b,c) OP a,b,c;
/* AK 021101
   faster als mit div und mod */
/* AK 261101 ggt immer positiv */
{
    INT erg = OK;
    INT t;
    OP d;

    CTO(INTEGER,"ggt_integer(1)",a);
    CTTO(LONGINT,INTEGER,"ggt_integer(2)",b);
    CTO(EMPTY,"ggt_integer(3)",c);

    if (NULLP_INTEGER(a)) 
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
    if (NEGP_INTEGER(a)) 
        erg += ADDINVERS_INTEGER(a,d);
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
    ENDR("ggt_integer");
}

INT ggt(a,b,c) OP a,b,c;
/* AK 190888 */ /* AK 280689 V1.0 */ /* AK 010290 V1.1 */
/* AK 140591 V1.2 */ /* AK 140891 V1.3 */
/* AK 030498 V2.0 */
/* AK 261101 ggt ist immer positiv */
{
    OP i,j;
    INT erg=OK,comperg;
    EOP("ggt(1)",a);
    EOP("ggt(2)",b);
    COP("ggt(3)",c);
    CE3(a,b,c,ggt);

    if  (S_O_K(a) == INTEGER)
        {
        erg+=ggt_integer(a,b,c);
        goto endr_ende;
        }
    else if (S_O_K(a) == LONGINT)
        {
        erg+=ggt_longint(a,b,c);
        goto endr_ende;
        }
    else if  ( (S_O_K(a) == MONOPOLY ) && (S_O_K(b) == MONOPOLY) )
	/* AK 170206 */
	/* only with finite field coeffs */
	{
	if (S_O_K(S_PO_K(a) ) != FF) error("ggt-monopoly: only finite field coeffs ");
	if (S_O_K(S_PO_K(b) ) != FF) error("ggt-monopoly: only finite field coeffs ");
		{ 
		OP aa = CALLOCOBJECT(); 
		OP bb = CALLOCOBJECT(); 
		t_MONOPOLY_POLYNOM(a,aa);
		t_MONOPOLY_POLYNOM(b,bb); ggt_field_polynom(aa,bb,c);
		t_POLYNOM_MONOPOLY(c,c);
		freeall(bb);
		freeall(aa);
		}
 	}
    else {
        erg += WTO("ggt(1)",a); 
        goto endr_ende;
        }
    ENDR("ggt");

}

#ifdef UNDEF
INT hoch_pre200902(a,b,c) OP a,b,c;
{
    INT erg = OK;
    EOP("hoch(1)",a);
    EOP("hoch(2)",b);
    COP("hoch(3)",c);
    CE3(a,b,c,hoch);
    switch(S_O_K(a)) {
        case INTEGER:
            erg += hoch_integer(a,b,c);
            break;
        case LONGINT:
            erg += hoch_longint(a,b,c);
            break;
        case BRUCH:
            erg += hoch_bruch(a,b,c);
            break;
        default:
            erg += hoch_default(a,b,c);
            break;
        }
    ENDR("hoch");
}
#endif

INT hoch(a,b,c) OP a,b,c ;
/* c = a^b */
/* algorithm 1.2.3 in cohen:a course in computational
   algebraic number theory */
/* AK 200902 V2.1 */
{
    INT erg = OK;
    EOP("hoch(1)",a);
    CTTO(INTEGER,LONGINT,"hoch(2)",b);
    COP("hoch(3)",a);
    CE3(a,b,c,hoch);
    {
    eins(a,c);
    if (not NULLP(b)) {
        INT f;
        OP N,z;
        N = CALLOCOBJECT();
        z = CALLOCOBJECT();
        if (NEGP(b))
            {
            ADDINVERS(b,N);
            INVERS(a,z);
            }
        else
            {
            COPY(b,N);
            COPY(a,z);
            }
        f = number_of_bits(N)-1; 
 
        CLEVER_COPY(z,c);
 
        while (1)
            {
            INT i;
            if (f == 0) break;
            else f--;
 
            square_apply(c);
 
            if (bit(N,f)) MULT_APPLY(z,c);
            }
        FREEALL2(N,z);
        }
    }
    ENDR("hoch");
}         

INT hoch_default(basis,expon,ergeb)    OP basis, ergeb, expon;
/* AK 041186 ergeb = basis ** expon */ 
/* AK 031286  ok */
/* AK 280689 V1.0 */ /* AK 160190 V1.1 */ /* AK 090891 V1.3 */
/* AK 030496 V2.0 */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"hoch_default(2)",expon);
    CTO(EMPTY,"hoch_default(1)",ergeb);

    if (NEGP(expon))
    {
        OP c=callocobject();
        erg += invers(basis,c);
        erg += addinvers_apply(expon);
        erg += hoch_default(c,expon,ergeb);
        erg += addinvers_apply(expon);
        erg += freeall(c);
        goto endr_ende;
    }
    else if (NULLP(expon))
        M_I_I(1,ergeb);
    else if (EINSP(expon))
        COPY(basis,ergeb);
    else    {
        OP n = callocobject();
        OP a = callocobject();
        COPY(expon,n);
        COPY(basis,a);
        COPY(basis,ergeb);  /* AK 290692 */
        DEC(n);  /* AK 290692 */
        while (not NULLP(n)) {
            MULT_APPLY(a,ergeb);
            DEC(n);
        }
        FREEALL2(a,n);
    };
    ENDR("hoch_default");
}


INT invers(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 070789 sonderfaelle 0 und 1 */
/* AK 081289 V1.1 */ /* AK 250391 V1.2 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("invers(1)",a);
    COP("invers(2)",b);
  
    /* no test on null , e.g. permutation */

    if (EINSP(a)) /* AK 070789 */
    {
        if (a == b) goto endr_ende;
        CLEVER_COPY(a,b);
        goto endr_ende;
    }

    CE2(a,b,invers);


    switch(S_O_K(a))
    {
#ifdef BRUCHTRUE
    case BRUCH : 
        erg += invers_bruch(a,b);
        break;
#endif /* BRUCHTRUE */

#ifdef    CYCLOTRUE
    case CYCLOTOMIC: 
        erg += invers_cyclo (a,b);
        break;
#endif /* CYCLOTRUE */

#ifdef FFTRUE
    case FF : erg += invers_ff(a,b); break;
#endif /* FFTRUE */

#ifdef GRTRUE
	case GALOISRING:
		erg += invers_galois(a,b); break;
#endif /* GRTRUE */

#ifdef LAURENTTRUE
    case LAURENT : erg += invers_laurent(a,b); break;
#endif /* LAURENTTRUE */

#ifdef MONOPOLYTRUE
    case MONOPOLY : erg += invers_monopoly(a,b); break;
#endif /* MONOPOLYTRUE */

#ifdef LONGINTTRUE
    case LONGINT : 
        erg += invers_longint(a,b);
        break;
#endif /* LONGINTTRUE */

#ifdef INTEGERTRUE
    case INTEGER :
        erg += invers_integer(a,b);
        break;
#endif /* INTEGERTRUE */    

#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case KOSTKA :
    case MATRIX :
        erg += invers_matrix(a,b);
        break;
#endif /* MATRIXTRUE */

#ifdef PERMTRUE
    case PERMUTATION :
        erg += invers_permutation(a,b);
        break;
#endif /* PERMTRUE */

#ifdef KRANZTRUE
    case KRANZ :
        erg += invers_kranz(a,b);
        break;
#endif /* KRANZTRUE */

#ifdef POLYTRUE
    case POLYNOM : /* CC */
        erg += invers_POLYNOM(a,b);
        break;

#endif  /* POLYTRUE */

#ifdef    SQRADTRUE
    case SQ_RADICAL: 
        erg += invers_sqrad (a,b);
        break;
#endif /* SQRADTRUE */

    default: 
        erg += WTO("invers(1)",a); 
        break;
    };
    ENDR("invers");
}


INT multadd_apply_default(a,b,c)  OP a,b,c;
{
	INT erg =OK;
		OP d;
		d=CALLOCOBJECT();
		MULT(a,b,d);
		ADD_APPLY(d,c);
		FREEALL(d);
	ENDR("multadd_apply_default");
}
INT multadd_apply(a,b,c) OP a,b,c;
/* c += a*b */
/* AK 170607 */
{
	INT erg =OK;
	if (
		(S_O_K(a) != S_O_K(b))
		||
		(S_O_K(c) != S_O_K(b))
		)
		{
		 multadd_apply_default(a,b,c);
		}
	else {
		switch(S_O_K(a))
		{
		case FF:
			multadd_apply_ff(a,b,c);
			break;
		default:
			multadd_apply_default(a,b,c);
			break;
		}
		}
	ENDR("multadd_apply");
}

INT mult(a,b,d) OP a,b,d;
/* AK 280689 V1.0 */ /* AK 081289 V1.1 */ /* AK 140891 V1.3 */
/* AK 070498 V2.0 */
{
    INT erg = OK;
    EOP("mult(1)",a);
    EOP("mult(2)",b);
    COP("mult(3)",d);
    CE3(a,b,d,mult);


    switch(S_O_K(a))
    {
#ifdef    MONOPOLYTRUE
    case MONOPOLY:  
        erg+=mult_monopoly (a,b,d);
        break;
#endif /* MONOPOLYTRUE */
#ifdef    MONOMTRUE
    case MONOM:  
        erg+=mult_monom (a,b,d);
        break;
#endif /* MONOMTRUE */
#ifdef    CYCLOTRUE
    case CYCLOTOMIC:  
        erg+=mult_cyclo (a,b,d);
        break;
#endif /* CYCLOTRUE */
#ifdef    REIHETRUE
    case REIHE:  
        erg+=mult_reihe(a,b,d);
        break;
#endif /* REIHETRUE */
#ifdef    FFTRUE
    case FF:  erg+=mult_ff(a,b,d); break;
#endif /* FFTRUE */
#ifdef    GRTRUE
    case GALOISRING:  erg+=mult_galois(a,b,d); break;
#endif /* GRTRUE */
#ifdef    SQRADTRUE
    case SQ_RADICAL:  
        erg+=mult_sqrad (a,b,d); break;
#endif /* SQRADTRUE */

#ifdef BRUCHTRUE
    case BRUCH :      
        erg+=mult_bruch(a,b,d); 
        break;
#endif  /* BRUCHTRUE */

#ifdef INTEGERTRUE
    case INTEGER :      
        erg+=mult_integer(a,b,d); 
        break;
#endif /* INTEGERTRUE */
#ifdef LAURENTTRUE
    case LAURENT :      
        erg+=mult_laurent(a,b,d); 
        break;
#endif /* LAURENTTRUE */
#ifdef POLYTRUE
    case POLYNOM :  
        erg+=mult_polynom(a,b,d);
        break;
#endif /* POLYTRUE */
#ifdef SCHUBERTTRUE
    case SCHUBERT :
        switch(S_O_K(b))
        {
        case BRUCH:
        case LONGINT:
        case INTEGER:  
            erg+=mult_scalar_schubert(b, a, d);
            break;
        case POLYNOM:  
            erg+=mult_schubert_polynom(a,b,d);
            break;
        case SCHUBERT:  
            erg+=mult_schubert_schubert(a,b,d);
            break;
        };
        break;
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE
    case SCHUR : 
        erg += mult_schur(a,b,d); 
        break;
    case MONOMIAL:
        erg += mult_monomial(a,b,d); 
        break;
    case POW_SYM :
        erg += mult_powsym(a,b,d); 
        break;
    case ELM_SYM :
        erg += mult_elmsym(a,b,d); 
        break;
    case HOM_SYM :  
        erg+=mult_homsym(a,b,d);
        break;
#endif  /* SCHURTRUE */
#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case KOSTKA :
    case MATRIX :
        erg+=mult_matrix(a,b,d);
        break;
#endif  /* MATRIXTRUE */
#ifdef LONGINTTRUE
    case LONGINT:    
        erg+=mult_longint(a,b,d);
        break;
#endif /* LONGINTTRUE */
#ifdef PERMTRUE
    case PERMUTATION:  
        erg+=mult_permutation(a,b,d);
        break;
#endif /* PERMTRUE */
#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case VECTOR :
        switch(S_O_K(b))
        {
#ifdef BRUCHTRUE
        case BRUCH:
#endif /* BRUCHTRUE */
        case LONGINT:
        case INTEGER:   
            erg+=mult_scalar_vector(b,a,d);
            break;
        case VECTOR:    
        case INTEGERVECTOR:    
            erg+=mult_vector_vector(a,b,d);
            break;
#ifdef MATRIXTRUE
        case MATRIX:    
            erg+=mult_vector_matrix(a,b,d);
            break;
#endif /* MATRIXTRUE  */
        default:
            printobjectkind(b);
            error("mult_vector:wrong second type");
            return ERROR;
        };
        break;
#endif /* VECTORTRUE */
#ifdef CHARTRUE
    case SYMCHAR :
        switch(S_O_K(b))

        {
        case BRUCH:
        case LONGINT:
        case INTEGER:  
            erg+=mult_scalar_symchar(b,a,d);
            break;
        case SYMCHAR:  
            erg+=mult_symchar_symchar(a,b,d);
            break;
        default:
            printobjectkind(b);
            error("mult_symchar in mult:wrong second type");
            return ERROR;                                                                     
        };
        break;
#endif /* CHARTRUE */
#ifdef KRANZTRUE
    case KRANZ :
        switch(S_O_K(b))
 
        {
        case KRANZ:
            erg+=mult_kranz_kranz(a,b,d);
            break;
        default:
            printobjectkind(b);
            error("mult_kranz in mult:wrong second type");
            return ERROR;
        };
        break; 
#endif /*KRANZTRUE */
#ifdef GRALTRUE
    case GRAL:
        erg += mult_gral(a,b,d); 
        break;
#endif

    default:   
        WTT("mult",a,b);
    }
    ENDR("mult");
}


INT scalarproduct(a,b,c) OP a,b,c;
/* AK 010888 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */
{
    INT erg=OK;
    EOP("scalarproduct",a);
    EOP("scalarproduct",b);
    CE3(a,b,c,scalarproduct);
    CTO(EMPTY,"scalarproduct(3)",c);

        
    switch(S_O_K(a))
    {

#ifdef SCHUBERTTRUE
    case SCHUBERT: 
        erg += scalarproduct_schubert(a,b,c);
        break;
#endif /* SCHURTRUE */

#ifdef SCHURTRUE
    case SCHUR : 
        erg += scalarproduct_schur(a,b,c);
        break;
#endif /* SCHURTRUE */
#ifdef MONOMIALTRUE
    case MONOMIAL : 
        erg += scalarproduct_monomial(a,b,c);
        break;
#endif /* MONOMIALTRUE */
#ifdef HOMSYMTRUE
    case HOMSYM : 
        erg += scalarproduct_homsym(a,b,c);
        break;
#endif /* HOMSYMTRUE */
#ifdef ELMSYMTRUE
    case ELMSYM : 
        erg += scalarproduct_elmsym(a,b,c);
        break;
#endif /* ELMSYMTRUE */
#ifdef POWSYMTRUE
    case POWSYM : 
        erg += scalarproduct_powsym(a,b,c);
        break;
#endif /* POWSYMTRUE */

#ifdef CHARTRUE
    case SYMCHAR : 
        erg += scalarproduct_symchar(a,b,c);
        break;
#endif /* CHARTRUE */

#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case VECTOR : 
        erg += scalarproduct_vector(a,b,c);
        break;
#endif /* VECTORTRUE */

    default:
        erg += WTT("scalarproduct",a,b);
        break;
    };
    ENDR("scalarproduct");
}


#ifdef POLYTRUE
INT vander(n,res) OP n,res;
/* AK 300588 */ /* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */
/* n and res may be equal */
{
    INT ni,i,j,erg = OK;
    OP a,b,c;

    EOP("vander",n);
    CTO(INTEGER,"vander",n);

    ni = S_I_I(n);
    m_i_i(1L,res);

    a = callocobject();
    b = callocobject();
    c = callocobject();

    for (i=2L;i<=ni;i++)
        for (j=1L;j<i;j++)
        {
            erg += m_iindex_monom(i-1,a);
            erg += m_iindex_monom(j-1,b);
            erg += sub(a,b,c);
            erg += mult_apply(c,res);
        }

    erg += freeall(a); 
    erg += freeall(b); 
    erg += freeall(c); 
    ENDR("vander");
}
#endif  /* POLYTRUE */

INT weight(a,b) OP a,b;
/* AK 280689 V1.0 */ /* AK 050390 V1.1 */
/* AK 140891 V1.3 */ /* AK 250298 V2.0 */
/* AK 131206 V3,1 */
{
    INT erg = OK;
    EOP("weight(1)",a);
    CE2(a,b,weight);

    switch(S_O_K(a))
    {

#ifdef PARTTRUE
    case AUG_PART : 
        erg+=weight_augpart(a,b);
        break;
    case PARTITION : 
        erg+=weight_partition(a,b);
        break;
#endif /* PARTTRUE */

#ifdef SKEWPARTTRUE
    case SKEWPARTITION : 
        erg+=weight_skewpartition(a,b);
        break;
#endif  /* SKEWPARTTRUE */

#ifdef TABLEAUXTRUE
    case TABLEAUX : 
        erg+=weight_tableaux(a,b); 
        break;
#endif /* TABLEAUXTRUE */

    case WORD:
    case INTEGERVECTOR:
    case VECTOR: /* number of nonzero entries */
	erg += weight_vector(a,b);
	break;

    default:
        erg += WTO("weight",a); 
        break;
    };
    ENDR("weight");
}

INT trace(a,b) OP a,b;
/* AK 131289 */ /* AK 131289 V1.1 */
/* AK 140891 V1.3 */
/* AK 250298 V2.0 */
{
    INT erg = OK;
    EOP("trace(1)",a);
    CE2(a,b,trace);

    switch (S_O_K(a)) {

#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case KOSTKA:
    case MATRIX: 
        erg += trace_matrix(a,b); break;
#endif /* MATRIXTRUE */

    default:
        erg += WTO("trace",a); break;
    };
    ENDR("trace");
}

INT det(a,b) OP a,b;
/* AK 151289 Determinante berechnung */ /* AK 151289 V1.1 */
{
    INT erg = OK;
    EOP("det",a);
    CE2(a,b,det);

    switch (S_O_K(a)) {
#ifdef MATRIXTRUE
    case KRANZTYPUS:
    case KOSTKA:
    case MATRIX: 
        erg += det_matrix(a,b);
        break;
#endif /* MATRIXTRUE */
    default:
        erg += WTO("det",a); break;
    };
    ENDR("det");
}

INT invers_apply(a) OP a;
/* AK 140591 V1.2 */ /* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("invers_apply",a);

    switch(S_O_K(a))
    {

#ifdef BRUCHTRUE
    case BRUCH :       
        erg += invers_apply_bruch(a);
        break;
#endif /* BRUCHTRUE */

#ifdef FFTRUE
    case FF :       
        erg += invers_apply_ff(a);
        break;
#endif /* FFTRUE */

#ifdef INTEGERTRUE
    case INTEGER :       
        erg += invers_apply_integer(a);
        break;
#endif /* INTEGERTRUE */

#ifdef LONGINTTRUE
    case LONGINT:
        erg += invers_apply_longint(a);
        break;
#endif /*LONGINTTRUE*/

    default: 
        {
            OP c = callocobject();
            erg += copy(a,c);
            erg += invers(c,a);
            erg += freeall(c);
        }
    }
    ENDR("invers_apply");
}

INT addinvers_apply(a) OP a;
/* AK 201289 V1.1 */ /* AK 140891 V1.3 */
/* AK 200498 V2.0 */
{
    INT erg = OK;
    EOP("addinvers_apply(1)",a);

    switch(S_O_K(a))
    {

#ifdef BRUCHTRUE
    case BRUCH :     
        erg+=addinvers_apply_bruch(a);
        break;
#endif /* BRUCHTRUE */

#ifdef    CYCLOTRUE
    case CYCLOTOMIC: 
        erg+=addinvers_apply_cyclo(a);
        break;
#endif /* CYCLOTRUE */

#ifdef    FFTRUE
    case FF: 
        erg+=addinvers_apply_ff(a); 
        break;
#endif /* FFTRUE */

#ifdef    GRTRUE
    case GALOISRING:
        erg+=addinvers_apply_galois(a);
        break;
#endif /* GRTRUE */

#ifdef    LAURENTTRUE
    case LAURENT: 
        erg+=addinvers_apply_laurent(a); 
        break;
#endif /* LAURENTTRUE */

#ifdef INTEGERTRUE
    case INTEGER :      
        erg+=addinvers_apply_integer(a);
        break;
#endif /* INTEGERTRUE */

#ifdef LONGINTTRUE
    case LONGINT :     
        erg+=addinvers_apply_longint(a);
        break;
#endif /* LONGINTTRUE */

#ifdef MONOMTRUE
    case MONOM : 
        erg+=addinvers_apply_monom(a);
        break;
#endif /* MONOMTRUE */

#ifdef    MONOPOLYTRUE
    case MONOPOLY: 
        erg+=addinvers_apply_monopoly (a);
        break;
#endif /* MONOPOLYTRUE */

#ifdef POLYTRUE
    case HOM_SYM:
        erg += addinvers_apply_homsym(a);
        break;
    case MONOMIAL:
        erg += addinvers_apply_monomial(a);
        break;
    case ELM_SYM:
        erg += addinvers_apply_elmsym(a);
        break;
    case POW_SYM:
        erg += addinvers_apply_powsym(a);
        break;
    case SCHUR:
        erg += addinvers_apply_schur(a);
        break;

    case SCHUBERT:
    case GRAL:
    case POLYNOM :     
        erg+=addinvers_apply_polynom(a);
        break;
#endif /* POLYTRUE */

#ifdef    SQRADTRUE
    case SQ_RADICAL: 
        erg+=addinvers_apply_sqrad (a);
        break;
#endif /* SQRADTRUE */

#ifdef CHARTRUE
    case SYMCHAR :     
        erg+=addinvers_apply_symchar(a);
        break;
#endif /* CHARTRUE */

#ifdef VECTORTRUE
    case INTEGERVECTOR:
    case VECTOR :      
        erg+=addinvers_apply_vector(a);
        break;

    case HASHTABLE:
        erg+=addinvers_apply_hashtable(a);
        break;
#endif /* VECTORTRUE */

    default: 
        erg += WTO("addinvers_apply",a); 
        break;
    };
    ENDR("addinvers_apply");
}

INT mult_apply_default (a,b) OP a,b;
/* hilfsroutine tut normales mult aufrufen */
/* AK 091092 */
{
    INT erg=OK;
    OP c;
    c = CALLOCOBJECT();
    *c = *b;
    C_O_K(b,EMPTY);
    erg += mult(a,c,b);
    FREEALL(c);
    ENDR("mult_apply_default");
}

INT mult_apply(a,b) OP a,b;
/* b := a * b */ 
/* AK 201289 V1.1 */ 
/* AK 190291 V1.2 */
/* AK 140891 V1.3 */
{
    INT erg = OK;
    EOP("mult_apply(1)",a);
    EOP("mult_apply(2)",b);
    CE2A(a,b,mult_apply);

/* switching according to the first type */

    switch(S_O_K(a)) {
#ifdef BRUCHTRUE
    case BRUCH: 
        erg += mult_apply_bruch(a,b);
        goto ende;
#endif /* BRUCHTRUE */
#ifdef FFTRUE
    case FF: 
        erg += mult_apply_ff(a,b);
        goto ende;
#endif /* FFTRUE */
#ifdef GRTRUE
    case GALOISRING:
	erg += mult_apply_default(a,b);
	goto ende;
#endif /* GRTRUE */
#ifdef GRALTRUE
    case GRAL: 
        erg += mult_apply_gral(a,b);
        goto ende;
#endif /* GRALTRUE */
    case INTEGER: 
        erg += mult_apply_integer(a,b); 
        goto ende;
#ifdef LONGINTTRUE
    case LONGINT: 
        erg += mult_apply_longint(a,b); 
        goto ende;
#endif /* LONGINTTRUE */
#ifdef MATRIXTRUE
    case MATRIX: 
        erg += mult_apply_matrix(a,b); 
        goto ende;
#endif /* MATRIXTRUE */
#ifdef MONOMTRUE
    case MONOM: 
        erg += mult_apply_monom(a,b); 
        goto ende;
#endif /* MONOMTRUE */
#ifdef PERMTRUE
    case PERMUTATION: 
        erg += mult_apply_permutation(a,b); 
        goto ende;
#endif /* PERMTRUE */
#ifdef POLYTRUE
    case POLYNOM: 
        erg += mult_apply_polynom(a,b); 
        goto ende;
#endif /* POLYTRUE */
#ifdef REIHETRUE
    case REIHE: 
        erg += mult_apply_reihe(a,b); 
        goto ende;
#endif /* REIHETRUE */
#ifdef SCHUBERTTRUE
    case SCHUBERT: 
        erg += mult_apply_default(a,b); 
        goto ende;
#endif /* SCHUBERTTRUE */
#ifdef SCHURTRUE
    case HOM_SYM: 
        erg += mult_apply_homsym(a,b); 
        goto ende;
    case POW_SYM:
        erg += mult_apply_powsym(a,b); 
        goto ende;
    case ELM_SYM:
        erg += mult_apply_elmsym(a,b); 
        goto ende;
    case MONOMIAL:
        erg += mult_apply_monomial(a,b); 
        goto ende;
    case SCHUR: 
        erg += mult_apply_schur(a,b); 
        goto ende;
#endif /* SCHURTRUE */
#ifdef CHARTRUE
    case SYMCHAR: 
        erg += mult_apply_symchar(a,b); 
        goto ende;
#endif /* CHARTRUE */
#ifdef    MONOPOLYTRUE
    case MONOPOLY: 
        erg +=  mult_apply_monopoly (a,b); 
        goto ende;
#endif /* MONOPOLYTRUE */
#ifdef    CYCLOTRUE
    case CYCLOTOMIC: 
        erg +=  mult_apply_cyclo (a,b); 
        goto ende;
#endif /* CYCLOTRUE */
#ifdef    SQRADTRUE
    case SQ_RADICAL: 
        erg +=  mult_apply_sqrad (a,b); 
        goto ende;
#endif /* SQRADTRUE */
#ifdef VECTORTRUE
    case VECTOR: 
    case INTEGERVECTOR:    
        erg += mult_apply_vector(a,b);
        goto ende;
#endif /* VECTORTRUE */
    default: 
        WTT("mult_apply(1,2)",a,b);
        goto ende;
    }
ende:
    ENDR("mult_apply");
}

INT half_apply(a) OP a;
/* AK 021294 */
{
    INT erg = OK;
    EOP("half_apply(1)",a);

    switch S_O_K(a) {
        case INTEGER: 
            M_I_I(S_I_I(a)/(INT)2, a);
            break;
        case LONGINT: 
            erg += half_apply_longint(a);
            break;
        default: {
            OP c;
            c = CALLOCOBJECT();
            *c = *a;
            C_O_K(a,EMPTY);
            erg += ganzdiv(c,cons_zwei,a);
            FREEALL(c);
            } ;
            break;
        }

    ENDR("half_apply");
}
INT double_apply_default(a) OP a;
/* AK 0102002 */
{
    INT erg = OK;
    OP c;

    c= CALLOCOBJECT();
    COPY(a,c);
    ADD_APPLY(c,a);
    FREEALL(c);
  
    ENDR("double_apply_default");
}

INT double_apply(a) OP a;
/* AK 010692 */
{
    INT erg = OK;
    EOP("double_apply(1)",a);

    switch S_O_K(a) {
        case INTEGER: 
            if ((S_I_I(a) > -1073741824) && /* 2^30 */
               (S_I_I(a) < 1073741824) )
                {
                M_I_I( (S_I_I(a)<<1),a);
                }
            else
                {
                erg += t_int_longint(a,a);
                erg += double_apply_longint(a);
                }
            goto ende;
        case LONGINT:
            erg += double_apply_longint(a);
            goto ende;
        case BRUCH: 
            double_apply(S_B_O(a));
            erg += kuerzen(a);
            goto ende;
        default:
            erg += double_apply_default(a);
            goto ende;
    }

ende:
    ENDR("double_apply");
}

INT add_apply(a,b) OP a,b;
/* b = a + b */ /* AK 120390 V1.1 */ /* AK 140591 V1.2 */
/* AK 140891 V1.3 */
/* AK 270298 V2.0 */
{
    INT erg = OK;
    EOP("add_apply(1)",a);
    EOP("add_apply(2)",b);
    if (a == b) 
        {
        erg += double_apply(a);
        goto endr_ende;
        }

/* switching according to the first type */
    switch(S_O_K(a)) 
        {
#ifdef BRUCHTRUE
        case BRUCH: 
            erg += add_apply_bruch(a,b);
            break;
#endif /* BRUCHTRUE */

#ifdef FFTRUE
        case FF: 
            erg += add_apply_ff(a,b);
            break;
#endif /* FFTRUE */

#ifdef POLYTRUE
        case GRAL: 
            erg += add_apply_gral(a,b) ; 
            break;
#endif /* POLYTRUE */

        case INTEGER: 
            erg += add_apply_integer(a,b);
            break;

#ifdef LONGINTTRUE
        case LONGINT: 
            erg += add_apply_longint(a,b);
            break;
#endif /* LONGINTTRUE */

#ifdef MATRIXTRUE
        case KRANZTYPUS:
        case MATRIX: 
            erg += add_apply_matrix(a,b);
            break;
#endif /* MATRIXTRUE */

#ifdef REIHETRUE
        case REIHE: 
            erg += add_apply_reihe(a,b);
            break;
#endif /* REIHETRUE */

#ifdef SCHUBERTTRUE
        case SCHUBERT:  
            erg += add_apply_schubert(a,b);
            break;
#endif /* SCHUBERTTRUE */

#ifdef SCHURTRUE
        case POW_SYM:
        case MONOMIAL:
        case HOM_SYM:
        case ELM_SYM:
        case SCHUR:  
            erg += add_apply_symfunc(a,b);
            break;
#endif /* SCHURTRUE */

#ifdef CHARTRUE
        case SYMCHAR:  
            erg += add_apply_symchar(a,b);
            break;
#endif /* CHARTRUE */

#ifdef POLYTRUE
        case POLYNOM: 
            erg += add_apply_polynom(a,b);
            break;
#endif /* POLYTRUE */

        case VECTOR: 
            erg += add_apply_vector(a,b);
            break;
        case INTEGERVECTOR:    
            erg += add_apply_integervector(a,b);
            break;

#ifdef    MONOPOLYTRUE
        case MONOPOLY: 
            erg += add_apply_monopoly (a,b);
            break;
#endif /* MONOPOLYTRUE */

#ifdef    CYCLOTRUE
        case CYCLOTOMIC: 
            erg += add_apply_cyclo (a,b);
            break;
#endif /* CYCLOTRUE */

#ifdef    SQRADTRUE
        case SQ_RADICAL: 
            erg += add_apply_sqrad (a,b);
            break;
#endif /* SQRADTRUE */

        default:  
            erg += add_apply_default(a,b);
            break;
        }
ende:
    ENDR("add_apply");
}

INT add_apply_default(a,b) OP a,b;
/* AK 040302 */
{
    INT erg = OK;
    OP c;
    EOP("add_apply_default(1)",a);
    EOP("add_apply_default(2)",b);
    c = CALLOCOBJECT();
    SWAP(b,c);
    ADD(a,c,b);
    FREEALL(c);
    ENDR("add_apply_default");
}


INT multinom_small(a,b,c) OP a,b,c;
/* AK 120901 */
{
    INT erg = OK,i;
    switch(S_I_I(a)) {
        case 1:     M_I_I(1L,c);break;
        case 2:     M_I_I(2L,c);break;
        case 3:     M_I_I(6L,c);break;
        case 4:     M_I_I(24L,c);break;
        case 5:     M_I_I(120L,c);break;
        case 6:     M_I_I(720L,c);break;
        case 7:     M_I_I(5040L,c);break;
        case 8:     M_I_I(40320L,c);break;
        case 9:     M_I_I(362880,c);break;
        case 10:     M_I_I(3628800L,c);break;
        case 11:     M_I_I(39916800L,c);break;
        case 12:     M_I_I(479001600L,c);break;
        default: error("wrong int value in multinom_small");goto endr_ende;
        }
    for (i=0;i<S_V_LI(b);i++)
        switch ( S_V_II(b,i) ) {
        case 0: break;
        case 1: break;
        case 2:     M_I_I(S_I_I(c)/2L,c);break;
        case 3:     M_I_I(S_I_I(c)/6L,c);break;
        case 4:     M_I_I(S_I_I(c)/24L,c);break;
        case 5:     M_I_I(S_I_I(c)/120L,c);break;
        case 6:     M_I_I(S_I_I(c)/720L,c);break;
        case 7:     M_I_I(S_I_I(c)/5040L,c);break;
        case 8:     M_I_I(S_I_I(c)/40320L,c);break;
        case 9:     M_I_I(S_I_I(c)/362880,c);break;
        case 10:     M_I_I(S_I_I(c)/3628800L,c);break;
        case 11:     M_I_I(S_I_I(c)/39916800L,c);break;
        case 12:     M_I_I(S_I_I(c)/479001600L,c);break;
        default: error("wrong int value in multinom_small");goto endr_ende;
        }
    ENDR("multinom_small");
}

INT multinom(a,b,c) OP a,b,c;
/* AK  040892 */
{
    OP d;
    INT i,erg = OK;
    CTO(INTEGER,"multinom(1)",a);
    CTTO(VECTOR,INTEGERVECTOR,"multinom(2)",b);

    if (S_I_I(a) < 1) {
	error("multinom  with negative value");
	goto endr_ende;
        }


    if (S_O_K(b) != INTEGERVECTOR)
    for (i=0L;i<S_V_LI(b);i++)
        if (S_O_K(S_V_I(b,i)) != INTEGER)
            {
            error("multinom:no integer vector");
            goto endr_ende;
            }

    CE3(a,b,c,multinom);

    if (S_I_I(a) <= 12 ) {
        erg += multinom_small(a,b,c);
        goto endr_ende;
        }
    M_I_I(1L,c);
    d = callocobject();
    for (i=0L;i<S_V_LI(b);i++)
    {
        erg += fakul(S_V_I(b,i),d);
        MULT_APPLY(d,c);
    }
    erg += invers_apply(c);
    erg += fakul(a,d);
    MULT_APPLY(d,c);
    FREEALL(d);
    ENDR("multinom");
}


static INT moebius_rekurs(n) OP n;
/* DL 030593 */
{
    INT erg;
    OP i, h;

    if (nullp(n))
        return 0L;

    if (einsp(n))
        return 1L;

    i = callocobject();
    h = callocobject();
    for (m_i_i(2L, i); mod(n, i, h), !nullp(h); inc(i));
    /* Koennte evtl. durch schnellere Version ersetzt werden, die
    nur Primzahlen durchlaeuft! */

    if (eq(i, n))
    {
        erg = -1L;
        goto fertig;
    }

    mult(i, i, h);
    mod(n, h, h);
    if (nullp(h))
    {
        erg = 0L;
        goto fertig;
    }

    div(n, i, h);
    erg = -moebius_rekurs(h);

fertig:
    freeall(h);
    freeall(i);
    return erg;
}


INT moebius(n, my) OP n, my;
/* DL 030593 */
{
    INT erg = OK;
    if (n == NULL)
        {
        erg += error("moebius: input parameter == NULL");
        goto endr_ende;
        }

    if (my == NULL)
        {
        erg += error("moebius: output parameter == NULL");
        goto endr_ende;
        }

    if (S_O_K(n) != INTEGER && S_O_K(n) != LONGINT)
        {
        WTO("moebius", n);
        goto endr_ende;
        }

    if (negp(n))
        {
        erg += error("moebius: input parameter negative");
        goto endr_ende;
        }

    erg += m_i_i(moebius_rekurs(n), my);
    ENDR("moebius");
}

INT square_apply(a) OP a;
/* a = a^2 */
/* AK 271101 */
{
    INT erg = OK;
    EOP("square_apply(1)",a);
    if (S_O_K(a) == INTEGER)
        erg += square_apply_integer(a);
    else if (S_O_K(a) == LONGINT)
        erg += square_apply_longint(a);
    else 
        {
        OP b;
        b = CALLOCOBJECT();
        COPY(a,b);
        MULT_APPLY(b,a);
        FREEALL(b);
        }

    ENDR("square_apply");
}

 
INT bin_ggt(a,b,c) OP a,b,c;
/* Knuth band 2 2. aufl. p.321 */
{
    OP k,u,v,t;
    INT erg = OK;
    CTTO(LONGINT,INTEGER,"bin_ggt(1)",a);
    CTTO(LONGINT,INTEGER,"bin_ggt(2)",b);

    k = CALLOCOBJECT();
    u = CALLOCOBJECT();
    v = CALLOCOBJECT();
    t = CALLOCOBJECT();

    COPY(a,u);
    COPY(b,v);
    if (NEGP(u))
        {
        ADDINVERS_APPLY(u);
        }
    if (NEGP(v))
        {
        ADDINVERS_APPLY(v);
        }
    M_I_I(0,k);

    b1:
    if (odd(u)) goto b2;
    if (odd(v)) goto b2;
    erg += half_apply(u);
    erg += half_apply(v);
    INC_INTEGER(k);
    goto b1;
    b2:
    if (odd(u)) {
        ADDINVERS(v,t);
        goto b4;}
    else
        COPY(u,t);
    b3:
    erg += half_apply(t);
    b4:
    if (even(t)) goto b3;
    /* b5: */
    if (POSP(t))
        {
        FREESELF(u);
        COPY(t,u);
        ADDINVERS_APPLY(v);
        ADD_APPLY(v,t);
        ADDINVERS_APPLY(v);
        }
    else     {
        ADDINVERS_APPLY(t);
        FREESELF(v);
        COPY(t,v);
        ADD_APPLY(u,t);
        }
    /* b6: */
    if (not NULLP(t)) goto b3;
 
    if (not NULLP(k)) {
        erg += hoch(cons_zwei,k,c);
        MULT_APPLY(u,c);
        }
    else {
        FREESELF(c);
        SWAP(u,c);
        }
    FREEALL(u);
    FREEALL(t);
    FREEALL(v);
    FREEALL(k);
    ENDR("bin_ggt");
}



#ifdef UNDEF
INT extended_ggt(a,b,c,d,e) OP a,b,c,d,e;
/* c = ggt = da + eb */
/* AK 051294 */
/* Kn Bd2 p.325 */
{
    INT erg = OK;
    OP v,u,t;
    OP q;
    EOP("extended_ggt(1)",a);
    EOP("extended_ggt(2)",b);
    COP("extended_ggt(3)",c);
    COP("extended_ggt(4)",d);
    COP("extended_ggt(5)",e);
    u = callocobject();
    v = callocobject();
    t = callocobject();
    q = callocobject();
    erg += m_il_v(3L,v);
    erg += m_il_v(3L,t);
    erg += m_il_v(3L,u);
    erg += m_i_i(1L,S_V_I(u,0L)); 
    erg += m_i_i(0L,S_V_I(u,1L));
    erg += copy(a,S_V_I(u,2L));
    erg += m_i_i(0L,S_V_I(v,0L));
    erg += m_i_i(1L,S_V_I(v,1L));
    erg += copy(b,S_V_I(v,2L));
x2:
    if (nullp(S_V_I(v,2L)))
        goto ende;
    erg += ganzdiv(S_V_I(u,2L),S_V_I(v,2L),q);
    erg += mult(q,v,q);
    erg += sub(u,q,t);
    erg += copy(v,u);
    erg += copy(t,v);
    
    goto x2;
ende:
    erg += copy(S_V_I(u,0L),d);
    erg += copy(S_V_I(u,1L),e);
    erg += copy(S_V_I(u,2L),c);
    erg += freeall(q);
    erg += freeall(v);
    erg += freeall(t);
    erg += freeall(u);
    ENDR("extended_ggt");
}
#endif

/* extended euklid algorithm */
INT gcd_ex(a,b,c,d,e) OP a,b,c,d,e;
/* AK 020703 */
/* c = da+be ; c = gcd(a,b) */
{
    INT erg = OK;
    CTTO(INTEGER,LONGINT,"gcd_ex(1)",a);
    CTTO(INTEGER,LONGINT,"gcd_ex(2)",b);
    if ((a == c) || (a==d) || (a==e))
        {
        OP v;
        v=CALLOCOBJECT(); SWAP(a,v);
        erg += gcd_ex(v,b,c,d,e);
        FREEALL(v); goto endr_ende;
        }
    if ((b == c) || (b==d) || (b==e))
        {
        OP v;
        v=CALLOCOBJECT(); SWAP(b,v);
        erg += gcd_ex(a,v,c,d,e);
        FREEALL(v); goto endr_ende;
        }
    
    FREESELF(c);
    FREESELF(d);
    FREESELF(e);
    if (NULLP(a))
        {
        COPY(b,c);
        M_I_I(0,d);
        M_I_I(1,e);
        }
    else if (NULLP(b))
        {
        COPY(a,c);
        M_I_I(1,d);
        M_I_I(0,e);
        }
    else if (NEGP(a))
        {
        ADDINVERS_APPLY(a);
        erg += gcd_ex(a,b,c,d,e);
        ADDINVERS_APPLY(a);
        ADDINVERS_APPLY(c);
        ADDINVERS_APPLY(d);
        ADDINVERS_APPLY(e);
        }
    else if (NEGP(b))
        {
        ADDINVERS_APPLY(b);
        erg += gcd_ex(a,b,c,d,e);
        ADDINVERS_APPLY(b);
        ADDINVERS_APPLY(c);
        ADDINVERS_APPLY(d);
        ADDINVERS_APPLY(e);
        }
    else 
        {
        OP v1,v2;
        OP q,r;
        INT i;
        CALLOCOBJECT4(v1,v2,q,r);
    /*init*/
        m_il_v(3,v1);
        m_il_v(3,v2);
        COPY(a,S_V_I(v1,0));M_I_I(1,S_V_I(v1,1));M_I_I(0,S_V_I(v1,2));
        COPY(b,S_V_I(v2,0));M_I_I(1,S_V_I(v2,2));M_I_I(0,S_V_I(v2,1));
    
    do {
        if (LT(S_V_I(v1,0),S_V_I(v2,0))) SWAP(v1,v2);
    
        quores(S_V_I(v1,0),S_V_I(v2,0),q,r);
        if (NULLP(r)) {
            SWAP(c,S_V_I(v2,0));
            SWAP(d,S_V_I(v2,1));
            SWAP(e,S_V_I(v2,2));
            goto ende;
            }
        ADDINVERS_APPLY(q);
        for (i=0;i<3;i++) 
            { 
            FREESELF(r);
            MULT(q,S_V_I(v2,i),r);
            ADD_APPLY(r,S_V_I(v1,i)); 
            }
        } while(1); 
        
    ende:
        FREEALL4(q,r,v1,v2);
        }
    
    ENDR("gcd_ex");
}
