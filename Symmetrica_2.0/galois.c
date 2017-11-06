#include "def.h"
#include "macro.h"


INT all_points_phg();

INT scan_galois(OP v)
{
	OP d=callocobject();
	INT i,erg=OK;
	printf("degree:");scan(INTEGER,d);
	erg += m_il_v(S_I_I(d)+2,v); C_O_K(v,GALOISRING);
	erg += copy(d,S_V_I(v,0));
	printf("characteristic:");scan(INTEGER,S_V_I(v,1));
	for (i=0;i<S_I_I(d);i++)
		{
		erg += scan(INTEGER,S_V_I(v,i+2));
		}
	erg += freeall(d);
	ENDR("scan_galois");
}

INT add_galois(OP p1,OP p2, OP p3) //p3 = p2+p1
{
	INT erg =OK,i;
	// funktioniert auch mit p1=p2.....

	copy(p1,p3);
	for (i=2;i<S_V_LI(p3);i++)
		{
		M_I_I((S_V_II(p1,i)+S_V_II(p2,i))%S_GR_CI(p3), S_V_I(p3,i)) ;
		}
	
	ENDR("add_galois");
}

INT t_galois_polynom(OP g, OP p)
{
	INT i,erg=OK;
	OP z;
	init(MONOPOLY,p);
	z=p;
	for (i=2;i<S_V_LI(g);i++)
		{
		OP mo;
		mo = callocobject();
		b_sk_mo(callocobject(),callocobject(),mo);
		C_L_S(z,mo);
		M_I_I(S_V_II(g,i),S_PO_K(z));
		M_I_I(i-2,S_PO_S(z));
		if (i+1  <S_V_LI(g)) { C_L_N(z,callocobject()); z=S_L_N(z); init(MONOPOLY,z); }
		}
	ENDR("t_galois_polynom");
}

static OP mgg_c=NULL; //charakteristik zu multiplikationstafel
static OP mgg_d=NULL; // degree zu multiplikationstafel
static OP mgg_mt=NULL; //multiplikationstafel
static OP mgg_pl=NULL; //irred polynom
static INT mgg_change_counter; // count the new entries in the mult table
INT get_galois_irred(OP g, OP ip) // irreduzible zu galois ring
{
	INT erg =OK;
	OP v;
	if (
		(S_I_I(mgg_c)==S_GR_CI(g))
		&&
		(S_I_I(mgg_d)==S_GR_DI(g))
		&&
		(not EMPTYP(mgg_pl))
	   ) {
		copy(mgg_pl,ip); 
		goto endr_ende;
	     }
	v=callocobject();
	factorize(S_GR_C(g),v);
	get_ff_irred(S_V_I(v,0) ,S_GR_D(g),ip);
	copy(S_GR_C(g),mgg_c);
	copy(S_GR_D(g),mgg_d);
	copy(ip,mgg_pl);
	freeall(v);
	ENDR("get_galois_irred");
}

INT t_polynom_galois(OP p ,INT c, INT d, OP g)
{
	INT erg =OK,i=2;
	OP z=p;
	m_il_nv(d+2,g); C_O_K(g,GALOISRING);
	m_i_i(d,S_V_I(g,0));
	m_i_i(c,S_V_I(g,1));

	if (S_L_S(z) == NULL) goto endr_ende;
	
	while (z!=NULL)
		{
		M_I_I(  S_I_I(S_PO_K(z)),
			S_V_I(g,2+S_I_I(S_PO_S(z)) )
                     );
		z = S_L_N(z);
		}
	ENDR("t_polynom_galois");
}

INT init_galois_global( OP charac, OP deg )
{
	INT erg =OK;
	if ((S_I_I(mgg_c)==S_I_I(charac)) && (S_I_I(mgg_d)==S_I_I(deg))) return OK;
	if (S_I_I(mgg_c) != 0) // previously different galois ring
		{
		// store mult table
		if (mgg_change_counter>0)
			store_result_2(charac,deg,"galois_mult",mgg_mt);
		}
	freeself(mgg_mt);
	// load mult table

	check_result_2(charac,deg,"galois_mult",mgg_mt);

	if (emptyp(mgg_mt)) // first time
		{
		OP h=callocobject();
		hoch(charac,deg,h);
		if (S_I_I(h) <= 256) // only table in small cases
		m_lh_m(h,h,mgg_mt);
		freeall(h);
		}
	copy(charac,mgg_c);
	copy(deg,mgg_d);
	mgg_change_counter=0;
	ENDR("init_galois_global");
}


INT galois_anfang()
{
	INT erg =OK;
	CALLOCOBJECT4(mgg_c,mgg_d,mgg_mt,mgg_pl);
	M_I_I(0,mgg_c);
	M_I_I(0,mgg_d);
	mgg_change_counter=0;
	ENDR("galois_anfang");
}
INT galois_ende()
{
	INT erg =OK;
	if (S_I_I(mgg_c) != 0) // previously different galois ring
		{
		// store mult table
		if (mgg_change_counter>0)
		S2R(mgg_c,mgg_d,"galois_mult",mgg_mt);
		}
	FREEALL4(mgg_c,mgg_d,mgg_mt,mgg_pl);
	ENDR("galois_ende");
}
INT index_galois(OP g)
// index of galois ring element
{
	INT d=S_GR_DI(g);
	INT c=S_GR_CI(g);
	INT res=0,i,m;
	for (i=0,m=1;i<d;i++,m*=c)
		res += S_V_II(g,2+i)*m;
	return res;
}

INT mult_galois_galois(OP p1, OP p2, OP p3)
{
	INT erg = OK,p1i,p2i;
	CTO(GALOISRING,"mult_galois(1)",p1);
	CTO(GALOISRING,"mult_galois(2)",p2);
	SYMCHECK(S_GR_CI(p1)!=S_GR_CI(p2),"mult_galois_galois:different characteristics");
	SYMCHECK(S_GR_DI(p1)!=S_GR_DI(p2),"mult_galois_galois:different degrees");
	{
	OP poly1,poly2,poly3,poly4,irred,diverg;
	if (S_GR_DI(p1)==1) { 
		copy(p1,p3); 
		M_I_I((S_V_II(p1,2)*S_V_II(p2,2))%S_GR_CI(p1), S_V_I(p3,2));
		goto endr_ende;
		}
	if (
		(S_GR_CI(p1)!=S_I_I(mgg_c))  ||      (S_GR_DI(p1)!=S_I_I(mgg_d))
	   )     
		init_galois_global(S_GR_C(p1),S_GR_D(p1)); // initialize irred polynomial and mult_table

	if (not EMPTYP(mgg_mt)) // check if result available 
		{
		p1i=index_galois(p1);
		p2i=index_galois(p2);
		if (p1i >= S_M_HI(mgg_mt)) error("mult_galois_galois:I1");
		if (p2i >= S_M_HI(mgg_mt)) error("mult_galois_galois:I2");
		if (not EMPTYP(S_M_IJ(mgg_mt,p1i,p2i))) // result of multiplicazion is known
			{
			copy(S_M_IJ(mgg_mt,p1i,p2i),p3);
			goto endr_ende;
			}
		}

	CALLOCOBJECT6(poly1,poly2,poly3,poly4,irred,diverg);
	t_galois_polynom(p1,poly1); 
	t_galois_polynom(p2,poly2);
	mult(poly1,poly2,poly3);
	mod(poly3,S_GR_C(p1),poly3);
	get_galois_irred(p1,irred);
	quores(poly3,irred,diverg,poly4);
	mod(poly4,S_GR_C(p1),poly4);
	t_polynom_galois(poly4,S_GR_CI(p1),S_GR_DI(p1),p3); 
	FREEALL6(poly1,poly2,poly3,poly4,irred,diverg);

	if (not EMPTYP(mgg_mt)) // check if result available 
		{
		mgg_change_counter++;
		copy(p3,S_M_IJ(mgg_mt,p1i,p2i)); 
		}

	}
	ENDR("mult_galois");
}

INT mult_galois(OP a, OP b, OP c)
{
	INT erg = OK;
	switch (S_O_K(b)) {
		case GALOISRING:
			erg += mult_galois_galois(a,b,c);
			break;
		case VECTOR:
			{
			INT i;
			copy(b,c);
			for (i=0;i<S_V_LI(c);i++)
				erg += mult_galois(a,S_V_I(b,i),S_V_I(c,i));
			}
			break;
		default:
			printobjectkind(b);
			error("mult_galois(2): wrong second type");
			erg = ERROR;
		}
	ENDR("mult_galois");
}

INT unitp_galois(OP g)
{
	INT j,erg =OK;
	for (j=2;j<S_V_LI(g);j++)
		{
		if (ggt_i(S_V_II(g,j), S_GR_CI(g)) == 1) return TRUE;
		}
	return FALSE;
	ENDR("unitp_galois");
}

INT nullp_galois(OP g)
/* AK 131206 V3.1 */
{
	INT erg = OK;
	INT i;
	for (i=2;i<S_V_LI(g);i++)
		if (S_V_II(g,i) != 0) return FALSE;
	return TRUE;
	ENDR("nullp_galois");
}

INT null_galois(OP a,OP b)
{
	INT erg =OK,i;
	copy(a,b);
	for (i=2;i<S_V_LI(b);i++) M_I_I(0,S_V_I(b,i));
	ENDR("null_galois");
}

INT einsp_galois(OP g)
{
        INT erg = OK;
        INT i;
	if (S_V_II(g,2) != 1) return FALSE;
	for (i=3;i<S_V_LI(g);i++)
                if (S_V_II(g,i) != 0) return FALSE;
        return TRUE;
        ENDR("einsp_galois");
}

INT first_gr_given_c_d(OP c, OP d, OP gr)
{
	INT erg =OK;
	m_il_nv(S_I_I(d)+2,gr); C_O_K(gr,GALOISRING);
	copy(d,S_V_I(gr,0));
	copy(c,S_V_I(gr,1));
	ENDR("first_gr_given_c_d");
}

INT null_gr_given_c_d(OP c, OP d, OP gr)
{
	return first_gr_given_c_d(c,d,gr);
}

INT eins_gr_given_c_d(OP c, OP d, OP gr)
{
	INT erg = OK;
        first_gr_given_c_d(c,d,gr);
	m_i_i(1,S_V_I(gr,2));
	ENDR("eins_gr_given_c_d");
}

INT eins_galois(OP a,OP b)
{
	INT erg = OK;
	if (a==b)
		{
		INT i;
		M_I_I(1,S_V_I(b,2));
		for (i=3;i<S_V_LI(b);i++) M_I_I(0,S_V_I(b,i));
		}
	else
		erg += eins_gr_given_c_d(S_GR_C(a),S_GR_D(a),b);
	ENDR("eins_galois");
}

INT invers_galois(a,b) OP a,b;
{
	INT erg = OK;
	CE2(a,b,invers_galois);
	{
	OP c;
	c=CALLOCOBJECT();
	copy(a,c);
	copy(a,b);
	while (! einsp_galois(c)) 
		{
		SWAP(b,c);
		mult_galois(a,b,c);
		}
	FREEALL(c);
	}
	ENDR("invers_galois");
}

INT addinvers_apply_galois(OP a)
/* AK 200307 */
{
	INT erg =OK,i,ai;
	CTO(GALOISRING,"addinvers_apply_galois(1)",a);
	for (i=2;i<S_V_LI(a);i++)
		{
		if (S_V_II(a,i)!=0)
			{
			ai = S_GR_CI(a)-S_V_II(a,i);
			M_I_I(ai,S_V_I(a,i));
			}
		}
	ENDR("addinvers_apply_galois");
}

INT random_gr_given_c_d(c,d,b) OP c,d; OP b;
{
    INT erg = OK;
    CTO(INTEGER,"random_gr_given_c_d(1)",c);
    CTO(INTEGER,"random_gr_given_c_d(2)",d);
    SYMCHECK(prime_power_p(c) ==FALSE,"random_gr_given_c_d:c no prime power");
    {	
    INT i;
    m_il_v(S_I_I(d)+2,b); C_O_K(b,GALOISRING);
    m_i_i(S_I_I(d),S_V_I(b,0));
    m_i_i(S_I_I(c),S_V_I(b,1));
    for (i=2;i<S_V_LI(b);i++)
	m_i_i(rand()%S_I_I(c),S_V_I(b,i));
    }
    ENDR("random_gr_given_c_d");
}



INT next_apply_gr(OP gr1)
/* AK 150307 */
{
	INT erg =OK,i,j,c;
	CTO(GALOISRING,"next_apply_gr(1)",gr1);
	c=S_V_II(gr1,1);
        for (i=S_V_LI(gr1)-1; i>=2;i--)
                if (S_V_II(gr1,i) < c-1) {
                        INC_INTEGER(S_V_I(gr1,i));
                        for (j=i+1;j<S_V_LI(gr1);j++) M_I_I(0,S_V_I(gr1,j));
                        return OK;
                        }
        return LAST_FF;

	ENDR("next_apply_gr");
}

INT next_gr(OP gr1, OP gr2)
{
	INT erg =OK,i,j,c;
	CTO(GALOISRING,"next_gr(1)",gr1);
	if (gr1!=gr2) copy(gr1,gr2); 
	return next_apply_gr(gr2);
/*
	c=S_V_II(gr2,1);
	for (i=S_V_LI(gr2)-1; i>=2;i--)
		if (S_V_II(gr2,i) < c-1) { 
			INC_INTEGER(S_V_I(gr2,i));
			for (j=i+1;j<S_V_LI(gr2);j++) M_I_I(0,S_V_I(gr2,j));
			return OK;
			}
	return LAST_FF;
*/
	ENDR("next_gr");
}


INT vectorofzerodivisors_galois(OP c, OP d, OP v)
/* vector with all non unit elements */
{
	INT erg =OK;
	OP sl=callocobject();
	m_il_v(0,v);
	first_gr_given_c_d(c,d,sl);
	do {
		if (! unitp_galois(sl)) { inc(v); copy(sl,S_V_I(v,S_V_LI(v)-1)); }
		} while(next_gr(sl,sl)!=LAST_FF);
	ENDR("vectorofzerodivisors_galois");
}


INT random_subgroup_glk_grcd_smaller_k(k,c,d,a) OP k,c,d,a;
/* erzeuger fuer kleinere glnk-1 */
{
    INT erg = OK;
    CTO(INTEGER,"random_subgroup_glk_grcd_smaller_k(1)",k);
    SYMCHECK(S_I_I(k)<1,"random_subgroup_glk_grcd_smaller_k(1): k<1");
    SYMCHECK(S_I_I(d)<1,"random_subgroup_glk_grcd_smaller_k(3): d<1");
    SYMCHECK(prime_power_p(c)==FALSE,"random_subgroup_glk_grcd_smaller_k(2): no prime power");
    {
    INT i,j;
    if (S_I_I(k)<=2)
        erg += random_subgroup_glk_grcd_cyclic(k,c,d,a);
    else
        {
        DEC(k);
        erg += random_subgroup_glk_grcd(k,c,d,a);
        for (i=0;i<S_V_LI(a);i++)
            {
            OP mat;
            mat = S_V_I(a,i);
            erg += inc(mat);
            erg += eins_gr_given_c_d(c,d,S_M_IJ(mat,S_M_HI(mat)-1,S_M_LI(mat)-1));
            for (j=0;j<S_M_HI(mat)-1;j++)
                {
                erg += null_gr_given_c_d(c,d,S_M_IJ(mat,j,S_M_LI(mat)-1));
                erg += null_gr_given_c_d(c,d,S_M_IJ(mat,S_M_HI(mat)-1,j));
                }
            }
        INC(k);
        }
    }
    ENDR("random_subgroup_glk_grcd_smaller_k");
}


INT random_subgroup_glk_grcd_diagonal(k,c,d,a) OP k,c,d,a;
/* subgroup generated by diagonal matrix */
/* AK 110804 */
{
    INT erg = OK;
    CTO(INTEGER,"random_subgroup_glk_grcd_diagonal(1)",k);
    SYMCHECK(S_I_I(k)<1,"random_subgroup_glk_grcd_diagonal(1): k<1");
    SYMCHECK(S_I_I(d)<1,"random_subgroup_glk_grcd_diagonal(3): d<1");
    SYMCHECK(prime_power_p(c)==FALSE,
             "random_subgroup_glk_grcd_diagonal(2): no prime power");
    {
    OP z;
    INT ii,jj;
    erg += m_il_v(1,a);
    z = S_V_I(a,0);
    erg += m_lh_m(k,k,z);
    for (ii=0;ii<S_M_HI(z);ii++)
    for (jj=0;jj<S_M_HI(z);jj++)
	if (ii!=jj) erg += null_gr_given_c_d(c,d,S_M_IJ(z,ii,jj));

    for (jj=0;jj<S_M_HI(z);jj++)
        {
        nn:
        erg += random_gr_given_c_d(c,d,S_M_IJ(z,jj,jj));
        if (! unitp_galois(S_M_IJ(z,jj,jj))) goto nn;
        }

    }
	printf("diag generator:");println(a);
    ENDR("random_subgroup_glk_grcd_diagonal");
}


INT random_subgroup_glk_grcd_2gen(k,c,d,a) OP k,d,c,a;
/* AK 170407 V3.1 */
{
	INT erg =OK;
    CTO(INTEGER,"random_subgroup_glk_grcd_2gen(1)",k);
    CTO(INTEGER,"random_subgroup_glk_grcd_2gen(2)",c);
    CTO(INTEGER,"random_subgroup_glk_grcd_2gen(3)",d);
	{
	OP v1,v2;
	CALLOCOBJECT2(v1,v2);
	erg += random_subgroup_glk_grcd_cyclic(k,c,d,v1);
	erg += random_subgroup_glk_grcd_cyclic(k,c,d,v2);
	erg += append(v1,v2,a);
	FREEALL2(v1,v2);
	}
    ENDR("random_subgroup_glk_grcd_2gen");
}

INT random_subgroup_glk_grcd_cyclic(k,c,d,a) OP k,d,c,a;
/* findet zufällige erzeuger einer zyklischen
   untergruppe von glk  ueber GR characteristik c und degree d */
/* AK 241106 V3.1 */
{
    INT erg = OK;
    CTO(INTEGER,"random_subgroup_glk_grcd_cyclic(1)",k);
    CTO(INTEGER,"random_subgroup_glk_grcd_cyclic(2)",c);
    CTO(INTEGER,"random_subgroup_glk_grcd_cyclic(3)",d);
    {
    OP mat;INT i,j;
    mat = CALLOCOBJECT();
    m_lh_m(k,k,mat);
    ag:
    for (i=0;i<S_M_HI(mat);i++)
    for (j=0;j<S_M_LI(mat);j++)
        {
        random_gr_given_c_d(c,d,S_M_IJ(mat,i,j));
        }
    m_o_v(mat,a);

        {
          OP d;
	  d=CALLOCOBJECT(); 
	  det_mat_imm(mat,d);  printf("det=");println(d);
          if (! unitp_galois(d))   { freeall(d); goto ag; }

          //order(mat,d); printf("ordnung:"); println(d);
          FREEALL(d);
        }

    FREEALL(mat);
    }
    ENDR("random_subgroup_glk_grcd_cyclic");
}

static INT multscal_221106(mat,point,res) OP mat,point,res;
{
   INT i; INT erg = OK;
   OP inv;
        //println(point);
   inv = CALLOCOBJECT();
   MULT(mat,point,res);
   for (i=0;i<S_V_LI(res);i++) if (unitp_galois(S_V_I(res,i))) break;
      // bei i eintrag != null
   if (i==S_V_LI(res)) { println(res); error("no unit found"); }
   INVERS(S_V_I(res,i),inv); // printf("break bei %d, mult mit:",i);println(inv);
   MULT_APPLY(inv,res);
   FREEALL(inv);
        //println(res);
   ENDR("multscal_151104");
}

INT random_subgroup_glk_grcd_stabilizer(k,phgc,phgd,a) OP k,phgc,phgd,a;
/* subgroup generated as stabilizer of operation on 1-dim subspaces over Galoisring *
/
/* AK 281106 */
{
    INT erg = OK;
    CTO(INTEGER,"random_subgroup_glk_grcd_stabilizer(1)",k);
    CTO(INTEGER,"random_subgroup_glk_grcd_stabilizer(3)",phgd);
    SYMCHECK(S_I_I(k)<1,"random_subgroup_glk_grcd_stabilizer(1): k<1");
    SYMCHECK(S_I_I(phgd)<1,"random_subgroup_glk_grcd_stabilizer(3): degree<1");
    SYMCHECK(prime_power_p(phgc)==FALSE,
             "random_subgroup_glk_grcd_stabilizer(2): no prime power");
    {
    /* first step onedim random element */
    OP z=callocobject(),v;
    INT i,np=-1;
    all_points_phg(k,phgc,phgd,z);
    i = rand()%S_V_LI(z);
    v = S_V_I(z,i);
    // println(v);
        /* jetzt ist v ein kanonischer 1-dim subspace */

    /* orbit mit stabilizer */


        {
        OP g = callocobject();
        OP res = callocobject();
nochmal:
        random_subgroup_glk_grcd(k,phgc,phgd,g);
        println(g); println(v);
        orbit(g,v,res,multscal_221106,a);

        println(res); println(S_V_L(res));
        /* check ob gesamte punkte */
        if (S_V_LI(res)==S_V_LI(z)) goto nochmal;
        FREEALL2(g,res);
        }

    FREEALL(z);
    }
    ENDR("random_subgroup_glk_grcd_stabilizer");
}


INT random_subgroup_glk_grcd(k,c,d,a) OP k,d,c,a;
{
	INT erg = OK;
        CTO(INTEGER,"random_subgroup_glk_grcd(1)",k);
        CTO(INTEGER,"random_subgroup_glk_grcd(2)",c);
        CTO(INTEGER,"random_subgroup_glk_grcd(3)",d);
        {
	INT i;
	i = rand();
	i = i%6;
	if (i==0) 
		return random_subgroup_glk_grcd_diagonal(k,c,d,a);
	else if (i==1) 
		return random_subgroup_glk_grcd_smaller_k(k,c,d,a);
	else if (i==2) 
		return random_subgroup_glk_grcd_stabilizer(k,c,d,a);
	else if (i==3) 
		return random_subgroup_glk_grcd_2gen(k,c,d,a);
	else
		return random_subgroup_glk_grcd_cyclic(k,c,d,a);
	}
	ENDR("random_subgroup_glk_grcd");
}


INT get_incidence_phg(OP k,OP phg_c, OP phg_d,OP erz,OP matrix,OP bahnsizes,
            OP eindim /*mybe NULL*/, OP eindimbahnen,
            OP hyper /*mybe NULL*/, OP hyperbahnen)
{
        INT erg =OK,i,j;
        INT edf=0;
        OP c,hyprep,anzbahn,transerz;
        CALLOCOBJECT4(c,hyprep,anzbahn,transerz);
        if (eindim==NULL) { edf=1; eindim=CALLOCOBJECT(); }
        all_points_phg(k,phg_c,phg_d,eindim);
        printf("anzahl punkte:"); println(S_V_L(eindim));
        all_orbits(eindim,erz,eindimbahnen,NULL,multscal_221106); // f bahnen von 1dim uvr nummeriert 1,2,...
        //println(eindimbahnen);

        erg +=max(eindimbahnen,anzbahn); // c ist anzahl bahnen
        printf("anzahl der bahnen = "); println(anzbahn);

        erg += m_lh_nm(anzbahn,anzbahn,matrix);
        erg += m_l_nv(anzbahn,bahnsizes);
        m_il_v(S_V_LI(erz),transerz);
        for (i=0;i<S_V_LI(transerz);i++) transpose(S_V_I(erz,i),S_V_I(transerz,i));
        if (hyper!=NULL) copy(eindim,hyper);
        else hyper=eindim;
        all_orbits(hyper,transerz,hyperbahnen,NULL,multscal_221106); // f bahnen von 1dim uvr nummeriert 1,2,...
        //printf("bahnen der hyperebenen:");println(hyperbahnen);
        max(hyperbahnen,c);
        printf("anzahl der hyperbahnen = "); println(c);
        m_l_v(c,hyprep); // vektor für repräsentanten der hyperebenen
        for (i=0;i<S_V_LI(hyperbahnen);i++) { M_I_I(i,S_V_I(hyprep, S_V_II(hyperbahnen,i)-1)); }
        println(hyprep);
        for (j=0;j<S_V_LI(eindimbahnen);j++)
                  {
                  for (i=0;i<S_V_LI(hyprep);i++)
                      {
                      OP y,x;
                      x = S_V_I(eindim,S_V_II(hyprep,i));
                      y = S_V_I(eindim,j);
                      erg +=scalarproduct(x,y,c);
                      if (NULLP(c)) INC(S_M_IJ(matrix,i,S_V_II(eindimbahnen,j)-1));
                      }

                  INC(S_V_I(bahnsizes,S_V_II(eindimbahnen,j)-1));
                  }
        if (edf==1) FREEALL(eindim);
        FREEALL4(c,hyprep,anzbahn,transerz);
        ENDR("get_incidence_phg");
}

INT all_points_phg(k,phg_c,phg_d,res) OP k,phg_c,phg_d,res;
/* alle 1 dimensionalen uvr von GR(c,d)^k */
/* in sortierter folge */
/* AK 211106 */
{
    INT erg = OK;
    CTO(INTEGER,"all_points_phg(1)",k);
    CTO(INTEGER,"all_points_phg(2)",phg_c);
    CTO(INTEGER,"all_points_phg(3)",phg_d);

    C3R(k,phg_c,phg_d,"all_points_phg_store",res);
    {
    INT i,j; OP z,h,v,nv;
    CALLOCOBJECT2(v,nv);
    vectorofzerodivisors_galois(phg_c, phg_d, nv);
    //printf("nullteiler sind:");println(nv);
    m_il_v(0,res);
    for (i=0;i<S_I_I(k);i++)
        {
	m_il_v(0,v);
        inc(v);
	z = S_V_I(v,S_V_LI(v)-1);
        m_l_v(k,z);
        for (j=0;j<i;j++) null_gr_given_c_d(phg_c,phg_d,S_V_I(z,j));
        eins_gr_given_c_d(phg_c,phg_d,S_V_I(z,i));
        for (j=i+1;j<S_I_I(k);j++)
             first_gr_given_c_d(phg_c,phg_d,S_V_I(z,j));

        // das war der erste mit der 1 an der stelle i
        h = CALLOCOBJECT();
        if (i<(S_I_I(k)-1))
        while (1) {
              INT res;
              copy(z,h);
              j=S_V_LI(h)-1;
    nochmal:
              res = next_gr(S_V_I(z,j),S_V_I(h,j));
              if (res == LAST_FF) {
                  if (j==(i+1)) break;
                  j--; goto nochmal;
                  }
              else {
                  INT jj;
                  for (jj=j+1;jj<S_V_LI(h);jj++)
                      first_gr_given_c_d(phg_c,phg_d,S_V_I(h,jj));
                  inc(v); z = S_V_I(v,S_V_LI(v)-1);
                  copy(h,z);
                  }
              }
        FREEALL(h);
        /* v ist jetzt der vektor mit 0'en bis platz i 
           jetzt müssen davor alle möglichen nullteiler in allen permutationen kommen */
	append_apply(res,v); // v an res anhängen
        if ((S_V_LI(nv)>1)&&(i>0)) {
		OP lv;
		lv=CALLOCOBJECT();
		m_il_nv(i,lv); // nv ist die schleife über alle füllungen , nullvektor ist start
nn:
		for (j=S_V_LI(lv)-1;j>=0;j--)
			{
			if (S_V_II(lv,j)+1 < S_V_LI(nv)) { inc(S_V_I(lv,j)); 
						           for (++j;j<S_V_LI(lv);j++) M_I_I(0,S_V_I(lv,j));
							// lv hat jetzt die indices der nullteiler
							   for (j=0;j<S_V_LI(v);j++)
								{
								INT k;
								for (k=0;k<S_V_LI(lv);k++)
									copy(S_V_I(nv,S_V_II(lv,k)), S_V_I(S_V_I(v,j),k));
								}
							    append_apply(res,v); // v an res anhängen
							// println(lv);
							    goto nn;
                                                          }
			// das war die letzte nullteiler verteilung
			}
		FREEALL(lv);	
		}
        }
    FREEALL2(v,nv);
    sort(res);
    }
    S3R(k,phg_c,phg_d,"all_points_phg_store",res);
    ENDR("all_points");
}

