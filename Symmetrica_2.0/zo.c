/* IK: 150591 */
#include "def.h"
#include "macro.h"
static INT berechne_Dominanz();
static INT berechne_sprod_kk();
static INT berechne_sumvec();
static INT berechne_M_Pk();
static INT mult_udrmatrix_matrix();

#ifdef MATRIXTRUE
#ifdef CHARTRUE
INT compute_zonal_with_alphabet(part,l,res) OP part,l,res;
/* AK 210891 V1.3 */
{
	OP c,d,e,f,g,h,i;
	INT ind,z;
	INT erg = OK;

	C2R(part,l,"compute_zonal_with_alphabet",res);
	CTO(PARTITION,"compute_zonal_with_alphabet",part);
	CTO(INTEGER,"compute_zonal_with_alphabet",l);
	if (S_PA_LI(part) > S_I_I(l))
		{
		erg += init(POLYNOM,res);
		goto s2r_ende;
		}
	c = callocobject();
	d = callocobject();
	e = callocobject();
	f = callocobject();
	g = callocobject();
	h = callocobject();
	i = callocobject();

	erg += weight(part,c);
	erg += makevectorofpart(c,e);

	erg += young_tafel(c,h,NULL,NULL);
	erg += invers(h,h);
	erg += transpose(h,i);

	erg += m_ilih_m(S_V_LI(e),S_V_LI(e),f);
	erg += berechne_Dominanz(S_V_LI(e),e,f);

	erg += m_ilih_m(S_V_LI(e),S_V_LI(e),g);
	erg += berechne_sprod_kk(S_V_LI(e),c,e,h,i, f, g);

	erg += m_ilih_m(S_V_LI(e),S_V_LI(e),d);
	erg += berechne_M_Pk(S_V_LI(e),g,e,f,d);

	ind = indexofpart(part);
	erg += init(POLYNOM,res);
	for (z=0L;z<S_V_LI(e);z++)
		{
		if (not nullp(S_M_IJ(d,ind,z)))
			{
			erg += compute_monomial_with_alphabet(S_V_I(e,z),l,f);
			erg += mult_apply(S_M_IJ(d,ind,z),f);
			erg += add_apply(f,res);
			}
		}

	erg += freeall(c);
	erg += freeall(d); 
	erg += freeall(e); 
	erg += freeall(f); 
	erg += freeall(g); 
	erg += freeall(h); 
	erg += freeall(i);
s2r_ende:
	S2R(part,l,"compute_zonal_with_alphabet",res);
	ENDR("compute_zonal_with_alphabet");
}
#endif /* CHARTRUE */
#endif /* MATRIXTRUE */



/*-----------------------------------------------------------------*/
/*                         UNTERPROGRAMME                          */
/*-----------------------------------------------------------------*/

/*-----------------------------------------------------------------*/
#ifdef PARTTRUE
static INT berechne_sumvec(dim,vectorofpart,laenge,sumvec) INT dim;
	OP vectorofpart,laenge,sumvec;
              /* sumvec enthaelt an der Stelle i den zu der Partition 
                 mit dem Index i gehoerenden Teilsummenvektor, also 
                 den Vektor der als i-ten Eintrag die Summe der 
                 ersten i Teile der Partition enthaelt */
  
/* AK 210891 V1.3 */
{
	INT i,j,k;

	for (i=1L;i<dim-1L;i++)
	   {
	   m_l_v(S_V_I(laenge,i),S_V_I(sumvec,i));
	   for (j=0L;j<S_V_II(laenge,i);j++)
	      {
	      m_i_i(0L,S_V_I(S_V_I(sumvec,i),j));
	      for (k=0L;k<=j;k++)
		 {
	add(S_V_I(S_V_I(sumvec,i),j),S_PA_I(S_V_I(vectorofpart,i),
	    S_V_II(laenge,i)-1-k),S_V_I(S_V_I(sumvec,i),j));
		 }
	      } /* for j */
	   } /* for i */
	return OK;
}                                          /* Ende berechne_sumvec */
#endif /* PARTTRUE */
/*-----------------------------------------------------------------*/

 


/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/
/*             siehe Programmbeschreibung unter 2.                 */
/*-----------------------------------------------------------------*/
#ifdef MATRIXTRUE
#ifdef PARTTRUE
static INT berechne_Dominanz(dim,vectorofpart,Dominanz) INT dim;
	OP vectorofpart,Dominanz;
/* AK 210891 V1.3 */
{
	INT i,j,k;
	OP laenge,sumvec;

	laenge=callocobject();
	sumvec=callocobject();

	for (i=1L;i<dim-1L;i++)
	   {
	   m_i_i(1L,S_M_IJ(Dominanz,i,i));
	   m_i_i(1L,S_M_IJ(Dominanz,0L,i));
	   m_i_i(1L,S_M_IJ(Dominanz,i,dim-1L));
	   }
	m_i_i(1L,S_M_IJ(Dominanz,0L,0L));
	m_i_i(1L,S_M_IJ(Dominanz,0L,dim-1L));
	m_i_i(1L,S_M_IJ(Dominanz,dim-1L,dim-1L));
	m_il_v(dim,laenge);       /* laenge enthaelt an Stelle i die Laenge 
				     der zum Index i gehoerenden Partition */   
					     
	for (i=0L;i<dim;i++)                  
	   M_I_I(S_PA_LI(S_V_I(vectorofpart,i)),S_V_I(laenge,i));
	m_il_v(dim,sumvec);
	berechne_sumvec(dim,vectorofpart,laenge,sumvec);
	for (i=1L;i<dim-2L;i++)
	   for (j=i+1L;j<dim-1L;j++)
	      if ( S_V_II(laenge,i) > S_V_II(laenge,j) )
		 m_i_i(0L,S_M_IJ(Dominanz,i,j));
	      else
		 {
		 m_i_i(1L,S_M_IJ(Dominanz,i,j));
		 for (k=0L;k<S_V_II(laenge,i);k++)
		    if (S_M_IJI(Dominanz,i,j) == 1L)
		       if (S_V_II(S_V_I(sumvec,i),k) - 
			   S_V_II(S_V_I(sumvec,j),k) < 0 )
			  m_i_i(0L,S_M_IJ(Dominanz,i,j));
		 } /* else */

	for (i=0L;i<dim;i++)
		for (j=0L;j<dim;j++)
				if (emptyp(S_M_IJ(Dominanz,i,j)))
					m_i_i(0L,S_M_IJ(Dominanz,i,j));

	freeall(sumvec); freeall(laenge); 
	return OK;
}                                        /* Ende berechne_Dominanz */
#endif /* PARTTRUE */
#endif /* MATRIXTRUE */
/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/




/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/
/*             siehe Programmbeschreibung unter 3.                 */
/*-----------------------------------------------------------------*/
#ifdef MATRIXTRUE
#ifdef PARTTRUE
static INT berechne_sprod_kk(dim,n,vectorofpart,ytinvers,M_ks,Dominanz,
		     sprod_kk)
        /* berechnet die Matrix sprod_kk, die an der Stelle (i,j) das 
           "alpha-Skalarprodukt" der monomialsym. Polynome zu den 
           Partitionen mit Indizes i und j enthaelt */
	INT dim;
	OP n,vectorofpart,ytinvers,M_ks,Dominanz,sprod_kk;
/* AK 210891 V1.3 */
{
	INT i,j,k;
        INT erg = OK;
	OP part,alpha,l,zen,h_eins,h_zwei,zen_zwei;

	l=callocobject();
	zen=callocobject();
	h_eins=callocobject();
	alpha=callocobject();
	h_zwei=callocobject();
	zen_zwei=callocobject();

	m_il_v(dim,zen_zwei);
	for(i=0L;i<dim;i++)
	   m_i_i(0L,S_V_I(zen_zwei,i));
	m_i_i(2L,alpha);
	for(i=0L;i<dim;i++)
	   {
	    part=callocobject();
	    copy(S_V_I(vectorofpart,i),part);
	    ordcen(part,zen);
	    length_partition(part,l);
	    hoch(alpha,l,h_eins);
	    mult(zen,h_eins,S_V_I(zen_zwei,i));
	    freeall(part);
            FREESELF(l);
	   }
	for(i=0L;i<dim;i++)
	   for(j=i;j<dim;j++)
	      {
	      m_i_i(0L,S_M_IJ(sprod_kk,i,j));
	      if(S_M_IJI(Dominanz,i,j)==1L)
		 for(k=0L;k<dim;k++)
		    {
		    mult(S_M_IJ(M_ks,i,k),S_M_IJ(M_ks,j,k),h_zwei);
		    mult(h_zwei,S_V_I(zen_zwei,k),h_zwei);
		    add_apply(h_zwei,S_M_IJ(sprod_kk,i,j));
		    }
	       }

	freeall(alpha); freeall(l); freeall(zen);
	freeall(h_eins); freeall(h_zwei); freeall(zen_zwei); 
	ENDR("berechne_sprod_kk:internal function");
}                                        /* Ende berechne_sprod_kk */
#endif /* PARTTRUE */
#endif /* MATRIXTRUE */
/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/




#ifdef MATRIXTRUE 
static INT berechne_Ainvers_und_b(dim,i,Ainvers,b,M_Pk,sprod_kk,Dominanz)
	INT dim,i;
	OP Ainvers,b,M_Pk,sprod_kk,Dominanz;
/* AK 210891 V1.3 */
{
	INT j,k;
	OP h,Ainvers_alt; 

	h=callocobject();
	Ainvers_alt=callocobject();

	m_ilih_m(dim-i-2L,dim-i-2L,Ainvers_alt);
	for (j=dim-i-3L;j>=0L;j--)
	   for (k=0L;k<=dim-i-3L;k++)
	      copy(S_M_IJ(Ainvers,j,k),S_M_IJ(Ainvers_alt,j,k));

	m_ilih_m(dim-i-1L,dim-i-1L,Ainvers); /* Speicher fuer neues Ainvers */
	for (j=dim-i-3L;j>=0L;j--)
	   for (k=0L;k<=dim-i-3L;k++)
	      copy(S_M_IJ(Ainvers_alt,j,k),S_M_IJ(Ainvers,j+1L,k+1L));
	freeall(Ainvers_alt); /* Ainvers_alt freigeben, Werte auf neues 
				 Ainvers kopiert */
	m_i_i(0L,S_M_IJ(Ainvers,0L,0L));

	for (j=0L;j<dim;j++)
		for (k=0L;k<dim;k++)
			{
			if (emptyp(S_M_IJ(sprod_kk,j,k)))
				m_i_i(0L,S_M_IJ(sprod_kk,j,k));
			if (emptyp(S_M_IJ(M_Pk,j,k)))
				m_i_i(0L,S_M_IJ(M_Pk,j,k));
			}

	for (k=i+1L;k<dim;k++)
	   {
	   mult(S_M_IJ(M_Pk,i+1L,k),S_M_IJ(sprod_kk,i+1L,k),h);
	   add(S_M_IJ(Ainvers,0L,0L),h,S_M_IJ(Ainvers,0L,0L));
	   }
	invers(S_M_IJ(Ainvers,0L,0L),S_M_IJ(Ainvers,0L,0L));
	for (j=1L;j<dim-i-1L;j++)
	   {
	   m_i_i(0L,S_M_IJ(Ainvers,j,0L));
	   for (k=1L;k<=j;k++)
	      {
	      mult(S_M_IJ(b,k-1L,0L),S_M_IJ(Ainvers,j,k),h);
	      add_apply(h,S_M_IJ(Ainvers,j,0L));
	      } /* for k */
	   mult_apply(S_M_IJ(Ainvers,0L,0L),S_M_IJ(Ainvers,j,0L));
	   } /* for j */
						  /* Ainvers ist berechnet */

	m_ilih_m(1L,dim-i-1L,b);
	for (j=0L;j<dim-i-1L;j++)
	   {
	   m_i_i(0L,S_M_IJ(b,j,0L));
	   if(S_M_IJI(Dominanz,i,j+i+1L) == 1L)
	      {
	      for (k=j;k<dim;k++)
		 {
		 mult(S_M_IJ(M_Pk,j+i+1L,k),S_M_IJ(sprod_kk,i,k),h);
		 add(S_M_IJ(b,j,0L),h,S_M_IJ(b,j,0L));
		 } /* for k */
	      addinvers(S_M_IJ(b,j,0L),S_M_IJ(b,j,0L));
	      }
	   } /* for j */

	freeall(h);
	return OK;
}                                   /* Ende berechne_Ainvers_und_b */
#endif /* MATRIXTRUE */
/*-----------------------------------------------------------------*/




/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/
/*             siehe Programmbeschreibung unter 4.                 */
/*-----------------------------------------------------------------*/
#ifdef MATRIXTRUE
static INT berechne_M_Pk(dim,sprod_kk,vectorofpart,Dominanz,M_Pk) INT dim;
	OP sprod_kk,vectorofpart,Dominanz,M_Pk;
/* AK 210891 V1.3 */
{
	INT i,j,k,domdim,sum,index[77];
	OP Ainvers,b,C,Adachinv,bdach;

	Ainvers=callocobject(); 
	b=callocobject();
	C=callocobject(); 

	for(i=0L;i<dim;i++) m_i_i(1L,S_M_IJ(M_Pk,i,i));
	m_ilih_m(1L,1L,Ainvers);
	invers(S_M_IJ(sprod_kk,dim-1L,dim-1L),S_M_IJ(Ainvers,0L,0L));
	m_ilih_m(1L,1L,b);
	addinvers(S_M_IJ(sprod_kk,dim-2L,dim-1L),S_M_IJ(b,0L,0L));
	mult(Ainvers,b,C);
	copy(S_M_IJ(C,0L,0L),S_M_IJ(M_Pk,dim-2L,dim-1L));
	freeall(C);

	for(i=dim-3L;i>=0L;i--)  /* Berechnung des zonalen Polynoms zur 
				  Partition mit Index i */
	  {
	   C=callocobject(); 
	   Adachinv=callocobject();
	   bdach=callocobject();

	   domdim=0L;
	   for (j=i+1L;j<dim;j++)
	      domdim = domdim + S_M_IJI(Dominanz,i,j);
				  /* domdim ist die Dimension von Adachinv */
	   for (j=0L;j<domdim;j++)
	      {
	      sum = 0L;
	      k = i;
	      while (sum < j+1L)
		 sum = sum + S_M_IJI(Dominanz,i,++k);
	      index[j] = k;
	      }
	   berechne_Ainvers_und_b(dim,i,Ainvers,b,M_Pk,sprod_kk,Dominanz);
	   m_ilih_m(domdim,domdim,Adachinv);
	   m_ilih_m(1L,domdim,bdach);

	   for (k=0L;k<domdim;k++)
	      copy(S_M_IJ(b,index[k]-(i+1L),0L),S_M_IJ(bdach,k,0L));
	   for (j=0L;j<domdim;j++)
	      for (k=0L;k<domdim;k++)
		    if (k<=j)
			copy(S_M_IJ(Ainvers,index[j]-(i+1L),index[k]-(i+1L)),
			     S_M_IJ(Adachinv,j,k));
	   for (j=0L;j<domdim;j++)
	      for(k=j+1L;k<domdim;k++)
		 m_i_i(0L,S_M_IJ(Adachinv,j,k));
	   mult_udrmatrix_matrix(Adachinv,bdach,C);
	    /* Multiplizieren der unteren Dreieckmatrix Adachinv mit bdach */

	   for (j=0L;j<domdim;j++)
	      copy(S_M_IJ(C,j,0L),S_M_IJ(M_Pk,i,index[j]));
	   for (j=i+1L;j<index[0];j++)
	      m_i_i(0L,S_M_IJ(M_Pk,i,j));
	   for (j=0L;j<domdim-1L;j++)
	      for (k=index[j]+1L;k<index[j+1];k++)
		 m_i_i(0L,S_M_IJ(M_Pk,i,k));

	   freeall(Adachinv);
	   freeall(bdach);
	   freeall(C);
	  }
	freeall(Ainvers);
	freeall(b);
	return OK;
}                                            /* Ende berechne_M_Pk */
#endif /* MATRIXTRUE */
/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/




/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/
/*             siehe Programmbeschreibung unter 5.                 */
/*-----------------------------------------------------------------*/
#ifdef KOSTKATRUE
static INT berechne_M_ke(dim,n,K,vectorofpart,M_ke)
     /* M_ke ist die Uebergangsmatrix zwischen den monomialsymm. 
        Polynomen und den Produkten der elementarsymm. Funktionen. */
	INT dim; OP n,K,vectorofpart,M_ke;
/* AK 210891 V1.3 */
{
	OP J,Kinvers,Ktinv;

	Kinvers=callocobject();
	Ktinv=callocobject();
	J=callocobject();

	invers_matrix(K,Kinvers);
	transpose_matrix(Kinvers,Ktinv);
	make_n_transpositionmatrix(n,J);
	mult(Ktinv,J,M_ke);
	mult(M_ke,Kinvers,M_ke);

	freeall(J); freeall(Kinvers); freeall(Ktinv);
	return OK;
}/* Ende berechne_M_ke */
#endif /* KOSTKATRUE */
/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/




/*-----------------------------------------------------------------*/
/*-----------------------------------------------------------------*/
/*             siehe Programmbeschreibung unter 6.                 */
/*-----------------------------------------------------------------*/
#ifdef MATRIXTRUE 
static INT Anpassen(dim,n,ytstern,M_ke,M_Pk)
           /* M_Pk wird anders normiert (siehe James, z.B. 1964), man 
              erhaelt M_Zk. Daraus wird M_Zs, die Uebergangsmatrix 
              zwischen den zonalen Polynomen Z und den Produkten der 
              Potenzsummen berechnet. Diese M_Zs sind tabelliert. 
              Analoges gilt fuer die M_Ze. */
	INT dim;
	OP n,ytstern,M_ke,M_Pk;
/* AK 210891 V1.3 */
{
	INT i,j;
	OP h,diag,M_Zk,M_Zs,M_Ze;
	h=callocobject();
	diag=callocobject();
	M_Zk=callocobject();
	M_Zs=callocobject();
	M_Ze=callocobject();     

	m_ilih_m(dim,dim,diag);
	fakul(n,h);
	for(i=0L;i<dim;i++)
	  {
	   for(j=0L;j<i;j++)          
	     {
	      m_i_i(0L,S_M_IJ(M_Pk,i,j));
	      m_i_i(0L,S_M_IJ(diag,i,j));
	     }
	   for(j=i;j<dim;j++)
	      m_i_i(0L,S_M_IJ(diag,i,j));
	  }
	for(i=0L;i<dim;i++)
	   div(h,S_M_IJ(M_Pk,i,dim-1L),S_M_IJ(diag,i,i));
	m_ilih_m(dim,dim,M_Zk);
	mult(diag,M_Pk,M_Zk); 

	printf("Uebergangsmatrizen, um die zonalen Polynome Z in \n");
	printf("verschiedenen Basen darzustellen:\n");
	printf("\n");
	printf("Basis : monomialsymm. Funktionen\n");
	println(M_Zk);
	printf("\n");
	printf("Basis : Potenzsummen\n");
	m_ilih_m(dim,dim,M_Zs);
	mult(M_Zk,ytstern,M_Zs);
	println(M_Zs); 
	printf("\n");
	printf("Basis : elementarsymm. Funktionen\n");
	m_ilih_m(dim,dim,M_Ze);
	mult(M_Zk,M_ke,M_Ze);
	println(M_Ze); 
	printf("\n");
	printf("\n");


	freeall(h); freeall(diag); freeall(M_Zk); freeall(M_Zs);
	freeall(M_Ze);
	return OK;
}                                                 /* Ende Anpassen */



static INT mult_udrmatrix_matrix(a,b,c) OP a,b,c;
/* AK 280388 */
/* AK 060789 V1.0 */ /* AK 210891 V1.3 */
{
	INT i,j,k;
        INT erg = OK;
	OP z; /* zwischen ergebnis bei matrix-multiplikation */

	if (neq(s_m_l(a),s_m_h(b)))
	{ 
		error("mult_matrix_matrix:can not be multiplied");
		return(ERROR); 
	};

	m_ilih_nm(S_M_LI(b),S_M_HI(a),c);
	z=callocobject(); /* zwischensumme*/
	for (i=0L;i<S_M_HI(a);i++)	/* ueber zeilen der linken Matrix */
		for (j=0L;j<S_M_LI(b);j++) /* ueber spalten der rechten Matrix */
			for (k=0L;k<i+1L;k++)
			{ 
				MULT(S_M_IJ(a,i,k),S_M_IJ(b,k,j),z);
				add_apply(z,S_M_IJ(c,i,j)); 
                                FREESELF(z);
			};
	FREEALL(z); 
	ENDR("mult_udrmatrix_matrix:internal function");
}
#endif 


