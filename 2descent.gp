read("rand.gp");
read("LinAlg.gp");
read("ModSq.gp");

hyperellinit(f,GRH=0)=
{
 my(x,z,p,q,n,g,d,fa,S,K,bnfcert,Places,Hbasis,Sk);
 \\ Get reduced model
 if(type(f)=="t_VEC",
	if(#f!=2,error("Cannot understand equation"));
	f=4*f[1]+f[2]^2
 );
 x=variable(f);
 n=poldegree(f);
 \\ Get odd degree model
 if(n%2==0,
	z=nfroots(,f); \\ Rational roots
	if(#z==0,error("Sorry, the case with no rational Weierstrass point is not yet implemented."));
	z=z[1];
	p=numerator(z);
	q=denominator(z);
	f=subst(f,x,1/x+p/q)*x^n;
	n-=1;
 );
 g=(n-1)\2;
 \\ Get integral monic model
 q=denominator(content(f));
 p=polcoef(f,n)*q;
 f=q^(n+1)*p^(n-1)*subst(f,x,x/(p*q));
 d=poldisc(f);
 \\ Check that f is squarefree
 if(d==0,
  error("This curve is singular.")
 );
 \\ Find bad primes
 fa=factor(4*d);
 S=List();
 for(i=1,#fa~,
  if(fa[i,2]>1,listput(S,fa[i,1]))
 );
 S=Vec(S);
 \\ List of factors of étale algebre Q[x]/f
 K=parapply(T->bnfinit(T,1),factor(f)[,1]~);
 if(GRH==0,
  bnfcert=parapply(bnfcertify,K);
  if(bnfcert!=vector(#K,i,1),error("Error in bnfinit"));
 );
 \\ Matrix of data about the places of fields in K above the primes in S
 Places=matrix(#K,#S,i,j,hyperlocdata(K[i],S[j]));
 \\ Find basis for H = oplus_K H_K
 Hbasis=vector(#K);
 for(k=1,#K,
  Sk=apply(X->X[2],concat(Places[k,])); \\ Vector of places of K[k] above S
  Hbasis[k]=bnfquadunram(K[k],Sk);
 );
 \\S=factor(abs(apply(norm,concat(Hbasis))))[,1]~;
 [f,g,d,S,K,Places,Hbasis];
}
 

SelmerDeltaLocal(f,v,Places,U)=
/* Let U in Q[x] come form a point [U,V] (Cantor form) of J(Qv).
(In particular, U is monic).
Computes the image of this point by the "x-T" map.
TODO if v=0 (place at infty), also accepts U in R[x]
but assumes deg(U)=1 and that the root of U is not a root of f. */
{
 my(fa,s,res=List(),K,P,pi,PR,B,r,u);
 fa=factor(U);
 if(#fa~>1,
  return(sum(i=1,#fa~,if(fa[i,2]%2,SelmerDeltaLocal(f,v,Places,fa[i,1]),0)))
 );
 \\ Now U is irreducible over Q
 if(v==0,
  u=polrootsreal(U)[1];
  for(k=1,#Places,
   K=Places[k];
   r=K.sign[1];
   listput(res,vector(r,i,sign2(u-K.roots[i]))~)
  )
 ,
  \\ Case v finite
  for(i=1,#Places,
   if(v==2,
    [K,P,pi,PR,B]=Places[i];
    if(U==K.pol, \\ 2-torsion?
     u=f/U
    ,
     u=U
    ); 
    s=(-1)^poldegree(u);
    listput(res,ModSqLocal_2(K,s*Mod(u,K.pol),P,pi,PR,B))
   ,
    [K,P,pi,PR]=Places[i];
    if(U==K.pol, \\ 2-torsion?
     u=f/U
    ,
     u=U
    );
    s=(-1)^poldegree(u);
    listput(res,ModSqLocal_odd(K,s*Mod(u,K.pol),P,pi,PR))
   )
  )
 );
 concat(Vec(res));
}

{
SelmerLocalBasis(f,v,Places,Uhint=[])=
 my(r,tgdim,Zf,A,U,res,prec=10,niter=0);
 if(v==0,
  print("Computing local Selmer at v=oo");
  Zf=vecsort(polrootsreal(f));
  r=#Zf;
  tgdim=(r-1)/2;
  A=[];
  for(j=1,tgdim,
   A=matconcat([A,SelmerDeltaLocal(f,v,Places,x-(Zf[2*j-1]+Zf[2*j])/2)])
  );
  A
 ,
  tgdim=#factorpadic(f,v,1)~-1;
  if(v==2,
   tgdim += floor((poldegree(f)-1)/2)
  );
  print("Computing local Selmer at v=",v,", wanted dimension:",tgdim);
  A=Mat();
  for(i=1,#Uhint,
   U=Uhint[i];
   [A,res]=ColAppend(A,SelmerDeltaLocal(f,v,Places,U));
   if(#A==tgdim,
    print("Got all from hints");
		return(A)
		)
  );
  if(#A,
   print("Got ",#A," from hints")
  );
  while(#A!=tgdim,
	 niter+=1;
   U=randJcantor(v,f,1+random(ceil(niter/2^12)),prec); \\ TODO tune exponent of 2
	 if(U==[],
		print("Increasing precision");
		prec += 10;
		next
	 );
   [A,res]=ColAppend(A,SelmerDeltaLocal(f,v,Places,U));
   if(res,print("Got ",#A))
  );
  A
 );
}

{
Hdim(f,v,Places)=
 if(v==0,return(#polrootsreal(f)));
 if(v==2,return(poldegree(f)+2*#Places));
 2*#Places;
}

{
SelmerLocalEqn(f,v,Places,Uhint=[])=
 my(Sel);
 Sel=SelmerLocalBasis(f,v,Places,Uhint);
 if(#Sel,
  EqnMat(Sel)
 ,
  \\ Treat case of null image specially because gp cannot handle matrices with 0 columns
  matid(Hdim(f,v,Places))*Mod(1,2)
 );
}

{
Sel2rank(C,hratmax=1000)=
 my([f,g,d,S,listK,Places,Hbasis]=C,ratpts,Uhint,SelEqns,K,Sk,A,Ap,e,delta,Pp,P,pi,PR,B,p);
 \\ Prepare hints for local Selmer computations
 ratpts=hyperellratpoints(f,hratmax); \\ Find some rational points
 ratpts=select(P->P[2]>0,ratpts); \\ Keep the ones with y>0
 Uhint=apply(P->variable(f)-P[1],ratpts); \\ Get the corresponding U
 Uhint=concat(vector(#listK-1,m,listK[m].pol),Uhint); \\ Add a basis of 2-torsion
 \\ Compute equations defining the 2-Selmer
 SelEqns=vector(#S,i,SelmerLocalEqn(f,S[i],concat(Places[,i]~),Uhint));
 SelEqns=concat(SelEqns,[SelmerLocalEqn(f,0,listK)]); \\ Add equations for the place infty
 \\ Prepare matrix
 A=[];
 \\ Start by equations for Ker norm
 for(k=1,#listK,
  for(i=1,#Hbasis[k],
   e=Hbasis[k][i];
   A=matconcat([A,QQSmodSq(norm(e),S)]);
  )
 );
 \\print("Matrice A pour les normes:");
 \\printp(lift(A));
 \\ Loop over S
 for(s=1,#S,
  p=S[s];
  print("Place p=",p);
  \\ Prepare matrix for this p
  Ap=[];
  \\ Loop over basis of H
  for(k=1,#listK,
   for(i=1,#Hbasis[k],
    e=Hbasis[k][i];
    \\ Compute image of basis element in H_p
    delta=[]~;
    for(j=1,#listK,
     Pp=Places[j,s];
     if(j==k,
      for(l=1,#Pp,
       if(p==2,
        [K,P,pi,PR,B]=Pp[l];
        delta=concat(delta,ModSqLocal_2(K,e,P,pi,PR,B))
       ,
        [K,P,pi,PR]=Pp[l];
        delta=concat(delta,ModSqLocal_odd(K,e,P,pi,PR))
       )
      )
     ,
      delta=concat(delta,vector(Hdim(listK[j].pol,p,Pp))~*Mod(0,2))
     )
    );
    \\ Now delta is the image of e
    \\ Apply equations to it and store result
    Ap=matconcat([Ap,SelEqns[s]*delta]);
   )
  );
  \\ Now the columns of Ap represent the failure of the elements of Hbasis to satisfy local conditions from p
  \\ Stack this to obstructions from other p's
  A=matconcat([A,Ap]~);
  \\print("Matrice A:");
  \\printp(lift(A));
 );
 \\ Now, place at infty
 print("Place oo");
 Ap=[];
 for(k=1,#listK,
  for(i=1,#Hbasis[k],
   e=Hbasis[k][i];
   delta=[]~;
   for(j=1,#listK,
    K=listK[j];
    r=K.sign[1];
    if(j==k,
     delta=concat(delta,apply(sign2,nfeltsign(K,e,[1..r])~))
    ,
     delta=concat(delta,vector(r)~*Mod(0,2))
    )
   );
   Ap=matconcat([Ap,SelEqns[#S+1]*delta]);
  )
 );
 A=matconcat([A,Ap]~);
 \\print("Matrice A finale:");
 \\printp(lift(A));
 \\ Now the columns of A represent the failure of the elements of Hbasis to satisfy all local conditions
 \\ So the kernel of A is the 2-Selmer
 #matker(A);
}

/*   for(l=1,#Pp,
      if(p==2,
       \\ Case p=2
       [K,P,pi,PR,B]=Pp[l];
       if(j==k,
        \\ Really evaluate at e
        delta=concat(delta,ModSqLocal_2(K,e,P,pi,PR,B));
       ,
        \\ Vector of 0
        delta=concat(delta,vector(P.e*P.f+2,m,Mod(0,2))~);
       )
      ,
       \\ Case p odd
       if(j==k,
        \\ Really evaluate at e
        [K,P,pi,PR]=Pp[l];
        delta=concat(delta,ModSqLocal_odd(K,e,P,pi,PR));
       ,
        \\ Vector of 0
        delta=concat(delta,[0,0]~);
       )
      )
     )
    );
    \\ Now delta is the image of e
    \\ Apply equations to it and store result
    Ap=matconcat([Ap,SelEqns[s]*delta]);
   )
  );*/


{
hyperellboundrank(C)=
 Sel2rank(C)-(#factor(C[1])~-1);
}
