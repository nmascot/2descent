sign2(x)=
/* sign of real x as an integer mod 2 */
{
 Mod((sign(x)-1)/2,2);
}

hyperlocdata(K,p)=
{
 my(res=List(),Pp,P,pi,PR,B);
 Pp=idealprimedec(K,p);
 for(k=1,#Pp,
  P=Pp[k]; \\ Prime ideal
  pi=nfbasistoalg(K,P.gen[2]); \\ Uniformiser
  PR=nfmodprinit(K,P); \\ Residual field data
  if(p==2,
   b=ffgen(nfmodpr(K,1,PR)); \\ Generator of residual field
   B=apply(t->nfbasistoalg(K,nfmodprlift(K,t,PR)),powers(b,P.f-1)); \\ Lift of F2-basis of residue field
   listput(res,[K,P,pi,PR,B])
  ,
   listput(res,[K,P,pi,PR])
  )
 );
 Vec(res);
}

ModSqLocal_odd(K,a,P,pi,PR)=
/* Class of a in KP* / KP*² where P is a prime of K above an odd p.
pi is assumed to be a uniformiser for P.
The result is a vector of length 2. */
{
 my(w,u);
 w=idealval(K,a,P);
 u=a/pi^w;
 [w,1-issquare(nfmodpr(K,u,PR))]~*Mod(1,2);
}

ModSqLocal_2(K,a,P,pi,PR,B)=
/* Class of x in KP* / KP*² where P is a prime of K above 2.
eP and fP are the ramif and inertia indices of P,
and B is the vector of lifts to ZK of the elements 1,x,x²,..,x^(fP-1) of ZK/P,
and pi is a uniformiser of P.
The result is a vector of length eP*fP+2. */
{
 my(i=2,eP=P.e,fP=P.f,w,s,u,r);
 s=vector(eP*fP+2)~;
 w=idealval(K,a,P);
 s[1]=w*Mod(1,2);
 u=a/pi^w;
 u=u^(2^fP-1); \\ Make u = 1 mod P
 for(j=1,eP,
  \\ Here u = 1 mod P^(2j-1)
  r=nfmodpr(K,(u-1)/pi^(2*j-1),P).pol;
  for(h=1,fP,
   s[i]=polcoeff(r,h-1)*Mod(1,2);
   if(s[i],
    u*=1+B[h]*pi^(2*j-1)
   );
   i+=1
  );
  \\ Now u = 1 mod P^2j
  if(j<eP,
   r=(u-1)/pi^(2*j);
   r=nfmodpr(K,r,P);
   r=sqrt(r);
   r=nfbasistoalg(K,nfmodprlift(K,r,P));
   u*=(1+r*pi^j)^2
  ,
   r=(u-1)/4;
   r=nfmodpr(K,r,P);
   s[i]=trace(r);
  )
 );
 s;
}

{
QQSmodSq(x,S)=
 concat([sign2(x)],apply(p->Mod(valuation(x,p),2),S))~;
}

bnfquadunram(K,S)=
{
 my(Clcyc=K.clgp.cyc,Clgen=K.clgp.gen,U,SU,A,Sel);
 U=Mod(concat([[K.tu[2]],K.fu]),K.pol);
 SU=Mod(bnfsunit(K,S)[1],K.pol);
 A=matrix(#S,#SU,i,j,Mod(idealval(K,SU[j],S[i]),2)); \\ Matrix of valuations of S-units
 A=matindexrank(A)[2]; \\ Indices of S-units generating SU/(even vals)
 SU=vector(#A,i,SU[A[i]]);
 Sel=List();
 for(i=1,#Clcyc,
  if(Clcyc[i]%2,break);
  listput(Sel,nfbasistoalg(K,bnfisprincipal(K,idealpow(K,Clgen[i],Clcyc[i]))[2]))
 );
 concat([U,SU,Vec(Sel)]);
}
