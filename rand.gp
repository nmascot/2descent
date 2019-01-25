\\ couple of N(0, 1)
boxmuller() =
{ my(x1,x2,w);

  until(w && w < 1,
    x1 = 2*random(1.) - 1;
    x2 = 2*random(1.) - 1;
    w = x1^2+x2^2;
  );
  w = sqrt(-2*log(w)/w);
  [x1 * w, x2 * w];
}

minusexp()=log(random(1.)); \\ - exp law of param 1

randv(v,s=1,prec=10)=
\\ random v-adic number
{
 my(w);
 if(v==0,
  s*boxmuller()[1]
 ,
  w=round(s*boxmuller()[1]);
  v^w*(random(v^prec)+O(v^prec))
 );
}

randJcantor(v,f,s=1,prec=10)=
\\ Random point on Jac(y²=f)(Qv)
\\ Only returns U, where [U,V] is
\\ the Cantor rep of the point.
{
 my(x=variable(f),y,g,d,U);
 y=varlower("y",x);
 g=floor((poldegree(f)-1)/2);
 while(1,
  iferr(
   d=1+random(g);
   U=x^d+Pol(vector(d,i,randv(v,s,prec)),x);
   fa=factor(polresultant(U,y^2-f,x))[,1]~;
   if(vector(#fa,i,fa[i]==subst(fa[i],y,-y))==0,
    return(liftint(U))
   )
  ,E,print("arghhh!");return([]);,Vec(E)[1..5]==["e_DOMAIN", "factorpadic", "precision", "<=", 0])
 );
}

