{
hypernbmod(f,p)=
 p+1+sum(i=0,p-1,kronecker(liftint(subst(f,variable(f),Mod(i,p))),p));
}
