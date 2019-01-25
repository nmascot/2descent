EqnMat(A)=matker(A~)~; \\ Linear equations defining the image of A

ColAppend(A,C)=
/*
Given a matrix A whose columns are lin. independent
and a column C of the same size as those of A,
returns [A cat C, 1] if C is not in the span of the columns of A,
[A,0] else. */
{
 my(AC);
 AC=matconcat([A,C]);
 if(#matker(AC),
  [A,0]
 ,
  [AC,1]
 );
}

