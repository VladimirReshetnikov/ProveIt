(* Independent fixed Gaussian cubature for the positive double-Laplace
   representation. Stable sinh quotients avoid small-argument cancellation.
   Node refinement is diagnostic, not a rigorous quadrature error bound. *)
ClearAll[gauss,ff,kk,hh,integral,v,z];
gauss[n_]:=Module[{mat,eval,evec,order},
 mat=N[SparseArray[{Band[{1,2}]->Table[j/Sqrt[4 j^2-1],{j,1,n-1}],Band[{2,1}]->Table[j/Sqrt[4 j^2-1],{j,1,n-1}]},{n,n}],65];
 {eval,evec}=Eigensystem[Normal[mat]];order=Ordering[eval];
 Transpose[{(eval[[order]]+1)/2,evec[[order,1]]^2}]];
rules=Association[Table[n->gauss[n],{n,{64,96}}]];
ff[a_,t_]:=-t Exp[-a t/2]Sinh[(a-1)t/2]/Sinh[t/2];
kk[a_,t_]:=1/(4 Sinh[t/2]^2)+a(1+Coth[t/2])/4;
hh[a_,t_,z_]:=t ff[a,t z]ff[a,t(1-z)]kk[a,t];
cut=200;segments=Partition[{0,1,4,16,64,cut},2,1];
integral[a_,n_]:=Module[{nodes=rules[n],sum=0,left,right,vv,zz},
 Do[left=seg[[1]];right=seg[[2]];
  sum+=Sum[vv=left+(right-left)nodes[[i,1]];zz=nodes[[j,1]]/2;
   (right-left)nodes[[i,2]]nodes[[j,2]]hh[a,vv,zz],{i,1,n},{j,1,n}],{seg,segments}];sum];
(* z -> 1-z symmetry accounts for the half-interval Jacobian: 2*(1/2)=1. *)
rows=Table[coarse=integral[N[a,65],64];fine=integral[N[a,65],96];
 target=(a-1)PolyGamma[2,a]/4+(PolyGamma[1,a]-Zeta[2])/2+3(a-1)Zeta[3]/2;
 err=Abs[fine-N[target,65]];diff=Abs[fine-coarse];
 mu=Min[a,1];mm=Max[1,Abs[a-1]];
 bound=mm^2(1+a)Exp[-mu cut](cut^3/mu+3cut^2/mu^2+6cut/mu^3+6/mu^4)/6;
 Print["Gauss shift ",a," residual ",InputForm[err]," refinement ",InputForm[diff]];
 <|"shift"->ToString[a,InputForm],"absolute_residual"->ToString[err,InputForm],"refinement_difference"->ToString[diff,InputForm],"analytic_outer_tail_bound"->ToString[N[bound,65],InputForm],"passed"->TrueQ[err<10^-24&&diff<10^-24&&bound<10^-30]|>,{a,{1/2,3/2,4/3,1+Sqrt[2]}}];
record=<|"engine"->$Version,"working_precision"->65,"Gauss_orders"->{64,96},"outer_cutoff"->cut,"rows"->rows,"all_pass"->And@@Lookup[rows,"passed"],"interval_certified"->False,"scope"->"Fixed Golub-Welsch Legendre rules and stable sinh integrand; independent positive double-Laplace quadrature of four trigamma-square values, with node refinement and a proved exponential truncation bound. Refinement and floating residuals do not certify interval accuracy."|>;
Export[FileNameJoin[{DirectoryName[$InputFileName],"dougall-gauss-native.json"}],record,"RawJSON"];
Exit[If[TrueQ[record["all_pass"]],0,1]];
