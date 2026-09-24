(* RationalHahn.wl -- exact, finite-rank ordered rational-function kernel.
   Variables {t1,...,td} denote Conway monomials with
   v(t1)=1, v(t2)=omega, ..., v(td)=omega^(d-1).
   Thus 0 < t[j+1] < t[j]^n for every positive ordinary integer n.
   Scope: rational coefficients only; no arbitrary Hahn streams, roots,
   transcendental functions, automatic numerical coercions, or global upvalues.
   All public arithmetic arguments must have been made with RHMake. *)
BeginPackage["RationalHahn`"];
RHData::usage = "RHData[variables,numerator,denominator] is private-format exact data; construct it with RHMake.";
RHMake::usage = "RHMake[p,q,variables] constructs p/q over Q in an ordered finite-rank monomial field.";
RHExpression::usage = "RHExpression[a] returns the ordinary rational-function expression, forgetting its monomial interpretation.";
RHAdd::usage = "RHAdd[a,b] adds objects in the same ordered monomial domain.";
RHNegate::usage = "RHNegate[a] negates a rational Hahn object.";
RHSubtract::usage = "RHSubtract[a,b] subtracts b from a.";
RHMultiply::usage = "RHMultiply[a,b] multiplies two objects in the same domain.";
RHInverse::usage = "RHInverse[a] inverts a nonzero object; zero gives Failure.";
RHSign::usage = "RHSign[a] returns -1, 0, or 1 exactly.";
RHCompare::usage = "RHCompare[a,b] returns the sign of a-b, or a domain Failure.";
RHLeadingData::usage = "RHLeadingData[a] returns {valuationVector,leadingCoefficient}; zero gives Missing.";
RHValuation::usage = "RHValuation[a] gives its exponent vector; zero gives the distinguished marker Infinity.";
RHStandardPart::usage = "RHStandardPart[a] returns an exact rational standard part for finite a, and Failure for infinite a.";
Begin["`Private`"];
rationalQ[c_] := IntegerQ[c] || Head[c] === Rational;
polyQ[p_, v_List] := PolynomialQ[p,v] &&
  AllTrue[Last /@ CoefficientRules[Expand[p],v], rationalQ];
validVarsQ[v_List] := Length[v] > 0 && DuplicateFreeQ[v] &&
  AllTrue[v, Head[#] === Symbol &];
RHMake[p_,q_,v_List] := Module[{r},
  If[!validVarsQ[v], Return[Failure["Variables",<|"MessageTemplate" ->
    "Use a nonempty list of distinct, unassigned symbols."|>]]];
  If[!polyQ[p,v] || !polyQ[q,v],
    Return[Failure["CoefficientDomain",<|"MessageTemplate" ->
      "Numerator and denominator must be polynomials with rational coefficients."|>]]];
  If[Expand[q] === 0, Return[Failure["ZeroDenominator",<||>]]];
  r = Cancel[p/q];
  RHData[v,Expand[Numerator[r]],Expand[Denominator[r]]]
];
RHExpression[RHData[_,p_,q_]] := p/q;
sameDomainQ[RHData[v_,_,_],RHData[w_,_,_]] := SameQ[v,w];
domainFailure[] := Failure["DomainMismatch",<|"MessageTemplate" ->
  "Explicitly embed both operands into the same ordered monomial domain."|>];
RHAdd[a_RHData,b_RHData] := If[sameDomainQ[a,b],
  RHMake[a[[2]] b[[3]]+b[[2]] a[[3]],a[[3]] b[[3]],a[[1]]],domainFailure[]];
RHNegate[a_RHData] := RHMake[-a[[2]],a[[3]],a[[1]]];
RHSubtract[a_RHData,b_RHData] := RHAdd[a,RHNegate[b]];
RHMultiply[a_RHData,b_RHData] := If[sameDomainQ[a,b],
  RHMake[a[[2]] b[[2]],a[[3]] b[[3]],a[[1]]],domainFailure[]];
RHInverse[a_RHData] := If[a[[2]] === 0,
  Failure["DivisionByZero",<||>],RHMake[a[[3]],a[[2]],a[[1]]];
(* Canonical Sort on lists of integers is lexicographic. Reversal makes
   the highest-rank exponent the first comparison coordinate. *)
leadingPolynomial[p_,v_List] := Module[{r},
  r = First[SortBy[CoefficientRules[p,v],Reverse[First[#]] &]];
  {First[r],Last[r]}
];
RHLeadingData[a_RHData] := Module[{lp,lq},
  If[a[[2]] === 0,Return[Missing["ZeroHasNoLeadingTerm"]]];
  lp=leadingPolynomial[a[[2]],a[[1]]];
  lq=leadingPolynomial[a[[3]],a[[1]]];
  {lp[[1]]-lq[[1]],lp[[2]]/lq[[2]]}
];
RHValuation[a_RHData] := If[a[[2]] === 0,Infinity,RHLeadingData[a][[1]]];
RHSign[a_RHData] := If[a[[2]] === 0,0,Sign[RHLeadingData[a][[2]]]];
RHCompare[a_RHData,b_RHData] := Module[{c=RHSubtract[a,b]},
  If[FailureQ[c],c,RHSign[c]]
];
vectorSign[v_List] := Module[{w=DeleteCases[Reverse[v],0]},
  If[w === {},0,Sign[First[w]]]
];
RHStandardPart[a_RHData] := Module[{ld,s},
  If[a[[2]] === 0,Return[0]];
  ld=RHLeadingData[a]; s=vectorSign[ld[[1]]];
  Which[s>0,0,s==0,ld[[2]],True,
    Failure["NotFinite",<|"MessageTemplate" ->
      "Standard part is defined here only for finite elements."|>]]
];
End[];
EndPackage[];
