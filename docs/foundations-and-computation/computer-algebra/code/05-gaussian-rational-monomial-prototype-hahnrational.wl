(* HahnRational.wl -- exact rational monomial prototype, 2026-09-21.
   Coefficients: Q(i). Value group: Z^rank with lexicographic order.
   Variables are listed from the most significant valuation coordinate
   to the least. For {u,t}, u is smaller than every positive power of t.
   Construct objects only with HCreate; direct HR expressions are private
   implementation data. This is not an arbitrary Hahn/transseries engine. *)
BeginPackage["HahnRational`"];
HCreate::usage = "HCreate[{u,t,...},r] constructs an exact rational monomial value over Q(i).";
HExpression::usage = "HExpression[a] returns the rational expression; variables retain their declared interpretation.";
HVariables::usage = "HVariables[a] gives the ordered monomial variables.";
HAdd::usage = "HAdd[a,b] adds values with identical parents.";
HMul::usage = "HMul[a,b] multiplies values with identical parents.";
HInv::usage = "HInv[a] inverts a nonzero value.";
HPower::usage = "HPower[a,n] computes an integer power.";
HScale::usage = "HScale[a,c] multiplies by c in Q(i).";
HEqualQ::usage = "HEqualQ[a,b] decides equality within a common parent.";
HZeroQ::usage = "HZeroQ[a] decides whether a is zero.";
HValuation::usage = "HValuation[a] gives the least exponent vector, or Infinity for zero.";
HLeadingCoefficient::usage = "HLeadingCoefficient[a] gives its initial coefficient (zero for zero).";
HConjugate::usage = "HConjugate[a] conjugates coefficients, fixing monomials.";
HRe::usage = "HRe[a] gives the real part.";
HIm::usage = "HIm[a] gives the imaginary part.";
HNormSquared::usage = "HNormSquared[a] returns a Conjugate[a], without requiring a square root.";
HSign::usage = "HSign[a] decides the sign of a real value; nonreal input is rejected.";
HCompare::usage = "HCompare[a,b] returns -1, 0 or 1 for real values in one parent.";
HStandardPart::usage = "HStandardPart[a] extracts the standard part of a finite value; infinite input is rejected.";
Begin["`Private`"];

fail[tag_, text_] := Failure[tag, <|"MessageTemplate" -> text|>];
gaussianQ[c_] := MatchQ[c, _Integer | _Rational |
    Complex[_Integer | _Rational, _Integer | _Rational]];
vectorSign[v_List] := With[{nz = Select[v, # != 0 &]},
  If[nz === {}, 0, Sign[First[nz]]]];
polyLeading[p_, vars_List] := First[SortBy[CoefficientRules[Expand[p], vars], First]];
polyConjugate[p_, vars_List] := Total[
  (Conjugate[Last[#]] Times @@ MapThread[Power, {vars, First[#]}]) & /@
    CoefficientRules[Expand[p], vars]];
sameParent[a_HR, b_HR] := SameQ[a[[1]], b[[1]]];
parentFailure[] := fail["ParentMismatch", "Monomial variables and their order must agree."];

HCreate[vars_List, expr_] := Module[{r, n, d, cs, c},
  If[vars === {} || !VectorQ[vars, MatchQ[#, _Symbol] &] ||
     Length[DeleteDuplicates[vars]] != Length[vars],
    Return[fail["InvalidParent", "Use a nonempty list of distinct unassigned symbols."]]];
  r = Quiet[Check[Cancel[Together[expr]], $Failed]];
  If[r === $Failed, Return[fail["InvalidExpression", "Rational normalization failed."]]];
  n = Numerator[r]; d = Denominator[r];
  If[!PolynomialQ[n, vars] || !PolynomialQ[d, vars] || TrueQ[d === 0],
    Return[fail["NotRational", "Input must be a rational function of the declared variables."]]];
  cs = Join[Last /@ CoefficientRules[n, vars], Last /@ CoefficientRules[d, vars]];
  If[!AllTrue[cs, gaussianQ],
    Return[fail["CoefficientDomain", "Only exact rational and Gaussian rational coefficients are supported."]]];
  If[TrueQ[n === 0], Return[HR[vars, 0, 1]]];
  c = Last[polyLeading[d, vars]];
  HR[vars, Expand[n/c], Expand[d/c]]
];
HCreate[___] := fail["InvalidInput", "Expected HCreate[variables, expression]."];
HVariables[a_HR] := a[[1]];
HExpression[a_HR] := a[[2]]/a[[3]];
HZeroQ[a_HR] := SameQ[a[[2]], 0];
HAdd[a_HR, b_HR] := If[sameParent[a,b],
  HCreate[a[[1]], HExpression[a] + HExpression[b]], parentFailure[]];
HMul[a_HR, b_HR] := If[sameParent[a,b],
  HCreate[a[[1]], HExpression[a] HExpression[b]], parentFailure[]];
HInv[a_HR] := If[HZeroQ[a], fail["DivisionByZero", "Cannot invert zero."],
  HCreate[a[[1]], a[[3]]/a[[2]]]];
HPower[a_HR, n_Integer] := If[n < 0 && HZeroQ[a],
  fail["DivisionByZero", "A negative power of zero is undefined."],
  If[n == 0, HCreate[a[[1]], 1], HCreate[a[[1]], HExpression[a]^n]]];
HScale[a_HR, c_?gaussianQ] := HCreate[a[[1]], c HExpression[a]];
HScale[a_HR, _] := fail["CoefficientDomain", "The scalar must belong to Q(i)."];
HEqualQ[a_HR, b_HR] := If[sameParent[a,b],
  TrueQ[Expand[a[[2]] b[[3]] - b[[2]] a[[3]]] === 0], parentFailure[]];
HValuation[a_HR] := If[HZeroQ[a], Infinity,
  First[polyLeading[a[[2]],a[[1]]]] - First[polyLeading[a[[3]],a[[1]]]]];
HLeadingCoefficient[a_HR] := If[HZeroQ[a], 0,
  Last[polyLeading[a[[2]],a[[1]]]]/Last[polyLeading[a[[3]],a[[1]]]]];
HConjugate[a_HR] := HCreate[a[[1]],
  polyConjugate[a[[2]],a[[1]]]/polyConjugate[a[[3]],a[[1]]]];
HRe[a_HR] := HScale[HAdd[a,HConjugate[a]], 1/2];
HIm[a_HR] := HScale[HAdd[a,HScale[HConjugate[a],-1]], 1/(2 I)];
HNormSquared[a_HR] := HMul[a,HConjugate[a]];
HSign[a_HR] := If[!TrueQ[HEqualQ[a,HConjugate[a]]],
  fail["Nonreal", "Surcomplex values have no compatible field ordering."],
  Sign[HLeadingCoefficient[a]]];
HCompare[a_HR, b_HR] := If[!sameParent[a,b], parentFailure[],
  If[!TrueQ[HEqualQ[a,HConjugate[a]]] || !TrueQ[HEqualQ[b,HConjugate[b]]],
    fail["Nonreal", "Only real values can be compared."],
    HSign[HAdd[a,HScale[b,-1]]]]];
HStandardPart[a_HR] := Module[{sgn},
  If[HZeroQ[a], Return[0]];
  sgn = vectorSign[HValuation[a]];
  Which[sgn > 0, 0, sgn == 0, HLeadingCoefficient[a], True,
    fail["InfiniteValue", "Standard part is defined here only for finite values."]]
];
End[];
EndPackage[];
