(* Sparse Hahn-polynomial demonstration. Not a full surreal-number package.
   Coefficients: exact Gaussian rationals. Exponents: Q^r, lexicographic order.
   Use the constructors; raw HData and RData expressions are internal data.
   No definitions are attached to System`Plus, Times, Power, N, or NumericQ. *)
BeginPackage["SurrealCASCore`"];
HData::usage = "Internal immutable sparse data HData[rank, terms].";
RData::usage = "Internal fraction data RData[numerator, denominator].";
HCreate::usage = "HCreate[{{exponentVector, coefficient},...}, rank] validates and normalizes a finite sum.";
HAdd::usage = "HAdd[a,b] adds finite sums of the same rank.";
HNegate::usage = "HNegate[a] negates a finite sum.";
HMultiply::usage = "HMultiply[a,b] multiplies finite sums of the same rank.";
HPower::usage = "HPower[a,n] computes a nonnegative integer power.";
HConjugate::usage = "HConjugate[a] conjugates Gaussian-rational coefficients.";
HValuation::usage = "HValuation[a] returns the least exponent, or Infinity for zero.";
HLeadingCoefficient::usage = "HLeadingCoefficient[a] returns the leading coefficient, or 0 for zero.";
HCompareReal::usage = "HCompareReal[a,b] returns -1,0,1, or Failure when an input is nonreal.";
RCreate::usage = "RCreate[a,b] represents a/b without expanding an infinite Hahn tail.";
RAdd::usage = "RAdd[a,b] adds fraction objects.";
RMultiply::usage = "RMultiply[a,b] multiplies fraction objects.";
RInverse::usage = "RInverse[a] inverts a nonzero fraction object.";
REqual::usage = "REqual[a,b] decides equality of same-rank fraction objects by cross multiplication.";
RValuation::usage = "RValuation[a] subtracts numerator and denominator valuations.";
Begin["`Private`"];
ratQ[x_] := MatchQ[x, _Integer | _Rational];
gaussianQ[x_] := ratQ[Re[x]] && ratQ[Im[x]];
fail[tag_] := Failure[tag, <||>];
lexLess[a_List,b_List] := Module[{p},
  p = Select[Range[Length[a]], a[[#]] =!= b[[#]] &, 1];
  If[p === {}, False, a[[First[p]]] < b[[First[p]]]]];
HCreate[terms_List,r_Integer] /; r > 0 := Module[{g, s},
  If[!AllTrue[terms, ListQ[#] && Length[#] == 2 && ListQ[#[[1]]] &&
      Length[#[[1]]] == r && AllTrue[#[[1]], ratQ] && gaussianQ[#[[2]]] &],
    Return[fail["InvalidTerms"]]];
  g = GatherBy[terms, First];
  s = ({#[[1,1]], Total[#[[All,2]]]} &) /@ g;
  s = Select[s, Last[#] =!= 0 &];
  HData[r, Sort[s, lexLess[First[#1], First[#2]] &]]];
HCreate[___] := fail["InvalidArguments"];
validQ[h_HData] := Length[h] == 2 && IntegerQ[h[[1]]] && h[[1]] > 0 &&
  ListQ[h[[2]]] && SameQ[HCreate[h[[2]],h[[1]]],h];
validQ[_] := False;
pairQ[a_,b_] := validQ[a] && validQ[b] && a[[1]] == b[[1]];
zeroQ[h_] := h[[2]] === {};
HAdd[a_,b_] := If[pairQ[a,b], HCreate[Join[a[[2]],b[[2]]],a[[1]]],
  fail["InvalidOrMismatchedDomain"]];
HNegate[a_] := If[validQ[a], HCreate[({First[#],-Last[#]}&)/@a[[2]],a[[1]]],
  fail["InvalidData"]];
HMultiply[a_,b_] := If[pairQ[a,b],
  HCreate[Flatten[Table[{u[[1]]+w[[1]],u[[2]] w[[2]]},
    {u,a[[2]]},{w,b[[2]]}],1],a[[1]]], fail["InvalidOrMismatchedDomain"]];
HPower[a_,n_Integer] /; n >= 0 := If[validQ[a],
  Nest[HMultiply[#,a]&,HCreate[{{ConstantArray[0,a[[1]]],1}},a[[1]]],n],
  fail["InvalidData"]];
HPower[___] := fail["NonnegativeIntegerPowerRequired"];
HConjugate[a_] := If[validQ[a],
  HCreate[({First[#],Conjugate[Last[#]]}&)/@a[[2]],a[[1]]], fail["InvalidData"]];
HValuation[a_] := If[validQ[a],If[zeroQ[a],Infinity,a[[2,1,1]]],fail["InvalidData"]];
HLeadingCoefficient[a_] := If[validQ[a],If[zeroQ[a],0,a[[2,1,2]]],fail["InvalidData"]];
HCompareReal[a_,b_] := Module[{d},
  If[!pairQ[a,b],Return[fail["InvalidOrMismatchedDomain"]]];
  If[!AllTrue[Join[a[[2]],b[[2]]],Im[Last[#]] === 0 &],
    Return[fail["NonrealInput"]]];
  d=HAdd[a,HNegate[b]]; Sign[HLeadingCoefficient[d]]];
RCreate[a_,b_] := If[!pairQ[a,b],fail["InvalidOrMismatchedDomain"],
  If[zeroQ[b],fail["ZeroDenominator"],RData[a,b]]];
rvalidQ[x_RData] := Length[x] == 2 && pairQ[x[[1]],x[[2]]] && !zeroQ[x[[2]]];
rvalidQ[_] := False;
rpairQ[a_,b_] := rvalidQ[a] && rvalidQ[b] && a[[1,1]] == b[[1,1]];
RAdd[a_,b_] := If[rpairQ[a,b],
  RCreate[HAdd[HMultiply[a[[1]],b[[2]]],HMultiply[b[[1]],a[[2]]]],
    HMultiply[a[[2]],b[[2]]]],fail["InvalidOrMismatchedDomain"]];
RMultiply[a_,b_] := If[rpairQ[a,b],
  RCreate[HMultiply[a[[1]],b[[1]]],HMultiply[a[[2]],b[[2]]]],
  fail["InvalidOrMismatchedDomain"]];
RInverse[a_] := If[rvalidQ[a],RCreate[a[[2]],a[[1]]],fail["InvalidData"]];
REqual[a_,b_] := If[rpairQ[a,b],
  SameQ[HMultiply[a[[1]],b[[2]]],HMultiply[b[[1]],a[[2]]]],
  fail["InvalidOrMismatchedDomain"]];
RValuation[a_] := If[rvalidQ[a],If[zeroQ[a[[1]]],Infinity,
  HValuation[a[[1]]]-HValuation[a[[2]]]],fail["InvalidData"]];
End[];
EndPackage[];
