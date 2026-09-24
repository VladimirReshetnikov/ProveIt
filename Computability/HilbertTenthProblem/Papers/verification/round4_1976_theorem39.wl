(* Numerical instance of Theorem 3.9 of Jones-Sato-Wada-Wiens (1976), k = 1.
   Necessity direction: build n, x, w, M, A, B, CC, K, L, R, S exactly as in the
   proof of necessity and verify the key inequality (XIV),
      (R / ((CC/(K L) - (w+1) x) (1 - R/CC)^2 L) - (S+1))^2 < 1/4,
   for the prime k+1 = 2.  The Pell numbers K and CC have about 87 million
   decimal digits; only exact integer arithmetic and high-precision N[] are
   used.  Run:  wolfram -script round4_1976_theorem39.wl   (needs ~1 GB RAM). *)
k = 1;
UU[x_, y_] := (x + 2)^3 (x + 4) (y + 1)^2 + 1;
psi[A_, m_] := Module[{a = 0, b = 1}, If[m == 0, Return[0]]; Do[{a, b} = {b, 2 A b - a}, {m - 1}]; b];
squareQ[v_] := IntegerQ[Sqrt[v]];
fail[msg_] := (Print["FAIL: ", msg]; Exit[1]);
(* (I): U(2k, n) square; the least admissible n for k = 1 is 244 (Lemma 2.3 with e = 4). *)
n = psi[2 k + 3, 2 k + 2]/(2 k + 2) - 1;
If[! IntegerQ[n] || ! squareQ[UU[2 k, n]], fail["(I)"]];
(* (II): U(2n, x) square; take the least Pell solution with 2n+2 | second coordinate. *)
x = psi[2 n + 3, 2 n + 2]/(2 n + 2) - 1;
If[! IntegerQ[x] || ! squareQ[UU[2 n, x]], fail["(II)"]];
Print["n = ", n, ",  x has ", IntegerLength[x], " digits"];
(* w from Floor[(x+1)^n / x^k] = Binomial[n,k] + (w+1) x *)
fl = Quotient[(x + 1)^n, x^k];
w = (fl - Binomial[n, k])/x - 1;
If[! IntegerQ[w] || w < 0, fail["w"]];
M = 16 n x (w + 2) + 1;              (* III *)
A = M (x + 1);                        (* IV *)
B = n + 1;                            (* V *)
S = k! - 1;                           (* XXI with z = 0 *)
Print["M has ", IntegerLength[M], " digits"];
t0 = AbsoluteTime[];
K = psi[M, n - k + 1];                (* XV, XVIII with p = 0 *)
L = psi[M x, k + 1];                  (* XVI, XIX with l = 0 *)
R = psi[M n x, k + 1];                (* XVII, XX with r = 0 *)
CC = psi[A, B];                        (* VII-XIII via Lemma 3.8; CC because C is Protected *)
Print["K has ", IntegerLength[K], " digits, CC has ", IntegerLength[CC], " digits; Pell time ", Round[AbsoluteTime[] - t0], " s"];
If[L != 2 M x || R != 2 M n x, fail["L or R"]];
(* sigma' = CC/(K L) - (w+1) x, computed from the exact integer numerator *)
num = CC - (w + 1) x K L;
den = K L;
sigmaP = N[num, 200]/N[den, 200];
oneMinus = N[CC - R, 200]/N[CC, 200];   (* 1 - R/CC *)
beta = (R/L)/(sigmaP oneMinus^2);      (* R/L = n exactly *)
Print["sigma' = ", N[sigmaP, 30], "   (Binomial[n,k] = ", Binomial[n, k], ")"];
Print["1 - R/CC = ", N[oneMinus, 30]];
Print["beta = ", N[beta, 30], "   k! = ", k!];
If[(beta - (S + 1))^2 < 1/4, Print["PASS: (XIV) holds, |beta - k!| = ", N[Abs[beta - k!], 10]], fail["(XIV)"]];
(* also the Case-1 bounds (15): 4 < sigma' < x/2, and (17): R/CC < 1/4 *)
If[! (4 < sigmaP < x/2), fail["(15)"]];
If[! (N[R, 50]/N[CC, 50] < 1/4), fail["(17)"]];
Print["PASS: (15) and (17) hold"];
Export[FileNameJoin[{DirectoryName[$InputFileName], "round4_1976_theorem39_results.json"}],
  <|"status" -> "PASS", "k" -> k, "n" -> n, "digits" -> <|"x" -> IntegerLength[x], "M" -> IntegerLength[M],
    "K" -> IntegerLength[K], "CC" -> IntegerLength[CC]|>, "sigma_prime" -> ToString[N[sigmaP, 20]],
    "beta" -> ToString[N[beta, 20]]|>, "JSON"];
