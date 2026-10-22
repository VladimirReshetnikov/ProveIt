# The direct ordinary-strong quartic: 33 positive variables, 24 quadratics

Final combined instance: use the complete four-port T4 tuple in ../bridge/T4_CONSTANTS.json. Its full compiler contract and canonical rank R = 3 modulo 4 are proved in ../bridge/BRIDGE_AUDIT.md. Historical packet06/08 coefficient discussions below document the derivation or a separate fallback, not a license to mix numerical ports. The arithmetic and witness arguments are unchanged.

## Coefficient contract and theorem scope

Fix a fully proved compatible blank-input native compiler, with four exact integer ports beta=B−1, K=DC+B DR, MC=native low mask, and MF=native high mask+B−1. The contract must establish the Start/impossible-selector interpretation, carry isolation, field masks, canonical mass and population bounds, helical soundness and completeness, and the connection to raw K215 blank halting. The numerical facts B≥16, K>0, 0<MC<B−1, and 0<MF−(B−1)<B−1 are necessary bounds used below, but are not by themselves this compiler theorem.

The authenticated raw-blank fallback is packet 06 at ProveIt commit 3b201cdea32d2c816f5f3d20734051f25fd3ef14. Its complete recipe is the packet's data/k215_constants.json plus code/blank_helical.py and code/compiler_constants.py, with proof interfaces proofs/blank_helical_proof.md and proofs/pell_lemma_audit.md. Its original machine/Pell evidence is pinned internally to cdd582bec13f908df3711fa9e05d1ddac368a5db. A newly checked smaller raw-blank compiler satisfying the same complete contract may replace these four ports together; no arithmetic formula below changes.

Source packet URL:
https://github.com/VladimirReshetnikov/ProveIt/tree/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67

The ordinary-strong core also imports the relaxed Pell-rank lemma. It is not obtained by unconditionally cancelling Delta from a square. Once that core theorem is established, the lift below is an exact positive-solution equivalence. For a compatible K215 compiler it follows, formalizably in ZFC, that absence of solutions is equivalent to Con(ZFC). No nonexistence claim or global optimality claim is made.

## Complete explicit system

All 33 coordinates are strictly positive integers:

J,F,alpha,z,f,h,i,o,s,w,tau,eta,zeta,y,gamma,
N,E,P,c,a,X,D,C2,G,L,R,F2,V0,V,g,I,Baux,Delta.

Only q=beta J+1 and k=eta+zeta are linear abbreviations. The 24 equations are:

1. L=q²−1.
2. N=(L+1)q.
3. X=wq.
4. a=E+Ns.
5. E=X(a−E).
6. c=eta+(a−E)k.
7. P=E(c−eta)+k.
8. tau²=P(P−k)+1.
9. D=X+ac+gamma(4a+3).
10. Delta=a²+4a+3.
11. C2=c².
12. D²−1=C2 Delta.
13. k=Eh+R+1.
14. G=(q−1)(q−F)+alpha.
15. R=GL+J(MC+q MF).
16. (K+w)(q−F−alpha)+q−F−z(q−1)=1.
17. F2=f².
18. V0=of−1.
19. V=cV0−RF2.
20. g=y²−V².
21. I=C2 i.
22. Baux=I².
23. Baux=Delta(F2−1).
24. y²−Baux g=1.

The JSON uses the short coordinate name B for Baux. It is unrelated to the fixed radix B used in the coefficient contract.

Let r_j be left minus right in each line, substituting the linear q,k. Then Q=sum_{j=1}^{24}r_j² is a single explicit quartic. Every residual has degree at most two, and only residual 8 contains tau, so the coefficient of tau⁴ is one. The degree is exactly four.

Relative to the old 34-variable normalized lift, the ordinary coefficient uses I=C2 i instead of I=A i. The norm auxiliary A is therefore unnecessary: its two equations A=D²−1 and A=C2 Delta collapse to line 12. This is the entire one-coordinate, one-equation saving in this presentation.

## Exact core obtained by projection

The first seven equations enforce the polynomial definitions

Y=sq³, X=wq, E=XY, a=E+Y, c=kY+eta,
P=E(kY)+k.

The remaining definition equations enforce

Delta=a²+4a+3,
D=X+ac+gamma(4a+3),
R=[(q−1)(q−F)+alpha](q²−1)+J(MC+q MF),
V=c(of−1)−Rf²,
I=ic²,
Baux=I².

The six nondefinitional equations become exactly

tau²−(EkY)(EkY+k)=1,
D²−Delta c²=1,
Baux(V²−y²)+y²=1,
k−Eh−R=1,
(K+w)(q−F−alpha)+q−F−z(q−1)=1,
(ic²)²=Delta(f²−1).

Thus every positive solution of the quadratic system projects to the ordinary-strong core with identical original coordinates. The converse assigns each displayed auxiliary its polynomial value. Its only nontrivial issue is positivity, proved next.

## Positive lifting, without circular assumptions

Set C=q−F−alpha and A0=a+2, so Delta=A0²−1. From transport=1, K+w>0 and q>1 one gets

(K+w)C=F+(z−1)(q−1)>0,

so C>0. Therefore G=(q−1)C+q alpha>0. The authentic mask bounds give q(q²−1)<R<q⁴−2, and E≥q⁴, hence a>R+2 and Delta>R.

Before the ordinary auxiliary norm is used, the first and main Pell norms give positive indices n,p with

tau=chi_{2XY²+1}(n), k=2 psi_{2XY²+1}(n),
D=chi_A0(p), c=psi_A0(p).

The index equation, the congruence 2XY²+1≡1 mod E, and the bounds above give n≥(R+1)/2≥24. Since 2XY²+1>A0 and c>k, Pell growth gives p>n and c>A0 Delta². This is established before any auxiliary positivity or desired equality p=R.

The strong equation yields f²=1+i²c⁴/Delta. With c>A0 Delta² and Delta<A0², it follows that f>2c and f²>Delta+c. Hence

Baux−(Rf²+c)=(Delta−R)f²−Delta−c>0.

The auxiliary equation is Baux V²−(Baux−1)y²=1, with Baux=(ic²)²>1. V cannot be zero. Since V≡−c mod f and f>2c>4, V cannot be ±1. For v=|V|>1, the identity

v²−1=(Baux−1)(y²−v²)

forces y≥v+1 and then v≥2Baux−1. But o>0 gives V>−(Rf²+c)>−Baux. This excludes negative V, so V>1. The same identity gives g=y²−V²>0. Also f>1 implies V0=of−1>0. Every other added coordinate is manifestly positive. This completes the exact positive lift.

The relaxed rank lemma is not needed merely for these positivity estimates, but is essential to the core's computation-soundness proof. Its premises are A0≥2, c=psi_A0(p)>A0 Delta² and (ic²)²=Delta(f²−1); its conclusions are f=chi_A0(m), p|m, c|m, and ic²=Delta psi_A0(m) for some m>0. In particular c² divides f²−1. These supply the two auxiliary quotient congruences and the signed Pell step-down needed to recover p=R. Dividing i by Delta without this argument is not valid.

The rank proof factors Delta into squarefree part times a square, uses the least positive integer-coefficient Pell unit, and applies strong divisibility of the Pell sequence. A proper divisor rank would force simultaneously h≥c/Delta and 2h²<A0 c, contrary to c>A0 Delta². The final binomial expansion gives c|m. It is written out in the accompanying combined-core proof and pinned upstream source:
https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md

## Formal and computational boundary

audit_quartic33_ordinary.py is newly authored, reads no upstream executable source, and checks all 24 symbolic substitution identities, counts, degrees, and the tau⁴ coefficient. Its receipt is quartic33_ordinary_audit.json. These checks certify algebra, not the unbounded compiler/Pell theorem.

For nonnegative coordinates, replace every positive variable by n+1, preserving 33 variables and degree four. An elementary unrestricted-integer conversion replaces x by 1+u²+v²+r(r+1). This positive polynomial represents every positive integer by the three-square theorem, giving 99 integer unknowns and degree eight. The original 33 signed ports are not claimed sound.
