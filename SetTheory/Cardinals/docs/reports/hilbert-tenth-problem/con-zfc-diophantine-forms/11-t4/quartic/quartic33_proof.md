# A new 33-variable quartic, without the relaxed strong-norm lemma

Final combined instance: use the complete four-port T4 tuple in ../bridge/T4_CONSTANTS.json. Its full compiler contract and canonical rank R = 3 modulo 4 are proved in ../bridge/BRIDGE_AUDIT.md. Historical packet06/08 coefficient discussions below document the derivation or a separate fallback, not a license to mix numerical ports. The arithmetic and witness arguments are unchanged.

## Result

The construction below has 33 strictly positive integer unknowns and 24 quadratic equations. Their sum of squared residuals is an explicit polynomial of exact degree four. It is an improvement on the pinned packet 08's 34-variable, 25-equation lift. This is an upper bound, not an optimality claim.

For the exact four Start-only coefficients in packet 08, the system has a positive solution if and only if the packet's six-equation normalized-strong system does. Consequently it inherits the packet's mathematical theorem

ZFC proves: no positive integer solution if and only if Con(ZFC).

This does not prove nonexistence. The new step is an elementary exact algebraic equivalence and positivity proof. It does not depend on the separate relaxed Pell-rank theorem needed to replace the normalized strong norm by the weaker ordinary strong norm. The upstream machine/compiler/Pell correctness chain remains an imported mathematical dependency, not a newly compiled proof-assistant certificate.

## Source and exact coefficient contract

Repository: VladimirReshetnikov/ProveIt.
Pinned containing commit: 3b201cdea32d2c816f5f3d20734051f25fd3ef14.
Packet: SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/08-start-only67.

Primary source:
https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/08-start-only67/diophantine_zfc.tex

Exact old object:
https://github.com/VladimirReshetnikov/ProveIt/blob/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/08-start-only67/evidence/diophantine_zfc_encoding/start_only_quartic34.json

Use beta=Bm1, K=Kconstant, MC=MC, MF=MF_native+B−1 from that packet's Start/forbidden-window coefficient ordering. K is a fixed coefficient, not the norm auxiliary A. These four integers are specified by a total bounded compiler, not by waiting for a machine to halt. The packet internally pins its machine evidence to cdd582bec13f908df3711fa9e05d1ddac368a5db. Do not confuse the containing commit with that internal source pin.

The algebra below is coefficient-agnostic. Another packet's compiler may be used only after separately establishing its exact six-equation core theorem and matching all four coefficient conventions; interchangeable notation alone is not sufficient. In particular a fully proved raw-blank compiler contract can replace packet 08's input-erasing compiler. The required contract includes Start/impossible-selector semantics, carry and mask decoding, helical soundness and completeness, and the K215 endpoint, not just numerical inequalities. Its elementary port bounds are beta>=15, K>0, 0<MC<beta and beta<MF<2 beta. The exact lifting argument below works for every such coefficient quadruple; its final consistency interpretation additionally requires the complete compiler theorem.

## All unknowns and all equations

Every coordinate is in Z_{>0}. The 33 coordinates are

J,F,alpha,z,f,h,i,o,s,w,tau,eta,zeta,y,gamma,
N,E,P,c,a,X,D,A,G,L,R,V,g,I,B,U,H,j.

Only q=beta J+1 and k=eta+zeta are abbreviations, not new coordinates. The equations, in order, are:

1. L=q²−1.
2. N=(L+1)q.
3. X=wq.
4. a=E+Ns.
5. E=X(a−E).
6. c=eta+(a−E)k.
7. P=E(c−eta)+k.
8. tau²=P(P−k)+1.
9. D=X+ac+gamma(4a+3).
10. A=D²−1.
11. U=(a+1)c.
12. A=U(U+2c).
13. k=Eh+R+1.
14. G=(q−1)(q−F)+alpha.
15. R=GL+J(MC+q MF).
16. (K+w)(q−F−alpha)+q−F−z(q−1)=1.
17. H=(a+1)(f−1).
18. V=of−c.
19. V=jc−R.
20. g=y²−V².
21. I=Ai.
22. B=I².
23. B=H(H+2a+2f+4).
24. y²−Bg=1.

Let r_l be left minus right for line l, after replacing q and k by their linear definitions. Then Q_33=sum_{l=1}^{24} r_l² is the promised single explicit quartic. The JSON file quartic33_normalized.json gives every expanded residual. All residuals have degree at most two. The coefficient of tau^4 is exactly one, since tau occurs in only line 8. Hence the degree is exactly four.

## Why this saves a variable

Put Delta=a²+4a+3=(a+1)(a+3) for this proof only.

The old main-norm block used three equations

Delta=a²+4a+3, C2=c², A=C2 Delta.

The new block uses two:

U=(a+1)c, A=U(U+2c).

Indeed U(U+2c)=(a+1)(a+3)c²=Delta c². This saves one coordinate and one equation, while retaining A for the normalized strong coefficient I=Ai.

The old strong/quotient block depended on F2=f² and V0=o_merged f−1. To remove Delta without restoring a coordinate elsewhere, use

H=(a+1)(f−1),
H+2a+2f+4=(a+3)(f+1),
H(H+2a+2f+4)=Delta(f²−1).

Thus H replaces F2, and two independent positive quotient coordinates o,j replace o_merged,V0. Their counts balance. The net reduction remains one coordinate and one equation.

## Map from the new system to the packet's core

From lines 10–12, A=Delta c² and D²−Delta c²=1. Lines 21–23 give

Delta² c^4 i²=I²=B=Delta(f²−1).

Since Delta>0, cancellation gives exactly the normalized strong relation

f²−1=Delta i² c^4.

In particular f²≡1 (mod c). Lines 18 and 19 yield of+R=(j+1)c. Multiplying this congruence by f gives

o+Rf≡0 (mod c).

Consequently o_merged=(o+Rf)/c is a strictly positive integer. Then

c(o_merged f−1)−Rf²=of−c=V.

Lines 20 and 24 give B(V²−y²)+y²=1, and B=(i Delta c²)². All other equations are unchanged from packet 08's quadratic lift, and hence yield its six comparisons. Nothing is inferred from merely allowing a signed auxiliary: all coordinates used here are positive.

## Map from the packet's core to the new system

Here is a direct positivity argument, so the lift is not restricted to the packet 08 backend. Let C=q−F−alpha. Transport=1 gives (K+w)C=F+(z−1)(q−1)>0, so C>0. Hence G=(q−1)C+q alpha>0. Since F,C,alpha>=1, G<=q²−q−1. The stated mask bounds give 0<J(MC+q MF)<(q−1)(1+2q), and consequently 0<R<q⁴−q³. Meanwhile Y=sq³, X=wq, E=XY>=q⁴ and a=E+Y, so Delta>R. Also c=kY+eta>2, and the normalized strong identity gives f²=1+Delta i²c⁴, hence f>c²>2c.

Write B=(i Delta c²)²=Delta(f²−1). Then B−(Rf²+c)=(Delta−R)f²−Delta−c>0. The auxiliary norm is B V²−(B−1)y²=1. It excludes V=0, while V≡−c mod f and f>2c exclude V=±1. For v=|V|>1, v²−1=(B−1)(y²−v²) forces v>=2B−1. But V=c(o_merged f−1)−Rf²>−(Rf²+c)>−B, excluding negative V. Thus V>1, y>V and g=y²−V²>0. Every other old lift coordinate is manifestly positive.

Retain the common coordinates, replace Delta,C2,F2 by

U=(a+1)c,
H=(a+1)(f−1),

and replace o_merged,V0 by

o=c o_merged−Rf,
j=o_merged f−R Delta i² c³−1.

Both are integers. The strong relation shows

of=V+c>0,
jc=V+R>0.

Thus o,j are strictly positive. Also U,H>0. Direct substitution proves every new equation. All other coordinates retain the positivity established in the source packet. The two maps are inverse on their common coordinates, and the quotient recovery is exact; no fresh computation tableau or relaxed rank argument is needed.

## Domain variants and verification

Replacing each positive coordinate x by n_x+1 gives 33 nonnegative unknowns and degree four. Replacing it by 1+u_x²+v_x²+r_x(r_x+1) gives 99 unrestricted integer unknowns and degree eight. This form is always positive and represents every positive integer: apply the three-square theorem to 4n+1, whose representation has exactly one odd coordinate and two even coordinates. Simply admitting signed values to the 33 original ports is not justified.

audit_quartic33.py is independently authored and uses SymPy only for polynomial identities, coordinate/equation counts, degree bounds, and the tau^4 coefficient. No downloaded repository Python was executed. quartic33_audit.json records the passing checks. The unbounded equivalence and positivity arguments are the mathematics above, not consequences of bounded testing.
