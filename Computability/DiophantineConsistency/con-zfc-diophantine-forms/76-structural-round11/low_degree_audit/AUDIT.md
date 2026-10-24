# Independent audit of the round-11 low-degree and positive equations

## Verdict and scope

**PASS for all nine submitted constructions: seven unrestricted-integer packets and two strictly-positive packets.** No mathematical counterexample, missing divisibility condition, sign exception, or literal transcription defect was found in the new reductions. All advertised variable counts, operation counts, exact degrees, and nonzero fixed-slice coefficient certificates below were independently checked.

This is an independent mathematical and exact-algebra audit, not an external human review or a kernel-checked formal derivation. It does not prove Con(ZFC), run the underlying machine to completion, or replace the inherited unbounded native-compiler/K215 calibration. The conclusion is conditional only in the ordinary proof-dependency sense: the named inherited compiler/Pell/calibration theorems are used as the source theorems, rather than being inferred from finite tests. No new consistency or arithmetic-soundness hypothesis is introduced.

The independently authored checker `audit_literals.py` uses only the Python standard library and its own sparse multivariate polynomial implementation. It does not import or execute any producer module or upstream coefficient builder. Source JSONs are parsed as inert polynomial data through a restricted AST. Both ordinary and `python -O` executions pass. `RESULTS.json` records exact counts and degree certificates. `ARCHIVE_MATCHES.json` records byte-exact source matches to the authenticated incoming archives, including the retained Pell interfaces in `inherited_interfaces/`.

## 1. Fixed integers and source provenance

There are two distinct coefficient tuples. They must not be conflated.

* The seven unrestricted-integer equations use beta=2^1064921-1 and the complete mixed-parity source-34 tuple K0, MC, MF, plus cone_A=2^1113 and cone_B=2^666104. Their six minimal unsigned little-endian payloads occupy 615883 bytes.
* The two strictly-positive equations use beta=2^590069-1 and the complete compact44 tuple K0, MC, MF. Those four payloads occupy 295388 bytes.

In both tuples, MF is already shifted by beta. Independently rebuilding the entire tuple from the ordered 943-tile list gives byte-identical integers at all four native ports. The checker separately reconstructs that ordered tile list from the literal 430-transition machine, verifies both compressed and raw hashes, verifies minimal encoding and bit lengths, and checks the actual mask intervals and congruences. In particular, no toy specialization is used to justify a fixed-coefficient claim.

Every one of the 29 inherited files/payloads in the integer component's hash manifest matches its stored digest. All eight incoming archives match both their SHA256 and Git blob SHA1 pins. The specific source69/70/73 positive graphs and proof texts, source71 quartic and determinant proof, source64 quartic and sign proofs, and the additional source61 Pell interfaces all have exact archive-member matches. Matching a pin establishes data identity, not mathematical truth; their proof content was separately reviewed at the points used below.

## 2. Common-sign cone and residue orientation really are compatible

Write A=cone_A, B=cone_B, C=q-F-alpha, and

T=(AF)(BC)-(q-AF-BC)^2.

The source71 determinant proof is applicable to the exact rebuilt source-34 tuple. Its soundness is sign-symmetric: T>0 implies AF and BC have the same nonzero sign, and

|q-AF-BC| < sqrt((AF)(BC)) <= (|AF|+|BC|)/2.

Therefore q has their sign and |q|>(A|F|+B|C|)/2>=|F|+|C| because A,B>=2. Hence alpha=q-F-C has that same strict sign. This restores the two older guards F alpha>0 and FC>0 without assuming q>0, X>0, or canonicality of the arbitrary zero.

The canonical completeness assertion is stronger than the existence of some source71 zero: it holds uniformly on the canonical occupied-cell family after all permitted rank-tuning dummy changes. The exact coefficient checks establish the relevant leading digit c0=105534389824824194647382298625, its bounds 2^96<=c0<c0+1<=3*2^95, the carry bound, and

121*8791+1113=1064921-97,
121*3296+666104=1064921-1.

The inherited canonical anchor/carry proof then gives q/2<=AF<4q/5 and q/2<=BC<3q/5. Consequently T>3q^2/25>0. Every positive integer has a Pos representation, where Pos(x,y,z)=1+x^2+y^2+z(z+1), by the three-square theorem applied to 4n-3.

Source70's signed orientation proof needs precisely the restored common-sign guards, eta*zeta>0, X=qW with |W|>=4, the odd nonzero Y/q^3, and the source mask inequalities. It explicitly performs rank recovery before choosing the sign of X and obtains X=epsilon*2^R with R odd. No invocation of the old positive-X theorem is hidden in that step.

For quartic37_direct, X=3X3-1 is nonzero and is 2 modulo3. Since q is nonzero and X=4q*w_scale, the retained w_scale must be nonzero, hence |4w_scale|>=4. The orientation theorem applies, and 2^R=2 modulo3 forces epsilon=+1. Restoring u=2^((R-1)/2) restores the deleted X=2u^2 row.

For quartic37, J_old=3J3+1 and w_old=3w3+1 imply q=2 modulo3, W=4w_old=1 modulo3, and X=qW=2 modulo3; here W cannot vanish. The same restoration proves soundness.

Completeness is an intersection of compatible canonical restrictions, not a claim that every old source zero lifts. The canonical family has q=2^t with t odd, R=3 modulo4, J_old=(2^t-1)/(2^1064921-1), and w_old=2^(R-t-2), with R-t-2 nonnegative and even. Hence J_old=w_old=1 modulo3. The determinant estimate holds on these very witnesses, so one may take their cone triple and their integral J3,w3 simultaneously. In the direct form take X3=(2^R+1)/3. This resolves the main completeness risk.

## 3. The thirty-integer sextic is an integral zero-set bijection

Starting from quartic37, use the two invertible root changes tau_old=tau+E(c-eta) and D_old=D+ac. Restore the seven deleted coordinates exactly as in the submitted packet:

P=eta+zeta+E(c-eta), X=4(3w3+1)q, N=q(L+1),
C2=c^2, Delta=a^2+4a+3, V=fo-c, Baux=I^2.

The independent sparse checker verifies that exactly seven source rows vanish identically under simultaneous substitution. The only additional change is to replace the restored difference row by

F2 o^2-2foc+c^2+g-y^2.

Replacement minus old row is exactly o^2(F2-f^2), and F2-f^2 is retained. This is reversible on zeros in both directions; it is not a division, a saturation, or a reduction from integer to rational coordinates. The two centered norm identities hold identically, leaving residual degrees at most three. Forgetting the seven registers and undoing the root shifts is the inverse map. Thus there are exactly 30 unrestricted variables and 17 residuals.

## 4. Octic projection and the transport pivot have no denominator gap

The eleven simultaneous octic restorations in the packet each use only retained variables. The checker verifies all eleven vanished definition rows, all thirteen surviving rows, and all variable occurrences. In particular k0=1-V+jc+hE restores zeta=k0-eta, and P=k0+E(c-eta). Forgetting and restoring those coordinates are inverse polynomial maps on integer zero sets. This gives 26 variables, 13 residuals, and residual degree at most four.

For the 25-variable degree-ten packet, first introduce C=q-F-alpha, equivalently alpha=q-F-C. The transport row is then monic in F:

(K0+W)C-F-z(q-1)=0, W=4(3w3+1).

Eliminating F by F=(K0+W)C-z(q-1) and substituting alpha=q-F-C uses only integer polynomials. Exactly one row disappears. No division by q-1, W, K0+W, or any potentially zero expression occurs. In particular the proof includes negative and zero values of those expressions before the other equations are imposed. It is a zero-set bijection, not an argument relying on a generic nonzero coefficient. The largest surviving degree is five.

## 5. Joint positivity is an exact existential equivalence

For arbitrary integers x,y define G(x,y,t)=xy-(t^2-x-y+1)^2.

If G>0, then xy>0. If both x,y were negative, writing x=-a,y=-b with a,b>0 would make the square at least (a+b+1)^2>ab=xy, impossible. Thus x,y>0.

Conversely, let x,y>0 and n=x+y-1. Then 1<=n<=xy. Put m=floor(sqrt(n)). Among the consecutive squares m^2 and (m+1)^2, one has distance from the integer n at most m, because their gap is 2m+1. If n is not a square, this distance is at most m<sqrt(n); if n is a square, the distance is zero. Therefore a choice of integral t gives (t^2-n)^2<n<=xy, so G>0. This argument covers x=1 or y=1 and all equality boundaries; there is no hidden lower-size assumption.

Apply this to x=T and y=eta*(k0-eta). Replace the two private Pos triples by G=Pos(p,qpos,rpos), with the additional integer t. Both directions restore suitable private witnesses, so the replacement is an existential equivalence. It is not a bijection of those private witnesses and need not be one. Six variables become four. The new guard has residual degree six, giving 24 variables and degree twelve. Applying the same monic transport pivot gives 23 variables and residual degree eight, hence degree sixteen. The pivot commutes with this existential replacement because it is a polynomial coordinate reconstruction, not a positivity assumption.

## 6. Exact degrees on the actual integer tuple

The exact coefficient calculations are independent sparse convolutions of the full literal residuals, not merely estimates from the circuit. The final polynomial in each case is the sum of all residual squares.

| Packet | Integer variables | Residuals | Exact degree | A certified coefficient |
|---|---:|---:|---:|---|
| quartic37_direct | 37 | 24 | 4 | [tau^4]=1 |
| quartic37 | 37 | 24 | 4 | [tau^4]=1 |
| sextic30 | 30 | 17 | 6 | [I^4 g^2]=1 |
| octic26 | 26 | 13 | 8 | [a^4 f^4]=1 |
| degree10_25 | 25 | 12 | 10 | [w3^2 C^2 J3^6]=104976 beta^6 |
| degree12_24 | 24 | 12 | 12 | [eta^4 j^4 c^4]=1 |
| degree16_23 | 23 | 11 | 16 | [w3^8 C^8]=429981696 cone_A^8 |

Every displayed coefficient remains strictly positive after the actual payload specialization, as beta>0 and cone_A>0. This closes both upper- and lower-degree arguments without generic-coefficient assumptions.

## 7. Positive11: removing q(q-1) is sound

The graph changes exactly I=i q(q-1)c^2 to I=i c^2 and removes two now-dead multiplication gates. It has eleven strictly-positive inputs and 111 live binary operations: 65 multiplications, 29 additions, 17 subtractions. All other gates match the source70 graph literally.

The replacement still gives I>=c^2. Every unconditional source70 separation estimate uses only this lower bound, not the removed prime support: 1<Dtau<Df<Q; |V|>1, including the b=cT-R=0 branch V=-c; pairwise distinct positive radicands; a strictly dominant radical; and L>sqrt(Df)+sqrt(Dy)>0. Thus a zero of the octic norm yields a rational signed sum of three roots with nonzero sum and distinct square values. The explicit rational-extraction identity in source70 then makes each root rational. Rational-square integrality handles the first two roots.

For the third root, the following adjacent-coefficient descent replaces the prime-support argument in full, rather than assuming its former coprimality conclusion.

Let Q>1, V integral, and y rational satisfy QV^2-(Q-1)y^2=1. The equation excludes zero coordinates; take absolute values. Write y=a/m in lowest terms, m>0. Then m^2 divides Q-1. If V=1, y=1. Otherwise y>V and QV>(Q-1)y. Define

V'=(2Q-1)V-2(Q-1)y,
y'=(2Q-1)y-2QV.

V' is integral, the same norm equation holds, and -V<V'<V. The norm excludes V'=0. Since 2Q-1=1 modulo m, y' has the same reduced denominator m. Strong induction on |V| forces m=1. All sign choices in the octic root extraction are covered by taking absolute values only in this descent.

Restore f_old=|f_*|, i_old=i, u=|y_*|-V, and r=n+L-f_*-y_*. Strict inequalities give u,r>0. It is essential that r use the signed extracted roots; replacing them there by absolute values would generally change the carrier identity. With these choices Z=Zbar-M(f_*+y_*)=M tau_*, and the four weighted-source residuals vanish. A1 is unchanged. The source70 weighted interface, reviewed together with source61's direct normalized rank and signed auxiliary-index lemmas, then gives the native source and a finite refutation. The modulo-four finalizer still forces N8=A1=0; it does not assume either residual is nonnegative.

Completeness admits an especially simple exact map: from any old source70 positive11 zero, keep all inputs except i and set i_new=q(q-1)i_old. Then I_new=i_new c^2=I_old. Every downstream register is identical, so the new equation also vanishes. This avoids any additional cofinality or fresh-Pell-witness assumption. Equivalently, the submitted finite-group construction is valid, but it is stronger than needed for this direction.

## 8. Positive12: the adaptive carrier composes without circular divisibility

The graph differs from source69 only by U=q^2Y, q^4X becoming qXY, and removal of dead q4. It has twelve strictly-positive inputs and 101 live operations: 56 multiplications, 26 additions, 19 subtractions.

With J=6j+1, q is even. All three residuals are squares modulo4, so the unit-product finalizer forces A0=A1=N=0. Source69's first-carrier argument, unchanged here, gives q^3|Y, (q-1)|Bt, Bt>0 and C>0. Only then are the source mask bounds 3q<R<q^4-2 used. Since U=q^2Y>=q^5, the positivity bound for Dstar holds without q|X. Rational-square integrality therefore gives a positive main Pell root. The first/main Pell classification excludes first index 1 and proves c>8XY^3>2R. Thus V=f^2(cT-R)-c>1 before strong- or auxiliary-rank recovery.

For the unchanged norm, write d=Delta c^4, rho=f^2-1, Q=Delta rho, h(z)=(1-Q)z^2+2(1-Q)Vz+V^2-1, aN=h(n), bN=2(1-Q)(n+V), and AN=d aN+(1-Q)rho. Here d,rho>0, Q>1, and bN is nonzero. If N=AN^2-d bN^2 rho=0, the rational i=AN/(d bN) satisfies d i^2=rho, while u=n-i satisfies h(u)=0. The latter is QV^2-(Q-1)(V+u)^2=1. The descent in Section7 makes V+u integral, hence u and i integral. Taking i_positive=|i| and u_positive=|V+u|-V gives strictly positive source coordinates. The exact converse identity is N|rho=d i^2=d^2 h(n-i)h(n+i).

We now have source73's thirteen-positive adaptive equation, with j73=2j. Its required rank recovery uses no q|X. After it yields p=R and 2n_first=R+1, the index surplus r0 is a positive multiple of 4XY^2. Crucially U=q^2Y divides 4XY^2 already because q^3 divides Y; q|X is not needed here. Only after that step does integrality of the carrier imply q|HX, hence q|X because gcd(q,H)=1. This resolves the principal possible circularity.

For completeness use the shared canonical compact witnesses. Their odd repunit exponent >1 yields J=1 modulo6 and positive j=(J-1)/6. Source73's lift gives gamma=gamma_old-w+r0/U>0, because r0/U>=4XY/q^2>w. The remaining carrier coordinates are unchanged; take t=f-1>0 and n=i+u>0. The norm identity gives N=0. All twelve inputs are strictly positive. No condition on arbitrary noncanonical witnesses is needed.

## 9. Positive degrees and actual-slice noncancellation

The checker independently expands A0 and each adaptive main carrier in an abstract weighted polynomial ring. It proves the degree16-to15 cancellation in A0 and the degree14-to13 cancellation in A1. It also verifies the entire two-root resultant identity and the factored octic norm center. The graph degree ledger uses these proved cancellation identities, rather than naive gate bounds.

For positive11, the degrees are I5, Df14, Q18, V18, L18, W19, Zbar24, A16, Bf22, Cnum62, Ncenter132, N8 264, and A1 13. The unique leading branch of N8 is Q0^4 Zbar0^8. Multiplying by A1 gives degree277. With q0=3 beta j and k0=eta+zeta, the exact selected coefficient is

[j^60 i^24 eta^49 X^42 Y^85 alpha^16 gamma] P11
=128*3^8*(3 beta)^60>0.

For positive12, the residual degrees are A0 15, A1 13 and N50. The only degree78 contribution is A0 A1 N. Its selected coefficient is

[j^18 eta^11 X^12 Y^23 t^8 n^2 gamma alpha F^2] P12
=64*(6 beta)^18>0.

Both selected coefficients were obtained by exact sparse multiplication and coefficient extraction, leaving the fixed ports symbolic. Neither depends on K0, MC or MF, so the authentic specialization cannot cancel it. The actual beta payload is positive in each separate tuple. These are exact degrees, not upper bounds.

## 10. Final interpretation

The new mathematical reductions preserve the intended existence predicate in both directions. Composing with the specifically inherited native/refutation equivalences and negating yields the stated formalizable-in-ZFC consistency equivalences. The integer and strictly-positive domains must remain explicit in the final report. The new certificates do not establish global minimality or certify the full semantic chain in Lean/Rocq. Within those accurately stated limits, all nine constructions pass this audit.

No correction is required for acceptance. The only recommended exposition improvement is to use the direct i_new=q(q-1)i_old map for positive11 completeness; it is shorter and eliminates an unnecessary proof obligation. Retain the exact full tuples, source notices, archived source proofs, and the audit's distinction between finite algebra checks and unbounded semantic theorems in the final ZIP.

### Release reproducibility note

The original archive authentication was completed during this audit and its receipts are retained. The distributable may omit the eight redundant full source ZIPs. In that case run `audit_literals.py --release`: it reruns all exact algebra and coefficient checks and verifies each retained source digest against the previously authenticated archive-member receipt. `RESULTS_RELEASE.json` states explicitly that this run does not recompute original ZIP hashes. Full archive reauthentication remains available by supplying the pinned original ZIPs and omitting `--release`. This distinction changes no mathematical verdict and prevents a compact release from claiming to rerun data it does not contain.
