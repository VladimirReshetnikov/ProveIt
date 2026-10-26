# A fixed-role, one-parameter seed schema

## Scope and measured tradeoff

This is an auxiliary calculus simplification discovered by inspecting the
actual lower-calibration proof. It is not the selected quartic optimization.
The ordinary theorem below is unconditional relative to the identified
inherited C222/ZF calibration. It has not been compiled as a new Lean term.
The independent local-expression ledger halves the largest derived-code
degree, from 524288 to 262144, but the complete source gains an axiom branch
and loses some arithmetic sharing. A trial quartic compilation therefore
need not have fewer variables. No variable saving is claimed here.

The exact inspected source commit is
953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4. Relevant files, available in this
audit's `calibration/`, are KCode222.lean, KEqCodes222.lean, KEind222.lean,
KSeedInterface222.lean, KSeedDirect222.lean, KLowerQHyp.lean, KEndpoint.lean,
and ConstructibleChoice.lean. Their original directory is
Computability/BusyBeaver/Lean/BusyBeaver/ZFC/.

## 1. Exact replacement

Use the same numerical constructors I,M,A,E, truth 0 and falsity 1 as
C222. Write

    N(h)=I(h,1),
    req(b,k,h)=A(b,I(h,N(A(b,I(h,N(M(b,k))))))),
    sub(a,b,k)=A(k,I(M(k,a),M(k,b))),
    clos(a,b,k,h)=A(b,I(M(b,k),
                      N(A(a,I(h,N(A(a,I(sub(a,b,k),req(b,k,h))))))))),
    nks(a,b,k)=A(k,I(clos(a,b,k,k),N(req(b,k,k)))),
    RV(a,b,c)=I(M(a,b),A(c,M(a,b))).

The original final C222 axiom is

    Bundle(a,b,c)=N(I(RV(a,b,c),nks(a,b,c)))

with guard c!=a and c!=b. Its propositional meaning is
RV(a,b,c) AND NOT nks(a,b,c).

Define Csplit by retaining truth, modus ponens, generalization, and all
eight ordinary C222 axiom families exactly. Replace its guarded bundle by
two axiom families:

    RV(a,b,c),       when c!=a and c!=b;
    Seed(c)=N(nks(0,1,c+2)),       for every c in N.

Thus only the large set-theoretic seed core has fixed input/output labels
0 and 1. The membership-vacuity schema remains available at every fresh
binder. Restricting membership vacuity to labels 0 and 1 would not justify
the inherited first-order completeness argument and is not proposed.

## 2. Every new derivation is an old derivation

The ordinary axioms and inference rules coincide. For RV, the classical
tautology NOT(P -> Q) -> P projects RV from the original bundle.
For Seed(c), put k=c+2>=2. The old bundle at (0,1,k) is allowed. The
classical tautology NOT(P -> Q) -> NOT Q projects N(nks(0,1,k)).
Both tautologies are derivable from the retained rho8 propositional basis;
falsity elimination is supplied by rho6, exactly as in the existing
`c222_classical` proof. Induction on a Csplit derivation therefore gives

    Csplit(n) -> C222(n)

for every code n. In particular a Csplit refutation yields a ZF refutation.

## 3. The first-order completeness interface survives

The named calculus ThmK is independent of the seed axioms. Its rules are:
axiom hypotheses, MP, generalization, rho8, rho2, rho4, rho6, rho1, rho7,
rho5, rho3, membership vacuity at every fresh binder, and equality vacuity
at the helper binder M(a,b).

The unchanged ordinary Csplit rows produce its classical propositional
basis. The derivations of equality reflexivity, helper vacuity, and rho7
in KEqCodes222 use only growG, rho1, rho2, rho6, MP, generalization, and
classical propositional logic. They therefore apply verbatim with Csplit
as the derivability predicate. Membership vacuity is now a direct axiom.

Inducting on a ThmK proof consequently transports every named proof into
Csplit. The induction cases are the same finite list as
`KEind222.c222_of_thmK`: each ordinary row uses its corresponding retained
axiom, rho7 and helper use the preceding derived rules, and vacRel uses
the new direct RV axiom. There is no remaining call to the original seed
bundle in this transport.

The equality interpretation th replaces named equality by the fixed
indiscernibility formula. The theorem `KEind222.thm_th` transports a proof
in the full named calculus into ThmK using only ThmK's rules; it does not
depend on the choice of seed axioms. Therefore the same completeness
composition proves the following interface:

    If every formula phi of a named theory T has
    Csplit(enc(th(phi))), and T has no irreflexive model with a valuation,
    then Csplit(1).

For explicitness, add the named irreflexivity sentence
forall_0 NOT M(0,0) to T. First-order completeness gives a named proof of
falsity. Interpret equality by th, then transport its ThmK derivation by
the induction just described. The added irreflexivity sentence has
interpreted code A(0,I(1,1)), derivable by generalizing the propositional
identity 1 -> 1. The conclusion's interpreted code is again 1.
This proves the interface without assuming the desired refutation.

## 4. Fixed-role seeds already suffice for the lower bound

Let Tsplit consist of the named formulas phi for which
Csplit(enc(th(phi))). Suppose an irreflexive structure with a valuation
satisfies Tsplit. Fix any named formula psi and valuation e. Put

    m=NOT NOT psi,    k=enc(th(m)).

The inherited elementary coding facts give k>1. Every free name of m is
strictly smaller than k, because th preserves free names and every free
name of a named formula is smaller than its code. In particular k is a
fresh private container label. The new Seed schema with parameter k-2
therefore proves N(nks(0,1,k)). The direct RV schema proves RV(0,1,k).
Classical conjunction introduction combines them into the old full
Bundle(0,1,k), now as a derived formula of Csplit.

Constructor identities and `th_bundleNF` identify that code as the
interpreted code of the named bundle with input label 0, output label 1,
private label k, and matrix m. The named semantic theorem
`named_bundle_iff_seed` uses only the freshness inequalities and says that
this bundle is exactly the seed property for the binary definable relation

    (x,y) |-> Sat( e[0:=x][1:=y], m ).

Classical double-negation elimination identifies this relation with the
one defined by psi. Since psi and e were arbitrary, the structure has
the same FullSeed property used in the existing direct lower calibration.

The inherited `formSeed_of_fullSeed` and
`KLower.zf_consistent_of_formSeed` now imply that ZF has no finite
refutation. Contrapositively, if ZF has a finite refutation, Tsplit has
no irreflexive model. Section 3 produces a Csplit refutation.

Combining with Section 2 yields

    Csplit(1) iff C222(1) iff a finite ZF refutation exists.

The identified constructible-choice theorem then gives equivalence to
finite ZFC refutability. This is an ordinary mathematical proof
formalizable in ZFC. It is a theorem about existence of finite proofs,
not a claim that the two calculi derive every identical code.

## 5. Transport to square-shell arithmetic

The inherited constructor-preserving bijection f from Cantor syntax to
square-shell syntax fixes 0 and 1. Hence k>=2 iff f(k)>=2. It transports
all ordinary rules and the two disequalities of RV.

For a Seed instance with k=c+2, use the new parameter

    c'=f(c+2)-2.

It is nonnegative, and its shell seed index is c'+2=f(c+2). This is the
correct witness transport. It would be incorrect to claim that the
bijection preserves addition or that c'=f(c). Its inverse reconstructs
the converse witness in the same way. Thus the split-calculus
refutability theorem applies to the literal square-shell equations.

## 6. Local source replacement

The old nonnegative Horn product contains the truth factor, eight
ordinary axiom factors, one guarded bundle factor, an MP factor, and a
generalization factor. Replace only the guarded bundle factor by

    [Sp(1+F*RV(a,b,c))-S]^2
       + {[(c-a)^2(c-b)^2]-(d+1)^2}^2,

and add the unguarded factor

    [Sp(1+F*Seed(c))-S]^2.

All factors are nonnegative at natural local inputs. Their product
vanishes exactly when a permitted local rule applies. The same four
parameters a,b,c,d suffice; there is no new CRT input column. The derived
label sum must include BOTH RV and Seed instead of the old bundle.

The proof does not assert that all old coefficient objects survive
unchanged. A complete implementation must rebuild the exact source,
majorants, projections, and emitted polynomial. The local ledger gives
the new polynomial-label degree 262144 and conservative label majorant
exponent 1767294, but these are not a variable count for a compiled
quartic. They are useful targets for a future architecture that benefits
more directly from reducing the degree of the set-theory source.
