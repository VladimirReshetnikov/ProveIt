# Flexible fresh binders in the merged equality axiom

## Status and pins

This is a new ordinary mathematical generalization of the accepted merged-equality calibration. It is designed to support source optimization, and does not itself assert a smaller machine or a new proof-assistant endpoint. The inspected ProveIt revision is `2762b8a183830b1f5a30cf059ffb4d92e77cddde`. The exact inherited calculus definitions are `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean`; the relevant proof decomposition is in `KEqCodes222.lean`, `KThmK.lean`, `KEind222.lean`, `KSeedModel222.lean`, and `KIndisc222.lean`. All paths below are relative to that Lean ZFC directory unless otherwise specified.

## The theorem

Let P(a,b)=(a+b)(a+b+1)/2+b, I(a,b)=4P(a,b), R(a,b)=4P(a,b)+1, Q_i(A)=4P(i,A)+2, and E(a,b)=4P(a,b)+3. F=1 and T=0, with I(0,0)=0. Let f:N^2->N be a primitive-recursive function satisfying

    a != b implies f(a,b) != a and f(a,b) != b.               (fresh-off-diagonal)

Form C_f by retaining truth, numerical MP, theorem-only GEN, rho1-rho6, the exact gated seed bundle C222, and the dominated rho8 family U<=A, but replacing the merged equality row by

    G_f(a,b,c) = E(c,a) -> (E(c,b) -> Q_{f(a,b)} E(a,b)).

Then, by ordinary reasoning formalizable in ZFC,

    Con(C_f) iff Con(ZFC),

where Con(C_f) means that native code1 is not derivable. The source-level claim uses exactly the accepted gated seed bundle, and makes no tacit arbitrary formula substitution or label-renaming assumption. It is a refutability calibration, not a claim that C_f derives the same native codes as the parent.

Three useful choices are

    f_R(a,b)=4P(a,b)+1    [accepted baseline],
    f_I(a,b)=4P(a,b)      [delete the relation-tag increment],
    f_P(a,b)=P(a,b)+1     [pairing index plus one].

The self-equality choice f_E(a,b)=4P(a,b)+3 also works but has a larger naive emitter.

## Proof: the unchanged classical layer

The accepted 3,728-node dominated-rho8 derivation recovers every unrestricted rho8 instance using only dominated rho8 and MP. It is independent of G and the theory bundle. Thus the same I,K,S,B,Peirce and classical propositional basis is available in C_f. The retained rho6 gives ex falso exactly as in `KCode222.c222_efq`. Ordinary propositional deduction, contraposition, and conjunction introduction/elimination below are shorthand for those fixed Hilbert derivations. Only closed theorems are generalized.

Write Ex_r X = not Q_r(not X), with native not X=I(X,F). The retained rho2 and closed GEN give universal monotonicity: from a theorem X->Y derive Q_r X->Q_r Y. Classical contraposition then gives existential monotonicity: from X->Y derive Ex_r X->Ex_r Y. The same rules prove

    Q_r(X->Y) -> (Ex_r X -> Ex_r Y).                          (all-ex)

These are the exact `all_ex` and `ex_mono` arguments in KEqCodes222, independent of f.

## Proof: reflexivity, the helper, and rho7 for arbitrary f

Fix x and put r=f(x,x). From G_f(x,x,r), contraction gives

    E(r,x) -> Q_r E(x,x).

Existential monotonicity, followed by rho1(r,x), gives Ex_r Q_r E(x,x). The retained rho6(r,E(x,x)) therefore gives E(x,x). No freshness condition was used in this step; in particular r=x is allowed.

Fix a,b and let r=f(a,b). Apply G_f(a,b,a) to reflexivity E(a,a). This gives

    E(a,b) -> Q_r E(a,b).                                    (helper-f)

Next derive specialization at this binder. K and universal monotonicity give

    Q_r E(a,b) -> Q_r(E(r,a)->E(a,b)).

Combine this with (all-ex) and rho1(r,a) to get

    Q_r E(a,b) -> Ex_r E(a,b).

Existential monotonicity applied to (helper-f) gives Ex_r E(a,b)->Ex_r Q_r E(a,b). Apply rho6 to conclude

    Q_r E(a,b) -> E(a,b).                                    (spec-f)

Composing G_f with (spec-f) recovers

    E(c,a) -> (E(c,b) -> E(a,b)),

the full rho7 schema. These are precisely the KEqCodes222 derivations with every occurrence of `wel a b` replaced by f(a,b); none requires a syntactic freshness premise. The proof works for arbitrary natural arguments and all numerical aliases.

## Proof: the only new lower-calibration point

Define indiscernibility by the equality-free named formula

    Eind(x,y) := [forall v (R(v,x)<->R(v,y))]
                 and [forall v (R(x,v)<->R(y,v))],

where v=x+y+1 is a fixed fresh auxiliary label. The connectives expand using implication and F exactly as in KEind222. Existing equality-free vacuity, quantifier-free specialization, and alpha-renaming derivations depend on rho1-rho6, rho7, membership vacuity, the classical layer, and equality reflexivity. They do not require equality vacuity at every fresh label. Membership vacuity is still projected from the unchanged gated bundle.

To derive E(x,y)->Eind(x,y), split into two numerical cases.

* If x!=y, choose w=f(x,y), which is different from both x,y by fresh-off-diagonal. Rho3, rho5 and equality symmetry give E(x,y)->Bin(w,x,y) and E(x,y)->Bout(w,x,y), where Bin and Bout are the two membership biconditionals. The helper-f gives E(x,y)->Q_w E(x,y). Universal monotonicity puts both Bin and Bout under Q_w, and conjunction introduction gives E(x,y)->Ev(w,x,y). The already available equality-free alpha-renaming changes w to x+y+1. This is literally the proof of `KEind222.Eq_Eind`, with f replacing wel.
* If x=y, every biconditional R(v,x)<->R(v,x) and R(x,v)<->R(x,v) is a propositional theorem. Closed GEN and conjunction introduction give Eind(x,x) directly. K then gives E(x,x)->Eind(x,x). No helper, no freshness of f(x,x), and no equality axiom are needed for this diagonal case.

The original implementation `Eq_Eind` used fresh wel uniformly; this explicit diagonal branch is the new point that permits f_I(0,0)=0.

Existential monotonicity and rho1 now give Ex_i Eind(i,j). The other translated equality axioms (Euclid, membership substitutivity, and arbitrary fresh equality vacuity of Eind) use only equality-free quantifier manipulations and are unchanged from KEind222. Consequently every finite ordinary Tarski derivation translates into the f-calculus after replacing literal equality by Eind. This includes genuine falsum, translated into native1, using the same irreflexivity sentence as `KEind222.c222_complete`.

## Proof: transfer of the unchanged seed calibration

The previous paragraph reproduces the full interface required by `KEind222.c222_complete`, with C_f replacing C222. One must not claim a literal transport of arbitrary old code derivations: the bundle ties its private numeric label to its matrix code, so arbitrary equality replacement would change that coupling.

Instead use the exact accepted lower-calibration route. Let T consist of named formulas whose equality interpretations have derivable native codes in C_f. If C_f does not derive1, first-order completeness and the interpreted Tarski derivation give a nonempty irreflexive model of T. For every equality-free named relation psi, its native encoding is unchanged by the equality interpretation, and the exact gated bundle at that code remains an axiom. The argument of `KSeedModel222.seed_eqFree`, including its low-code/padding treatment and private-code freshness lemma, is therefore unchanged. The model has the seed property for every equality-free relation. The indiscernibility quotient in `KIndisc222.fullSeed_quotient` then gives the seed property for every relation, literal equality included. The accepted seed-theory calibration produces the required model/consistency consequence for ZF and hence ZFC. Thus Con(C_f)->Con(ZFC), with the whole argument formalizable in ZFC.

For the converse, retain the accepted upper interpretation of the exact seed bundle in the ZFC-calibrated model. All retained logical rows are unchanged. G_f is valid in every ordinary nonempty structure: when a!=b, its binder is different from both labels, so the antecedent equalities imply E(a,b) and changing the binder does not change either term; when a=b, E(a,a) remains reflexive under every reassignment, regardless of f(a,a). Hence the original upper model validates G_f as well, and derivation induction shows Con(ZFC)->Con(C_f). This argument includes arbitrary natural code arguments, because numerical decoding of implication and quantification is compositional and the zero alias is already handled by the inherited decoder theorem.

All uses of first-order completeness and the inherited seed interpretation are explicit. No claim is made that finite numerical tests establish either consistency implication.

## Arithmetic verification of the compact choices

Let s=a+b. Since s(s+1)/2 >= s for every natural s except no exception is needed at s=0 (both sides zero), P(a,b)>=a+b. Thus P(a,b)+1>max(a,b).

If (a,b)!=(0,0), then s>=1 and 4P(a,b)>=4s>s>=max(a,b). Hence f_I is fresh except at (0,0); that pair is diagonal and covered above. At (0,0), Q_0 E(0,0) is ordinary universal reflexivity, so it introduces no singleton-domain assumption. By contrast f=P without +1 is not covered: at (a,b)=(1,0), P=1 equals a while a!=b, and G_f can force universal equality from a local equality antecedent in a nonsingleton structure. This is why blindly dropping every tag and scale is invalid.

## Exact source opportunity

In the inspected K215 source, the complete G macro word occupies primitive ordinals [479,888), and the binder R macro occupies [695,723). The old macro word is

    [168,166,182,168,121,182,166,121,181,166,121,182,180,119,119].

Here 166/121/168 load a/b/c, 119 constructs I, 181 constructs R, 182 constructs E, and 180 constructs Q. Replacing the unique181 by119 gives exactly G_I and removes its final `CI1` from the closed binder constructor, at the level of the arithmetic source. Source reassociation, physical allocation, all-natural runtime, and blank startup are separate machine obligations. The general theorem also permits a P+1 constructor if its exact source cost is lower.

The current source agent is assessing these alternatives. This note asserts neither a source-DAG decrease nor a state decrease before that measurement.

## Sharpness of the binder condition and the 2P option

The fresh-off-diagonal condition is not merely sufficient for structural validity of every G_f row; it is necessary. Suppose a!=b and f(a,b) equals a or b. In a two-element structure assign every initially relevant label, including c, the element0. Both antecedent equalities are true. Within the quantified consequent assign the binder the element1. Exactly one of the distinct labels a,b changes, so E(a,b) is false. Thus the row fails. This provides an exact characterization of which numeric binder functions preserve validity in all ordinary structures, independent of the membership relation.

For every fixed integer k>=2, f_k(a,b)=kP(a,b) is fresh except at (0,0): if s=a+b>0, kP>=ks>s>=max(a,b). Accordingly 2P is another calibrated candidate binder; it could remove one doubling relative to I=4P while retaining no final tag. The source/backend cost, rather than the numerical growth rate, determines whether it helps.
