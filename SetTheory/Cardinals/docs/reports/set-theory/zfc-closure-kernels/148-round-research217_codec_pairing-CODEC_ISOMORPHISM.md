# Exact native-calculus transport to the 2-adic pairing codec

Date: 2026-10-20. Ordinary mathematical proof and source-definition audit. No received code was executed, no proof-assistant build is claimed, and no source-DAG or physical-state saving is claimed.

## Result

Replacing Cantor pairing P(a,b)=tri(a+b)+b by

    S(a,b)=2^a(2b+1)-1

inside every tagged formula constructor preserves the exact native theorem relation up to an explicit bijection f of natural numbers. This includes the full helper-free, support-bearing seed bundle with its private label equal numerically to its matrix code, and the merged equality row with a membership-code binder. Since f(1)=1, consistency is preserved exactly. The existing calibration therefore transfers at the level of the numerical calculus.

This is not a conjugacy theorem for the enumerator, its raw proof-list pairing, cache arithmetic, source program, or Turing machine. Those layers still need new implementation and proof.

## 1. Pairing interface

The following argument works for any two pairings beta and gamma for which the underlying arithmetic proves:

1. Each is a bijection N^2 -> N with an effective inverse.
2. beta(0,0)=gamma(0,0)=0.
3. Both dominate their components: beta(a,b)>=a,b and gamma(a,b)>=a,b.

Bijectivity and item 2 imply that a paired value is zero exactly when both components are zero. Define the four tagged constructors for each codec by

    I_beta(a,b)=4 beta(a,b),       R_beta(a,b)=4 beta(a,b)+1,
    Q_beta(a,b)=4 beta(a,b)+2,     E_beta(a,b)=4 beta(a,b)+3.

Every positive tagged number n has decoded components at most floor(n/4), hence strictly less than n. The exceptional alias I_beta(0,0)=0 is common to both codecs.

For S, unique factorization n+1=2^a(2b+1) gives the bijection and effective inverse. Also S(0,0)=0. Since 2^a>=a+1 and 2b+1>=1, S(a,b)>=a; since 2^a>=1, S(a,b)>=2b>=b. Pairing, unpairing, and the translations below can be defined by primitive recursion/course-of-values recursion. There is no appeal to a model of set theory in these arithmetic facts.

## 2. A simultaneous permutation of codes and labels

Take beta=P and gamma=S. Define f(0)=0. If n>0, write

    t=n mod 4,  (a,b)=unP(floor(n/4)),
    f(n)=4 S(f(a),f(b))+t.

Both recursive calls have arguments less than n. Importantly, recurse through BOTH numeric fields. A field that serves as a variable label is transformed by the same f as a field that serves as a formula code. Keeping labels fixed would not prove the required exact isomorphism.

Define g similarly, interchanging P and S and using unS. By induction on the argument, f(n)=0 iff n=0, and likewise for g: a positive code with tag 0 must have at least one positive component, and that component remains positive. Consequently the recursive equations apply without a hidden zero exception at a positive translated code.

For each t in {0,1,2,3}, including the exceptional n=0 case,

    f(4 P(a,b)+t)=4 S(f(a),f(b))+t.

The t=0, a=b=0 case is f(0)=0; all other cases follow directly from unpairing. The analogous equation holds for g. Strong induction on n now yields g(f(n))=n, using the homomorphism equation for g and the induction hypotheses for the decoded children of n. Interchanging codecs yields f(g(n))=n. Thus f is a bijection, not just an embedding.

In particular f commutes exactly with I/R/Q/E, and f fixes 0,1,2,3. Negation N(x)=I(x,1), existential coding, conjunction, and every constructor term therefore commute with f.

The map is generally neither the identity nor order preserving. For example f(16)=20, since 16=I_P(1,1) and I_S(1,1)=20, whereas f(20)=16 because 20=I_P(0,2) and I_S(0,2)=16. Thus 16<20 but f(16)>f(20). No monotonicity of f is needed.

## 3. Exact native rows and full seed

The audited numerical definitions are:

- research218_companion/evidence/logic/KCode230.v: four tags, F=1, derived connectives, and the older seed terms;
- research218_companion/evidence/logic/Codes230.v: rho1 through rho8;
- latest219_baseline/k225-formal/rocq224/src/Codes222.v: merged growG, nks222, vrel, and bundle222;
- latest219_baseline/k225-formal/rocq224/src/Thm222.v: truth0, MP, GEN, all retained rows, unrestricted rho8, and the gated bundle.

Every audited axiom term uses only those constructors, its natural-number parameters, and F=1. The only side conditions are the bundle inequalities c!=a and c!=b. Injectivity of f preserves and reflects both inequalities.

Two potentially delicate occurrences are harmless:

1. The merged equality row uses the binder R_P(a,b). Its translation is exactly R_S(f(a),f(b)), as required by the new row.
2. The seed uses the same parameter c both as a private bound-variable label and as an opaque formula code. Both uses become the same natural f(c), so the shared-code condition is preserved, not weakened.

If the executable gated helper emits raw 0 on a failed gate, that branch is preserved too, because f(0)=0 and equalities are reflected.

There is no hidden fixed raw label beyond the parameters in these native axiom definitions. The downstream completeness development makes convenient named choices 1 and 3 for the seed roles, and 0,1,2,3 in elementary equality formulas. All four numbers are fixed by f. The seed's own large private label is translated, not held constant. Proof-internal fresh-name choices such as successor(x+y) are not native axiom conditions and need not be preserved by f.

## 4. Derivation isomorphism and consistency

Let T_P and T_S be the native theorem predicates with identical rules/templates and their respective tagged constructors. Induction on a T_P derivation gives T_S(f(n)):

- truth0 is preserved;
- each axiom translates to the same template at the f-translated parameters, with the same valid gates;
- MP translates from x and I_P(x,y) to f(x) and I_S(f(x),f(y)), hence f(y);
- GEN translates from h to Q_S(f(a),f(h)).

The converse uses g. Therefore, for every natural n,

    T_P(n) iff T_S(f(n)).

In particular T_P(1) iff T_S(1). Thus consistency of the new native calculus is exactly equivalent to consistency of the calibrated old native calculus, including the full seed. This proof does not assume a deduction theorem, a semantic representation of the theorem set, arbitrary theorem substitution, or renaming of relation atoms inside a fixed native theorem. It translates entire numerical derivations through a proven global constructor isomorphism.

The same argument applies to a calibrated alternative propositional basis, such as H/PW, provided its native rows are constructor terms and all other axioms and gates are retained.

## 5. Support and arithmetic dependencies

The existing semantic support lemmas use the fact that every label appearing inside a positive tagged code is numerically smaller than that code. Component domination supplies this again for S. For example the inspected `tau_fr`, `seed_code_gt3`, and merged-row freshness arguments invoke P_ge_l/P_ge_r, not a special property of Cantor diagonals.

However, a literal reuse of the existing arithmetic implementation or proof text is not justified. KCode230's `unP_step`, `P_unP_step`, `P_pred`, and triangular walk proofs are Cantor-specific. Their conclusions must be reproved from the 2-adic inverse. The abstract derivation isomorphism above avoids re-proving the whole set-theoretic calibration, but not source/decoder correctness.

## 6. Explicit boundary: raw stacks, scheduler, and machine

The formula translation does NOT commute with untagged pairing. For example,

    f(P(1,1))=f(4)=4, but S(f(1),f(1))=5.

It also does NOT commute with addition: f(8+8)=f(16)=20, while f(8)+f(8)=16. Therefore one cannot transform a raw proof-list by applying f once to the list number, nor translate cache expressions d+x or h+y by replacing each operand with its f-image.

Instead, translate a finite abstract proof formula by formula, and compile its commands afresh using the new raw stack/proof-list codec. A suitable completeness proof must re-establish the new AX interfaces, generalization and MP operations, cache-reset behavior, and coverage by the universal natural enumeration. Reset-cache AX calls can avoid demanding a false additive conjugacy, but their availability and correctness belong to that new implementation proof.

Likewise, the old power-of-two residue/polynomial theorem for the Cantor-based scheduler does not automatically transfer to S. No such transfer is asserted here. Even a correct new unpairing loop does not by itself prove fair proof enumeration or blank-start equivalence.

Remaining implementation obligations are therefore concrete: build and verify the S pairing/unpairing macros; price their complete shared source DAG; verify stack, parser, and cache contracts; reconstruct the finite-proof-to-enumerator completeness proof; and compile/check the resulting exact machine and blank loader. Until then this is a calibrated formalism route, not a <=217-state candidate.
