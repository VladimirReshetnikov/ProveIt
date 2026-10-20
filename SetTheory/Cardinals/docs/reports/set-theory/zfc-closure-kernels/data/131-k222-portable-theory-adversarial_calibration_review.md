# Adversarial calibration review of the combined 222 construction

This is an independent review of the **logical** composition. It does not certify the transition table, source emitter, or runtime. The exact source binding is a separate audit.

## Verdict and stronger new certificate

The combination is sound at the native numerical deductive-theory level. It is not necessary to invent a new K interpretation or assume that the two independent packages share the same source syntax. The old and new numerical theories prove the same formulas, by a uniform finite-proof transformation.

A new independent checker, `check_uniform_composition.py`, accepts `uniform_composition_proofs.json`: **109 proof nodes, 104 formulas, nine roots**. Unlike the earlier 33 numeric examples, these roots use symbolic natural-valued label terms x,y,z and kappa(x,y). The checker validates schema instances and expected roots syntactically, without importing the generator. It permits no hypothesis rule and enforces topological proof references. All generalizations are therefore on closed derivations. Both a changed root and a changed G-schema argument are rejected by included negative controls.

The proof digest is `975d6e38e556a972c86054cb6b5fe3a6546fb2e6c39f5f1c8af25ed47522b980`. Its receipt is `uniform_composition_receipt.json`.

Under any simultaneous substitution of natural numbers for x,y,z, interpret kappa(s,t) as 4*((s+t)*(s+t+1)/2+t)+1. Each checked schema and inference specializes to the literal numerical rule. No inequality or distinctness premise was used by the checker. Thus labels may coincide, and may be zero; a symbolic kappa term may coincide with another instantiated label. Identifying formerly distinct propositional atoms after substitution preserves a Boolean tautology. Encoding formulas as numerical constructors preserves every checked implication/quantifier inference even where the numerical encoding has exceptional small codes. Native rule application, not a decoder-injectivity claim, is being checked.

The generator uses the existing proof-building routines only to produce this new proof DAG. Replaying the DAG requires only the new standalone checker and Python's standard library.

## Exact interface

Use native I,Q,R,E, N(A)=I(A,1), and kappa(a,b)=R(a,b). Put

- H(a,b)=I(E(a,b),Q(kappa(a,b),E(a,b))).
- G(a,b,c)=I(E(c,a),I(E(c,b),Q(kappa(a,b),E(a,b)))).
- V=I(R(a,b),Q(c,R(a,b))).
- J=Q(c,I(h,N(w))), with w and h exactly the seed-request package's request and hereditary closure.

The old seed bundle is N(I(V,I(H,J))). The new bundle is N(I(V,J)). These are not equal numerical expressions. The certificate proves old bundle implies new bundle and H, and that new bundle plus H implies old bundle. The root J is treated opaquely, so this calculation cannot depend on an unproved K principle or on matrix freshness.

The new G row remains **ungated** and is emitted for all a,b,c. Only the K/V bundle retains c!=a and c!=b. No logical row is removed other than replacing rho7 by G. In particular rho1 and rho6 remain available.

## Where the equality proof could have gone wrong

1. **No assumed reflexivity.** For x put z=kappa(x,x). G(x,x,z) gives E(z,x)->Q_z E(x,x). Existential monotonicity and rho1(z,x) yield Ex_z Q_z E(x,x), and rho6 yields E(x,x). Old rho7 and H are absent from this derivation.
2. **No generalization under a hypothesis.** H follows by propositional composition from G(a,b,a) and the closed reflexivity theorem. Only the closed theorem H is then generalized.
3. **No unproved universal instantiation.** Seriality Q_i A->Ex_i A follows from rho1(i,i), rho2 and propositional reasoning. Applied to Q_i A, it combines with rho6 to give Q_i Q_i A->A. Generalizing H and distributing gives Q_i E(a,b)->Q_i Q_i E(a,b), hence the needed equality-box elimination. One must not directly assert Q_i E(a,b)->E(a,b) before this derivation.
4. **No old equality rows hidden in the forward proof.** The checker rejects OLD_H or OLD_RHO7 dependencies for every forward root. Conversely the old-to-G root rejects a G dependency.
5. **No free-variable freshness assumption on raw bottom.** The native bottom is 1=R(0,0). The TAUT bridge is available without rho7/H: pinned `Comp_Prop230.v` proves `thm_F` using rho6(0,A) and the rho8-derived K combinator. From premise F, K gives Ex_0 Q_0 A because that expression is literally an implication to F; rho6 then gives A. Peirce and explosion yield classical negation and the Boolean tautologies. This argument does not generalize F under an assumption and does not claim that label 0 is absent from R(0,0).

## Deductive-equivalence proof for the full theories

From the old seed theory, H(a,b) is obtained by projecting any enabled bundle, choosing c=max(a,b)+1. This is a numerical choice of an axiom instance; no assertion of K's independent provability is needed. Old rho7 plus H gives G. Projection also gives each new enabled bundle. Disabled bundles remain the same truth seed 0. Therefore every new axiom has an old-theory proof.

From the new theory, the uniform derivations give H and rho7 without using any K instance. The checked propositional introduction reconstructs every old enabled bundle. All other rows and inference rules are literally unchanged, so a finite proof is translated line by line. The chosen c in the reverse direction is needed only to extract old H; it is not confused with the actual private code in a K instance.

Both transformations are effective on finite proofs and can be formalized in ZFC. In particular they transfer existence of a refutation, not only validity in standard models. They compose with the seed package's existing ZFC calibration. The proof does not state or require that ZFC proves Con(ZFC), or that ZFC proves existence of a set model of all of ZFC.

## Adversarial checks on inherited seed calibration

The following details were checked against `native_seed_request_audit.md`, `seed_request_k.md`, and the delivered `theory223.tex`.

- **Native decoding exceptions:** Intentional I(A,1) occurrences are genuine named negations. Every other implication's consequent is provably different from1. The membership occurrences R(b,c),R(c,b) meet that condition by the retained c!=b gate. Q/E constructors and positive compounds cannot equal1. Do not replace this check by a claim that all native implications decode homomorphically.
- **Ungated G:** Its equalities have tag3, its quantified consequent has tag2, and its implication antecedents are positive. Thus the new row has no code0/consequent1 exception. kappa(a,b)>a,b even at (0,0), where kappa=1. It may equal the third row parameter c: this is harmless because its quantifier scopes only E(a,b), not either antecedent containing c.
- **Private code0:** D(0) is a closed tautology with bound occurrences of0. The required fact is free-variable freshness, not absence of all syntactic occurrences. The gate forces a,b!=0 when c=0.
- **Private code1:** D(1)=R(0,0), whose only label is below1. The gate excludes a=1 and b=1 but permits other coincidences, handled by the existing abstraction/diagonal split.
- **Coincident active roles a=b:** Distinct-role abstraction is unavailable. Literal shadowing reduces the subset test to a tautology and the closure to `forall u(R(u,C)->((exists x psi(x)) and W(C)))`. If no psi witness exists use empty C; otherwise use a singleton containing a witness. A split on the value of psi in the original environment would be wrong.
- **Label0 as output:** Existential-premise/request equivalence must be argued after D_wn/D_wex and the inherited relative-falsity bridge, not by incorrectly declaring raw F fresh at0.
- **Lower-direction padding:** Interpret equality first, then set c=enc(not not theta(f)). This ensures the actual matrix/private code is fresh beyond all names introduced by equality interpretation. Choosing c before theta would leave a gap. The K outer template is membership-only and hence commutes with theta.
- **No new equality interpretation is required:** Since the new theory derives literal old H and rho7, the old restricted-helper adapter is restored exactly before using the seed calibration. Neither full primitive equality vacuity nor unproved substitutions are silently granted.

No defect was found in these inherited arguments or in their composition. The new symbolic certificate closes the particular finite-instance limitation of the original numerical equality proof samples, but it is not a compiled Rocq or Lean theorem and does not independently formalize the entire upstream K/ZFC interpretation chain.

## Reproduction and dependencies

Run:

    python -B check_uniform_composition.py uniform_composition_proofs.json --output fresh_receipt.json

The baseline propositional bridge inspected is the pinned `coq/logic/Comp_Prop230.v`, especially thm_F and thm_DNE, together with rho8-derived combinators in CD230.v. The seed theory sources remain Elliot Glazer's pinned K230 development and the delivered K223 witness-request calibration. Attribution to the seed theory is unchanged. Source and binary certificates must bind this reviewed interface to the final 222-state bytes before any machine claim is made.
