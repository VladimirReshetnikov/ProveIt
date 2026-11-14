# PA equivalence audit and a syntactic reverse compiler

## Pinned sources

* James Chang, `jamesyc/BusyBeaver`, commit `407cdc356f6b586635e71ac92be394255f4bfea4` (196 working states).
* Previous publication, commit `69d98241a721ead20b4f0b17df9062950b40fbfe` (209 working states).
* ProveIt, commit `f7d2482e35cf2f8f3bd03b5a82387ad999243548`, `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`.

## What the current Lean endpoint actually says

`docs/result.md` lists `PA196.Arithmetic.pa_proves_nonhalting_consistency`:

    PA proves nonhaltingSentence -> consistencySentence.

`PA196/Independence.lean` has exactly that direction. The two-sided independence theorem is a metatheorem; it is not the missing biconditional. `PA196/Logic/Soundness.lean` explicitly calls its proof external. It proves derivation soundness in the concrete hereditarily finite list model from `PA196/Logic/FiniteModel.lean`. `PA196/Source/Nonhalting.lean` and `PA196/Nonhalting.lean` then establish nonhalting in Lean's metatheory.

Thus a description of the published endpoint as a Lean-verified PA-provable biconditional would overstate what these files contain. This is not an obstruction to the biconditional. The following syntactic argument supplies a written route for its other direction. It must be distinguished from a completed Lean implementation.

## A fixed arithmetical interpretation

Work temporarily in a fixed definitional extension PA+ for exponentiation and the binary-bit predicate. This extension has a primitive recursive proof translation back to ordinary PA. Let `B(u,v)` say that bit `v` of `u` is one; the first argument is the container, matching this repository's `wel` convention. Fix PA+ proofs of:

1. `B(u,v) -> v < u`.
2. The elementary binary-digit update laws for `s` and `s + 2^n` under `s < 2^n`.
3. In particular `not B(u,u)`.

Translate a decoded formula compositionally: truth to `0=0`, implication to implication, `wel(a,b)` to `B(x_a,x_b)`, `weq(a,b)` to `x_a=x_b`, and `wal(a,f)` to `forall x_a T(f)`. The numerical decoder has `wal(a,f)=4 pair(f,a)+2`; the transposition changes decoding only. Formula code zero is truth, even though `wim(0,0)=0`; its translation is provably equivalent to `T(0)->T(0)`, so this sole constructor collision is handled by a fixed logical proof. For all other implication codes the translation commutes literally.

`PA196/Logic/Decode.lean` already proves the essential syntactic bound: every variable label in decoded code `c` is less than `c`. Consequently `x_c` is fresh in `T(c)`.

## Finite comprehension is a proof schema, not a truth predicate

For every arithmetical formula `psi(z,params)`, PA+ proves

    forall n exists s < 2^n forall z < n,
      B(s,z) <-> psi(z,params).

Use induction on `n` with precisely the displayed formula as the induction formula. At zero take `s=0`. At the step split on `psi(n,params)`, take `s+2^n` when it holds and `s` otherwise, and apply the binary update lemmas. All fresh variables are selected syntactically. From the code of `psi`, a primitive recursive program constructs the induction-axiom instance and the surrounding proof. PA proves that the output is a valid PA+ proof by syntactic verification. There is no quantification over a satisfaction predicate for arbitrary PA formulas.

Taking the property `(B(A,z) or z=b) and psi(z)`, and a cutoff `A+b+1`, yields the pointed version

    exists s forall z,
      B(s,z) <-> ((B(A,z) or z=b) and psi(z)).

The cutoff is valid because `B(A,z)` implies `z<A`. In particular it proves both subset separation on the members of `A` and inclusion of the distinguished point `b` when `psi(b)` holds.

## Every PA196 axiom has a uniformly constructible PA proof

The six heads and the restricted propositional head are first-order/equality tautologies after translation. Coincident variable labels are dealt with by finite syntactic case distinctions. The bound on the fourth parameter of `rho8` restricts available instances but is irrelevant to soundness.

For the guarded gate, write `c` for both its property code and fresh variable label, as in the upstream paper. If the guard fails, the command returns code zero, whose translation is provable. If `c!=a,b`, let `phi=T(c)`. Equality and membership vacuity under `x_c` have elementary first-order proofs, because `x_c` does not occur in either atom.

The pointed comprehension theorem constructs `s` such that, when `a!=b`,

    forall x_b,
      (B(x_a,x_b) -> (phi -> B(s,x_b)))
      and (B(s,x_b) -> phi),

and also `phi -> B(s,x_b)` at the original distinguished assignment. Freshness of `x_c` lets this witness serve as the interpretation of the gate's existential variable. If `a=b`, the first antecedent becomes `B(x_b,x_b)`, which PA refutes; use the comprehension theorem on the singleton distinguished point. This explicitly addresses the label collision, rather than treating `x_a` as a parameter under a binder that also binds `x_a`.

Hence PA+ proves the existential separation-and-point bundle, which propositionally entails the actual gate `not (Delta -> (V -> Q))`. This supplies a primitive recursive proof-producing procedure for every gate instance.

## Refutations translate to PA refutations

Let `Prf_C(p,f)` be a standard primitive recursive checker for finite derivations of the exact eight-head PA196 calculus (the six heads, restricted `rho8`, gate), with only modus ponens and generalization. Using the preceding axiom-proof constructor and proof concatenation, primitive recursion over a derivation produces `F(p)`, a PA+ proof of the universal closure of the translation of its conclusion. PA proves the syntactic correctness implication

    Prf_C(p,f) -> Prf_PAplus(F(p), close(T(f))).

The implication constructor collision at zero is handled as above. `T(1)` is `B(x_0,x_0)`, which PA+ refutes. Append this fixed proof, then eliminate the definitional extension. There is therefore a primitive recursive `F_bottom` such that PA proves

    Prf_C(p,1) -> Prf_PA(F_bottom(p), bottom).

This is a proof transformation; it neither proves nor assumes reflection for PA.

## Extracting a refutation from a finite halting run

Replace the existential assertions `Nonempty (Derivation f)` in `PA196/Logic/CommandSoundness.lean` by actual finite derivation codes. Maintain a derivation code for each of the two live formulas `t,h`, and a list of derivation codes parallel to the Cantor stack. Underflow returns truth with its fixed identity proof. A successful MP appends modus ponens; a failed MP returns truth. AX appends exactly the fixed head instances, the generalization of the old `h`, and the saved old top. Its new top is either truth or a guarded gate instance. All updates are primitive recursive operations on syntax. If Shift halts because `t+h=1`, one of `t,h` is exactly one, and its retained certificate is a derivation of code one.

For the literal machine, prepend its exact finite startup. Positive-length instruction contracts plus determinism allow bounded extraction from a given halting trace. A trace of length `N` contains at most `N` completed source instructions. Simulate those source instructions, and the command-boundary traversal, keeping the annotations. The primitive recursive engine contracts make the boundary recognition and the partial final instruction check effective. The machine cannot halt in an unfinished nonhalting macro, because each macro's totality and unique exit are part of its register-engine contract. The only terminal source instruction is the Shift test. This gives a primitive recursive extraction algorithm `E` and a syntactic PA proof of

    Trace_M(t,halt) -> Prf_C(E(t),1).

This is the reverse trace/certificate direction that the current formal endpoint does not explicitly package. Its construction should be included when claiming a PA-provable biconditional, or the claim should be conditional on this lemma until it is formalized.

Combining it with `F_bottom` gives `PA proves Halt(M) -> not Con(PA)`, equivalently `PA proves Con(PA) -> Nonhalt(M)`. The opposite direction is the direction implemented by the published PA196 refutation compiler and independence theorem. A new machine with a PA-verifiable, finite-run-preserving simulation of this table inherits both directions.

## What ConciseIPRA can and cannot contribute

The current ConciseIPRA core has terms `x,0,S,I`; formula constructors `=,Q,D`; and progress restricted to literal equations. Its objective counts Python checker tokens, AST nodes, and normalized bytes. The article carefully distinguishes its tiny code envelopes from reductions in the primitive mathematical rule inventory.

These are useful design principles for proof-command encodings: infer redundant certificate fields, share a syntax traversal, derive equality laws from a restricted transport, and use freshness supplied by numerical codes. They do not by themselves give a smaller two-symbol TM or preserve the target theory. Replacing a PA proof enumerator by one for iPRA changes the consistency statement. An appropriate strengthened calculus (for example a route to full HA plus an explicit negative translation of PA) would need a fresh equivalence proof and an actual compiled state count. No such construction is claimed in this audit.

## Formalization status to state in the final report

| Claim | Status |
|---|---|
| Published literal table has 196 working states | Exact upstream data and Lean finite checks |
| Published PA proves Nonhalt -> Con(PA) | Explicit upstream Lean theorem |
| Published external nonhalting and two-sided independence | Explicit upstream Lean theorems, using standard-model metatheory |
| Reverse syntactic translation of the command calculus into PA | Written construction above; not a new Lean artifact |
| Reverse extraction from arbitrary finite halting trace | Written invariant/extraction argument above; must be checked against any altered decoder/engine |
| Full PA-provable iff for a reduced table | Inherits only after proving the reduced table's simulation and the extraction obligations |

