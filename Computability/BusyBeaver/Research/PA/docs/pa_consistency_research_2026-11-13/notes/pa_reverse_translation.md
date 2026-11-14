# The missing internal direction for PA196

## Status and exact target

The retrieved upstream theorem list (`jamesyc/BusyBeaver/docs/result.md`) states
`PA196.Arithmetic.pa_proves_nonhalting_consistency`, namely
`PA ⊢ ¬H196 → Con(PA)`. It does not list the converse. The source
`PA196/Logic/Soundness.lean` explicitly describes its proof as external and
its model uses Lean's type of hereditarily finite lists. It is consequently
incorrect to describe a PA proof of the converse as already checked by that
development.

The converse has a direct syntactic proof. The construction below explains
how to obtain it without a truth predicate or an appeal to uniform PA
soundness. It is a paper-level proof and a specification for an additional
formalization, not a claim that the additional Lean theorem has been built.

## Arithmetic interpretation

Work temporarily in the conservative definitional extension of PA with the
primitive-recursive function `pow2(n) = 2^n`. Its totality has a fixed PA proof,
and every resulting proof can be translated back into the ordinary PA
language by a primitive-recursive proof transformation.

Let `Bit(s,z)` say that the bit at index `z` in the binary expansion of `s`
is one. An explicit formula is

    ∃u,v (s = (2u+1)·2^z + v ∧ v < 2^z).

PA proves the fixed arithmetic lemmas for this formula, including
`Bit(s,z) → z < s`, and therefore `¬Bit(x,x)`.

The interpretation `T(c)` of a numeric PA196 formula code is obtained by
primitive-recursive decoding (the repository has the fuel-bounded decoder
in `PA196/Logic/Decode.lean`):

* `T(0)` is `0=0`.
* `T(M(a,b))` is `Bit(x_a,x_b)`. The first argument is the container.
* `T(E(a,b))` is `x_a=x_b`.
* `T(U(a,B))` is `∀x_a T(B)`.
* `T(I(A,B))` is equivalent to `T(A)→T(B)`.

The last clause has one harmless encoding exception: `I(0,0)=0`. Rather
than pretending the decoded formulas are literally identical, the compiler
uses the fixed proof `0=0 ↔ ((0=0)→(0=0))` in that case. More generally, it
constructs the relevant compositional equivalence proofs while decoding.
Every nonzero code has strictly smaller recursive subcodes. Every variable
label occurring anywhere in `T(c)` is below `c`; in particular `x_c` does
not occur in it. For arithmetic proofs, fresh auxiliary bound variables can
always be chosen above the largest displayed label, by a primitive-recursive
renaming operation.

## The essential proof schema: finite binary comprehension

For every arithmetic formula `φ(z,params)`, PA proves the following schema:

    ∀n ∃s<2^n ∀z<n (Bit(s,z) ↔ φ(z,params)).                (BCφ)

The proof is full induction on `n` with exactly the displayed existential
formula as induction formula. At `n=0`, use `s=0`. For the successor step,
let `s` be the previous witness. By excluded middle for `φ(n,params)`, use
`s+2^n` if it holds and use `s` otherwise. The fixed binary arithmetic lemmas
verify all bits below `n+1` and the upper bound on the new witness.

This is a *uniform syntactic schema supplier*: given the syntax code of
`φ`, insert it into this fixed induction-and-propositional proof template.
The supplier and the verification of its output are primitive recursive.
It does not compute the truth of `φ`. The same statement applies to
nonstandard formula and proof codes inside a model of PA because the
compiler's correctness is proved arithmetically by induction on coded
syntax. It is not a claim of a single arithmetic satisfaction predicate.

From (BCφ), PA obtains pointed finite separation. With `A,B` numerical
parameters, take `n=A+B+1` and apply the schema to

    ψ(z) := (Bit(A,z) ∨ z=B) ∧ φ(z).

The witness `s` satisfies

    ∀z [(Bit(A,z) → (φ(z)→Bit(s,z))) ∧ (Bit(s,z)→φ(z))]
    and (φ(B)→Bit(s,B)).                                  (PSφ)

Here elements of `A` have index below `A`, and all bits of `s` at indices
at least `n` vanish. Thus the bounded comprehension assertion supplies the
unbounded universal assertion in (PSφ).

## A uniform PA proof for the gate

Use the numeric source notation of `PA196/Logic/Basic.lean`. For labels
`a,b` and code `c`, write `C=T(c)` and suppose `c≠a,b`. The gate is

    ¬(Δ → (V → Q)),

where

    Δ := E(a,b) → U(c,E(a,b)),
    V := M(a,b) → U(c,M(a,b)),
    P := c → M(c,b),
    S := U(b, (M(a,b)→P) ∧ (M(c,b)→c)),
    Q := U(c, S → ¬P).

The source negation uses code 1. Its arithmetic image is implication to
`Bit(x_0,x_0)`, which PA uniformly proves false; hence the usual classical
equivalences for negation, conjunction, and existential quantification are
available by fixed proof templates, even when a surrounding source binder
has label 0.

The guard gives PA proofs of the two vacuity formulas Δ and V. The freshness
lemma for code `c` says that the witness variable `x_c` does not occur in C.
Instantiate (PSφ) with `φ(z)=C[x_b:=z]`, using capture-avoiding substitution
and fresh bound variables. If `a≠b`, this supplies exactly

    ∃x_c (S ∧ P).

If `a=b`, the first antecedent inside S becomes `Bit(z,z)` and is false.
The same finite-comprehension witness still proves the second conjunct
and P, so this label-collision case is valid too. This distinction is made
on *numeric labels*, not on the values of the free variables. The case
split is decidable syntactically and can be built into the proof compiler.

By classical logic, `∃x_c(S∧P)` implies `¬Q`; combined with Δ and V it
proves the arithmetic image of the gate. When the command's guard fails,
the command emits code 0 and the proof supplier emits the fixed proof of
`0=0`.

## Other heads, rules, and compiler correctness

Every remaining AX head has a fixed proof template in ordinary first-order
logic with equality:

1. `(∃x_d ∀x_d H)→H` by quantifier elimination;
2. commutation of universal quantifiers (identity if labels coincide);
3. and 4. substitution of equality in a membership atom;
5. existence of an equality witness, with a separate reflexive case if its
   two variable labels coincide;
6. distribution of universal quantification over implication;
7. the restricted `rho8` propositional head, which is classically valid
   without even using its numeric dominance condition.

The generalization head is obtained by generalizing the existing proof of
the formula in the `h` register. Modus ponens is ordinary modus ponens,
with the `I(0,0)=0` exception handled by the fixed truth proof. Thus there
is a primitive-recursive map `F` on coded source derivations such that PA
proves

    ∀p,c (Prf_source(p,c) → Prf_PA(F(p),T(c))).

More precisely, the codomain proof is initially in the fixed conservative
extension, followed by its primitive-recursive proof elimination. Append
the fixed PA proof of `¬Bit(x_0,x_0)` when `c=1`. This yields a map `R`
with

    PA ⊢ ∀p (Prf_source(p,1) → Prf_PA(R(p),0=1)).          (TR)

This syntactic correctness assertion is proved by induction on the coded
derivation and on the decoding recursion. PA is proving a relation between
proof codes; it is not asserting that any arithmetical theorem is true.

## From a literal halting trace to a source refutation

Two finite-program verification obligations complete the internal converse.
They should be stated, not silently replaced by the external nonhalting
theorem.

First, annotate the command store with codes of source proofs for its two
visible formula codes and every live stack entry. The clean store has the
fixed code-0 proof. AX appends the source axiom proofs and a generalization
of the previous `h` proof; MP appends a modus-ponens proof on a successful
match and otherwise the code-0 proof; Shift moves proof references along
with the formula codes. A zero stack underflow returns code 0 and its fixed
proof. A halting Shift has `t+h=1`, so one visible code is 1 and its attached
proof is a source refutation. The transformations of annotated stores are
primitive recursive. The register program's verified macro contracts and
the scheduler show that a finite source halt supplies such a finite
command computation. This is the arithmetical version of the syntactic
invariant in `PA196/Logic/CommandSoundness.lean`, with `not_refutable`
replaced by (TR) and Con(PA).

Second, use the exact startup and the positive-length, all-site simulation
to reflect a literal tape halt back to a source halt. The following generic
argument avoids a delicate reverse decoder for arbitrary tape states.
Given a tape halting trace of length `t`, run the deterministic source for
`t+1` instructions from the certified startup frame. If it has not halted,
concatenate the positive-length simulations of these instructions. This
produces a literal tape run longer than `t` from the same blank start,
contradicting determinism and the absence of any outgoing row at the halt
label. Startup times below the fixed startup endpoint are checked directly.
All constructions and inductions are available in PA: the source steps
are primitive recursive, single-instruction tape segments have explicitly
terminating unary scans, and sequence concatenation is primitive recursive.
The all-site contracts must be available arithmetically with their positive
length bounds, not just as statements about standard natural numbers.

Equivalently, prove inside PA under Con(PA) that the annotated scheduler
never takes its halt branch, and then apply this finite deterministic
simulation argument. No uniform semantic soundness is used.

Together these give

    PA ⊢ H196 → ¬Con(PA),

and the already published internal direction yields

    PA ⊢ (¬H196 ↔ Con(PA)).

For a smaller machine, a separate PA-formalizable halting-preserving
simulation of that literal table with PA196 transfers both implications.

## Relevance and limitation of ConciseIPRA

The native ConciseIPRA calculus has only literal-equation induction; the
bridge is to iPRA. Its short checkers do not supply (BCφ) for arbitrary
arithmetic φ, and substituting one of them as the searched proof system
changes the consistency target. Classicalizing it alone does not supply
full PA induction. Its useful contributions here are proof-certificate
engineering, shared syntactic traversals, fused equality/computation, and
freshness/capture discipline. Any replacement calculus used for this PA
machine must still carry a PA-internal refutation translation in *both*
directions; equiconsistency asserted in a stronger metatheory is insufficient.

## Sources inspected

* ProveIt `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`, retrieved
  at main `239b7a406e24405d464edc526e09d402abce5bc5`.
* jamesyc/BusyBeaver `paper/pa196.tex`, `docs/result.md`.
* `PA196/Logic/Basic.lean`, `Decode.lean`, `FiniteModel.lean`,
  `Soundness.lean`, `CommandSoundness.lean`.
* jamesyc/BusyBeaver commit
  `69d98241a721ead20b4f0b17df9062950b40fbfe`, `paper/pa209.tex`, especially
  the external-soundness qualification in Section 4.2.
