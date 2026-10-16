# Audit of the equality-free search calculus

These are independently derived mathematical results and reproducible checks for
the four-row base-three candidate at ProveIt commit
`17d0f2eaa650901cda59764dfcc4661c199e49c8`. The memo does not claim a verified
compiler, an end-to-end TM theorem, or a consistency calibration of the changed
calculus. It can also support a candidate obtained by bijectively renaming the
four metavariables of the retained Łukasiewicz row: that change preserves the
set of axiom instances exactly.

## 1. The exact distinction that matters

Write `F=1`, `A => B = 3P(A,B)`, `Q_i A = 3P(i,A)+2`, and
`R_ij=3P(i,j)+1`, with `P(a,b)=(a+b)(a+b+1)/2+b`. Derived negation is
`nA=(A=>F)`, conjunction is `n(A=>nB)`, and `E_i A=n Q_i n A`.

The retained nonpropositional logical rows are normality

    Q_i(A=>B) => (Q_i A=>Q_i B),

commutation

    Q_i Q_j A => Q_j Q_i A,

and the new row

    D_i(A): A => Q_i E_i A.

Atomic membership vacuity appears in the bundled theory row for `k != i,j`.
The original row was

    B_i(A): E_i Q_i A => A.

With primitive false and ordinary classical quantifiers, `B_i(nA)` and
`D_i(A)` are equivalent. This semantic observation does **not** justify a
replacement in a calculus whose negation is implication into an arbitrary
distinguished atom. In the original calculus, `B_i(A)` is exactly what supplies
explosion `F=>A`. Using explosion to prove equivalence of the two rows is
circular after deleting `B`.

### Theorem 1. The full old and dual calculi are not deductively equivalent

There is a two-valued Boolean interpretation in which all dual-candidate
axioms, including every emitted C/G/vacuity bundle, are true, but some old
`B_i(A)` and some explosion `F=>A` are false.

**Proof.** Interpret every `Q_i` as the identity operation. Interpret `F` as
true, `R_01` as false, and all other raw membership atoms arbitrarily. Extend
this to codes with ordinary material implication and `0=true`. All normality
and commutation instances are tautologies. Every atomic vacuity instance is
`p=>p`. The Łukasiewicz axiom is a propositional tautology. Since F is true,
every relative existential `E_i A` is true and every relative conjunction
`n(A=>nB)` is true. Consequently the dual row is `A=>true`, and every emitted
theory bundle is true. Generalization and modus ponens preserve truth.

Taking `A=R_01` gives a false explosion instance. The old row has value
`true=>false` and is false as well. Thus neither is derivable in the dual
calculus. In the old calculus, K gives `F=>E_i Q_i A`; combining with
`B_i(A)` gives `F=>A`. This proves the strict failure of the proposed
deductive-equivalence argument. □

The interpretation is compatible with numeric code zero: the only coding
collapse is `Imp(0,0)=0`, and `true=>true=true`.

**Limit of the result.** Here F is true. The model separates derivability but
does not separate refutability, which asks specifically whether F itself is
derivable. It therefore does not prove that the candidate misses ZFC
inconsistency. A new refutation-conservativity theorem could still rescue the
dual replacement.

### Theorem 2. Persistence of F survives the dual replacement

The dual calculus proves `F=>Q_i F` for every index i.

**Proof.** Let `T=Q_i(F=>F)`. Identity and generalization prove T. Now
`E_i F=(T=>F)`. K proves `F=>E_i F`; the theorem T and propositional
reasoning prove `E_i F=>F`. Generalize the latter and use normality to obtain
`Q_i E_i F=>Q_i F`. Compose this with the instance
`F=>Q_i E_i F` of the dual row. □

### Theorem 3. Old B is recoverable on F-stable formulas

If the dual calculus proves `F=>A`, then it proves `E_i Q_i A=>A`.

**Proof.** First, Peirce together with `F=>A` gives relative double-negation
elimination `nnA=>A`; the converse `A=>nnA` is purely implicational. Thus
`A` and `nnA` are provably equivalent. Generalization and normality preserve
provable equivalence under `Q_i`; ordinary implication preserves it under
relative negation. Apply the dual row to `nA`:

    nA => Q_i E_i nA = Q_i n Q_i nnA.

Using `nnA <=> A`, replace the right side with `Q_i n Q_i A`. Relative
contraposition yields `n Q_i n Q_i A => nnA`. Its antecedent is `E_i Q_i A`;
compose with relative double-negation elimination. □

This proof identifies a useful interval of the Lindenbaum Boolean algebra.
The formulas above F, meaning those A with `F=>A` provable, contain F and
truth and are closed under implication, relative complement, and every
`Q_i` (the last assertion uses Theorem 2 and normality). Within this interval
the old and dual rows have the usual relationship.

### Why this does not yet calibrate C/G

A natural translation sends an atom A to `j(A)=nnA`, which behaves
propositionally as `F or A`, and then commutes with implication and
quantification. The translated formulas are F-stable, so Theorem 3 applies.
However, the homomorphism

    j(Q_i A) <=> Q_i j(A)

does not follow merely from `F=>Q_i F`. F-true successor worlds may still
affect `Q_i A` when they do not affect `Q_i j(A)`.

This matters concretely in the C axiom. Replacing atoms by j enlarges the
subset predicate

    Q_c(R_cb=>R_ca)

to `Q_c(j(R_cb)=>j(R_ca))`. A powerset-container clause must then contain
more candidates: its antecedent has become weaker as a test for failure,
or equivalently stronger as a true subset relation. Consequently one cannot
argue that the original C axiom trivially implies its translated version.
A sound transport of this clause, or an alternative refutation translation,
is still required. The G schema is more flexible because the translated
matrix can itself be chosen as a new matrix instance, but that flexibility
does not automatically solve the fixed C clause.

### Theorem 3a. Even general refutation conservativity is false

There is a theory formed from the retained **logical fragment** and a single
F-stable added axiom that is refutable using the old B row and is not refutable
using the dual row. Thus the proposed localization cannot give a theorem for
arbitrary F-stable theories. The C/G bundles are not included in this theorem.

**Proof.** Take two worlds w and g. Interpret F as false at w and true at g,
and choose an atom A that is false at both worlds. Interpret every Q_i as
the box operation for the relation

    w R w; w R g; g R g.

Other atoms can be F, A, or any persistent truth assignment. Normality and
generalization are sound; all boxes are identical, so commutation holds;
atomic vacuity holds because atoms are persistent.

Every dual row holds, even for arbitrary formulas. At g its existential
subformula is true because F is true. At w, if a formula p is true, then
`p=>F` is false at the reflexive successor w; hence `E_i p` is true at w.
It is also true at g. Thus `p=>Q_i E_i p` holds at w as well.

Now add the single axiom

    T = (Q_i(F=>A)) => F.

At w the boxed antecedent is false because `F=>A` is false at g. At g the
consequent F is true. Thus T is globally true. The dual calculus plus T
cannot derive F, since F is false at w. T is F-stable already by K because
it is an implication ending in F.

The original B calculus derives `F=>A`, then `Q_i(F=>A)` by generalization,
and then F by T. This is the promised refutation separation. □

This axiom T is not asserted to be a consequence of the emitted C/G bundles.
The result rules out an unrestricted repair and makes the missing task
precise: any successful dual-refutation theorem must use special properties
of those exact theory rows or a stronger preserved invariant.

## 2. Equality deletion has an independent logical cost

Even retaining the old B row does not justify importing standard equality-free
first-order completeness from the original equality-bearing proof. Let worlds
be assignments `s:N->{0,1}`. Let `Q_i` evaluate its argument after flipping
coordinate i. Let `R_ij` be the proposition `s(i)!=s(j)`, and F be `R_00`,
which is false everywhere. Then:

* The modal operations are Boolean automorphisms, so normality and
  generalization are sound.
* Coordinate flips commute, so the commutation row is valid.
* A flip is an involution, so both B and the dual B hold.
* An atom `R_ij` is unaffected by a fresh-coordinate flip, so atomic vacuity
  holds.
* If `s(i)=s(j)` with i different from j, then `R_ij` is false while
  `Q_i R_ij` is true.

Therefore the valid first-order principle `Q_i A=>A` is not derivable from
the retained logical fragment alone. The deleted equality rows may have
been essential to the original first-order completeness proof.

This is deliberately a countermodel of the **logical fragment**. It is not a
model of the complete C/G theory: deterministic coordinate flips cannot
provide the required container witnesses. The possible route that C/G
themselves supply enough strength to interpret ordinary first-order logic
remains open. The report must distinguish this issue from the set-theoretic
equiconsistency of abstract CP/GIC when placed in ordinary first-order logic.

## 3. Base-three coding, including zero, has a clean total solution

Use finite syntax with four written forms:

    Top; Rel(i,j); Imp(A,B); All(i,A).

Top is a decoding convenience, not a new runtime tag. Define its code as 0
and the other three codes exactly as above. Define D on natural numbers by
`D(0)=Top`; for n>0, use `n mod 3` to choose the constructor and unpair
`floor(n/3)` for its payload.

### Theorem 4. Total decoding, canonicality, and freshness

1. D is total and produces a finite formula.
2. Encoding after decoding is the identity on all naturals.
3. Decoding after encoding is normalization that recursively replaces only
   `Imp(Top,Top)` by Top.
4. Every variable label, including every binder label, in D(n) is less than n.

**Proof.** If `P(a,b)>0`, then `P(a,b)>=a,b` and therefore
`3P(a,b)>a,b`. Tags 1 and 2 also dominate both payloads when `P(a,b)=0`.
Thus every recursive formula child in the n>0 decoder is strictly smaller
than n; every atom and binder label is smaller as well. Strong induction
proves termination and freshness. At n=0 the formula is Top and has no
labels, so freshness is vacuous. The defining equations show that decoding
and encoding are inverse, except that the implication tag has the unique
zero collision `Imp(0,0)=0`. Structural induction gives exactly the stated
normalization. □

The consequence is stronger than merely checking positive finite formula
codes. There is a bijection between all naturals and canonical finite
formulas, where canonical means that no implication node has two Top
children. The old phrase “cyclic code zero” can be replaced by this finite
canonical syntax.

The constructor equation for decoding implication holds literally except at
the pair (0,0); there the two decoded formulas are Top and `Top=>Top`, which
are propositionally equivalent. Rel and All constructor equations hold
literally everywhere.

### Freshness versus schema coverage

Theorem 4 proves that the matrix code c is absent from all labels in D(c),
including when c=0 or c=1. It thus proves the dynamic-binder freshness used
by G. It does not prove the rest of the first-order bridge.

To recover an arbitrary ordinary first-order matrix phi for fixed input and
output labels a,b, take a fresh label k larger than every label in phi and
larger than a,b. Let psi be `All(k,phi)`. Its code c exceeds k and hence is
different from a and b; D(c) is equivalent to phi in ordinary first-order
semantics. This produces a matrix satisfying the runtime gate. But removing
the vacuous quantifier in the **machine calculus** still needs a valid
first-order or relative-calculus completeness argument. The fresh-code
construction must not be mistaken for that argument.

## 4. The abstract enumerator does match its own code calculus

This is a separate theorem that needs no interpretation of membership,
equality, or the intended set theory. Define K to be the least set of natural
codes containing 0, all four row instances, and every gated theory bundle,
and closed under numeric modus ponens and generalization.

An AX command in the modified candidate pushes six slots:

    old current; GEN; rho8; rho2; rho4; dual rho6

in that order, then leaves the gated bundle current. Set m=6. At a command
boundary write the retained data as `(T,S,d,h)`, where T is current, S the
theorem stack, d the additive parameter counter, and h the cache. Let
`AX(c;x,y,u)` mean the AX selector c with its three extra parameters; the
first is added to d and the second to h. All plain DROP and NIP commands have
zero additive parameters.

### Theorem 5. Abstract-enumerator halting iff K proves 1

**Soundness.** Maintain that T, h, and every stack entry belong to K. The
infinite zero tail is justified by `0 in K`. A successful MP constructs a
K-conclusion; a failed MP constructs 0. AX emits only row instances, GEN of
a K-theorem, and either a legitimate bundle or 0. DROP and NIP only move
K-theorems. Hence a NIP halt on cached 1 implies `1 in K`.

**Completeness.** The following blocks construct any K-derivation. Each
contract is from `(T,S,0,0)` to `(result,S,0,0)`, unless a NIP has already
halted. Earlier halting is acceptable.

| Block | Exact commands |
|---|---|
| Discard, result 0 | `MP 1; AX(1;0,0,0); NIP^6` |
| Bundle(a,b,c) | `Discard; AX(c;a,b,u); NIP^6` |
| Logical row at depth j, 1<=j<=4 | `Discard; AX(c;a,b,u); NIP^j; DROP; NIP^(7-j)` |
| GEN i of a sub-built H | `Build_H; DROP; NIP; AX(i;i,0,0); NIP^5; DROP; NIP; NIP` |
| MP of A and A=>B | `Build_A; DROP; Build_(A=>B); NIP; DROP; NIP; MP B; AX(B;0,0,0); NIP^6; DROP; NIP; NIP` |
| Reset arbitrary retained state | `AX(0;1,1,0)` |
| Halt from current 1 | `DROP; NIP; NIP` |

For Discard, `Imp(T,1)=3P(T,1)>0`, so its MP against cache zero fails.
The following AX has a=c=1 and is gated off. Six NIPs remove its six pushed
slots and recover the saved zero. A row extraction first pops the required
row to h; DROP makes it current; the remaining NIPs remove the pushed bundle
and the other unused slots. For GEN, the AX reads the incoming H for GEN
before reading its updated second parameter. Its gate fails because a=c=i.
The MP block preserves its first premise under the second sub-build, then
arranges the two premises in the exact current/cache order used by MP. Its
second AX resets the nonzero additive counter while preserving B. These
are finite algebraic command calculations.

The reset prefix takes arbitrary retained d,h to zero because AX clears them;
the added units ensure a,b>0, although the resulting top and stack may be
arbitrary. The construction blocks tolerate those retained values.

Finally, a finite block has an exact candidate number. For an ordinary
command record use `P(selector,P(x,tail))`; AX additionally pairs y and u.
Every subsequent record is prefixed by +1, to account for the enumerator's
decrement before a noninitial command. End the list by tail zero. Use the
first record itself as candidate N. If the enumerator does not halt sooner,
it reaches N: within any current candidate its positive remaining proof-list
counter strictly decreases on every noninitial command, and the next-proof
counter increases once at each candidate start. The finite encoded program
`Reset; Build_1; halt suffix` therefore eventually halts. □

The theorem is about the abstract enumeration specified by these command
equations. It does not certify that a particular edited register DAG, compiler,
initializer, or binary transition table implements them.

### Safe row renaming

If the four metavariables of rho8 are permuted bijectively, its family of
instances is unchanged: invert the permutation on the tuple of natural
parameters. The bundle emitted by the same AX command may change, but the
row-extraction block discards it and all other unused rows. Thus this
optimization preserves the code calculus and its abstract halting behavior.
It does not repair or worsen its logical-calibration gap.

## 5. Independent exact tests

Run:

    python codec_and_macros.py

The script performs 10,000 total numeric codec round trips with freshness,
1,000 randomized finite-syntax normalization checks, and 5,712 exact
abstract-command contracts. There are four profiles: original or permuted
L, each with original or dual B. Each profile checks 720 row extractions,
180 bundle extractions, 360 generalizations, 108 MP contexts, and the
remaining reset, discard, and halting contexts, for 1,428 contracts per
profile. Thus the permuted-L/original-B profile of the recommended
248-state output is directly covered at the abstract AX level. These
tests do not cover the subsequent register-grammar transformation or binary
compiler. The script also checks the Boolean axiom assignments in Theorem 1
and the two-world logical countermodel in Theorem 3a. The evidence is written
to `codec-and-macro-results.json`.

Because literal iterated Cantor-pair integers can be enormous, the macro
tests use a DAG of exact natural-number expressions. Equalities use canonical
expression identity or exact small integers. Inequalities used by the
simulator have certified distinct remainders modulo three or elementary
lower bounds. A comparison lacking a certificate raises an exception. No
hash or numerical fingerprint is used as an equality oracle. These checks
support the independent specification; the displayed mathematical proofs
explain the universal claims. The Python program is not a kernel proof.

## 6. Priorities for a credible record claim

The base-three alias and abstract enumeration have short mathematical
solutions. The remaining difficult issue is the changed calculus. Two
separate results are needed: refutation conservativity of the dual row in
its exact theory context, and an equality-free logical interpretation strong
enough for the ordinary CP/GIC consistency calibration. A proof of abstract
CP/GIC equiconsistency with ZFC does not itself provide either result.

The original B row should therefore remain an explicit control experiment.
A compiler optimization that produces fewer than 254 states while retaining
that row would remove the dual-refutation problem, but would still need the
equality-free first-order bridge. Conversely, a proof that C/G supply the
missing logical strength could be valuable even before another state is
saved. The exact full-program simulation and source-to-table connection are
additional obligations after the mathematical calculus is calibrated.

## Primary material audited

The calculations use these pinned source declarations, with new arguments
written independently in this memo:

* [Original pure row and enumeration specification](https://github.com/VladimirReshetnikov/ProveIt/blob/17d0f2eaa650901cda59764dfcc4661c199e49c8/lib/jeff-busy-beaver-zfc254/ZF/m254/tools/logic/spec.py).
* [Original propositional proof: thm_F uses old rho6](https://github.com/VladimirReshetnikov/ProveIt/blob/17d0f2eaa650901cda59764dfcc4661c199e49c8/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/logic/Comp_Prop254.v).
* [Original enumeration bridge design and later status](https://github.com/VladimirReshetnikov/ProveIt/blob/17d0f2eaa650901cda59764dfcc4661c199e49c8/lib/jeff-busy-beaver-zfc254/ZF/m254/design/logic.md).
* [Modified equality-free, dual, base-three emitter](https://github.com/VladimirReshetnikov/ProveIt/blob/17d0f2eaa650901cda59764dfcc4661c199e49c8/Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.py).
* [Repository statement of the 252-state candidate's unresolved scope](https://github.com/VladimirReshetnikov/ProveIt/blob/17d0f2eaa650901cda59764dfcc4661c199e49c8/Computability/BusyBeaver/Research/ZFC/raw_candidate_252.md).
