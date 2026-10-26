# Logical calibration and the boundary of the independent audit

## Exact meaning of the consistency statement

Use the fixed first-order ZFC presentation denoted `ZFCax_s` in ProveIt,
and its finite proof relation `BProv`. The formal target is the absence of
a finite derivation of `Form.fBot` from that theory. This is the repository's
arithmetized consistency predicate. The finite syntax is recursively coded;
it is not a semantic assertion that every ZFC theorem is externally true.
The usual effective translations between standard presentations of ZFC
give the customary consistency statement.

The logical chain used by the arithmetic construction is

    a square-shell C222 refutation
    iff an original C222 derivation of code 1
    iff a BProv ZFax_s [] Form.fBot derivation
    iff a BProv ZFCax_s [] Form.fBot derivation.

The first equivalence is the ordinary square-shell syntax recoding. It
fixes truth 0 and falsity 1 and transports every guarded rule instance.
It must not be replaced by the unsupported claim that the new numerical
constructors literally are the old Lean constructors.

The next two equivalences are the exact identified logical interfaces:

* `SetTheory.BusyBeaver.ZFC.KEndpoint.c222_iff_zf_refutation`;
* `SetTheory.BusyBeaver.ZFC.ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The pinned source URLs are:

* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean

These endpoints concern the numerical calculus itself. Their use does not
depend on running K215 or any other Turing machine. `KEndpoint.lean` also
contains machine endpoints, but the theorem named above has no machine
argument.

## What was independently inspected

The two endpoint source files were inspected, together with their principal
logical components `KCode222`, `Code254`, `KSeedDirect222`, `KLowerQHyp`,
`KUpper222`, `KEind222`, `KSeed222`, `KQ1ZF`, `KQ1Model`, `KThmK`,
`KSeedInterface222`, `KEqCodes222`, and `WFModelCore`. The inspected
endpoints contain actual proof terms, not a new `axiom` or `sorry` replacing
the desired conclusion. This is a source review, not a recompilation of
the full transitive Lean import closure, and it does not establish what
axioms occur anywhere in that entire closure.

The lower chain in `KEndpoint.c222_of_zf_refutation` uses:

1. named-formula completeness with interpreted codes (`KEind222.c222_complete`);
2. derivability of the named seed property (`fullSeed_direct_of_derivable`);
3. the seed-to-model construction (`zf_consistent_of_formSeed`).

The latter passes through a tagged domain, an extensional quotient, and
the internally well-founded part of that quotient. The word internally
is material. The argument does not assume that a model of ZF has an
externally well-founded membership relation or that Con(ZFC) yields a
transitive set model. Such an assumption would be substantially stronger
than the requested consistency predicate and would be an actual gap.

The upper chain is `KUpper222.zf_refutation_of_c222`; it interprets the
calculus in the constructible model. The Choice transport uses soundness,
first-order completeness, and the constructible-class model of ZFC inside
a ZF model. These are ordinary mathematical constructions available in
ZFC; their occurrence does not assume Con(ZFC).

## The least independently certified inherited bridge

The largest inherited logical obligation, and the part least reproduced
by this new submission, is the full unbounded C222/ZF calibration. Its
seed-to-ZF-model lower direction is not implied by the finite polynomial
checker or by inspecting the displayed two-line endpoint composition.
It remains an explicitly credited dependency of the full imported proof
development. No new independent formalization of that bridge is claimed.

On the arithmetic side, the most delicate inherited bridge is the signed
Pell canonical-index theorem: classification of all integral Pell
solutions, the squared-divisibility and abscissa comparison lemmas, the
odd frame bound, and the bounded-error orientation pool. The retained
ordinary proofs are the round-17 `PROOF_315.md`,
`ORIENTATION_FIRST_PROOF.md`, and `STRICT_BUDGET_PROOF.md`, together with
the current pooled-power theorem. The new C-anchor argument spells out
how those results apply when its nominal index is initially signed.
This submission does not turn finite Pell spot checks into an unbounded
proof.

The generalized factorial-free binomial CRT argument was checked at its
ordinary theorem level. Both directions of its prime-power selection
are needed: every row has a selector, and every prime of the binomial has
a compatible row. The proof's denominator loss is bounded by k-1, with
precision 2x and lower index k<=x. Omitting the every-prime direction would
leave completeness unjustified. The new construction retains both.

Pinned arithmetic sources:

* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/151-factorial-free-binomial-crt/report/main.tex
* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/PROOF_315.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/ORIENTATION_FIRST_PROOF.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/135-cofinal-anchors-round17/direct/STRICT_BUDGET_PROOF.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4/Computability/DiophantineConsistency/con-zfc-diophantine-forms/158-pooled-powers/proofs/POOLED_POWERS.md

## What the new finite certificate establishes

The depth certificate binds an independent syntax AST to the exact
square-shell constructor source, checks every constructor depth, and
records the constant ell=2^20. The inductive inequality in
`LABEL_SEPARATION_WITHOUT_DERIVED_RANGE.md` then proves the uniform bound
on all local labels. Finite coefficient collection and exact variable
projections establish literal equality or equisatisfiability of the
specified finite polynomial systems. They do not prove their entire
unbounded semantic interpretation on their own.

The new ordinary mathematical argument supplies what the finite checks
cannot: large-evaluation multiplicity recovery, removal of the derived
label range, preservation of the local CRT bound, sound signed-anchor
relocation, and a cofinal completeness construction. All recursions are
over finite syntax, finite lists, or natural numbers. Induction, integer
factorization, polynomial arithmetic, and finite CRT are available in ZFC.

No step reasons only about externally standard finite certificates.
The target equivalence is a theorem about the internally coded integers
and finite derivations of each model of ZFC. In a nonstandard model, a
nonstandard integer tuple and a nonstandard finite derivation are related
by the same internally proved uniform lemmas. No appeal to external
termination, omega-consistency, or external correctness of a nonstandard
proof is used.

The justified status is therefore an ordinary mathematical proof,
formalizable in ZFC, composed with the identified inherited calibration
and accompanied by exact finite certificates. It is not a new end-to-end
Lean/Rocq certificate and proves neither Con(ZFC) nor its negation.

