# Implication-layer simplification at the pinned current commit

Baseline: `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0` of
`VladimirReshetnikov/ProveIt`. This note concerns only the implication layer.

## What is already in the repository

The current Lean `DominatedImplication.lean` is a representation-independent
58-step condensed-detachment proof. It derives unrestricted rho8, composition,
and prefixing from restricted rho8 and modus ponens. Its import is `Init`.
`DomRho8.lean` is a 73-line numerical adapter, and `KCodeDom.lean` transports
between the dominated and unrestricted code calculi.

The current Rocq `rocq/rocq-extension/coq/215/DomRho8.v` is still the
22,673-byte compact replay: 629 retained theorem nodes, 735 instructions,
272 symbolic DAG entries. The `rho8cd` directory already contains a 52-step
numeric Rocq rendering proposal. Thus neither discovering condensed
detachment nor suggesting an abstract Lean core is new work in this packet.

## Concrete next step: use the same abstract theorem in Rocq

`DominatedImplication.v` is a new port of the exact current 58-step Lean
derivation. Its abstract interface has an arbitrary type A, a binary
operation `imp`, and a relation `below`. It assumes precisely:

1. `below a a`;
2. `below u x -> below u (imp x y)`;
3. `below u y -> below u (imp x y)`;
4. `T (imp a b) -> T a -> T b`;
5. `below u a -> T (rho8 a b c u)`.

It proves unrestricted `rho8_all`, `composition`, and `lift_right`.
There is no transitivity, antisymmetry, injectivity, interpretation into
propositions, formula decoder, truth element, or arithmetic assumption.
In particular, it never uses the numerical collision `wim 0 0 = 0`.

`DomRho8Adapter.v` is the proposed numerical adapter. It retains the exact
public `DomImp` record, including its unused truth field, and retains the
`rho8_all` statement. It obtains the context-closure properties from the
existing pairing bounds. The derivation itself is independent of codes.

This is a portability and auditability improvement. It does not claim a
new shorter mathematical derivation. Retaining the full 58-step proof gives
Lean and Rocq matching public interfaces and one shared derivation. Rocq's
existing consumer requires only `rho8_all`; the exact transitive dependency
closure of that result contains 52 lemmas. The other six current helpers are
`d32`, `d51`, `d53`, `d55`, `d57`, and `d58`.

## Why the proof has to remain syntactic

The operation `imp` is an arbitrary operation on codes. A tactic proving a
classical propositional tautology would establish a statement about actual
logical implication, not about membership in the arbitrary predicate T.
It cannot replace the derivation without a separate soundness theorem for
the chosen encoding. The explicit MP proof avoids this extra dependency and
therefore also covers noninjective encodings and nondecodable codes.

Each generated lemma is a single ordinary application of the abstract MP
rule. Its premises are explicit instances of earlier lemmas or the guarded
row. Side conditions are proved by a literal occurrence path or by a local
hypothesis. Across the 58 lemmas, the 33 used guard proofs are:

| Witness | Uses |
| --- | ---: |
| Reflexivity | 15 |
| An existing local hypothesis | 5 |
| Right operand, R | 9 |
| Right then right, RR | 2 |
| Left then left, LL | 1 |
| Left, left, right, LLR | 1 |

These counts explain why no general order theory is necessary. They do
not prove that one of the two growth fields can be deleted: the current
certificate uses both. Deleting a field would require a different proof.

## Explicit certificate and independent checking

`expanded_proof.json` records every substitution argument explicitly. It was
expanded from the repository's `rho8cd/derivation_core.txt` using the pinned
upstream renderer, with both SHA-256 values recorded in the JSON.

`check_and_render.py` does not perform unification or search. For each
step it checks that the instantiated major premise is exactly the pair
consisting of the instantiated minor premise and the stated conclusion.
It checks that each guard is a local hypothesis or a structural subterm
inclusion, references are backward, variables are in scope, and the three
public goals are the exact unguarded expected schemata. It then prints
ordinary Rocq proofs. Its own correctness is not trusted by the theorem:
the Rocq kernel rechecks the output.

`validate.py` reproduces the structural check and five meaningful negative
controls: a false MP conclusion, a forward reference, a removed guard, a
changed public target, and weakening the restricted-row leaf to an
unrestricted row. All five are rejected. The recorded result is
`checker_validation.json`.

## Size and status

| Source | Bytes |
| --- | ---: |
| Current production Rocq replay | 22,673 |
| New generic Rocq proof | 14,655 |
| New numerical adapter | 1,389 |
| New generic proof plus numerical adapter | 16,044 |

The last total is 6,629 bytes smaller (29.24%). These are proof-source
sizes, not a repository-wide reduction or a timing measurement. The extra
JSON/checker in this research packet are review evidence. The already
available 11,190-byte numeric 52-step rendering is smaller still; its
tradeoff is that it does not share the representation-independent interface.

The exact current Lean generic core was compiled here with Lean 4.32.0.
All three public results reported no axioms. This is a focused check,
not a rebuild of the complete machine endpoint. `lean_control.json`
records the source hash and scope. The new generic Rocq port also compiled
with Coq 8.18.0, all three public theorems printed closed assumption reports,
and `coqchk -silent DominatedImplication` independently returned exit 0.
`coq_core_check.json` records that focused check. The numerical adapter also
passed a focused Coq 8.18 check against the two pinned arithmetic modules
archived in the baseline repository. Four modules compiled, its `rho8_all`
printed a closed assumption report, and a recursive `coqchk` of the adapter
returned exit 0. The only compatibility edit was the import spelling
`From Stdlib` to `From Coq`; the exact edit is supplied as a patch and the
hashes and outputs are in `adapter_check.json`. The first adapter elaboration
attempt required making the language argument explicit; that failed record
is retained separately. The modern Rocq 9.1 production chain remains an
integration obligation.

## Integration sequence

1. Compile the new generic Rocq file by itself and inspect its assumptions.
2. Compile the numerical adapter against the exact K230 code definitions,
   preserving the `K215F.DomRho8` import/API expected by `ThmDom.v`.
3. Update the current Rocq producer to reproduce these exact source bytes;
   add the generic file to the dependency order and source manifest.
4. Compile the actual affected calculus clients, then rebuild and recursively
   kernel-check the literal dense endpoint before marking the new lane
   adopted. Keep the existing checked replay until that integration succeeds.

The code-calculus transport in `KCodeDom.lean` is already straightforward:
two structural inductions, differing only at the rho8 case. Generalizing
all calculus constructors into a generic inference closure could shorten
those inductions, but would broaden the interface migration substantially.
It is a lower priority than sharing this isolated mathematical core.

## Main repository sources

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCodeDom.lean`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/derivation_core.txt`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/DomRho8.v`

The formulas and derivation are the repository's existing mathematical work.
This packet contributes the generic Rocq port and a small independent
explicit-instance audit, without asserting authorship of that derivation.
