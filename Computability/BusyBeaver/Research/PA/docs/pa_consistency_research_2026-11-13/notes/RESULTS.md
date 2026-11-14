# Independent proof and grammar-search handoff

This directory contains research and intermediate artifacts for the PA196
comparison. It does not contain a verified machine with fewer than 196 states.

## Mathematical results

* `pa_reverse_translation.md` supplies a written proof of the reverse
  PA-internal calibration by a primitive-recursive **syntactic proof
  translation** into PA. It uses binary-coded finite sets and a PA proof
  supplier for finite comprehension. It does not appeal to an arithmetical
  truth predicate or to PA proving its own soundness.
* `diagonal_vacuity_proof.md` gives a replacement for the gate's primitive
  equality-vacuity clause. The new clause is `B -> U(B,B)`, where a formula's
  code is also used as a fresh variable label. It recovers the exact
  reverse-rewriting, neighborhood, and witness interfaces required by the
  original PA-refutation compiler. The proof explicitly covers `B=A`, the
  property-code register used in the strongest validated implementation.
* The diagonal clause needs seven existing AX macros in place of seventeen.
  The resulting AX word has 191 tokens and the same nine-item selector
  protocol. The changed source has 3700 primitive sites, versus 3812 in
  PA196. Source shortening by itself does not imply a smaller transition
  table.
* These are mathematical proofs and proof-construction specifications, not
  claims of completed new Lean formalizations. The upstream repository's
  stated internal theorem is the direction from nonhalting to Con(PA).
  Its external semantic soundness theorem alone is not an internal proof of
  the converse.
* ConciseIPRA's literal-equation induction presentation concerns iPRA. A
  contradiction search for it cannot be substituted for a PA contradiction
  search without an additional strength argument.

## Best concrete grammar results from this directory

| Artifact | Calculus | Raw AX concat nodes | Full source depth | Maximum consecutive zeroes | Status |
|---|---|---:|---:|---:|---|
| `milp_preserve_.json` | Original PA196 | 67 | 29 | 6 | Plain 201-state compilation passed all 4959 symbolic site/outcome cases, reported by the compiler agent |
| `milp_preserve_folds.json` | Original PA196 | 68 | 28 | 6 | Plain 202-state control compilation passed all 4959 cases |
| `milp_preserve_123456_123456_A.json` | Diagonal vacuity at A | 69 | 28 | 6 | Prefix-valid grammar preserving twelve old fold-root shapes and their incoming tags; physical compilation/folding delegated |
| `milp_preserve_12356_123456_A.json` | Diagonal vacuity at A | 68 | 28 | 6 | Prefix-valid grammar preserving five old fold-pair shapes/tags, omitting the pair `(x45,x25)`; physical compilation/folding delegated |

The fixed portion of the plain compiler occupies 134 states. Therefore
`134 + raw AX nodes` is the plain state count. The published PA196 obtains
six extra identifications of reader states. Preserving the twelve pair-root
shapes and tags is not by itself a certificate that all six folds remain
valid: their finite detours can depend on other helper subtrees.

The best validated new-calculus table reported by the compiler agent at
this handoff is the 199-state diagonal machine under
`../proveit_analysis/diagonal199_final/`. It has 3700 source sites, 4815
symbolic site/outcome contracts, and a checked startup. Consult its receipts
for exact filenames and hashes.

## Search limits

Forcing all twelve original fold-root shapes and tags in the diagonal-A
grammar gives optimum 69 in the implemented restricted MILP: targets 67
and 68 were infeasible, and the unrestricted objective solved at 69. This
is a lower bound for that particular grammar model, not a lower bound on
Turing-machine state counts or on general source compression.

Each of the six models preserving any five of the six original fold pairs
also ruled out a 66-node target. Their optimum was 69 except when the
`(x45,x25)` pair was omitted, in which case it was 68. Those optima apply
only to the stated fixed-shape models.

The following prefix-constrained searches timed out without an incumbent:

* Diagonal A, diagonal D with the gate conjuncts swapped, and diagonal H
  with the conjuncts swapped, each with at most 66 raw nodes and a
  120-second limit.
* Diagonal A with every verified negation peephole, in either conjunct
  order, with at most 65 raw nodes and a 90-second limit.

A timeout is not an infeasibility result.

Unconstrained results such as `milp_balanced67.json`, `milp_head_order.json`,
and `milp_neg.json` must not be represented as valid physical-machine
certificates. Some exceed the runtime's maximum zero-run bound or have not
been checked against it. The reader treats seven consecutive zeroes as a
left sentinel; every source route must respect the six-zero limit.

## Reproduction entry points

`grammar_milp.py` searches shared-substring grammars. `rebalance_guarded.py`
reparents selected rules subject to the reader's prefix constraints.
`grammar_preserve_folds.py` combines optional old fold-root preservation,
prefix constraints, head permutations, diagonal vacuity choices, gate
conjunct order, and the independently verified negation peephole.

All grammar scripts use the literal PA196 tree and symbolic parser in
`../root_analysis/symbolic.py`; they are research scripts, not standalone
proof assistants. The mathematical notes distinguish their written
arguments from executable finite certificates.
