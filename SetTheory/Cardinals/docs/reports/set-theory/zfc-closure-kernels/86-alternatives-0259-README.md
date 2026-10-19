# Logical routes below the 246-state consistency machine

## Current outcome

No new sub-246 machine is established in this workstream. The most actionable
new result is a rigorous abstract proof that contradiction detection can move
from NIP to successful MP, even while resetting the MP parameter and removing
its dummy truth push. The modified source must still be checked against its
emitted binary table and new startup. An initially tempting direct POP edit
was caught as incorrect because it retained the old cache additively.

Three other exact or semantically justified changes have actual negative
first compiler results rather than speculative state estimates:

| Route | Matched complete control | New best | Logical status |
|---|---:|---:|---|
| Fix CP variable names | 268 | 280 | Ordinary semantic calibration supplied |
| Fix GIC variable names | 268 | 277 | Ordinary semantic calibration, including c=0, supplied |
| Fix both | 268 | 283/284 | Same, offsets1/2 |
| Dual-rho6 plus explicit EFQ | 268 | 272–273 | Complete retained equality engine; EFQ essential |
| Replace commutation by Double-B6 | 268 | 273 | Explicit interderivation, no new EFQ row |
| Reparameterize four logical rows | 268 | 267 | Exact same axiom families, inverse leaf parameters |
| Then globally reassociate closed source sequences | 267 | 266 | Canonical control/sequence comparison checked |

These are complete Wade-backend comparison tables, not costs obtained by
subtracting source edits from the optimized 246-state table. Both changed
sharing and framework depth are charged by the compiler. The baseline source
and native calculus are pinned at ProveIt
`7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.

## Deliverables

- `mp_first_f_proof.md`: first-occurrence theorem for the original native
  enumerator; exact Variant-A and Variant-B definitions; soundness, constructive
  completeness and arbitrary-tail startup theorem; concrete compiler caveat.
- `fixed_binder_routes.md`: exact CP/GIC replacements, all-code/zero-alias
  analysis, macros and measured costs.
- `fixed_binder_semantics.py` and `_results.json`: 98,704 independent exact
  finite semantic comparisons.
- `double_b6_route.md`: unchanged complete theory/calculus via a new
  interderivable quantifier row with equal macro-word length.
- `double_b6_modal_check.py` and `_results.json`: 4,164 modal frame-pair
  equivalences and 66,064 individual B6 validations.
- `permuted_row_search.py`: fresh bounded search in a previously available
  source19 search family over exact independent
  reparameterizations of the universally quantified logical rows. This changes
  representation sharing without changing a single axiom family. Its output
  is in `permuted_rows/`; see `row_reparameterization.md` for the exact schema proof
  and the single-u-read implementation restriction.
- `permuted_rows_global/`: further exact closed reassociation,204nodes/266states.
- `bundle_label_swaps/`: all16 safe C/G/vacuity a/b-swap masks;21,600grammar
  trials found no improvement beyond the unchanged267-state word.

The independent audit workstream reviewed the MP and Double-B6 proofs and
accepts their ordinary arguments, with exact boundary details recorded in
`../verification/mp_first_f_review.md` and `../verification/double_b6_review.md`.
The independent reparameterization audit is
`../verification/permuted_rows_review.md`. No new Lean verification is asserted.

## What the source audit rules out

The published 246-state candidate retains the complete original proof search;
its savings concern contextual decoder/startup structure. Its ordinary
Con(ZFC) calibration is accepted in the pinned README, while the exact final
Lean endpoint is still pending. The public254 baseline is
https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254;
https://wiki.bbchallenge.org/wiki/Logical_independence supplies the historical
context, not the proof of any experiment here.

The current numerical core has four formula tags, two special codes (0 truth,
1 designated relative falsity), an equality-based cross-variable transport
layer, one CP sentence schema and one arbitrary-formula GIC schema. The
quantifier/equality layer is not dispensable merely because the set-theory
formula uses membership only. The repository's finite-sort countermodel
refutes previous equality-free logical deletions. Primitive Bottom, adding
same-name specialization, or adding atom-parametric modal axioms does not by
itself supply the missing cross-variable transport.

The following alternatives were audited before proposing the new changes:

1. Raw EPSC/PSC, exact fixed-point hulls and functional subset closure.
   Their ordinary calibrations are meaningful, but preserved full-logic
   compiler controls are already about270–347 states. Exact hulls do not
   supply a free reduction of matrix occurrences: the required Separation
   and intersection resources and all parameter instances must remain.
2. One-parameter EPSC. The repository has a cross-component interpretation
   missing Pairing and the required parameterized Replacement instance.
   Its exact consistency strength is still open; it cannot replace full
   ZFC calibration without a new interpretation proof.
3. Outgoing-profile equality and three-tag encodings. These can preserve a
   complete logic only when their translated transport axioms and capture-safe
   reserved-variable conventions are retained. Actual strict EPSC control288
   and related288/289 measurements defeat the naive constructor-count saving.
4. Finite assignment/class and ground-resolution kernels. The concrete FEC5
   control has16 clauses,35 literals,167 term nodes and9 proper function
   symbols; these are real payloads, but no verified sub-246 binary compiler
   follows from finite axiomatizability.
5. Equational/cylindric and universal carriers. The measured complete
   ground-equational proof generator is299 states before the actual ZFC query
   writer. An isolated171-state basis or small universal interpreter does not
   pay for the query, parser and blank-tape initializer.
6. GEN-free prefix-closed axioms. This is an exact logical reorganization, but
   the measured complete controls are285/286 states. Removing a named GEN
   operation does not remove its encoded quantification cost.

These are specific prior experimental boundaries, not impossibility theorems.
The new work avoids repeating the already refuted equality-free inference or
silently changing the target to a stronger theory.

## Proof standard

Every claimed logical equivalence here is an ordinary finite proof or has its
remaining numerical/interface obligations stated. Finite tests are labelled
as diagnostics. Actual state counts come from complete emitted tables and
source-edge extraction, not token counts or interpreter-only counts. None of
these artifacts is a publication, a proof of Con(ZFC), or a new Busy Beaver
bound.

## Canonical arenas and square-code arithmetic (new architecture handoff)

- `canonical_arena.md` proves that unique constructor triples plus strict
  backward references and excluding positive Imp(0,0) make node denotations
  injective. Both bundle disequality paths may then be replaced by ID tests.
  `canonical_arena.py` implements normalization and a finite checker; it also
  gives a deterministic shell generator which avoids a global uniqueness
  check by construction. Duplicate-checking or generator costs are explicit.
- `square_pair_conjugacy.md` proves that shell IDs use the pairing
  S(l,r)=l²+l+r for l>=r, else r²+l. A primitive-recursive bijection to the
  native Cantor code algebra fixes 0 and 1 and preserves every C254 rule,
  including G's code/variable-label coupling. This is exact refutation
  equivalence, not a registerwise simulation: additive D+x/H+y updates and
  stack/scheduler arithmetic require separate contracts. The finite tests in
  `square_pair_conjugacy.py` include nontrivially renamed parameters 4 and 8.
- No complete binary state cost is available for either route. They are
  implementable logical specifications passed to the arithmetic and direct-
  tape workers, not sub-246 candidate claims.

## Growing forward saturation (current direct-runtime target)

`forward_saturation.md` and `.py` give an exact deterministic finite-algorithm
search with native canonical record IDs, persistent proved bits, fair growing
sweeps, primitive-axiom recognition, GEN and MP. It halts iff native C254
derives1. There is no proof-certificate input or fixed-point detector.

Two equivalent recognizers are supplied: representative-path parameter
recovery followed by complete oracle verification; and five leaf-class passes
using one temporary node marker, followed by the bundle gate pass. The latter
is the default production reference and needs no four-parameter tuple or
representative-path table. Its physical marker/control implementation remains
charged and unimplemented. Tests include2,565 recognizer equivalences and129
growing sweeps independently checked via optional diagnostic derivations.
No complete binary state saving is claimed.
