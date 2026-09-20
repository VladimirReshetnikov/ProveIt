# Research status

> This file is the status record of the **dfao-reversal-coloring-bound** source
> report, kept verbatim as provenance after that report was merged into this one.
> It therefore describes that report's scope and evidence, not the merged
> package's. For the merged scope see the article and README.md; for the merged
> attribution boundaries see source_audit.md.

Date of draft and literature search: **20 September 2026**.

## Target

Sylvie Davies, *State Complexity of Reversals of Deterministic Finite Automata
with Output*, arXiv:1705.07150v2 (17 October 2017), Section 5, question 1,
printed page 17: can a binary input alphabet attain the general `k^n` reversal
bound when `k >= 3`? The paper conjectures nonattainment. Its diagonal case
`k = n` was already proved; the proposed argument here covers `3 <= k < n` too.

## Result proposed in this package

For arbitrary transformations `a,b` of an `n`-element set, and arbitrary output
map `tau` to `k` labels with `3 <= k <= n`:

    |tau <a,b>| <= k^n - k! + g(k) < k^n.

`g(k)` is the maximal order of an element of the symmetric group on `k` symbols.
The proof is complete as written and has no stated unresolved lemma or
computational assumption. It has not been externally refereed or formalized
in a proof assistant. Its status is therefore a **candidate theorem with a
self-contained proposed proof**, not an independently certified result.

The main ingredients are the three-colorability of a cyclic orbital graph,
a collision obstruction for words containing a singular generator, and the
cyclic image of the stabilizer of an output-fiber partition.

## Further results in the draft

- An instance-dependent chromatic-polynomial deficit.
- A polynomial-time method to produce an unreachable reverse coloring and
  independently checkable finite certificates.
- A necessary symmetric-group quotient condition for more general permutation
  groups, conditional on colorability of the relevant graph.
- The exact input-alphabet threshold of three letters, combining the proposed
  obstruction with the previously known three-letter construction.

## What is not claimed

- No proof of the exact optimal binary reversal complexity for arbitrary `n,k`.
- No resolution of Davies's other open questions.
- No novelty claim for the orbit reduction, ternary witness, standard Landau
  function, elementary group facts, or previously reported small maxima.
- No claim that the absence of a located later solution proves the problem
  remained open until this draft.
- No Lean, Isabelle, Coq, or other proof-assistant certification.
- No claim that random tests establish the universal theorem.
- No claim that all improper graph colorings are reachable in arbitrary cases.

## Evidence actually obtained

The C++ search covered 462,066 symmetry-reduced instances through four states.
The Python audits covered every ordered pair of three-state transformations
and every output bijection, plus explicit cyclic-membership, chromatic-formula,
finite-orbit, and certificate checks. All passed. Ten focused unit tests passed.
All 24 words printed in the article's sharp three-state certificate were
individually checked against the stated transformations.

These are finite audits and executable certificates, not machine-checked
proofs of the universal quantification. The final mathematical evaluation
should focus on the lemmas and the three-case argument in the article.
