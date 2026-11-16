# Exact standard separation theory

`fullSepTheory_mem_iff_typed` proves the set-theoretic identity

```
σ ∈ fullSepTheory ↔ ∃ p : Semiproposition SourceL 1,
  σ = (separationFormula p).univCl
```

for every standard typed source sentence σ. The forward direction decodes each standard arity-one property code, and the reverse direction quotes the typed property. The proof uses the earlier exact typed closure quotation and the equality of candidate-PRA-induced and canonical Nat arithmetic structures. `PA194NatQuoteBridge` transports sentence quotation, semiformula quotation, validity, and classifier evaluation between those structures; its generic transport lemmas quantify over the dependent IΣ₁ proofs explicitly.

This identifies the standard extension of the already constructed Δ₁ theory with the repository's fully parameterized universally closed typed separation scheme. The arithmetic-model classifier remains valid also for nonstandard internal syntax, without asserting that nonstandard codes quote standard typed formulas. This theorem is a Lean metatheorem, not a native iPRA derivation and not a proof of the PA194 consistency/halting equivalence.

Run from the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-typed-theory.sh "$PWD" \
  /dev/shm/pa194-nat-structure-replay-v2 \
  /dev/shm/pa194-typed-class-replay \
  /dev/shm/pa194-standard-source-decode-replay \
  /dev/shm/pa194-typed-theory-replay
```

The two sources and eight-declaration audit are rebuilt in one fresh output; the source hashes and three selected imported objects are pinned before and after, and the checker rejects `sorryAx`. Other staged overlays and Foundation are prebuilt. Successful log: `/tmp/pa194-typed-theory-replay.log`.
