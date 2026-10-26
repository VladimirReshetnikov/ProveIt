# Fresh numerical endpoint: specialize growth at the complete exponent

## Baseline and precise target

Pinned repository commit: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

Target:
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean`,
`rank_gt_twice_window` (the new packing-rank module from commit `493d46d`).

The current proof starts from `u < 2^u`, establishes positivity of the window,
then `q >= 2`, then `q^2 >= 2`, and finally obtains `2u < 2q <= q^3`.
Those intermediate estimates are unnecessary for this precise endpoint.
Use the same existing theorem at exponent `3u`:

`2u <= 3u < 2^(3u) = (2^u)^3 = q^3`.

The first inequality is true for every natural `u`; the strict inequality is
`Nat.lt_two_pow_self`. This arithmetic argument even works at `u=0`. The
production theorem retains its original `[NeZero N]`, source positivity, and
`C+F < q N` assumptions because the subsequent packing cast still needs its
existing domain conditions. No domain assumption is silently dropped from the
public theorem.

Exact replacement:

```lean
  have hc : 2*(width*N) < q N^3 := by
    rw [q_binary, ← Nat.pow_mul]
    exact Nat.lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := (width*N)*3))
```

The remaining `fourBlocks_ge_cube` application, natural/integer conversion,
and `fourBlocks_cast` application are unchanged.

## Novelty boundary

The prior-art agent checked the 36 placed packets and the five current incoming
ZIP archives. No exact target or full-exponent specialization was found.
Earlier proposals for general exponential thresholds are granted. This is a
narrow proof deletion at a newly added client, using an existing theorem;
it is not a new exponential lemma, induction scheme, or mathematical result.

Packet u's stronger-looking source-rank envelope has actual source-zero/Pell
premises. This endpoint is deliberately before population or Pell witnesses,
so importing that endpoint would strengthen assumptions incorrectly.

## Artifacts and accounting

- `full-exponent-growth.patch`: one exact source-body patch.
- `CurrentPackingRank2011.baseline.lean`: unchanged pinned module.
- `CurrentPackingRank2011.lean`: complete proposed module.
- `full_exponent_source.json`: SHA-256 values and physical line accounting.
- `FullExponentGrowth.lean`: arithmetic proof core with all packing facts
  explicitly supplied, plus zero-window and one-window checks.
- `FullExponentGrowth.log` and `full_exponent_validation.json`: actual compiler
  result, return code 0; both named theorems depend only on `propext` and `Quot.sound`.

The complete module changes from 138 to 133 physical lines: 5 lines removed,
with no helper/import overhead. This is source accounting, not a compile-time,
kernel-term-size, or repository-wide saving. The standard-library arithmetic core does not
certify fresh integration of the complete repository module or its transitive
imports.

## Rejected numerical directions

1. Minimal carry certificates are explicitly prior in b/report.tex:641–672;
   carry uniqueness, explicit least/greatest carries and normalization coherence
   are covered in i/j and later material.
2. Shared literal source-row decoding, including `N=q^3`, is explicit in b;
   a shorter linear-combination proof is not a fresh source-register mechanism.
3. `fourBlocks_cast` direct signed repunit residual is already the reversed
   identity of `NativeSourceMask.packing_four_block`, which itself uses
   `linear_combination q * h`. Packet zj explicitly rejects another rank-block
   cast cleanup under the earlier natural/integer rank bridge proposal.
   `PackingRankBalance.lean` is scratch-only and must not be presented as a new
   contribution. Its unused check was stopped deliberately.
4. Pell parity, signed residue composition, fundamental-unit criteria, positive
   recurrence comparison, error factors, and fixed-index-six anchors are prior.
5. Horner-block affine-map packaging would merely repackage prior finite-block
   certificates without deleting a distinct mathematical obligation.
6. A principal bitset ideal description appears distinct as an abstract API,
   but no current proof saving beyond existing short mask lemmas was identified;
   it is not recommended as a concrete simplification in this report.
