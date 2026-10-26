# Exact finite-order client simplifications

## Result

Two independently reviewable local changes in `WangTiles942PhysicalOrder.lean`:

| Candidate | Original → proposed whole-file physical lines | Net | New helper/import cost |
|---|---:|---:|---|
| Finite-order rigidity (`order_iso`) | 180 → 156 | −24 | None; all order-isomorphism packaging included |
| Library finite predecessor (`fin_pred`, optional definition edit) | 180 → 173 | −7 | None |
| Combined | 180 → 149 | −31 | None |

These are exact new-client uses of existing library mathematics, **not** new general theorems, certificate dispatch, or a runtime claim. Lean has **not** been run. Static, patch, and finite smoke checks pass; integration/elaboration remains an explicit gate.

Source pin: `09d65a93c9df8684c1a226341d6a5120623d1cdb`. Source path: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942PhysicalOrder.lean`. Baseline SHA-256: `eafbd5914bf4219d6ce48b501c8be41c228253ef719b65a02e7d167ada0ce3e9`.

## A. Replace the custom finite-order rigidity induction

The theorem `strictMono_fin_eq_self` (original lines 68–97) already has exactly the conclusion of the Mathlib finite-order isomorphism rigidity result. Instead of reproducing strong induction, obtain the finite surjectivity of the strictly monotone map, package the map as an order isomorphism, and use `Fin.coe_orderIso_apply`:

```lean
theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f)
    (i : Fin n) : f i = i := by
  let e : Fin n ≃o Fin n :=
    ⟨Equiv.ofBijective f
      ⟨hf.injective, Finite.surjective_of_injective hf.injective⟩, hf.le_iff_le⟩
  exact Fin.ext (Fin.coe_orderIso_apply e i)
```

The theorem declaration is 30 → 6 lines; its body is 28 → 4. The original `rankMap_eq` client and all public statements remain unchanged. This works uniformly for `Fin 0` (vacuous), `Fin 1`, and arbitrary finite size. It does not inspect the 941-row certificate or recompute any floor comparisons.

The required theorem occurs at the end of [the pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Order/Fin/Basic.lean). Its full source snapshot and GitHub blob receipt are in `evidence/mathlib_fin_basic.*`. That module is already imported by `WangTiles942PhysicalData`; the candidate adds no import. The equivalence's forward map reduces to `f`, so the library numeric equality yields the existing result by `Fin.ext`.

### Counterfactual novelty

The corpus baseline is assumed available even when not maintained in this pin. The baseline reviewer found no earlier proposal for this exact custom theorem. The nearest older contracts are: `k/novelty-audit.md:67–69`, an exploratory direction involving order embeddings; incoming/placed report `i` §LE04, finite invariant-set injectivity implying surjectivity; and report `s` rank/cardinality reasoning for `strictUpper`/`strictRank`. Those do not remove this newly introduced explicit induction. Credit only this exact client deletion; finite surjectivity and order rigidity are existing library results, not new proposed helpers.

## B. Optional: replace the hand-built predecessor representation

Original lines 41–52 manually subtract one, establish the smaller `Fin` bound with arithmetic, and prove successor cancellation. The standard operation has exactly this value:

```lean
def nonStartIndex (j : Fin 941) : Fin 941 :=
  (abstractIndex j).pred (abstractIndex_ne_zero j)

theorem nonStartIndex_succ (j : Fin 941) : (nonStartIndex j).succ = abstractIndex j :=
  Fin.succ_pred (abstractIndex j) (abstractIndex_ne_zero j)
```

This is **a definition-body edit**, separately selectable, not a proof-only patch. It changes neither signature nor computed index: in pinned Lean 4.32.0, `Fin.pred` is `subNat 1`, and `subNat`'s value is natural subtraction. The core source explicitly proves `Fin.val_pred` by `rfl`; `Fin.succ_pred` has the exact required signature. The proposed `PhysicalOrderRegressionChecks.lean` includes an `rfl` comparison with the complete original constructor expression. That regression is prepared, **not compiled**.

The definition plus cancellation block changes 12 → 5 physical lines (11 → 4 nonblank). The explicit nonzero hypothesis remains supplied from the already-proved `abstractIndex_ne_zero`. No implicit wraparound, changed rank convention, or change to the protected Start is introduced. All actual row indices are in 1…941, and subtract-one/successor recovery was checked for each of the 941 literal pairs.

Core source attribution: [Fin.Basic at v4.32.0](https://github.com/leanprover/lean4/blob/v4.32.0/src/Init/Data/Fin/Basic.lean), definitions `subNat` and `pred`; [Fin.Lemmas at v4.32.0](https://github.com/leanprover/lean4/blob/v4.32.0/src/Init/Data/Fin/Lemmas.lean), `val_pred` and `succ_pred`. Snapshots/receipts under `evidence` retain the fetched blob hashes. The independent corpus screen found no earlier proposed `Fin.pred` use for this or a comparable bounded-subtraction client. Report `v` includes a `Fin.pred` occurrence only in bundled Mathlib evidence (`EquivFinBasic.lean`), not as a recommendation. The novelty is this fresh client, not predecessor cancellation itself.

## Accounting and validation

- All three full-file candidates preserve every public declaration header and import. No new helper theorem, imported module, axiom, `sorry`, `admit`, or `native_decide` is added.
- Separate and combined patches pass `git apply --check` against the frozen upstream. The combined patch is the canonical way to select both changes.
- `build_candidates.py` is newly authored, standard-library-only review code. It reads frozen sources and writes only this `physical/` directory; it does not execute repository or incoming scripts.
- Finite smoke checks enumerate all endomaps of `Fin n` for `n=0,…,6` (50,070 maps total): the strictly increasing maps are exactly the identity maps. This is illustration, not verification of an unbounded Lean theorem.
- The literal certificate is independently parsed as data: 941 indices are exactly 1…941; all 940 adjacent recorded-weight inequalities are strict; predecessor/successor arithmetic holds for every index. These checks do **not** independently decode `selectorWeight` or establish the original data certificate.
- `check_physical.py` is the separate read-only replay entry point; it prints JSON and uses no Python `assert`. Its default baseline is the enclosing package’s `baseline/` tree; during this review use `--baseline-tree ../upstream` from `physical/`. Both normal and optimized-Python runs pass. The enclosing package must retain original `PhysicalOrder` and `PhysicalData` under their canonical source paths.
- Complete measurements, hashes, and check status are in `evidence/checks.json`. Local-library source receipts and candidate regression files add review artifacts, not production source helpers.
- No compilation-speed, proof-term-size, or axiom-list claim is made for these uncompiled candidates. Before adoption, rebuild the modified `WangTiles942PhysicalOrder`, its existing checks, and the new regression against the pinned dependencies and inspect axiom output. Do not let checks silently import an old `.olean` for the replacement module.

## No recommendation / excluded work

`WangTiles942PhysicalData.rows_good` is long, but shortening its 59-chunk assembly is already covered by the prior generic finite-certificate dispatch/assembly contract E18. No credit or patch is offered for that. `PowerDimensions` uses explicit cofinal exponents and a width split, and is already short; packaging those behind another helper would not produce a demonstrated marginal reduction after the existing geometry/transport baseline. No change is recommended there.
