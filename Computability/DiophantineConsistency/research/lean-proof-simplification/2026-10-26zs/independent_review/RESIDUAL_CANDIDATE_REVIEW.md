# Independent review of the round 6 residual arithmetic candidates

## Decision

- **`fourBlocks_cast`: retain at most as a narrow, previously unproposed client detour removal.** The exact existing `NativeSourceMask.packing_four_block` certificate is not new. The proposed change removes this client's named `hbeta`, instantiated `hh`, and fully expanded `hB` equation, while preserving all subtraction guards. Source body: 23 to 12 physical lines, 1,037 to 586 UTF-8 bytes. No new theorem, import, executable definition, mathematical claim, or proof infrastructure. Adoption trades an explicit reusable-lemma boundary for a shorter inlined certificate; shorter source is not automatically the better abstraction.
- **`rank_gt_twice_window`: exclude as a repeated proposal mechanism.** Do not deliver it or count its four-line source saving as a new round 6 result, including under an “optional cleanup” label.
- **The combined patch is not a recommended deliverable**, because it includes the excluded rank-growth edit. Its checks are retained only as audit evidence.

This supersedes the preliminary suggestion that both edits could be retained as optional client cleanup. The stricter rank-growth decision followed inspection of the prior packet's future-work reservation, not a correctness failure.

## Scope and provenance

Source pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

Frozen target: `sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean`, SHA-256 `614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546`.

The reviewed retained candidate is `arithmetic_candidates/fourblocks_certificate/candidate/CurrentPackingRank2011.lean`, SHA-256 `e702cc6554f32c83d142b1b3ea594a0e7924ae19b8b085f6deff1302ba38740b`. The patch is in its parent directory as `fourblocks_certificate.patch`.

The audit is **source/model review, not Lean compilation or kernel validation**. It makes no timing, proof-term-size, axiom-footprint, downstream-build, or hypothetical fully integrated baseline claim.

## Exact proof and guard review

The theorem header, ambient `{N : ℕ} [NeZero N]`, all executable definitions, all other proof bodies, and all three imports are byte-identical for the retained single-candidate patch. In particular, the once-shifted fourth source port remains `(highPort + beta : ℕ)` in `rank`; it is not shifted twice or replaced by an unshifted mask.

`CurrentPackingRank2011.lean:53–59` establishes the same local facts before either proof's algebra. All five `Nat.cast_sub` arguments from the original proof are preserved modulo indentation:

| Natural subtraction | Required bound | Evidence retained |
| --- | --- | --- |
| `C - 1` | `1 ≤ C` | `hC` via `omega` |
| `highPort * repunit width N - 1` | `1 ≤ highPort * repunit width N` | `highPort_pos`, `repunit_pos`, `Nat.mul_pos` |
| `q N - C` | `C ≤ q N` | `hCF` via `omega` |
| `(q N - F) - 1` | `1 ≤ q N - F` | original `hFq : F + 1 ≤ q N`, via `omega` |
| inner `q N - F` | `F ≤ q N` | original natural hypotheses via `omega` |

The nonzero period instance is retained and still supports `repunit_pos`; no positivity theorem is silently generalized. Addition/multiplication/power casts introduce no extra domain obligations. The cast of `highPort + beta` becomes the intended sum of integer casts.

`CurrentNativePacking2011.lean:34–43` gives `beta * repunit width N + 1 = q N`. After the unchanged `congrArg` and `push_cast`, `hb` is its integer equality. Writing `J` for the repunit and `MC`, `MF` for the ports, the exact ordinary-integer residual is

```
fourBlocks_expansion - windowRank(q, C, F, MC, MF + beta, J)
  = -q * (beta * J + 1 - q).
```

Thus the sign in `linear_combination -(q N : ℤ) * hb` is correct. It is a polynomial equality over integers, with no division or cancellation hypothesis and no new circular dependency. The source already imports the required tactic environment; the recorded import path reaches `Mathlib.Tactic`, and the imported `NativeSourceMask` already uses `linear_combination`.

The proof is plausible as written at the source level. Actual elaboration of `unfold`, the guarded `push_cast` simplification, and the final tactic remains untested.

## Existing certificate versus prior proposal

These are distinct novelty questions and should not be conflated.

1. **Existing maintained lemma.** `NativeSourceMask.lean:87–94` explicitly says the beta–J relation is used exactly once and proves its four-block identity by `linear_combination q * h`. Its left-hand polynomial is ring-equal to `windowRank`. The candidate inlines that very certificate with the opposite equality orientation and the `+1` form of the balance. It is not a newly discovered signed polynomial certificate.
2. **Prior proposal scope.** The exact EX051 source is `lean_simplification_round3_20261026/baseline_audit/placed/2026-10-26c/notes/arithmetic.txt:227–251`. It proposes a shared source-facts API for repeated `R := nativeRank.toNat`, its integer cast equality, and rank bounds in `NativePellFirstIndex`/source-window clients. Its natural-subtraction warning is also already assumed. The present candidate has no `toNat`, does not build that source-facts API, and receives no credit for preserving those old cast guards. The scoped prior review did not find a proposal to inline `packing_four_block` or delete this client's explicit intermediate polynomial. Consequently this **particular client-structure edit**, not its algebra/cast method, may be retained under the root's strict rules.

The baseline reviewer independently reached this narrow distinction. Mere absence of the target filename was not used as the novelty argument; the actual prior contract was read.

## Why rank growth is excluded

The candidate rewrites `q N ^ 3` as `2 ^ ((width * N) * 3)`, uses `Nat.lt_two_pow_self` at that exponent, and closes the linear comparison by `omega`. Mathematically, `2u ≤ 3u < 2^(3u)` is valid for all natural `u`, including zero. Its unchanged final natural bound and cast chain is valid at source level.

But the prior packet at `lean_simplification_round5_20261026/baseline_audit/closing_sources/2026-10-26zc/report.tex:345–375` already proposes normalizing a power expression, applying `Nat.lt_pow_self`, and closing by `omega`. More decisively, **lines 570–582** reserve systematic same-base normalization or exponent shifts that expose a standard growth inequality and a resulting linear/polynomial certificate. Applying that method at `3u` adds no different residual mechanism. The prior reservation need not supply a fictitious universal callable Lean theorem to exclude repeated research. A new client name or a four-line source reduction does not reopen it.

The root and baseline reviewer were informed immediately when the broader reservation changed the preliminary classification.

## Reproducible independent checks

Run from any directory:

```sh
python /workspace/scratch/ce29ab924f1c/lean_simplification_round6_20261026/independent_review/check_residual_candidates.py
```

The script uses only the Python standard library and the installed `patch` command. It does not invoke Lean. It checks:

- exact frozen source hash;
- unchanged statements, definitions, imports, and all text outside the selected proof bodies;
- all five cast guards unchanged modulo whitespace;
- exact zero-fuzz application of each supplied patch in a temporary independent fixture, including equality with the supplied candidate file;
- source-line and UTF-8 byte measurements;
- exact multivariate integer coefficient arithmetic, independently implemented without the author's SymPy code, proving the displayed residual and its identity with the existing `packing_four_block` polynomial;
- 13,230 guarded small natural model cases;
- a negative control outside the actual theorem's fixed port definitions: if `MF * J = 0`, the natural expression can be 241 while the integer expression is 237, demonstrating why the preserved guard cannot be dropped;
- the normalized rank-growth arithmetic at `u = 0` through `512`, retained as rejected-candidate correctness evidence only;
- existing source import paths to `NativeSourceMask` and `Mathlib.Tactic`.

Output: `RESIDUAL_CANDIDATE_CHECKS.json`. `CHECK_RUN_OUTPUT.json` records successful normal, `-O`, and `-OO` runs with byte-identical output, plus injected wrong-source-hash and wrong-polynomial-sign checks rejected both normally and under `-O`. All runtime guards use explicit `require` calls, not optimizable assertion statements; the failure path is also exercised on every run. Finite cases are not universal proofs, and exact polynomial model checking is not Lean elaboration.

## Verification gap and action status

**Pending, not denied:** Compile the retained candidate in a complete checkout at the frozen pin, with Lean `4.32.0` and mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`, then compile its existing checks/clients. The minimal target command from the project Lean root is:

```sh
lake env lean DiophantineConsistency/CurrentPackingRank2011.lean
```

Reason this was not run: neither `lean` nor `lake` is on this execution environment's PATH, and the source mirror is selective rather than a configured full Lean checkout. No toolchain installation, desktop launch, permission escalation, upstream edit, or network mutation was attempted or authorized by this audit. The dependency-path check reports ten nonlocal modules absent from this selective import-root view; this is not a newly introduced dependency error.

Completed work: source proof review, semantic prior-scope comparison, guard/identity/patch checks, independent model checks, and precise measurement. Still uncertain: Lean elaboration, kernel acceptance of the replacement proof, axiom comparison, downstream integration, and performance.
