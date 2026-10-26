# Canonical residues for the bounded-forall certificate decoder

## Proposal and exact targets

At pinned commit `96520cd1a5179f470b4da127bd47bc26a8d808ff`, replace the coordinatewise `choose j` / `min (a i) j` block in:

- `Computability/DiophantineConsistency/Lean/DiophantineConsistency/BoundedForallCertificate.lean:39–46`;
- its duplicated proof in `Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean:238–245`.

Use one shared arithmetic theorem:

```lean
theorem prime_dvd_descendingProduct_iff {p a u : ℕ} (hp : p.Prime) :
    p ∣ ∏ t ∈ Finset.range (u + 1), (a - t) ↔ a % p ≤ u
```

The decoder then uses:

```lean
let j := fun i => a i % p
have hWitness_bound i : j i ≤ u i :=
  (prime_dvd_descendingProduct_iff hp).mp (hPrime_product.trans (hWitness_product i))
have hWitness_congruence i : a i ≡ j i [MOD p] := (mod_modEq _ _).symm
```

The old argument chooses a separately divisible factor for each coordinate and repairs truncated subtraction with `min`. The new argument chooses the least residue once a row prime `p` has been fixed. Each required congruence is the standard residue identity. Its size bound follows from the shared divisibility criterion. The public certificate statement, compiled arithmetic expressions and reverse CRT construction need no change.

This removes arbitrary **coordinate-factor choice**, not every choice in the theorem: the row prime is still obtained existentially and the reverse direction still selects a witness family. The displayed `ModEq` fact is `mod_modEq.symm`, not literally `rfl` because it includes repeated remainder reduction.

## Why the helper is valid

If a prime divides the descending product, it divides a factor `a - t` with `t ≤ u`. Set `s = min a t`, so `s ≤ a` and natural truncated subtraction satisfies `a - t = a - s`. Thus `a ≡ s [MOD p]`, and

`a % p = s % p ≤ s ≤ t ≤ u`.

Conversely, if `a % p ≤ u`, the product contains the factor at `t = a % p`; `Nat.dvd_sub_mod a` says that `p` divides that factor. The proof covers `a < t` and zero factors without a side assumption such as `u ≤ a`. Primality is necessary in the forward direction: for `p = 6`, `a = 3`, and `u = 1`, the product is `3 * 2 = 6` while `3 % 6 = 3 > 1`.

## Novelty against the stipulated baseline

The closest old proposal is packet `2026-10-26n`, section S1, `report/sections/09_supplemental.tex`: it replaces the reverse CRT index branch's `gcongr; exact?` with the already available explicit congruence. Both the report and `supplemental/SUPPLEMENTAL_REVIEW.md` explicitly leave the preceding falling-factorial branch unchanged. Its included `BoundedForallCertificateCandidate.lean:39–46` still contains the original factor-selected witness. Therefore the proposed change remains after that prior fix is assumed applied.

Early Euclidean-certificate uniqueness/canonicality proposals concern quotient/remainder certificate correctness; controller canonical-residue proposals concern field representatives and affine subset constructions. They do not prove the descending-product criterion or change this bounded-forall witness reconstruction. All available `.tex`, `.md`, and `.lean` sources across the excluded research tree were searched for falling factorials, the exact client name, and canonical residue/descending factorial variants. Text inside every incoming ZIP archive was also scanned recursively; `novelty_archive_search.json` records hits. This semantic comparison, rather than identifier absence alone, supports novelty.

## Exact size accounting

Each old witness block is 8 physical lines including two explanatory comments; each new block is 5 including one explanatory comment. The shared helper is 16 nonblank lines including its doc comment, plus one separating blank line at insertion.

| Complete file | Before | After | Delta |
|---|---:|---:|---:|
| `MRDPCore.lean` | 391 | 405 | +14 |
| `BoundedForallCertificate.lean` | 98 | 95 | -3 |
| Combined | 489 | 500 | +11 |

This is a conceptual simplification with a useful new arithmetic interface, **not a claim of net source-line reduction**. The hypothesis that prior proposals have been applied does not alter this delta: the nearest prior CRT change touches a disjoint branch and is not included in the new patch or counted as a new saving.

## Artifacts and validation scope

- `CanonicalResidue.lean`: standalone shared criterion with axiom audit; both initial stdin check and saved-file check succeeded with Lean 4.32.0; the saved-file receipt is hash-bound.
- `CanonicalDecoder.lean`: focused complete forward-decoder proof. It exposes only the unchanged `encodedModuliProduct_eq_prod` fact as a hypothesis, replaces `v.head` by its scalar value, and retains prime selection, factorial separation, index congruence, polynomial congruence and final equality recovery. This is a faithful check of the changed argument; it does not claim a complete import/build of both original modules.
- `Diophantine/Common/MRDPCore.lean` and `DiophantineConsistency/BoundedForallCertificate.lean`: complete candidate sources with original theorem statements.
- `canonical-residue.patch`: patch for both source paths, adding the helper in namespace `MRDP` and reusing it from the requested target.
- `*.validation.json` and `*.validation.log`: compiler scope, hashes, outcome and full output.
- `source_receipt.json`: pinned auxiliary-source Git blob and SHA-256. The original source was fetched at the exact pin; its Git blob was independently recomputed.
- `mathlib_source/Mathlib/Data/Nat/Prime/Factorial.lean`: the unchanged 46-line Mathlib dependency, locally compiled because its `.olean` was absent from the available partial cache. It is not a proposed Mathlib change.

A complete modified `MRDPCore.lean` compilation was attempted and stopped immediately at the missing cached `Mathlib.NumberTheory.Dioph.olean`; no conclusion about the rest of that module follows from the attempt. The focused check is designed to give meaningful verification without rebuilding unrelated MRDP dependencies. A normal checkout with complete Mathlib can run `lake env lean CanonicalResidue.lean` and `lake env lean CanonicalDecoder.lean`, then check the two candidate modules after applying the patch.

## Independent novelty reviews

The middle-corpus auditor confirmed no n–z proposal performs this product-witness canonicalization; the closest Euclidean-certificate work does not provide the prime-divisibility interval interface. The latest-corpus auditor independently confirmed no overlap through za–zq, original incoming archives, and the additional six incoming ZIPs found in the closing-head check. This review supports the narrowly stated criterion/forward-decoder idea; it does not justify a broad claim that canonical residues as a general technique are new.

## Final validation outcome

The standalone helper and the focused full forward decoder both passed with exit code 0. The final focused source SHA-256 is `34175920284a9a795b314b4be3e28d60189225c15d98a51c50db525d23bcb787`; the standalone source SHA-256 is `0ab4cecbe1c4f81597ac6d7738eefdee08eeb97a724d0b0cac1463cc00b0237d`. Their axiom audits report exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx`.

The focused check caught and resolved an integration-only ambiguity: opening both `List` and `Finset` requires `Finset.mem_range.mp` in the helper. The complete production candidate and focused proof use that qualification. The standalone minimal-import file retains its already valid shorter name and matches its saved successful receipt exactly. This qualification does not affect the source-line counts.

Compiler: `/workspace/scratch/77ef15dff129/toolchain/lean-4.32.0-linux/bin/lean` (Lean 4.32.0). Mathlib objects came from `/workspace/scratch/77ef15dff129/ProveIt/.lake/packages/mathlib/.lake/build/lib/lean`, supplemented only with the locally recompiled unchanged `Mathlib.Data.Nat.Prime.Factorial` module. All final `*.validation.json` records include exact paths, elapsed time, scope and source hashes. The original full-module import limitation remains as described above.
