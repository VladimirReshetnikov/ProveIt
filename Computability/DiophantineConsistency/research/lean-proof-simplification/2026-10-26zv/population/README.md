# Constructed-packing rank: one residual deletion and one micro cleanup

**All Lean candidates are UNCOMPILED.** No installation, Lean elaboration,
kernel check, axiom audit or timing measurement was performed. The upstream
checkout is not edited. Source pin:
`9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

## Result

| Exact target | Entire source file | Entire candidate file | Net physical deletion |
|---|---:|---:|---:|
| `CurrentPackingRank2011.rank_gt_twice_window` | 138 | 133 | 5 |
| `NativePackingPopulation.disjoint_add_lt` (optional) | 57 | 55 | 2 |
| **Total, including all context** | **195** | **188** | **7** |

No production helper, wrapper, definition or import is added or removed.
All comments, namespaces, options, public theorem headers, variable and
`omit [NeZero N]` scopes remain byte-identical. Full-file counts include
blank lines and comments; they are source-size counts, not performance claims.
The second row is optional housekeeping only, not a new mathematical contribution.
The primary recommendation saves five lines; seven is the optional-inclusive total.

## Primary candidate: discharge the actual cubic lower bound directly

Source: `CurrentPackingRank2011.lean:88–100`; changed proof span: `90–97`.
Write `u = width*N`. The already-proved `q_binary` identifies `q N = 2^u`.
The original proof establishes `u<q`, `u>0`, `2≤q`, `2≤q²`, and finally
`2u<2q≤q³`. These intermediate bounds are unnecessary: use

```
2*u ≤ 3*u < 2^(3*u) = (2^u)^3 = q N^3.
```

The strict step is the existing core theorem `Nat.lt_two_pow_self`. The exact
replacement is:

```lean
  have hc : 2*(width*N) < q N^3 := by
    rw [q_binary, ← pow_mul]
    exact (show 2*(width*N) ≤ (width*N)*3 by omega).trans_lt Nat.lt_two_pow_self
```

The original `hn`, `hz`, and final `rwa` lines are retained verbatim. Thus the
proof still uses `fourBlocks_ge_cube C F hC hCF`, then the exact existing
natural-to-integer binding `fourBlocks_cast C F hC hCF`. The full theorem
shrinks from 13 to 8 physical lines, including its unchanged two-line header.

The small numerical inequality even holds for `u=0`, but this does **not**
remove or weaken `[NeZero N]` from the actual theorem. The same positive `C`,
strict `C+F<q N`, once-shifted `highPort+beta`, explicit subtraction domains,
and rank expression are retained. No source-system or Pell premise is added.

## Optional housekeeping candidate: rewrite the existing disjoint-sum identity in place

Source: `NativePackingPopulation.lean:12–17`; changed span: `14–17`.
Instead of naming `JM1984.add_eq_land_add_lor A M`, rewriting that local
equality, and rewriting the goal, perform the identical rewrites in the goal:

```lean
  rw [JM1984.add_eq_land_add_lor, hm, zero_add]
  exact Nat.or_lt_two_pow hA hM
```

This removes only a transient equality and two tactic lines; it does not
claim a new disjointness, population or binary-word abstraction. Both strict
window bounds and the zero-AND condition are unchanged, including `u=0`.
The entire theorem shrinks from 6 to 4 lines. Its callers, exact
`four_block_exact`, `mask_population`, and `calibrated_population`, are
unchanged. In particular, population remains an **equality**, not merely an
upper/lower inequality, and the top block remains unrestricted.

## Prior-contract boundary and rejected alternatives

All proposals in both exclusion directories and the previously delivered
round five are assumed available, including optional/uncompiled alternatives.
This packet does not recast those contracts as new work:

* Packets zc/zf and fresh incoming threshold proposals already remove
  inductions through common-base/quadratic exponential bounds. Those exact
  threshold contracts remain granted. The claim here is only the five-line
  deletion at the newly constructed rank client.
* `Nat.lt_two_pow_self` is not a new technique: packet u's
  `NativePellScaleBounds.source_binary_exponent_bound` already uses it to
  compare a binary exponent with a source rank. That proof uses a
  source-system-derived `3*q<rank`; the current client instead has the
  independently constructed `q³≤fourBlocks`. No new exponential theorem
  or source-rank interface is credited.
* Prior EX051 natural/integer rank bridges, generic rank perturbation,
  coherent word/carry views, repeated-word population, mask decomposition,
  and canonical-witness interfaces are excluded. The existing cast bridge
  and constructed witness are deliberately not changed.
* A generic four-block/list population helper would merely repackage prior
  word/carry contracts and can cost more than the short current proof.
  No such abstraction is proposed. `mask_population` and
  `packing_rank_population` are unchanged, rather than weakened or moved
  behind a newly charged helper.

The independent baseline reviewer screened the fresh incoming reports and
inherited prototypes; no exact target overlap was found. This is a bounded
source-specific novelty decision, not a proof of global mathematical novelty.

## Artifacts and verification

* `source/`: complete unchanged pinned files.
* `candidates/`: complete proposed replacement files, not isolated snippets.
* `patches/`: independently replayable exact unified diffs.
* `evidence/accounting.json`: exact changed spans, hashes and counts.
* `evidence/library_api.json`: read-only official Lean v4.32.0 API excerpts.
* `evidence/repository_dependency_excerpts.json`: pinned existing sum and
  exact population identities read from local Git objects with lazy fetch off.
* `checks/audit_population.py`: newly authored portable standard-library
  Python auditor; it reads files and prints JSON, with no writes, network,
  subprocesses, compiler calls or imports from incoming archives. Checks use
  explicit runtime guards and remain active under Python `-O` (both runs pass).

Run from any directory:

```sh
python3 /path/to/population/checks/audit_population.py
```

Optionally compare the delivered snapshots with a local pinned checkout:

```sh
python3 /path/to/population/checks/audit_population.py --upstream /path/to/repo
```

The auditor verifies complete-file hashes, replays each patch, and proves by
byte comparison that only the stated proof spans changed. It checks 3,280
bounded disjoint sums, 66,430 exact population cases (1,085 calibrated),
2,340 unrestricted-top-block cases, 257 cubic growth cases, and 13,869
coherent packing/cast/strict-rank cases. Six explicit mutation witnesses
reject omitted disjointness, a missing low-block bound, weakened exact
population, missing `C>0`, missing `C+F<q`, and a double beta shift.

The arithmetic models use small abstract powers of two, not the literal
94517-bit radix-width construction. They are independent bounded tests, not
universal proofs or Lean acceptance. The retained actual source dependencies
provide the mathematical bridge; compilation remains a separate pending
validation step in an authorized, prepared Lean environment.
