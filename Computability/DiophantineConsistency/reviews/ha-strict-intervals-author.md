# Genuine HA proofs for strict successor intervals

Author: `circuit_reduction`. This is an author receipt; root's independent
review remains separate. The author also wrote several reused HA arithmetic
and order leaves. No existing source or maintained equation was edited.

## Exact statements and proof

`HAStrictIntervals` proves, for arbitrary terms and their free parameters:

* `not_lt_zero`: actual HA proof of `¬ltFormula s 0`;
* `lt_self_succ`: actual HA proof of `ltFormula s (S s)`;
* `lt_succ_split` and `lt_succ_join`: both directions between
  `ltFormula s (S t)` and `ltFormula s t ∨ s=t`, under any finite context;
* `lt_succ_iff`: the conjunction of those two object-language implications.

The order formula literally supplies `d` with `s+S d=t`. For the successor
split its actual witness is eliminated, then the proved HA natural-case
formula splits `d=0` or `d=S e`. Successor injectivity yields equality in the
first branch; the second retains `e` as the new strict-order witness. Ambient
terms and every open assumption shift through both eigenvariable binders.
The reverse split uses the already proved transitivity or equality transport
and the actual zero witness for `s<S s`. Empty intervals contradict
`succ_ne_zero` after `add_succ`.

These proofs do not use order DNE, model semantics, a classical PA proof,
an arithmetic image axiom, or an assertion about standard-Nat instances.
They reuse the proved HA natural-case theorem; they do not introduce new
formula induction in this leaf. The companion checks include sparse/nested
terms using slots0/4/7, finite open contexts, successor-renamed contexts,
bound zero and one, and universal reclosure retaining free parameters.

## Frozen sources and private replay

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
|---|---:|---|
| `HAStrictIntervals.lean` | 105 | `60a199a6ffa8d8c34ddccef40883a71432e1e7e9937c129b78cc15db413bc342` |
| `HAStrictIntervalsChecks.lean` | 60 | `128b6daea4f2d6c27d131266daa12c83f94d0cde42798cd28aea87def40e0662` |

The complete sources and replay driver were read before execution, and the
entire final pair was reread after success. Final fresh main/check executions
passed in 1.857/1.635 seconds with an empty main log. All twelve final axiom
reports use only `propext` and `Quot.sound`.

Output directory: `/tmp/ha-strict-intervals-author-k21hls97/lib`.
Main object SHA:
`acbacc7febae8c2a1b392ca005caf573b877f64285fa0dd285dc026defe83dee`;
checks object SHA:
`4a8f363b0ebf4b291258cc2b2c15f97fe9530dfd375edefe74d12001c18f9e28`.
Invocations used full actual source paths, Lean4.32.0,
`-M6000 -j1 -DElab.async=false`, sequential execution and a 512MiB reserve.
Only new private objects were written; no symlink output was overwritten.

Three failed attempts are retained distinctly. The first two main failures
were unresolved namespace lookup of the existing `rename_ltFormula` helper;
the final source opens its actual `FoundationHAOrderBase` namespace. The
third main passed, but checks needed an explicit context type for a local
contradiction and a qualified axiom-print name. That failed check's error
recovery printed `sorryAx` and produced no accepted object. The final check
does not contain it. No theorem statement or logical premise was weakened.

## Authentication and reproducible records

The exact dependency set is **99 cached current-source modules**, including
**76 Foundation modules**, **327 cached artifacts** and **34 external boundary
names**. It is the accepted OrderDecidable98 closure plus root's independently
checked OrderDecidable main. All605 deduplicated source/object/toolchain/
manifest/provider/boundary pins match before and after each fresh invocation.
Import headers are reparsed, missing providers and reused imports of new
leaves are rejected, and no Foundation/dependency module is rebuilt.

The36-file bundle preserves every attempt's sources, inputs, logs and result:

* Summary `ha-strict-intervals-replay.json`:
  `1de845315e91de2bf02ba56bebe7cbeeea3323cbfa236609940dfefa49254b4a`.
* Bundle `FILES.json`:
  `9cc5d5fbba8621cfb14570c4a0ff75b466f6c9e5b46f9d9169d604b54cdf44f6`.
* Final `attempt-1793063558020311469/RESULT.json`:
  `265b9cf8b9327e311f5ad9c3bcc50e6877e30509eee1489aae35482647b6943b`.
* Final inputs:
  `8682e8058bca0d5035957344eab472aee576eae6a54fdd01a3edb8cb4311ee36`.
* Driver:
  `8f05564d4de7567ccdb345eba06bf4c80ad9df966a17237c52e5f638e5816210`.

The separately requested read-only plan is
`research/ha-bounded-quantifier-next-leaf-audit.md`, SHA
`125168a2dfcb9291ccf5b7c07f447cbbab7f52ecd9a40c6112225fc5f488f8b9`.
The broader bounded-quantifier decision theorem is not implemented here.
The actual Foundation Δ1 proof checker, its Σ1 representation and the
untranslated HA consistency comparison remain separate obligations.
