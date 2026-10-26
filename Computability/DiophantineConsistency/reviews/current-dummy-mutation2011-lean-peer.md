# Actual dummy mutation: independent Lean review

PASS, 2026-10-26. Reviewer: `controller_certificate`; author:
`circuit_reduction`. I read all 193 main lines, all 91 check lines, the full
author receipt, the complete direct high-mask import, the actual rank identity,
and the invoked word/carry/clause bindings before execution. No correction is
requested. I authored the reused `CurrentWordConstruction2011`,
`CurrentWordClause2011`, `CurrentWordTopBounds2011`, and `CurrentKernel2011`
dependencies; this review is independent of the new mutation packet, not of
those prior dependencies.

| Frozen input | SHA256 |
|---|---|
| `CurrentDummyMutation2011.lean` | `7bddcd9b7380e296a524ef229b467d4875e81a609dd4a4c5a7b126804a424f96` |
| `CurrentDummyMutation2011Checks.lean` | `12a960efd87d6596b6be56aab02176e18ddbe776ca07e8a305c498338ce45f25` |
| `CurrentWordHighMask2011.lean` | `f14b90ec3d4210c75dce2e4ece4de6f50bb1b2069e26b9329309eadd1c7da74a` |
| `NativeRankVariation.lean` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |

The new function identity updates exactly physical slot `base j+977`.
Its proof handles every other slot by the actual quotient/remainder
reconstruction, so a field-977 index belonging to another cell is unchanged.
This remains valid for the last canonical cell and `N=1`; no unproved
identification of cyclic and natural indices appears. The generic finite-sum
update identity is an ordinary natural equality and permits non-Boolean data.
The explicit old-value hypothesis `dummy j=0` is used exactly where setting the
slot to one must become an increment by one. It yields the full source change
`C'=C+radix^977*(radix^2011)^j.val`. The canonical representative exponent is
derived with `base_add_val`, not reduced modulo the exponent length.

Boolean hypotheses enter the normalized-word statements through the new
word's actual clause-based strictness and through construction of its carries.
`update_boolean` derives the new Boolean control property; marker data is
unchanged. Neither a marked tableau nor a high-mask premise is assumed, despite
the convenient import providing the index-reconstruction lemma. The old and
new `Facts.transport` fields refer to the same literal K and exact
`2^(47*(2011*s))` transport multiplier.

The crucial hypothesis remains explicitly

```
F + (K + 2^(displacement s))*dummyIncrement j < radix^(N*2011)-1.
```

The generic `transport_increment` first derives the proposed sum's congruence,
then uses both strict representative bounds. It does not infer an ordinary
equality from congruence alone. Strictness of the new F is proved from its
actual normalized clause, rather than supplied as a second target premise.
`exists_normalized_increment` constructs the new bounded carries and digits.
Only after both source and F equalities have been proved does `rank_decrement`
apply the complete integer rank identity. Its fixed MC/MF/J parameters retain
the already shifted source high-mask port exactly once. No positive rank or
safe-position assertion is smuggled into that ring identity.

The focused checks cover non-Boolean generic data, N=1, canonical last-cell
positions, a numeric marker value 23, preservation of the distinct marker1004
slot, and the already-enabled-dummy obstruction. The modular counterexample
with multiplier7 and modulus5 correctly shows why both strict representatives
can exist while the proposed ordinary increment still wraps. The separate
no-wrap example and q=1 zero-Gamma control also check the intended boundaries.
All 11 axiom reports use only `propext`, `Classical.choice`, `Quot.sound`, or no
axioms. No additional axiom, `sorry`, or unsafe evaluator was introduced.

Fresh direct builds used Lean4.32.0, `-M6000 -j1`, and the source's
`Elab.async false`. Both output objects were written only under
`/tmp/current-dummy-mutation2011-controller-peer/lib/DiophantineConsistency`.
The main was freshly compiled against existing pinned imports; the checks
used an overlay prepended **after** `lake env` initialization so their import
was the newly compiled main. Existing dependencies were reused; no entire
closure replay is claimed. The main and checks completed with no diagnostics:
3.96 seconds / 3,273,860 KB and 3.52 seconds / 3,259,528 KB respectively.

| Replay artifact | SHA256 |
|---|---|
| Main object, byte-identical to author | `b5957a17097df06225d106560bec2918217a91f86f27e9cecbffa0b06069aa38` |
| Checks object, byte-identical to author | `8e911f1ca754fbef3763988155397501b3cdebe63c57be2eaaa864061a8fa88a` |
| `main.log` | `23be722adbed0ae6b2fdd6245e636114f0fadc4bc07ef70c4f73c9d48da92930` |
| `checks.log` | `5540bc4be2f243d08349b3db253895a69375ba03a1a6eaa59611bcb93a2d5f1b` |
| `inputs-before.json` | `28bba5765c014ee93e369fc701c3093f8aa25a19b115a03e82593933a89a6ba7` |

All 24 pinned source/object/toolchain/author-receipt inputs were rehashed after
the two builds and remained unchanged; the before and after manifests agree.
No reviewed source, prerequisite object, shared document, or Git state was
modified. This receipt accepts the exact conditional mutation interface. It
does not discharge its physical safety/nonwrapping bound, construct an orbit,
or establish the converse consistency endpoint.
