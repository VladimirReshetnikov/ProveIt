# Latest witness archive: focused comparison and fresh checks

This supplement reviews the witness archive newly included at ProveIt commit
`99f17206a77a04d36a9bb7dd04ce2e5d0360cf7d`. The exact archive is
`pa194_witness_research_2026-11-15.zip`, SHA-256
`cc51ef4f2858e37cc72c5079bb6f8b0d86ce0ed9eae1aed428c1bd69baffb4cc`,
Git blob `4b142f53b8c3c677172409aa2ca33cf6c60f7deb`.

The source files here are a selected extraction. `UPSTREAM_README.md` describes
the full original archive; its complete verification commands require that
archive. Our fresh check receipts and their exact scope are listed in
`review_provenance.json`. Upstream notices and licenses are retained.

## Two additional prior designs

Let `N(A)=I(A,1)`, `W(d,h)=U(d,N(E(h,d)))`, and
`X(d,h)=U(d,N(U(d,h)))`. The numerical contradiction code is 1; an explosion
rule cannot be assumed before it has been derived in the chosen calculus.

| Design | New logical presentation | AX tokens | Source sites/outcomes | State budget |
|---|---|---:|---:|---|
| PA194H5X | Replaces `W(d,h)→1` by `W(d,h)→a`, with a independent of d,h | 189 | 3677 / 4786 | 134 fixed + 69 readers − 9 folds = 194 |
| PA194JH5X | Also replaces `(X(d,h)→1)→h` by `(X(d,h)→h)→h` | 188 | 3683 / 4794 | 134 + 69 − 9 = 194 |

Both use the ordinary sixth-head premise order, explicit-binder
generalization, visible MP without a dummy push, cache-only Shift, and the
four-field/eleven-entry AX interface. Their reported exact startup is 57922.
The new logical presentations and source counts are attributed upstream;
their complete physical contracts were not rerun during this focused review.
Their proof calibration imports the same revised AX11H archive
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.

Dense hashes:

- H5X: `caffdd9f10d87d0d050eff07ab8f6e8edd9ab443aa94c948f03ee5316e37b614`.
- JH5X: `70be32fe352ee0fb29581f1037948f429334cfc9c6bcaa813aba43c4efba0148`.

## Fresh logical replay and the repaired coupled route

The supplied independent Hilbert checkers were freshly run. H5X's two
directions have 13 and 1 lines. Its 16-line explosion proof uses only one
diagonal instance, one closed generalization, three K instances, two S
instances, seven MP steps, one distribution instance, and one H5X instance.
**It uses neither the old first head nor Peirce.** The J translations have
95/72 lines; the additional generalized J_A translations have 358/72 lines.
These are checked schematic proof templates over the explicitly inherited
derived implication basis, not new Lean endpoint proofs.

This new fifth head removes the obstruction to the earlier isolated dual-head
proposal. Write

`B_d(h) = N(h) → U(d,N(U(d,h)))`,

`R_d(h) = h → U(d,N(U(d,N(h))))`.

The witness archive supplies the coupled `B + H5X` translations to the old
calculus (204/131 lines), also freshly replayed. Our earlier dual family was R.
The two schema families are uniformly interderivable using K, S, theorem
generalization and distribution, without explosion:

1. The pure implicational theorem `h→N(N(h))`, composed with `B_d(N(h))`,
   gives `R_d(h)`.
2. `R_d(N(h))` gives
   `N(h)→U(d,N(U(d,N(N(h)))))`.
   Generalize `h→N(N(h))` and use distribution to get
   `U(d,h)→U(d,N(N(h)))`. Contraposition gives
   `N(U(d,N(N(h))))→N(U(d,h))`. Generalize this theorem and distribute once
   more, then compose with the displayed R instance to obtain `B_d(h)`.

Thus `R + H5X` is a sound newly available coupled presentation. This does not
invalidate the countermodel for changing the first head alone: the additional
H5X family supplies precisely the missing independent explosion derivation.

The archive already searched `B + H5X`: its recorded run made 6694768
mutations, accepted 1186057, and obtained effective reader score 66, a nominal
`134+66=200` controls. These are **attributed upstream search counts**, not a
fresh repeated search or a lower bound.

As a bounded additional check, `audit_compositions.py` freshly reprices that
one best binary-tree shape and the corresponding R replacement. It reproduces
`78−12=66` effective readers for B, and obtains `81−10=71` for R, nominally
200 and 205 controls. The complete 17-token head replacement is checked in a
free term algebra; the rest of the 189-token word and the tree shape are kept.
These are two fixed grammar prices with optimistic matching, not validated
new TMs or an optimization search.

## The 193-state runtime core is explicitly rejected

The archive's Runtime193 patch redirects target 301 to 88, deletes 301,
sets `88/0 = 0 L 51`, and sets `51/0 = 0 R 122`. Its native table hash is
`df4646a9d0cf7f6c58ad12bd7b6d18a60d869cda06e720896d10fad59d8a6903`.

Its full prepared-frame runtime at a 36-cell minimum header is an upstream
positive result. That does not initialize a blank machine. We freshly replayed
the exact rejection traces for **all 193 blank start controls**: two halt and
191 enter certified escaping self-loop rays, in at most 93 transitions. The
ten boundary-84 visits contain at most four ones; every complete canonical
frame needs at least twelve. This is a proof about that fixed core and those
blank starts, independent of a cutoff or header reinterpretation. It excludes
neither additional bootstrap edits nor other 193-state architectures.

## Composition with the two delivered constructions

The LCSF3 shortcut cannot simply be copied: these witness tables enter native
190 via `139/0 = 0 R 190`, giving predecessor bit 0, and their row `190/1`
is `1 R 99`. LCSF3 requires the different LC predecessor invariant and the
three-step path beginning with `190/1 = 1 L 73`.

Both witness tables do have the four original MP decoder rows used by our MP
reassociation. We checked the exact four-row composition on their raw
203-state tables at the fixed allocation. For each table, all nine existing
simultaneous folds still pass their 36 local cases. The complete non-box
three-step predecessor-bit matching graph has maximum nine both before and
after the edit: eleven eligible pairs for H5X, twelve for JH5X. Consequently
this immediate composition supplies no tenth fold in that precise model and
no 193-state nomination. Full source/runtime/startup proofs for these
composites were not run, so no extra accepted machine is claimed.

## Reproduce these focused checks

From this directory, with Python assertions enabled:

```sh
python3 -B logic/verify_logic.py logic/certificates --output fresh_logic_replay.json
python3 -B logic/verify_j.py logic/j_certificates --output fresh_j_replay.json
python3 -B logic/verify_ja.py logic/ja_certificates --output fresh_ja_replay.json
python3 -B research/runtime/header_feasibility/replay_traces.py research/runtime/header_feasibility
python3 -B audit_compositions.py
```

The original broad randomized and physical searches were not rerun. None of
the focused checks establishes a valid machine with fewer than 194 states.
