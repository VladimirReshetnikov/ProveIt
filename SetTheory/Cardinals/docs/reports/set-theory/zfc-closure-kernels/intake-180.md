# Intake 180: a 223-state machine for conditional K

Placement `9b1fa851a9` imports one package as **Source 127** and retires its ZIP. The host now
reconciles **127 sources**; the collection remains **290 reports**. The
[placement map](data/intake180-placement.json) accounts for all 165 members:

- 131 staged byte-identical, 2 of them at the host root;
- 30 exact aliases;
- 1 history alias: the vendored `K224_Construction_2026-10-20.zip` is Source 125's archive
  (blob `a4b02ffe` of `49ee7cfdc8`);
- 3 archive-only (the main manuscript, its PDF and the delivery README).

## Source 127 — `K223_Construction_2026-10-20.zip` (prefix `127-k223-`)

Arrival `281af27565`. It delivers a **223-state machine** (canonical SHA-256 `7edafbb2…`), now the
[smallest known candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k223/README.md).
The saving has three parts:

1. **Conditional K.** The source emits the conditional K core `m → ∃c (c ∋ b ∧ H)` in place of
   K's `∃c ((m → c ∋ b) ∧ H)`. H, the eight logical rows, the gate, the commands and the
   stack-slot count are unchanged, and the 224's restricted equality helper is kept. The
   source (SHA-256 `b4e453a8…`) still has 4,799 leaves and 210 distinct subtrees, but 1,162 of
   its leaves differ from the 224's.
2. **Helper allocation.** Four new source roles go to existing helper states 37, 26, 162 and 11.
   All 24 priority orders were checked; a greedy allocation loses one sharing.
3. **A fold.** Native state 18 merges into 180 through a previously written left-neighbour tag
   and an existing helper. Every old transition matches one or three new ones.

**The calculus is new again.** The calibration uses the 224 package's side result
`conditional_k_calibration.md`, unused by the 224 itself:

- Ku + IR is interpreted in Kc + IR by two markers and a hereditary domain (Ku is
  unconditional K, Kc conditional K);
- the upper direction holds because the private name is not free in the decoded matrix;
- the restricted equality-helper interpretation is composed with it.

The package's `conditional_calibration.md` binds the exact source to this calculus and gives a
1,611-node fusion certificate. The intake has not replayed these logical certificates.

**Intake replays**, with the same adapted Source 103 checkers as for the 224, on the
candidate page's inherited-label table:

| Check | Result |
| --- | --- |
| Decoder accounting | 49 engine + 187 nodes − **13** shared = 223, 4,799 leaves |
| Finite screen | 0 of 6,238 failed |
| Exact blank startup | the dispatch frame after 409,835 steps, sparse and dense |
| Unbounded runtime | `UNIVERSAL_MATHEMATICAL_PASS`, 6,238 cases, 1,515,697 rules, all 446 rows (the package's figures) |

The distinct-node count equals the 224's (187); the saving is one more tag-shared role (13
against 12). The intake has not decomposed it between the helper allocation and the fold.

## Formal status

The Rocq work for the 224 ([rocq224](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/rocq224/README.md)) carries over in large part:

- the soundness of the fused bundle;
- the equality interpretation `lprov_th`;
- the program-layer pipeline (`dag224`-style AX word, offset certificate);
- the TM side.

Two pieces are new for the 223:

- **Soundness through decoding.** The conditional core follows from K's only because the
  private name is not free in the decoded matrix. So this direction must go through Elliot's
  decoder (`Sound230`, `D_private_fresh`), not through the code-level embedding that suffices
  for the 224.
- **The conditional-K interpretation.** The two-marker hereditary-domain interpretation of
  Ku + IR in Kc + IR (singletons, pairs, markers, the domain, relativized K instances). It is
  the largest new formal obligation.

## Non-claims

No proof-assistant theorem for the 223. No PA endpoint. No minimality.

## Attribution

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The conditional-K calibration, the equality helper and the 224-state parent come from
Source 125; the helper allocation and the final fold are Source 127's own.
