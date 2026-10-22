# Shared implication basis: pinned proposal, current-client recheck

This component packages the previously proposed six-goal implication core
and its unrestricted adapter from ProveIt commit
`49e99c5b7cc6c2e164331961de28bad3904361fd`.
It is a revalidation and integration proposal, not a claim of a new derivation.
The production comparison is against
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

## Recommended change

Apply `shared-basis.patch` at the root of a checkout of the production
revision. It changes only `DominatedImplication.lean` and `Lukasiewicz.lean`.
Apply the companion `producer-wiring.patch` as well: it updates the
renderer, neutral core derivation, and regeneration instructions. Otherwise
the baseline generator would recreate the old core. The documentation patch
also removes the destructive use of the old `--luk` command on the new adapter.
The shared core exports the unrestricted row, composition, right-prefix
lifting, K, Peirce, and S. The unrestricted syntactic calculus is its
instance with `below := fun _ _ => True`.

| File | Original lines / bytes | Proposed lines / bytes |
| --- | ---: | ---: |
| DominatedImplication | 287 / 13,723 | 300 / 14,146 |
| Lukasiewicz | 524 / 28,731 | 101 / 4,097 |
| Total | 811 / 42,454 | 401 / 18,243 |

This patch is independent of `../lean-bridge/minimal.patch`. Their combined
three-file saving is 433 physical lines and 25,015 UTF-8 bytes. Generator
and audit artifacts are excluded from that explicitly selected scope.

## Fresh component validation

`verification/receipt.json` records a successful 16-module build with
Lean 4.32.0, including the unchanged numerical adapters, `TarskiFalsity`,
`KThmK`, and a separate axiom-audit client. Every source, log, and compiled
object has a recorded SHA-256. The source files themselves are supplied
under `src/`; binary compiler objects are omitted.

All six core exports and all four unrestricted basis exports report no
axioms. The existing Tarski completeness client reports
`[propext, Classical.choice, Quot.sound]`. This is a component check;
the complete `KEndpoint215` endpoint was not rebuilt.

From this directory, reproduce with an absolute path to the pinned compiler:

```bash
python3 build.py --lean /absolute/path/to/lean-4.32.0-linux/bin/lean
```

The driver builds the listed modules in dependency order, writes objects
and a new receipt under `build/`, and does not use project object caches,
Lake, or network access. It needs Python 3 and a POSIX environment.
The retained `verification/` evidence is not overwritten by this command.

## Reproduce the generated core

The unchanged producer and neutral derivation are included. There are
58 inference steps plus input row 0: 59 numbered rows, not 59 inference
steps. Two unused final aliases are inlined, leaving 56 private derivation
lemmas, in addition to the two private domination-growth helpers.

```bash
python3 producer/generate_domrho8_cd.py \
  --derivation producer/derivation_core.txt \
  --core /tmp/K215-DominatedImplication.lean
cmp /tmp/K215-DominatedImplication.lean \
  src/BusyBeaver/ZFC/DominatedImplication.lean
```

The producer check in this packet found exact byte equality. The core's
SHA-256 is
`bd07364a829e8a1535b0ecf1ee6ed0c292d5af35e01a6db8f152dd2610e247d8`.
The small `Lukasiewicz` adapter is maintained source: the producer's older
`--luk` mode renders a separate derivation and is not its regeneration path.

The producer is outside the logical trust base. Lean checks every generated
proof application using its ordinary kernel.

`public-api-review.json` records a separate static comparison of 14 common
public declaration headers and three exact definition/tail blocks. It finds
no removed public declaration or changed existing header. The only added
public names are the core's `k`, `peirce`, and `s`. Its reproducer,
`compare_api.py`, is a scoped source scanner, not an elaborated Lean type checker.
