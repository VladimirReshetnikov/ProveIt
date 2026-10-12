"""Assemble Proofs15FejerSelection.lean from Proofs15Restriction (reused
sections, renamed selection -> fejer) and the new Fejér sections."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
S = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')

src = (GS / 'Proofs15Restriction.lean').read_text(encoding='utf-8').split('\n')

# 1-based inclusive ranges
RANGES = [
    (22, 549),    # Bernoulli averaging, arrangements as hyperedges, the beta^15 count
    (571, 575),   # features and phases
    (588, 604),   # index card, feature and phase values
    (644, 656),   # exponential simp lemmas
    (688, 698),   # product of exponentials
    (746, 808),   # character sums and the phase average
    (878, 896),   # the parity pattern
    (1042, 1202), # the parity pattern annihilates every monomial
    (1482, 1593), # distinct vertices of non-degenerate arrangements
]

HEADER = '''import GowersSzemeredi.Proofs15Restriction
import GowersSzemeredi.Proofs15DegenerateRange

/-!
# Lemma 15.5 with a single Fejér selection (Notes L.16)

Lemma 15.5 restricts `B` at random so that almost every surviving
8-arrangement is respected. The printed proof (`Proofs15Restriction`) keeps a
point with the Riesz weight `(1 + cos θ)/2 = |1 + e(θ)|²/4` and iterates
`2^(M−1)` independent stages, `M = 2^(k+4)`, because one stage favours a
respected arrangement only by the factor `1 + 2^(1−M)`. Hence the exponent
`arrangementSelectionExponent k = 2^(2^(k+4)+k+3)`.

Here one stage uses the Fejér weight of order `m`,
`|∑_{a ≤ m} e(a θ)|² / (m + 1)²` (the Riesz weight is `m = 1`). Averaging
over the phase (`fejer_oneStage_average`) counts digit pairs `(a, b)` whose
values `a − b` annihilate every feature:
* a respected arrangement has at least `∑_{j<T} (m+1−j)^M` of them, from the
  multiples `j·ε` of the parity pattern (`fejerValidRelations_card_good`);
* a non-respected arrangement without a dependence in `[−m, m]` has only the
  `(m+1)^M` diagonal ones (`fejerValidRelations_subset_diagonal`), by the
  `m`-range Lemma 15.4 of `Proofs15DegenerateRange`.

With `m + 1 = M·⌈6/(αη)⌉` Bernoulli's inequality gives a gain of
`(T+1)/2 ≥ 3/(αη)` in one stage, at the density cost `(m+1)^(−M)`. The result
(`fejer_arrangement_restriction`) is Lemma 15.5 with exponent
`fejerSelectionExponent k = 2^(k+4)·(k+6)`, and it implies the printed one
(`lemma_15_5_of_fejer_restriction`).

The finite Bernoulli averaging, the hyperedge bookkeeping, the parity moment
and the vertex injectivity are copied from `Proofs15Restriction` (private
there). -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi
'''

parts = [HEADER]
for a, b in RANGES:
    block = '\n'.join(src[a - 1:b])
    block = block.replace('selection', 'fejer').replace('Selection', 'Fejer')
    parts.append(block + '\n')
parts.append((S / 'fejer_new.lean').read_text(encoding='utf-8'))
out = '\n'.join(parts)
assert 'arrangementfejer' not in out
(GS / 'Proofs15FejerSelection.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()), 'lines')
