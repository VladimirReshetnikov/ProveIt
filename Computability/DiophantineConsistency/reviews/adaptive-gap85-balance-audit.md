# Independent review of the 85-operation balance shift

This read-only review checked the new balance-shift sources and the three
focused replay packets. It does not establish that the 85-operation equation
is equivalent to the 86-operation equation.

* `AdaptiveGap85BalanceModel.literal_preserved` proves equality of the
  signed interpretations of the exact `expressionAt85` before and after
  the shift in arbitrary IΣ₁ models, under the displayed non-strict C and r
  decrement bounds. `positive_zero_shift` adds strict bounds and positive
  input coordinates, yielding a positive zero with
  `F′ + C′ + b*b*t = F + C`. The separate
  `AdaptiveGap85BalanceProgress.gap_strictly_decreases` additionally assumes
  `b > 0`, `t > 0`, and the available C decrement. These hypotheses do not
  show that an arbitrary zero can be shifted, or that a normalized witness
  satisfying `F + C < 1 + b` exists.
* The integer theorem covers arbitrary integer ports and witnesses for the
  literal equality. Its positive-zero client assumes `p 0 ≥ 0`, `t ≥ 0`,
  positive coordinates and both displayed strict decrement bounds. Its sum
  identity permits zero decrement when `b = 0` or `t = 0`; strict decrease
  needs positivity of both. The packet wording was corrected after review.
* I independently read the three Lean checked-axiom logs and verified the
  SHA-256 of each frozen author/peer state, source snapshot and full log
  against its comparison receipt. Workspace sources for the four named
  balance modules matched their frozen source hashes. The direct
  `AdaptiveGap85ShiftContextEquiv.olean` used by the model replay matched
  both its guarded hash and the original provider's matching output row.
  The reported proof axiom lists contain only `propext`, `Classical.choice`
  and `Quot.sound` where present; these are Lean metatheoretic axioms, not
  extra axioms of an object theory.
* A separate inline Python integer calculation, seeded with `855197`, checked
  the independently transcribed literal and shift on 200 small signed
  configurations and 100 positive configurations constructed to satisfy the
  strict decrement bounds. It returned `PASS`. This finite test is a typo
  check, not an arbitrary-model proof; the inline test script was not saved.

The author and peer replays use the same selected historical provider per
packet. They guard the listed selected project `.olean*` paths and one direct
Foundation object, but do not record a complete direct-import resolution
trace or independently rebuild historical transitive project, package or
dynamic ancestry. The snapshot does not by itself produce an iPRA derivation
of the 85 equation's consistency equivalence. See the packet READMEs and
`comparison.json` files under `adaptive-gap85-balance-shift-replay/`,
`adaptive-gap85-balance-model-replay/` and
`adaptive-gap85-balance-progress-replay/` for the exact scopes and hashes.

To recheck the preserved states, sources and logs from the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib, json
base = Path('Computability/DiophantineConsistency/reviews')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for kind in ('shift', 'model', 'progress'):
    packet = base / f'adaptive-gap85-balance-{kind}-replay'
    receipt = json.loads((packet / 'comparison.json').read_text())
    for side in ('author', 'peer'):
        assert sha(packet / side / 'state.json') == receipt[f'{side}_state_sha256']
        for row in receipt['rows']:
            name = row['module']
            assert sha(packet / side / 'src' / f'{name}.lean') == row['source_sha256']
            assert sha(packet / side / 'logs' / f'{name}.log') == row['log_sha256']
    print(kind, 'PASS', len(receipt['rows']), 'rows')
PY
```
