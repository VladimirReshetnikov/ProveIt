# Independent review of the exact WangTiles942 Lean packet

**Verdict: PASS within the scope below.** Reviewer: circuit_reduction; packet author: complemented47_review. I read all four frozen files completely (527 + 230 + 188 + 56 = 1001 lines), the complete maintained equation.tex, and the decoder definitions used by the new packet. I found no mathematical, coordinate, numeral-binding, or target-renaming discrepancy. I made no edits to any reviewed source.

## Frozen source binding

Paths are relative to Computability/DiophantineConsistency.

| File | SHA-256 |
| --- | --- |
| Lean/DiophantineConsistency/WangTiles942Data.lean | ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125 |
| Lean/DiophantineConsistency/WangTiles942Core.lean | 7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85 |
| Lean/DiophantineConsistency/WangTiles942.lean | 77be337f20089de1b8a5b795d0a61628e4334673d26f8100fc1500009ac28ea6 |
| Lean/DiophantineConsistency/WangTiles942Checks.lean | 6835a5280546f89b7e211378f9f8209c190b66a3c5680fc8e473b37585fd9aa3 |
| Lean/DiophantineConsistency/DecimalMachine215.lean | da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a |
| equation.tex | a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e |

The existing DecimalMachine215 module supplies the previously checked state conjugacy. This review independently rechecks its printed numeral and all 430 actions against the new caches; it does not claim a fresh replay of the full BusyBeaver dependency closure.

## Mathematical and source review

1. **Data cache is certified, not assumed.** The 430 literal cache entries are proved equal to DecimalMachine215.action in disjoint kernel-checked batches covering every Fin 430. The complete cached action list is transported to the actual decoded list. Bool tuple order is write, moveRight, next. Discovery-order state 1 is the actual first target; the checks retain its dense-state image 93 instead of substituting 93 into the discovery-order table.
2. **Target sets and rails are exact.** The direction filters use the movement component, include halting target 215, and eliminate duplicates before cardinality. The finite target lists have 45 and 199 elements. The rail formula intersects with Finset.range q, so q = 0 gives an empty interval. The finite rail cache is checked at all 216 inputs in both directions; rail_eq_formula and rail_eq_decoded cover every natural q by an explicit formula fallback outside the cache. This avoids the erroneous natural-subtraction interpretation of the printed interval ending at -1.
3. **Every printed tile row is present exactly once.** The row constructors agree with all nine printed table families. orderedRows only swaps the two copy blocks and two signal blocks. Its index list is exactly range 942, and the structural permutation transfers count and unique indices to printed-order indexedRows. The tile accessor uses that complete ordered list. Colors have the actual order west, north, east, south. The stronger vertical bound 438 and horizontal bound 255 are proved for all rows; no East/West convenience convention is substituted.
4. **The printed floor formula has no hidden truncated subtraction.** selectorWeight is precisely the unscaled printed chi, including its leading 1 and inner 1. The proven bound chi < 2^44 implies the natural rank numerator never truncates. nonStart_rows proves that the dropped list is exactly abstract indices 1 through 941. physicalPosition_eq_printed is consequently a full formula identity, including pi(0) = 0.
5. **Initializer 928 is numerically and semantically bound.** Its tuple is (3,436,4,4). The first decoded action is (1,1,1), hence its south color 4 is h(1,0). The structural rank argument counts greater-weight tiles by complete constructor families: 0 transitions, 2 copies, 395 right signals, 90 left signals, 16 tail tiles; their total 503 gives position 504. The special right-signal q = 0 and q = 1 branches are handled explicitly, rather than applying an invalid uniform bound.
6. **No desired calibration conclusion appears as a premise.** The results use the literal decoder, finite row definitions, and generic arithmetic/list facts. The files do not assume a tableau, a valid computation, consistency, or a theorem equating this table with a native equation.

## Fresh Lean replay

All four files were checked sequentially with the existing configured Lean v4.32.0 and `-M6000 -j1`; their own `Elab.async false` option is retained. Objects were written only under `/tmp/wang942-circuit-peer/DiophantineConsistency`. For downstream files, the temporary directory was prepended to LEAN_PATH. Existing non-Wang DiophantineConsistency prerequisite entries were symlinked into this temporary namespace because Lean selects a namespace root as a unit; no shared object was overwritten. Thus Core used the freshly checked Data object, main used freshly checked Core, and Checks used the newly checked main. Prerequisites were reused, not claimed freshly rebuilt.

The first attempted Core invocation failed immediately because the temporary namespace lacked DecimalMachine215.olean. I added symlinks to the already existing prerequisites and repeated it successfully. This was a temporary import-path setup failure, not a source or theorem failure. No Lake scheduler was run.

Commands, with SOURCE and NAME substituted in dependency order:

```sh
# Data: ordinary configured prerequisite path.
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1   Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Data.lean   -o /tmp/wang942-circuit-peer/DiophantineConsistency/WangTiles942Data.olean

# Core, main, Checks: temporary freshly built predecessors first.
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c   'export LEAN_PATH=/tmp/wang942-circuit-peer:"$LEAN_PATH"; exec lean -M6000 -j1 SOURCE -o /tmp/wang942-circuit-peer/DiophantineConsistency/NAME.olean'
```

| File | Result | Seconds | Peak resident KB |
| --- | --- | ---: | ---: |
| Data | PASS, exit 0 | 88.58 | 5942432 |
| Core | PASS, exit 0 | 13.96 | 3706896 |
| Main | PASS, exit 0 | 4.38 | 3217248 |
| Checks | PASS, exit 0 | 9.75 | 3693412 |

Logs: `/tmp/wang942-circuit-peer-{data,core,main,checks}.log`. Data/Core/main produced no diagnostics. Checks printed all 15 requested axiom audits. action_eq_decoder uses only propext and Quot.sound; each remaining reported theorem uses only propext, Classical.choice, and Quot.sound. These remaining endpoints are targets_eq_decoded, rail_eq_formula, rail_eq_decoded, transitionRow_eq_decoded, row_indices_exact, row_indices_nodup, row_count, ordered_rows_perm, tile_bounded, start_zero, initializer_928, first_transition, physicalPosition_eq_printed, and physical_initializer. No sorryAx, native_decide axiom, or new source axiom occurs.

## Independent actual-source numeric challenge

The standard-library-only program reproduced below reads the actual maintained TeX digit rows and inert Lean cache text. It imports no repository code. Prefix division and successive divmod independently agree at all 430 mixed-radix digits and all 431 prefix endpoints. It checks every action, both target lists, all 432 cached rails, the complete printed 942-row table, all 885481 non-Start rank comparisons, and the initializer family count. It also numerically verifies distinct tiles, distinct weights, and the complete physical-position permutation; those additional numerical checks do not substitute for a formal permutation theorem.

Both commands passed, and their output files were byte-identical:

```sh
python /tmp/wang942-circuit-peer-numeric.py > /tmp/wang942-circuit-peer-numeric.json
python -O /tmp/wang942-circuit-peer-numeric.py > /tmp/wang942-circuit-peer-numeric-optimized.json
cmp /tmp/wang942-circuit-peer-numeric.json /tmp/wang942-circuit-peer-numeric-optimized.json
```

Program SHA-256: `d5d35cfd13210bd8ea975853d5d5e2107dc7b56b3443e31ebb6511df4d5b9f63`.
Output SHA-256: `ffce955de18bb5209aea82373dc5eca4b25e6ea84740ad1dc980fc1a6a116cff`.

The counterchecks distinguish saturated subtraction at the actual halt action 125, omission of outer mod 216, an incorrectly nonempty interval at q = 0, deletion of the two halt-signal rows, unconverted dense-state first target 93, swapped west/east packing, and actual first/last decimal-digit mutations. They are scoped arithmetic/source-binding checks, not a general-purpose TeX mutation validator.

The script implements the printed fixed formulas after a full manual source review; it does not parse arbitrary TeX mathematics. Its extracted numeral and parsed literal action/target/rail caches are actual source data. Numerical output is auxiliary evidence; the fresh Lean proofs remain the theorem check.

```json
{
  "actions": 430,
  "canonical_json_sha256": {
    "actions": "4c81320292708dae99501de44503470418fc7ae8703e4b95d01117be2961016c",
    "positions": "1b59692fdc532fffd605d9569a47f8173adc5308a2ba993074eaef437b30c517",
    "rails": "a1d043d948b365c767befe41ae07f72d08190f1491be9960041d3db8c4fd1684",
    "targets": "31548ed7d939ebc7c5f9c7225209abddfd33c18f0244e0375d4ba7fbbfc35c82",
    "tiles": "3fda0b730eb2698fe3bb399100843fcf9223631607b49f138793e0b157371067",
    "weights": "0e41a3dabf834eb9685a4f3c84398c65831cfd7f14759c93ed01f38c1da1dfb4"
  },
  "color_sums": [
    59966,
    102059,
    54887,
    110738
  ],
  "decimal_ascii_sha256": "7509e3059b175745251852154cab77a8e697241397965a2eeb37c0a1a5faad35",
  "decimal_digits": 715,
  "discoveries": 214,
  "doubled_weight_sum": 7624644664715100,
  "flag_nibbles": 71,
  "halt_action": 125,
  "initializer_position": 504,
  "initializer_rank_group_sums": [
    0,
    2,
    395,
    90,
    16
  ],
  "negative_controls": {
    "dense93_used_without_conjugacy": true,
    "first_decimal_digit_mutation": true,
    "last_decimal_digit_mutation": true,
    "nat_subtraction_at_halt": true,
    "omitted_halt_signal_rows": true,
    "omitted_outer_mod_at_halt": true,
    "west_east_swap_changes_weight": true,
    "wrong_nonempty_zero_interval": true
  },
  "prefix_endpoints": 431,
  "rail_values_checked": 432,
  "rank_comparisons": 885481,
  "raw_halt_target": -1,
  "result": "PASS",
  "source_sha256": {
    "Lean/DiophantineConsistency/DecimalMachine215.lean": "da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a",
    "Lean/DiophantineConsistency/WangTiles942.lean": "77be337f20089de1b8a5b795d0a61628e4334673d26f8100fc1500009ac28ea6",
    "Lean/DiophantineConsistency/WangTiles942Checks.lean": "6835a5280546f89b7e211378f9f8209c190b66a3c5680fc8e473b37585fd9aa3",
    "Lean/DiophantineConsistency/WangTiles942Core.lean": "7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85",
    "Lean/DiophantineConsistency/WangTiles942Data.lean": "ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125",
    "equation.tex": "a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e"
  },
  "target_counts": [
    45,
    199
  ],
  "tile_rows": 942,
  "weight_sum": 3812322332357550
}
```

## Limits of this receipt

This four-file packet establishes exact machine-action-to-tile data, all indexed rows and color bounds, the literal physical rank expression, and the actual initializer's physical position. It does **not** by itself prove that physicalPosition is a bijection for all 942 selectors; the separate WangTiles942Permutation module is outside this review. It also does not establish the complete Phi/kernel coefficient map, native carry/phase/onehot decoding, a tableau/computation equivalence, or the final equation/Con(ZFC) equivalence. The already checked decimal machine conjugacy and ZFC endpoint are separate dependencies/results, not additional claims of this replay.

## Reproducible independent program

The following fenced body is exactly the 192-line temporary program identified above; its workspace root is explicit. Extract it to the shown temporary path to reproduce the normal and optimized checks.

```python
#!/usr/bin/env python3
"""Independent stdlib-only review of the actual printed decoder and Wang caches.

This is a fixed-recipe reconstruction, not a general TeX/Lean parser. It imports
no repository program. All input files are read as inert text.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
BASE = ROOT / 'Computability/DiophantineConsistency'
LEAN = BASE / 'Lean/DiophantineConsistency'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def digest(value):
    return sha(json.dumps(value, separators=(',', ':'), sort_keys=True).encode())


def decode(number):
    mask = number % 2**636
    payload = number // 2**636
    discoveries = [(mask >> j) & 1 for j in range(430)]
    sigma, prefix, radices = [0], [1], []
    for bit in discoveries:
        radix = (sigma[-1] + 2)**(1 - bit)
        radices.append(radix)
        prefix.append(prefix[-1] * radix)
        sigma.append(sigma[-1] + bit)
    digits = [(payload // prefix[j]) % radices[j] for j in range(430)]
    remaining, successive = payload, []
    for radix in radices:
        remaining, digit = divmod(remaining, radix)
        successive.append(digit)
    require(successive == digits, 'prefix versus successive division')
    require(remaining == payload // prefix[-1], 'complete prefix endpoint')
    marks = [(mask >> (430 + q)) & 1 for q in range(215)]
    tally, flags = 0, []
    for mark in marks:
        flags.append(14 + mark * (((remaining >> (4 * tally)) & 15) - 14))
        tally += mark
    raw = [sigma[j + 1] - digits[j] for j in range(430)]
    actions = [[(flags[j//2] >> (2*(j%2))) & 1,
                (flags[j//2] >> (2*(j%2)+1)) & 1,
                raw[j] % 216] for j in range(430)]
    return actions, raw, sigma, prefix, tally


tex = (BASE / 'equation.tex').read_text()
data = (LEAN / 'WangTiles942Data.lean').read_text()
decimal = (LEAN / 'DecimalMachine215.lean').read_text()
printed = ''.join(re.findall(r'^([0-9]+)\\par$', tex, re.M))
require(len(printed) == 715, 'complete 715-digit page numeral')
seed = int(printed)
lean_seed = int(re.search(r'def seed : ℕ := ([0-9]+)', decimal).group(1))
require(seed == lean_seed, 'actual printed numeral equals Lean numeral')
actions, raw, sigma, prefix, flag_count = decode(seed)
cache_text = data.split('def actionCache', 1)[1].split('def actionNat', 1)[0]
cached = [[int(w == 'true'), int(d == 'true'), int(q)]
          for w, d, q in re.findall(
              r'\((true|false),\s*(true|false),\s*([0-9]+)\)', cache_text)]
require(len(cached) == 430 and cached == actions, 'every cached action')
require(actions[0] == [1, 1, 1], 'actual first target is discovery state one')
require([j for j, r in enumerate(raw) if r < 0] == [125], 'unique signed halt')
require(raw[125] == -1 and actions[125][2] == 215, 'signed halt target')
require(sigma[-1] == 214 and len(prefix) == 431, 'all prefix endpoints')

targets = [sorted({a[2] for a in actions if a[1] == d}) for d in (0, 1)]
target_text = data.split('def targetList', 1)[1].split('def targets (', 1)[0]
target_arrays = re.findall(r'\[([0-9,\s]+)\]', target_text)
require(len(target_arrays) == 2, 'two literal target arrays')
target_cache = [ast.literal_eval('[' + s + ']') for s in target_arrays]
require(target_cache == [targets[1], targets[0]], 'entire target lists')
require([len(t) for t in targets] == [45, 199], 'distinct target counts')


def rail(d, q):
    return 205 - 199*d + sum(t < q for t in targets[d])


rails = [[rail(d, q) for q in range(216)] for d in (0, 1)]
rail_text = data.split('def railCache', 1)[1].split('theorem targetList_nodup', 1)[0]
rail_arrays = re.findall(r'#\[([0-9,\s]+)\]', rail_text)
require(len(rail_arrays) == 2, 'two literal rail arrays')
rail_cache = [ast.literal_eval('[' + s + ']') for s in rail_arrays]
require(rail_cache == [rails[1], rails[0]], 'all 432 rail-cache values')
require([rail(0, 0), rail(1, 0), rail(1, 1)] == [205, 6, 7], 'zero/one rails')
require([rail(0, 216), rail(1, 216)] == [250, 205], 'post-cache rails')

rows = [(0, (2, 435, 3, 1))]
transitions, copies, signals, tail = [], [], [[], []], []
for j, (write, direction, target) in enumerate(actions):
    q, b = divmod(j, 2)
    transitions.append((j+1, ((1-direction)*rail(0, target), 2*q+b+2,
                              direction*rail(1, target), write)))
for a in (0, 1):
    for b in (0, 1):
        copies.append((433-2*a+b, (0, 432*a+b, 0, 432*a+b)))
for d in (0, 1):
    for q in targets[d]:
        for b in (0, 1):
            r = rail(d, q)
            signals[d].append((423+2*r+b, (d*r, b, (1-d)*r, 2*q+b+2)))
for a in (0, 1):
    for b in (0, 1):
        tail.append((923+2*a+b, (0, 432*a+b, 0, 438)))
tail += [(927, (2, 434, 2, 0)), (928, (3, 436, 4, 4)), (929, (4, 436, 4, 0))]
tail += [(496+t, (1, 438, 1, t)) for t in (434, 435, 436)]
tail += [(933+3*a+b, (a*a, 437, b, 437)) for a in range(3) for b in range(3)]
rows += transitions + copies + signals[0] + signals[1] + tail
require(len(rows) == 942, 'complete table row count')
require(sorted(i for i, _ in rows) == list(range(942)), 'exact index partition')
tiles = [tile for _, tile in sorted(rows)]
require(len(set(tiles)) == 942, 'all tiles distinct, independent numerical check')
require(all(0 <= w < 256 and 0 <= e < 256 and 0 <= n <= 438 and 0 <= s <= 438
            for w, n, e, s in tiles), 'all four color bounds')
require(tiles[1] == (0, 2, 7, 1), 'first transition tile')
require(tiles[928] == (3, 436, 4, 4), 'initializer tile')
require(tiles[928][3] == 2*actions[0][2]+2, 'actual first-target initializer')


def weight(tile):
    w, n, e, s = tile
    return 1 + 2**10 * (1 + w + 2**8*n + 2**17*e + 2**25*s)


weights = [weight(t) for t in tiles]
require(all(0 <= c < 2**44 for c in weights), 'untruncated weight bounds')
require(len(set(weights)) == 942, 'distinct packed weights')
positions = [0]
pair_count = 0
for i in range(1, 942):
    total = 0
    for j in range(1, 942):
        numerator = 2**44 - 1 + weights[j] - weights[i]
        require(numerator >= 0, 'natural rank subtraction is exact')
        result = numerator // 2**44
        require(result == int(weights[j] > weights[i]), 'strict floor comparison')
        pair_count += 1
        total += result
    positions.append(1+total)
require(pair_count == 885481, 'all non-Start pair comparisons')
require(sorted(positions) == list(range(942)), 'numerical physical permutation')
require(positions[928] == 504, 'initializer physical rank')
require(weights[0] == 34876427265, 'printed Start packed weight')

score = lambda tile: int(weight(tile) > weights[928])
group_scores = [sum(score(t) for _, t in family)
                for family in (transitions, copies, signals[1], signals[0], tail)]
require(group_scores == [0, 2, 395, 90, 16], 'independent initializer rank groups')

controls = {}
controls['nat_subtraction_at_halt'] = max(raw[125], 0) % 216 != actions[125][2]
controls['omitted_outer_mod_at_halt'] = raw[125] != actions[125][2]
controls['wrong_nonempty_zero_interval'] = 6+int(0 in targets[1]) != rail(1, 0)
controls['omitted_halt_signal_rows'] = len(rows)-2 != 942
controls['dense93_used_without_conjugacy'] = 2*93+2 != tiles[928][3]
controls['west_east_swap_changes_weight'] = weight((3, 435, 2, 1)) != weights[0]
controls['first_decimal_digit_mutation'] = decode(seed+10**714)[0] != actions
controls['last_decimal_digit_mutation'] = decode(seed+1)[0] != actions
require(all(controls.values()), 'all concrete negative controls distinguish the binding')

files = ['equation.tex', 'Lean/DiophantineConsistency/DecimalMachine215.lean']
files += ['Lean/DiophantineConsistency/'+name+'.lean' for name in
          ('WangTiles942Data', 'WangTiles942Core', 'WangTiles942', 'WangTiles942Checks')]
report = {
    'result': 'PASS', 'source_sha256': {f: sha((BASE/f).read_bytes()) for f in files},
    'decimal_digits': len(printed), 'decimal_ascii_sha256': sha(printed.encode()),
    'actions': len(actions), 'prefix_endpoints': len(prefix), 'discoveries': sigma[-1],
    'flag_nibbles': flag_count, 'halt_action': 125, 'raw_halt_target': raw[125],
    'target_counts': [len(t) for t in targets], 'rail_values_checked': 432,
    'tile_rows': len(rows), 'color_sums': [sum(t[k] for t in tiles) for k in range(4)],
    'weight_sum': sum(weights), 'doubled_weight_sum': 2*sum(weights),
    'rank_comparisons': pair_count, 'initializer_position': positions[928],
    'initializer_rank_group_sums': group_scores,
    'canonical_json_sha256': {name: digest(obj) for name, obj in
                              [('actions', actions), ('targets', targets), ('rails', rails),
                               ('tiles', tiles), ('weights', weights), ('positions', positions)]},
    'negative_controls': controls,
}
print(json.dumps(report, indent=2, sort_keys=True))
```
