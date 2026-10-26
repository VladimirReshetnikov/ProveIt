# Independent review of NativePreliminaryCount2011

**Verdict: PASS for the stated arithmetic theorem.** Reviewer: circuit_reduction; author: root. I read the entire 89-line module and 28-line checks file, the complete imported PaddingStaircase source, and the relevant complete section 7 of the frozen ordinary 2011 proof. No issue or requested source change was found. No reviewed file was edited.

## Exact source binding

Paths are relative to Computability/DiophantineConsistency.

| File | SHA-256 |
| --- | --- |
| Lean/DiophantineConsistency/NativePreliminaryCount2011.lean | ee138db4fc12507fa9dbd11c49aa6677c159bd1795588b5d0070c142e0080d2c |
| Lean/DiophantineConsistency/NativePreliminaryCount2011Checks.lean | 027e4d3636f4834cf8d89dbc7fe49e9b1961bb79f39ae5651926f732f9779f04 |
| Lean/DiophantineConsistency/PaddingStaircase.lean | b75d9c9cf430b4e3f8b020246c75eefd9c367f740cc6b1a99bc5de4859fb4932 |
| research/padding-staircase-independent/PROOF.md | 69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8 |

The hashes remained unchanged after both fresh Lean runs.

## Proof and premise audit

`clause_low_mask` applies reduction modulo 2^11 to the actual complete mask equality. The mask (2^45 - 4) reduces to 2044, so the resulting test is precisely bits 2 through 10, not an assumed numerical upper bound. `count_of_small_low` uses an explicit low < 2048 premise to avoid any modular-wrap inference, then the imported proved `low_mask_iff` leaves only values 0 through 3. Its 2*n <= low premise consequently gives n <= 1.

The three branches agree with ordinary section 7:

- For phases 0 through 6, Boolean selectors first give n <= 942. With k <= 57, b <= 1, epsilon <= 1, the temporal summand is at most 64. Thus 2*n + k + b + temporal <= 2006 < 2048 before any count or label recovery.
- For phases at least 11, 2^phase*epsilon is divisible by 2048. The remaining low sum is at most 2*942 + 57 + 1 = 1942. This branch does not require an upper bound on phase or epsilon; the divisibility proof is valid for all natural values under its stated lower bound on phase.
- For phases 7 through 10, the theorem requests precisely 483 padding tests and their modulo-16 residue bindings. The imported staircase proof starts from prefix 0, increases by a Boolean bit, and rules out the first hit at 4 because 2*4+u is 8, 9, or 10 for u <= 2. Hence the first 483 selectors total at most 3 and the remaining 459 total at most 459, giving n <= 462. Only then is temporal <= 1024 used, making the low sum at most 2006 and permitting the clause test to force n <= 1.

The `hpadding` premise is a function required only under 7 <= phase <= 10. No padding premise is used in either other branch. The `bit`, `u`, and `digit` functions may be arbitrary naturals subject to the explicit hypotheses. `hbit` covers every selector index 0 through 941. All quantities are nonnegative by type. No zero incoming carry, label equality, occupation, fractional alignment, or desired n <= 1 conclusion is silently assumed. The already proved generic prefix bound supplies the initial n <= 942, and the total theorem is stronger than the physical phase range because it covers every natural phase.

The checks include both 2006 endpoints, divisibility at actual phases 11 and 46, and a counterexample to omitting the middle-phase information. Its raw full clause is

```text
2*512 + 2^10 + 2048*(2^34-1) = 2^45,
```

which passes the entire mask 2^45 - 4 while the raw selector count is 512. This is correctly described as a raw arithmetic example, not a realizable native source solution or a counterexample to the constructed equation.

## Fresh bounded Lean replay

Both new files were independently compiled with `lake env lean -M6000 -j1`. The module object was written under `/tmp/native-count2011-circuit-peer/DiophantineConsistency`; the Checks run used that freshly compiled object through a temporary LEAN_PATH overlay. Existing prerequisite entries were symlinked into the temporary namespace. No shared compiled object or source was overwritten; no Lake scheduler was invoked. Existing PaddingStaircase/mathlib prerequisites were reused, and their fresh replay is not claimed here.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePreliminaryCount2011.lean -o /tmp/native-count2011-circuit-peer/DiophantineConsistency/NativePreliminaryCount2011.olean
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c 'export LEAN_PATH=/tmp/native-count2011-circuit-peer:"$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePreliminaryCount2011Checks.lean -o /tmp/native-count2011-circuit-peer/DiophantineConsistency/NativePreliminaryCount2011Checks.olean'
```

Module: PASS, exit 0, 3.58 seconds, peak 1637840 KB. Checks: PASS, exit 0, 2.12 seconds, peak 1632668 KB. Logs are `/tmp/native-count2011-circuit-peer-module.log` and `/tmp/native-count2011-circuit-peer-checks.log`.

The module emitted no diagnostics. All four checked axiom reports were standard only: clause_low_mask uses propext and Quot.sound; count_small_phase, count_large_phase, and total_le_one_all_phases use propext, Classical.choice, and Quot.sound. No sorryAx, native_decide axiom, or added source axiom occurs.

## Independent arithmetic challenge

A separate standard-library-only program below exhaustively checked 5,003,318 reduced cases across all 47 physical phases. It uses the appropriate independently justified count cap (462 for phases 7..10, 942 otherwise), every value of k+b from 0 to 58, and both epsilon values. Combining k+b does not omit an attainable sum: all 59 values occur with k <= 57 and b <= 1. Every accepted low mask had n <= 1. Separately, all 24 local staircase transitions were checked, as was the exact full-mask raw counterexample above. The program also finds the first low-mask counterexample in each middle phase when the padding bound is removed.

Normal and optimized Python runs passed and their JSON outputs were byte-identical. This finite challenge supplements the Lean proof; it does not establish any missing physical digit binding.

```sh
python /tmp/native-count2011-circuit-peer-numeric.py > /tmp/native-count2011-circuit-peer-numeric.json
python -O /tmp/native-count2011-circuit-peer-numeric.py > /tmp/native-count2011-circuit-peer-numeric-optimized.json
cmp /tmp/native-count2011-circuit-peer-numeric.json /tmp/native-count2011-circuit-peer-numeric-optimized.json
```

Program SHA-256: `1ff6c41145b2f0e4b72ed9b6de022fb1114527b22dc73b374dde13f431f91f05`.
Output SHA-256: `fec742adb0c3173de91b673989210e0d90576ba008fb0249ece007c33f2483ea`.

```json
{
  "accepted_cases": 504,
  "first_unpadded_middle_counterexamples": {
    "10": [
      483,
      57,
      1,
      1
    ],
    "7": [
      931,
      57,
      1,
      1
    ],
    "8": [
      867,
      57,
      1,
      1
    ],
    "9": [
      739,
      57,
      1,
      1
    ]
  },
  "full_mask_counterexample": 35184372088832,
  "local_staircase_cases": 24,
  "phase_count": 47,
  "reduced_cases_checked": 5003318,
  "result": "PASS"
}
```

## Scope limit

This is the complete arithmetic inference from the displayed explicit premises to an at-most-one selector count. It is not yet an unconditional theorem from an actual current polynomial zero. The literal native proof must still bind the actual 942 Boolean selector digits, incoming carry at most 57, Boolean extra and temporal source, the full clause residue/mask, and (only for phases 7..10) the 483 actual padding digit residue/mask identities with unit bound 2. This module neither assumes nor establishes tableau/halting or Con(ZFC) calibration. The theorem and file documentation accurately preserve that boundary.

## Reproducible challenge program

```python
import json

def require(p, label):
    if not p:
        raise ValueError(label)

checked = 0
accepted = 0
for phase in range(47):
    cap = 462 if 7 <= phase <= 10 else 942
    for n in range(cap + 1):
        for carry_plus_boolean in range(59):
            for epsilon in range(2):
                low = 2*n + carry_plus_boolean + (2**phase)*epsilon
                passes = ((low % 2048) & 2044) == 0
                require(not passes or n <= 1, 'all-phase preliminary count')
                checked += 1
                accepted += passes
middle_counterexamples = {}
for phase in range(7, 11):
    cases = ((n, k, b, epsilon) for n in range(2, 943)
             for k in range(58) for b in range(2) for epsilon in range(2))
    bad = next((c for c in cases if
                ((2*c[0]+c[1]+c[2]+2**phase*c[3]) % 2048) & 2044 == 0), None)
    require(bad is not None, 'middle-phase padding is necessary for this method')
    middle_counterexamples[str(phase)] = bad
for prefix in range(4):
    for bit in range(2):
        for unit in range(3):
            next_prefix = prefix + bit
            require(((2*next_prefix+unit) & 8) != 0 or next_prefix <= 3,
                    'no first hit at four')
full_clause = 2*512 + 2**10 + 2048*(2**34-1)
require(full_clause == 2**45 and full_clause & (2**45-4) == 0,
        'full-mask raw phase10 counterexample')
require(3 + (942-483) == 462, 'prefix-to-total bound')
print(json.dumps({'result':'PASS', 'phase_count':47,
                  'reduced_cases_checked':checked, 'accepted_cases':accepted,
                  'first_unpadded_middle_counterexamples':middle_counterexamples,
                  'full_mask_counterexample':full_clause,
                  'local_staircase_cases':24}, sort_keys=True, indent=2))
```
