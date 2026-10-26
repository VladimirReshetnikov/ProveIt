# Independent review of CurrentClause2011

**Verdict: PASS for the literal clause identities and stated normalization premises.** Reviewer: circuit_reduction; author: root. I read the complete 184-line module and 33-line checks, compared their formulas to the frozen current kernel, masks, actual permutation and ordinary2011 clause geometry, and independently replayed both new files. No finding or source edit was needed.

## Frozen source binding

Paths below are relative to Computability/DiophantineConsistency.

| File | SHA-256 |
| --- | --- |
| Lean/DiophantineConsistency/CurrentClause2011.lean | a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566 |
| Lean/DiophantineConsistency/CurrentClause2011Checks.lean | 3b24f04353d5fa4bf49b056d85d1dcb572744e45293d26d0f49cde48a1a9521e |

Both hashes remained unchanged after the fresh runs. The imported exact kernel and permutation are the same definitions used in the separate reflected-geometry packet; this review changes neither dependency.

## Mathematical review

- Addition and subtraction residues are proved by equality in ZMod(N*2011), then reduced modulo the divisor2011. No absolute source index is confused with a cell residue. In particular the spatial input to clause1005 has residue996; in a two-cell word at base0 its absolute index is3007, as the focused check explicitly verifies.
- The clause target has residue1005 and cannot be global origin0. Therefore the exact repeated high-mask digit is2^45-4; the exceptional origin subtraction does not alter this target in any cell.
- `clause_convolution` expands the actual979-term folded kernel. The bare18 input has residue987, and bare2020 has residue996; both are excluded by the full lowSupport recipe. The bare1004 input is exactly selector1. Every reflected entry is retained, including a coefficient collision with the marker term, and its index becomes b+position(e) by exact cast subtraction using position(e)<=985<1005. The resulting sum contains all976 reflected entries. There is no Booleanity, occupation, count, phase, or label premise in this identity.
- `selectorCount_eq_prefix` uses the proved actual `physicalEquiv`, followed by the finite-sum/range identity, to count precisely physical fields0..941. It does not assume that an arbitrary sorting map is a permutation.
- `reflected_weight_mod` has residue2 for every doubled selector coefficient and0 for every doubled control coefficient modulo2048. Its selector branch uses the actual chi formula; each of the34 control entries is checked. Multiplying by arbitrary natural source digits and summing preserves that congruence, giving exactly2*selectorCount+c(b+1).
- `normalized_clause_residue` retains the actual incoming carry at b+1004, the bare selector1, and the temporal digit at b+1005. It only uses the stated full local normalization identity and the fact that radix2^47 is divisible by2048. No carry bound, zero incoming carry, label recovery, Boolean temporal digit, or alignment is needed for this congruence. The carry-bound wording in its documentation refers to the intended later application; the theorem itself correctly proves the stronger unrestricted congruence.
- `normalized_clause_mask` specializes the actual pointwise high-mask condition using the proved full clause-mask identity. It does not replace that mask with a convenient numerical upper bound.

This supplies the literal clause interfaces required by NativePreliminaryCount2011. It does not itself prove onehot, provide the middle-phase padding premises, or establish a tableau/Con(ZFC) equivalence.

## Fresh bounded Lean replay

Both new files were checked with the configured Lean v4.32.0, `-M6000 -j1`, and Elab.async false. The module was compiled to a temporary object under /tmp/current-clause2011-circuit-peer/DiophantineConsistency. Checks imported that new object through a temporary LEAN_PATH overlay with symlinks to the existing other prerequisite entries. No source or shared object was modified, and no Lake scheduler was run. Prerequisites were reused, not freshly rebuilt by these two commands.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentClause2011.lean -o /tmp/current-clause2011-circuit-peer/DiophantineConsistency/CurrentClause2011.olean
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c 'export LEAN_PATH=/tmp/current-clause2011-circuit-peer:"$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentClause2011Checks.lean'
```

Module: PASS, exit0,5.39seconds, peak3282576KB. Checks: PASS, exit0,3.23seconds, peak3232576KB. Logs: /tmp/current-clause2011-circuit-peer-module.log and /tmp/current-clause2011-circuit-peer-checks.log. The module emitted no diagnostics. All eight axiom reports contain only propext, Classical.choice, and Quot.sound: addition_residue, subtraction_residue, clause_mask, clause_convolution, selectorCount_eq_prefix, clause_low_residue, normalized_clause_residue, normalized_clause_mask. No sorryAx, native_decide axiom, or added source axiom occurs.

## Independent numeric source challenge

The program below invokes only the already independently reviewed, hash-pinned standard-library decimal/table reconstruction reproduced in wang-tiles942-lean-peer.md. It imports no repository implementation. From those actual printed715digits, full942tile weights and actual physical ranks, it builds every976 reflected entry and all979 kernel terms independently. It checks24 supported cyclic words at lengths1,2,3cells, including non-Boolean values because the clause identity does not require Booleanity. It compares direct convolution to the literal clause sum and its selector-count residue. Across every physical phase0..46 and incoming carries0,1,57,3384 normalization cases retain all low terms. The cross-cell absolute index3007/residue996 is also checked.

Normal and optimized Python runs passed with byte-identical output. Program SHA-256:a4c33d0f95eea00a9bd013f7548a26da19345d4293c05bbd9e8180cfc617278d. Output SHA-256:f1f0fc248f1d8f737dd9ef5b5b8edf1e4ec9125e866e768b8893eb46e540a043. These finite cases are an independent source-binding challenge, not a substitute for the universal Lean theorem or for global cyclic normalization existence.

```json
{
  "cell_lengths": [
    1,
    2,
    3
  ],
  "clause_cases": 24,
  "entry_count": 976,
  "includes_non_boolean_sources": true,
  "normalized_cases": 3384,
  "result": "PASS",
  "term_count": 979
}
```

To reproduce, first extract the exact Python appendix from wang-tiles942-lean-peer.md to /tmp/wang942-circuit-peer-numeric.py. Extract the following program to /tmp/current-clause2011-circuit-peer-numeric.py and run it under both `python` and `python -O`; compare their output bytes.

```python
import contextlib
import hashlib
import io
import json
import runpy
from pathlib import Path

# This is the previously fully reviewed peer script reproduced verbatim in
# reviews/wang-tiles942-lean-peer.md, not any incoming implementation.
program = Path('/tmp/wang942-circuit-peer-numeric.py')
if hashlib.sha256(program.read_bytes()).hexdigest() != 'd5d35cfd13210bd8ea975853d5d5e2107dc7b56b3443e31ebb6511df4d5b9f63':
    raise ValueError('reviewed decimal reconstruction changed')
with contextlib.redirect_stdout(io.StringIO()):
    d = runpy.run_path(str(program))
require = d['require']
weights, positions = d['weights'], d['positions']
entries = list(zip(positions, [2*w for w in weights]))
for pos, shift, width in [(978, 11, 8), (960, 19, 9), (969, 28, 8), (942, 36, 9)]:
    entries += [(pos+j, 2**(shift+j)) for j in range(width)]
require(len(entries) == 976 and len({p for p,w in entries}) == 976, 'complete entry list')
terms = [(18,1), (1004,1), (2020,1)] + [(1005-p,w) for p,w in entries]
support = set(range(951)) | set(range(960,986)) | {1004}
rho = 2**47
clause_cases, normalized_cases = 0, 0
for cells in (1,2,3):
    size = 2011*cells
    for mode in range(4):
        # Include non-Boolean values: the clause identity itself does not
        # require Booleanity or at-most-one occupancy.
        c = [((k*17+mode*13)%7+1 if mode else (k%2)) if k%2011 in support else 0
             for k in range(size)]
        for cell in range(cells):
            base = 2011*cell
            target = base+1005
            raw = sum(w*c[(target-e)%size] for e,w in terms)
            expected = c[base+1] + sum(w*c[base+p] for p,w in entries)
            require(raw == expected, 'literal clause convolution')
            count = sum(c[base+j] for j in range(942))
            require(raw%2048 == (2*count+c[base+1])%2048, 'all physical selectors low residue')
            require(c[(target-18)%size] == c[(target-2020)%size] == 0,
                    'unwanted bare inputs really absent')
            require(raw-sum(w*c[base+p] for p,w in entries) == c[base+1],
                    'bare selector1 is retained separately')
            clause_cases += 1
            for phase in range(47):
                for incoming in (0,1,57):
                    temporal = 2**phase
                    outgoing, digit = divmod(raw+temporal+incoming, rho)
                    require(raw+temporal+incoming == digit+rho*outgoing, 'normalization')
                    require(digit%2048 == (2*count+incoming+c[base+1]+temporal)%2048,
                            'normalized clause keeps incoming and temporal terms')
                    normalized_cases += 1
require((1005-2020)%4022 == 3007 and 3007%2011 == 996, 'cross-cell source')
print(json.dumps({'result':'PASS', 'entry_count':len(entries), 'term_count':len(terms),
                  'clause_cases':clause_cases, 'normalized_cases':normalized_cases,
                  'cell_lengths':[1,2,3], 'includes_non_boolean_sources':True}, sort_keys=True, indent=2))
```
