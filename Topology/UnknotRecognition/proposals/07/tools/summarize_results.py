"""Generate readable paired results from the recorded cold-process measurements."""
from __future__ import annotations
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMES = {
    'conway.json': 'Conway (11 crossings)',
    'kinoshita_terasaka.json': 'Kinoshita--Terasaka (11)',
    'hard_unknot_8.json': 'Hard unknot (8)',
    'random5_36.json': 'Five-strand example (36)',
    'unknot_braid40.json': 'Unknot braid (40)',
    'torus_3_5.json': 'Torus knot T(3,5) (10)',
    'conway_sum_2.json': 'Two Conway summands (22)',
    'conway_sum_3.json': 'Three Conway summands (33)',
    'unknot_chain_64.json': 'Unknot chain (64)',
    'unknot_chain_256.json': 'Unknot chain (256)',
    'unknot_chain_1024.json': 'Unknot chain (1024)',
}

def main() -> None:
    data = json.loads((ROOT/'results/benchmark.json').read_text())
    rows = {(r['case'], r['mode'], r['backend']): r for r in data['measurements']}
    cap = data['soft_cap_seconds']
    paired = []
    lines = ['# Recorded benchmark summary', '',
             'Times are seconds; medians of three fresh processes for completed cases.',
             'A capped case has only one attempt and is a lower bound, not a runtime.',
             'Inputs and imports are outside timing for both versions.', '',
             '| Case | Operation | Baseline | Accelerated | Baseline / accelerated |',
             '|---|---|---:|---:|---:|']
    for (case, mode, backend), new in rows.items():
        if backend != 'optimized' or (case, mode, 'baseline') not in rows:
            continue
        old = rows[case, mode, 'baseline']
        a, b = old['median_seconds'], new['median_seconds']
        ratio = (a if a is not None else cap)/b if b else None
        a_text = f'{a:.6g}' if a is not None else f'>{cap:g} (capped)'
        b_text = f'{b:.6g}' if b is not None else 'capped'
        display_ratio = ratio
        if ratio and a is None:
            scale = 10**(2-math.floor(math.log10(ratio)))
            display_ratio = math.floor(ratio*scale)/scale
        r_text = ('' if a is not None else '>')+f'{display_ratio:.3g}x' if ratio else 'n/a'
        lines.append(f'| {NAMES.get(case, case)} | {mode} | {a_text} | {b_text} | {r_text} |')
        paired.append({'case':case, 'mode':mode, 'baseline_seconds':a,
                       'accelerated_seconds':b, 'speed_ratio':ratio,
                       'ratio_is_censored_lower_bound':a is None})
    lines += ['', '## Caveats', '',
              '`scan` does not include preprocessing or filters. The 36-crossing case',
              'is already cheap in the baseline default pipeline (its Alexander test',
              'rejects it after reduction), so its backend improvement is not a',
              'corresponding full-pipeline speedup. `forced-scan-pipeline` disables',
              'Alexander and, for the new code, Jones; it isolates decomposition.',
              '`order` measures only greedy scan ordering, not knot recognition.',
              'A ratio below one is an observed regression on that case.', '',
              'The `old-algebra-fill` ablation changes only pivot scheduling and uses',
              'the baseline uncached algebra. It independently gives reduced rank',
              '2949 for the 36-crossing case, agreeing with the optimized backend.',
              'Neither benchmark agreement nor d-squared checks are formal verification.']
    (ROOT/'results/summary.md').write_text('\n'.join(lines)+'\n')
    (ROOT/'results/paired-summary.json').write_text(json.dumps(paired,indent=2)+'\n')

if __name__ == '__main__':
    main()
