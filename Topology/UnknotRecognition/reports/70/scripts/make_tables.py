#!/usr/bin/env python3
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
a=json.loads((ROOT/'results/benchmarks.json').read_text())
rows=[]
labels={'sparse-prefix-replay':'96 sparse prefixes','monotone-epoch-rebuilds':'200 full-map updates'}
for x in a['experiments']:
    label=labels.get(x['name'],r'$W='+x['name'].split('-')[-1]+'$')
    m=x['medians']
    rows.append(f"{label} & {1000*m['reference']:.3f} & {1000*m['optimized']:.3f} & {x['paired_reference_over_optimized']:.2f} & {x['paired_control_over_optimized']:.2f} \\\\")
(ROOT/'article/benchmark_table.tex').write_text('\n'.join(rows)+'\n\\bottomrule\n')
rows=[]
for x in a['large_bit_certificates']:
    rows.append(f"$2^{{{x['exponent']}}}$ & {1000*x['median_seconds']:.3f} & {x['histogram_support']} & {x['certificate_bytes']:,} \\\\")
(ROOT/'article/certificate_table.tex').write_text('\n'.join(rows)+'\n\\bottomrule\n')
