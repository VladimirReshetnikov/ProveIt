"""Regenerate article tables from saved paired benchmark samples."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT/'data/benchmark.json').read_text())
rows = []
for r in data['endpoint']:
    rows.append(f"{r['strands']} & {r['letters']} & {1000*r['median_baseline_seconds']:.3f} & "
                f"{1000*r['median_new_verified_seconds']:.3f} & {r['median_paired_speedup']:.2f} & "
                f"{r['median_AA']:.3f} \\\\")
(ROOT/'article/endpoint_rows.tex').write_text('\n'.join(rows)+'\n')
rows = [f"{r['letters']} & {r['raw_generators']} & {r['median_paired_speedup']:.2f} \\\\" 
        for r in data['standalone_recognition']]
(ROOT/'article/cube_rows.tex').write_text('\n'.join(rows)+'\n')
