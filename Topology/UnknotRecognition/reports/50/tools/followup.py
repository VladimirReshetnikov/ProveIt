"""Longer batches for the main largest gain and the negative control."""
from bootstrap import bootstrap, PINS
ROOT=bootstrap()
from benchmark import fixtures, measure_case
import json,random,platform,sys
rng=random.Random(261008912)
selected={'static-disjoint-10','paired-blocks-8','all-signatures-6'}
rows=[measure_case(c,rng,7,10) for c in fixtures() if c[0] in selected]
result=dict(seed=261008912,rounds=7,repeats=10,python=sys.version,
            platform=platform.platform(),native_git_blobs=PINS,cases=rows,
            reason='Longer batches to assess initial identical-arm variability; initial results retained')
(ROOT/'results/benchmark_followup.json').write_text(json.dumps(result,indent=2))
for r in rows:print(r['name'],r['medians_ms'],r['paired_dense_over_arm'])
