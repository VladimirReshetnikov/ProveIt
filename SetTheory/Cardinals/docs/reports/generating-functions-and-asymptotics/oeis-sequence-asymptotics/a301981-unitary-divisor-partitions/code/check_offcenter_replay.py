"""Off-center higher-cutoff/precision replay and exact tail bounds through r=7."""
from pathlib import Path
import json
from numerics_core import offcenter_diagnostics,rational_tail_bounds
base=Path(__file__).resolve().parents[1]
hi=offcenter_diagnostics(cutoff=1800,precision=90)
(base/'data/offcenter_replay_1800_90.json').write_text(json.dumps(hi,indent=2)+'\n')
lo=json.loads((base/'data/offcenter_diagnostics.json').read_text())
keys=['t0','delta','grades_1_through_5','errors']
comparisons=[{'sequence':a['sequence'],'n':a['n'],
              'all_stored_digits_match':all(a[k]==b[k] for k in keys)}
             for a,b in zip(lo['cases'],hi['cases'])]
assert len(comparisons)==8
assert all(x['all_stored_digits_match'] for x in comparisons)
_,bounds=rational_tail_bounds([1200,1800],7)
bounds=[{'cutoff':b['cutoff'],'r':b['derivative_order'],
         'numerator':b['bound_numerator'],'denominator':b['bound_denominator'],
         'approx_decimal':b['approximate_decimal_for_readability']} for b in bounds]
report={'comparisons':comparisons,'rational_tail_bounds_for_t_at_least_one_tenth':bounds,
        'scope':'Exact coefficient equality and truncation majorants; floating ratios/roundoff remain non-interval.'}
(base/'data/offcenter_replay_report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'all_stored_digits_match':True,'cases':len(comparisons)},indent=2))
