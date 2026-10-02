"""Double-cutoff/higher-precision replay plus exact rational truncation bounds."""
from pathlib import Path
import json
from numerics_core import saddle_diagnostics,rational_tail_bounds
base=Path(__file__).resolve().parents[1]
hi=saddle_diagnostics(cutoff=2000,precision=80,include_fixed=True)
(base/'data/fixed_saddle_replay_2000_80.json').write_text(json.dumps(hi,indent=2)+'\n')
lo=json.loads((base/'data/fixed_saddle_diagnostics.json').read_text())
keys=['t','C1','C2','relative_errors_M0_M1_M2','fixed_saddle_relative_error',
      'location_difference_over_t0_squared','stationary_exponent_difference']
comparisons=[{'sequence':a['sequence'],'n':a['n'],
              'all_stored_digits_match':all(a[k]==b[k] for k in keys),
              'changed_fields':[k for k in keys if a[k]!=b[k]]}
             for a,b in zip(lo,hi)]
assert len(comparisons)==10
assert all(x['all_stored_digits_match'] for x in comparisons)
lower,bounds=rational_tail_bounds([1000,2000],6)
report={'baseline':{'cutoff':1000,'decimal_working_precision':60},
        'replay':{'cutoff':2000,'decimal_working_precision':80},
        'comparisons':comparisons,
        'all_saddles_greater_than_one_tenth_lower_mean':
           {'numerator':lower.numerator,'denominator':lower.denominator,'float':float(lower)},
        'rigorous_rational_absolute_tail_upper_bounds':bounds,
        'scope':'Exact truncation majorants; floating arithmetic and roots themselves are not interval-certified.'}
(base/'data/cutoff_precision_report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'all_stored_digits_match':True,'case_count':len(comparisons),
                  'cutoff1000_bounds':[(x['derivative_order'],x['approximate_decimal_for_readability'])
                                       for x in bounds if x['cutoff']==1000]},indent=2))
