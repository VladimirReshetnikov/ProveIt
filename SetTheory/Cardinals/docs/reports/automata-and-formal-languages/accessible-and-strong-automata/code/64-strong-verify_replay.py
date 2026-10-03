"""Compare a fresh computation directory with the distributed reference data."""
from pathlib import Path
import json
import sys
import mpmath as mp
mp.mp.dps = 110
root = Path(__file__).resolve().parent
fresh = Path(sys.argv[1]).resolve()
files = [f'coefficients_k{k}.json' for k in (2,3,4)] + [
    'precision_validation.json', 'exact_sector_validation.json',
    'inverse_validation.json', 'all_model_inverse_validation.json', 'cyclic_lift_validation.json',
    'independent_checks/low_orders.json', 'independent_checks/small_models.json'] + [
    f'independent_checks/exact_k{k}.json' for k in (2,3,4)]
def clean(value):
    if isinstance(value,dict): return {k:clean(v) for k,v in value.items() if k != 'seconds'}
    if isinstance(value,list): return list(map(clean,value))
    return value
for name in files:
    expected = clean(json.loads((root/name).read_text()))
    actual = clean(json.loads((fresh/name).read_text()))
    assert actual == expected, f'Reference mismatch: {name}'
for row in json.loads((fresh/'independent_checks/low_orders.json').read_text()):
    for field,values in row['differences'].items():
        assert max(map(lambda x:abs(mp.mpf(x)),values)) < mp.mpf('1e-68'), (row['k'],field)
for row in json.loads((fresh/'all_model_inverse_validation.json').read_text()):
    assert abs(mp.mpf(row['degree5_smooth_error'])) < abs(mp.mpf(row['two_correction_error']))
print(f'All {len(files)} JSON outputs match, ignoring only run time fields.')
print('Independent coefficient discrepancies < 1e-68; all 48 inverse improvement checks passed.')
