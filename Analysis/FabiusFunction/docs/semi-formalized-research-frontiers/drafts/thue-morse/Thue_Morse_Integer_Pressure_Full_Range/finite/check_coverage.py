"""Check the delivered pressure data, hashes, degree lists and exact signs.

Extract all interval ZIPs into the package directory so data/ is its sibling.
An alternate data directory can be supplied as the first argument.
This checks output evidence; replay_one.py regenerates the arithmetic proof.
"""
from pathlib import Path
import hashlib,json,sys
sys.set_int_max_str_digits(0)
root=Path(__file__).resolve().parent
data=Path(sys.argv[1]) if len(sys.argv)>1 else root.parent/'data'
manifest=json.loads((root/'production_manifest.json').read_text())
assert [r['m']for r in manifest['cases']]==list(range(2,112))
total=orders=states=0
for row in manifest['cases']:
    m=row['m'];raw=(data/row['pressure_file']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==row['pressure_sha256']
    v=json.loads(raw);assert v['m']==m
    bounds=v['pressure_bounds'];assert [r['degree']for r in bounds]==list(range(2*m,6*m,2))
    for i,r in enumerate(bounds):
        lo,hi,den=map(int,(r['lower_numerator'],r['upper_numerator'],r['denominator']))
        assert den>0 and lo<=hi and ((lo>0)if i else(lo<=0<=hi))
    assert row['checked_response_orders']==v['checked_response_orders']==6*m-2
    idx=json.loads((root/'state_indices'/f'compact_m{m:03}.json').read_text())
    assert idx['m']==m and [r['order']for r in idx['orders']]==list(range(6*m-1))
    total+=len(bounds)-1;orders+=6*m-2;states+=6*m-1
assert (total,orders,states)==(12320,37070,37180)
print('PASS: 110 orders, 12320 positive intervals, 37070 nonconstant response orders, 37180 state hashes.')
