"""Check the m=24 interval against independently reduced exact rational values."""
from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)
r=Path(__file__).resolve().parent
p=Path(sys.argv[1])if len(sys.argv)>1 else r.parent/'data/interval_m024.json'
exact=json.loads((r/'exact_reference_m024.json').read_text())
interval=json.loads(p.read_text());assert exact['m']==interval['m']==24
for row in interval['pressure_bounds']:
    n,_,d=exact['pressure_even_coefficients'][row['degree']//2].partition('/')
    n,d=int(n),int(d or'1');lo,hi,den=map(int,(row['lower_numerator'],row['upper_numerator'],row['denominator']))
    assert lo*d<=n*den<=hi*d
print('PASS: all m=24 intervals enclose the independently reduced exact coefficients.')
