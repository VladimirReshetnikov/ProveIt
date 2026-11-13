#!/usr/bin/env python3
"""Materialize the 70/140 and 71/128 gate lists with the 2011 port tuple."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; HERE=Path(__file__).resolve().parent
def load(path,h):
    b=(D/path).read_bytes()
    if hashlib.sha256(b).hexdigest()!=h:raise RuntimeError('input drift '+path)
    return json.loads(b)
base=load('research/thirteen-unit-sphere96/polynomial.json','48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1')
inputs={70:('research/thirteen-variable-independent/polynomial70.json','b36b1b4fa645b772d5cafe82a0359eca264e228114cacd2fcce6da902b2eac82'),71:('research/thirteen-variable-normalized-independent/polynomial.json','50c7d99e5a1abb19f83c9c3b243995d965ecb3d1d39d509d13fd3b18dcec95d4')}
for n,(path,h) in inputs.items():
    old=load(path,h); out=HERE/f'polynomial{n}.json'
    if out.exists():raise RuntimeError('refusing overwrite '+str(out))
    data={'schema':'literal_integer_arithmetic_dag_v1','name':f'thirteen_positive_current2011_{n}',
      'witness_domain':'strictly positive integers','witnesses':old['witnesses'],'fixed_numerals':old['fixed_numerals'],
      'coefficient_binding':{'path':'../thirteen-unit-sphere96/coefficients/','ports':base['coefficient_binding']['ports'],
        'raw_bytes':base['coefficient_binding']['raw_bytes']},'operations':old['operations'],
      'operation_counts':old['operation_counts'],'exact_degree':{70:140,71:128}[n],
      'source':old['source'],'output':old['output'],'source_graph':path,'source_graph_sha256':h}
    out.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
