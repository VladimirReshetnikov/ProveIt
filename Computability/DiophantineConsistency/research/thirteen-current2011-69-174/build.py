#!/usr/bin/env python3
"""Retarget the audited 69-row gate list to the current2011 port tuple."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def load(path,h):
 b=(D/path).read_bytes()
 if hashlib.sha256(b).hexdigest()!=h:raise RuntimeError('input drift '+path)
 return json.loads(b)
base=load('research/thirteen-unit-sphere96/polynomial.json','48573f58aac3d60f706eb7f52e92f5c061bd74d41ad7e9e9ee3e2ea43dcd9ca1')
path='research/thirteen-variable-independent/polynomial69.json';h='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f';old=load(path,h)
out=P/'polynomial69.json'
if out.exists():raise RuntimeError('refuse overwrite')
g={'schema':'literal_integer_arithmetic_dag_v1','name':'thirteen_positive_current2011_69','witness_domain':'strictly positive integers','witnesses':old['witnesses'],'fixed_numerals':old['fixed_numerals'],'coefficient_binding':{'path':'../thirteen-unit-sphere96/coefficients/','ports':base['coefficient_binding']['ports'],'raw_bytes':base['coefficient_binding']['raw_bytes']},'operations':old['operations'],'operation_counts':old['operation_counts'],'exact_degree':174,'source':old['source'],'output':old['output'],'source_graph':path,'source_graph_sha256':h}
out.write_text(json.dumps(g,indent=2,sort_keys=True)+'\n')
