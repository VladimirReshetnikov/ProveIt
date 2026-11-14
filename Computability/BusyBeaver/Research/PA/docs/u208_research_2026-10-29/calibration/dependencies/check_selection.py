"""Validate retained dependency bytes and exact U212/theory binding; do not run dependency programs."""
from pathlib import Path
import hashlib,json,zipfile,io
r=Path(__file__).resolve().parent; d=json.loads((r/'SELECTION_LEDGER.json').read_text())
def need(b,m):
 if not b:raise RuntimeError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
n=0
for x in d['members']:
 if x['destination'] is None:continue
 p=r/x['destination'];need(p.is_relative_to(r) and '..' not in Path(x['destination']).parts,'path');b=p.read_bytes();need(len(b)==x['bytes'] and sha(b)==x['sha256'],'member '+x['destination']);n+=1
b=(r/'u212_combined_2026-10-29.zip').read_bytes();a=next(x for x in d['archives']if x['label']=='Research/reference/u212_combined_2026-10-29.zip');need(len(b)==a['bytes'] and sha(b)==a['sha256'],'U212 archive')
with zipfile.ZipFile(io.BytesIO(b)) as z:
 need(z.testzip() is None,'CRC');nm=next(n for n in z.namelist()if n.endswith('pa_unary_power_cover.zip'));need(sha(z.read(nm))==d['theory_U_sha256'],'theory U')
print('PASS',n,'retained dependency member hashes and nested theory U')
