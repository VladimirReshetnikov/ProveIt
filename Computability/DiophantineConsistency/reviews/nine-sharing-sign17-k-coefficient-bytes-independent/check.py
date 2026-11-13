#!/usr/bin/env python3
import gzip,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-coefficient-bytes';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha((p/'check.py').read_bytes())=='e2f880def9fe5501d0d9515904d77ac10cdf4de114b9f5c81eb3d3a2f72636e1' and sha((p/'result.json').read_bytes())=='34f321334788707482641c54e78f9962dd59fdf54881eed8ad6269b5f772cf26'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';coeffs=root/'research/padding-staircase-independent/coefficients.json';assert sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac' and sha(coeffs.read_bytes())=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';c=json.loads(coeffs.read_text());assert len(c)==3297 and all(type(n)==int and n>=0 for n in c) and c[985]>0 and all(n==0 for n in c[986:])
binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']=='64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7' and len(raw)==11868
r=1<<47;h=0
for n in c[:986]:h=h*r+n
value=(h*r**20)+r**18+r**1004+r**2020;assert value.to_bytes(len(raw),'big')==raw
result=json.loads((p/'result.json').read_text());assert result['status']=='PASS_EXTERNAL_K_COEFFICIENT_RECIPE' and result['coefficient_count']==3297 and result['last_nonzero_index']==985 and result['raw_sha256']==sha(raw)
print(json.dumps({'status':'PASS_EXTERNAL_K_RECIPE','coefficient_count':len(c),'last_nonzero_index':985,'raw_bytes':len(raw),'scope':'external coefficient recipe equals raw K integer; no Lean K coefficient or file theorem'},indent=2))
