#!/usr/bin/env python3
import gzip,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-block-layout';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha((p/'check.py').read_bytes())=='8ee7f7c0f32cb36bbe8f01d997faf7094c6aee0f0ef792621cb58bce76f43352' and sha((p/'result.json').read_bytes())=='390af8360b10c73cfa37584b4451f6b7f3b2becd40c6312321afde551706ea35'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';coeffs=root/'research/padding-staircase-independent/coefficients.json';assert sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac' and sha(coeffs.read_bytes())=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';c=json.loads(coeffs.read_text());assert len(c)==3297 and c[985]>0 and all(x==0 for x in c[986:]);r=1<<47;h=0
for x in c[:986]:h=h*r+x
value=h*r**20+r**18+r**1004+r**2020;binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['K0'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']=='64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7' and len(raw)==11868 and value.to_bytes(len(raw),'big')==raw
v=value;digits=[]
while v:v,d=divmod(v,r);digits.append(d)
assert len(digits)==2021
blocks=[]
for i in range(0,len(digits),8):
 ds=digits[i:i+8];n=0
 for d in reversed(ds):n=n*r+d
 blocks.append(n.to_bytes(47 if len(ds)==8 else 24,'little'))
assert b''.join(blocks)==raw[::-1] and len(blocks)==253 and len(set(blocks))==126 and sum(b==bytes(47) for b in blocks)==128
result=json.loads((p/'result.json').read_text());assert result['status']=='PASS_EXTERNAL_K_BLOCK_LAYOUT' and result['block_sha256']==[sha(b) for b in blocks] and result['radix_digits']==2021 and result['tail_bytes']==24
print(json.dumps({'status':'PASS_EXTERNAL_RECONSTRUCTION','radix_digits':2021,'blocks':253,'distinct_patterns':126,'zero_full_blocks':128,'tail_bytes':24,'scope':'external coefficient recipe decomposition only; no Lean K-to-array/file theorem'},indent=2))
