#!/usr/bin/env python3
"""Size companion for the frozen n=2 partial scalar construction."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;root=h.parents[1];p=root/'research/trace74-mask-coordinate-probe/candidate.json'
def sha(x):return hashlib.sha256(x).hexdigest()
assert sha((h/'check.py').read_bytes())=='5b606d5a9864be51eed36d7bbb11812ef3e4928500eb732b802741a86290a9e4'
assert sha(p.read_bytes())=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
x=json.loads(p.read_text());item=x['coefficient_binding']['ports']['beta'];data=(root/'candidates/ten-positive-qcube-product-square/coefficients'/item['file']).read_bytes();raw=gzip.decompress(data)
assert sha(data)==item['parent_gzip_sha256'] and sha(raw)==item['raw_sha256'];q=int.from_bytes(raw,'little')+1
assert q==2**(67*8807)
P=q**7;k=8*P+4;Y=q**3;c=k*Y+1
assert 8*P+4<=k and 2*q**4<c
print(json.dumps({'status':'PASS','n':2,'P':'q^7','k':'8*P+4','k_bound':True,'c':'k*q^3+1','c_gt_two_q4':True,'scope':'same partial scalar tuple as pinned check.py; no full graph zero'},sort_keys=True))
