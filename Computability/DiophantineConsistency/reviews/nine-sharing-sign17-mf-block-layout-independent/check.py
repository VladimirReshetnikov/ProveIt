#!/usr/bin/env python3
import gzip,hashlib,itertools,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mf-block-layout';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha((p/'check.py').read_bytes())=='d316191f784d0f36ef5f64a62c9b7f5383866a40a577cea7250fd3710bb3eee0' and sha((p/'result.json').read_bytes())=='31ed2aa6a062402179dfee6bcc203cec9d2cccf190f2e45d25a817acca93f5e4'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MF'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']=='5c15fc24e4978b878ed531abf30b2dcfe255083372034612b759b65eee1f0c25' and len(raw)==11815
digits=[3]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005+[1];assert len(digits)==2012;blocks=[]
for start in range(0,2012,8):
 chunk=digits[start:start+8];value=0
 for d in reversed(chunk):value=value*(1<<47)+d
 blocks.append(value.to_bytes(47 if len(chunk)==8 else 18,'little'))
assert len(blocks)==252 and b''.join(blocks)==raw[::-1]
patterns={tuple(digits[i:i+8]) for i in range(0,2012,8)};assert len(patterns)==10
segments=[(len(list(g)), key) for key,g in itertools.groupby(tuple(digits[i:i+8]) for i in range(0,2012,8))];counts=[n for n,_ in segments];assert counts==[1,113,1,5,1,1,1,1,1,1,125,1]
result=json.loads((p/'result.json').read_text());assert result['status']=='PASS_EXTERNAL_MF_BLOCK_LAYOUT' and result['blocks']==252 and result['raw_sha256']==sha(raw) and [c for _,c in result['segments']]==counts
print(json.dumps({'status':'PASS_EXTERNAL_RECONSTRUCTION','blocks':252,'distinct_patterns':10,'run_counts':counts,'scope':'independent Python arithmetic/filesystem only; no Lean file or whole-port theorem'},indent=2))
