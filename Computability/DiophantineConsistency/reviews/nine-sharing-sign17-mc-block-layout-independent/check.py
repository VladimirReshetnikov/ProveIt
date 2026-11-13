#!/usr/bin/env python3
import gzip,hashlib,itertools,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mc-block-layout';sha=lambda b:hashlib.sha256(b).hexdigest();assert sha((p/'check.py').read_bytes())=='dd84a5dec47a120bd8064516448ce47afb5522fc555efe226a48cb9001dc8ed9' and sha((p/'result.json').read_bytes())=='e05f1f4caef342b7cceebf8fae1c25332c6b5be0649e629a79bfd7feaab6751c'
seed=root/'research/nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(seed.read_bytes())=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';binding=json.loads(seed.read_text())['coefficient_binding'];rec=binding['ports']['MC'];packed=(seed.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert sha(packed)==rec['gzip_sha256'] and sha(raw)==rec['raw_sha256']=='2b5c9296e32616260e64a051c92892645b9aa1bf0bf4c0d931e464080702ca9f' and len(raw)==11815
support=set(range(951))|set(range(960,986))|{1004};digits=[(1<<47)-(2 if i in support else 1) for i in range(2011)];expected=[]
for start in range(0,2011,8):
 block=digits[start:start+8];value=0
 for d in reversed(block):value=value*(1<<47)+d
 expected.append(value.to_bytes((47*len(block)+7)//8,'little'))
assert len(expected)==252 and b''.join(expected)==raw[::-1]
patterns={tuple(digits[i:i+8]) for i in range(0,2011,8)};assert len(patterns)==6
segments=[(len(list(g)), key) for key,g in itertools.groupby(tuple(digits[i:i+8]) for i in range(0,2011,8))];assert [n for n,_ in segments]==[118,1,1,3,1,1,1,125,1]
result=json.loads((p/'result.json').read_text());assert result['status']=='PASS_EXTERNAL_BLOCK_LAYOUT' and result['blocks']==252 and result['raw_sha256']==sha(raw) and [c for _,c in result['segments']]==[n for n,_ in segments]
print(json.dumps({'status':'PASS_EXTERNAL_RECONSTRUCTION','blocks':252,'distinct_patterns':6,'run_counts':[n for n,_ in segments],'scope':'independent Python arithmetic and filesystem only; no Lean file or whole-port theorem'},indent=2))
