#!/usr/bin/env python3
"""Compose prior checked Lean headers by exact source hash and import list."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;V=D.parent
N=('ipra-current-repaired-survey','ipra-current-repaired-six-drift-source-survey','ipra-current-repaired-seven-drift-source-survey','ipra-current-repaired-eight-drift-source-survey','ipra-current-repaired-eleven-drift-source-survey','ipra-current-repaired-post172-source-survey','ipra-current-repaired-post159-preliminary-source-survey','ipra-current-repaired-post159-four-drift-source-survey','ipra-current-repaired-post159-final-source-survey','ipra-current-repaired-post120-eight-drift-source-survey','ipra-current-repaired-post120-final-source-survey','ipra-current-native14-source-survey-v2')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();paths=[Path(__file__).resolve(),D/'manifest.json'];layers=[]
for name in N:
 root=V/name;mp=root/'manifest.json';rp=root/'lean-deps-receipt.json';paths.extend((mp,rp));m=json.loads(mp.read_text());r=json.loads(rp.read_text())
 if name=='ipra-current-repaired-survey':
  lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');checker=root/'check_lean_deps.py';paths.extend((lean,checker));assert r['manifest_sha256']==H(mp) and r['checker_sha256']==H(checker) and r['lean_sha256']==H(lean) and r['count']==len(r['rows'])==1099 and not r['errors'];keys=set(r['rows'])
 else:
  assert r['status']=='PASS_HEADER_DEPS'
  for p,h in r['input_sha256'].items():assert H(p)==h;paths.append(Path(p))
  assert r['input_sha256'][str(mp.absolute())]==H(mp)
  keys=set(r['rows']) if 'rows' in r else {r['module']}
  if 'rows' in r:
   for row in r['rows'].values():
    if 'stdout' in row:assert hashlib.sha256(row['stdout'].encode()).hexdigest()==row['stdout_sha256']
  elif 'stdout' in r:assert hashlib.sha256(r['stdout'].encode()).hexdigest()==r['stdout_sha256']
 layers.append((name,m,keys))
before={str(p.resolve()):H(p) for p in paths};cur=json.loads((D/'manifest.json').read_text());assert len(cur['sources'])==995
base=layers[-2][1];orig=layers[0][1];extra=layers[-1][1];shared=set(cur['sources'])&set(base['sources']);added=set(cur['sources'])-set(base['sources']);assert len(shared)==984 and len(added)==11
used={};changed=[]
for name,row in cur['sources'].items():
 p=D/'sources'/(name.replace('.','/')+'.lean');assert p.is_file() and not p.is_symlink() and H(p)==row['sha256']
 if name in shared:assert row==base['sources'][name]
 else:assert row==extra['sources'][name]
 options=[label for label,m,keys in layers if name in keys and name in m['sources'] and m['sources'][name]==row]
 assert options,('missing verified exact-source header',name)
 used[name]=options[-1]
 if name in shared and row!=orig['sources'][name]:changed.append(name)
assert {str(p.resolve()):H(p) for p in paths}==before
assert all(H(D/'sources'/(n.replace('.','/')+'.lean'))==row['sha256'] for n,row in cur['sources'].items())
out={'status':'PASS_DEPENDENCY_RECEIPT_COVERAGE','input_sha256':before,'count':len(cur['sources']),'shared_count':len(shared),'additional_count':len(added),'changed_shared_count':len(changed),'changed_shared':sorted(changed),'covering_receipts':used,'boundary':'Composes previously recorded Lean header checks using exact source hashes and import lists; captures a historical source snapshot and does not authenticate project objects, dynamic imports or a successor proof.'};p=D/'dependency-inheritance-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],out['count'],out['changed_shared_count'],H(p))
