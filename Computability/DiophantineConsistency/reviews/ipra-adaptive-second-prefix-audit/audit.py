#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,os,collections,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];C=R/'Computability/DiophantineConsistency/reviews';Q=C/'ipra-adaptive-native-warning-continuation';M=Q/'manifest.json';DR=Q/'replay.py';REC1=C/'ipra-adaptive-prefix-audit/receipt.json';REC2=C/'ipra-adaptive-warning-prefix-audit/receipt.json';P=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');P1=Path('/tmp/ipra-adaptive-native-current-qpk97_3z');P2=Path('/tmp/ipra-adaptive-native-continuation-l58un8d6');A=Path('/tmp/ipra-adaptive-native-warning-continuation-qze9dm1q');B=Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();m=json.loads(M.read_text());a=json.loads((A/'state.json').read_text());b=json.loads((B/'state.json').read_text());mh=h(M);dh=h(DR);ah=h(__file__);asum=h(A/'state.json');bsum=h(B/'state.json');k=2
assert a['status']==b['status']=='FAILED' and a['failure']==b['failure']=='KeyboardInterrupt()'
assert a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256']
assert [r['name'] for r in a['records'][:k]]==[r['name'] for r in b['records'][:k]]==m['order'][:k]
changed='DiophantineConsistency.MFCurrentHighDigits2011';rev=collections.defaultdict(set)
for n,ds in m['direct_imports'].items():
 for d in ds:rev[d].add(n)
cone={changed};todo=[changed]
while todo:
 for n in rev[todo.pop()]-cone:cone.add(n);todo.append(n)
assert not cone.intersection(m['prefix']+m['second_prefix']+m['order'][:k])
seen=set(m['prefix']+m['second_prefix']);affected=set(m['affected'])
for x,y in zip(a['records'][:k],b['records'][:k]):
 assert x['name']==y['name'] and x['exit']==y['exit']==0 and x['object_sha256']==y['object_sha256'] and x['log_sha256']==y['log_sha256'] and x['warnings']==y['warnings']==[]
 assert set(x['direct_imports'])==set(y['direct_imports'])
 for n in x['direct_imports']:
  assert x['direct_imports'][n]['sha256']==y['direct_imports'][n]['sha256'];assert n not in affected or n in seen
 seen.add(x['name'])
def audit():
 assert h(M)==mh and h(DR)==dh and h(__file__)==ah and h(A/'state.json')==asum and h(B/'state.json')==bsum
 assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256'] and h(REC1)==m['prefix_receipt_sha256'] and h(P1/'state.json')==m['prefix_state_sha256'] and h(REC2)==m['warning_receipt_sha256'] and h(P2/'state.json')==m['second_prefix_state_sha256']
 assert all(h(R/p)==m['source_sha256'][n] for n,p in m['source_files'].items())
 assert all(h(Q/'sources'/(n.replace('.','/')+'.lean'))==m['source_sha256'][n] for n in m['affected'])
 inv={str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')};assert inv==set(m['parent_objects'])
 assert all(h(P/'lib'/f)==v for f,v in m['parent_objects'].items())
 assert all(h(PKG/f)==v['sha256'] and str((PKG/f).resolve())==v['resolved_path'] for f,v in m['external_direct'].items())
 for provider,records in [(P1,m['prefix_records']),(P2,m['second_prefix_records'])]:
  for n,row in records.items():
   assert h(provider/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(provider/'logs'/(n.replace('.','_')+'.log'))==row['log_sha256']
   assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
 for root,state in [(A,a),(B,b)]:
  for row in state['records'][:k]:
   n=row['name'];assert h(root/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(root/'logs'/(n.replace('.','_')+'.log'))==row['log_sha256'];assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
audit()
for label,root in [('author',A),('independent',B)]:
 shutil.copyfile(root/'state.json',D/(label+'-interrupted-state.json'));dest=D/(label+'-logs');dest.mkdir(exist_ok=True)
 for row in json.loads((root/'state.json').read_text())['records']:
  f=row['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/f,dest/f)
shutil.copyfile(R/m['source_files'][changed],D/'MFCurrentHighDigits2011-before-merge.lean');audit()
receipt={'status':'PASS','purpose':'Authenticate 103 inherited plus two matching completed rows from intentionally interrupted runs before source merge; endpoint not established.','author_root':str(A),'peer_root':str(B),'author_state_sha256':asum,'peer_state_sha256':bsum,'manifest_sha256':mh,'driver_sha256':dh,'audit_sha256':ah,'first_receipt_sha256':h(REC1),'second_receipt_sha256':h(REC2),'prefix':m['prefix']+m['second_prefix'],'new_prefix':m['order'][:k],'author_rows':a['records'][:k],'peer_rows':b['records'][:k],'changed_source':changed,'changed_reverse_cone':sorted(cone),'source_count':len(m['source_files']),'parent_object_count':len(m['parent_objects']),'external_file_count':len(m['external_direct']),'boundary':m['scope']}
(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('SECOND_PREFIX_AUDIT_PASS',len(receipt['prefix']),'+',k,'cone',len(cone),flush=True)
