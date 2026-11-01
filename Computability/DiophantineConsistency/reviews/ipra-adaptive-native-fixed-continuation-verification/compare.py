#!/usr/bin/env python3
"""Authenticate and compare both finished fixed-snapshot endpoint replays."""
from pathlib import Path
import json,hashlib,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';DR=F.parent/'replay.py';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';P=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');A=Path('/tmp/ipra-adaptive-native-fixed-continuation-8mckr1yj');B=Path('/tmp/ipra-adaptive-native-fixed-continuation-n1l8kvzg');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
f,fh=read(F);a,ah=read(A/'state.json');b,bh=read(B/'state.json');dh=h(DR);ch=h(__file__);assert a['status']==b['status']=='PASS' and a['manifest_sha256']==b['manifest_sha256']==fh and a['driver_sha256']==b['driver_sha256']==dh==f['driver_sha256'];assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==f['order']
files={}
def add(p,v):
 key=str(Path(p));assert key not in files or files[key]==v,(key,files[key],v);files[key]=v
add(P/'state.json',f['parent_state_sha256'])
for path,key in [(V/'ipra-adaptive-prefix-audit/receipt.json','prefix_receipt_sha256'),(V/'ipra-adaptive-warning-prefix-audit/receipt.json','warning_receipt_sha256'),(V/'ipra-adaptive-second-prefix-audit/receipt.json','second_audit_receipt_sha256'),(V/'ipra-adaptive-fixed-snapshot-prefix/receipt.json','fixed_snapshot_receipt_sha256')]:add(path,f[key])
for path,key in [(Path('/tmp/ipra-adaptive-native-current-qpk97_3z'),'prefix_state_sha256'),(Path('/tmp/ipra-adaptive-native-continuation-l58un8d6'),'second_prefix_state_sha256'),(Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da'),'third_prefix_state_sha256'),(Path('/tmp/ipra-adaptive-native-second-continuation-8ziag05a'),'fourth_prefix_state_sha256')]:add(path/'state.json',f[key])
add(LEAN,f['lean_sha256'])
for n,v in f['source_sha256'].items():add(SNAP/(n.replace('.','/')+'.lean'),v)
for rel,v in f['parent_objects'].items():add(P/'lib'/rel,v)
for rel,v in f['external_direct'].items():assert str((PKG/rel).resolve())==v['resolved_path'];add(PKG/rel,v['sha256'])
def warnings(s):
 out=[]
 for line in s.splitlines():
  if 'warning:' not in line: continue
  msg=line.split('warning:',1)[1].strip()
  tests=[('unused_simp',r'^This simp argument is unused:'),('unused_section',r'^automatically included section variable\(s\) unused in theorem '),('unused_variable',r'^Variable name `[^`]+` is not explicitly referenced\.$'),('simp_suggestion',r"^(?:try 'simp' instead of 'simpa'|Try `simp at this` instead of `simpa using this`)$"),('noop_tactic',r"^'.+' tactic does nothing$"),('unreachable_tactic',r'^this tactic is never executed$'),('deprecation',r'^`[^`]+` has been deprecated(?:[.:].*)?$'),('simp_discrimination',r'^Left-hand side of simp theorem is headed by a `\.other` key in the discrimination tree'),('tactic_sequence',r'^Used `tac1 <;> tac2` where `\(tac1; tac2\)` would suffice$'),('exponent_threshold_notice',r'^exponent [0-9]+ exceeds the threshold [0-9]+, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold$')]
  hits=[cat for cat,pat in tests if re.search(pat,msg)]
  assert len(hits)==1,('unrecognized warning',line)
  out.append({'category':hits[0],'message':msg,'full_line':line})
 return out


for x,y in zip(a['records'],b['records']):
 assert all(x.get(k)==y.get(k) for k in ['name','exit','object_sha256','log_sha256','warnings']) and x['exit']==0
 assert {n:v['sha256'] for n,v in x['direct_imports'].items()}=={n:v['sha256'] for n,v in y['direct_imports'].items()}
 for root,row in [(A,x),(B,y)]:
  n=row['name'];add(root/'lib'/(n.replace('.','/')+'.olean'),row['object_sha256']);add(root/'logs'/(n.replace('.','_')+'.log'),row['log_sha256'])
  text=(root/'logs'/(n.replace('.','_')+'.log')).read_text();assert 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text);assert warnings(text)==row['warnings']
  for dep in row['direct_imports'].values():add(dep['resolved_path'],dep['sha256'])
for provider,key in [(Path('/tmp/ipra-adaptive-native-current-qpk97_3z'),'prefix_records'),(Path('/tmp/ipra-adaptive-native-continuation-l58un8d6'),'second_prefix_records'),(Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da'),'third_prefix_records'),(Path('/tmp/ipra-adaptive-native-second-continuation-8ziag05a'),'fourth_prefix_records')]:
 for n,row in f[key].items():
  add(provider/'lib'/(n.replace('.','/')+'.olean'),row['object_sha256']);add(provider/'logs'/(n.replace('.','_')+'.log'),row['log_sha256'])
  for dep in row['direct_imports'].values():add(dep['resolved_path'],dep['sha256'])
excluded={n.replace('.','/')+'.olean' for n in f['affected']}
def expected_inventory(root,state):
 result={rel:{'sha256':v,'resolved_path':str((P/'lib'/rel).resolve())} for rel,v in f['parent_objects'].items() if rel not in excluded}
 for provider,key in [(Path('/tmp/ipra-adaptive-native-current-qpk97_3z'),'prefix_records'),(Path('/tmp/ipra-adaptive-native-continuation-l58un8d6'),'second_prefix_records'),(Path('/tmp/ipra-adaptive-native-warning-continuation-x2wbh2da'),'third_prefix_records'),(Path('/tmp/ipra-adaptive-native-second-continuation-8ziag05a'),'fourth_prefix_records')]:
  for n,row in f[key].items():
   rel=n.replace('.','/')+'.olean';result[rel]={'sha256':row['object_sha256'],'resolved_path':str((provider/'lib'/rel).resolve())}
 for row in state['records']:
  rel=row['name'].replace('.','/')+'.olean';out=root/'lib'/rel;assert out.is_file() and not out.is_symlink() and out.resolve()==out.absolute();result[rel]={'sha256':row['object_sha256'],'resolved_path':str(out.absolute())}
 return result
def actual_inventory(root):
 result={}
 for d,_,fs in __import__('os').walk(root/'lib',followlinks=True):
  for name in fs:
   if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
    p=Path(d)/name;result[str(p.relative_to(root/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return result
expected_a=expected_inventory(A,a);expected_b=expected_inventory(B,b)
def audit():
 assert h(F)==fh and h(DR)==dh and h(__file__)==ch and h(A/'state.json')==ah and h(B/'state.json')==bh
 assert all(h(path)==v for path,v in files.items())
 assert actual_inventory(A)==expected_a and actual_inventory(B)==expected_b
 assert all(str((PKG/rel).resolve())==v['resolved_path'] for rel,v in f['external_direct'].items())
audit()
for root,label in [(A,'author'),(B,'independent')]:
 dest=D/(label+'-logs');dest.mkdir(exist_ok=True);shutil.copyfile(root/'state.json',D/(label+'-state.json'))
 for r in a['records']:
  name=r['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/name,dest/name)
for root,label,expected in [(A,'author',ah),(B,'independent',bh)]:
 assert h(D/(label+'-state.json'))==expected
 for r in a['records']:
  assert h(D/(label+'-logs')/(r['name'].replace('.','_')+'.log'))==r['log_sha256']
log=(A/'logs/DiophantineConsistency_IPRAAdaptiveNativeZFCChecks.log').read_text();blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',log);assert len(blocks)==2 and all(set(x.strip() for x in v.split(','))=={'propext','Classical.choice','Quot.sound'} for v in blocks)
audit();result={'status':'MATCHED_PASS','author_path':str(A),'peer_path':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,'manifest_sha256':fh,'driver_sha256':dh,'compare_sha256':ch,'rows':len(a['records']),'matched_rows':[{'name':r['name'],'object_sha256':r['object_sha256'],'log_sha256':r['log_sha256'],'warnings':r['warnings']} for r in a['records']],'guarded_file_count':len(files),'workspace_drift':{'author_before':a['workspace_drift_before'],'author_after':a['workspace_drift_after'],'peer_before':b['workspace_drift_before'],'peer_after':b['workspace_drift_after']},'boundary':'Historical fixed snapshot; known project-origin mismatch remains independently documented; 848 ancestor author-only and package-transitive/dynamic ancestry inherited.'};(D/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print('MATCHED_PASS',len(a['records']),'rows',len(files),'files')
