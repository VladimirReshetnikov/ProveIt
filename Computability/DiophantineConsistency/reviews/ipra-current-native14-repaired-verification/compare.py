#!/usr/bin/env python3
"""Compare both completed literal 14-variable fixed-source replays."""
from pathlib import Path
import hashlib,json,os,re,shutil,sys
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';M=V/'ipra-current-native14-repaired-replay/manifest.json';DR=M.parent/'replay.py';F=V/'ipra-frozen-repair-plan-v2/manifest.json';BF=V/'ipra-adaptive-native-fixed-continuation/manifest.json';G=V/'ipra-current-native14-frozen-graph/manifest.json';E=V/'ipra-current-native14-frozen-extra/manifest.json';SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';EXTRA=V/'ipra-current-native14-frozen-extra/sources';PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 raw=Path(p).read_bytes();return json.loads(raw),hashlib.sha256(raw).hexdigest()
assert len(sys.argv)==3;A=Path(sys.argv[1]);B=Path(sys.argv[2]);m,mh=read(M);a,ah=read(A/'state.json');b,bh=read(B/'state.json');dh=h(DR);ch=h(__file__);assert a['status']==b['status']=='PASS' and a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256'];assert [r['name'] for r in a['records']]==[r['name'] for r in b['records']]==m['order'];P=Path(m['peer']);AP=Path(m['author']);src=lambda n:(EXTRA if n in m['extra_names'] else SNAP)/(n.replace('.','/')+'.lean')
ORIG=V/'ipra-frozen-repair-plan-v2-verification/receipt.json';CMP=V/'ipra-frozen-repair-v2-verification/receipt.json';AT=CMP.parent/'terminal.json';CMP2=V/'ipra-frozen-repair-v2-verification-fourth/receipt.json';CT=CMP2.parent/'terminal.json';CL=V/'ipra-frozen-repair-plan-v2-closure-audit/receipt.json';SO=V/'ipra-frozen-repair-plan-v2-source-origin-audit/receipt.json';ST=SO.parent/'terminal.json'
files={}
def add(p,v):
 key=str(Path(p));assert key not in files or files[key]==v,(key,files[key],v);files[key]=v
for p,v in [(F,m['frozen_13_manifest_sha256']),(G,m['graph_sha256']),(E,m['extra_manifest_sha256']),(LEAN,m['lean_sha256']),(P/'state.json',m['peer_state_sha256']),(AP/'state.json',m['author_state_sha256']),(m['ancestor_state'],m['ancestor_state_sha256'])]:add(p,v)
for p,v in m['ancestral_manifests'].items():add(p,v)
for p,v in [(BF,m['original_fixed_manifest_sha256']),(M.parent/'prepare.py',m['preparer_sha256']),(ORIG,m['parent_origin_receipt_sha256']),(CMP,m['parent_comparison_receipt_sha256']),(AT,m['parent_comparison_author_terminal_sha256']),(CMP2,m['parent_comparison_peer_receipt_sha256']),(CT,m['parent_comparison_terminal_sha256']),(CL,m['parent_closure_receipt_sha256']),(SO,m['parent_source_origin_receipt_sha256']),(ST,m['parent_source_origin_terminal_sha256'])]:add(p,v)
for p,v in m['parent_origin_guard'].items():add(p,v)
for p,v in m['parent_receipt_checker_guard'].items():add(p,v)
for p,v in m['parent_external_direct_paths'].items():add(p,v)
for n,v in m['source_sha256'].items():add(src(n),v)
for rel,v in m['parent_inventory'].items():assert str((P/'lib'/rel).resolve())==v['resolved_path'];add(P/'lib'/rel,v['sha256'])
for rel,v in m['external_direct'].items():assert str((PKG/rel).resolve())==v['resolved_path'];add(PKG/rel,v['sha256'])

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
  assert set(row['direct_imports'])==set(m['direct_imports'][n])
  for dep,x in row['direct_imports'].items():
   path=root/'lib'/(dep.replace('.','/')+'.olean');assert path.exists() and str(path.resolve())==x['resolved_path'] and h(path)==x['sha256'];add(x['resolved_path'],x['sha256'])
excluded={n.replace('.','/')+s for n in m['order'] for s in ['.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash']}
def expected(root,state):
 result={rel:v for rel,v in m['parent_inventory'].items() if rel not in excluded}
 for r in state['records']:
  rel=r['name'].replace('.','/')+'.olean';p=root/'lib'/rel;assert p.is_file() and not p.is_symlink() and p.resolve()==p.absolute();result[rel]={'sha256':r['object_sha256'],'resolved_path':str(p.absolute())}
 return result
def actual(root):
 result={}
 for d,_,fs in os.walk(root/'lib',followlinks=True):
  for name in fs:
   if name.endswith(('.olean','.olean.private','.olean.server','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean','.ilean.hash')):
    p=Path(d)/name;result[str(p.relative_to(root/'lib'))]={'sha256':h(p),'resolved_path':str(p.resolve())}
 return result
expa=expected(A,a);expb=expected(B,b)
def audit():
 assert h(M)==mh and h(DR)==dh and h(__file__)==ch and h(A/'state.json')==ah and h(B/'state.json')==bh
 assert all(h(path)==v for path,v in files.items());assert all(str((P/'lib'/rel).resolve())==v['resolved_path'] for rel,v in m['parent_inventory'].items());assert all(str((PKG/rel).resolve())==v['resolved_path'] for rel,v in m['external_direct'].items());assert actual(A)==expa and actual(B)==expb
 assert all(str(Path(p).resolve())==v for p,v in m['parent_external_resolved_paths'].items()) and all(not os.path.lexists(p) for p in m['parent_external_absent_paths']) and all(not os.path.lexists(PKG/p) for p in m['parent_external_absent'])
 for root,state in [(A,a),(B,b)]:
  for row in state['records']:
   for dep,x in row['direct_imports'].items():
    path=root/'lib'/(dep.replace('.','/')+'.olean');assert path.exists() and str(path.resolve())==x['resolved_path'] and h(path)==x['sha256']
audit()
for root,label,expected_sha in [(A,'author',ah),(B,'independent',bh)]:
 dest=D/(label+'-logs');dest.mkdir(exist_ok=True);shutil.copyfile(root/'state.json',D/(label+'-state.json'));assert h(D/(label+'-state.json'))==expected_sha
 for r in a['records']:
  name=r['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/name,dest/name);assert h(dest/name)==r['log_sha256']
log=(A/'logs/DiophantineConsistency_IPRACurrentNativeZFCChecks.log').read_text();blocks=re.findall(r'depends on axioms: \[([^\]]*)\]',log);assert len(blocks)==1 and set(x.strip() for x in blocks[0].split(','))=={'propext','Classical.choice','Quot.sound'}
audit();result={'status':'MATCHED_PASS','author_path':str(A),'peer_path':str(B),'author_state_sha256':ah,'peer_state_sha256':bh,'manifest_sha256':mh,'driver_sha256':dh,'compare_sha256':ch,'rows':len(a['records']),'matched_rows':[{'name':r['name'],'object_sha256':r['object_sha256'],'log_sha256':r['log_sha256'],'warnings':r['warnings']} for r in a['records']],'guarded_file_count':len(files),'workspace_drift':{'author_before':a['workspace_drift_before'],'author_after':a['workspace_drift_after'],'peer_before':b['workspace_drift_before'],'peer_after':b['workspace_drift_after']},'boundary':m['boundary']};(D/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print('MATCHED_PASS',len(a['records']),'rows',len(files),'files')
