#!/usr/bin/env python3
"""No-Lean, point-in-time review of proposed 22-module marked suffix."""
import hashlib,json,os,pathlib,re,subprocess,sys,tempfile
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated non-optimized Python required')
P=pathlib.Path;root=P.cwd();b=root/'Computability/DiophantineConsistency';research=b/'research/ordinary12-ipra-bridge';p=research/'compact44-marked-suffix-source-plan';prior=research/'compact44-graph-marked-join-plan';aud=b/'reviews/compact44-wang-chunk-author-artifact-independent-audit';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest()
assert H(p/'scan.py')=='5518eab1c4844af1c27318a15a2974572f702ad31810809d0c6db5aaaf2e0c6d' and H(p/'source-scan.json')=='1aca547836bef23a058e5714dbaf33bd86666f931e3e872319efc73d6e78a880'
priorpins={'source-scan.json':('3e57c2c7d1','2aeb7400ef18c7cd4bc0c74b1ca09b53e0c685f6054e99d92617f3af9bab7cc6'),'busybeaver-source-scan.json':('64706f743b','abe89bf1cf589a8146771707d322c663012e03e63a7e4e605df486b808f19846')}
for name,(commit,sha) in priorpins.items():
 f=prior/name;assert H(f)==sha;blob=subprocess.run(['git','show',commit+':'+str(f.relative_to(root))],capture_output=True,check=True,timeout=60).stdout;assert hashlib.sha256(blob).hexdigest()==sha
j=json.loads((p/'source-scan.json').read_bytes());rows=j['sources'];assert j['status']=='PASS_SOURCE_ONLY_SUFFIX_SCAN' and len(rows)==22 and len(j['direct_candidates'])==26 and len(j['target_slots'])==440 and not j['unresolved'] and not j['conflicting_direct_objects'] and not j['target_collisions']
assert H(aud/'CHECK.json')=='59dd1eefe5fc2d46bbb0ca7b2d83e14bcc1de9b692da98e94c5598f17678945e' and H(aud/'audit.py')=='a48b7684dc27fff4705419d30fbf14a62fb99f9ac302edcd79b1d508bccbcda1' and H(aud/'terminal-observation.json')=='af62d28207cca0c6d6163b4f46731919031600bd69d5efddc1a41dbe509e6b9a'
r=subprocess.run([sys.executable,'-I','-S','-B',str(aud/'audit.py')],cwd=root,capture_output=True,timeout=600);assert r.returncode==0 and not r.stderr and json.loads(r.stdout)==json.loads((aud/'CHECK.json').read_bytes())
with tempfile.TemporaryDirectory(prefix='marked-suffix-review-') as tmp:
 out=P(tmp)/'scan.json';q=subprocess.run([sys.executable,'-I','-S','-B',str(p/'scan.py'),'--output',str(out)],cwd=root,capture_output=True,timeout=120);assert q.returncode==0 and not q.stderr and out.read_bytes()==(p/'source-scan.json').read_bytes();opt=P(tmp)/'optimized.json';z=subprocess.run([sys.executable,'-O','-I','-S','-B',str(p/'scan.py'),'--output',str(opt)],cwd=root,capture_output=True,timeout=120);assert z.returncode==1 and b'optimized Python rejected' in z.stderr and not opt.exists()
old=json.loads((prior/'busybeaver-source-scan.json').read_bytes())['ordered_sources']+json.loads((prior/'source-scan.json').read_bytes())['ordered_sources'];assert len(old)==100
expected=[r['module'] if '.' in r['module'] else 'DiophantineConsistency.'+r['module'] for r in old[82:]]+['DiophantineConsistency.CompactLocalWord','DiophantineConsistency.OldWordIdentification','DiophantineConsistency.FixedGraphMarkedHalt','DiophantineConsistency.MarkedSuffixInventory'];assert [r['module'] for r in rows]==expected
indices={x['module']:i for i,x in enumerate(rows)};assert len(indices)==22;direct=set();source_rows=[]
for x,row in zip(old[82:],rows[:18]):assert P(row['source'])==root/x['source'] and row['sha256']==x['sha256']
for i,x in enumerate(rows):
 f=P(x['source']);raw=f.read_bytes();imps=re.findall(r'^import\s+([\w.]+)',raw.decode(),re.M);assert H(f)==x['sha256'] and imps==x['imports'];assert all(len(line.split())==2 for line in raw.decode().splitlines() if line.startswith('import '));blob=subprocess.run(['git','show','b3f96a5c9e:'+str(f.relative_to(root))],capture_output=True,check=True,timeout=60).stdout;assert hashlib.sha256(blob).hexdigest()==x['sha256']
 for d in ['Init']+imps:
  if d in indices:assert indices[d]<i,(x['module'],d)
  else:direct.add(d)
 source_rows.append({'module':x['module'],'source':str(f.relative_to(root)),'sha256':x['sha256'],'imports':imps})
assert direct==set(j['direct_candidates'])
def checkslots(items):
 for n,v in items.items():
  f=P(n)
  if v is None:assert not os.path.lexists(f),n
  else:assert f.is_file() and str(f.resolve(strict=True))==v['realpath'] and H(f)==v['sha256'],n
checkslots(j['target_slots']);assert all(v is None for v in j['target_slots'].values())
count=0;roots={};
for dep,record in j['direct_candidates'].items():
 cs=record['candidates'];assert len(cs)==2
 for c in cs:
  assert len(c['slots'])==10;checkslots(c['slots']);count+=len(c['slots'])
 present=[c for c in cs if c['object'] is not None];assert present and record['chosen_root']==present[0]['root'] and len({c['object']['sha256'] for c in present})==1
 for c in cs:
  roots[(c['root'],c['object'] is not None)]=roots.get((c['root'],c['object'] is not None),0)+1
assert count==520
client=(p/'MarkedSuffixInventory-DRAFT.lean').read_text();prints=re.findall(r'^#print axioms\s+([\w.]+)\s*$',client,re.M);assert len(prints)==len(set(prints))==16
halt=(p/'FixedGraphMarkedHalt-DRAFT.lean').read_text();sound=(b/'Lean/DiophantineConsistency/ArithmeticWangSoundness.lean').read_text();assert 'first (ArithmeticMachineRun215.run t)=0' in halt and 'theorem marked_halts : ∃ t < N, first (run t) = 0' in sound and 'ArithmeticWangSoundness.marked_halts hm.2' in halt
print(json.dumps({'status':'PASS_NO_LEAN_MARKED_SUFFIX_SOURCE_REVIEW','reviewed_commit':'b3f96a5c9e','scan_sha256':H(p/'source-scan.json'),'prior_scan_pins':{k:v[1] for k,v in priorpins.items()},'parent_audit_rerun_exit':r.returncode,'author_scan_rerun_exit':q.returncode,'optimized_scan_exit':z.returncode,'sources':source_rows,'source_count':len(rows),'direct_modules':len(direct),'candidate_roots':52,'candidate_slots':count,'target_slots':len(j['target_slots']),'provider_slot_counts':{str(k):v for k,v in roots.items()},'inventory_requested_reports':prints,'lean_launched':False,'scope':'Source and point-in-time provider artifact review only; draft uncompiled, no Lean dependency query, transitive authentication, paired build or internal PRA theorem.'},indent=2,sort_keys=True))
