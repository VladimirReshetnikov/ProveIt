#!/usr/bin/env python3
"""Check seed/static iff source and recorded direct producers; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-seed-static-iff-check';B=D/'research/nine-sharing-norm38-slots-batched-retry01';BASE=Path('/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for p,h in [(P/'run.py','0cf443dd29de95ee7690fbeb757a919c92b7fe2b062e56f02009ad8fa84a1146'),(P/'source-manifest.json','438be22e558c613b101e40b3b1d93c7ba6dba5eb7e4890559fd1bfdc32e9ca1c'),(P/'src/DiophantineConsistency/Norm38SeedStaticIff.lean','4e50939e858e2d8e6f6ad8d5726e993c14a098d070f9002095345cd02e7cc3de'),(B/'attempt01/state.json','5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc')]:need(sha(p)==h,'pin '+str(p))
s=(P/'src/DiophantineConsistency/Norm38SeedStaticIff.lean').read_text();need('InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) ↔' in s and 'NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w' in s and '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in s,'same valuation and casts');need('Norm38GateExtraction.seed_zero_gatesHold p ports w hp hz' in s and 'Norm38SlotExtraction.seed_zero_fiveNorms p ports w hp hz' in s and 'Norm38Forward.static_implies_seed_zero p ports w hp hg hn' in s,'composition orientation');m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==1 and m[0]['source_sha256']==sha(root/m[0]['source']) and m[0]['imports']==re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M) and len(m[0]['imports'])==3,'manifest')
b=json.loads((B/'attempt01/state.json').read_text());need(b['status']=='FAILED' and len(b['rows'])==12 and b['rows'][-1]['compile']['stop_reason']=='timeout','partial slots state');prod=[(Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105'),B/'attempt01',r) for r in b['rows'][1:11]]
for packet,tmp,pin in [('nine-sharing-norm38-each-slot-retry01','/tmp/nine-sharing-norm38-each-slot-retry01-20261105','8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70'),('nine-sharing-norm38-gates-assembly-retry','/tmp/nine-sharing-norm38-gates-assembly-retry-20261105','1ca0968a7e2acfbd398302581e30f3c02caebcf2a4c81081ba73e0b913ea8b72'),('nine-sharing-norm38-five-norms-check-v2','/tmp/nine-sharing-norm38-five-norms-check-v2-20261105','a16e6c80cd1f713b0ec2e863b800847a80265e86643f757ae146c1f1c9656140'),('nine-sharing-norm38-static-to-seed-retry01','/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105','ae9f8310391bea63f5d591966b81284846bbf0f526c1da00c8a4225fb56c0b74')]:
 q=D/'research'/packet/'attempt01';need(sha(q/'state.json')==pin==sha(Path(tmp)/'state.json'),'state '+packet);v=json.loads((q/'state.json').read_text());need(v['status']=='PASS' and len(v['rows'])==1,'success '+packet);prod.append((Path(tmp),q,v['rows'][0]))
guards=0
for temp,records,row in prod:
 n=row['module'];need(row['deps']['exit']==row['compile']['exit']==0 and all(row[k]['stop_reason'] is None and not row[k]['monitor_errors'] and not row[k]['observed_descendant_pids'] for k in ('deps','compile')),'producer exit '+n);need(sha(temp/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256'] and sha(temp/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'source/object '+n)
 for typ in ('deps','compile'):need(sha(temp/(n+'-'+typ+'.txt'))==sha(records/(n+'-'+typ+'.txt'))==row[typ]['log_sha256'],'log '+n+typ)
 for path,v in row['direct_guard'].items():
  guards+=1;q=Path(path)
  if v is None:need(not os.path.lexists(q),'absence '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'guard '+path)
 if temp!=BASE:
  q=BASE/'lib/DiophantineConsistency'/(n+'.olean');need(q.is_symlink() and q.resolve()==(temp/'lib/DiophantineConsistency'/(n+'.olean')).resolve(),'route '+n)
static=json.loads((BASE/'state.json').read_text());
for path,target in static['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
need(not os.path.lexists(BASE/'lib/DiophantineConsistency/Norm38SeedStaticIff.olean'),'target shadow');q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=60);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT','preflight '+q.stderr)
print(json.dumps({'status':'PASS_SCOPED_PRELAUNCH_REVIEW','producer_records':len(prod),'direct_guard_slots':guards,'overlay_links':len(static['overlay_links']),'preflight_exit':q.returncode,'scope':'Same-valuation theorem source and recorded producer point checks only; no Lean or current-equation equivalence.'},indent=2,sort_keys=True))
