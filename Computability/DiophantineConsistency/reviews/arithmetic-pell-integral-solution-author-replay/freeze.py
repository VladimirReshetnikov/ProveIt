from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';V=D/'reviews'
B=V/'arithmetic-pell-integral-solution-author-replay';PACK=V/'arithmetic-pell-integral-solution-replay.json'
OBS=[]
def require(x,msg):
 if not x:raise RuntimeError(msg)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def check(expected,actual=None):
 a=rec(actual or expected['path']);require(a['sha256']==expected['sha256'],'hash '+expected['path']);OBS.append(dict(expected=expected,actual=a));return a
def copy(src,dest):
 dest.parent.mkdir(parents=True,exist_ok=True);require(not dest.exists(),'new destination');shutil.copyfile(src,dest);check(rec(src),dest)
paths=[Path(p)for p in Path('/tmp/arithmetic-pell-integral-solution-author-runs.txt').read_text().splitlines()]
require(len(paths)==2,'two attempts');states=[json.loads((p/'state.json').read_text())for p in paths]
require([s['status']for s in states]==['FAILED','PASS'],'chronology')
require(not B.exists()and not PACK.exists(),'new frozen packet');B.mkdir()
for i,(p,s)in enumerate(zip(paths,states),1):
 inp=json.loads((p/'inputs.json').read_text());auth=json.loads((p/'authentication.json').read_text())
 for source in inp['sources']:check(source,p/'logs'/Path(source['path']).name)
 for pin in auth['pins']:
  if pin['path']in [x['path']for x in inp['sources']]:check(pin,p/'logs'/Path(pin['path']).name)
  else:check(pin)
 check(s['inputs']);check(s['driver'],p/'driver.py')
 for row in s['records']:
  for k in ['snapshot','log','timing']:check(row[k])
  if 'object'in row:check(row['object'])
 for name in ['state.json','inputs.json','authentication.json','providers.json','driver.py']:
  copy(p/name,B/f'attempt-{i}'/name)
 for src in sorted((p/'logs').iterdir()):copy(src,B/f'attempt-{i}'/src.name)
final=states[-1];p=paths[-1];inp=json.loads((p/'inputs.json').read_text())
require(inp['counts']==dict(custom=101,Foundation=95,artifacts=386,external=38,boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,fresh_prerequisites=0),'scope')
require(len(final['records'])==2 and len(final['records'][1]['axiom_reports'])==5,'five reports')
for row in final['records']:
 check(row['source']);check(row['object']);require(row['exit_code']==0,'exit')
 require(not re.search(r'\b(?:warning|error|sorryAx)\b',Path(row['log']['path']).read_text()),'clean')
 row['peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',Path(row['timing']['path']).read_text()).group(1))
for _,a in final['records'][1]['axiom_reports']:require(set(x.strip()for x in a.split(','))<={'propext','Classical.choice','Quot.sound'},'axioms')
copy(Path(inp['plan']['path']),B/'plan.json');copy(Path(inp['proposal']['path']),B/'proposal.md');copy(Path(__file__),B/'freeze.py');copy(Path(inp['accepted_supplement']['path']),B/'accepted-strong-divisibility.json')
save(B/'freeze-authentication.json',dict(observations=OBS,count=len(OBS),unique_paths=len({x['actual']['path']for x in OBS})))
manifest=[rec(f)for f in sorted(B.rglob('*'))if f.is_file()]
for f in manifest:f['path']=str(Path(f['path']).relative_to(R))
save(B/'FILES.json',manifest)
packet=dict(status='PASS',author='complemented47_review',scope='Actual positive relaxed norm R=i*c*c with c=ycoord p a and (a+2)*delta(a)^2<c derives the common-unit index multiple before producing positive m, p|m, f=xcoord m a and R=delta(a)*ycoord m a. Additive and justified truncated input endpoints. No supplied common unit/index/coprimality/standard-index premise; no final c|m, cubic congruence or HA endpoint.',counts=inp['counts'],attempts=[dict(private=str(pp),status=ss['status'],state=rec(pp/'state.json'),durable=rec(B/f'attempt-{i}'/'state.json'))for i,(pp,ss)in enumerate(zip(paths,states),1)],records=final['records'],private_provider=str(p/'lib'),final_state=rec(p/'state.json'),plan=inp['plan'],scope_supplement=inp['proposal'],inputs=rec(p/'inputs.json'),providers=rec(p/'providers.json'),authentication=rec(p/'authentication.json'),freeze_authentication=rec(B/'freeze-authentication.json'),manifest=rec(B/'FILES.json'),driver=final['driver'],compiler=inp['compiler'],LEAN_PATH=inp['LEAN_PATH'],boundary_artifacts=114,boundary_primaries=38,boundary_companions=76,first_provider_artifacts=500,accepted_strong_supplement=inp['accepted_supplement'],final_observed_paths=final['final_observed_paths'],final_free_bytes=final['final_free_bytes'],failed_attempts=1,history='Attempt1 failed only when simp did not convert internal 1+1 to2 in the proper-divisor quotient lower bound. Attempt2 adds explicit one_add_one_eq_two, then main and Checks pass cleanly. No statements/imports/caps changed. Both complete source/driver/input snapshots and logs, including unused Checks, are preserved.')
save(PACK,packet)
print(json.dumps(dict(packet=rec(PACK),manifest=rec(B/'FILES.json'),files=len(manifest),freeze_observations=len(OBS),freeze_paths=len({x['actual']['path']for x in OBS}),records=final['records']),indent=2))
