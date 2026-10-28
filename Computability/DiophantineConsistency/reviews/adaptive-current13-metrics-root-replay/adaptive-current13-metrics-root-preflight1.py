from pathlib import Path
from collections import Counter
import gzip,hashlib,json,os,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';B=D/'research/adaptive-current13-metrics'
obs=[]
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p);return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
def check(x):
 p=Path(x['path']);p=p if p.is_absolute() else D/p;a=rec(p)
 need(a['sha256']==x['sha256'],'hash '+str(p))
 if 'bytes'in x:need(a['bytes']==x['bytes'],'size '+str(p))
 obs.append(a)
def load(p):return json.loads(Path(p).read_text())
def nested(o):
 if isinstance(o,dict):
  if 'path'in o and 'sha256'in o:yield o
  for v in o.values():yield from nested(v)
 elif isinstance(o,list):
  for v in o:yield from nested(v)
def save(p,o):Path(p).write_text(json.dumps(o,indent=2)+'\n')
for n,h in [('audit.py','50eca7f5fba298afc0057d42dace191828703e193f34493c34ce651971bd606f'),('FILES.json','5e7551a72fc80966267071cfe81f477abeb8bd07e142d23aa62e7ba1feab0e93'),('REPLAY.json','eb99c3e009d9e3e0af37c0efa75b80f159ec2a682dca49cbfdd3e5b51614c613'),('CERTIFICATE.json','d25fba7eeca7081c3ebb3532eede3e9d96c6252a4b083f713f3dfe75a772e9df')]:check(dict(path=str(B/n),sha256=h))
check(dict(path=str(D/'reviews/adaptive-current13-metrics-author.md'),sha256='4c8640d3efd8a8090c6b82043e02277bbba5365fa4d5858c78e5393811308430'))
manifest=load(B/'FILES.json');need(len(manifest)==55,'55 frozen files')
for r in manifest:check(r)
for name in ['INPUTS.json','SUPPLEMENT.json','REPLAY.json']:
 for r in nested(load(B/name)):check(r)
author=load(B/'REPLAY.json');need(author['status']=='AUTHOR_PASS' and author['failed_attempts']==0 and len(author['runs'])==4,'author history')
endpoint=load(D/'reviews/native-adaptive-current2011-peer-replay.json')
for r in endpoint['records']:
 for k in ['source','object','log']:check(r[k])
g=load(B/'polynomial.json');c=load(B/'CERTIFICATE.json');names=g['witnesses'];ports=g['fixed_numerals'];symbols=names+ports
need(len(names)==13 and len(g['source'])==88 and Counter(row[1] for row in g['source'])=={'+':23,'-':17,'*':48},'paid gates')
live=set();rows={row[0]:row for row in g['source']}
def reach(n):
 if type(n)is int or n in live:return
 live.add(n)
 if n in rows:
  for arg in rows[n][2:]:reach(arg)
reach(g['output']);need(live==set(rows)|set(symbols),'complete liveness')
values={}
for n in ports:
 entry=g['coefficient_binding']['ports'][n]
 raw=gzip.decompress((B/'coefficients'/entry['file']).read_bytes())
 need(len(raw)==entry['raw_bytes'] and hashlib.sha256(raw).hexdigest()==entry['raw_sha256'],'whole raw port')
 values[n]=int.from_bytes(raw,'big')
need(values['beta']==(1<<94517)-1 and sum(g['coefficient_binding']['ports'][n]['raw_bytes'] for n in ports)==47313,'actual beta/size')
leaders=c['degree']['all_gate_leaders'];need(set(leaders)==set(rows),'all88 leaders')
for n,row in leaders.items():
 formal=row['complete_formal_leader'];need(formal and all(len(m)==17 and sum(m[:13])==row['degree'] for m,a in formal),'homogeneous '+n)
 witness=row['specialized_nonzero'];mod=witness['modulus'];actual={}
 for m,a in formal:
  z=a
  for i,p in enumerate(ports):z=z*pow(values[p],m[13+i],mod)%mod
  key=tuple(m[:13]);actual[key]=(actual.get(key,0)+z)%mod
 actual={m:a for m,a in actual.items() if a}
 stored={tuple(m):a for m,a in witness['full_specialized_leader_modulus']}
 need(actual==stored and actual.get(tuple(witness['unknown_monomial']))==witness['coefficient']!=0,'complete exact specialization '+n)
out=c['degree']['complete_output_leader'];need(len(out)==232 and out==leaders[g['output']]['complete_formal_leader'],'entire leader')
selected=c['degree']['selected_unknown_monomial'];mon=tuple(selected.get(n,0) for n in names)
coefficient={tuple(m[13:]):a for m,a in out if tuple(m[:13])==mon}
need(sum(mon)==51 and coefficient=={(15,0,0,0):-32},'exact surviving coefficient')
need(c['degree']['factor_degrees']=={'F0':15,'F1':13,'Fa':13,'Fs':10},'complete factor degrees')
t=c['table_data'];labels=[0]+list(range(1,431))+[431,432,433,434]
for d in [1,0]:
 for q in t['target_lists'][d]:
  for b in [0,1]:labels.append(423+2*t['rails'][d][q]+b)
labels+=list(range(923,942));need(labels==list(range(942)),'actual orderedRows order equals indexed labels')
coeff=[0]*3297
for i,w in enumerate(t['abstract_weights']):coeff[t['physical_positions'][i]]+=2*w
for start,power,count in [(978,10,8),(960,18,9),(969,27,8),(942,35,9)]:
 for j in range(count):coeff[start+j]+=1<<(power+j+1)
need(coeff==t['all3297_coefficients'],'complete independent coefficient accumulation')
radix=lambda e:1<<(47*e)
K=radix(18)+radix(1004)+radix(2020)+sum(a*radix(1005-i) for i,a in enumerate(coeff) if a)
MC=values['beta']-sum(radix(i) for i in list(range(951))+list(range(960,986))+[1004])
MF=values['beta']+8*sum(radix(i) for i in range(917))-4+((1<<45)-4)*radix(1005)+sum(radix(i) for i in list(range(960,969))+list(range(987,995))+[1004])
need([values[n] for n in ports]==[values['beta'],K,MC,MF],'all complete current integers/once-shifted MF')
need(len(c['rejected_mutations'])==258,'all258 controls')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'initial reserve')
p=Path(tempfile.mkdtemp(prefix='adaptive-current13-metrics-root-'));shutil.copyfile(__file__,p/'driver.py')
state=dict(status='RUNNING',private=str(p),records=[],independent_checks=dict(gates=88,unknowns=13,leaders=88,output_leader_terms=232,degree=51,raw_bytes=47313,actual_table_order=True,whole_current_integers=True),compiler_invocations=0)
save(p/'state.json',state);Path('/tmp/adaptive-current13-metrics-root-latest').write_text(str(p)+'\n')
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
try:
 for mode in ['normal','optimized']:
  need(shutil.disk_usage('/tmp').free>=512*1024**2,'command reserve')
  command=[sys.executable,'-B',*(['-O'] if mode=='optimized' else []),str(B/'audit.py')]
  log=p/(mode+'.log');timing=p/(mode+'.time');start=time.monotonic()
  with log.open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*command],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  record=dict(mode=mode,command=command,exit_code=r.returncode,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing));state['records'].append(record);save(p/'state.json',state)
  need(r.returncode==0,'audit '+mode)
  need(rec(log)['sha256']==author['runs'][-1]['stdout']['sha256'],'complete stdout equality')
  for row in list(obs):check(row)
  print('PASS',mode,round(record['seconds'],3),flush=True)
 need(state['records'][0]['log']['sha256']==state['records'][1]['log']['sha256'],'normal optimized equality')
 state.update(status='PASS',observations=len(obs),distinct_paths=len({r['path'] for r in obs}),free_bytes=shutil.disk_usage('/tmp').free)
 save(p/'observations.json',obs);save(p/'state.json',state);print('PASS',p,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(p/'state.json',state);raise
