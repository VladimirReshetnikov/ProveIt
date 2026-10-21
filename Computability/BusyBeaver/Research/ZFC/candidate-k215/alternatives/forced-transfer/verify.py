#!/usr/bin/env python3
"""Owned portable checks. Written calibration proofs remain explicit dependencies."""
import os,sys
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):raise SystemExit('Run with assertions enabled.')
from pathlib import Path
import argparse,json,hashlib,subprocess,time
R=Path(__file__).resolve().parent;sys.path.insert(0,str(R/'checks'))
import independent_runtime as I
from source_graph import guarded_graph
import check_fixed_certificate as C
ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--runtime',action='store_true');a=ap.parse_args();W=a.work.resolve()
if W==R or R in W.parents:raise SystemExit('Output directory must be outside packet.')
W.mkdir(parents=True,exist_ok=True)
if any(W.iterdir()):raise SystemExit('Use an empty output directory.')
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();start=time.monotonic();results={}
if (R/'MANIFEST.json').exists():
 for x in json.loads((R/'MANIFEST.json').read_text())['files']:
  p=R/x['path'];assert p.stat().st_size==x['bytes'] and H(p)==x['sha256'],x['path']
 results['manifest']='PASS'
for name,old,checker in [('forced215','st215.reference.sites.json','check_forced_source.py'),('cache216','st215.reference.sites.json','check_cache_source.py'),('composite216','composite_transfer.sites.json','check_composite_source.py')]:
 D=R/name;receipt=json.loads((D/'RUNTIME.json').read_text());T=I.table(D/'machine.native.tm');K=I.table(D/'machine.tm');sites=json.loads((D/'source.sites.json').read_text())
 assert H(D/'machine.native.tm')==receipt['table_sha256'] and H(D/'source.sites.json')==receipt['source_sha256']
 assert H(D/'RUNTIME_CASES.json')==receipt['cases_sha256']
 M={int(q):z for q,z in json.loads((D/'native_to_canonical.json').read_text()).items()};states=receipt['working_states'];assert M[0]==0 and M[254]==states
 assert len(T)==2*states and K=={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in T.items()}
 assert {q for q,b in K}==set(range(states)) and all((q,b)in K for q in range(states)for b in (0,1))
 seen={0};todo=[0]
 for q in todo:
  for b in (0,1):
   z=K[q,b][2]
   if z!=states and z not in seen:seen.add(z);todo.append(z)
 assert len(seen)==states
 # Three independent whole-tape runs: native sparse, native dense, canonical sparse.
 f=json.loads((D/'STARTS.json').read_text())[0];assert f['start']==0 and f['steps']==70506 and f['ordinal']==(59 if name=='forced215' else 58)
 q=qd=qk=0;h=hd=hk=0;ones=set();ks=set();lo=-20000;dense=bytearray(40001)
 for tick in range(f['steps']):
  w,d,q=T[q,int(h in ones)];wd,dd,qd=T[qd,dense[hd-lo]];wk,dk,qk=K[qk,int(hk in ks)]
  assert (w,d,q)==(wd,dd,qd) and (wk,dk,qk)==(w,d,M[q])
  if w:ones.add(h);ks.add(hk)
  else:ones.discard(h);ks.discard(hk)
  dense[hd-lo]=wd;h+=d;hd+=dd;hk+=dk
 assert q==84 and qk==M[84] and h==hd==hk==f['head'] and sorted(ones)==f['ones']
 assert ones==ks=={i+lo for i,b in enumerate(dense)if b}
 # Independent exact source prefix from partial initial AX.
 G=guarded_graph(sites);v=[1,0,2,0,0,0,0,0,0];j=(26 if name=='forced215' else 25);trace=[]
 for _ in range(177):
  trace.append([j,v.copy()]);op=G[j]
  if op[0]=='CI':v[op[1]]+=1;j=op[2]
  elif op[0]=='CD':b=bool(v[op[1]]);v[op[1]]-=int(b);j=op[3 if b else 2]
  elif op[0]=='CONTROL':j=op[1]
  else:raise AssertionError(op)
 assert j==f['ordinal'] and v==f['registers'] and sites[j][0]==f['pc']
 # Decode the complete frame and reconstruct its exact finite support.
 physical=[None]*9
 for i,z in enumerate((6,2,0,4,3,7,8,5,1)):physical[z]=v[i]
 regs=physical+f['spares'];expected={h-1,h+64+f['gap']}|{h+i for i,b in enumerate(sites[j][0])if b=='1'};p=h+65+f['gap']
 for x in regs:expected.update(range(p+1,p+x+2));p+=x+2
 assert expected==ones and len(f['spares'])==63
 (W/(name+'_startup.json')).write_text(json.dumps(dict(status='PASS',source_steps=177,source_trace=trace,frame=f,table_sha256=H(D/'machine.native.tm')),indent=2)+'\n')
 subprocess.run([sys.executable,'-B',str(R/'checks'/checker),'--old',str(R/'inputs'/old),'--new',str(D/'source.sites.json'),'--output',str(W/(name+'_source.json'))],check=True,stdout=(W/(name+'_source.log')).open('w'))
 item=dict(states=states,rows=2*states,graph_reachable=states,native_sha256=H(D/'machine.native.tm'),canonical_sha256=H(D/'machine.tm'),source_sha256=H(D/'source.sites.json'),startup='PASS: dense, sparse, canonical, exact source bridge',source_binding='PASS')
 if a.runtime:
  import symbolic_runtime as S
  mapping={int(q):z for q,z in json.loads((R/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()}
  for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
   if q not in mapping:mapping[q]=max(mapping.values())+1
  U={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()};lemmas,blocks=S.prove_blocks(U);cases=[];rows=set()
  for i,site in enumerate(sites):
   for positive in ((False,True)if site[1]=='CD'else(False,)):
    c=S.case(U,lemmas,site,positive,append=0);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=positive,**c))
   if i%500==0:print(name,'proved',len(cases),flush=True)
  assert json.loads(json.dumps(cases))==json.loads((D/'RUNTIME_CASES.json').read_text())
  assert len(cases)==receipt['cases'] and len(rows)==receipt['row_coverage']==2*states
  assert sum(c['symbolic_steps']for c in cases)==receipt['symbolic_rules'] and min(c['duration'][0]for c in cases)==receipt['minimum_duration']
  item['runtime']={k:receipt[k] for k in ['cases','symbolic_rules','row_coverage','minimum_duration']};item['runtime']['status']='ALL_NATURAL_RUNTIME_PASS'
  (W/(name+'_cases.json')).write_text(json.dumps(cases,indent=2)+'\n')
 results[name]=item
results['dominated_certificate']=C.verify(C.read_json(R/'inputs/dominated_rho8_full_certificate.json'),True)[0]
for check in ['check_constant_credit.py','check_automatic_credit.py','check_forced_credit.py']:
 subprocess.run([sys.executable,'-B',str(R/'checks'/check),'--out',str(W/check.removesuffix('.py'))],check=True,stdout=(W/(check+'.log')).open('w'))
for generated,archived in [('check_constant_credit/DENSITY_CREDIT_BASE.json','CONSTANT_DENSITY_BASE.json'),('check_constant_credit/ODD_SCHEDULE_BASE.json','CONSTANT_ODD_BASE.json'),('check_automatic_credit/AUTOMATIC_CREDIT.json','AUTOMATIC_CREDIT.json'),('check_forced_credit/FORCED_TRANSFER_CREDIT_BASE.json','FORCED_TRANSFER_CREDIT_BASE.json')]:
 assert json.loads((W/generated).read_text())==json.loads((R/'evidence'/archived).read_text()),generated
subprocess.run([sys.executable,'-B',str(R/'checks/check_distinctness.py'),'--output',str(W/'distinctness.json')],check=True,stdout=(W/'distinctness.log').open('w'))
results['credit_bases_and_finite_distinctness']='PASS'
results.update(status='LISTED_CHECKS_PASS',target_met=True,result='Materially different FT215; no 214-state result',scope='FT215 and two 216 companions, relying also on included written logical/compiler/credit proofs. No exact-table Lean/Rocq endpoint.',runtime_requested=a.runtime,seconds=time.monotonic()-start)
(W/'verification.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
