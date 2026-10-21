#!/usr/bin/env python3
"""Owned replay of exact feedback215 bytes, startup, and universal runtime."""
import os,sys
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise SystemExit('Run without -O, -OO, or PYTHONOPTIMIZE.')
from pathlib import Path
import argparse,hashlib,json,subprocess,time
R=Path(__file__).resolve().parent
sys.path.insert(0,str(R/'checks'))
import independent_runtime as I
import check_fixed_certificate as C
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--runtime',action='store_true');ap.add_argument('--work',type=Path,required=True);a=ap.parse_args();W=a.work.resolve()
if W==R or R in W.parents:raise SystemExit('Work directory must be outside the package.')
W.mkdir(parents=True,exist_ok=True)
if any(W.iterdir()):raise SystemExit('Use an empty work directory.')
start=time.monotonic();report={}
if (R/'MANIFEST.json').exists():
 for item in json.loads((R/'MANIFEST.json').read_text())['files']:
  p=R/item['path'];assert p.stat().st_size==item['bytes'] and H(p)==item['sha256'],item['path']
 report['manifest']='PASS'
T=I.table(R/'machine/feedback215.native.tm');K=I.table(R/'machine/feedback215.tm')
assert len(T)==430 and len({q for q,b in T})==215
M={int(k):v for k,v in json.loads((R/'machine/native_to_canonical.json').read_text()).items()}
assert M[74]==0 and M[254]==215 and K=={(M[q],b):(w,d,M[z])for(q,b),(w,d,z)in T.items()}
assert set(q for q,b in K)==set(range(215)) and all((q,b)in K for q in range(215)for b in(0,1))
reach={0};todo=[0]
for q in todo:
 for b in(0,1):
  z=K[q,b][2]
  if z!=215 and z not in reach:reach.add(z);todo.append(z)
assert reach==set(range(215));report['machine']={'states':215,'rows':430,'start':0,'halt':215,'graph_reachable':215,'native_sha256':H(R/'machine/feedback215.native.tm'),'canonical_sha256':H(R/'machine/feedback215.tm')}
subprocess.run([sys.executable,'-B',str(R/'checks/check_startup.py')],check=True,stdout=(W/'startup.log').open('w'))
f=json.loads((R/'evidence/STARTUP.json').read_text());q=0;h=0;ones=set()
for _ in range(f['blank_steps']):
 w,d,q=K[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
assert q==M[84] and h==f['head'] and sorted(ones)==f['ones']
report['startup']='PASS: independent source bridge, dense/native, sparse/native, canonical whole tape'
subprocess.run([sys.executable,'-B',str(R/'checks/check_return_target.py')],check=True,stdout=(W/'return_target.log').open('w'))
report['return_target_error']='CONFIRMED: CC3 targets selector23, not scheduler0'
subprocess.run([sys.executable,'-B',str(R/'checks/check_source_binding.py'),'--source',str(R/'machine/source.sites.json'),'--parent',str(R/'inputs/composite_transfer.sites.json'),'--output',str(W/'source_binding.json')],check=True,stdout=(W/'source_binding.log').open('w'))
report['source_macro_and_halting_suffix']='CONFIRMED: inherited AX and exact 2*T+15 post-AX halt'
cert=C.verify(C.read_json(R/'inputs/dominated_rho8_full_certificate.json'),True)[0]
report['inherited_dominated_certificate']=cert
if (R/'checks/check_feedback.py').exists():
 subprocess.run([sys.executable,'-B',str(R/'checks/check_feedback.py'),'--out',str(W/'feedback.json')],check=True,stdout=(W/'feedback.log').open('w'))
 report['feedback_checks']='PASS'
subprocess.run([sys.executable,'-B',str(R/'checks/check_density.py'),'--out',str(W/'density.json')],check=True,stdout=(W/'density.log').open('w'))
report['finite_density_base']='PASS'
subprocess.run([sys.executable,'-B',str(R/'physical_search/source200/verify.py')],check=True,stdout=(W/'source200.log').open('w'))
subprocess.run([sys.executable,'-B',str(R/'physical_search/folds/verify_contexts.py')],check=True,stdout=(W/'contexts.log').open('w'))
report['source200_and_context_certificates']='PASS'
raw=[]
for name in ['stack_0_0_mpfirst','stack_0_0_sfirst']:
 rt=I.table(R/'formalism'/(name+'.native.tm')); assert len(rt)==434 and len({q for q,b in rt})==217
 raw.append({'name':name,'raw_states':217,'status':'UNVERIFIED_ALLOCATION_ONLY'})
report['stack_output_raw_allocations']=raw
CT=I.table(R/'companion217/global217.native.tm');CK=I.table(R/'companion217/global217.tm')
CM={int(q):z for q,z in json.loads((R/'companion217/native_to_canonical.json').read_text()).items()}
assert len(CT)==434 and CM[74]==0 and CM[254]==217 and CK=={(CM[q],b):(w,d,CM[z])for(q,b),(w,d,z)in CT.items()}
assert set(q for q,b in CK)==set(range(217))
subprocess.run([sys.executable,'-B',str(R/'checks/check_companion_startup.py')],check=True,stdout=(W/'companion_startup.log').open('w'))
f=json.loads((R/'companion217/STARTUP.json').read_text());q=0;h=0;ones=set()
for _ in range(f['blank_steps']):
 w,d,q=CK[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
assert q==CM[84] and h==f['head'] and sorted(ones)==f['ones']
subprocess.run([sys.executable,'-B',str(R/'checks/check_companion_source.py'),'--old',str(R/'companion217/context-root.reference.sites.json'),'--baseline',str(R/'inputs/composite_transfer.sites.json'),'--new',str(R/'companion217/source.sites.json'),'--output',str(W/'companion_source.json')],check=True,stdout=(W/'companion_source.log').open('w'))
report['corrected_companion217']={'states':217,'startup':'PASS','canonical_mapping':'PASS','source_binding':'PASS: complete literal CFG, unchanged macro identities and exact common footer','target_met':False}
if a.runtime:
 import symbolic_runtime as S
 mapping={int(q):int(z)for q,z in json.loads((R/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()}
 for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
  if q not in mapping:mapping[q]=max(mapping.values())+1
 U={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()}
 lemmas,blocks=S.prove_blocks(U);sites=json.loads((R/'machine/source.sites.json').read_text());cases=[];rows=set()
 for i,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   c=S.case(U,lemmas,site,positive,append=0);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=positive,**c))
  if i%500==0:print('proved',len(cases),flush=True)
 assert json.loads(json.dumps(cases))==json.loads((R/'evidence/SCRATCH_RUNTIME_CASES.json').read_text())
 assert len(cases)==6152 and len(rows)==430 and sum(c['symbolic_steps']for c in cases)==1617669 and min(c['duration'][0]for c in cases)==6
 report['runtime']={'status':'ALL_NATURAL_RUNTIME_PASS','cases':len(cases),'symbolic_rules':1617669,'row_coverage':len(rows),'minimum_duration':6,'append_spare_value':0}
 (W/'runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
if a.runtime:
 mapping={int(q):int(z)for q,z in json.loads((R/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()}
 for q in sorted({q for q,b in CT}|{z for w,d,z in CT.values()}):
  if q not in mapping:mapping[q]=max(mapping.values())+1
 U={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in CT.items()}
 lemmas,blocks=S.prove_blocks(U);sites=json.loads((R/'companion217/source.sites.json').read_text());cases=[];rows=set()
 for i,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   c=S.case(U,lemmas,site,positive,append=0);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=positive,**c))
  if i%500==0:print('companion proved',len(cases),flush=True)
 assert json.loads(json.dumps(cases))==json.loads((R/'companion217/RUNTIME_CASES.json').read_text())
 assert len(cases)==6153 and len(rows)==434 and sum(c['symbolic_steps']for c in cases)==1618212 and min(c['duration'][0]for c in cases)==8
 report['corrected_companion217']['runtime']={'status':'ALL_NATURAL_RUNTIME_PASS','cases':6153,'symbolic_rules':1618212,'row_coverage':434,'minimum_duration':8}
 (W/'companion_runtime_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
report.update(status='LISTED_CHECKS_PASS',experiment215_status='REJECTED: unconditional post-AX halt from wrong source return',companion217_status='CALIBRATED_BY_INCLUDED_WRITTEN_PROOFS_PLUS_RUNTIME_AND_STARTUP',target_met=False,runtime_requested=a.runtime,seconds=time.monotonic()-start)
(W/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
