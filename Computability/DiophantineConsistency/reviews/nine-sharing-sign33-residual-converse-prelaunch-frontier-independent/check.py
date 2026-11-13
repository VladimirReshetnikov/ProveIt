#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-converse-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'b53053e8eb3f7d2e1c4e1bd1b36174c69d345198a50b8a38f2bebf75e5b21e29','provider_survey.py':'f0718b73be164360084728be13bf6c5966d71b9ea43fa5e75b759aafdb6bf83f','source-manifest.json':'90bcc6d188297855299b9fa22f379318f9e3c8341f13be87344d26c7e0feff9f','src/DiophantineConsistency/Sign33ResidualConverse.lean':'9e6bdcea410a2ce3e881ca7e7d2732475283270f470ad9b3c17b3179b3d3567f'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==9
for i,row in enumerate(rows):
 n='Sign33ResidualConverse%02d'%i if i<8 else 'Sign33ResidualConverse';q=p/'src/DiophantineConsistency'/f'{n}.lean';assert row['module']=='DiophantineConsistency.'+n and h(q)==row['source_sha256'];s=q.read_text();imps=re.findall(r'^import ([\w.]+)$',s,re.M);assert row['imports']==imps
 if i<8:
  assert imps==['DiophantineConsistency.Sign33ResidualAssembly'];assert re.findall(r'^theorem (\w+)',s,re.M)==['residuals_zero'];assert s.count(f'hc.batch{i:02}.')==3
  found=[int(x) for x in re.findall(r'InternalZero \(Sign33ResidualBatch%02d.tailResidual p (\d+)\) v'%i,s.split(':= by',1)[0])];assert found==([0,1] if i==0 else list(range(3*i-1,3*i+2)))
  for j in range(3*i,3*i+3):assert f'have h{j} :' in s
  for k in range(4):assert f'(hp{k} :' in s
 else:
  assert imps==['DiophantineConsistency.Sign33ResidualConverse%02d'%j for j in range(8)];assert s.count('rfl |')==23
  for j in range(8):assert f'Sign33ResidualConverse{j:02}.residuals_zero p ports v hp0 hp1 hp2 hp3 hc' in s
  bullets=re.findall(r'^  · (.*)$',s,re.M);assert len(bullets)==24
  for k,line in enumerate(bullets):
   group=k//3;proj=['1','2.1','2.2'][k%3];assert f'hg{group}.{proj}' in line
   if k>0:assert f'Sign33ResidualBatch{group:02}.tailResidual' in line
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==9
print(json.dumps({'status':'PASS','preflight':o,'group_modules':8,'enumerated_cases':24,'scope':'uncompiled AllCuts-to-seed converse; no Lean replay'},sort_keys=True,indent=2))
