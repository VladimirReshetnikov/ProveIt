#!/usr/bin/env python3
"""Read-only validation of graph02 and its four direct prior producer receipts."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency'; RESEARCH=TASK/'research'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
rows=[('p64-qcube72-model-divisibility-draft/observations/attempt02','FreeMainDivisibility','7bb7e9f6bee67dfe4d2a422bba3ca394b773d836484de8f21fb184dd78c6e342'),
('p64-qcube72-free-main-candidate/observations/graph','P64QCube72Free','942251ebbb10ba1497b6e51a0e52d8ddddb3bdbaac47f5b1f84c233d2e5d226d'),
('p64-qcube72-model-carrier-draft/observations/scale01','FreeMainCarrierScale','a7c8af94532cbebfa324e5f95ed2612df43eabc72ffa652e8c880d90a17d211d'),
('p64-qcube72-model-carrier-draft/observations/shape01','FreeMainGraphShape','b267810654a87962413aaf1681318b4f57b950d41ead489415033919ddb11ba2'),
('p64-qcube72-model-carrier-draft/observations/graph02','FreeMainGraphDivisibility','1f646961efda3232a04ed453729f5d911807dbd2e79c675b472fe93ad79bac33')]
receipts={}
for rel,name,objhash in rows:
 d=RESEARCH/rel; r=json.loads((d/'result.json').read_text());receipts[name]=r
 need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],(name,'status or guards'))
 for path,expected in r['guards_before'].items():
  path=Path(path)
  if expected is None:need(not os.path.lexists(path),(name,'unexpected',str(path)))
  else:need(path.is_file() and str(path.resolve())==expected['realpath'] and sha(path)==expected['sha256'],(name,'changed',str(path)))
 need(r['command'][-2]=='-o' and sha(r['command'][-1])==r['object_sha256']==objhash,(name,'object'))
 need(sha(d/'compile.log')==r['log_sha256'],(name,'log'))
 text=(d/'compile.log').read_text();need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),(name,'bad log'))
 source=Path(r['command'][-3]);snap=d/(name+'.lean')
 need(str(source) in r['guards_before'] and sha(source)==r['guards_before'][str(source)]['sha256'],(name,'source guard'))
 if snap.is_file():need(sha(source)==sha(snap),(name,'source snapshot'))
 carrier=RESEARCH/'p64-qcube72-model-carrier-draft'
 if name in ('FreeMainCarrierScale','FreeMainGraphShape','FreeMainGraphDivisibility'):
  run={'FreeMainCarrierScale':'check01.py','FreeMainGraphShape':'check_shape01.py','FreeMainGraphDivisibility':'check_graph02.py'}[name]
  need(sha(carrier/run)==r['runner_sha256'] and sha(carrier/'missing_child.py')==r['missing_child_helper_sha256'],(name,'runner helper'))
for consumer,producer in [('FreeMainCarrierScale','FreeMainDivisibility'),('FreeMainGraphShape','P64QCube72Free'),('FreeMainGraphDivisibility','FreeMainCarrierScale'),('FreeMainGraphDivisibility','FreeMainGraphShape')]:
 c=receipts[consumer];p=receipts[producer];path=p['command'][-1]
 need(c['guards_before'][path]['sha256']==p['object_sha256'],(consumer,producer,'producer guard'))
 roots=c['lean_path'].split(':');need(str(Path(path).parent) in roots,(consumer,producer,'path'))
 for root in roots[:roots.index(str(Path(path).parent))]:
  need(not Path(root,producer+'.olean').exists(),(consumer,producer,'earlier shadow'))
log=(RESEARCH/'p64-qcube72-model-carrier-draft/observations/graph02/compile.log').read_text()
need(log.strip()=="'FreeMainGraphDivisibility.q_dvd_h' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
t=(RESEARCH/'p64-qcube72-model-carrier-draft/FreeMainGraphDivisibility.lean').read_text()
for f in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V)','(hv : ∀ i, 0 < v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','((p 0:V)*v 0+1) ∣ v 13','FreeMainGraphShape.M_eval','FreeMainCarrierScale.of_carrier'):
 need(f in t,'missing theorem source fragment '+f)
print(json.dumps({'status':'PASS','scope':'Recorded direct receipts, paths, guards and theorem source; no Lean or full transitive/dynamic audit.','graph02_receipt_sha256':sha(RESEARCH/rows[-1][0]/'result.json'),'graph02_object_sha256':rows[-1][2],'review_script_sha256':sha(__file__)},sort_keys=True))
