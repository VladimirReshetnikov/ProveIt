#!/usr/bin/env python3
"""Read-only direct-guard audit of actual-graph model-level large-c client."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-actual-large-draft';O=P/'observations/attempt02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='47d2c20249e9cadd6e985df44786e8626af091f99c3091f1746845f6fe112c0b'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainActualLarge.lean')==sha(O/'FreeMainActualLarge.lean'),'source')
need(sha(P/'check02.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash');text=(O/'compile.log').read_text()
need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
need(text.strip()=="'FreeMainActualLarge.main_index_large' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
for rel,expected in [('p64-qcube72-main-root-draft/observations/attempt01/result.json','2429ba1307bde7a83ca68110773cd073825ba5f1d1ee0e1dd59dbbf8dc8d7930'),('p64-qcube72-main-index-lower-plan/observations/attempt02/result.json','27b2dac60724412a67574610fc5f613940fcf93bf403e1c61f3b5d2029cf18c1')]:
 q=json.loads((TASK/'research'/rel).read_text());path=q['command'][-1]
 need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']==expected and r['guards_before'][path]['sha256']==expected,('provider linkage',rel))
providers={'FreeMainGraphMainRoot':'2429ba1307bde7a83ca68110773cd073825ba5f1d1ee0e1dd59dbbf8dc8d7930','FreeMainIndexLower':'27b2dac60724412a67574610fc5f613940fcf93bf403e1c61f3b5d2029cf18c1','DiophantineConsistency/ArithmeticPellResidueAux':'822ff3a7319d4e56cab509034489ec8a984816078630cb3d7fdb01a4df00df29'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainActualLarge.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V)','(hv : ∀ i, 0 < v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','(hq : 33≤(p 0:V)*v 0+1)','∃ g m : V, g*g=1+delta a*c*c','xcoord m a=g ∧ ycoord m a=c ∧ 6≤m ∧ (a+2)*delta a*delta a<c','FreeMainGraphMainRoot.main_index p v hv hz','FreeMainIndexLower.six_le_index','large_of_six a m hm'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct captured-provider, source, result and actual-zero model theorem shape; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
