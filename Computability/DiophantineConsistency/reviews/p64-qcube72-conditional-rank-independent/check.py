#!/usr/bin/env python3
"""Read-only audit of conditional actual-graph rank client."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-conditional-rank-draft';O=P/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='5aaee0759cb98c0e1cafcc2c3a3d42c016b9f65c9827d8e584c46192c0226d34'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainConditionalRank.lean')==sha(O/'FreeMainConditionalRank.lean'),'source')
need(sha(P/'check01.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash');text=(O/'compile.log').read_text()
need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
need(text.strip()=="'FreeMainConditionalRank.main_index_eq_rank' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
prior=TASK/'research/p64-qcube72-actual-large-draft/observations/attempt02/result.json';q=json.loads(prior.read_text());path=q['command'][-1]
need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']=='47d2c20249e9cadd6e985df44786e8626af091f99c3091f1746845f6fe112c0b' and r['guards_before'][path]['sha256']==q['object_sha256'],'prior producer linkage')
providers={'FreeMainActualLarge':'47d2c20249e9cadd6e985df44786e8626af091f99c3091f1746845f6fe112c0b','DiophantineConsistency/AdaptiveGap85GenericSignedHalfIndex':'f6b6b2d9dfa98620acd4ef401efbab1bbc4ee9c0f5fea17f9aa25ea1ceee0d5d'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainConditionalRank.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V) (R : V)','(hv : ∀ i, 0 < v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','(hq : 33≤qval p v) (hR : 0<R) (hhalf : 2*R<cval p v)','(hstrong :','(haux : let z := absdiff','∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v)','xcoord R (aval p v)=g ∧ ycoord R (aval p v)=cval p v','FreeMainActualLarge.main_index_large p v hv hz hq','signed_half_index_of_facts'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct captured-provider, source, result and conditional model theorem shape; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
