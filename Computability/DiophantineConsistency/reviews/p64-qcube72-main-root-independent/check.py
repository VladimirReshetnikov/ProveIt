#!/usr/bin/env python3
"""Read-only check of actual-zero root/index client and direct provider link."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-main-root-draft'; O=P/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='2429ba1307bde7a83ca68110773cd073825ba5f1d1ee0e1dd59dbbf8dc8d7930'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainGraphMainRoot.lean')==sha(O/'FreeMainGraphMainRoot.lean'),'source')
need(sha(P/'check01.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash')
text=(O/'compile.log').read_text();need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
need(text.splitlines()==["'FreeMainGraphMainRoot.main_root' depends on axioms: [propext, Classical.choice, Quot.sound]","'FreeMainGraphMainRoot.main_index' depends on axioms: [propext, Classical.choice, Quot.sound]"],'axiom reports')
prior=TASK/'research/p64-qcube72-model-carrier-draft/observations/graph02/result.json';q=json.loads(prior.read_text());path=q['command'][-1]
need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']=='1f646961efda3232a04ed453729f5d911807dbd2e79c675b472fe93ad79bac33' and r['guards_before'][path]['sha256']==q['object_sha256'],'graph02 producer linkage')
providers={'DiophantineConsistency/ArithmeticAdaptiveQuotients2011':'90a77fd0f87f7f2388d0c9a4be0d50a4ef37b54e4122ec27047e456d99ca7515','DiophantineConsistency/ArithmeticPellClassification':'ae342d8638c01772896fbfbd4bf91883fa7b299b70b6fa1a3ef19b2a583a67bb','FreeMainGraphDivisibility':'1f646961efda3232a04ed453729f5d911807dbd2e79c675b472fe93ad79bac33'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainGraphMainRoot.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V)','(hv : ∀ i, 0 < v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','∃ g : V, g*g = (a*a+H)*(c*c)+1','∃ g m : V, g*g=1+delta a*c*c','xcoord m a=g ∧ ycoord m a=c','scaled_quotient U D N hU hsq','solution_index a g c hnorm'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct-provider, source, result and theorem-shape audit; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
