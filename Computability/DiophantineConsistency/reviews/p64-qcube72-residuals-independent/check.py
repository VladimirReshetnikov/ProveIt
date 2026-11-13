#!/usr/bin/env python3
"""Read-only direct-guard audit of actual-graph residual-splitting client."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-residuals-draft';O=P/'observations/attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='3c25b31eb0baa9aa8c9148d75da59af554978371b6b3a9eea5bf7dea51a73720'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainGraphResiduals.lean')==sha(O/'FreeMainGraphResiduals.lean'),'source')
need(sha(P/'check01.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash');text=(O/'compile.log').read_text()
need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M)
need([n for n,_ in reports]==['FreeMainGraphResiduals.first_same','FreeMainGraphResiduals.transport_same','FreeMainGraphResiduals.residuals'],'report names')
need(all(not (set(map(str.strip,a.split(',')))-{'propext','Classical.choice','Quot.sound',''}) for _,a in reports),'axiom reports')
prior=TASK/'research/p64-qcube72-model-carrier-draft/observations/shape01/result.json';q=json.loads(prior.read_text());path=q['command'][-1]
need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']=='b267810654a87962413aaf1681318b4f57b950d41ead489415033919ddb11ba2' and r['guards_before'][path]['sha256']==q['object_sha256'],'shape provider linkage')
providers={'FreeMainGraphShape':'b267810654a87962413aaf1681318b4f57b950d41ead489415033919ddb11ba2','P64QCube77Unit':'5e4e354b5a0a420c94967ca71c99a5088d41bac615651225c5aaf44a9390370d'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainGraphResiduals.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','g.A0.evalRing z=1 ∧ g.M.evalRing z=0 ∧ g.W.evalRing z=0 ∧','g.Na.evalRing z=1 ∧ g.Lt.evalRing z=0','P64QCube77Unit.first_ne_neg_of_transport p v hv hlt','P64QCube77Unit.positive_factors hunit haneg'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct captured-provider, source, result and actual-zero model theorem shape; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
