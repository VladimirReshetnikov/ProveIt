#!/usr/bin/env python3
"""Read-only direct-guard audit of actual-graph natural strong norm."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-natural-norms-draft';O=P/'observations/strong02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='0396dc0d272ba556762ac08c1b80a8b4669b74af2117176cc7b15547c3f51918'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainStrongNorm.lean')==sha(O/'FreeMainStrongNorm.lean'),'source')
need(sha(P/'check_strong02.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash');text=(O/'compile.log').read_text()
need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M)
need([n for n,_ in reports]==['FreeMainStrongNorm.strong_same','FreeMainStrongNorm.strong'],'report names')
need(all(not (set(map(str.strip,a.split(',')))-{'propext','Classical.choice','Quot.sound',''}) for _,a in reports),'axiom reports')
prior=TASK/'research/p64-qcube72-residuals-draft/observations/attempt01/result.json';q=json.loads(prior.read_text());path=q['command'][-1]
need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']=='3c25b31eb0baa9aa8c9148d75da59af554978371b6b3a9eea5bf7dea51a73720' and r['guards_before'][path]['sha256']==q['object_sha256'],'prior producer linkage')
providers={'FreeMainGraphResiduals':'3c25b31eb0baa9aa8c9148d75da59af554978371b6b3a9eea5bf7dea51a73720','P64QCubeBinding':'b0a32668e5e6869e4067d7813b9142ad3465b941cc174452c08579938deda07d'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainStrongNorm.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)','(hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)','(v 5*c*c)*(v 5*c*c)+delta a=delta a*(v 4*v 4)','FreeMainGraphResiduals.residuals p v hv hz','P64QCubeBinding.strong pp z','P64Root.strong p w hW'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct captured-provider, source, result and actual-zero model theorem shape; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
