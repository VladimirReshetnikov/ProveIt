#!/usr/bin/env python3
"""Read-only verification of conditional rank-half client and provider."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-rank-half-draft';O=P/'observations/attempt02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='419eed176429e0e1f2d31f05db1963bb3d893a6d63b0f249aa89e83b6d867079'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainRankHalf.lean')==sha(O/'FreeMainRankHalf.lean'),'source')
need(sha(P/'check02.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash')
text=(O/'compile.log').read_text();need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
need(text.strip()=="'FreeMainRankHalf.rank_half' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
prior=TASK/'research/p64-qcube76-independent-y-guarded-check/observations/bounds-attempt03/result.json';q=json.loads(prior.read_text());path=q['command'][-1]
need(q['status']=='PASS' and q['exit']==0 and q['object_sha256']=='6458991845eba747546b4d45c454a31a907e226a98fbb7301d6cf30ae41da582' and r['guards_before'][path]['sha256']==q['object_sha256'],'provider linkage')
roots=r['lean_path'].split(':');need(str(Path(path).parent) in roots,'provider path')
for root in roots[:roots.index(str(Path(path).parent))]:need(not Path(root,'IndependentYBounds.olean').exists(),'provider shadow')
s=(P/'FreeMainRankHalf.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(q X Y R c g : DiffRing V)','(hq : 0≤q) (hX : q≤X) (hY : q*q*q≤Y)','(hwin : R+1 < q*(q*q*q)) (hc : 3≤c) (hg : 0≤g)','(hpell : g*g = 1+(((X*Y+Y)+2)*((X*Y+Y)+2)-1)*(c*c))', '2*R<c', 'IndependentYBounds.pell_c_bound'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct-provider, source, result and theorem-shape audit; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
