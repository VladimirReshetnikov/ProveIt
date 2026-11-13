#!/usr/bin/env python3
"""Inspect frozen trace75 index receipt and provider selection without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Index.lean';o=P/'observations/index-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-index-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75Index.olean')==t['object_sha256']=='6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75Index.first_index_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Trace75Fold','Trace75Pell','Direct80IndexOne'],'imports')
mods=imports+['PellRecovery','PellOddFold','PellFold','Trace75Joined','Trace75Residue','Trace75Adjacent','Trace75Factors','Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticPellFirstNorm'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p is not None,'selection '+m)
 pinned=any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items())
 if m!='DiophantineConsistency.ArithmeticPellFirstNorm':need(pinned,'unpinned '+m)
 else:
  earlier=json.loads((P/'observations/pell-attempt01/terminal.json').read_text())
  need(not pinned and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in earlier['inputs'].items()),'prior first norm pin')
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports,'pinned_by_index_runner':pinned})
expected={'Trace75Fold':'60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263','Trace75Pell':'cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9','PellFold':'5a45b94a6ff3dea0ba802c852b84f83daa99aace8415ede0bf682a11100a908b'}
for m,h in expected.items():need(next(x for x in selected if x['module']==m)['sha256']==h,'provider '+m)
ft=json.loads((P/'observations/index-attempt01/terminal.json').read_text());need(ft['exit']!=0,'failed first attempt')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
