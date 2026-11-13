#!/usr/bin/env python3
"""Audit frozen trace75 fold receipt, snapshots and selected providers without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Fold.lean';o=P/'observations/fold-attempt03';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-fold-v3.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75Fold.olean')==t['object_sha256']=='60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75Fold.graph_odd_ordinate' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['PellRecovery','Trace75Joined'],'imports')
mods=imports+['PellOddFold','PellFold','Trace75Residue','Trace75Adjacent','Trace75Factors','Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticPellHalfIndex'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
for m,h in {'PellRecovery':'0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a','PellOddFold':'853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175','PellFold':'5a45b94a6ff3dea0ba802c852b84f83daa99aace8415ede0bf682a11100a908b','Trace75Joined':'be92565d27f2893ed85e46c44d726a7a699d51ee9019105f932446831be7b305'}.items():
 x=next(x for x in selected if x['module']==m);need(x['sha256']==h,'hash '+m)
 if m.startswith('Pell'):need(x['path'].startswith('/tmp/pell-generic-fold-1n_2g52k/'),'fresh generic provider '+m)
for a in ['fold-attempt01','fold-attempt02']:need(json.loads((P/'observations'/a/'terminal.json').read_text())['exit']!=0,'prior failed '+a)
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
