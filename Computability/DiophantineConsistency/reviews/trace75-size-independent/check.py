#!/usr/bin/env python3
"""Inspect trace75 size receipt and provider paths without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Size.lean';o=P/'observations/size-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-size.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75Size.olean')==t['object_sha256']=='2a536f3a3eb2129213dd4b30df564cff717068221c8e7b9b5e864475c29cf058','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75Size.graph_rank_size' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
need(re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)==['Trace75Index'],'direct import')
mods=['Trace75Index','Trace75Fold','Trace75Pell','Direct80IndexOne','PellRecovery','PellOddFold','PellFold','Trace75Joined','Trace75Factors','DiophantineConsistency.ArithmeticPellFirstNorm'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p is not None,'selected '+m)
 pinned=any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items())
 if m!='DiophantineConsistency.ArithmeticPellFirstNorm':need(pinned,'unpinned '+m)
 else:
  earlier=json.loads((P/'observations/pell-attempt01/terminal.json').read_text());need(not pinned and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in earlier['inputs'].items()),'prior first norm pin')
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'pinned_by_size_runner':pinned})
need(selected[0]['sha256']=='6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34','index provider')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
