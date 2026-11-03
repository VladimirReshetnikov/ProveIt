#!/usr/bin/env python3
"""Inspect frozen trace75 three/two receipt without invoking Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75ThreeTwo.lean';o=P/'observations/threetwo-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-threetwo.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75ThreeTwo.olean')==t['object_sha256']=='c6526cbc36bbc37365527ea028d25e46e514bca5461ef2a803e3d489725f7053','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75ThreeTwo.graph_three_two_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
need(re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)==['Trace75ThreeBinding'],'direct import')
mods=['Trace75ThreeBinding','Trace75ThreeLarge','Trace75Index','Trace75Pell','Trace75Fold','Trace75Factors','Trace75Joined','PellRecovery','PellOddFold','PellFold'];selected=[]
for m in mods:
 p=next((pathlib.Path(x)/(m+'.olean') for x in t['lean_path'].split(':') if (pathlib.Path(x)/(m+'.olean')).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m=='Trace75ThreeBinding'})
need(selected[0]['sha256']=='a66ff3021153cafb70db06a89dd9ca83be49aa162c008ef9cb7e50d84da43877','binding provider')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
