#!/usr/bin/env python3
"""Inspect frozen graph binding receipt and direct providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75ThreeBinding.lean';o=P/'observations/threebinding-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-threebinding.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75ThreeBinding.olean')==t['object_sha256']=='a66ff3021153cafb70db06a89dd9ca83be49aa162c008ef9cb7e50d84da43877','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75ThreeBinding.first_index_eq_two_of_main_three' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Trace75Index','Trace75ThreeLarge'],'imports')
selected=[]
for m,h in [('Trace75Index','6cc75eb28726516d4901542f26f083ecceeb682d459ff4a71022f3d88b1a3a34'),('Trace75ThreeLarge','d8e8d07e7b91ee60a8afe6ea393f839f9c49aa386185d134d2bdefee8ca7b604')]:
 p=next((pathlib.Path(x)/(m+'.olean') for x in t['lean_path'].split(':') if (pathlib.Path(x)/(m+'.olean')).is_file()),None)
 need(p and sha(p)==h and any(pathlib.Path(q).resolve()==p.resolve() and d==h for q,d in t['inputs'].items()),'direct '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p)})
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
