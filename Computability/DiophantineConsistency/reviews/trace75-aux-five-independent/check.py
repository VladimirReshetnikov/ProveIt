#!/usr/bin/env python3
"""Inspect trace75 auxiliary-index receipt and selected providers without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75AuxFive.lean';o=P/'observations/auxfive-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-auxfive-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75AuxFive.olean')==t['object_sha256']=='4cedad6c7e803f3d9c262f2b90910fb8988850075b628708e9468c84d8d15381','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75AuxFive.graph_auxiliary_index_ge_five' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
need(re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)==['Trace75MainSize'],'direct import')
mods=['Trace75MainSize','Trace75MainFive','Trace75MainIndex','Trace75ThreeExcluded','Trace75ThreeTwo','Trace75ThreeGap','Trace75Index','Trace75Fold','Trace75Pell','PellRecovery','PellOddFold','PellFold','DiophantineConsistency.ArithmeticPellFirstNorm'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p is not None,'selection '+m);pin=any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items())
 if m!='DiophantineConsistency.ArithmeticPellFirstNorm':need(pin,'unpinned '+m)
 else:
  old=json.loads((P/'observations/pell-attempt01/terminal.json').read_text());need(not pin and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in old['inputs'].items()),'prior firstnorm pin')
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m=='Trace75MainSize','pinned_here':pin})
need(selected[0]['sha256']=='617754ec439b63ae5ab242ce2c161d0b500b3925220b1a790ac6f6c151d6555f','mainsize')
need(json.loads((P/'observations/auxfive-attempt01/terminal.json').read_text())['exit']!=0,'prior failed')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
