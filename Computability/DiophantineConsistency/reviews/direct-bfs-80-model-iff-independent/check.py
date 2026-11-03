#!/usr/bin/env python3
"""Audit frozen corrected model iff receipt and shared providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-80-model-iff-corrected-prototype';s=P/'DirectBFS80ModelIffCorrected.lean';o=P/'observations/directbfs80iffcorrected-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFS80ModelIffCorrected.olean')==t['object_sha256']=='4858598cb5d931d788b6a0a76e00029ecd47cd24062217afa4059713aba9116d','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'DirectBFS80ModelIffCorrected.positive_model_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
expected=['95f9655fe3b57826b1ef5b786396ae31ea089c3e859dbc59e04c355204278de3','583dd7aa369634a3e575b6fd38f774ead915a751d7fce7bd8e5a64d620dfbf30','4da9ee64cb8258c8885d9194ca48d96f3cab806d2c0e2cadefc06fe63e95fd39','bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437']
for x,h in zip(t['direct_imports'],expected):
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256']==h,'selection '+x['module'])
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
paths=['research/direct-bfs-halt-80-graph-prototype/observations/directbfshalt80-attempt01/terminal.json','research/direct-bfs-80-model-halt-prototype/observations/directbfs80modelhalt-attempt03/terminal.json']
common={'Direct80Graph':'95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','DirectBFSSymbolicKernel':'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f'};selected=[]
for m,h in common.items():
 for u in [t]+[json.loads((D/f).read_text()) for f in paths]:
  q=next((pathlib.Path(z)/(m+'.olean') for z in u['lean_path'].split(':') if (pathlib.Path(z)/(m+'.olean')).is_file()),None);need(q and sha(q)==h,'common '+m)
  selected.append({'module':m,'path':str(q),'sha256':sha(q)})
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'common_selected':selected,'stage_receipts':len(t['stage_receipts']),'lean_replayed':False},indent=2,sort_keys=True))
