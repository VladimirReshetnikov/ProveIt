#!/usr/bin/env python3
"""Read-only endpoint and receipt inspection; does not invoke Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-explicit-rows-binding';s=P/'DisplayedRowsIPRA.lean';o=P/'observations/ipra-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and all(t['checks'].values()),'receipt')
need(sha(P/'run-ipra.py')==t['runner_sha256'] and sha(s)==t['source_sha256']==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'DisplayedRowsIPRA.olean')==t['object_sha256']=='128c42d9aeda9fa2cebb1faa84115bf7300d165d9233e5159a1f3685b2d7d547','object')
for p,h in t['pins'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
reports=re.findall(r"'(TenPositive80DisplayedRowsIPRA\.\w+)' depends on axioms: \[([^\]]+)\]",(o/'stdout').read_text(),re.S)
names=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']
need([x[0] for x in reports]==['TenPositive80DisplayedRowsIPRA.'+x for x in names] and all([z.strip() for z in a.split(',')]==['propext','Classical.choice','Quot.sound'] for _,a in reports) and (o/'stderr').read_text()=='','reports')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['DisplayedRows','Direct80SymbolicFixedIPRA'],'direct imports')
selected=[]
for m in imports+['Direct80Graph']:
 rel=m+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and str(p) in t['pins'] and sha(p)==t['pins'][str(p)],'selected '+m)
 selected.append({'module':m,'path':str(p),'sha256':sha(p),'direct':m in imports})
outer=json.loads((o/'outer-observation.json').read_text());output=json.loads(outer['output'])
need(outer['exit_code']==0 and outer['session_id']==17488 and output['exit']==0 and output['reason'] is None and output['object_sha256']==t['object_sha256'] and output['checks']==t['checks'],'outer observation')
print(json.dumps({'status':'PASS','source_sha256':sha(s),'runner_sha256':sha(P/'run-ipra.py'),'object_sha256':t['object_sha256'],'reports':names,'selected':selected,'outer_exit':outer['exit_code'],'lean_replayed':False},indent=2,sort_keys=True))
