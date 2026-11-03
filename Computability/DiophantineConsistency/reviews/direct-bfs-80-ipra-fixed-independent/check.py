#!/usr/bin/env python3
"""Inspect frozen BFS fixed-port iPRA source, receipts and providers without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-80-ipra-fixed-prototype';s=P/'DirectBFS80FixedIPRA.lean';o=P/'observations/directbfs80iprafixed-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFS80FixedIPRA.olean')==t['object_sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
names=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']
need((o/'stdout').read_text()==''.join(f"'DirectBFS80FixedIPRA.{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in names) and (o/'stderr').read_text()=='','reports')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']]==['DirectBFS80IPRA'],'imports')
x=t['direct_imports'][0];rel=x['module']+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256']=='5a568d6580ca19a563a5e59514adcaffea499691183734df13bee9d27d2e4082','direct selection')
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
outer=P/'observations/outer-attempt01';ot=json.loads((outer/'terminal.json').read_text())
need(ot['exit']==0 and ot['pins']==ot['after'] and ot['pins']['source']==sha(s) and ot['pins']['runner']==sha(P/'run.py') and ot['pins']['supervisor']==sha(P/'run-supervised.py'),'supervisor state')
need(sha(outer/'stdout')==ot['stdout_sha256'] and sha(outer/'stderr')==ot['stderr_sha256'],'outer logs')
first=(outer/'stdout').read_text().splitlines()[0];out=json.loads(first)
need(out['exit']==0 and out['reason'] is None and out['object_sha256']==t['object_sha256'] and out['output_root']==t['output_root'],'outer/inner link')
need((outer/'stdout').read_text().split('\n',1)[1]==(o/'stdout').read_text()+'\n' and (outer/'stderr').read_text()=='\n','outer log contents')
selected=[]
for m,h in {'Direct80Graph':'95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','DirectBFSSymbolicKernel':'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f'}.items():
 q=next((pathlib.Path(z)/(m+'.olean') for z in t['lean_path'].split(':') if (pathlib.Path(z)/(m+'.olean')).is_file()),None);need(q and sha(q)==h,'common '+m);selected.append({'module':m,'path':str(q),'sha256':sha(q)})
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'common_selected':selected,'stage_receipts':len(t['stage_receipts']),'supervised_runner_exit':ot['exit'],'lean_replayed':False},indent=2,sort_keys=True))
