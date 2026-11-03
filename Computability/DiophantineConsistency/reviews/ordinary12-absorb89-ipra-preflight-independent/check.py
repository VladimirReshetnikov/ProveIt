#!/usr/bin/env python3
"""Read-only audit of the 89-halt closure and proposed iPRA join runner."""
from hashlib import sha256
import importlib.util,json
from pathlib import Path
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-absorb89-ipra-join';O=H/'observations/scan-attempt02'
R=H/'run.py';S=O/'result.json';V=D/'research/ordinary12-direct90-ipra-join/run-v9.py';P=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
J=D/'research/ordinary12-absorb89-probe/observations/halt-attempt01/result.json'
PINS={R:'2d67b7118319bb22b7471de6f4f9ca10aad3fd8ea4a4f4922408feb73f49b93b',
 S:'7f2a1a85f7406e72e717efaa160fdbce4207fbd7c3fd7098dc266448fd38fbd0',
 V:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03',
 P:'09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed',
 J:'394ff5eb91126c7c879c07d215a959e3899bbe4db1e157727c373d67e8e73cb3'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'pin changed '+str(p))
spec=importlib.util.spec_from_file_location('v9_review',V);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
scan=json.loads(S.read_text());c=scan['closure'];old=json.loads(P.read_text());halt=json.loads(J.read_text())
need(scan['status']=='PASS' and old['status']=='PASS' and halt['status']=='PASS','predecessor status')
found={};minmem=10**12;maxlean=0
for i in range(c['header_batches']):
 label=f'selected-headers-{i:03}';r=json.loads((O/(label+'.json')).read_text());so=O/(label+'.stdout');se=O/(label+'.stderr')
 need(r['exit']==0 and r['reason'] is None and sha(so)==r['stdout_sha256'] and sha(se)==r['stderr_sha256'] and not se.read_bytes(),'header receipt '+label)
 cmd=r['command'];need(cmd[:6]==[str(m.LEAN),'-M3000','-j1','-DElab.async=false','--run',str(m.HELPER)],'header command')
 local={};current=None
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):
   need(current is None and line[6:] not in local,'header begin');current=line[6:];local[current]=[]
  elif line.startswith('IMPORT ') and current is not None:local[current].append(line[7:])
  elif line=='END' and current is not None:current=None
  else:raise RuntimeError('invalid header log')
 need(current is None and set(local)==set(cmd[6:]) and not set(local)&set(found),'header coverage');found.update(local)
 pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight')
 for sample in [pre]+r['samples']:
  minmem=min(minmem,sample['mem_available_kib']);maxlean=max(maxlean,len(sample['lean_pids']))
  need(sample['mem_available_kib']>=8*1024**2 and len(sample['lean_pids'])<=2,'resource sample')
need(len(found)==len(c['project'])==787 and all(r['path'] in found and found[r['path']]==r['imports'] for r in c['project'].values()),'project header coverage')
seen=set();outside=set();todo=list(c['roots'])
while todo:
 n=todo.pop()
 if n in seen or n in outside:continue
 if n in c['project']:seen.add(n);todo.extend(c['project'][n]['imports'])
 elif n in c['outside']:outside.add(n)
 else:raise RuntimeError('unresolved import '+n)
need(c['roots']==['Absorb89Halt'] and seen==set(c['project']) and outside==set(c['outside']) and len(outside)==44,'closure')
oldroot=Path(old['output_root'])/'lib';roots=[Path(x) for x in halt['lean_path'].split(':')];counts={'matched':[],'missing':[],'mismatched':[]}
for n,row in c['project'].items():
 stem=row['path'][:-len('.olean')]
 need(m.rec(row['path'])==row['record'] and {x:m.rec(stem+x) for x in m.SUFFIXES}==row['companions'],'selected provider '+n)
 if '.' in n:
  top=n.split('.')[0];rel=Path(n.replace('.','/')+'.olean');first=next((root for root in roots if (root/top).is_dir()),None)
  need(first is not None and (first/rel).is_file(),'namespace shadow '+n)
 target=oldroot/n.replace('.','/');other={x:m.rec(str(target)+x) for x in m.SUFFIXES}
 need(other==row['join_provider'],'90 union record '+n)
 if other['.olean'] is None:key='missing'
 elif all((None if other[x] is None else other[x]['sha256'])==(None if row['companions'][x] is None else row['companions'][x]['sha256']) for x in m.SUFFIXES):key='matched'
 else:key='mismatched'
 counts[key].append(n)
need(all(sorted(counts[k])==scan['report'][k] for k in counts),'classification')
need(len(counts['matched'])==765 and len(counts['missing'])==22 and not counts['mismatched'] and all('.' not in x for x in counts['missing']),'unexpected classification')
m.recheck_outside(c)
project_dirs={x.name for x in oldroot.iterdir() if x.is_dir()};package_dirs={x.name for x in m.PACKAGE.iterdir() if x.is_dir()}
need(not project_dirs&package_dirs,'union/package namespace overlap')
f=json.loads(m.FINAL.read_text());m.validate_final(f);m.manifest_recheck(f);producers=m.producer_receipts(json.loads(m.APPROVED_CONE.read_text()),f)
need(len(producers)==425 and producers==old['producer_receipts'],'90 producer receipts')
for n,row in old['post_headers']['project'].items():
 stem=row['path'][:-len('.olean')];need(m.rec(row['path'])==row['record'] and {x:m.rec(stem+x) for x in m.SUFFIXES}==row['companions'],'90 selected object '+n)
m.recheck_outside(old['post_headers'])
for p,h in PINS.items():need(sha(p)==h,'pin changed during audit '+str(p))
print(json.dumps({'status':'PASS','runner_sha256':PINS[R],'header_batches':c['header_batches'],'project':len(seen),'external':len(outside),
 'matched':len(counts['matched']),'missing':len(counts['missing']),'mismatched':len(counts['mismatched']),
 '90_producers':len(producers),'minimum_sample_mem_kib':minmem,'maximum_sample_lean_processes':maxlean,
 'scope':'pre-launch selected-header/provider/runner audit; no Lean replay or package-transitive/dynamic/source-object audit'},indent=2,sort_keys=True))
