#!/usr/bin/env python3
"""Audit the retained 90-row iPRA join; no Lean process is launched."""
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-direct90-ipra-join';A=H/'observations/attempt03';S=H/'run-v9.py'
PINS={A/'result.json':'09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed',
 S:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03'}
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
spec=importlib.util.spec_from_file_location('join_v9_audit',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for p,h in m.PINS.items():need(sha(p)==h,'runner input pin '+str(p))
d=json.loads((A/'result.json').read_text());need(d['status']=='PASS' and d['runner_sha256']==PINS[S] and sha(A/'runner.py')==PINS[S],'runner result')
need(d['final_sha256']=='7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e' and sha(m.FINAL)==d['final_sha256'],'manifest pin')
need(d['cone_sha256']==m.PINS[m.APPROVED_CONE] and sha(Path(d['completion_path']))==d['completion_sha256']=='5483e0f8444fcaeaec8a68929f63a77d2aa3435d27fafa1b89c78eed3dc57977','cone/completion pin')
cone=json.loads(m.APPROVED_CONE.read_text());final=json.loads(m.FINAL.read_text());m.validate_final(final);m.manifest_recheck(final)
producers=m.producer_receipts(cone,final);need(len(producers)==425 and producers==d['producer_receipts'],'producer receipt chain changed')
need(any(x['sha256']==m.PINS[m.QSCHEMA_RECEIPT] and x['index']==419 for x in producers['ZFCinPA.QSchema']),'repair producer')
need(any(x['sha256']==d['completion_sha256'] and x['index']==425 for x in producers[cone['topological_candidate'][-1]]),'completion producer')
base=m.snapshot_lib();need(len(base)==d['canonical_inventory_count']==2616 and sha256(json.dumps(base,sort_keys=True).encode()).hexdigest()==d['canonical_inventory_sha256'],'canonical inventory')
out=Path(d['output_root'])/'lib';src=Path(d['output_root'])/'src';need(out.is_dir() and src.is_dir(),'missing join output')
# Reconstruct the initial union independently from the canonical file records,
# then replace only the four affected modules and add the four new stages.
union={rel:{'sha256':r['sha256'],'resolved':r['resolved'],'link':r['resolved']} for rel,r in base.items()}
need(d['supplemental_modules']==final['report']['direct_missing'] and len(d['supplemental_modules'])==65,'supplemental set')
for n in d['supplemental_modules']:
 for suffix,r in final['records'][n]['selected_provider']['companions'].items():
  if r is not None:
   key=n.replace('.','/')+suffix;need(key not in union,'supplemental collision '+key)
   union[key]={'sha256':r['sha256'],'resolved':r['resolved'],'link':r['resolved']}
need(len(union)==d['initial_union_count']==2681 and sha256(json.dumps(union,sort_keys=True).encode()).hexdigest()==d['initial_union_sha256'],'initial union reconstruction')
stages=d['stages'];stage_names=m.AFFECTED+[x[0] for x in m.ADAPTER_SOURCES]+[m.CLIENT[0]]
need([x['module'] for x in stages]==stage_names,'stage order')
adapter=json.loads(m.ADAPTER.read_text());approved={x['module']:(m.ROOT/x['source'],x['source_sha256']) for x in adapter['rebuild_order']}
approved.update({n:(p,h) for n,p,h in m.ADAPTER_SOURCES+[m.CLIENT]})
need(all(row['source_sha256']==approved[row['module']][1] and sha(approved[row['module']][0])==row['source_sha256'] for row in stages),'approved canonical stage sources')
for row in stages:
 rel=row['module'].replace('.','/')
 for suffix in m.SUFFIXES:union.pop(rel+suffix,None)
 for suffix,item in row['companions'].items():
  if item is not None:need(rel+suffix not in union,'new collision');union[rel+suffix]=item
observed={p.relative_to(out).as_posix():m.rec(p) for p in out.rglob('*') if p.is_file()}
need(union==observed,'current final union mismatch');m.recheck_new(stages)
def process(label):
 info=json.loads((A/(label+'.json')).read_text());stdout=A/(label+'.stdout');stderr=A/(label+'.stderr')
 need(info['exit']==0 and info['reason'] is None and sha(stdout)==info['stdout_sha256'] and sha(stderr)==info['stderr_sha256'],'process receipt '+label)
 pre=info['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight '+label)
 for sample in info['samples']:need(sample['mem_available_kib']>=8*1024**2 and len(sample['lean_pids'])<=2,'resource sample '+label)
 return info,stdout.read_text(),stderr.read_text()
for i,row in enumerate(stages,1):
 label=f'stage-{i:02}';info,stdout,stderr=process(label);rel=row['module'].replace('.','/')
 need(sha(A/(label+'.source.lean'))==sha(row['archived_source'])==sha(row['compiled_source'])==row['source_sha256'],'stage source '+label)
 need(info['command']==[str(m.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(src/(rel+'.lean')),'-o',str(out/(rel+'.olean'))],'stage command '+label)
 need(not m.diagnostic(stdout+stderr,'error') and 'sorryAx' not in stdout+stderr,'stage error '+label)
 if i==4:
  need(not stderr and row['warning_policy']['accepted_exact_warning'],'warning stage stderr/record')
  r=subprocess.run([sys.executable,'-I','-S','-B',str(m.STANDARD_WARNING_VERIFY),str(A/(label+'.stdout')),row['compiled_source']],capture_output=True,timeout=30)
  need(r.returncode==0 and not r.stderr and sha256(r.stdout).hexdigest()==row['warning_policy']['stdout_sha256'],'exact warning policy')
 else:need(not m.diagnostic(stdout+stderr,'warning'),'stage warning '+label)
 need(sha(row['object'])==row['object_sha256'] and row['object_record']==m.rec(row['object']),'stage object '+label)
endpoint=(A/'stage-08.source.lean').read_text()
expected=['''theorem standard_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output) 🡘
      ∼mappedNativeRefutation embedding''',
 '''theorem standard_translated_consistency : standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ''',
 '''theorem reference_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)) 🡘
      ∼erase (mappedNativeRefutation embedding)''',
 '''theorem reference_translated_consistency : referenceTheory ⊢
    erase (IPRAExpressionNative.nativeNoZero (positiveShift (graph byteP).output)) 🡘
      erase ((Semiformula.lMap embedding sourceSentence)ᴺ)''']
need(all(endpoint.count(t)==1 for t in expected),'endpoint statement mismatch')
need(endpoint.count('theorem positive_bridge : PositiveModelBridge (graph p).output')==1 and endpoint.count('theorem byte_positive_bridge : PositiveModelBridge (graph byteP).output')==1,'bridge statements')
axioms=(A/'stage-08.stdout').read_text();names=['positive_bridge','byte_positive_bridge','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']
reports={}
for n in names:
 lines=re.findall(r"^'Direct90IPRAEndpoint\."+n+r"' depends on axioms: \[([^\]]*)\]$",axioms,re.M)
 need(len(lines)==1,'axiom report '+n);reports[n]=[x.strip() for x in lines[0].split(',')]
 need(reports[n]==['propext','Classical.choice','Quot.sound'],'unexpected axiom report '+n)
need(reports==d['endpoint_axioms'],'axiom result mismatch')
def closure(prefix,record):
 project=record['project'];outside=record['outside'];found={}
 need(sha256(json.dumps(record,sort_keys=True).encode()).hexdigest()==d[prefix+'_headers_sha256'],'closure hash '+prefix)
 for i in range(record['header_batches']):
  info,text,stderr=process(f'{prefix}-headers-{i:03}');need(not stderr,'header stderr')
  cmd=info['command'];need(cmd[:6]==[str(m.LEAN),'-M3000','-j1','-DElab.async=false','--run',str(m.HELPER)],'header command')
  current=None;local={}
  for line in text.splitlines():
   if line.startswith('BEGIN '):
    need(current is None and line[6:] not in local,'header begin');current=line[6:];local[current]=[]
   elif line.startswith('IMPORT ') and current is not None:local[current].append(line[7:])
   elif line=='END' and current is not None:current=None
   else:raise RuntimeError('bad header output '+prefix)
  need(current is None and set(local)==set(cmd[6:]) and not (set(local)&set(found)),'header paths');found.update(local)
 need(len(found)==len(project) and all(row['path'] in found and found[row['path']]==row['imports'] for row in project.values()),'header coverage '+prefix)
 seen=set();external=set();pending=list(record['roots'])
 while pending:
  n=pending.pop()
  if n in seen or n in external:continue
  if n in project:seen.add(n);pending.extend(project[n]['imports'])
  elif n in outside:external.add(n)
  else:raise RuntimeError('missing closure import '+n)
 need(seen==set(project) and external==set(outside) and set(record['roots'])<=seen,'closure reachability '+prefix)
 for n,row in project.items():
  need(row['path']==str(out/(n.replace('.','/')+'.olean')),'project path '+n)
  if prefix=='post' or n not in m.AFFECTED:
   stem=row['path'][:-len('.olean')]
   need(row['record']==m.rec(row['path']) and row['companions']=={s:m.rec(stem+s) for s in m.SUFFIXES},'project object/companions '+n)
 m.recheck_outside(record)
 return len(seen),len(external)
pre=closure('pre',d['pre_headers']);post=closure('post',d['post_headers'])
need(pre==(1605,79) and post==(1609,79),'closure counts')
need(all(n in d['pre_headers']['outside'] and row==d['pre_headers']['outside'][n] for n,row in d['post_headers']['outside'].items()),'external provider selection changed')
graph={n:r['imports'] for n,r in d['pre_headers']['project'].items()};candidate=set(cone['topological_candidate']);affected=set(graph)&candidate
while True:
 nxt=affected|{n for n,deps in graph.items() if any(x in affected for x in deps)}
 if nxt==affected:break
 affected=nxt
need(affected-candidate==set(m.AFFECTED),'affected project closure')
for stage in stages:
 n=stage['module'];need(n in d['post_headers']['project'],'stage absent from final closure '+n)
 row=d['post_headers']['project'][n]
 need(row['record']==stage['object_record'] and row['companions']==stage['companions'],'new stage selection '+n)
for p,h in PINS.items():need(sha(p)==h,'pin changed '+str(p))
for p,h in m.PINS.items():need(sha(p)==h,'runner input changed '+str(p))
need(m.snapshot_lib()==base and {p.relative_to(out).as_posix():m.rec(p) for p in out.rglob('*') if p.is_file()}==union,'provider changed during audit')
print(json.dumps({'status':'PASS','stage_count':len(stages),'producer_modules':len(producers),'pre_project':pre[0],
 'pre_external':pre[1],'post_project':post[0],'post_external':post[1],
 'pre_header_batches':d['pre_headers']['header_batches'],'post_header_batches':d['post_headers']['header_batches'],
 'endpoint_object_sha256':stages[-1]['object_sha256'],'result_sha256':PINS[A/'result.json'],
 'scope':'retained source/receipt/header/provider audit; outer exit author-observed, no new Lean replay or full package/dynamic/source-object ancestry'},indent=2,sort_keys=True))
