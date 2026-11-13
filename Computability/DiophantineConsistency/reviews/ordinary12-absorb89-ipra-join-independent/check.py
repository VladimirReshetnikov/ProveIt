#!/usr/bin/env python3
"""Independent audit of retained 89-operation iPRA join evidence."""
from hashlib import sha256
import importlib.util,json,re
from pathlib import Path
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-absorb89-ipra-join';A=H/'observations/join-attempt01';OUTER=H/'observations/outer-attempt01'
S=H/'run.py';WRAPPER=H/'run-outer.py';V=D/'research/ordinary12-direct90-ipra-join/run-v9.py'
P=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json';Q=H/'observations/scan-attempt02/result.json'
SOURCE=D/'research/ordinary12-absorb89-ipra-endpoint-draft/Absorb89IPRAEndpoint.lean'
PINS={A/'result.json':'77d82979cc040aadecad2e859e69037f8de1d4a70bda65a6457f47d97d73dc4e',
 OUTER/'terminal.json':'3831eac0462366fce56b49a41d920c5318f21abf39650b7849a2d3cd39c021e5',
 S:'2d67b7118319bb22b7471de6f4f9ca10aad3fd8ea4a4f4922408feb73f49b93b',
 WRAPPER:'5dd247afd597400e4cf36991eacb3a598db6275a47eb2dc711cc27d4fdae9347',
 V:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03',
 P:'09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed',
 Q:'7f2a1a85f7406e72e717efaa160fdbce4207fbd7c3fd7098dc266448fd38fbd0',
 SOURCE:'dad83ae6a217eaffeec8b1a6d6813ad1c69a3f280a0ac2056f2d71aa95e567f4'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'pin changed '+str(p))
spec=importlib.util.spec_from_file_location('v9_evidence',V);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for p,h in m.PINS.items():need(sha(p)==h,'prior input pin '+str(p))
d=json.loads((A/'result.json').read_text());outer=json.loads((OUTER/'terminal.json').read_text());old=json.loads(P.read_text());scan=json.loads(Q.read_text());c=scan['closure']
need(d['status']=='PASS' and old['status']=='PASS' and scan['status']=='PASS','prior status')
need(d['runner_sha256']==outer['runner_sha256']==PINS[S] and outer['wrapper_sha256']==PINS[WRAPPER] and outer['exit']==0,'outer process receipt')
need(sha(OUTER/'stdout')==outer['stdout_sha256'] and sha(OUTER/'stderr')==outer['stderr_sha256'] and not (OUTER/'stderr').read_bytes(),'outer logs')
outer_output=json.loads((OUTER/'stdout').read_text());need(outer_output=={'status':'PASS','error':None,'output_root':d['output_root']},'outer result')
need(d['source_sha256']==PINS[SOURCE] and d['prior_join_sha256']==PINS[P] and d['scan_sha256']==PINS[Q],'join input pins')
out=Path(d['output_root'])/'lib';src=Path(d['output_root'])/'src';oldroot=Path(old['output_root'])/'lib'
need(sha(A/'source.lean')==sha(src/SOURCE.name)==PINS[SOURCE],'endpoint source snapshot')
text=SOURCE.read_text();expected=['''theorem standard_consistency : standardTheory ⊢
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
need(all(text.count(x)==1 for x in expected) and text.count('theorem positive_bridge : PositiveModelBridge (graph p).output')==1 and text.count('theorem byte_positive_bridge : PositiveModelBridge (graph byteP).output')==1,'endpoint statements')
def process(label):
 r=json.loads((A/(label+'.json')).read_text());so=A/(label+'.stdout');se=A/(label+'.stderr')
 need(r['exit']==0 and r['reason'] is None and sha(so)==r['stdout_sha256'] and sha(se)==r['stderr_sha256'],'process receipt '+label)
 pre=r['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'preflight '+label)
 for x in r['samples']:need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'resource sample '+label)
 return r,so.read_text(),se.read_text()
row,stdout,stderr=process('endpoint');obj=out/'Absorb89IPRAEndpoint.olean'
need(row['command']==[str(m.LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(src/SOURCE.name),'-o',str(obj)],'endpoint command')
need(not stderr and not m.diagnostic(stdout,'warning') and not m.diagnostic(stdout,'error') and 'sorryAx' not in stdout,'endpoint diagnostics')
need(m.rec(obj)==d['object_record'],'endpoint object')
names=['positive_bridge','byte_positive_bridge','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];reports={}
for n in names:
 hits=re.findall(r"^'Absorb89IPRAEndpoint\."+n+r"' depends on axioms: \[([^\]]*)\]$",stdout,re.M)
 need(len(hits)==1,'axiom report '+n);reports[n]=[x.strip() for x in hits[0].split(',')]
 need(reports[n]==['propext','Classical.choice','Quot.sound'],'unexpected axiom '+n)
need(reports==d['axioms'],'recorded axioms')
for n,r in c['project'].items():
 stem=r['path'][:-len('.olean')];need(m.rec(r['path'])==r['record'] and {s:m.rec(stem+s) for s in m.SUFFIXES}==r['companions'],'89 selected input '+n)
 target=oldroot/n.replace('.','/');need({s:m.rec(str(target)+s) for s in m.SUFFIXES}==r['join_provider'],'90 union selection '+n)
for n,r in old['post_headers']['project'].items():
 stem=r['path'][:-len('.olean')];need(m.rec(r['path'])==r['record'] and {s:m.rec(stem+s) for s in m.SUFFIXES}==r['companions'],'90 prior input '+n)
m.recheck_outside(c);m.recheck_outside(old['post_headers'])
f=json.loads(m.FINAL.read_text());m.validate_final(f);m.manifest_recheck(f);producers=m.producer_receipts(json.loads(m.APPROVED_CONE.read_text()),f)
need(len(producers)==425 and producers==old['producer_receipts'],'prior 425 producers')
prior={p.relative_to(oldroot).as_posix():m.rec(p) for p in oldroot.rglob('*') if p.is_file()};initial={k:{'sha256':v['sha256'],'resolved':v['resolved'],'link':v['resolved']} for k,v in prior.items()}
need(len(prior)==2685,'prior union count')
for n in scan['report']['missing']:
 for suffix,item in c['project'][n]['companions'].items():
  if item is not None:
   key=n.replace('.','/')+suffix;need(key not in initial,'supplement collision '+key)
   initial[key]={'sha256':item['sha256'],'resolved':item['resolved'],'link':item['resolved']}
need(len(initial)==d['union_initial_count']==2707 and sha256(json.dumps(initial,sort_keys=True).encode()).hexdigest()==d['union_initial_sha256'],'initial union')
final=dict(initial)
for suffix in m.SUFFIXES:
 rec=m.rec(str(obj)[:-len('.olean')]+suffix)
 if rec is not None:need('Absorb89IPRAEndpoint'+suffix not in final,'endpoint collision');final['Absorb89IPRAEndpoint'+suffix]=rec
def snapshot():return {p.relative_to(out).as_posix():m.rec(p) for p in out.rglob('*') if p.is_file()}
need(snapshot()==final,'final union drift')
post=d['post_headers'];found={}
for i in range(post['header_batches']):
 label=f'post-headers-{i:03}';r,log,err=process(label);need(not err,'header stderr');cmd=r['command']
 need(cmd[:6]==[str(m.LEAN),'-M3000','-j1','-DElab.async=false','--run',str(m.HELPER)],'header command')
 local={};current=None
 for line in log.splitlines():
  if line.startswith('BEGIN '):need(current is None and line[6:] not in local,'header begin');current=line[6:];local[current]=[]
  elif line.startswith('IMPORT ') and current is not None:local[current].append(line[7:])
  elif line=='END' and current is not None:current=None
  else:raise RuntimeError('header parse')
 need(current is None and set(local)==set(cmd[6:]) and not set(local)&set(found),'header coverage');found.update(local)
need(len(found)==len(post['project']) and all(r['path'] in found and found[r['path']]==r['imports'] for r in post['project'].values()),'header object coverage')
seen=set();outside=set();todo=list(post['roots'])
while todo:
 n=todo.pop()
 if n in seen or n in outside:continue
 if n in post['project']:seen.add(n);todo.extend(post['project'][n]['imports'])
 elif n in post['outside']:outside.add(n)
 else:raise RuntimeError('missing post import '+n)
need(post['roots']==['Absorb89IPRAEndpoint'] and seen==set(post['project']) and outside==set(post['outside']) and len(seen)==1631 and len(outside)==79,'post closure')
allowed=set(old['post_headers']['project'])|set(c['project'])|{'Absorb89IPRAEndpoint'}
need(seen<=allowed and not ({'FreeJRootBinding','FreeJSignedTransport'}&seen),'project collision or unknown')
for n,r in post['project'].items():
 path=out/(n.replace('.','/')+'.olean');stem=str(path)[:-len('.olean')]
 need(r['path']==str(path) and r['record']==m.rec(path) and r['companions']=={s:m.rec(stem+s) for s in m.SUFFIXES},'post object '+n)
 if n!='Absorb89IPRAEndpoint':
  source=c['project'].get(n,old['post_headers']['project'].get(n));need(source is not None,'unknown source '+n)
  for suffix in m.SUFFIXES:
   x=r['companions'][suffix];y=source['companions'][suffix]
   need((None if x is None else x['sha256'])==(None if y is None else y['sha256']),'post companion '+n+suffix)
for n,r in post['outside'].items():need(r==c['outside'].get(n,old['post_headers']['outside'].get(n)),'outside selection '+n)
m.recheck_outside(post);need(snapshot()==final,'union changed during audit')
for p,h in PINS.items():need(sha(p)==h,'input changed during audit '+str(p))
for p,h in m.PINS.items():need(sha(p)==h,'prior input changed '+str(p))
print(json.dumps({'status':'PASS','outer_exit':outer['exit'],'endpoint_object_sha256':d['object_record']['sha256'],
 'post_project':len(seen),'post_external':len(outside),'header_batches':post['header_batches'],
 'prior_producers':len(producers),'initial_union_files':len(initial),'final_union_files':len(final),
 'result_sha256':PINS[A/'result.json'],'scope':'retained author-join and selected provider audit; no independent Lean replay or full package/dynamic/source-object ancestry'},indent=2,sort_keys=True))
