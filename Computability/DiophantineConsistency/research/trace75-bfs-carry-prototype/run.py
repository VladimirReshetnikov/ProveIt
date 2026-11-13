#!/usr/bin/env python3
"""HELD: check trace75/direct-BFS carry against the fresh replay union."""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse,fcntl,json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1];SRC=H/'Trace75BFSCarry.lean'
ATT=D/'research/trace75-fresh-provider-rebuild/observations/attempt01';RESULT=ATT/'result.json';INITIAL=ATT/'initial-union.json';OUTER=D/'research/trace75-fresh-provider-rebuild/observations/outer-attempt01/terminal.json'
BFSATT=D/'research/direct-bfs-80-coherent-rebuild/observations/attempt01';BFS=BFSATT/'result.json';OUTSIDE=BFSATT/'outside-baseline.json'
HELPER=D/'research/ordinary12-ipra-bridge/compact12-ipra-all-project-import-inventory/ReadObjectImports.lean';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={SRC:'84b55b0b1e206c5a9e7d16292581651bbe69cbed51b4f50f8a2faf6563bf1499',RESULT:'b74858343a05be6710e0666abb86189aea375ebd4d494411fee00d31e9f31e1a',INITIAL:'1b6b3f1c3938bd1448dda5811509971de2b16d8c07a407831a86434b89863c10',OUTER:'4c310be9b2ee9aa32378f27869c87e7bbbd8af2512f3b6391d02518e3dcbc7af',BFS:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',OUTSIDE:'5ed42b353836c0cae01a838b701347c7a2c9cc84318e893fbe5c4ae0c7c0b777',HELPER:'886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def rel(n):
 need(re.fullmatch(r'[A-Za-z0-9_\.]+',n) is not None,'bad module '+n);return n.replace('.','/')
def rec(p):
 if not os.path.lexists(p):return None
 need(p.is_file(),'dangling/non-file '+str(p));return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def bundle(stem):return {s:rec(Path(str(stem)+s)) for s in SUFFIXES}
def hashes(r):return {s:None if r[s] is None else r[s]['sha256'] for s in SUFFIXES}
def selected(n,roots):
 for root in roots:
  p=root/(rel(n)+'.olean')
  if os.path.lexists(p):need(p.is_file(),'dangling shadow '+str(p));return p
 return None
def report_ok(out,err):
 return out=="'Trace75BFSCarry.graph_indexed_carry' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and err==''
def check_root(root,allowed):
 for p in root.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling output-root entry '+str(p))
  if p.is_file() or p.is_symlink():need(str(p.relative_to(root)) in allowed,'unexpected output-root entry '+str(p))
def resources():
 rows=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in rows if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def guard():
 x=resources();need(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<2,'resource preflight');return x
def monitored(cmd,env,out,err,timeout):
 pre=guard();samples=[];reason=None;start=time.monotonic()
 with out.open('x') as so,err.open('x') as se:
  proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
  try:
   while proc.poll() is None:
    time.sleep(1);s=resources();samples.append(s)
    if s['mem_available_kib']<8*1024**2 or len(s['lean'])>2:reason='resource guard';proc.kill();break
    if time.monotonic()-start>timeout:reason='timeout';proc.kill();break
  finally:
   if proc.poll() is None:proc.kill()
   proc.wait()
 return {'command':cmd,'env':env,'exit':proc.returncode,'reason':reason,'preflight':pre,'postflight':resources(),'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(out),'stderr_sha256':sha(err)}
def parse_header(text,path):
 lines=text.splitlines();need(lines and lines[0]=='BEGIN '+str(path) and lines[-1]=='END','bad header envelope')
 need(all(s.startswith('IMPORT ') and re.fullmatch(r'[A-Za-z0-9_\.]+',s[7:]) for s in lines[1:-1]),'bad header record');return [s[7:] for s in lines[1:-1]]
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args();need(args.preflight_only != bool(args.attempt),'choose preflight or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
RUNSHA=sha(__file__)
for p,h in PINS.items():need(sha(p)==h,'input drift '+str(p))
run=json.loads(RESULT.read_text());outer=json.loads(OUTER.read_text());bfs=json.loads(BFS.read_text());outside=json.loads(OUTSIDE.read_text());initial=json.loads(INITIAL.read_text())
need(run['status']=='PASS' and outer['exit']==0 and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after'] and outer['child_result_sha256']==PINS[RESULT] and bfs['status']=='PASS','bad producer receipt')
lib=Path(run['output_root'])/'lib';expected=dict(initial)
for st in run['stages']:
 need(st['status']=='PASS' and st['exit']==0 and st['reason'] is None,'stage failed');need(st['module'] not in expected,'duplicate stage');expected[st['module']]=st['object']
need(len(expected)==1977 and len(outside)==80,'inventory count')
source_imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',SRC.read_text(),re.M)
DIRECT=['Trace75FixedCongruence','DirectBFSBandCarry','DiophantineConsistency.ActualTemporalBand'];need(source_imports==DIRECT,'source imports changed')
prior=bfs['closure']['project'];ext=bfs['closure']['outside'];subtrees={}
for root in DIRECT[1:]:
 todo=deque([root]);seen=set();boundary=set()
 while todo:
  n=todo.popleft()
  if n in seen or n in boundary:continue
  if n not in prior:boundary.add(n);continue
  seen.add(n);todo.extend(prior[n]['imports'])
 need(boundary<=set(ext),'BFS subtree outside missing '+root);subtrees[root]={'project':sorted(seen),'outside':sorted(boundary)}
for root,sub in subtrees.items():
 for n in sub['project']:
  need(n in expected and hashes(expected[n])==hashes(prior[n]['companions']),'BFS ancestry/companion conflict '+n)
 for n in sub['outside']:need(n in outside and hashes(outside[n])==hashes(ext[n]['companions']),'BFS outside conflict '+n)
for n in DIRECT:need(n in expected,'direct provider absent '+n)
root=None
def stable():
 for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
 need(sha(__file__)==RUNSHA,'runner changed')
 if root is not None:check_root(root,{SRC.name,'Trace75BFSCarry.olean'})
 paths={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
 for p in lib.rglob('*'):
  if p.is_symlink():need(p.is_file(),'dangling union entry '+str(p))
 wanted={rel(n)+suffix for n,r in expected.items() for suffix,item in r.items() if item is not None};need(paths==wanted,'union inventory changed')
 for n,r in expected.items():
  cur=bundle(lib/rel(n));need(hashes(cur)==hashes(r),'union hash drift '+n)
  for s,item in r.items():
   if item is not None:need(cur[s]['resolved']==item['resolved'],'union target drift '+n+s)
 for n,r in outside.items():
  path=Path(r['.olean']['path']);search=([root] if root is not None else [])+[lib,PACK,CORE];need(selected(n,search)==path,'outside selection changed '+n)
  cur=bundle(Path(str(path)[:-6]));need(hashes(cur)==hashes(r),'outside bundle drift '+n)
  for s,item in r.items():
   if item is not None:need(cur[s]['resolved']==item['resolved'],'outside target drift '+n+s)
stable();pre=guard()
if args.preflight_only:
 print(json.dumps({'status':'PREFLIGHT_PASS','union':len(expected),'outside':len(outside),'subtrees':{n:len(v['project']) for n,v in subtrees.items()},'runner_sha256':RUNSHA}));raise SystemExit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
O=H/'observations'/args.attempt;need(not os.path.lexists(O),'attempt exists');O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='trace75-bfs-carry-'));copy=root/SRC.name;shutil.copyfile(SRC,copy);shutil.copyfile(SRC,O/'source.txt');need(sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'source copy drift')
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(root)+':'+str(lib)+':'+str(PACK),'LEAN_NUM_THREADS':'1'};reader_env={'PATH':'/usr/bin:/bin'};output=root/'Trace75BFSCarry.olean'
r={'status':'FAILED','runner_sha256':RUNSHA,'inputs':{str(p):h for p,h in PINS.items()},'output_root':str(root),'provider_union':str(lib),'preflight':pre,'subtrees':subtrees,'env':env,'scope':'symbolic direct-BFS parameterized carry only; external kernel/PDF binding and historical outside/package ancestry remain open'}
def save():
 p=O/'result.tmp';p.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');os.replace(p,O/'result.json')
try:
 stable();cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(copy),'-o',str(output)];r['stage']={'status':'RUNNING','command':cmd};save()
 stage=monitored(cmd,env,O/'stdout',O/'stderr',600);r['stage'].update(stage);r['stage']['status']='CHECKING';save()
 need(stage['exit']==0 and stage['reason'] is None and output.is_file() and not output.is_symlink() and report_ok((O/'stdout').read_text(),(O/'stderr').read_text()),'Lean result or axiom report failed')
 need(sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'copied source changed');stable();r['object_sha256']=sha(output);r['stage']['status']='PASS';save()
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER),str(output)];r['header']={'status':'RUNNING','command':cmd};save();head=monitored(cmd,reader_env,O/'header.stdout',O/'header.stderr',45);r['header'].update(head);save()
 need(head['exit']==0 and head['reason'] is None and not (O/'header.stderr').read_text(),'header failed');imports=parse_header((O/'header.stdout').read_text(),output)
 need([n for n in imports if n!='Init']==DIRECT,'unexpected serialized direct imports');need(sha(output)==r['object_sha256'] and sha(copy)==PINS[SRC] and sha(O/'source.txt')==PINS[SRC],'output/source changed');stable()
 r.update({'status':'PASS','header_imports':imports,'postflight':resources()});r['header']['status']='PASS';save();print(json.dumps({'status':'PASS','root':str(root),'object_sha256':r['object_sha256'],'result_sha256':sha(O/'result.json')}))
except BaseException as e:
 r.update({'status':'FAILED','exception':repr(e),'traceback':traceback.format_exc(),'postflight':resources()});save();raise
