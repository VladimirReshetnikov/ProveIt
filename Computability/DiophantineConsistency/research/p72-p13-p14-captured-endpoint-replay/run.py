#!/usr/bin/env python3
"""Rebuild P13/P14 endpoint modules over the separately audited captured P64 overlay."""
import hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1];ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file())
PROV=Path('/tmp/p64-independent-captured-replay/lib');OUT=Path('/tmp/p72-p13-p14-captured-endpoint-20261105');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');TOOL=LEAN.parent.parent/'lib/lean'; AUDIT=D/'research/fourteen-p64-independent-replay/audit.py'; BASE=D/'Lean/DiophantineConsistency/Compact44';TOOLS=D/'research/ordinary13-p72-endpoint/tools'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
def save():
 p=OUT/'state.tmp';p.write_text(json.dumps(state,sort_keys=True,indent=2)+'\n');os.replace(p,OUT/'state.json')
def no_lean():
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  try:
   if (p/'comm').read_text().strip()=='lean' and (p/'stat').read_text().rsplit(')',1)[1].split()[0] not in ('Z','X'):return False
  except (FileNotFoundError,ProcessLookupError):continue
 return True
pins={HERE/'monitor.py':'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad',HERE/'controls.py':'549acb06c7e0a8a80545c4a2e6143ce8b0730974407fe3e9e8382c367ca31c4f',HERE/'controls-result.json':'11eb2364388e53a42fd9d3175a3b7255f29581093207d7d89257bdc0c8336fd5',AUDIT:'58c7fef4b45189b2fa6db0b4bbcb3e508f8d47ca2528df8acce0c002da8cb317',BASE/'IPRAOrdinary72.lean':'2a296211af161f8c8b7f4173f81c12e64dffeede4a76adf455928d7b9b54558e',BASE/'IPRAOrdinary72P14.lean':'b88eb198df9ae1a2f7366f10c5b5363aee95dc0d3546146a45d7cb39b9aada03',BASE/'P72Graph.lean':'fa31965a9b6c6c4937b4a27f22607a1e7e8ac4877bc8c9eb7994c28cb4fc677a',TOOLS/'generate_p72.py':'71cbdd3b052f8859421c10f77a5b5d0c710d7b993c49556220c3b9c93e3f017d',TOOLS/'generate_p14.py':'4960fc921f6b7826af3e2390221166c3fdce077e6879a63cb0d716a8831c31c1',PROV/'DiophantineConsistency/Compact44/P72Graph.olean':'cd9c5b6b0429a90a25d5b9ab88cde120f8e3b684045a561a90b56be0037661b7',PROV/'DiophantineConsistency/Compact44/P72Converse.olean':'98649a059e3c95f920b41cd0ad4dfa4798e48c52361ea7e963054636e6ea8f4a',PROV/'DiophantineConsistency/Compact44/IPRAOrdinary12Chain.olean':'c5b7cdd8507f9da7bde3ca34b0b42e97bf45a743f1e79180f15b7b4cc57a0df5'}
def checkpins():
 for p,h in pins.items():need(p.is_file() and sha(p)==h,'input drift '+str(p))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT)],cwd=ROOT,capture_output=True,timeout=120);need(q.returncode==0 and json.loads(q.stdout)['status']=='PASS','captured-provider audit failed')
 for script,src,expected in [('generate_p72.py','P72Graph.lean','ok: 98 gates'),('generate_p14.py','IPRAOrdinary72P14.lean','ok: 101 gates')]:
  q=subprocess.run([sys.executable,'-I','-S','-B',str(TOOLS/script),'--check',str(BASE/src)],cwd=ROOT,capture_output=True,timeout=60);need(q.returncode==0 and q.stdout.decode().startswith(expected) and not q.stderr,'graph binding '+script)
 need(sha(Path(__file__))==selfhash,'runner drift')
# The graph object is an audited import-only P72Graph shim. Verify its literal
# source body and object link without calling the captured provider current-base.
def checkgraph():
 shim=Path('/tmp/p65-reverse-provider/src/DiophantineConsistency/Compact44/P72Graph.lean');need(shim.is_file() and sha(shim)=='c015cac37af0877ad8d5f370b078557fc8007b06bd6a69ed06266465743c9754','graph shim')
 original=(BASE/'P72Graph.lean').read_text();modified=original.replace('import DiophantineConsistency.Compact44.FreeJSumSquares\n','import FreeJSumSquares\n',1);need(shim.read_text()==modified,'graph shim is not exact import-only change')
selfhash=sha(__file__);need(not OUT.exists() and no_lean() and PROV.is_dir(),'output exists, Lean active or provider missing');checkpins();checkgraph();OUT.mkdir()
state={'status':'RUNNING','runner_sha256':selfhash,'pins':{str(k):v for k,v in pins.items()},'records':[],'scope':'Current endpoint source over independently audited captured P64/P65 providers; not a fresh current-base closure or full dynamic/transitive provenance. Resource limits are sampled; escaped processes/spikes can be missed.'};save()
spec=importlib.util.spec_from_file_location('mon',HERE/'monitor.py');mon=importlib.util.module_from_spec(spec);spec.loader.exec_module(mon)
SUF=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def inventory():
 out={}
 for root,dirs,files in os.walk(PROV,followlinks=False,onerror=lambda e:(_ for _ in ()).throw(e)):
  rr=Path(root)
  for n in list(dirs):
   p=rr/n
   if p.is_symlink():need(p.is_dir(),'broken provider directory');out[str(p.relative_to(PROV))]=('dir',str(p.resolve()));dirs.remove(n)
  for n in files:
   p=rr/n;need(p.is_file(),'broken provider file');out[str(p.relative_to(PROV))]=('file',str(p.resolve()))
 return out
def overlay_check(inv):
 for rel,(_,target) in inv.items():
  p=OUT/'lib'/rel;need(p.is_symlink() and str(p.resolve())==target,'overlay drift '+rel)
def guards(names):
 out={}
 for n in sorted(names):
  for root in (OUT/'lib',TOOL):
   for suffix in SUF:
    p=root/(n.replace('.','/')+suffix)
    if os.path.lexists(p):need(p.is_file(),'bad input '+str(p));out[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
    else:out[str(p)]=None
 return out
try:
 inv=inventory();state['provider_inventory_sha256']=hashlib.sha256(json.dumps(inv,sort_keys=True).encode()).hexdigest();state['provider_inventory_entries']=len(inv)
 for rel,(kind,target) in inv.items():
  p=OUT/'lib'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(target,target_is_directory=kind=='dir')
 state['overlay_links']=inv;save()
 env=dict(os.environ,LEAN_PATH=str(OUT/'lib'),LEAN_NUM_THREADS='1')
 for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
 prefix=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','19',str(LEAN),'-M4000','-j1','-DElab.async=false']
 targets=[('IPRAOrdinary72',['DiophantineConsistency.Compact44.IPRAOrdinary12Chain','DiophantineConsistency.Compact44.P72Converse']),('IPRAOrdinary72P14',['DiophantineConsistency.Compact44.IPRAOrdinary72'])]
 for name,imports in targets:
  module='DiophantineConsistency.Compact44.'+name;source=OUT/'src/DiophantineConsistency/Compact44'/f'{name}.lean';source.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(BASE/f'{name}.lean',source)
  need(sha(source)==pins[BASE/f'{name}.lean'],'copied source')
  obj=OUT/'lib/DiophantineConsistency/Compact44'/f'{name}.olean';need(not os.path.lexists(obj),'output shadow '+name)
  record={'module':module,'source_sha256':sha(source),'runs':[]};state['active']=record;save()
  for typ,args in [('deps',['--deps',str(source)]),('compile',['--root='+str(OUT/'src'),str(source),'-o',str(obj)])]:
   log=OUT/f'{name}-{typ}.txt';m=mon.run(prefix+args,OUT,env,log,rss_limit=5*1024**3,mem_floor=10*1024**3,seconds=180,interval=.1);record['runs'].append({'command':prefix+args,**m,'log':str(log),'log_sha256':sha(log)});save();need(m['exit']==0 and m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids'],'Lean '+name+' '+typ+' failed')
   if typ=='deps':
    actual={};counts={}
    for line in log.read_text().splitlines():
     p=Path(line);roots=[r for r in (OUT/'lib',TOOL) if p.is_relative_to(r)];need(p.is_absolute() and p.is_file() and line.endswith('.olean') and len(roots)==1,'invalid dep '+line);n=str(p.relative_to(roots[0]))[:-6].replace('/','.');counts[n]=counts.get(n,0)+1;need(n not in actual or (n=='Init' and counts[n]<=2 and actual[n]['path']==line),'duplicate dep '+n);actual[n]={'path':line,'realpath':str(p.resolve()),'sha256':sha(p)}
    need(set(actual)-{'Init'}==set(imports),'unexpected direct imports '+name);record['direct_inputs']=actual;record['direct_guard']=guards(actual);save()
  text=(OUT/f'{name}-compile.txt').read_text();need(not re.search(r'(?im)^.*(?:error:|sorryAx|declaration uses .sorry.).*$',text),'error or placeholder '+name)
  expected=['positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'];expected=(['P72P14.zero_iff']+expected if name.endswith('P14') else expected)
  reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text);need(len(reports)==len(expected),'report count '+name)
  for (key,val),short in zip(reports,expected):need(key.endswith('.'+short) or key==short,'report name '+key);need(set(x.strip() for x in val.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},'axiom '+key)
  record['object_sha256']=sha(obj);need(guards(record['direct_inputs'])==record['direct_guard'],'direct input drift '+name);state['records'].append(record);state.pop('active');save();overlay_check(inv);checkpins();checkgraph()
 need(inventory()==inv,'provider inventory drift');need(sha(__file__)==selfhash,'runner drift');state['status']='PASS';save();print('PASS captured-provider P13/P14 endpoints',flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=repr(e));save();print('FAILED',repr(e),flush=True);raise
