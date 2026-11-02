#!/usr/bin/env python3
"""Prelaunch-only paired compact44 controller replay; independent review required."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S, without optimization')
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';PLAN=R/'compact44-controller-closure-plan';CONTEXT=BASE/'reviews/historical-endpoint-contextual-audit';END_AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit';END_PKG=BASE/'research/thirteen-model-endpoint-successor';PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');VIEW=Path('/tmp/ipra-historical-audit-review-01');MONITOR=R/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
DATA=R/'compact44-controller-data-prototype/ArithmeticControllerDataCompact44.lean';CHOICE=R/'compact44-controller-choice-prototype/ArithmeticControllerChoiceCompact44.lean';OBS=[R/'compact44-controller-data-prototype/observation.txt',R/'compact44-controller-choice-prototype/observation.txt']
REVIEWED_CONTROLLER_PLAN=BASE/'reviews/compact44-controller-closure-independent-audit';REVIEWED_CONTEXT=BASE/'reviews/historical-endpoint-contextual-independent-audit'
PINS={PLAN/'scan.py':'80da1d9767307f2142be6db32cb007bee9cdbdbce78dbd8e427bd1a1aa307e82',PLAN/'scan.json':'d7799f4abc1afa29a7164eadd0cec74266a904d7ee8ff113508f6007cb9e564d',PLAN/'terminal-observation.json':'545dbcd2afd27361248c89f8067ab483cb1e6b38f8223526a079d1c0d367a67b',DATA:'8f28cce9e32b29bd3fd70ef193c46730aee3b2664e92037ce594ce0638c2f02c',CHOICE:'27d550683bcbeb285d3b84b621a2e4f61f691460ababca6c777e3214c2f9cc8e',OBS[0]:'2e08da8e327cd29c0d0b86f1519d1503378b8da8b98494c953aa8a9e7ba51c5c',OBS[1]:'a4bd0e50cb2ecb25c0c52b1d4a44f435e3fb881eaccf0da51a1526fafafe574b',CONTEXT/'contextual-endpoint.py':'a8a04953d66f0df7af61647e82f01e2120d86861c017b8c9bf2bfccce71b14db',CONTEXT/'CHECK.json':'d0308098d2d7816c0c8bf72c8c78227718a17984da34e35c1fb8a6f497d50f5e',END_AUDIT/'CHECK.json':'50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce',END_PKG/'replay-receipt.json':'8cf5b948a9442105a88627653e99e78d395a8f40f496b88e9adb6e439630e5cd',MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',REVIEWED_CONTROLLER_PLAN/'audit.py':'76f070d34a290412b47f4044e80f7ed12264b3377688eef9c7a21399c23d4ab8',REVIEWED_CONTROLLER_PLAN/'CHECK.json':'c787fecab4bf9d88388056cb0f9d94539c88f01a189fd73628caf2812a2baaac',REVIEWED_CONTROLLER_PLAN/'terminal-observation.json':'ee895d8e9d096c75fef8713cd36047f024b2324a7e8bc41e3319f1fe18c888a8',REVIEWED_CONTEXT/'audit.py':'7d4fa7211545463951fd79b8865e2653f1c963addf194cc5262264d1a99209a3',REVIEWED_CONTEXT/'CHECK.json':'4472b449716afd151f51d44931e9e66bad5c89c002419a86812361c3087a26b3',REVIEWED_CONTEXT/'terminal-observation.json':'ea6fcc5cfd293e93230e6fbcbd2cffdc5853a9ff88a76fef823fcd852bda69da'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def githead():return subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,check=True,text=True,capture_output=True).stdout.strip()
def verify(view):
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('pinned input drift or missing review',str(p)))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
 if q.returncode or q.stderr or json.loads(q.stdout)!=json.loads((PLAN/'scan.json').read_bytes()):raise ValueError(('controller scan',q.returncode,q.stderr))
 for directory,status in ((REVIEWED_CONTROLLER_PLAN,'PASS_INDEPENDENT_CONTROLLER_SOURCE_CLOSURE'),(REVIEWED_CONTEXT,'PASS_INDEPENDENT_CONTEXTUAL_ENDPOINT_EVIDENCE')):
  expected=json.loads((directory/'CHECK.json').read_bytes());obs=json.loads((directory/'terminal-observation.json').read_bytes())
  if expected.get('status')!=status or obs.get('check_sha256')!=PINS[directory/'CHECK.json'] or obs.get('lean_launched') is not False:raise ValueError(('invalid independent review',str(directory)))
  required=('observed_exit',) if directory==REVIEWED_CONTROLLER_PLAN else ('independent_preparation_exit','independent_contextual_exit','static_check_observed_exit')
  if any(type(obs.get(k)) is not int or obs[k]!=0 for k in required):raise ValueError(('independent review exit',str(directory)))
  q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],cwd=ROOT,capture_output=True,text=True,timeout=120)
  if q.returncode or q.stderr or json.loads(q.stdout)!=expected:raise ValueError(('independent review rerun',str(directory),q.returncode,q.stderr))
 q=subprocess.run([sys.executable,'-I','-S','-B',str(CONTEXT/'contextual-endpoint.py'),'--historical-view',str(view)],cwd=ROOT,capture_output=True,text=True,timeout=1200)
 if q.returncode or q.stderr or json.loads(q.stdout)!=json.loads((END_AUDIT/'CHECK.json').read_bytes()):raise ValueError(('contextual endpoint audit',q.returncode,q.stderr))
 return json.loads((PLAN/'scan.json').read_bytes())
def observed_expected(path):
 text=path.read_text();src=re.search(r'^Source was ([^;\n]+)',text,re.M)
 if not src or text.count('Compiler output:\n')!=1:raise ValueError(('bad observation schema',str(path)))
 return text.split('Compiler output:\n',1)[1].replace(src.group(1),'<SOURCE>')
def load(path):
 sp=importlib.util.spec_from_file_location('monitor',path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);return m
def guards(paths):
 result={}
 for obj in paths:
  if not obj.is_file():raise ValueError(('required direct object missing',str(obj)))
  stem=str(obj)[:-6]
  for s in SUFFIXES:
   p=Path(stem+s)
   if os.path.lexists(p):
    if not p.is_file():raise ValueError(('invalid companion',str(p)))
    result[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
   else:result[str(p)]=None
 return result
def check_frozen(source_dir):
 for original in (DATA,CHOICE):
  frozen=source_dir/original.name
  if not frozen.is_file() or frozen.is_symlink() or H(frozen)!=PINS[original]:raise ValueError(('frozen source drift',original.name))
def checkguards(items):
 for path,v in items.items():
  p=Path(path)
  if v is None:
   if os.path.lexists(p):raise ValueError(('new companion',path))
  elif not p.is_file() or str(p.resolve())!=v['realpath'] or H(p)!=v['sha256']:raise ValueError(('companion drift',path))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--expected-head',required=True);ap.add_argument('--historical-view',type=Path,required=True);args=ap.parse_args();out=args.output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-controller-pair-') or os.path.lexists(out):raise ValueError('fresh direct /tmp output required')
 if githead()!=args.expected_head:raise ValueError('unexpected launch HEAD')
 if shutil.disk_usage('/tmp').free<4*1024**3:raise ValueError('sampled free space below reserve')
 driver=H(__file__);before=verify(args.historical_view);mon=load(MONITOR);expected=[observed_expected(p) for p in OBS];out.mkdir();frozen=out/'src';d=frozen/'DiophantineConsistency';d.mkdir(parents=True)
 for source in (DATA,CHOICE):
  dest=d/source.name;shutil.copyfile(source,dest)
  if H(dest)!=PINS[source]:raise ValueError('frozen source drift')
 check_frozen(d)
 runs=[];allguards={}
 for side in ('author','peer'):
  run=out/side;run.mkdir();lib=run/'lib';mon.overlay(PARENT/side/'lib',lib);env=os.environ.copy()
  for k in tuple(env):
   if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for i,source in enumerate((DATA,CHOICE)):
   check_frozen(d)
   src=d/source.name;obj=lib/'DiophantineConsistency'/source.with_suffix('.olean').name;log=run/(source.stem+'.log')
   for suffix in SUFFIXES:
    if os.path.lexists(Path(str(obj)[:-6]+suffix)):raise ValueError(('output companion collision',str(obj),suffix))
   init=PACKAGE/'Init.olean'
   deps=[init,lib/'DiophantineConsistency/ArithmeticStandardCasts.olean',lib/'DiophantineConsistency/ArithmeticControllerLift.olean',lib/'DiophantineConsistency/ArithmeticPackingBlocks.olean',PACKAGE/'Mathlib/Tactic/ReduceModChar.olean'] if i==0 else [init,lib/'DiophantineConsistency/ArithmeticControllerDataCompact44.olean',lib/'BusyBeaver/ZFC/ArithmeticCantor.olean']
   g=guards(deps);checkguards(allguards)
   for k,v in g.items():
    if k in allguards and allguards[k]!=v:raise ValueError(('guard drift',k))
    allguards[k]=v
   q=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120)
   if q.returncode or q.stderr or set(q.stdout.splitlines())!=set(map(str,deps)):raise ValueError(('direct deps',side,source.stem,q.returncode,q.stderr,q.stdout))
   checkguards(allguards)
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={frozen}',str(src),'-o',str(obj)];code,peak,reason=mon.monitored(cmd,env,log,timeout=600);text=log.read_text()
   if code or reason or not obj.is_file() or obj.is_symlink() or text.replace(str(src),'<SOURCE>')!=expected[i] or 'sorryAx' in text or 'error:' in text:raise ValueError(('compiler/report/warning mismatch',side,source.stem,code,reason,text[-8000:]))
   if H(src)!=PINS[source] or githead()!=args.expected_head:raise ValueError('source or HEAD drift')
   checkguards(allguards)
   for k,v in guards([obj]).items():
    if k in allguards and allguards[k]!=v:raise ValueError(('output guard drift',k))
    allguards[k]=v
   check_frozen(d)
   steps.append({'module':source.stem,'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'compiler_exit':code,'deps_exit':q.returncode,'deps_stdout':q.stdout,'sampled_peak_rss_bytes':peak,'stop_reason':reason,'direct_guards':g,'command':cmd})
  runs.append({'side':side,'steps':steps})
 if any(a['source_sha256']!=b['source_sha256'] or a['object_sha256']!=b['object_sha256'] or a['stdout'].replace(str(frozen),'<ROOT>')!=b['stdout'].replace(str(frozen),'<ROOT>') for a,b in zip(runs[0]['steps'],runs[1]['steps'])):raise ValueError('paired mismatch')
 check_frozen(d);checkguards(allguards);after=verify(args.historical_view);check_frozen(d);checkguards(allguards)
 if before!=after or H(__file__)!=driver or githead()!=args.expected_head:raise ValueError('final input or HEAD drift')
 receipt={'status':'PASS_PAIRED_COMPACT_CONTROLLER','runs':runs,'driver_sha256':driver,'head':args.expected_head,'direct_and_output_guards':allguards,'scope':'Conditional symbolic model controller only, no retained graph/K binding, machine or iPRA theorem; contextual historical endpoint parent and dynamic/provider/resource boundaries apply.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_CONTROLLER',H(out/'receipt.json'))
if __name__=='__main__':main()
