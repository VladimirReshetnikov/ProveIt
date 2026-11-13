#!/usr/bin/env python3
"""Draft: same-side audited finite coefficient decomposition replay."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2];REPO=ROOT.parents[1]
PLAN=BASE/'compact44-coefficient-decomposition-closure-plan';AUDITS=[ROOT/'reviews/compact44-943-decoder-independent-audit',ROOT/'reviews/compact44-coefficient-mass-independent-audit'];CLOSURE=ROOT/'reviews/compact44-coefficient-decomposition-closure-independent-audit'
SOURCE=BASE/'compact44-coefficient-decomposition-prototype/CompactCoefficientDecoder.lean';PREFIX=Path('/tmp/ipra-compact943-decoder-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
CLOSURE_PINS={CLOSURE/'audit.py':'07b8b99d3a208b6e055f8e8b54081160be17a419085c84828cca9298e48c7a8d',CLOSURE/'CHECK.json':'72cce2c801432154f8cbac90e4ef8f238ef4e636081c5475648ce8ec0bfd43e7',CLOSURE/'terminal-observation.json':'e002d9b22f3f514386f2139e8942484d66e063fdf0a04f71944a153c40b884b6'}
PINS={MONITOR:'2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',SOURCE:'86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8',
 PLAN/'scan.py':'853c7bf77369c1231cfa79349b107c547056725515959c2f09870bf6a3a3c2c8',PLAN/'scan.json':'3fab03590ed1723c04213c2a916d2c9476f51e9c1384ea73310883e1f486e6f4',PLAN/'README.md':'fa693afe9bca2a8ae146ab74eeea00d99696cba0f9bcec7f8dd85e115d2a331e',PLAN/'terminal-observation.json':'9ac7188fdc452a1bd5cd890e8fdf0c416d9700ed2883cbfd8fa51720b4f20e79',
 AUDITS[0]/'audit.py':'add329304148b75a4091684abb1afa64f5000d29d5f2bd37b0d388c7e9c90bc7',AUDITS[0]/'CHECK.json':'5a6695bd9fe61ae0d04331170eef880aa0bbea185b5dc3227950fc812877d578',AUDITS[0]/'terminal-observation.json':'5a29da0ea330d1781372fd5d2c8fd22c36a87eaa215b315720c087400d3618d3',
 AUDITS[1]/'audit.py':'ffd0206fd736c55bd633470a92bd28fe7f486973305e8a7e2fb3254d3f903d22',AUDITS[1]/'CHECK.json':'9fc48750f7846e6f2b5cfe3ea93b14935720fd04115b45e8cbf276b02af92a55',AUDITS[1]/'terminal-observation.json':'86e0753623b1f8d7ce2e0c0134e02e84430eccf53174d580f0de477e836b87e7'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
REPORTS={'CompactCoefficientDecoder.'+x for x in ('cast_value','selector_model','finite_decomposition')};AXIOMS={'propext','Classical.choice','Quot.sound'}
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def head():return subprocess.run(['git','rev-parse','HEAD'],cwd=REPO,text=True,capture_output=True,check=True,timeout=10).stdout.strip()
def guard(stem):
 out={}
 for suf in SUFFIXES:
  p=Path(str(stem)+suf)
  if os.path.lexists(p):
   need(p.is_file(),('invalid companion',str(p)));out[str(p)]={'realpath':str(p.resolve()),'sha256':h(p)}
  else:out[str(p)]=None
 return out
def checkguards(rows):
 for name,old in rows.items():
  p=Path(name)
  if old is None:need(not os.path.lexists(p),('unexpected companion',name))
  else:need(p.is_file() and str(p.resolve())==old['realpath'] and h(p)==old['sha256'],('companion drift',name))
def merge(rows,new):
 for k,v in new.items():need(k not in rows or rows[k]==v,('guard mismatch',k));rows[k]=v
def output(obj,before):
 stem=str(obj)[:-6];g=guard(stem)
 for suffix in SUFFIXES:
  value=g[stem+suffix]
  if suffix=='.olean' and not before:need(value is not None and obj.is_file() and not obj.is_symlink(),('invalid output',str(obj)))
  else:need(value is None,('unexpected output companion',stem+suffix))
 return g
def frozen_location(src,out):
 need(out.is_dir() and not out.is_symlink() and src.parent.is_dir() and not src.parent.is_symlink() and src.parent.parent.is_dir() and not src.parent.parent.is_symlink() and src.parent.parent.parent==out and src.parent.resolve().is_relative_to(out.resolve()),('invalid frozen source directory',str(src.parent)))
def frozen(src):
 frozen_location(src,src.parent.parent.parent)
 need(src.is_file() and not src.is_symlink() and h(src)==PINS[SOURCE],('frozen source drift',str(src)))
def outdir(obj,lib):
 need(not lib.is_symlink() and not lib.parent.is_symlink() and not lib.parent.parent.is_symlink() and not obj.parent.is_symlink() and obj.parent.resolve().is_relative_to(lib.resolve()),('invalid output directory',str(obj.parent)))
def verify():
 pins=PINS|CLOSURE_PINS
 for p,sha in pins.items():need(p.is_file() and h(p)==sha,('input drift',str(p)))
 scan=json.loads((PLAN/'scan.json').read_bytes());need(scan['status']=='PRELIMINARY_COEFFICIENT_DECOMPOSITION_CLOSURE_NOT_A_BUILD' and scan['decoder_objects_per_side']==123 and scan['mass_objects_per_side']==115 and scan['overlap_objects_per_side']==115 and len(scan['seeds'])==4,'closure scan schema')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=REPO,capture_output=True,timeout=180);need(q.returncode==0 and not q.stderr and q.stdout==(PLAN/'scan.json').read_bytes(),('closure rerun',q.returncode,q.stderr))
 closure=json.loads((CLOSURE/'CHECK.json').read_bytes());obs=json.loads((CLOSURE/'terminal-observation.json').read_bytes())
 need(closure.get('status')=='PASS_INDEPENDENT_COEFFICIENT_DECOMPOSITION_CLOSURE' and closure.get('reviewed_commit')=='28622c2888' and closure.get('audited_seed_objects')==4 and closure.get('scan_sha256')==PINS[PLAN/'scan.json'] and closure.get('source_sha256')==PINS[SOURCE] and closure.get('init_slots')==10 and closure.get('target_and_carry_slots')==80 and closure.get('seed_source_companion_slots')==40 and type(obs.get('observed_exit')) is int and obs['observed_exit']==0 and obs.get('lean_launched') is False and obs.get('check_sha256')==CLOSURE_PINS[CLOSURE/'CHECK.json'],'closure audit schema')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(CLOSURE/'audit.py')],cwd=REPO,capture_output=True,timeout=300);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==closure,('closure audit rerun',q.returncode,q.stderr))
 parents=[]
 for a in AUDITS:
  expected=json.loads((a/'CHECK.json').read_bytes());q=subprocess.run([sys.executable,'-I','-S','-B',str(a/'audit.py')],cwd=REPO,capture_output=True,timeout=1800)
  need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==expected,('parent audit rerun',str(a),q.returncode,q.stderr));parents.append(expected)
 for p,sha in pins.items():need(p.is_file() and h(p)==sha,('input drift after audits',str(p)))
 return scan,parents

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');ap.add_argument('--expected-head',required=True);ap.add_argument('--output',type=Path);args=ap.parse_args()
 need(re.fullmatch('[0-9a-f]{40}',args.expected_head) is not None and head()==args.expected_head,'launch HEAD mismatch')
 need(not args.verify_only or args.output is None,'verify-only forbids output')
 if not args.verify_only:
  need(args.output is not None,'missing output');out=args.output.absolute();need(out.parent.resolve(strict=True)==Path('/tmp').resolve() and out.name.startswith('ipra-compact-coefficient-decomposition-pair-') and not os.path.lexists(out),'fresh direct /tmp output required')
 driver=h(__file__);scan,parents=verify();need(h(__file__)==driver and head()==args.expected_head,'preflight drift')
 if args.verify_only:print(json.dumps({'status':'PASS_COEFFICIENT_DECOMPOSITION_PREFLIGHT','driver_sha256':driver,'lean_launched':False}),flush=True);return
 need(shutil.disk_usage('/tmp').free>=4*1024**3,'free space below reserve')
 spec=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
 out.mkdir();src=out/'frozen/DiophantineConsistency/CompactCoefficientDecoder.lean';src.parent.mkdir(parents=True);frozen_location(src,out);need(not os.path.lexists(src),'frozen source collision');shutil.copyfile(SOURCE,src);frozen_location(src,out);frozen(src);runs=[];allguards={}
 for side in ('author','peer'):
  need(head()==args.expected_head,'HEAD drift');frozen(src);checkguards(allguards);run=out/side;run.mkdir();lib=run/'lib';monitor.overlay(PREFIX/side/'lib',lib)
  for row in (x for x in scan['seeds'] if x['side']==side):
   seed=Path(row['path']);need(seed.is_file() and h(seed)==row['sha256'],('seed drift',side,row['module']));g=guard(str(seed)[:-6]);need(g[str(seed)] is not None and all(v is None for k,v in g.items() if k!=str(seed)),('seed companion',side));merge(allguards,g)
   target=lib/'DiophantineConsistency'/(row['module']+'.olean');outdir(target,lib);need(all(v is None for v in guard(str(target)[:-6]).values()),('seed collision',side));shutil.copyfile(seed,target)
   outdir(target,lib);need(target.is_file() and not target.is_symlink() and h(target)==row['sha256'],('seed copy drift',side));merge(allguards,output(target,False))
  init=PACKAGE/'Init.olean';window=lib/'DiophantineConsistency/ArithmeticWindowCarry.olean';need(init.is_file() and window.is_file(),'missing direct import');expected={str(init),str(window),str(lib/'DiophantineConsistency/Compact943Decoder.olean'),str(lib/'DiophantineConsistency/CompactCoefficientMass.olean')}
  for dep in expected:merge(allguards,guard(dep[:-6]))
  checkguards(allguards);env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=120);lines=deps.stdout.splitlines()
  need(deps.returncode==0 and not deps.stderr and set(lines)==expected and 1<=lines.count(str(init))<=2 and all(lines.count(x)==1 for x in expected if x!=str(init)),('dependency mismatch',side,deps.stdout,deps.stderr))
  frozen(src);checkguards(allguards);obj=lib/'DiophantineConsistency/CompactCoefficientDecoder.olean';outdir(obj,lib);output(obj,True);log=run/'compiler.log';cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out/"frozen"}',str(src),'-o',str(obj)]
  code,peak,reason=monitor.monitored(cmd,env,log,timeout=600);text=log.read_text();reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
  need(type(code) is int and code==0 and reason is None and re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text) is None,('compiler failure',side,code,reason,text[-4000:]));need(len(reports)==3 and {x for x,_ in reports}==REPORTS and all({x.strip() for x in ax.split(',') if x.strip()}==AXIOMS for _,ax in reports),('axiom reports',side,reports))
  outdir(obj,lib);merge(allguards,output(obj,False));checkguards(allguards);frozen(src);runs.append({'side':side,'object_sha256':h(obj),'log_sha256':h(log),'stdout':text,'compiler_exit':code,'stop_reason':reason,'deps_stdout':deps.stdout,'command':cmd,'sampled_peak_rss_bytes':peak})
 need(runs[0]['object_sha256']==runs[1]['object_sha256'] and runs[0]['stdout']==runs[1]['stdout'],'paired output mismatch')
 frozen(src);checkguards(allguards);scan2,parents2=verify();frozen(src);checkguards(allguards);need(scan2==scan and parents2==parents and h(__file__)==driver and head()==args.expected_head,'final input drift')
 for row in runs:
  obj=Path(row['command'][-1]);log=out/row['side']/'compiler.log';outdir(obj,out/row['side']/'lib');need(obj.is_file() and not obj.is_symlink() and h(obj)==row['object_sha256'] and log.is_file() and not log.is_symlink() and h(log)==row['log_sha256'],('final output drift',row['side']))
 receipt={'status':'PASS_PAIRED_COEFFICIENT_DECOMPOSITION','runs':runs,'driver_sha256':driver,'protected_head':args.expected_head,'guards':allguards,'parents':parents,'scope':'Finite external-index model coefficient identity for arbitrary inputs only; no Boolean/NoCarry/graph-column/retained-K binding or internal iPRA theorem. Point-in-time and inherited provider limitations apply.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'status':receipt['status'],'receipt_sha256':h(out/'receipt.json')}),flush=True)
if __name__=='__main__':main()
