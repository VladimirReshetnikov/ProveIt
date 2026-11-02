#!/usr/bin/env python3
"""Paired exact symbolic low-mask population over audited concrete-mask parents."""
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
PARENT=BASE/'compact44-concrete-mask-prototype';AUDIT=ROOT/'reviews/compact44-concrete-mask-independent-audit'
PREFIX=Path('/tmp/ipra-compact-concrete-mask-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
MONITOR=BASE/'free-j-current-denominator-composition/replay.py';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
STEPS=(('CompactLowPopulation',('CompactConcreteMask',),{'CompactLowPopulation.list_population','CompactLowPopulation.model_population'}),('CompactSupportCard',('CompactConcreteMask',),{'CompactSupportCard.support_card'}),('CompactLowExact',('CompactLowPopulation','CompactSupportCard'),{'CompactLowExact.model_population'}))
PINS={MONITOR: '2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8',
 LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 AUDIT/'audit.py': '51b88d7f5944cf5605730ab686ca17c91317d42af104a86a2b3f9126d86a1203',
 AUDIT/'CHECK.json': '38e176a41a83b029d0cf7a9c4f2406ea162b40528b56b3036343a9137b962fb8',
 PARENT/'evidence/receipt.json': '65a893c524bff130c16e63687a9e0aa896f2246ac5a1e57fdca149096de59fbd',
 HERE/'CompactLowPopulation.lean': 'b4b052b87a8883bc5f8096aca1eb1416583a51bda277c6eee95d973f018ed32b',
 HERE/'CompactSupportCard.lean': '654b825840ffdd9deda64f6ad608d707231bae9c09b6d7d8ad125467493b73e8',
 HERE/'CompactLowExact.lean': '189d3a0d400409b26595cdaa1a7aeacf99285481cb91827d2a4f89dd769018f6'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(path):
 spec=importlib.util.spec_from_file_location('monitor',path);obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
 for p,h in PINS.items():
  if H(p)!=h:raise ValueError(('fixed input drift',str(p)))
 check=json.loads((AUDIT/'CHECK.json').read_text());meta=json.loads((PARENT/'evidence/receipt.json').read_text())
 if check.get('status')!='PASS_INDEPENDENT_COMPACT44_CONCRETE_MASK_AUDIT' or check.get('recorded_outer_exit')!=0 or check.get('receipt_sha256')!=PINS[PARENT/'evidence/receipt.json'] or meta.get('status')!='PASS_PAIRED_COMPACT_CONCRETE_MASK' or len(meta['runs'])!=2:raise ValueError('invalid concrete-mask parent')
 for row in meta['runs']:
  if row['compiler_exit'] or row['deps_exit'] or H(PREFIX/row['label']/'CompactConcreteMask.olean')!=row['object_sha256']:raise ValueError(('concrete parent drift',row['label']))
 proc=subprocess.run([sys.executable,'-I','-S','-B',str(AUDIT/'audit.py')],capture_output=True,text=True,timeout=900)
 if proc.returncode or proc.stderr or json.loads(proc.stdout)!=check:raise ValueError(('concrete audit rerun failed',proc.returncode,proc.stderr))
 return check,meta

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);out=ap.parse_args().output.absolute()
 if out.parent.resolve(strict=True)!=Path('/tmp').resolve() or not out.name.startswith('ipra-compact-low-exact-pair-') or out.exists() or out.is_symlink():raise ValueError('use a fresh direct /tmp/ipra-compact-low-exact-pair-* path')
 before,meta=verify();monitor=load(MONITOR);out.mkdir();runs=[]
 for side in ('author','peer'):
  run=out/side;root=run/'src';(root/'DiophantineConsistency').mkdir(parents=True);lib=run/'lib';monitor.overlay(PREFIX/side/'lib',lib)
  seed=lib/'DiophantineConsistency/CompactConcreteMask.olean'
  if seed.exists() or seed.is_symlink():raise ValueError('concrete seed path occupied')
  shutil.copyfile(PREFIX/side/'CompactConcreteMask.olean',seed)
  row=next(r for r in meta['runs'] if r['label']==side)
  if H(seed)!=row['object_sha256']:raise ValueError(('seed copy drift',side))
  env=os.environ.copy()
  for key in tuple(env):
   if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
  env['LEAN_PATH']=str(lib)+':'+str(PACKAGE);steps=[]
  for module,imports,names in STEPS:
   source=HERE/(module+'.lean');src=root/'DiophantineConsistency'/(module+'.lean');obj=lib/'DiophantineConsistency'/(module+'.olean');log=run/(module+'.log')
   if obj.exists() or obj.is_symlink():raise ValueError(('output path occupied',module))
   shutil.copyfile(source,src)
   if H(src)!=PINS[source]:raise ValueError(('source copy drift',module))
   cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
   code,peak,reason=monitor.monitored(cmd,env,log);text=log.read_text();reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
   if code or reason or 'warning:' in text or 'error:' in text or 'sorryAx' in text or len(reports)!=len(names) or {n for n,_ in reports}!=names:raise ValueError(('compiler failure',side,module,code,reason,text[-8000:]))
   if any({v.strip() for v in ax.split(',') if v.strip()}-{'propext','Classical.choice','Quot.sound'} for _,ax in reports):raise ValueError(('unexpected axioms',module,reports))
   deps=subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
   expected={str(PACKAGE/'Init.olean')}|{str(lib/'DiophantineConsistency'/(v+'.olean')) for v in imports}
   if deps.returncode or deps.stderr or set(deps.stdout.splitlines())!=expected:raise ValueError(('direct import drift',side,module,deps.returncode,deps.stdout,deps.stderr))
   if H(src)!=PINS[source]:raise ValueError(('source drift',side,module))
   steps.append({'module':module,'compiler_exit':code,'deps_exit':deps.returncode,'deps_stdout':deps.stdout,'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'log_sha256':H(log),'stdout':text,'axiom_reports':reports,'sampled_peak_rss_bytes':peak,'stop_reason':reason})
   print(side,module,'exit',code,'peak_RSS',peak,flush=True)
  runs.append({'label':side,'seed_sha256':H(seed),'steps':steps})
 if [{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[0]['steps']]!=[{k:v for k,v in r.items() if k not in ('command','deps_stdout','sampled_peak_rss_bytes')} for r in runs[1]['steps']]:raise ValueError('paired outputs differ')
 after,meta2=verify()
 if before!=after or meta!=meta2:raise ValueError('parent drift')
 receipt={'status':'PASS_PAIRED_COMPACT_LOW_EXACT','runs':runs,'parent_audit':after,'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},'scope':'Exact all-model population of the symbolic finite-list low mask. No retained MC/graph-port equality, high-mask population, machine/checker or PRA proof. No full package-transitive/dynamic ancestry audit.'}
 with (out/'receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
 print('PASS_PAIRED_COMPACT_LOW_EXACT',H(out/'receipt.json'),flush=True)
if __name__=='__main__':main()
