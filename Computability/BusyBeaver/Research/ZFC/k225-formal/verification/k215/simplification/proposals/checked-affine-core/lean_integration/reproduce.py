#!/usr/bin/env python3
"""Reproduce the current K215 closure and the complete CM215 endpoint.

Run with a checkout containing the pinned source hashes, Lean 4.32.0, and a new
output directory. No project cache is imported. All compilers are serialized.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,default=HERE/'source',help='Pinned source snapshot (defaults to bundled source/)')
p.add_argument('--lean',required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args();repo=a.repo.resolve();out=a.out.resolve()
assert not out.exists(),'Use a new output directory'
lean=Path(shutil.which(a.lean) or a.lean).resolve()
assert lean.is_file() and (lean.parent/'lake').is_file()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((HERE/'base_sources.json').read_text())
for row in manifest:
 assert sha(repo/row['path'])==row['sha256'],row['path']
out.mkdir(parents=True);snapshot=out/'snapshot'
for row in manifest:
 dst=snapshot/row['path'];dst.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(repo/row['path'],dst)
subprocess.run([sys.executable,'-B',str(HERE/'batching/generator/verify_generator.py'),
                '--source',str(snapshot),'--out',str(out/'generator-check')],check=True)
# Four proof bodies use explicit kernel batches. All program/certificate data
# and public statements are identical to the pinned repository source.
for row in json.loads((HERE/'batching/sources.json').read_text()):
 dst=snapshot/row['repository_path'];src=HERE/'batching'/row['overlay_file']
 assert sha(dst)==row['original_sha256']
 assert sha(src)==row['batched_sha256']
 shutil.copyfile(src,dst)
rel=Path('Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean')
driver=snapshot/rel/'build.py'
old=driver.read_text();needle="['lake', 'env', 'lean', flag]"
assert old.count(needle)==1,'Unexpected driver revision'
driver.write_text(old.replace(needle,"['lake', '-q', 'env', 'lean', flag]"))
env=os.environ.copy();env['PATH']=str(lean.parent)+os.pathsep+env.get('PATH','')
env.pop('LEAN_PATH',None)
base=out/'baseline'
subprocess.run([sys.executable,'-B',str(driver),'--repo',str(snapshot),'--out',str(base),'--memory-mib','12288','--timeout','900'],env=env,check=True)
subprocess.run([sys.executable,str(HERE/'build_integration.py'),'--base-build',str(base),'--source',str(HERE/'cm215'),'--out',str(out/'integration'),'--lean',str(lean)],env=env,check=True)
subprocess.run([sys.executable,str(HERE/'build_calculus.py'),'--base-build',str(base),'--cm-build',str(out/'integration'),'--source-repo',str(snapshot),'--out',str(out/'calculus'),'--lean',str(lean)],env=env,check=True)
# This second call exercises the corrected driver's resume identity and cache bindings.
before={name:sha(base/name) for name in ['verification.json','completed.json','inventory.json','toolchain.json']}
attempts_before=len(list((base/'attempts').iterdir()))
sessions_before=len(list((base/'sessions').iterdir()))
command=[sys.executable,'-B',str(driver),'--repo',str(snapshot),'--out',str(base),'--memory-mib','12288','--timeout','900']
with (base/'resume.log').open('wb') as log:
 subprocess.run(command,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
after={name:sha(base/name) for name in before}
assert before==after
assert len(list((base/'attempts').iterdir()))==attempts_before
assert len(list((base/'sessions').iterdir()))==sessions_before+1
resume={'status':'PASS','command':command,'unchanged_bindings':after,
        'compiler_attempts_before':attempts_before,'compiler_attempts_after':attempts_before,
        'sessions_before':sessions_before,'sessions_after':sessions_before+1,
        'log_sha256':sha(base/'resume.log')}
(base/'resume_receipt.json').write_text(json.dumps(resume,indent=2)+'\n')
print('PASS: K215 endpoint (180 original + 4 batched project modules), CM215 endpoint, semantic refactor, and driver resume')
