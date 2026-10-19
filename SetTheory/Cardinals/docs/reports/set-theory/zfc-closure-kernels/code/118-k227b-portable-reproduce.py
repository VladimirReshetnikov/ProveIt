#!/usr/bin/env python3
"""Portable exact construction/source/startup replay; --full rederives both runtimes."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
H=Path(__file__).resolve().parent
NAMES=('delayed_erasure229','loop_delayed228','source_fold227_zerofix')
def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true');ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args();O=a.output_dir.resolve();require(O!=H,'output must not replace packet root');O.mkdir(parents=True,exist_ok=True);beg=time.time()
 manifest=json.loads((H/'MANIFEST.json').read_text())
 for name,digest in manifest['files'].items():
  p=H/name;require(p.is_file()and sha(p)==digest,('manifest mismatch',name))
 def run(script,args,label):
  cmd=[sys.executable,'-B',str(H/script),*map(str,args)];result=subprocess.run(cmd,cwd=H,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(O/(label+'.log')).write_text(result.stdout);require(result.returncode==0,('replay failed',label,result.returncode,str(O/(label+'.log'))));print(label,'PASS',flush=True)
 run('check_construction.py',['--output-dir',O/'construction'],'construction')
 run('check_construction227.py',['--output-dir',O/'construction227'],'construction227')
 run('check_local227.py',['--output-dir',O/'local227'],'local227')
 run('check_source227.py',['--output',O/'source227/source_equivalence.json'],'source227')
 run('check_source_equivalence.py',['--output-dir',O/'source'],'source_equivalence')
 run('check_startup229.py',['--output-dir',O/'startup229'],'startup229')
 run('check_startup228.py',['--output-dir',O/'startup228'],'startup228')
 run('check_startup227.py',['--output-dir',O/'startup227'],'startup227')
 for name,sub in zip(NAMES,('startup229','startup228','startup227')):
  old=json.loads((H/name/'startup.json').read_text());new=json.loads((O/sub/'startup.json').read_text());old.pop('checker_sha256');new.pop('checker_sha256');require(old==new,('fresh startup differs from sealed',name))
 old=json.loads((H/'loop_delayed228/source_equivalence_independent.json').read_text());new=json.loads((O/'source/source_equivalence_independent.json').read_text());old.pop('checker_sha256');new.pop('checker_sha256');require(old==new,'fresh source proof differs from sealed')
 old=json.loads((H/'source_fold227_zerofix/source_audit/source_equivalence.json').read_text());new=json.loads((O/'source227/source_equivalence.json').read_text());old.pop('checker_sha256');new.pop('checker_sha256');require(old==new,'fresh227 source proof differs')
 run('replay_runtime.py',[*NAMES,'--check-only'],'runtime_inputs')
 if a.full:run('replay_runtime.py',[*NAMES,'--output-dir',O/'runtime'],'runtime_full')
 results=[]
 for name in NAMES:
  D=H/name;U=json.loads((D/'universal_runtime.json').read_text());P=json.loads((D/'proof_chain.json').read_text());require(U['status']=='UNIVERSAL_MATHEMATICAL_PASS' and P['status']=='PASS_EXACT_LITERAL_SOURCE_STARTUP_AND_UNIVERSAL_RUNTIME_COMPOSITION','sealed proof status');require(U['table_sha256']==sha(D/'candidate.tm')and U['sites_sha256']==sha(D/'sites.json')and P['canonical_sha256']==sha(D/'candidate.canonical.tm'),'sealed pins');results.append({'name':name,'working_states':U['working_states'],'canonical_sha256':P['canonical_sha256'],'guards':U['cases'],'symbolic_steps':U['symbolic_steps'],'startup_steps':P['startup_steps']})
 status='FULL_PORTABLE_REPLAY_PASS'if a.full else'QUICK_PORTABLE_BINDING_REPLAY_PASS';r={'status':status,'full_universal_runtimes_freshly_rederived':a.full,'manifest_sha256':sha(H/'MANIFEST.json'),'packet_files_verified':len(manifest['files']),'seconds':time.time()-beg,'candidates':results,'proof_boundary':'Fresh ordinary executable source/startup/runtime evidence as selected; no new Rocq/Lean theorem, no fresh K230 kernel build, no unconditional nonhalting. Quick mode does not rederive universal runtime cases.'};(O/'verification_result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
