#!/usr/bin/env python3
"""Source66 reviewed replay proposal, not yet executed.
Seven certificate/witness jobs on a new external copy. Optional full direct
symbolic replay has a separate explicit360s cap; default jobs have120s each.
No manifest sweeps, compilers, solvers, version queries or discovery searches.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--package',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--full-symbolic',action='store_true');a=ap.parse_args();assert __debug__
    a.output=a.output.resolve();assert not a.output.exists();a.output.mkdir(parents=True);p=a.output/'package';shutil.copytree(a.package.resolve(),p);env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('ZFC246_TABLE',None)
    jobs=[('generate and close actual-root interval certificate',['code/abstract_program.py']),('independent exact interval closure and negative controls',['audit/verify_interval_independent.py','results/interval-invariants.json']),('local core plus closed-component integration obstruction',['search/reductions/code/check_shared_core.py','--baseline',p/'reference/context246','--output',a.output/'shared-core.json']),('scanner first-return witness and path census',['search/scanner/scanner_search.py','--obstruction-only','--output',a.output/'scanner']),('register-program bisimulation only',['search/decoder/check_bisimulation_certificate.py','search/decoder/rotation178_bisimulation.json','search/decoder/rotation178_sites_logical.json']),('seven saved abstract grammars and commutation census',['search/grammar/code/validate_grammars.py']),('rejected rotation exact startup and bounded runtime failure',['search/grammar/code/replay_rejected_rotation.py'])]
    if a.full_symbolic:jobs.append(('complete8385-case direct symbolic proof',['code/full_symbolic.py']))
    records=[];out=dict(status='RUNNING',source=66,source_package=str(a.package.resolve()),working_package=str(p),checksum_manifests_checked=False,line_endings_checked=False,compiler_invoked=False,new_search_run=False,reference_full_suite_replayed=False,full_symbolic_replayed=a.full_symbolic,commands=records)
    for i,(label,args) in enumerate(jobs,1):
        command=[sys.executable,'-B',*map(str,args)];cap=360 if args[0]=='code/full_symbolic.py' else 120
        print(f'[{i}/{len(jobs)}] {label}',flush=True);began=time.monotonic()
        try:r=subprocess.run(command,cwd=p,env=env,text=True,capture_output=True,timeout=cap);stdout,stderr,rc=r.stdout,r.stderr,r.returncode
        except subprocess.TimeoutExpired as e:
            stdout=e.stdout or '';stderr=e.stderr or ''
            if isinstance(stdout,bytes):stdout=stdout.decode(errors='replace')
            if isinstance(stderr,bytes):stderr=stderr.decode(errors='replace')
            rc=124
        op=a.output/f'{i:02d}.stdout.txt';ep=a.output/f'{i:02d}.stderr.txt';op.write_text(stdout);ep.write_text(stderr)
        records.append(dict(label=label,command=command,cwd=str(p),timeout_seconds=cap,returncode=rc,seconds=time.monotonic()-began,stdout=str(op),stderr=str(ep),stdout_sha256=sha(op),stderr_sha256=sha(ep)))
        out['status']='FAIL'if rc else'RUNNING';(a.output/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
        if rc:raise SystemExit(rc)
    x=json.loads((p/'results/interval-invariants.json').read_text());assert x['counts']['guarded_cases']==8385 and x['closure_edges']==8384
    x=json.loads((a.output/'shared-core.json').read_text());assert not x['zfc_consistency_machine']and x['blank_prefix_enters_trap_after']==3
    if a.full_symbolic:
        x=json.loads((p/'results/full-symbolic-results.json').read_text());assert x['status']=='PASS'and x['complete']and x['counts']['cases']==8385 and len(x['rows'])==492 and x['minimum_steps']==13
    out['status']='PASS';out['scope']='Certificate/witness replay only. Pure grammar/source bisimulation and matching blank startup do not certify a changed binary runtime. Rejected245 table stays rejected; no new complete sub246 machine or Lean/PA endpoint.';(a.output/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(records),'reviewed jobs',flush=True)
if __name__=='__main__':main()
