#!/usr/bin/env python3
"""Reconstruct, certify the source, and independently audit both K215-R6s.

Default: audit the archived full runtime evidence. --full-runtime additionally
reruns the inherited symbolic induction checker on both reconstructed machines.
No solver, network access, external repository, or third-party Python package.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,log,timeout=600):
    started=time.monotonic()
    with log.open('w')as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
    if r.returncode:raise RuntimeError(f'Exit {r.returncode}; inspect {log}')
    return {'argv':cmd,'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-started}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--full-runtime',action='store_true');ap.add_argument('--timeout',type=int,default=600);a=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise ValueError('Run with assertions enabled')
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);py=sys.executable;manifest=json.loads((ROOT/'manifest.json').read_text());jobs=[]
    for rel,h in manifest['verification_input_hashes'].items():
        if digest(ROOT/rel)!=h:raise ValueError('Changed verification input: '+rel)
    jobs.append(run([py,'-B',str(ROOT/'code/reconstruct.py'),'--out',str(out/'reconstructed')],out/'reconstruction.log'))
    jobs.append(run([py,'-B',str(ROOT/'code/check_joint_swaps.py'),'--zfc',str(ROOT/'baseline'),'--output',str(out/'source-certificate')],out/'source.log'))
    for name,item in manifest['candidates'].items():
        candidate=out/'reconstructed'/name if a.full_runtime else ROOT/'machines'/name
        if a.full_runtime:
            cmd=[py,'-B',str(ROOT/'code/runtime-inputs/validate_native.py'),str(candidate/'candidate.native.tm'),str(candidate/'sites.json'),str(candidate/'runtime')]
            before={f:digest(candidate/f)for f in item['output_hashes']};job=run(cmd,candidate/'runtime.log',a.timeout);jobs.append(job)
            after={f:digest(candidate/f)for f in item['output_hashes']}
            if before!=after:raise ValueError('Runtime input mutation')
            receipt={'kind':'direct subprocess return observation','observed_tool_exit_code':job['exit_code'],'stdout_stderr_file':'runtime.log','prelaunch_before_after_receipt':'The supplied reproduction wrapper recorded equal before/after artifact hashes.','before':before,'after':after,'argv':cmd,'elapsed_seconds':job['elapsed_seconds']}
            (candidate/'execution_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        cmd=[py,'-B',str(ROOT/'code/audit_candidate.py'),'--candidate',str(candidate),'--parent',str(ROOT/item['parent']),'--runtime-code',str(ROOT/'code/runtime-inputs'),'--dense',str(candidate/'candidate.tm'),'--output',str(out/(name+'-audit.json'))]
        for ref in manifest['accepted_reference_tables']:cmd+=['--reference',str(ROOT/ref)]
        other='rho6_120'if name=='rho6_210'else'rho6_210';cmd+=['--reference',str(ROOT/'machines'/other/'candidate.native.tm')]
        jobs.append(run(cmd,out/(name+'-audit.log')))
        audit=json.loads((out/(name+'-audit.json')).read_text())
        if any(x['isomorphic']for x in audit['rooted_graph_comparisons']):raise ValueError('Unexpected graph-isomorphic reference')
    result={'status':'PASS_REPRODUCED_CONSTRUCTION_SOURCE_AND_AUDITS','fresh_symbolic_runtime':a.full_runtime,'candidates':list(manifest['candidates']),'jobs':jobs,'scope':'Ordinary mathematical certificates and exact finite evidence audit; not a Lean/Rocq kernel proof.'}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='jobs'},indent=2))
if __name__=='__main__':main()
