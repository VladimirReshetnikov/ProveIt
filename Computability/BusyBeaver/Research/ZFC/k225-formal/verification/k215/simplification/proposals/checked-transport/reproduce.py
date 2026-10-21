#!/usr/bin/env python3
"""Audit the contribution; optionally rebuild its two minimal proof closures.

Python 3.10+ and the standard library suffice for default checks.
--proofs requires coqc/coqchk (recorded toolchain: Coq 8.18.0).
The complete Correct215/ZFC client is deliberately outside this minimal build.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time
ROOT=Path(__file__).resolve().parent

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out',type=Path,required=True,help='new output directory outside this archive')
    p.add_argument('--proofs',action='store_true')
    p.add_argument('--full-search',action='store_true')
    p.add_argument('--context-search',action='store_true')
    a=p.parse_args();out=a.out.resolve()
    if ROOT==out or ROOT in out.parents:raise SystemExit('Use an output directory outside the source archive.')
    out.mkdir(parents=True,exist_ok=False);(out/'logs').mkdir()
    report={'status':'RUNNING','steps':[],'excluded':['Full Correct215/ZFC endpoint closure','Lean compilation']}
    def save(): (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    manifest=json.loads((ROOT/'manifest.json').read_text())
    for name,info in manifest['files'].items():
        if digest(ROOT/name)!=info['sha256']:raise SystemExit('Artifact hash mismatch: '+name)
    report['manifest_files']=len(manifest['files']);save();print('Archive hashes PASS',flush=True)
    def run(name,args):
        t=time.monotonic()
        r=subprocess.run(args,cwd=ROOT,capture_output=True,text=True)
        log=out/'logs'/(name+'.log');log.write_text(r.stdout+r.stderr)
        report['steps'].append({'name':name,'command':list(map(str,args)), 'exit':r.returncode,
                                'seconds':time.monotonic()-t,'log_sha256':digest(log)})
        save();print(name,'PASS' if r.returncode==0 else 'FAIL',flush=True)
        if r.returncode:
            report['status']='FAILED';save();raise SystemExit(r.stdout+r.stderr)
    py=[sys.executable,'-B']
    run('literal-table-audit',py+[ROOT/'transport/generate_tables.py','--check','--output',out/'literal-table.json'])
    run('context-family-audit',py+[ROOT/'comparison/audit_context_family.py','--old',ROOT/'transport/old.tm',
                                '--new',ROOT/'transport/new.tm','--output',out/'context-family.json'])
    args=py+[ROOT/'state_reduction/code/reproduce.py','--output',out/'reduction']
    if a.full_search:args+=['--full-search']
    if a.context_search:args+=['--context-search']
    run('reduction-checks',args)
    if a.proofs:
        run('rank-proof',py+[ROOT/'rocq_seed_rank/reproduce.py','--out',out/'rank-proof'])
        run('literal-context-adapter',py+[ROOT/'adapter/build.py','--native-dir',ROOT/'transport',
                                          '--out',out/'context-proof','--lock',out/'compiler.lock'])
    report['status']='PASS';save();print('All requested checks PASS',flush=True)
if __name__=='__main__':main()
