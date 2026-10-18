#!/usr/bin/env python3
"""Reproduce the 242-state machine's quick or expanded verification offline."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__: raise RuntimeError('Python assertions must remain enabled.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True,help='A fresh directory outside the delivered archive.')
    ap.add_argument('--expanded',action='store_true',help='Also replay every universal expanded instruction case.')
    a = ap.parse_args()
    output = a.output.resolve()
    if output.exists(): raise RuntimeError('Choose a fresh output directory.')
    if output == ROOT or ROOT in output.parents: raise RuntimeError('Output must be outside the archive.')
    paths = [p for directory in ['machine','code','reference'] for p in sorted((ROOT/directory).rglob('*'))
             if p.is_file() and '__pycache__' not in p.parts]
    before = {str(p.relative_to(ROOT)):sha(p) for p in paths}
    output.mkdir(parents=True)
    record = dict(status='RUNNING',expanded_requested=a.expanded,commands=[],input_hashes=before,
                  scope='Exact relative proof premises and finite replays; optional expanded ordinary symbolic induction.',
                  proof_assistant_executed=False)
    def save():
        (output/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def run(label,args):
        command=[sys.executable,'-I','-B',*map(str,args)]
        began=time.monotonic()
        with (output/(label+'.stdout.log')).open('wb')as out, (output/(label+'.stderr.log')).open('wb')as err:
            proc=subprocess.run(command,stdout=out,stderr=err,cwd=output)
        record['commands'].append(dict(label=label,command=command,exit_code=proc.returncode,seconds=time.monotonic()-began))
        save()
        if proc.returncode: raise RuntimeError('Verification failed: '+label)
    save()
    try:
        candidate=output/'machine'
        run('local-proof',[ROOT/'code/build_and_audit.py','--output',candidate])
        for name in ['zfc_return242.tm','zfc_return242_old.tm','renumbering.json']:
            assert (candidate/name).read_bytes() == (ROOT/'machine'/name).read_bytes(),name
        for name in ['sites_logical.json','sites_physical.json']:
            shutil.copyfile(ROOT/'machine'/name,candidate/name)
        run('execution',[ROOT/'code/check_execution.py','--candidate',candidate,'--output',output/'execution'])
        if a.expanded:
            run('expanded',[ROOT/'code/check_expanded.py','--candidate',candidate,
                            '--reference',ROOT/'reference/runtime','--output',output/'expanded-runtime.json'])
        after={str(p.relative_to(ROOT)):sha(p) for p in paths}
        assert before == after,'An input file changed during verification.'
        record.update(status='PASS_RETURN242_EXPANDED_REPRODUCTION' if a.expanded else 'PASS_RETURN242_QUICK_REPRODUCTION',
                      all_input_postchecks=True,table_sha256=sha(candidate/'zfc_return242.tm'),
                      local_proof_sha256=sha(candidate/'local-proof-audit.json'),
                      blank_sha256=sha(output/'execution/blank.json'),literal_sha256=sha(output/'execution/literal.json'))
        if a.expanded: record['expanded_sha256']=sha(output/'expanded-runtime.json')
    except BaseException as ex:
        record.update(status='FAIL',error=repr(ex))
        save()
        raise
    save()
    print(json.dumps({k:v for k,v in record.items() if k not in ('input_hashes','commands')},indent=2))

if __name__=='__main__':main()
