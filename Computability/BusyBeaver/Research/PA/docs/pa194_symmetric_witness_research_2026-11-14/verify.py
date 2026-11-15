#!/usr/bin/env python3
"""Reproduce the new symmetric-witness constructions and checks offline."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, time

ROOT=Path(__file__).resolve().parent
NAMES=('PA194H5XS','PA194JH5XS')

def main():
    assert __debug__ and not sys.flags.optimize
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work',type=Path,required=True)
    a=p.parse_args();work=a.work.resolve()
    assert not work.exists(), 'Choose a new work directory.'
    work.mkdir(parents=True)
    logs=work/'logs';logs.mkdir()
    results=[]
    def run(label,args):
        started=time.monotonic()
        with (logs/(label+'.log')).open('w') as f:
            result=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,
                                  stdout=f,stderr=subprocess.STDOUT)
        assert result.returncode==0,(label,'see',logs/(label+'.log'))
        results.append(dict(check=label,status='PASS',seconds=time.monotonic()-started))
        print(label, 'PASS', flush=True)
    run('construction',[ROOT/'construction/build_symmetric.py','--output',work/'machines'])
    core=('machine.tm','machine.native.tm','raw.native.tm','labels.json',
          'nodes.json','grammar.tree.json','folds.json','sites.json','instructions.json')
    for name in NAMES:
        candidate=work/'machines'/name
        for file in core:
            assert (candidate/file).read_bytes()==(ROOT/'machines'/name/file).read_bytes(),(name,file)
        run(name+'_emitter',[ROOT/'check_emitter.py',candidate,'--output',candidate/'emitter.json'])
        run(name+'_source',[ROOT/'verification/source/check_source_commands.py',
                           '--machine',candidate,'--output',candidate/'source_command'])
    run('literal',[ROOT/'verification/check_literal.py',*[work/'machines'/n for n in NAMES],
                   '--output',work/'literal'])
    for name in NAMES:
        candidate=work/'machines'/name
        shutil.copytree(work/'literal'/name,candidate/'independent')
        run(name+'_closure',[ROOT/'verification/physical_ipra_audit.py',
                            '--machine',candidate,'--output',candidate/'physical_ipra_audit.json'])
        assert (candidate/'independent/contracts.json').read_bytes()==(
            ROOT/'machines'/name/'independent/contracts.json').read_bytes(),name
    result=dict(status='PASS',checks=results,scope='Finite construction, source and symbolic literal execution checks; inherited absolute calibration is a written mathematical theorem, not kernel-checked by this script.')
    (work/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
