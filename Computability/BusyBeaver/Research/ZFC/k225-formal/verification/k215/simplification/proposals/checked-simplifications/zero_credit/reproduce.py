#!/usr/bin/env python3
"""Fresh standard-library Coq build and recursive kernel check."""
import argparse, hashlib, json, shutil, subprocess, time
from pathlib import Path

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True,
                    help='fresh directory for source, compiled objects and logs')
    ap.add_argument('--coqc',default='coqc'); ap.add_argument('--coqchk',default='coqchk')
    args=ap.parse_args(); root=Path(__file__).resolve().parent
    assert not args.output.exists(), 'choose a fresh output directory'
    args.output.mkdir(parents=True)
    source=root/'TagLowering.v'; target=args.output/'TagLowering.v'
    shutil.copy2(source,target)
    results=[]
    for label,cmd in [('version',[args.coqc,'--version']),
                      ('compile',[args.coqc,'TagLowering.v']),
                      ('kernel',[args.coqchk,'-silent','TagLowering'])]:
        start=time.monotonic()
        p=subprocess.run(cmd,cwd=args.output,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (args.output/(label+'.log')).write_text(p.stdout)
        result={'stage':label,'command':cmd,'exit_code':p.returncode,
                'seconds':round(time.monotonic()-start,3)}
        results.append(result)
        print(json.dumps(result),flush=True)
        if p.returncode: raise SystemExit(p.stdout)
    reports=(args.output/'compile.log').read_text()
    assert reports.count('Closed under the global context')==5
    receipt={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
             'source_bytes':source.stat().st_size,'source_lines':len(source.read_text().splitlines()),
             'closed_assumption_reports':5,'results':results,
             'claim':'Concrete Cantor parse/encode inverse, tag-lowering injection, all finite prefix credit and positive credit before NIP.',
             'not_claimed':'Exact binary-machine/source adapter or new Lean/Rocq ZFC consistency endpoint.'}
    (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('TAG_LOWERING_KERNEL_PASS')
if __name__=='__main__': main()
