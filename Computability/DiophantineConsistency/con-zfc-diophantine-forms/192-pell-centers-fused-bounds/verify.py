#!/usr/bin/env python3
"""Run the finite checks for every new equation, without searching for roots."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time

ROOT=Path(__file__).resolve().parent

def execute(relative,*args):
    command=[sys.executable,'-B']
    env=os.environ.copy()
    if sys.flags.optimize:
        command.append('-O');env['PYTHONOPTIMIZE']=str(sys.flags.optimize)
    command += [str(ROOT/relative),*map(str,args)]
    start=time.monotonic()
    r=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,env=env)
    if r.returncode:raise RuntimeError(relative+'\n'+r.stdout+'\n'+r.stderr)
    result=json.loads(r.stdout)
    return {'seconds':round(time.monotonic()-start,3),'result':result}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--checksums',action='store_true',help='also authenticate the complete frozen file manifest')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args()
    checks={
      'quartic212':execute('quartic212/verify.py',
        '--source',ROOT/'quartic212/source210.json',
        '--raw',ROOT/'quartic212/equation',
        '--reduced',ROOT/'quartic212/reduced','--mutations'),
      'literal_appendix':execute('quartic212/check_printed.py'),
      'projected':execute('projected/verify_all.py'),
      'projected_reconstruction':execute('projected/rebuild_all.py'),
      'compact13':execute('compact13/verify.py')}
    total=0
    if a.checksums:
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            expected,relative=line.split('  ',1)
            path=ROOT/relative
            if not path.resolve().is_relative_to(ROOT.resolve()):raise ValueError('Manifest path escapes package')
            if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
                raise ValueError('Checksum mismatch: '+relative)
            total+=1
    result={'status':'PASS','python_optimized':bool(sys.flags.optimize),
      'checks':checks,'authenticated_manifest_files':total,
      'scope':'Exact finite artifacts and reconstruction only. Ordinary unbounded proofs and inherited calibrations are identified in the report.'}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
