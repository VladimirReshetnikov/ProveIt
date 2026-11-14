from pathlib import Path
import subprocess, sys, time, shutil

lake=shutil.which('lake')
if not lake: raise SystemExit('Install Lean 4.35.0 and put lake on PATH.')
namespace=sys.argv[1] if len(sys.argv)>1 else 'PA196'
with open(f'build_{namespace}_coverage.log','w') as log:
    for base in range(0,239,8):
        names=[f'{namespace}.Coverage.S{i:03d}' for i in range(base,min(239,base+8))]
        print('Building',names[0],'through',names[-1],flush=True)
        p=subprocess.run([str(lake),'build',*names],stdout=log,stderr=subprocess.STDOUT)
        log.flush()
        if p.returncode:sys.exit(p.returncode)
    p=subprocess.run([str(lake),'build',f'{namespace}.PhysicalEndpoint'],stdout=log,stderr=subprocess.STDOUT)
    sys.exit(p.returncode)
