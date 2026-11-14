#!/usr/bin/env python3
"""Extend both inherited encodings simultaneously; source contexts precomputed."""
from pathlib import Path
import concurrent.futures,json,subprocess,time
HERE=Path(__file__).resolve().parent
machines=json.loads((HERE/'machine_manifest.json').read_text())
def run(m):
    out=HERE/(m['name']+'_r6')
    for _ in range(120):
        if (out/'contexts.txt').exists():break
        time.sleep(1)
    with (out/'fold_combined.stdout').open('w') as stdout,(out/'fold_combined.stderr').open('w') as stderr:
        subprocess.run([str(HERE/'fold_combined'),str(HERE/m['input_dir']/'machine.tm'),str(out/'contexts.txt'),'128'],stdout=stdout,stderr=stderr,check=True)
    lines=(out/'fold_combined.stdout').read_text().splitlines()
    r=dict(name=m['name'],summary=lines[-1],survivors=[s for s in lines if s.startswith('PASS ')])
    print(json.dumps(r),flush=True);return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(run,machines))
(HERE/'combined_receipt.json').write_text(json.dumps(dict(radius=6,max_child_steps=128,results=results),indent=2)+'\n')
