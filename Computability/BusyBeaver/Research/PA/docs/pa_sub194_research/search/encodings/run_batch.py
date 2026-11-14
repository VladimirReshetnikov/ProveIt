#!/usr/bin/env python3
"""Run the two bounded representation-changing folds on eight 194 machines."""
from pathlib import Path
import concurrent.futures,json,subprocess,time
HERE=Path(__file__).resolve().parent
runtime=HERE/'reference/symbolic_runtime.py'
machines=json.loads((HERE/'machine_manifest.json').read_text())
started=time.monotonic()
def worker(m):
    out=HERE/(m['name']+'_r6');out.mkdir(exist_ok=True)
    input_dir=HERE/m['input_dir']
    args=['python3',str(HERE/'derive_contexts.py'),'--machine-dir',str(input_dir),'--runtime',str(runtime),'--radius','6','--physical',m['physical'],'--output',str(out)]
    with (out/'derive.stdout').open('w') as stdout,(out/'derive.stderr').open('w') as stderr:
        subprocess.run(args,stdout=stdout,stderr=stderr,check=True)
    ctx=json.loads((out/'contexts.json').read_text())
    checks={}
    for name in ('fold_shift','fold_bitphase'):
        with (out/(name+'.stdout')).open('w') as stdout,(out/(name+'.stderr')).open('w') as stderr:
            subprocess.run([str(HERE/name),str(input_dir/'machine.tm'),str(out/'contexts.txt'),'128'],stdout=stdout,stderr=stderr,check=True)
        lines=(out/(name+'.stdout')).read_text().splitlines()
        checks[name]=dict(summary=lines[-1],survivors=[s for s in lines if s.startswith('PASS ')])
    result=dict(name=m['name'],sha256=m['sha256'],radius=6,max_child_steps=128,source_context_count=ctx['source_context_count'],coarse_context_count=ctx['coarse_context_count'],source_contracts=ctx['source_contracts'],startup_steps=ctx['startup_steps'],checks=checks)
    (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
    return result
results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    fs={pool.submit(worker,m):m for m in machines}
    for f in concurrent.futures.as_completed(fs):
        try:results.append(f.result())
        except Exception as e:
            print(json.dumps(dict(name=fs[f]['name'],error=repr(e))),flush=True)
            results.append(dict(name=fs[f]['name'],error=repr(e)))
result=dict(scope='Bounded local-fold search. A failure to find a witness is not a state lower bound. Inherited source interpreter and arithmetic-box contracts are assumed.',seconds=time.monotonic()-started,results=results)
(HERE/'batch_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print('COMPLETE',len(results),time.monotonic()-started,flush=True)
