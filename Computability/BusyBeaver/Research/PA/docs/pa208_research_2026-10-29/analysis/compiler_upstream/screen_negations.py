"""Bounded allocation and finite regression for direct-negation layouts."""
from pathlib import Path
import subprocess, json, sys, time

ROOT=Path(__file__).resolve().parents[2]
source_dir=ROOT/'analysis/runtime_redesign/direct_negation'
dest=ROOT/'analysis/compiler_upstream/negation_screen'
dest.mkdir(exist_ok=True)
inventory=[]
for src in sorted(source_dir.glob('n*.sites.json')):
    name=src.name.removesuffix('.sites.json')
    out=dest/name
    command=[sys.executable,'-B',str(Path(__file__).with_name('allocate_current.py')),
             str(src),str(out),'--fresh','8','--seconds','8']
    start=time.monotonic()
    run=subprocess.run(command,text=True,capture_output=True,cwd=ROOT)
    out.mkdir(exist_ok=True)
    (out/'allocator.log').write_text(run.stdout+run.stderr)
    if not (out/'allocation.json').is_file():
        inventory.append({'variant':name,'status':'ALLOCATOR_ERROR'});continue
    info=json.loads((out/'allocation.json').read_text())
    result={k:info.get(k)for k in ('status','solver','states','metrics')}
    result.update(variant=name,seconds=time.monotonic()-start)
    if (out/'candidate.native.tm').is_file():
        rows=json.loads(src.read_text())
        tsv=out/'sites.tsv'
        tsv.write_text(''.join(f'{p} {op} {arg if arg is not None else 0}\n' for p,op,arg in rows))
        trial=subprocess.run([str(ROOT/'analysis/offset_search/primitive_merge'),
             str(out/'candidate.native.tm'),str(tsv),str(out/'seen_rows.txt'),'-2'],
             text=True,capture_output=True,cwd=ROOT)
        (out/'finite.log').write_text(trial.stdout+trial.stderr)
        result['finite_pass']=trial.returncode==0
        result['finite_output']=trial.stdout+trial.stderr
    inventory.append(result)
    (dest/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
    print(json.dumps(result),flush=True)
