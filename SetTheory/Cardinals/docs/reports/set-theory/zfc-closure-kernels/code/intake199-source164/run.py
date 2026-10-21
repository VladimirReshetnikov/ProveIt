#!/usr/bin/env python3
"""Run seven explicitly selected Source164 leaves on a fresh disposable copy.
No wrapper, MANIFEST, ancestor execution, search, or full runtime is invoked.
The constructor reads its pinned parent archives only as immutable input data.
"""
import argparse, hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path

def identity(p):
    raw=p.read_bytes()
    return {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}

def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); source=args.packet.resolve(); out=args.output.resolve()
    if out.exists():raise SystemExit('Refusing an existing output directory')
    out.mkdir(parents=True); packet=out/'packet';shutil.copytree(source,packet)
    results=out/'outputs';results.mkdir();logs=out/'logs';logs.mkdir()
    certificate=packet/'theory/dominated_rho8_full_certificate.json'
    jobs=[
      ('construction',['candidate215/build.py','--output',str(results/'construction')]),
      ('projection',['theory/audit_projection_basis.py',str(certificate),str(results/'projection.json')]),
      ('projection-independent',['review/review_projector_certificate.py','--certificate',str(certificate),'--output',str(results/'projection-independent.json')]),
      ('context-matrix',['review/review_context_matrix.py','--output',str(results/'context-matrix.json')]),
      ('matrix-lifting',['review/review_matrix_lifting.py','--output',str(results/'matrix-lifting.json')]),
      ('residual-contracts',['theory/check_residual_contracts.py',str(results/'residual-contracts.json')]),
      ('scanner-counterexample',['review/review_short_scanner.py','--baseline',str(packet/'baseline'),'--output',str(results/'scanner-counterexample.json')]),
    ]
    selected={v[0] for _,v in jobs}|{'theory/check_classical_compact.py','theory/dominated_rho8_full_certificate.json',
      'candidate215/SOURCE_PINS.json','candidate215/recipes/table210.json','candidate215/k215.native.tm',
      'candidate215/k215.tm','candidate215/sites215.json','baseline/k217.native.tm','baseline/sites217.json'}
    pins=json.loads((packet/'candidate215/SOURCE_PINS.json').read_text())
    selected|={str((Path('candidate215')/x['relative_path'])) for x in pins['archives'].values()}
    selected|={'candidate215/inputs/'+n for n in pins['inputs']}
    selected|={'candidate215/vendor/'+n for n in pins['vendor']}
    # Normalize the one ../ archive path; no source manifest is interpreted.
    selected=sorted({str((packet/n).resolve().relative_to(packet)) for n in selected})
    before={n:identity(packet/n) for n in selected}
    original={n:identity(source/n) for n in selected}
    if before!=original:raise SystemExit('Disposable copy differs from selected original inputs')
    record={'schema':1,'scope':'Seven selected construction/finite-theory/diagnostic leaves only; no full runtime or primary blank replay',
      'packet':str(source),'disposable_packet':str(packet),'runner':identity(Path(__file__)),
      'wall_cap_seconds_per_job':60,'before':before,'original':original,'jobs':[],'status':'RUNNING'}
    write(out/'actual.json',record)
    env=dict(os.environ);env.pop('PYTHONPATH',None);env.pop('PYTHONHOME',None);env['PYTHONDONTWRITEBYTECODE']='1'
    for name,tail in jobs:
      argv=[sys.executable,'-B',str(packet/tail[0]),*tail[1:]]
      stdout=logs/(name+'.stdout');stderr=logs/(name+'.stderr');started=time.monotonic();timed_out=False
      with stdout.open('wb') as so,stderr.open('wb') as se:
        p=subprocess.Popen(argv,cwd=packet,env=env,stdout=so,stderr=se,start_new_session=True)
        try:rc=p.wait(timeout=60)
        except subprocess.TimeoutExpired:
          timed_out=True;os.killpg(p.pid,signal.SIGKILL);rc=p.wait()
      entry={'name':name,'argv':argv,'cwd':str(packet),'exit_code':rc,'timed_out':timed_out,'elapsed_seconds':time.monotonic()-started,
        'stdout':{'path':str(stdout.relative_to(out)),**identity(stdout)},'stderr':{'path':str(stderr.relative_to(out)),**identity(stderr)}}
      record['jobs'].append(entry);write(out/'actual.json',record)
      print(name,rc,round(entry['elapsed_seconds'],3),flush=True)
      if rc!=0 or timed_out:break
    record['after']={n:identity(packet/n) for n in selected}
    record['original_after']={n:identity(source/n) for n in selected}
    record['inputs_unchanged']=record['before']==record['after']==record['original_after']
    record['outputs']={str(p.relative_to(results)):identity(p) for p in sorted(results.rglob('*')) if p.is_file()}
    record['status']='PASS_PROCESS_AND_INPUT_BINDINGS' if len(record['jobs'])==len(jobs) and all(j['exit_code']==0 and not j['timed_out'] for j in record['jobs']) and record['inputs_unchanged'] else 'FAIL'
    write(out/'actual.json',record)
    if record['status']=='FAIL':raise SystemExit(1)
if __name__=='__main__':main()
