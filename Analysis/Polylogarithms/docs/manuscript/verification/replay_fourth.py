"""Replay new certificates in isolated copies; preserve all delivered evidence."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time
B = Path(__file__).resolve().parents[1]
names = {'jets':'integral-distribution-reflection-jets',
         'integral':'integral-distribution-reflection',
         'fractional':'fractional-cayley-scaling',
         'threshold':'real-order-threshold',
         'golden':'finite-golden-uniform-continuation'}
ap = argparse.ArgumentParser(); ap.add_argument('--part', choices=names, required=True)
a = ap.parse_args(); source = B.parent/'reports'/names[a.part]
root = B/'verification/.scratch-fourth'/a.part
out = B/'verification/fourth-replay'/a.part
root.parent.mkdir(parents=True, exist_ok=True); out.mkdir(parents=True, exist_ok=True)
shutil.copytree(source, root, dirs_exist_ok=True, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
start = time.time_ns(); runs = []
def run(program, *args):
    env = dict(os.environ, PYTHONUTF8='1', PYTHONIOENCODING='utf-8',
               PYTHONDONTWRITEBYTECODE='1', PYTHONPATH=str(root))
    p = subprocess.run([sys.executable, str(root/program), *args], cwd=root, env=env,
                       capture_output=True, text=True, encoding='utf-8', errors='replace')
    (out/(Path(program).stem+'-run.txt')).write_text((p.stdout+p.stderr).rstrip()+'\n', encoding='utf-8')
    runs.append(dict(program=program, arguments=list(args), exit_code=p.returncode))
    print(a.part, program, 'exit', p.returncode, flush=True)
    if p.returncode: raise RuntimeError('Replay failed: '+str(out))
if a.part == 'jets':
    for p in ['verify_certificates.py','test_exact.py','test_smith.py']: run('code/'+p)
elif a.part == 'integral':
    for p in ['run_checks.py','check_resolution.py','check_short_identities.py',
              'check_smith.py','check_products_and_controls.py']: run('code/'+p)
    run('code/verify_certificates.py','data/normal_forms_q12.json')
elif a.part == 'fractional': run('code/run_verification.py')
elif a.part == 'threshold': run('code/certify.py')
else:
    run('code/verify_all.py')
    run('code/canonical_reconstruction_check.py','--dps','160','--terms','600')
fresh = []
for p in sorted(root.rglob('*.json')):
    if p.stat().st_mtime_ns < start: continue
    rel=p.relative_to(root); q=out/rel; q.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p,q); fresh.append(rel.as_posix())
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(source.rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part, source_folder=names[a.part],
    source_code_sha256=manifest, commands=runs, fresh_result_files=fresh,
    passed=all(c['exit_code']==0 for c in runs),
    scope='Exact finite certificates, Smith calculations and labeled notation diagnostics; analytic theorems require manuscript audit.'), indent=2)+'\n', encoding='utf-8')
print(a.part,'completed;',len(fresh),'fresh JSON receipts.')
