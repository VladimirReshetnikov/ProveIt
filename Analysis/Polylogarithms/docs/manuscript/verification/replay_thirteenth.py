"""Replay selected thirteenth-intake cores on fresh temporary copies.
All other deliveries retain explicit pending full-replay and analytic scopes.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={'exact-resonant':('stieltjes-harmonic-resonance/continuations/exact-resonant-identities',['certificates/cayley/code/verify_complete_cayley.py']), 'parity':('stieltjes-harmonic-resonance/continuations/harmonic-parity-resolvents',['code/verify_all.py','--full'])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);args=a.parse_args();folder,command=plans[args.part]
source=B.parent/'reports'/folder;root=Path(tempfile.mkdtemp(prefix='polylog-thirteenth-replay-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
out=V/'thirteenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);assert not os.environ.get('PYTHONOPTIMIZE');started=time.time_ns()
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1')
p=subprocess.run([sys.executable,*command],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8');(out/'full-run.txt').write_text(p.stdout+p.stderr,encoding='utf-8');print(p.stdout[-5000:]);assert p.returncode==0
fresh=[]
for q in sorted(root.rglob('*.json')):
    if q.stat().st_mtime_ns<started:continue
    rel=q.relative_to(root);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target);fresh.append(rel.as_posix())
if args.part=='exact-resonant':
    shutil.copyfile(root/'certificates/cayley/verification.json',out/'complete-cayley-verification.json');fresh.append('complete-cayley-verification.json')
record=dict(part=args.part,source_folder=folder,commands=[dict(arguments=command,exit_code=p.returncode)],fresh_result_files=fresh,source_code_sha256={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*.py')},passed=True,scope='Selected exact full-Cayley certificate or full five-script harmonic-parity/resolvent suite. Finite replay is separate from all-order analytic acceptance and does not complete the other sixteen reports.')
(out/'replay-summary.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print('Fresh replay complete:',args.part,len(fresh))
