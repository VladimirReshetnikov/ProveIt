"""Replay the incoming mathematics in isolated copies, preserving all inputs."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
B=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=['rigidity','distribution','conductor','complement','reflection'],required=True)
a=ap.parse_args()
folders=dict(rigidity='rigidity-and-reflected-moments',distribution='distribution-jets',conductor='conductor-descent',complement='complementary-depth',reflection='reflection-euler-tornheim')
source=B.parent/'reports'/folders[a.part]
root=B/'verification/.scratch-incoming'/a.part
out=B/'verification/incoming-replay'/a.part
root.parent.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
shutil.copytree(source,root,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
start=time.time_ns();runs=[]
def run(program,*args):
 env=dict(os.environ,PYTHONUTF8='1',PYTHONPATH=str(root))
 p=subprocess.run([sys.executable,str(root/program),*args],cwd=root,env=env,
                  capture_output=True,text=True,encoding='utf-8',errors='replace')
 transcript=p.stdout+p.stderr
 (out/(Path(program).stem+'-'+str(len(runs))+'-run.txt')).write_text(transcript.rstrip()+'\n',encoding='utf-8')
 runs.append(dict(program=program,arguments=list(args),exit_code=p.returncode))
 if p.returncode:raise RuntimeError(program+' failed; inspect fresh transcript')
if a.part=='rigidity':run('code/run_checks.py')
elif a.part=='distribution':
 run('code/verify_exact.py','--max-q','60')
 run('code/verify_characters.py','--max-q','60')
 run('code/verify_s4_presentation.py');run('code/replay_certificate.py')
 for group in ['traces','stieltjes','s4']:run('code/verify_numeric.py','--group',group,'--dps','55')
elif a.part=='conductor':
 for name in ['verify_exact.py','verify_s4_obstruction.py','verify_trace_coefficients.py','verify_numeric.py']:run('src/'+name)
elif a.part=='complement':
 for name in ['check_exact.py','check_numerical.py','certify_gaussian.py','audit_s4_rows.py','replay_certificates.py']:run('code/'+name)
else:
 run('scripts/certify_s6.py','--output','data/s6_rational_certificate.json')
 run('scripts/verify_relation_spaces.py','--output','data/relation_space_certificates.json')
 run('scripts/verify_moments.py','--dps','180','--output','data/moment_checks.json')
 run('scripts/verify_herglotz.py','--dps','70','--output','data/herglotz_checks.json')
 run('scripts/verify_tornheim.py','--dps','80','--degree','120','--diagonal','240','--output','data/tornheim_checks.json')
 for name in ['verify_analytic_identities','verify_s6_mellin','series_crosscheck']:
  filename=dict(verify_analytic_identities='analytic_identity_checks',verify_s6_mellin='s6_mellin_check',series_crosscheck='series_crosscheck')[name]
  run('scripts/'+name+'.py','--output','data/'+filename+'.json')
results=[]
for p in sorted(root.rglob('*.json')):
 if '__pycache__' in p.parts or p.stat().st_mtime_ns<start:continue
 rel=p.relative_to(root);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);results.append(rel.as_posix())
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for folder in ['code','src','scripts'] for p in sorted((source/folder).rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_folder=folders[a.part],source_code_sha256=manifest,
 commands=runs,fresh_result_files=results,passed=all(x['exit_code']==0 for x in runs),
 scope='Written analytic proofs, exact finite certificates and numerical diagnostics have distinct evidence scopes.'),indent=2)+'\n',encoding='utf-8')
print(a.part,'completed;',len(results),'fresh JSON result files.')
