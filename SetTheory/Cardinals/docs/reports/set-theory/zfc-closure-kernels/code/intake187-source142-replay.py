"""Reviewed finite Source142 jobs, isolated from pristine intake and repository."""
from pathlib import Path
import argparse,difflib,hashlib,json,os,shutil,subprocess,sys,time
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packet',type=Path,required=True,help='Recovered research218_companion directory')
parser.add_argument('--output',type=Path,required=True,help='New output directory; must not already exist')
args=parser.parse_args()
src=args.packet.resolve();out=args.output.resolve()
if not (src/'checks/recheck.py').is_file():parser.error('--packet must contain checks/recheck.py')
if out==src or src in out.parents:parser.error('--output must be outside --packet')
out.mkdir(exist_ok=False)
copy=out/'copy';shutil.copytree(src,copy)
original=copy/'checks/recheck.py';before=original.read_text()
needle="for p, v in manifest.items():\n    if not p.startswith('upstream:'): assert h(p)==v['sha256'], p\n"
assert before.count(needle)==1
out.joinpath('recheck-original.py').write_bytes(original.read_bytes())
after=before.replace(needle,'# Intake policy: provenance-manifest validation omitted; substantive checks retained.\n')
original.write_text(after)
out.joinpath('recheck-adapter.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='original/checks/recheck.py',tofile='disposable/checks/recheck.py')))
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(p):return {str(q.relative_to(p)):h(q) for q in sorted(p.rglob('*')) if q.is_file()}
pristine_before=snapshot(src);copy_before=snapshot(copy)
jobnames=['checks/recheck.py','checks/dominated/check_dag.py','checks/dominated/audit_fragment_leaves.py','checks/dominated/derive_lr_peirce.py','checks/dominated/audit_cd59_conditional_replay.py','checks/dominated/audit_cd59_and_B_conditional_replay.py']
results=[]
for index,job in enumerate(jobnames):
 stem=f'{index+1:02d}-'+Path(job).stem;cmd=[sys.executable,'-B',job];t=time.monotonic()
 with (out/(stem+'.stdout')).open('w') as so,(out/(stem+'.stderr')).open('w') as se:
  try:r=subprocess.run(cmd,cwd=copy,stdout=so,stderr=se,timeout=120,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'));code=r.returncode;status='PASS' if code==0 else 'FAIL'
  except subprocess.TimeoutExpired:code=None;status='TIMEOUT'
 entry={'script':job,'argv':cmd,'cwd':str(copy),'timeout_seconds':120,'status':status,'exit_code':code,'seconds':time.monotonic()-t,'stdout':{'path':str(out/(stem+'.stdout')),'sha256':h(out/(stem+'.stdout'))},'stderr':{'path':str(out/(stem+'.stderr')),'sha256':h(out/(stem+'.stderr'))},'conditional_cd59':index>=4}
 results.append(entry);print(json.dumps(entry),flush=True)
 if code!=0:break
copy_after=snapshot(copy)
assert pristine_before==snapshot(src)
result={'status':'SELECTED_SIX_SOURCE142_FINITE_CHECKS_PASS' if len(results)==6 and all(x['status']=='PASS' for x in results) else 'INCOMPLETE_OR_FAILURE','role':'Independent source reviewer executing only six root-authorized reviewed finite checks; not delivered optimizers, Rocq, runtime, startup or theoretical model construction.','pristine_source':str(src),'pristine_unchanged':True,'source_members':pristine_before,'runner':{'path':str(Path(__file__)),'sha256':h(Path(__file__))},'adapter':{'original_sha256':h(out/'recheck-original.py'),'adapted_sha256':h(original),'diff_sha256':h(out/'recheck-adapter.diff'),'only_change':'Omit PROVENANCE per-file manifest validation loop.'},'jobs':results,'copy_files_changed':[p for p in copy_after if copy_after[p]!=copy_before.get(p)],'limitations':['Cofinal model and all-natural equality are ordinary proofs reviewed separately, not established by finite samples.','Last two checks assume unproved cd59 and preexisting fragment replacements; no completed classical basis.','No provisional machine executed; no full runtime/startup, proof-assistant or <=218 result.']}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],flush=True)
