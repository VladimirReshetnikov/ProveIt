from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,datetime
S=Path('/tmp/k215-phase12-publication');O=Path(__file__).resolve().parent;P=Path('/tmp/k215-phase12-published/lean');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('mode',choices=['capture','saved']);args=a.parse_args()
f=json.loads((S/'freeze.json').read_text());assert sha(S/'freeze.json')=='23d05264e1ac30bdcb6b978526c8b3eb584d7c4d604ff68e432763a2dbfbbf45'
before={str(S/n):sha(S/n)for n in f['files']};assert before=={str(S/n):v['sha256']for n,v in f['files'].items()}
core=['basis.py','basis-reference.json','packet.py','review_saved.py','README.md','index.json','result.json','execution.tar.gz']
packet_before={n:sha(P/n)for n in core}if args.mode=='saved'else{}
cmd=['python','-B',str(S/'collect.py'),'--basis-repo',str(R),'--out',str(P)]if args.mode=='capture'else['python','-B',str(P/'review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(O/'saved-review.json')]
label=args.mode+'-v2'
out=O/(label+'.stdout.log');err=O/(label+'.stderr.log');actual=O/(label+'-actual.json');assert not any(p.exists()for p in [out,err,actual])
start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with out.open('x')as stdout,err.open('x')as stderr:
 env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';done=subprocess.run(cmd,cwd=R,env=env,stdout=stdout,stderr=stderr)
after={p:sha(p)for p in before};packet_after={n:sha(P/n)for n in core}if P.is_dir()and all((P/n).is_file()for n in core)else{}
record={'status':'OUTER_EXIT_0'if done.returncode==0 else'OUTER_FAILURE','command':cmd,'cwd':str(R),'exit_code':done.returncode,'seconds':time.monotonic()-start,'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wrapper_sha256':sha(__file__),'freeze_sha256':sha(S/'freeze.json'),'before_helpers':before,'after_helpers':after,'helpers_unchanged':before==after,'packet_before':packet_before,'packet_after':packet_after,'packet_unchanged':packet_before==packet_after if args.mode=='saved'else None,'stdout_sha256':sha(out),'stderr_sha256':sha(err),'compiler_or_producer_invoked':False}
actual.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:record[k]for k in ['status','exit_code','seconds','helpers_unchanged','packet_unchanged']},indent=2),flush=True)
assert done.returncode==0 and before==after and(args.mode!='saved'or packet_before==packet_after)
