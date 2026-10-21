"""Run only the reviewed maintained producer in scratch; preserve both terminals."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
P=Path(__file__).resolve().parent;S=Path('/tmp/k215-generic-cd52/production')
G=S/'generate_dominated_implication_lean.py';EXPECTED='49099c1c05e6a18a6c500a46f190545abfa441330ddeee7880a39ac7af9f077d'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(G)==EXPECTED
inputs={str(p):sha(p)for p in S.rglob('*')if p.is_file()}
out=P/'generated';assert not out.exists();runs=[]
for label,flags in [('generate',[]),('check',['--check'])]:
 cmd=[sys.executable,str(G),'--out',str(out),*flags];start=time.monotonic()
 r=subprocess.run(cmd,cwd=S,capture_output=True,timeout=120)
 stdout=P/(label+'.stdout.json');stderr=P/(label+'.stderr.txt');stdout.write_bytes(r.stdout);stderr.write_bytes(r.stderr)
 rec={'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-start,'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),'producer_sha256':EXPECTED}
 runs.append(rec);(P/'producer-execution.json').write_text(json.dumps({'runs':runs},indent=2)+'\n')
 assert r.returncode==0 and not r.stderr,rec
 parsed=json.loads(r.stdout);assert parsed['generic_sha256']=='5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f';assert parsed['adapter_sha256']=='8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378'
assert all(sha(p)==h for p,h in inputs.items())
assert sha(out/'BusyBeaver/ZFC/DominatedImplication.lean')=='5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f'
assert sha(out/'BusyBeaver/ZFC/DomRho8.lean')=='8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378'
result={'status':'PASS_EXACT_MAINTAINED_PRODUCER_REPRODUCTION','runs':runs,'inputs':inputs,'reviewer_sha256':sha(__file__),'original_supplied_renderer_or_search_executed':False,'compiled_proof_bytes_reproduced_exactly':True,'scope':'Reviewed maintained producer only; two successful scratch terminal runs, generation and exact check. No canonical writes or proof compilation.'}
(P/'producer-execution.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['inputs','runs']},indent=2))
