"""Verify the final early-return-to-conditional-block transformation."""
import ast,concurrent.futures,hashlib,io,json,platform,subprocess,sys,tokenize
from pathlib import Path
ROOT=Path(__file__).resolve().parent
source=ROOT/'strict_tokens_candidate.py';candidate=ROOT/'strict_ast_candidate.py'
t=ast.parse(source.read_text());f=next(n for n in t.body if isinstance(n,ast.FunctionDef))
check=f.body[1]
assert isinstance(check,ast.If) and isinstance(check.test,ast.Compare) and isinstance(check.test.ops[0],ast.In)
assert len(check.body)==1 and isinstance(check.body[0],ast.Return) and check.body[0].value is None
check.test.ops[0]=ast.NotIn();check.body=f.body[2:];f.body=f.body[:1]+[check]
assert ast.dump(t)==ast.dump(ast.parse(candidate.read_text()))
prior=json.loads((ROOT/'token_refinement_validation.json').read_text())
expected={(r['optimized'],r['fixture']):r['accepted'] for r in prior['results'] if r['program']=='strict_candidate'}
fixtures=json.loads((ROOT/'fixtures/index.json').read_text())
def run(task):
 optimized,fixture=task;cmd=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])+[str(candidate)]
 try:
  r=subprocess.run(cmd,input=(ROOT/'fixtures'/fixture['name']).read_bytes(),capture_output=True,timeout=8)
  accepted=r.returncode==0 and r.stdout==b'ACCEPT\n'
  return {'optimized':optimized,'fixture':fixture['name'],'accepted':accepted,'expected':expected[optimized,fixture['name']],'passed':accepted==expected[optimized,fixture['name']]}
 except subprocess.TimeoutExpired:return {'optimized':optimized,'fixture':fixture['name'],'passed':False,'timeout':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:results=list(pool.map(run,[(o,f) for o in [False,True] for f in fixtures]))
s=ast.unparse(ast.parse(candidate.read_text()))+'\n';skip={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
metrics={'tokens':sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(s).readline)),'ast_nodes':sum(1 for _ in ast.walk(ast.parse(s))),'normalized_bytes':len(s.encode()),'sha256':hashlib.sha256(candidate.read_bytes()).hexdigest()}
report={'python':platform.python_version(),'metrics':metrics,'process_executions':len(results),'failures':[r for r in results if not r['passed']],'structural_transform_checked':True,'results':results}
(ROOT/'ast_refinement_validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
if report['failures']:sys.exit(1)
