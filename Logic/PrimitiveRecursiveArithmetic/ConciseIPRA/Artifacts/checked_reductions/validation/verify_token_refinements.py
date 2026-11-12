"""Reproduce the two source-level refinements; no network access required."""
import ast,concurrent.futures,hashlib,io,json,platform,subprocess,sys,tokenize
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROGRAMS={'strict_control':'selected/strict_tokens_control.py','strict_candidate':'strict_tokens_candidate.py','native_control':'selected/native_tokens_control.py','native_candidate':'native_tokens_candidate.py'}
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
def metrics(path):
 data=path.read_bytes();s=ast.unparse(ast.parse(data))+'\n'
 return {'tokens':sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(s).readline)),'ast_nodes':sum(1 for _ in ast.walk(ast.parse(s))),'normalized_bytes':len(s.encode()),'sha256':hashlib.sha256(data).hexdigest()}
fixtures=[{**row,'path':ROOT/'fixtures'/row['name']} for row in json.loads((ROOT/'fixtures/index.json').read_text())]
def run(task):
 program,optimized,fixture=task;cmd=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])+[str(ROOT/PROGRAMS[program])]
 try:
  r=subprocess.run(cmd,input=fixture['path'].read_bytes(),capture_output=True,timeout=8)
  accepted=r.returncode==0 and r.stdout==b'ACCEPT\n'
  return {'program':program,'optimized':optimized,'fixture':fixture['name'],'accepted':accepted,'exit_code':r.returncode,'strict_expected':fixture['strict_expected']}
 except subprocess.TimeoutExpired:return {'program':program,'optimized':optimized,'fixture':fixture['name'],'accepted':False,'timeout':True,'strict_expected':fixture['strict_expected']}
tasks=[(program,optimized,fixture) for program in PROGRAMS for optimized in [False,True] for fixture in fixtures]
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:results=list(pool.map(run,tasks))
index={(r['program'],r['optimized'],r['fixture']):r for r in results};failures=[]
for optimized in [False,True]:
 for fixture in fixtures:
  for family in ['strict','native']:
   a=index[family+'_control',optimized,fixture['name']];b=index[family+'_candidate',optimized,fixture['name']]
   if a['accepted']!=b['accepted'] or 'timeout' in a or 'timeout' in b:failures.append({'family':family,'fixture':fixture['name'],'optimized':optimized,'reason':'parity_or_timeout'})
  for program in ['strict_control','strict_candidate']:
   a=index[program,optimized,fixture['name']]
   if a['accepted']!=fixture['strict_expected']:failures.append({'program':program,'fixture':fixture['name'],'optimized':optimized,'reason':'strict_expectation'})
# Structural proof obligation: the strict change is exactly the sentinel expression.
control=(ROOT/PROGRAMS['strict_control']).read_text()
expected=control.replace("q = not str(p).strip('0123456789-[], ') and p.pop", "q = str(p).strip('0123456789-[], ') or p.pop").replace('(not a or a > 1 == a % 2)', 'a % 2 == (a > 1)')
assert ast.dump(ast.parse(expected))==ast.dump(ast.parse((ROOT/'strict_tokens_candidate.py').read_text()))
control=(ROOT/PROGRAMS['native_control']).read_text()
expected=control.replace('(not a or a > 1 == a % 2)', 'a % 2 == (a > 1)')
assert ast.dump(ast.parse(expected))==ast.dump(ast.parse((ROOT/'native_tokens_candidate.py').read_text()))
# For the validating phase k=0, accepted leaves are nonnegative exact integers.
assert all(bool(not a or a>1==a%2)==bool(a%2==(a>1)) for a in range(5001))
report={'python':platform.python_version(),'metrics':{k:metrics(ROOT/v) for k,v in PROGRAMS.items()},'fixture_count':len(fixtures),'process_executions':len(results),'failures':failures,'structural_replacements_checked':True,'results':results}
(ROOT/'token_refinement_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
if failures:sys.exit(1)
