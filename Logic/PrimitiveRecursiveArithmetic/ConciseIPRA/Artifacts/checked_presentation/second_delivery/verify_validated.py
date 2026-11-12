import ast,concurrent.futures,hashlib,io,json,platform,subprocess,sys,tokenize
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
GROUPS=[(Path('tests/native'),Path('controls/native629.py'),Path('code/checker_native.py')),(Path('tests/strict/proofs'),Path('controls/strict646.py'),Path('code/checker_strict.py')),(Path('tests/strict/boundary'),Path('controls/strict646.py'),Path('code/checker_strict.py'))]
def measure(path):
 raw=(ROOT/path).read_bytes();source=ast.unparse(ast.parse(raw))+'\n';compile(source,str(path),'exec')
 return dict(path=str(path),tokens=sum(x.type not in SKIP for x in tokenize.generate_tokens(io.StringIO(source).readline)),ast_nodes=sum(1 for _ in ast.walk(ast.parse(source))),normalized_bytes=len(source.encode()),sha256=hashlib.sha256(raw).hexdigest())
def run(task):
 program,fixture,optimized,expected=task
 command=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else[])+[str(ROOT/program)]
 try:
  r=subprocess.run(command,input=(ROOT/fixture).read_bytes(),capture_output=True,timeout=10)
  accepted=r.returncode==0 and r.stdout==b'ACCEPT\n'
 except subprocess.TimeoutExpired:
  accepted=False
 return dict(program=str(program),fixture=str(fixture),optimized=optimized,expected=expected,accepted=accepted,passed=accepted==expected)
def main():
 tasks=[];paths=[]
 for folder,control,candidate in GROUPS:
  paths.extend([control,candidate])
  cases=json.loads((ROOT/folder/'cases.json').read_text())
  for case in cases:
   for program in (control,candidate):
    for optimized in (False,True): tasks.append((program,folder/case['file'],optimized,case['expected']))
 with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: rows=list(pool.map(run,tasks))
 report=dict(python=platform.python_version(),metrics=[measure(p)for p in dict.fromkeys(paths)],executions=len(rows),failures=[r for r in rows if not r['passed']],results=rows)
 (ROOT/'evidence/validated_results.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k!='results'},indent=2))
 if report['failures']:raise SystemExit(1)
if __name__=='__main__':main()
