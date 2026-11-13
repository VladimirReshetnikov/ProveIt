import ast,gzip,hashlib,io,json,subprocess,sys,tokenize
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT
OUT=ROOT/'fixtures/shifted';OUT.mkdir(exist_ok=True)
def shift(x):
 if type(x) is int:return x+2 if x>0 else x
 if type(x) is list:return [shift(y) for y in x]
 return x
def translate(x):
 y=shift(x)
 for packet,old in zip(y[:-1],x[:-1]):
  if old[0]==[]:packet[0]=0
 return y
def run(program,payload,opt):
 p=subprocess.run([sys.executable,'-I','-S','-B']+(['-O']if opt else[])+[str(program)],input=json.dumps(payload).encode(),capture_output=True,timeout=10)
 return {'accepted':p.returncode==0 and p.stdout==b'ACCEPT\n','exception':p.stderr.decode(errors='replace').splitlines()[-1]if p.stderr else'', 'exit_code':p.returncode}
results=[]
for fixture in sorted((SOURCE/'fixtures/original').glob('*.json')):
 old=json.loads(fixture.read_text());new=translate(old)
 (OUT/fixture.name).write_text(json.dumps(new,separators=(',',':'))+'\n')
 expect=not fixture.name.startswith(('reject_','future_witness'))
 for opt in (False,True):
  for name,path,payload in [('control469',SOURCE/'controls/checker469.py',old),('candidate468',ROOT/'checker468.py',new),('readable',ROOT/'checker_readable.py',new)]:
   result=run(path,payload,opt);results.append(dict(fixture=fixture.name,variant=name,optimized=opt,expected=expect,**result))
   if expect:
    bad=payload[:-1]+[[[0,[0]],0]]
    result=run(path,bad,opt);results.append(dict(fixture=fixture.name,variant=name,optimized=opt,expected=False,kind='false-goal',**result))
metrics=[]
for path in [SOURCE/'controls/checker469.py',ROOT/'checker468.py',ROOT/'checker_readable.py']:
 s=ast.unparse(ast.parse(path.read_text()))+'\n';b=s.encode();metrics.append(dict(file=str(path.relative_to(ROOT)),tokens=sum(t.type not in {tokenize.ENCODING,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER,tokenize.COMMENT}for t in tokenize.generate_tokens(io.StringIO(s).readline)),ast_nodes=len(list(ast.walk(ast.parse(s)))),normalized_bytes=len(b),gzip9_bytes=len(gzip.compress(b,compresslevel=9,mtime=0)),sha256=hashlib.sha256(b).hexdigest()))
fail=[r for r in results if r['accepted']!=r['expected']]
(ROOT/'evidence/verification.json').write_text(json.dumps(dict(python=sys.version,metrics=metrics,results=results,failures=fail),indent=2)+'\n')
print(json.dumps(dict(executions=len(results),unexpected=len(fail),metrics=metrics),indent=2))
assert not fail,fail
