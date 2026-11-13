"""Verify eager substitution and the empty-list administrative certificate.

Fixtures are translated only at neutral-major packet fields. No public
formula or numerical field changes. Expected results refer to successful
normal execution printing exactly ACCEPT plus a newline.
"""
from pathlib import Path
import ast,concurrent.futures,gzip,hashlib,io,json,subprocess,sys,tokenize
HERE=Path(__file__).resolve().parent
OLD=HERE
PAIRS=[
 ('byte','controls/checker_bytes597.py','code/checker_bytes589.py','fixtures/strict_cases.json'),
 ('tokens','controls/checker_tokens317.py','code/checker_tokens315.py','fixtures/supply_cases.json'),
 ('ast','controls/checker_ast356.py','code/checker_ast353.py','fixtures/supply_cases.json')]

def metrics(p):
 t=ast.parse(p.read_text());s=(ast.unparse(t)+'\n').encode();ignored={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
 return {'tokens':sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(s.decode()).readline)), 'ast_nodes':len(list(ast.walk(t))),'normalized_bytes':len(s),'gzip9':len(gzip.compress(s,compresslevel=9,mtime=0)),'sha256':hashlib.sha256(s).hexdigest()}

def translate(document,profile,candidate):
 if type(document) is not list:return document
 result=[]
 for row in document[:-1]:
  if type(row) is list and len(row)==4:
   m,s,u,t=row
   if candidate and type(m) is int and m==0:m=[]
   row=[s,u,t,m] if profile=='byte' else [m,s,u,t]
  result.append(row)
 return result+document[-1:]

def run(job):
 profile,case,path,candidate,opt=job
 data=translate(case['certificate'],profile,candidate)
 p=subprocess.run([sys.executable,*(['-O'] if opt else []),str(path)],input=json.dumps(data),text=True,capture_output=True,timeout=30)
 good=p.returncode==0 and p.stdout=='ACCEPT\n'
 return {'profile':profile,'case':case['name'],'candidate':candidate,'optimized':opt,'expected':case['expected'],'accepted':good,'returncode':p.returncode}

def exact_rewrites():
 for old,new in [('checker_tokens317.py','checker_tokens315.py'),('checker_ast356.py','checker_ast353.py')]:
  source=(HERE/'controls'/old).read_text()
  expected=source.replace('(d % 2 or not g) and i(t, d=3)','d % 2 * i(t, d=3)').replace("g += b'\\x00'",'g += [[]]')
  assert ast.dump(ast.parse(expected))==ast.dump(ast.parse((HERE/'code'/new).read_text()))
 source=(HERE/'controls/checker_bytes597.py').read_text()
 expected=(source.replace('def c(g, a, k=0, v=0):','def c(g, a, k=0):')
  .replace('len(a) ** v in (1, 2 + d % 2)','(g or len(a) in (1, 2 + d % 2))')
  .replace('v <= d & a % 2','(g or d & a % 2)')
  .replace('d % 2 | v and i(t, d=3)','d % 2 * i(t, d=3)')
  .replace('in ((v := 0), *g,','in (g.append([]), *g,')
  .replace('c([], q(), v=1)','c([], q())'))
 assert ast.dump(ast.parse(expected))==ast.dump(ast.parse((HERE/'code/checker_bytes589.py').read_text()))
 return True

def main():
 exact_rewrites()
 jobs=[];measurements={};counts={}
 for profile,control,candidate,fixture in PAIRS:
  cases=json.loads((OLD/fixture).read_text())['cases']
  # Known relaxed-validator failure and native grammar boundary tests.
  if profile=='byte':
   for name,goal in [('bad_D_D_scalar',[[0]]),('bad_D_D_negative',[[-1]]),('bad_empty_formula',[]),('bad_scalar_formula',0),('false_zero_one',[1,[1]])]:
    cases.append({'name':name,'expected':False,'certificate':[[0,0,0,0]]*4+[goal]})
  counts[profile]=len(cases)
  paths=[(OLD/control,False),(HERE/candidate,True)]
  if profile=='byte':paths.append((HERE/'code/readable_checker.py',True))
  for path,flag in paths:measurements[str(path.relative_to(HERE))]=metrics(path)
  jobs.extend((profile,case,path,flag,opt) for case in cases for path,flag in paths for opt in (False,True))
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(run,jobs))
 bad=[r for r in results if r['expected']!=r['accepted']]
 receipt={'python':sys.version,'scope':'Inherited canonical-rule and malformed-input tests with empty-neutral translation; not arbitrary-trace equivalence','exact_source_rewrites':True,'cases':counts,'process_runs':len(results),'measurements':measurements,'failures':bad,'results':results}
 (HERE/'evidence/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
 if bad:raise SystemExit(1)
if __name__=='__main__':main()
