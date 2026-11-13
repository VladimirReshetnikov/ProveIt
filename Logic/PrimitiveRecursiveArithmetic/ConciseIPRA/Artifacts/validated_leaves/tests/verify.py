from pathlib import Path
import copy,json,subprocess,sys,ast,io,tokenize,gzip,hashlib
BASE=Path(__file__).resolve().parent.parent
CHECKERS=['checker_strict606.py','checker_native579.py']

def run(name,data,opt=False):
 p=subprocess.run([sys.executable]+(['-O'] if opt else [])+[str(BASE/"code"/name)],input=json.dumps(data),text=True,capture_output=True,timeout=10)
 return p.returncode==0 and p.stdout=='ACCEPT\n'

positive=[(p.stem,json.loads(p.read_text())) for p in sorted((BASE/'fixtures').glob('*.json'))]
positive.append(('direct_zero',[[0,0,1,1],[[1,1,1],1]]))
negative=[
 ('false_zero_equals_one',[[0,0,1,1],[1,[1]]]),
 ('wrong_compute_endpoint',[[0,0,1,1],[[1,1,1],[1]]]),
 ('future_capture',[[0,0,1,1],[[-1,1],-1,1,[3,[1]]],[1,[1]]]),
 ('public_old_zero',[[0,0,1,1],[0,0]]),
 ('public_even_alias',[[0,0,1,1],[2,2]]),
 ('public_free_hole',[[0,0,1,1],[3,3]]),
 ('public_Q',[[0,0,1,1],[[1,1],[1,1],[1,1]]]),
 ('public_empty_term',[[0,0,1,1],[[],[]]]),
 ('public_negative_parameter',[[0,0,1,1],[-1,-1]]),
 ('missing_packet',[[1,1,1],1]),
]
for name,data in positive:
 bad=copy.deepcopy(data);bad[-1]=[1,[1]]
 negative.append(('false_goal_mutation_'+name,bad))
results=[]
for checker in CHECKERS:
 for opt in [False,True]:
  for name,data in positive:
   actual=run(checker,data,opt);results.append({'checker':checker,'optimized':opt,'case':name,'expected':True,'actual':actual})
  for name,data in negative:
   actual=run(checker,data,opt);results.append({'checker':checker,'optimized':opt,'case':name,'expected':False,'actual':actual})
  for typ,obj in [('float',1.0),('bool',True),('null',None),('string','unused'),('object',{'x':1})]:
   data=[obj]+copy.deepcopy(positive[-1][1])
   expected=checker=='checker_native579.py'
   actual=run(checker,data,opt);results.append({'checker':checker,'optimized':opt,'case':'unused_prefix_'+typ,'expected':expected,'actual':actual})
metrics={}
for name in CHECKERS:
 s=ast.unparse(ast.parse((BASE/"code"/name).read_text()))+'\n';b=s.encode()
 ts=[z for z in tokenize.generate_tokens(io.StringIO(s).readline) if z.type not in [tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER]]
 metrics[name]={'tokens':len(ts),'ast':len(list(ast.walk(ast.parse(s)))),'bytes':len(b),'gzip9':len(gzip.compress(b,compresslevel=9,mtime=0)),'sha256':hashlib.sha256(b).hexdigest()}
summary={'python':sys.version,'metrics':metrics,'executions':len(results),'unexpected':[r for r in results if r['expected']!=r['actual']],'results':results}
(BASE/'evidence/verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='results'},indent=2))

if summary["unexpected"]:
 raise SystemExit("Unexpected checker outcome")
