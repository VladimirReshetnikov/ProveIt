"""Independent finite semantic and scope audit of the triplicate kernel.

Reads a reviewed kernel, executes its declarations only, and checks its
opener against independent named syntax. This is not a universal proof.
"""
from pathlib import Path
import ast,copy,hashlib,itertools,json,math,random,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
CANDIDATE=ROOT/'code/checker_bytes.py'
EXCEPTIONS=(Exception,)

def kernel_namespace(path):
 tree=ast.parse(path.read_text())
 # Keep only reviewed declarations; omit the public JSON/CLI driver.
 body=[]
 for n in tree.body:
  if isinstance(n,ast.Try):break
  body.append(n)
 ns={};exec(compile(ast.Module(body=body,type_ignores=[]),str(path),'exec'),ns)
 return ns


def numeral(term,env=(),parameters=None,budget=None):
 if parameters is None:parameters={-5:0,-4:3,-3:2,-2:1,-1:0}
 if budget is None:budget=[1800]
 budget[0]-=1
 if budget[0]<0:raise OverflowError('evaluation budget')
 if isinstance(term,list):
  n=len(term)
  if n==0 or n==2 or n>=4:return 0
  if n==1:return 1+numeral(term[0],(0,0)+env,parameters,budget)
  counter=numeral(term[0],(0,)+env,parameters,budget)
  value=numeral(term[1],(0,)+env,parameters,budget)
  if counter>60:raise OverflowError('counter cap')
  for unused in range(counter):value=numeral(term[2],(value,)+env,parameters,budget)
  return value
 if term<0:return parameters[math.floor(term)]
 if term<3:return 0
 return env[math.floor((term-3)/2)]


def generated_supply(ns,source,mode):
 ns['k']=-4
 predecessor,seed,update=copy.deepcopy(source)
 equation=[[mode and [predecessor],seed,update],ns['i'](update,source,3) if mode else seed]
 ns['k']=-5
 return ns['i'](equation,-5)

# Independent named AST and encoder. No production encoder is imported.
def v(name):return ('var',name)
def suc(x):return ('suc',x)
def itr(n,a,u,h):return ('iter',n,a,u,h)
def eq(s,t):return ('eq',s,t)
def closure(y,b):return ('closure',y,b)
def pair(x,y,b):return ('pair',x,y,b)

def replace(t,name,value):
 if t==0:return 0
 tag=t[0]
 if tag=='var':return value if t[1]==name else t
 if tag=='suc':return suc(replace(t[1],name,value))
 if tag=='iter':return itr(replace(t[1],name,value),replace(t[2],name,value),t[3],t[4] if t[3]==name else replace(t[4],name,value))
 if tag=='eq':return eq(replace(t[1],name,value),replace(t[2],name,value))
 if tag=='closure':return t if t[1]==name else closure(t[1],replace(t[2],name,value))
 if tag=='pair':return t if name in t[1:3] else pair(t[1],t[2],replace(t[3],name,value))
 raise ValueError(tag)

PARAMS={'p':-1,'q':-2,'r':-3,'old':-4,'fresh':-5}
def encode_term(t,scope=(),exposed=None):
 if t==0:return 0
 tag=t[0]
 if tag=='var':
  name=t[1]
  if name in scope:return 3+2*scope.index(name)
  if name==exposed:return 3+2*len(scope)
  return PARAMS[name]
 if tag=='suc':return [encode_term(t[1],(None,None)+scope,exposed)]
 if tag=='iter':return [encode_term(t[1],(None,)+scope,exposed),encode_term(t[2],(None,)+scope,exposed),encode_term(t[4],(t[3],)+scope,exposed)]
 raise ValueError(tag)

def encode_formula(f,scope=(),exposed=None):
 if f[0]=='eq':return [encode_term(t,scope,exposed) for t in f[1:]]
 if f[0]=='closure':return [encode_formula(f[2],(f[1],)+scope,exposed)]*3
 if f[0]=='pair':return [encode_formula(f[3],(f[2],f[1])+scope,exposed)]
 raise ValueError(f)


def binding_checks(ns):
 records=[]
 def check(name,actual,expected):
  if actual!=expected:raise AssertionError({'name':name,'actual':actual,'expected':expected})
  records.append({'name':name,'pass':True})
 x,y,p,q=v('x'),v('y'),v('p'),v('q')
 matrices=[
  eq(x,y),eq(suc(x),suc(y)),eq(itr(y,x,'u',suc(v('u'))),suc(x)),
  closure('z',eq(itr(v('z'),x,'u',suc(v('u'))),itr(y,p,'v',x))),
  pair('w','z',eq(itr(v('z'),x,'u',itr(y,v('u'),'v',suc(v('v')))),v('w'))),
  closure('z',pair('w','b',eq(itr(v('b'),x,'u',v('z')),itr(y,v('w'),'v',suc(v('v'))))))]
 witnesses=[0,suc(0),suc(suc(0)),p,itr(p,q,'j',suc(v('j'))),itr(suc(0),p,'j',v('j'))]
 for a,matrix in enumerate(matrices):
  raw=encode_formula(matrix,('y','x'))
  for b,witness in enumerate(witnesses):
   ns['k']=-4;opened=ns['i'](raw,encode_term(witness),2)
   after_x=replace(matrix,'x',witness)
   check(f'DI_witness_{a}_{b}',opened,encode_formula(after_x,('y',)))
   ns['k']=-5
   check(f'DI_successor_{a}_{b}',ns['i'](opened,[-5]),encode_formula(replace(after_x,'y',suc(v('fresh')))))
   check(f'DI_zero_{a}_{b}',ns['i'](opened,0),encode_formula(replace(after_x,'y',0)))
   check(f'DI_current_{a}_{b}',ns['i'](opened,-5),encode_formula(replace(after_x,'y',v('fresh'))))
  ns['k']=-5
  check(f'DE_both_coordinates_{a}',ns['i']([raw]*3,-5),encode_formula(closure('y',replace(matrix,'x',v('fresh')))))
  body=replace(matrix,'x',p)
  for b,witness in enumerate(witnesses):
   ns['k']=-4
   check(f'QE_{a}_{b}',ns['i'](encode_formula(body,('y',)),encode_term(witness)),encode_formula(replace(body,'y',witness)))
 updates=[v('u'),suc(v('u')),itr(v('u'),p,'w',suc(v('w'))),itr(p,v('u'),'w',suc(v('w'))),itr(p,q,'w',itr(v('w'),v('u'),'z',suc(v('z'))))]
 for a,update in enumerate(updates):
  for b,n in enumerate(witnesses):
   whole=itr(n,p,'u',update)
   ns['k']=-4
   check(f'IS_state_{a}_{b}',ns['i'](encode_term(update,('u',)),encode_term(whole),3),encode_term(replace(update,'u',whole)))
 return records


def main():
 ns=kernel_namespace(CANDIDATE)
 bindings=binding_checks(ns)
 atoms=list(range(-6,12))+[-4.5,-3.5,-0.5,0.5,2.5,3.5,4.5,6.5]
 leaves=atoms+[[],[0],[1],[2],[3],[4],[5],[6],[7],[8],[0,0],[0,3],[3,0]]+[[0]*n for n in range(4,11)]+[[0,0,[],0]]
 terms=leaves+[[x] for x in leaves]+[[0,0,x] for x in leaves]+[[3,0,x] for x in leaves]+[[x,0,0] for x in leaves]+[[0,x,0] for x in leaves]
 rng=random.Random(104731)
 cases=list(itertools.product(leaves,leaves,atoms+[[],[0],[3],[4],[5],[6],[7],[8]]))
 cases += [tuple(rng.choice(terms) for unused in range(3)) for unused in range(80000)]
 evaluated=rejected=limited=0;failures=[]
 parameter_sets=[{-5:0,-4:3,-3:2,-2:1,-1:0},{-5:0,-4:0,-3:3,-2:2,-1:1}]
 for source in cases:
  for mode in (0,1):
   try:h=generated_supply(ns,list(source),mode)
   except Exception:rejected+=1;continue
   for parameters in parameter_sets:
    try:left,right=(numeral(x,parameters=parameters) for x in h)
    except Exception:limited+=1;continue
    evaluated+=1
    if left!=right:
     failures.append({'source':source,'mode':mode,'hypothesis':h,'parameters':parameters,'values':[left,right]})
     if len(failures)>=10:break
   if len(failures)>=10:break
  if len(failures)>=10:break
 # A previously unsafe positional-unpack certificate must reject under
 # the new unary D protocol, where its binary goal supplies too many args.
 controls=[('old_positional_false_equation',[[0,0,0,[0,0]],[0,[0]]],False)]
 cli=[]
 for name,certificate,expected in controls:
  for candidate in ['checker_bytes.py','checker_tokens.py','checker_ast.py']:
   for optimized in [False,True]:
    path=ROOT/'code'/candidate
    command=[sys.executable]+(['-O'] if optimized else [])+[str(path)]
    run=subprocess.run(command,input=json.dumps(certificate),capture_output=True,text=True,timeout=8)
    accepted=run.returncode==0 and run.stdout=='ACCEPT\n'
    cli.append({'name':name,'candidate':candidate,'optimized':optimized,'expected':expected,'accepted':accepted,'pass':accepted==expected})
    if accepted!=expected:failures.append(cli[-1])
 # Record the semantic-only idempotence qualification, not as a failure.
 ns['k']=-1
 first=ns['i']([0]*6,-1)
 try:second=ns['i'](first);reopens=True
 except Exception:reopens=False
 result={'candidate':str(CANDIDATE.relative_to(ROOT)),'candidate_sha256':hashlib.sha256(CANDIDATE.read_bytes()).hexdigest(),'source_cases':len(cases),'mode_cases':len(cases)*2,'parameter_valuations':2,'supplies_rejected':rejected,'equations_evaluated':evaluated,'evaluations_limited_or_undefined':limited,'binding_commutations':len(bindings),'binding_checks':bindings,'cli_controls':cli,'failures':failures,'raw_idempotence_counterexample':{'floor':-1,'input':[0]*6,'image':-1,'opened':first,'reopens_without_image':reopens,'decoded_formula':'truth'},'scope':'Independent finite diagnostics; not a universal soundness or bi-interpretability proof.'}
 (ROOT/'evidence/independent_result.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='binding_checks'},indent=2))
 if failures:raise SystemExit(1)
if __name__=='__main__':main()
