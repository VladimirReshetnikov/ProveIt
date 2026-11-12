"""Verify the backward representation of supplied-proof Name.

Translate the delivered deterministic-Export fixtures through the matched
Name control, then abstract its opened parameter into the template slot.
Also check raw-template completion and the exact Name endpoint identity.
This support script is not imported by either standalone checker.
"""
from pathlib import Path
import ast,copy,importlib.util,json,random,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
PACK=ROOT
def module(path):
    tr=ast.parse(path.read_text());tr.body=[n for n in tr.body if isinstance(n,(ast.FunctionDef,ast.Import,ast.ImportFrom))]
    ns={};exec(compile(tr,str(path),'exec'),ns);return ns
K=module(ROOT/'code/checker_backward_name.py')
N=module(PACK/'code/control_name.py')
X=module(PACK/'code/checker.py')
CTX=[([], [1,1])]
walk,sub,syntax=K['walk'],K['sub'],K['syntax']
# Deterministic Export -> explicit Name, followed by abstraction of the Name
# branch's opened parameter. Both translations are checked independently.
def named(p,g):
    n=len(g);b=-n;code,*args=p
    if type(code)is int:
        t,q=args;base,B=g[code]
        return [code,t,named(q,g) if base else None]
    if code:
        r,=args;B=sub(code,1-n,1);base=sub(B,0)
        hyp=sub(B,b) if base==[0,0] else base
        return [code,named(r,g+[([],hyp)])]
    q,r=args;D,=X['prove'](q,g);B=sub(D,b,1);base=sub(B,0);row=sub(B,[0,0,0])
    eq=[n,[0,0,0],[0,0,None]]if base==[0,0]and row[0]==b else[0,b,None]
    return[[],named(q,g),eq,named(r,g+[(base,B)])]
def backward(p,g):
    b=-len(g);code,*args=p
    if type(code)is int:
        t,q=args;base,B=g[code]
        return['u',code,t,backward(q,g)if base else None]
    if code:
        r,=args;B=sub(code,b+1,1);base=sub(B,0);hyp=sub(B,b)if base==[0,0]else base
        return['i',backward(r,g+[([],hyp)])]
    major,eq,branch=args;D,=N['prove'](major,g);B=sub(D,b,1);local=g+[(sub(B,0),B)]
    s,t=N['prove'](eq,local);assert s==b
    F=N['prove'](branch,local)
    T=walk(F,lambda i,d:d+1 if i==b else i+(i>d))
    assert sub(T,b)==F
    return['e',D,T,t,backward(major,g),backward(eq,local),backward(branch,local)]
examples={}
for path in sorted((PACK/'validation/fixtures/positive').glob('*.json')):
    goal,p=json.loads(path.read_text());np=named(p,CTX);assert N['prove'](np,CTX)==goal
    bp=backward(np,CTX);K['prove'](goal,bp,CTX);examples[path.stem]=[goal,bp]
# Auxiliary out-of-scope template parameters may be erased at both endpoints.
ONE=[0,0,0];dummy=['i',['u',0,0,None]]
for label,extra in [('free',-99),('bound',99)]:
    T=[[0,0,extra],ONE]
    p=['e',[0,0],T,-1,dummy,['u',0,-1,None],['u',0,ONE,None]]
    goal=[ONE,ONE];K['prove'](goal,p,CTX);examples['erased_extra_'+label]=[goal,p]
# The following are impossible goals or malformed endpoint/template attacks.
negative={
 'false_goal':[[0,ONE],['u',0,0,None]],
 'boolean_goal':[[False,False],['u',0,0,None]],
 'float_goal':[[0.0,0.0],['u',0,0,None]],
 'supplied_old_source':[[0,0],['e',[0,0],[0,0],0,0,dummy,['u',0,0,None],['u',0,0,None]]],
 'source_not_fresh':[[0,0],['e',[0,0],[0,0],0,dummy,['u',0,0,None],['u',0,0,None]]],
 'fresh_export':[[0,0],['e',[0,0],[1,1],-1,dummy,['u',0,-1,None],['u',0,-1,None]]],
 'active_extra_free':[[0,0],['e',[0,0],[-99,-99],-1,dummy,['u',0,-1,None],['u',0,0,None]]],
 'active_extra_bound':[[0,0],['e',[0,0],[99,99],-1,dummy,['u',0,-1,None],['u',0,0,None]]],
 'erased_boolean_template':[[ONE,ONE],['e',[0,0],[[0,0,True],ONE],-1,dummy,['u',0,-1,None],['u',0,ONE,None]]],
 'erased_wrong_arity':[[ONE,ONE],['e',[0,0],[[0,0,[0,0]],ONE],-1,dummy,['u',0,-1,None],['u',0,ONE,None]]],
}
for label,data in negative.items():
 try:K['prove'](*data,CTX)
 except Exception:pass
 else:raise AssertionError(('invalid accepted',label))
# Independently test the template-completion operation with the source fixed
# to the fresh parameter. The replacement may itself contain that parameter.
def norm(x):return walk(x,lambda i,d:i)
def complete(x,d=0):
 if type(x)is int:return 0 if x < -1 or x > d+1 else x
 return[complete(a,d+2*(len(x)!=2 and j==len(x)-1))for j,a in enumerate(x)]
rng=random.Random(1907619)
def term(k,d):
 if k<=0 or rng.randrange(3)==0:return rng.choice([-3,-2,-1,0,*range(1,d+4)])
 return[rng.choice([0,-1,d+1,d+2]),term(k-1,d),term(k-1,d+2)]
def form(k,d=0):
 if k and rng.randrange(3)==0:return[form(k-1,d+2)]
 return[term(k,d),term(k,d)]
def valid(x,fresh,form=True):
 try:syntax(x,fresh,form);return True
 except(ValueError,RecursionError):return False
trials=5000;checked=erased=self_target=0
for _ in range(trials):
 T=form(3);t=rng.choice([0,-1,ONE,[0,-1,0],[-1,0,1]])
 try:
  F,A=sub(T,-1),sub(T,t)
  if not(valid(F,-2)and valid(A,-1)):continue
  U=norm(complete(T))
  assert walk(U,lambda i,d:K['need'](-2<i<=d)or i,1,True)==U
  assert sub(U,-1)==F and sub(U,t)==A
  assert walk(F,lambda i,d:t if i==-1 else i)==A
  checked+=1;erased+=complete(T)!=T;self_target+=t in(-1,[0,-1,0],[-1,0,1])
 except RecursionError:continue
folder=ROOT/'validation/fixtures/backward_name';folder.mkdir(exist_ok=True)
for label,data in examples.items():(folder/(label+'.json')).write_text(json.dumps(data)+'\n')
cli=0
for optimized in(False,True):
 for label,data,expected in[(k,v,True)for k,v in examples.items()]+[(k,v,False)for k,v in negative.items()]:
  cmd=[sys.executable,'-I','-S','-B']+(['-O']if optimized else[])+[str(ROOT/'code/checker_backward_name.py')]
  r=subprocess.run(cmd,input=json.dumps(data).encode(),capture_output=True,timeout=20)
  accepted=r.returncode==0 and r.stdout==b'ACCEPT\n'
  assert accepted==expected,(label,optimized,r.stdout,r.stderr);cli+=1
result={'matched_Name_translations':24,'additional_erased_template_accepts':2,'negative_cases':len(negative),'CLI_runs':cli,'scope_completion':{'trials':trials,'valid_endpoint_pairs':checked,'with_erased_auxiliary_parameters':erased,'replacement_contains_fresh_parameter':self_target,'exact_Name_endpoint_checks':checked,'counterexamples':0},'limits':'The arbitrary-renaming stability lemma in the paper proves equivalence with Name, including explicit ambient occurrences and self-containing replacements. These bounded tests exercise that identity and template completion but do not prove the general metatheorems.'}
(ROOT/'evidence/backward_name_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
