from pathlib import Path
import ast,hashlib,json,math
ROOT=Path(__file__).resolve().parent.parent
FILES=['checker.py']
BASE=ROOT/'code'
VALUES=[None,True,False,'','x',{},-100,-5,-2,-1,0,1,2,3,4,5,10,100,-100.0,-5.0,-2.0,-1.0,-.5,0.0,.5,1.0,2.0,3.0,4.0,5.0,10.0,100.0,float('nan'),float('inf'),float('-inf')]
def typed(a):
 return type(a) in (int,bool) or type(a) is list and all(map(typed,a))
def hasfloat(a):
 return type(a) is float or type(a) is list and any(map(hasfloat,a))
def kernel(file):
 t=ast.parse(file.read_text()); keep=[]
 for n in t.body:
  if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id in ('k','i') for x in n.targets):keep.append(n)
 ns={};exec(compile(ast.Module(body=keep,type_ignores=[]),str(file),'exec'),ns)
 return ns
out={}
for name in FILES:
 ns=kernel(BASE/name);cases=0;returns=0;errors=[]
 for k in (0,-1,-5):
  ns['k']=k
  for d in (-3,-1,0,1,2,3,5,7):
   for v in VALUES:
    for a in (v,[v],[v,1],[1,1,v],[[v]]):
     cases+=1
     try:r=ns['i'](a,d=d)
     except Exception:continue
     returns+=1
     if not typed(a) or not typed(r):errors.append(('missing_image',k,d,repr(a),repr(r)))
 for k in (0,-1,-5):
  ns['k']=k
  for d in (-3,-1,0,1,2,3,5,7):
   for v in VALUES:
    for image in (0,1,[1],-1,[-1],[1,1,3],.5,100.0,float('nan'),''):
     for a in (v,[v],[v,1],[1,1,v]):
      cases+=1
      try:r=ns['i'](a,image,d)
      except Exception:continue
      returns+=1
      if not typed(r):errors.append(('general_output',k,d,repr(a),repr(image),repr(r)))
 # Witnesses for the distinction between typed-source and typed-output.
 examples=[]
 for a,image,d in [(100.5,1,3),(float('nan'),[1],3),(-100.5,1,3),([100.5,1],[1],0),(100.5,1,0),(1.0,1,3)]:
  ns['k']=-5
  try:r=ns['i'](a,image,d);examples.append({'source':repr(a),'image':repr(image),'depth':d,'result':r})
  except Exception as e:examples.append({'source':repr(a),'image':repr(image),'depth':d,'rejection':type(e).__name__})
 out[name]={'candidate_sha256':hashlib.sha256((BASE/name).read_bytes()).hexdigest(),'opener_checks':cases,'successful_returns':returns,'unexpected':errors,'illustrative_cases':examples}
print(json.dumps(out,indent=2))
(ROOT/'evidence/retained_opener_audit.json').write_text(json.dumps(out,indent=2)+'\n')
assert all(not v['unexpected'] for v in out.values())
