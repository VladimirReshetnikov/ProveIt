"""Independent Robinson-style CD checker; does not import search code."""
import json,re
from pathlib import Path
D=Path(__file__).parent
r=json.loads((D/'bounded_cd_refined_result.json').read_text())

def parse(s):
 ts=re.findall(r'\d+|T|[()>]',s);i=0
 def go():
  nonlocal i
  t=ts[i];i+=1
  if t=='(':
   a=go();assert ts[i]=='>';i+=1;b=go();assert ts[i]==')';i+=1;return (a,b)
  return int(t) if t.isdigit() else t
 out=go();assert i==len(ts);return out

def norm(t):
 if not isinstance(t,tuple):return t
 a,b=map(norm,t)
 return 'T' if a=='T' and b=='T' else (a,b)

def rename(t,prefix):
 return tuple(rename(x,prefix) for x in t) if isinstance(t,tuple) else prefix+str(t) if isinstance(t,int) else t

def isvar(t):return isinstance(t,str) and t!='T'
def has(t,v):return t==v or isinstance(t,tuple) and any(has(x,v) for x in t)
def repl(t,v,u):
 if t==v:return u
 return norm(tuple(repl(x,v,u) for x in t)) if isinstance(t,tuple) else t

def canon(t):
 vs={}
 def go(x):
  if isinstance(x,tuple):return norm(tuple(go(y) for y in x))
  if isvar(x):
   if x not in vs:vs[x]=len(vs)
   return vs[x]
  return x
 return go(t)

def cd(major,minor):
 major=rename(major,'m');minor=rename(minor,'n')
 assert isinstance(major,tuple)
 todo=[(major[0],minor)];out=major[1]
 while todo:
  a,b=todo.pop(0)
  if a==b:continue
  if isvar(a) or isvar(b):
   if not isvar(a):a,b=b,a
   assert not has(b,a),(a,b)
   todo=[(repl(x,a,b),repl(y,a,b))for x,y in todo]
   out=repl(out,a,b)
  else:
   assert isinstance(a,tuple) and isinstance(b,tuple),(a,b)
   todo.extend(zip(a,b))
 return canon(out)

def I(a,b):return norm((a,b))
def L(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
seeds={'U=0':L(0,1,2,'T'),'U=A':L(0,1,2,0),'A=D→U':L(I(3,0),1,2,0),'A=U→D':L(I(0,3),1,2,0),'truth0':'T'}
# Canonicalize integer variables by the same mathematical alpha convention.
def icanon(t):return canon(rename(t,'v'))
fs=r['formulas'];terms=[]
for f in fs:
 t=parse(f['term']);p=f['parent']
 if 'seed'in p:expected=icanon(seeds[p['seed']])
 else:
  assert p['major']<len(terms) and p['minor']<len(terms)
  expected=cd(terms[p['major']],terms[p['minor']])
 assert expected==t,(f['id'],expected,t)
 terms.append(t)
proofs={}
for name,idx in r['found'].items():
 seen=set()
 def walk(j):
  if j in seen:return
  seen.add(j);p=fs[j]['parent']
  if 'major'in p:walk(p['major']);walk(p['minor'])
 walk(idx)
 proofs[name]={'root':idx,'nodes':len(seen),'dag':[fs[j]for j in sorted(seen)]}
(D/'checked_basis_fragments.json').write_text(json.dumps({'checked':len(terms),'proofs':proofs},indent=2))
print(json.dumps({'checked':len(terms),'proofs':{k:{x:y for x,y in v.items() if x!='dag'} for k,v in proofs.items()}},indent=2))
