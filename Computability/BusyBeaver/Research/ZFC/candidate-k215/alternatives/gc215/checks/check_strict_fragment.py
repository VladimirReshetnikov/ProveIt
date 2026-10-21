#!/usr/bin/env python3
"""Independently verify exact MP equations and all raw-zero cases of a finite
strict-dominance certificate. Does not import or execute synthesis code.
"""
import hashlib,itertools,json,sys
from pathlib import Path

def req(p,m):
 if not p:raise ValueError(m)
def I(a,b):return ('i',a,b)
def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def check(path):
 d=json.loads(path.read_text());req(d['format']=='strict_rho8_fragment_v1','format');ts=[]
 for n,t in enumerate(d['terms']):
  if t[0]=='v':req(len(t)==2 and type(t[1])is int and t[1]in (0,1),'variable');x=tuple(t)
  elif t[0]=='one':req(len(t)==1,'one');x=tuple(t)
  else:
   req(t[0]=='i' and len(t)==3,'constructor');req(all(type(j)is int and 0<=j<n for j in t[1:]),'term refs');x=I(ts[t[1]],ts[t[2]])
  ts.append(x)
 proof=[];leaves={}
 for n,p in enumerate(d['proof']):
  req(p['id']==n,'id');t=ts[p['term']];ps=p['parents'];req(all(type(j)is int and 0<=j<n for j in ps),'proof refs')
  if p['rule']=='MP':
   req(len(ps)==2,'MP count');maj,mn=[proof[j] for j in ps];req(maj[0]=='i' and maj[1]==mn and maj[2]==t,'MP equation')
  else:
   req(p['rule']=='proper_rho8' and not ps,'axiom')
   req(t[0]=='i' and t[1][0]=='i' and t[1][1][0]=='i','rho8 left')
   c,u=t[1][1][1:];a=t[1][2]
   req(t[2][0]=='i' and t[2][2][0]=='i','rho8 right');b=t[2][2][1]
   req(t==R(a,b,c,u),'rho8 full shape');req(a[0]=='i' and a[2]==u,'proper right subterm')
   leaves[n]=(a,u,t)
  proof.append(t)
 p,q=('v',0),('v',1)
 expected={'I':I(p,p),'K':I(p,I(q,p)),'P':I(I(I(p,q),p),p)}
 req(set(d['roots'])==set(expected),'root names');results={}
 def nz(t,pat):
  if t[0]=='one':return True
  if t[0]=='v':return pat[t[1]]
  return nz(t[1],pat) or nz(t[2],pat)
 def vars_(t):
  if t[0]=='one':return set()
  if t[0]=='v':return {t[1]}
  return vars_(t[1])|vars_(t[2])
 for name,root in d['roots'].items():
  req(proof[root]==expected[name],'exact root')
  need=set();todo=[root]
  while todo:
   n=todo.pop()
   if n not in need:need.add(n);todo.extend(d['proof'][n]['parents'])
  nv=1+max(vars_(proof[root]));cases=[]
  for bits in itertools.product([False,True],repeat=nv):
   if not nz(proof[root],bits):cases.append({'nonzero':bits,'reason':'target is literal truth0'});continue
   strict=truth=0
   for n in need&leaves.keys():
    a,u,t=leaves[n]
    if nz(a,bits):strict+=1  # A=I(v,U)>0 implies U<A for I=4P.
    else:req(not nz(t,bits),'non-strict nontruth axiom');truth+=1
   cases.append({'nonzero':bits,'strict_axioms':strict,'literal_truth_axioms':truth})
  results[name]={'root':root,'dependency_nodes':len(need),'unique_axiom_leaves':len(need&leaves.keys()),'zero_patterns':cases}
 return {'verdict':'PASS','scope':'I,K,Peirce only; strict-rho8 completeness is not claimed.',
  'proof_nodes':len(proof),'term_nodes':len(ts),'roots':results,
  'arithmetic_lemmas':['I(a,b)=0 iff a=b=0','I(a,b)>=4a and I(a,b)>=4b','I(v,U)>0 implies I(v,U)>U'],
  'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
  'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
if __name__=='__main__':
 p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('strict_fragment_certificate.json')
 r=check(p);print(json.dumps(r,indent=2))
 if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(r,indent=2)+'\n')
