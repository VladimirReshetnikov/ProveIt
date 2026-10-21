#!/usr/bin/env python3
"""Independent schema-matching audit of the padding proof and exact code bound.

Does not import or execute the submitted proof generator or checker.
The arithmetic calculation expands the literal Cantor encoding in Q[i,b],
then certifies strict positivity from nonnegative integer coefficients.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import json,hashlib,argparse

def need(x,m):
 if not x:raise ValueError(m)
def I(x,y):return ('imp',x,y)
def Q(x,y):return ('all',x,y)
def P(x):return ('?',x)
def N(x):return I(x,('const',1))
def R(i,b):return I(N(Q(i,N(Q(i,b)))),b)
def matches(pattern,term,env=None):
 if env is None:env={}
 if pattern[0]=='?':
  v=pattern[1]
  if v not in env:env[v]=term;return env
  return env if env[v]==term else None
 if not isinstance(term,tuple)or pattern[0]!=term[0]or len(pattern)!=len(term):return None
 for p,t in zip(pattern[1:],term[1:]):
  if isinstance(p,tuple):
   env=matches(p,t,env)
   if env is None:return None
  elif p!=t:return None
 return env

def add(x,y):
 out=x.copy()
 for k,v in y.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items()if v}
def scale(x,c):return{k:v*c for k,v in x.items()if v*c}
def mul(x,y):
 out={}
 for (a,b),v in x.items():
  for (c,d),w in y.items():
   k=a+c,b+d;out[k]=out.get(k,0)+v*w
 return{k:v for k,v in out.items()if v}
def numeral(n):return{(0,0):Fraction(n)}if n else{}
def cantor(x,y):
 s=add(x,y);return add(scale(mul(s,add(s,numeral(1))),Fraction(1,2)),y)
def polynomial_bound():
 i={(1,0):Fraction(1)};b={(0,1):Fraction(1)};e=add(i,numeral(1));w=scale(cantor(e,e),4);m=scale(cantor(w,b),4)
 need(w=={(2,0):8,(1,0):24,(0,0):16},'identity-code equation')
 lower=scale(w,4);gap=add(lower,scale(i,-1));need(gap=={(2,0):32,(1,0):95,(0,0):64},'claimed loose bound expansion')
 diff=add(m,scale(lower,-1));strict=add(m,scale(i,-1))
 for name,p in [('M-4W',diff),('4W-i',gap),('M-i',strict)]:
  need(all(v.denominator==1 and v>=0 for v in p.values()),name+' nonnegative integer coefficients')
 need(gap.get((0,0),0)>0 and strict.get((0,0),0)>0,'positive constants')
 encode=lambda p:[{'i_degree':a,'b_degree':b,'coefficient':int(v)}for(a,b),v in sorted(p.items(),reverse=True)]
 return dict(identity=encode(w),padding_minus_binder=encode(strict),padding_minus_four_identity=encode(diff),claimed_lower_bound_minus_binder=encode(gap),scope='Exact formal polynomial identities with nonnegative integer coefficients, valid for every natural i,b.')

def check(path):
 d=json.loads(path.read_text());need(d['format']=='quantifier_padding_v1','format');terms=[]
 for j,t in enumerate(d['terms']):
  tag=t[0]
  if tag=='var':need(len(t)==2 and t[1]in('i','b'),'variable');x=tuple(t)
  elif tag=='const':need(len(t)==2 and type(t[1])is int and t[1]>=0,'numeral');x=tuple(t)
  else:
   need(tag in('imp','all','succ'),'term constructor');need(len(t)==(2 if tag=='succ' else 3),'term arity');need(all(type(k)is int and 0<=k<j for k in t[1:]),'term topological order');x=(tag,*(terms[k]for k in t[1:]))
  terms.append(x)
 A,B,C,J=P('A'),P('B'),P('C'),P('J')
 schemes={'K':I(A,I(B,A)),'S':I(I(A,I(B,C)),I(I(A,B),I(A,C))),'rho2':I(Q(J,I(A,B)),I(Q(J,A),Q(J,B))),'rho6_strict':R(J,A)}
 rules=Counter();proof=[];strict=[]
 for j,n in enumerate(d['nodes']):
  need(n['id']==j and type(n['term'])is int and 0<=n['term']<len(terms),'proof id');f=terms[n['term']];ps=n['parents'];kind=n['rule'];rules[kind]+=1
  need(all(type(k)is int and 0<=k<j for k in ps),'proof topological order')
  if kind=='MP':
   need(len(ps)==2,'MP arity');major,minor=[proof[k]for k in ps];need(major==I(minor,f),'exact MP equation')
  elif kind=='GEN':
   need(len(ps)==1 and f[0]=='all' and f[2]==proof[ps[0]],'GEN premise');need(f[1]==('var','i'),'GEN binder')
  else:
   need(kind in schemes and not ps,'axiom kind and absence of hypotheses');env=matches(schemes[kind],f);need(env is not None,kind+' schema')
   if kind=='rho6_strict':
    binder=env['J'];matrix=env['A'];need(binder==('var','i'),'restricted binder');e=('succ',binder);need(matrix==I(I(e,e),('var','b')),'restricted padded matrix');strict.append(j)
  proof.append(f)
 need(type(d['root'])is int and 0<=d['root']<len(proof),'root index');need(proof[d['root']]==R(('var','i'),('var','b')),'unrestricted root conclusion');need(strict==[86],'single permitted rho6 premise')
 used=set();todo=[d['root']]
 while todo:
  j=todo.pop()
  if j in used:continue
  used.add(j);todo.extend(d['nodes'][j]['parents'])
 need(used==set(range(len(proof))),'complete dependency closure')
 return dict(status='INDEPENDENT_QUANTIFIER_PADDING_PASS',certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),proof_nodes=len(proof),term_nodes=len(terms),rule_counts=dict(rules),restricted_rho6_nodes=strict,unrestricted_rho6_axiom_used=False,all_nodes_dependency_relevant=True,arithmetic=polynomial_bound(),scope='All-natural symbolic Hilbert derivation relative to K,S,rho2,closed GEN,MP, and strictly allowed rho6 instances. No binary machine, no automatic validation of upstream K/S derivation, no proof-assistant endpoint.')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--out',type=Path);a=ap.parse_args();r=check(a.certificate);raw=json.dumps(r,indent=2)+'\n';print(raw,end='');a.out.write_text(raw)if a.out else None
