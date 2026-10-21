"""Emit61 small universal bootstrap lemmas directly, with no valuation/term DAG."""
import json,hashlib
from pathlib import Path
from functools import cache
P=Path(__file__).resolve().parent
d=json.loads((P/'bootstrap.json').read_text());terms=d['term_table'];nodes=d['nodes'];T='T'
@cache
def expr(i):
 t=terms[i]
 return (expr(t[0]),expr(t[1])) if isinstance(t,list) else (t['var'] if isinstance(t,dict) else T)
def norm(t):
 if not isinstance(t,tuple):return t
 a,b=map(norm,t);return T if a==T and b==T else(a,b)
def variables(t):return set().union(*map(variables,t)) if isinstance(t,tuple) else {t} if isinstance(t,int) else set()
def sub(t,e):return (sub(t[0],e),sub(t[1],e)) if isinstance(t,tuple) else e[t] if isinstance(t,int) else T
def lean(t):return '(wim '+lean(t[0])+' '+lean(t[1])+')' if isinstance(t,tuple) else 'v'+str(t) if isinstance(t,int) else '0'
def contains(a,u):return a==u or isinstance(a,tuple) and (contains(a[0],u) or contains(a[1],u))
def bound(u,a):
 if u==T:return '(Nat.zero_le _)'
 if u==a:return '(Nat.le_refl _)'
 assert isinstance(a,tuple)
 if contains(a[0],u):return '(le_l '+lean(a[1])+' '+bound(u,a[0])+')'
 assert contains(a[1],u)
 return '(le_r '+lean(a[0])+' '+bound(u,a[1])+')'
def rename(a,b,e):
 if isinstance(a,int):
  assert isinstance(b,int) and e.setdefault(a,b)==b
 elif a==T:assert b==T
 else:
  assert isinstance(b,tuple);rename(a[0],b[0],e);rename(a[1],b[1],e)
forms=[expr(n['term']) for n in nodes]
def call(i,e):
 args={v:norm(e[v]) for v in variables(forms[i])}
 raw=sub(forms[i],args); normalized=norm(raw)
 pf='(b'+str(i)+' h'+''.join(' '+lean(args[v]) for v in sorted(args))+')'
 if raw!=normalized:pf='(show T '+lean(normalized)+' from by simpa only [wim00] using '+pf+')'
 return pf,normalized
head=(P/'Bootstrap.lean').read_text().split('/-! ## Terms -/')[0]
head+='''theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]
attribute [local irreducible] wim

section
variable {T : Nat → Prop} (h : DomImp T)
include h
'''
L=[head]
for i,node in enumerate(nodes):
 f=forms[i];r=node['rule'];kind=r['kind']
 if kind=='truth':pf='h.truth'
 elif kind=='dominated_rho8':
  (cu,a),((aa,c),(b,cc))=f;ccc,u=cu;assert c==cc==ccc and a==aa
  pf='(show T '+lean(f)+' from by simpa only [Code254.rho8] using h.rho8 '+lean(a)+' '+lean(b)+' '+lean(c)+' '+lean(u)+' '+bound(u,a)+')'
 elif kind=='mp_substitution':
  ma,mi=r['major'],r['minor'];assert ma<i and mi<i
  me={int(k):expr(v) for k,v in r['major_substitution'].items()};ie={int(k):expr(v) for k,v in r['minor_substitution'].items()}
  major=sub(forms[ma],me);minor=sub(forms[mi],ie);assert isinstance(major,tuple)
  ren={};rename(norm(major[1]),f,ren);assert len(set(ren.values()))==len(ren)
  # Variables absent from the conclusion are arbitrary, so instantiate them by truth0.
  for v in variables(major)|variables(minor):ren.setdefault(v,T)
  me={v:sub(t,ren) for v,t in me.items()};ie={v:sub(t,ren) for v,t in ie.items()}
  pm,tm=call(ma,me);pi,ti=call(mi,ie)
  if tm==T:pm='(show T (wim 0 0) from by simpa only [wim00] using '+pm+')';tm=(T,T)
  assert tm==(ti,f),(i,tm,ti,f)
  pf='(h.mp '+pm+' '+pi+')'
 else:raise ValueError(kind)
 names=' '.join('v'+str(v) for v in sorted(variables(f)));bind=' ('+names+' : Nat)' if names else ''
 L.append('private theorem b'+str(i)+bind+' : T '+lean(f)+' :=\n  '+pf+'\n')
L.append('end\nend SetTheory.BusyBeaver.ZFC.DomRho8\n')
s='\n'.join(L);(P/'PlainBootstrap.lean').write_text(s)
print(json.dumps({'bytes':len(s.encode()),'lines':s.count('\n'),'proof_nodes':len(nodes),'term_definitions':0,'sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2))
