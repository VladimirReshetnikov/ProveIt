#!/usr/bin/env python3
"""Bounded native-constructor condensed detachment; own research, no Lean.

Variables range over numeric codes, including binder/atom labels. The sole
constructor alias is I(0,0)=0. No substitution inside an arbitrary theorem is
assumed: each record is a universally parametrized, explicitly instantiated
finite derivation schema. Negative search results are bounded only.
"""
import argparse, hashlib, itertools, json, time
from pathlib import Path

Z=0
def I(a,b): return norm(('I',a,b))
def R(a,b): return ('R',a,b)
def Q(a,b): return ('Q',a,b)
def E(a,b): return ('E',a,b)
F=R(0,0)
def norm(t):
 if not isinstance(t,tuple): return t
 t=(t[0],norm(t[1]),norm(t[2]))
 return 0 if t==('I',0,0) else t
def vars_(t):
 if isinstance(t,str): return {t}
 if t==0:return set()
 return vars_(t[1])|vars_(t[2])
def subst(t,s):
 if isinstance(t,str):return subst(s[t],s) if t in s else t
 if t==0:return 0
 return norm((t[0],subst(t[1],s),subst(t[2],s)))
def instantiate(t,s):
 if isinstance(t,str):return s.get(t,t)
 if t==0:return 0
 return norm((t[0],instantiate(t[1],s),instantiate(t[2],s)))
def nodes(t):return 1 if not isinstance(t,tuple) else 1+nodes(t[1])+nodes(t[2])
def unify(pairs):
 s={}; todo=list(pairs)
 while todo:
  a,b=(subst(x,s) for x in todo.pop())
  if a==b:continue
  if isinstance(b,str) and not isinstance(a,str):a,b=b,a
  if isinstance(a,str):
   if a in vars_(b):
    # Every positive I has strictly smaller fields; any occurrence cycle
    # can only collapse to zero, and only through I constructors.
    s[a]=0;todo.append((b,0))
   else:s[a]=b
   continue
  if a==0 or b==0:
   t=b if a==0 else a
   if not isinstance(t,tuple) or t[0]!='I':return None
   todo.extend(((t[1],0),(t[2],0)));continue
  if a[0]!=b[0]:return None
  todo.extend(((a[1],b[1]),(a[2],b[2])))
 return s
def positive(t):
 if t==0 or isinstance(t,str):return False
 return t[0]!='I' or positive(t[1]) or positive(t[2])
def disjoint(a,b):
 if a==0:return positive(b)
 if b==0:return positive(a)
 return isinstance(a,tuple) and isinstance(b,tuple) and a[0]!=b[0]
def conditions(cs):
 out=[]
 for a,b in cs:
  a,b=norm(a),norm(b)
  if a==b:return None
  if not disjoint(a,b) and (a,b) not in out and (b,a) not in out:out.append((a,b))
 return out
def canonical(t,cs):
 names={}
 def cv(x):
  if isinstance(x,str):
   if x not in names:names[x]='v'+str(len(names))
   return names[x]
  if x==0:return 0
  return (x[0],cv(x[1]),cv(x[2]))
 return cv(t),[(cv(a),cv(b)) for a,b in cs],names
def map_names(t,names):return subst(t,{v:names.get(v,0) for v in vars_(t)})
def neg(t):return I(t,F)
def ex(i,t):return neg(Q(i,neg(t)))
def h(a,b,c,variant):
 u=R(b,c) if variant=='bc' else R(c,b) if variant=='cb' else R(a,b)
 return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def roots(variant,bundle):
 a,b,c='a','b','c'
 out=[('truth',0,[]),('r1',ex(a,E(a,b)),[]),
 ('r2',I(Q(a,I(b,c)),I(Q(a,b),Q(a,c))),[]),
 ('r3',I(E(a,b),I(R(c,a),R(c,b))),[]),
 ('r4',I(Q(a,Q(b,c)),Q(b,Q(a,c))),[]),
 ('r5',I(E(c,a),I(R(c,b),R(a,b))),[]),
 ('r6',I(ex(a,Q(a,b)),b),[]),
 ('G',I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b)))),[]),
 ('H',h(a,b,c,variant),[])]
 if bundle:
  def req(b,k,m):return Q(b,I(m,neg(Q(b,I(m,neg(R(b,k)))))))
  sub=Q(c,I(R(c,a),R(c,b)))
  clo=Q(b,I(R(b,c),neg(Q(a,I(c,neg(Q(a,I(sub,req(b,c,c)))))))))
  d=Q(c,I(clo,neg(req(b,c,c))))
  v=I(R(a,b),Q(c,R(a,b)))
  out.append(('bundle',neg(I(v,d)),[(c,a),(c,b)]))
 return out
def pattern_matches(p,t,env=None):
 if env is None:env={}
 if isinstance(p,str):
  if p in env:return env[p]==t
  env[p]=t;return True
 if p==0:return t==0
 if t==0:return p[0]=='I' and pattern_matches(p[1],0,env) and pattern_matches(p[2],0,env)
 return isinstance(t,tuple) and p[0]==t[0] and pattern_matches(p[1],t[1],env) and pattern_matches(p[2],t[2],env)
def check_record(r,allr,rootmap):
 t,cs=r['formula'],r['conditions']
 if r['rule']=='axiom':
  u,uc=rootmap[r['axiom']]; v,vc,_=canonical(u,uc);assert (t,cs)==(v,vc)
 elif r['rule']=='gen':
  p=allr[r['parent']];s=r['substitution']
  assert t==Q(r['label'],instantiate(p['formula'],s))
  assert cs==conditions([(instantiate(a,s),instantiate(b,s)) for a,b in p['conditions']])
 else:
  p,m=(allr[r[k]] for k in ('major','minor'));ps,ms=r['major_substitution'],r['minor_substitution']
  assert instantiate(p['formula'],ps)==I(instantiate(m['formula'],ms),t)
  cc=[(instantiate(a,s),instantiate(b,s)) for q,s in ((p,ps),(m,ms)) for a,b in q['conditions']]
  assert cs==conditions(cc)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True)
 ap.add_argument('--variant',choices=['ab','bc','cb'],default='bc');ap.add_argument('--bundle',action='store_true')
 ap.add_argument('--rounds',type=int,default=3);ap.add_argument('--max-schemas',type=int,default=1000)
 ap.add_argument('--max-nodes',type=int,default=160);ap.add_argument('--seconds',type=float,default=30)
 a=ap.parse_args();assert not a.out.exists();a.out.mkdir(parents=True)
 (a.out/'condensed.py').write_bytes(Path(__file__).read_bytes());start=time.monotonic()
 rs=[];seen={};targets={};pairs=0;oversize=0;stop=None
 x,y,z='@x','@y','@z'
 goals={'F':F,'identity':I(x,x),'K':I(x,I(y,x)),
 'S':I(I(x,I(y,z)),I(I(x,y),I(x,z))),
 'Peirce':I(I(I(x,y),x),x),'EFQ':I(F,x),'top':I(x,0)}
 rr=roots(a.variant,a.bundle);rootmap={name:(t,cs) for name,t,cs in rr}
 def add(t,cs,proof):
  nonlocal oversize
  t=norm(t);cs=conditions(cs)
  if cs is None:return
  if nodes(t)>a.max_nodes:oversize+=1;return
  t,cs,names=canonical(t,cs);key=repr((t,cs))
  if key in seen:return
  r={'id':len(rs),'formula':t,'conditions':cs,**proof}
  for key2 in ('major_substitution','minor_substitution','substitution'):
   if key2 in r:r[key2]={v:map_names(w,names) for v,w in r[key2].items()}
  if 'label' in r:r['label']=map_names(r['label'],names)
  check_record(r,rs,rootmap);seen[key]=r['id'];rs.append(r)
  if not cs:
   for name,goal in goals.items():
    if name not in targets and pattern_matches(t,goal):targets[name]=r['id']
 for name,t,cs in rr:add(t,cs,{'rule':'axiom','axiom':name,'depth':0})
 previous=set();rounds=[]
 for depth in range(1,a.rounds+1):
  snapshot=list(rs);frontier=[r for r in snapshot if r['id'] not in previous];old=set(previous);previous={r['id'] for r in snapshot}
  for r in frontier:
   vv=vars_(r['formula'])|set().union(*(vars_(u)|vars_(v) for u,v in r['conditions']))
   rename={v:'g'+v for v in vv}
   add(Q('label',subst(r['formula'],rename)),[(subst(u,rename),subst(v,rename)) for u,v in r['conditions']],{'rule':'gen','parent':r['id'],'substitution':rename,'label':'label','depth':depth})
  for major,minor in itertools.product(snapshot,repeat=2):
   if major['id'] in old and minor['id'] in old:continue
   if time.monotonic()-start>a.seconds:stop='time';break
   if len(rs)>=a.max_schemas:stop='schema-cap';break
   pairs+=1
   vv=[vars_(r['formula'])|set().union(*(vars_(u)|vars_(v) for u,v in r['conditions'])) for r in (major,minor)]
   ren=[{v:p+v for v in vs} for p,vs in zip(('M','N'),vv)]
   mt,nt=[subst(r['formula'],s) for r,s in zip((major,minor),ren)]
   s=unify([(mt,I('prem','out')),(nt,'prem')])
   if s is None:continue
   bindings=[{v:subst(w,s) for v,w in re.items()} for re in ren]
   cs=[(instantiate(u,bs),instantiate(v,bs)) for r,bs in zip((major,minor),bindings) for u,v in r['conditions']]
   add(subst('out',s),cs,{'rule':'mp','major':major['id'],'minor':minor['id'],'major_substitution':bindings[0],'minor_substitution':bindings[1],'depth':depth})
  rounds.append({'depth':depth,'schemas':len(rs),'pairs':pairs,'stop':stop})
  if stop:break
 for r in rs:check_record(r,rs,rootmap)
 result={'status':'BOUNDED_SCHEMA_SEARCH','variant':a.variant,'bundle':a.bundle,'targets':targets,'schemas':len(rs),'pairs':pairs,'oversize_rejections':oversize,'rounds':rounds,'elapsed':time.monotonic()-start,'limits':{'rounds':a.rounds,'max_schemas':a.max_schemas,'max_nodes':a.max_nodes,'seconds':a.seconds},'stop':stop,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'Exact finite proof schemas checked by substitution and constructor normalization. No arbitrary theorem substitution principle. No negative completeness claim; genus/round/node/schema/time bounds apply.'}
 (a.out/'proofs.json').write_text(json.dumps(rs,indent=2)+'\n');(a.out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
