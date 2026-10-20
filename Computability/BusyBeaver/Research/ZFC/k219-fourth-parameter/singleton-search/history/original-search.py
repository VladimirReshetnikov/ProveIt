#!/usr/bin/env python3
"""Three-value singleton-index matrix diagnostic for rho8(A,B,C,R(A,B)).

Every relational atom has value f, every equality atom e, and every All has
one unary operation q. Negation is ONLY I(x,f), with no extra Boolean law.
Literal req/clos/nks/bundle222 are kept; no quantifier designatedness premise.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,signal,time
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
CODE=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean'
KCODE=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean'
F,T,X=0,1,2
VALUES=range(3)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def timeout(signum,frame):raise TimeoutError('Hard60-second deadline')

# Independent declarative transcription of the exact code-constructor trees.
# Label arguments disappear because all indices have the same unary q and
# all membership/equality atoms are constant; matrix c remains variable.
def imp(a,b):return ('I',a,b)
def q(a):return ('Q',a)
def neg(a):return imp(a,'f')
def ex(a):return neg(q(neg(a)))
REQ=q(imp('m',neg(q(imp('m',neg('f'))))))
SUB=q(imp('f','f'))
CLOS=q(imp('f',neg(q(imp('m',neg(q(imp(SUB,REQ))))))))
NKS=q(imp(CLOS,neg(REQ)))
VREL=imp('f',q('f'))
BUNDLE=neg(imp(VREL,NKS))
ROWS={
 'rho1':ex('e'),
 'rho2':imp(q(imp('b','c')),imp(q('b'),q('c'))),
 'rho3':imp('e',imp('f','f')),
 'rho4':imp(q(q('c')),q(q('c'))),
 'rho5':imp('e',imp('f','f')),
 'rho6':imp(ex(q('b')),'b'),
 'G':imp('e',imp('e',q('e'))),
 'rho8':imp(imp(imp('c','u'),'a'),imp(imp('a','c'),imp('b','c'))),
 'bundle':BUNDLE,
}
def ast_eval(n,env,table,quant):
 if isinstance(n,str):return env[n]
 if n[0]=='Q':return quant[ast_eval(n[1],env,table,quant)]
 return table[3*ast_eval(n[1],env,table,quant)+ast_eval(n[2],env,table,quant)]
def closure(table,quant,e):
 s={F,T,e}
 while True:
  z=s|{quant[a] for a in s}|{table[3*a+b] for a in s for b in s}
  if z==s:return tuple(sorted(s))
  s=z

def formulas(table,quant,e):
 def I(a,b):return table[3*a+b]
 def N(a):return I(a,F)
 def E(a):return N(quant[N(a)])
 def req(m):return quant[I(m,N(quant[I(m,N(F))]))]
 def clos(m):return quant[I(F,N(quant[I(m,N(quant[I(quant[I(F,F)],req(m))]))]))]
 def nks(m):return quant[I(clos(m),N(req(m)))]
 def bundle(m):return N(I(I(F,quant[F]),nks(m)))
 def rho8(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
 return I,N,E,req,clos,nks,bundle,rho8

def common(table,quant,e,s):
 I,N,E,req,clos,nks,bundle,rho8=formulas(table,quant,e)
 if E(e)!=T:return 'rho1'
 if any(I(quant[I(b,c)],I(quant[b],quant[c]))!=T for b in s for c in s):return 'rho2'
 if I(e,I(F,F))!=T:return 'rho3_rho5'
 if any(I(quant[quant[c]],quant[quant[c]])!=T for c in s):return 'rho4'
 if any(I(E(quant[b]),b)!=T for b in s):return 'rho6'
 if I(e,I(e,quant[e]))!=T:return 'G'
 if any(bundle(m)!=T for m in s):return 'literal_bundle'
 return None

def independent_validate(table,quant,e,s):
 env={'f':F,'e':e,'a':F,'b':F,'c':F,'u':F,'m':F}
 I,N,E,req,clos,nks,bundle,rho8=formulas(table,quant,e)
 for m in s:
  env['m']=m
  assert ast_eval(REQ,env,table,quant)==req(m)
  assert ast_eval(CLOS,env,table,quant)==clos(m)
  assert ast_eval(NKS,env,table,quant)==nks(m)
  assert ast_eval(BUNDLE,env,table,quant)==bundle(m)
 for a,b,c,u in itertools.product(s,repeat=4):
  env.update(a=a,b=b,c=c,u=u)
  assert ast_eval(ROWS['rho8'],env,table,quant)==rho8(a,b,c,u)
 for b,c in itertools.product(s,repeat=2):
  env.update(b=b,c=c)
  for name in ('rho1','rho2','rho3','rho4','rho5','rho6','G'):
   assert ast_eval(ROWS[name],env,table,quant)==T,(name,env)
 for m in s:
  env['m']=m;assert ast_eval(BUNDLE,env,table,quant)==T
 for a,b,c in itertools.product(s,repeat=3):
  env.update(a=a,b=b,c=c,u=F);assert ast_eval(ROWS['rho8'],env,table,quant)==T


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
 assert __debug__ and not a.output.exists()
 a.output.mkdir(parents=True);(a.output/'search.py').write_bytes(Path(__file__).read_bytes())
 sources={str(p):sha(p) for p in (CODE,KCODE)}
 for p in (CODE,KCODE):(a.output/p.name).write_bytes(p.read_bytes())
 signal.signal(signal.SIGALRM,timeout);signal.alarm(60);start=time.monotonic()
 # Classical Boolean subalgebra control: retained rows hold; the true-matrix
 # singleton seed bundle fails. Third value is unreachable in this control.
 control=tuple(T if x==F else y for x in VALUES for y in VALUES)
 cq=(F,T,X);cs=closure(control,cq,T);assert cs==(F,T)
 assert common(control,cq,T,cs)=='literal_bundle'
 assert all(formulas(control,cq,T)[-1](a,b,c,u)==T for a,b,c,u in itertools.product(cs,repeat=4))
 models=[];full=[];stats=[];stop=None
 try:
  for e in (T,F,X):
   stat={'e':e,'enumerated':0,'common_pass':0,'restricted_pass':0,'full_pass':0,'first_failures':{}}
   stats.append(stat)
   # I(t,t)=t and I(t,x)!=t for x!=t enforce truth alias and MP globally.
   for tf,tx in itertools.product((F,X),repeat=2):
    for other in itertools.product(VALUES,repeat=6):
     table=(other[0],other[1],other[2],tf,T,tx,other[3],other[4],other[5])
     for qf,qx in itertools.product(VALUES,repeat=2):
      quant=(qf,T,qx);stat['enumerated']+=1;s=closure(table,quant,e)
      failure=common(table,quant,e,s)
      if failure is not None:
       stat['first_failures'][failure]=stat['first_failures'].get(failure,0)+1;continue
      stat['common_pass']+=1;rho8=formulas(table,quant,e)[-1]
      if not all(rho8(a,b,c,F)==T for a,b,c in itertools.product(s,repeat=3)):
       stat['first_failures']['restricted_rho8']=stat['first_failures'].get('restricted_rho8',0)+1;continue
      stat['restricted_pass']+=1;independent_validate(table,quant,e,s)
      full_ok=all(rho8(a,b,c,u)==T for a,b,c,u in itertools.product(s,repeat=4))
      m={'e':e,'implication':[list(table[i:i+3]) for i in (0,3,6)],'q':list(quant),'reachable':list(s),'full_rho8':full_ok,'id':len(models)}
      models.append(m);dump(a.output/f'model-{m["id"]:03d}.json',m);print('MODEL',json.dumps(m),flush=True)
      if full_ok:stat['full_pass']+=1;full.append(m)
   assert stat['enumerated']==26244
   dump(a.output/f'e{e}.json',stat);print('DONE_E',json.dumps(stat),flush=True)
 except TimeoutError as exc:stop=str(exc)
 finally:signal.alarm(0)
 assert all(sha(Path(p))==h for p,h in sources.items()),'Source changed'
 result={'status':'COMPLETE_3_VALUE_SINGLETON_SEARCH' if stop is None else 'INCOMPLETE_TIMEOUT','elapsed_seconds':time.monotonic()-start,'hard_timeout_seconds':60,'f':F,'t':T,'carrier':[F,T,X],'eq_order':[T,F,X],'stats':stats,'models':models,'full_unrestricted_control_models':full,'total_enumerated':sum(s['enumerated'] for s in stats),'sources':sources,'script_sha256':sha(Path(__file__)),'literal_ast':{'req':REQ,'clos':CLOS,'nks':NKS,'vrel':VREL,'bundle':BUNDLE,**ROWS},'control':'Boolean reachable subalgebra validates all retained nonbundle rows and unrestrictedrho8; literal true-matrix seed bundle fails.','scope':'Finite matrix search, not Tarski classical semantics. All atoms R=f, Eq=e; all binders share unaryq. No Boolean negation, Q reflection or Q designatedness-iff constraint imposed. Complete absence is bounded to this3-value family; a model would need code-evaluation/derivation induction for a consistency theorem.'}
 dump(a.output/'result.json',result);print(json.dumps({k:v for k,v in result.items() if k not in ('literal_ast','models','sources')},indent=2),flush=True)
 if stop:raise SystemExit(2)
if __name__=='__main__':main()
