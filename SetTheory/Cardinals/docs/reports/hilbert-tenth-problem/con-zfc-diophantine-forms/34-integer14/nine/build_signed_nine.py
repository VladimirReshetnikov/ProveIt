"""New data-only synthesis: quartic31 + coefficient folding/Horner + signed finalizer.
No received upstream Python is executed. circuit_support is our round4 author's code.
"""
from pathlib import Path
from functools import lru_cache
import json
from circuit_support import Circuit,audit_body
HERE=Path(__file__).resolve().parent

def build(base,co,variant='structured',positive=False,heuristic=8):
 d=Circuit();names={};mapping={};special={}; c=d.const
 def A(*xs):
  out=c(0)
  for x in xs:out=d.add(out,x)
  return out
 def M(*xs):
  out=c(1)
  for x in xs:out=d.mul(out,x)
  return out
 def S(a,b):return d.op('sub',a,b)
 @lru_cache(None)
 def P(a,n):
  if n==0:return c(1)
  if n==1:return a
  z=P(a,n//2);z=M(z,z)
  return M(z,a) if n%2 else z
 def save(k,x):names[k]=x;return x
 pn={'epsilon':'epsilon_plus','g0':'g','h0':'h','s0':'s','w0':'w','phi':'phi_plus','i0':'i','j0':'j','n':'n_plus'}
 def clone(i):
  if i in special:return special[i]
  if i in mapping:return mapping[i]
  nd=base['nodes'][i];k=nd['kind']
  if k in ('add','sub','mul'):r=d.op(k,clone(nd['left']),clone(nd['right']))
  elif k=='variable' and positive:r=S(d.leaf('variable',name=pn[nd['name']]),c(1))
  else:r=d.intern(nd.copy())
  mapping[i]=r;return r
 if positive:
  eps=d.leaf('variable',name='epsilon_plus');yi=d.leaf('fixed',name='y_index')
  special[base['named_nodes']['b']]=A(yi,eps)
 B=clone(base['named_nodes']['B']);nu=co['nu'];L=co['L']
 z=d.leaf('fixed',name='z_index');t=[B]
 for _ in range(nu+1):t.append(M(P(t[-1],4),t[-1]))
 vs=[c(1)]*(nu+1)
 for j in range(nu-1,-1,-1):vs[j]=M(P(t[j],4),vs[j+1])
 ws=[t[nu]]+vs;hs=[c(1)]+[c(0)]*4
 for w in ws:
  for a in range(1,5):hs[a]=A(hs[a],M(w,hs[a-1]))
 aliases={};canon={};terms=[]
 for row in co['coefficient_records']:
  recipe=row['coefficient_polynomial_in_fixed_ports'];sig=json.dumps(recipe,sort_keys=True,separators=(',',':'))
  if len(recipe)==1 and not any(recipe[0]['powers']):
   coeff=c(recipe[0]['coefficient']);aliases[row['name']]={'literal':recipe[0]['coefficient']}
  else:
   nm=canon.setdefault(sig,row['name']);coeff=d.leaf('fixed',name=nm);aliases[row['name']]={'fixed':nm}
  alpha=tuple(row['alpha']);terms.append(((4-sum(alpha),)+alpha,coeff))
 @lru_cache(None)
 def horner(terms):
  if not terms:return c(0)
  scores=[(sum(ex[j]>0 for ex,v in terms),sum(ex[j] for ex,v in terms),j) for j in range(len(ws))]
  if heuristic==0:hit,_,j=max(scores)
  elif heuristic==1:hit,_,j=max(scores,key=lambda a:(a[0],a[1],-a[2]))
  elif heuristic==2:hit,_,j=max(scores,key=lambda a:(a[1],a[0],a[2]))
  elif heuristic==3:hit,_,j=max(scores,key=lambda a:(a[1],a[0],-a[2]))
  else:hit,_,j=max(scores,key=lambda a:(a[0],a[1],((a[2]+1)*heuristic*2654435761)%4294967296))
  if not hit:return A(*(v for ex,v in terms))
  yes=[];no=[]
  for ex,v in terms:
   if ex[j]:u=list(ex);u[j]-=1;yes.append((tuple(u),v))
   else:no.append((ex,v))
  return A(horner(tuple(no)),M(ws[j],horner(tuple(yes))))
 e=M(t[nu],A(M(z,hs[4]),horner(tuple(terms))))
 q=t[nu+1];ell=A(*t[1:nu+1]);lam=M(*(A(c(1),M(x,A(c(1),x),A(c(1),P(x,2)))) for x in t[:nu+1]),A(c(1),q),A(c(1),P(q,2)))
 for nm,val in [('e',e),('q',q),('ell',ell),('lambda',lam)]:special[base['named_nodes'][nm]]=val
 for nm,i in base['named_nodes'].items():names[nm]=clone(i)
 var={nd['name']:clone(i) for i,nd in enumerate(base['nodes']) if nd['kind']=='variable'}
 R=names['R'];Y=names['Y'];U=names['U'];PP=names['P'];K=names['K'];AA=names['A'];CC=names['C'];JJ=names['J'];QQ=names['Q'];DD=names['D'];EE=names['E'];FF=names['F'];HH=names['H'];a0=names['a0'];a1=names['a1'];margin=names['margin']
 r=save('r',A(M(names['b'],A(var['w0'],c(1))),var['phi']))
 sigma=save('sigma',M(Y,A(U,c(1))))
 if variant=='structured':
  md=save('M_D',M(sigma,A(P(R,2),P(CC,2))))
  tc=save('T_C',A(M(A(var['j0'],c(3)),P(CC,2)),P(r,2)))
 else:
  md=save('M_D',M(sigma,A(M(R,CC),P(r,2))))
  tc=save('T_C',A(M(CC,HH),P(r,2)))
 mf=save('M_F',A(M(AA,EE),c(1)))
 mi=save('M_I',A(S(M(FF,A(M(DD,tc),M(c(2),P(HH,2)),P(AA,2))),P(AA,2)),c(1)))
 v0=save('V0',A(M(PP,K),c(1)));v1=save('V1',A(M(md,mf,mi),c(1)))
 u=save('signed_divisor',M(JJ,FF));v=save('signed_dividend',A(M(QQ,FF),M(JJ,S(HH,CC))))
 mdiv=save('M_div',A(P(QQ,2),P(S(HH,CC),2),c(1)))
 om=save('Omega',M(u,margin))
 th=save('Theta',S(A(M(u,A(var['n'],mdiv)),v),M(om,A(M(c(2),mdiv),M(v0,v1)))))
 inner=save('inner',S(P(th,2),M(P(om,2),A(a0,M(P(v0,2),a1)))))
 out=save('output',S(P(inner,2),M(c(4),P(om,4),P(v0,2),a0,a1)))
 body=d.pack(out,names);body.update(nu=nu,L=L,variant=variant,horner_heuristic=heuristic,domain='positive integers' if positive else 'nonnegative integers',model='Binary +,-,*; fixed integer coefficients free; polynomial registers are not unknowns.',coefficient_aliases=aliases,coefficient_binding='INDEX_CONSTANTS.json')
 return body

def main():
 co=json.loads((HERE/'INDEX_CONSTANTS.json').read_text());base=json.loads((HERE/'base31.json').read_text());led={}
 for variant in ['structured','signed_quadratic']:
  for pos in [False,True]:
   body=build(base,co,variant,pos);name='nine31_'+variant+('_positive' if pos else '')
   (HERE/(name+'.json')).write_text(json.dumps(body,separators=(',',':'))+'\n');led[name]=audit_body(body)
 (HERE/'BUILD_LEDGER.json').write_text(json.dumps(led,indent=2)+'\n');print(json.dumps(led,indent=2))
if __name__=='__main__':main()
