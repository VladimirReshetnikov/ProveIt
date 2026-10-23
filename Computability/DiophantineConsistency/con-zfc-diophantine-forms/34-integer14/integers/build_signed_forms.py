"""New data-only signed Jones synthesis. Does not execute upstream sources."""
from pathlib import Path
from functools import lru_cache
import json,collections
from circuit_support import Circuit,audit_body
HERE=Path(__file__).resolve().parent

def build(base,sixteen=True,fifteen=False,release_j=False):
 d=Circuit();names={};mapping={};special={};c=d.const
 def A(*xs):
  o=c(0)
  for x in xs:o=d.add(o,x)
  return o
 def M(*xs):
  o=c(1)
  for x in xs:o=d.mul(o,x)
  return o
 def S(a,b):return d.op('sub',a,b)
 @lru_cache(None)
 def P(a,k):
  if k==0:return c(1)
  if k==1:return a
  h=P(a,k//2);h=M(h,h)
  return M(h,a) if k%2 else h
 def save(k,v):names[k]=v;return v
 def var(n):return d.leaf('variable',name=n)
 if sixteen:special[base['named_nodes']['b']]=save('b',M(d.leaf('fixed',name='b_floor_odd' if fifteen else 'b_floor'),P(var('epsilon'),2)))
 if fifteen:
  wvar=next(i for i,n in enumerate(base['nodes']) if n.get('kind')=='variable' and n.get('name')=='w0')
  for idx,nd in enumerate(base['nodes']):
   if nd['kind']=='add' and wvar in (nd['left'],nd['right']):
    other=nd['right'] if nd['left']==wvar else nd['left']
    if base['nodes'][other]=={'kind':'literal','value':1}:special[idx]=P(var('wroot'),2)
 if release_j:
  for oldname,newname in [('h0','h'),('i0','i'),('j0','j')]:
   vid=next(i for i,n in enumerate(base['nodes']) if n.get('kind')=='variable' and n.get('name')==oldname)
   for idx,nd in enumerate(base['nodes']):
    if nd['kind']=='add' and vid in (nd['left'],nd['right']):
     other=nd['right'] if nd['left']==vid else nd['left']
     if base['nodes'][other]=={'kind':'literal','value':1}:special[idx]=var(newname)
 def clone(i):
  if i in special:return special[i]
  if i not in mapping:
   nd=base['nodes'][i];k=nd['kind']
   mapping[i]=d.op(k,clone(nd['left']),clone(nd['right'])) if k in ('add','sub','mul') else d.intern(nd.copy())
  return mapping[i]
 for n in ['b','B','q','ell','lambda','e','N','Gcap','R','U','Y','M','P','K','A','Wsmall','C','J','Q','D','E','F','Gp','H','I','a0','a1','margin']:
  names[n]=clone(base['named_nodes'][n])
 guards=(['g0','s0','phi','j0'] if sixteen else ['epsilon','g0','s0','phi','j0']) if fifteen else (['g0','s0','w0','phi','j0'] if sixteen else ['epsilon','g0','s0','w0','phi','j0'])
 if release_j:guards.remove('j0')
 zz=[var('z'+str(j+1)) for j in range(len(guards)+1)]
 stack=c(1)
 for j,x in enumerate([A(M(c(3),var(n)),c(2)) for n in guards]+[S(M(c(3),names['margin']),c(1))]):
  factor=save('guard_factor'+str(j+1),A(c(1),M(c(4),x,stack,P(zz[j],2))))
  stack=save('guard_stack'+str(j+1),M(stack,factor))
 DD=save('Ddiv',M(names['J'],names['F']))
 TT=save('Tdiv',A(M(names['Q'],names['F']),M(names['J'],S(names['H'],names['C']))))
 nz=[var('i') if release_j else A(var('i0'),c(1))]+zz
 if sixteen:nz.append(var('epsilon'))
 if fifteen:nz.append(var('wroot'))
 Z=save('Znonzero',M(*nz));den=save('Smerge',M(Z,P(DD,5)))
 rr=save('r_intersective',A(TT,M(DD,var('residue'))));D2=P(DD,2)
 T=save('Tmerge',M(S(S(P(rr,3),M(D2,rr)),M(D2,DD)),A(P(rr,2),M(c(23),D2))))
 weight1=save('weight1',stack)
 weight2=save('weight2',M(stack,A(P(names['P'],2),P(names['K'],2),c(2))))
 X=save('Xnorm',S(M(den,var('normroot')),T));den2=P(den,2)
 a0=save('A0norm',M(den2,stack));a1=save('A1norm',M(den2,P(weight1,2),names['a0']));a2=save('A2norm',M(den2,P(weight2,2),names['a1']))
 V=save('Vnorm',S(S(A(P(X,2),a2),a0),a1));four=M(c(4),P(X,2),a2)
 W=save('Wnorm',S(A(P(V,2),four),M(c(4),a0,a1)))
 out=save('output',S(P(W,2),M(c(4),P(V,2),four)))
 body=d.pack(out,names);body.update(nu=base['nu'],L=base['L'],domain='unrestricted integers',variant=('signed15' if sixteen else 'signed16_linear') if fifteen else ('signed16' if sixteen else 'signed17_reduced'),coefficient_aliases=base['coefficient_aliases'],coefficient_binding='SIGNED_BINDING.json')
 if release_j:body['variant']='signed14' if sixteen else 'signed15_linear'
 return body

def degree_data(body,fixed=None,mod=1000003):
 # Structural degree upper bounds plus leading diagonal residues. A nonzero
 # final residue proves equality with the bound. Cancellation may yield zero
 # at an intermediate bound, but does not invalidate propagated upper bounds.
 rows=[]
 for nd in body['nodes']:
  k=nd['kind']
  if k=='literal':v=(0,nd['value']%mod)
  elif k=='fixed':v=(0,37 if fixed is None else fixed[nd['name']]%mod)
  elif k=='variable':v=(1,1)
  else:
   da,ca=rows[nd['left']];db,cb=rows[nd['right']]
   if k=='mul':v=(da+db,ca*cb%mod)
   else:
    dd=max(da,db);v=(dd,((ca if da==dd else 0)+(1 if k=='add' else -1)*(cb if db==dd else 0))%mod)
  rows.append(v)
 final=rows[body['output']]
 if not final[1]:raise RuntimeError('Final degree not certified')
 return {'degree':final[0],'leading_diagonal_modulus':mod,'leading_diagonal_residue':final[1],'named_degrees':{n:rows[i][0] for n,i in body['named_nodes'].items()}}

def main():
 base=json.loads((HERE/'source_core31.json').read_text());ledger={}
 for small,tiny,rj in ((True,True,True),(False,True,True)):
  b=build(base,small,tiny,rj);name=b['variant'];dd=degree_data(b);b['exact_degree']=dd['degree']
  (HERE/(name+'.json')).write_text(json.dumps(b,separators=(',',':'))+'\n')
  ledger[name]={**audit_body(b),**dd}
 (HERE/'SIGNED_BUILD_LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
