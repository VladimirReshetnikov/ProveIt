import json, pathlib, random
import sympy as S
P=pathlib.Path(__file__).parent
d=json.loads((P/'upstream/quartic32.json').read_text())
names=d['variables']; vs=S.symbols(' '.join(names)); sy=dict(zip(names,vs))
beta,K0,MC,MF=S.symbols('beta K0 MC MF'); sy.update(dict(zip(['beta','K0','MC','MF'],[beta,K0,MC,MF])))
base=[S.sympify(x,locals=sy) for x in d['residuals']]
original=set(names[:16]); candidates=set(names)-original
def degree(e, live):return S.Poly(e,*[sy[x] for x in live]).total_degree()
def eliminate(live,eqs,name):
 v=sy[name]
 for idx,e in enumerate(eqs):
  a=e.coeff(v)
  if a in (-1,1) and not e.has(v**2) and not (e-a*v).has(v):
   value=S.expand(-(e-a*v)/a)
   nlive=tuple(x for x in live if x!=name)
   neqs=tuple(S.expand(r.subs(v,value)) for k,r in enumerate(eqs) if k!=idx)
   yield nlive,neqs,(name,idx,str(value))
def search(mode,bound,width):
 live=tuple(names); eqs=list(base)
 if 'first' in mode:
  t=sy['tau']; k=sy['eta']+sy['zeta']; p=sy['P']
  eqs=[S.expand(e.subs(t,t+p-k)) for e in eqs]
 if 'main' in mode:
  dr=sy['D']; a=sy['a']; c=sy['c']
  eqs=[S.expand(e.subs(dr,dr+a*c)) for e in eqs]
  # Use Delta=a^2+4a+3 to reduce the main equation before eliminating.
  eqs[11]=S.expand(eqs[11] + sy['C2']*eqs[9])
  # With C2=c^2, eliminate the apparent quartic cancellation in the same equation.
  eqs[11]=S.expand(eqs[11]+sy['a']**2*eqs[10])
 frontier=[(live,tuple(eqs),[])]; seen=set(); best=frontier[0]
 for step in range(20):
  nxt=[]
  for liv,es,tr in frontier:
   for name in candidates.intersection(liv):
    for nl,ne,el in eliminate(liv,es,name):
     key=tuple(nl)
     if key in seen:continue
     if all(degree(e,nl)<=bound for e in ne):
      seen.add(key); nxt.append((nl,ne,tr+[el]))
  if not nxt:break
  nxt.sort(key=lambda st:sum(len(S.Add.make_args(e)) for e in st[1]))
  frontier=nxt[:width];best=frontier[0]
  print(mode,bound,step,len(frontier),len(best[0]),flush=True)
 liv,es,tr=best
 out={'mode':mode,'degree_bound':bound,'variables':liv,'variable_count':len(liv),'residuals':[str(e) for e in es],'equation_count':len(es),'elimination_steps':tr}
 (P/f'search_{mode}_{bound}.json').write_text(json.dumps(out,indent=2)+'\n')
 return out
if __name__=='__main__':
 for mode in ['raw','first','first_main']:
  for bound in [3,4]:search(mode,bound,100)
