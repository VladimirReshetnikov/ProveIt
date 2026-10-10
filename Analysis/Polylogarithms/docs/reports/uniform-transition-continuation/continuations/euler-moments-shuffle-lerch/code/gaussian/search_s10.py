"""Exploratory Euler/PSLQ diagnostics. No equality or independence assertion."""
from pathlib import Path
import json,time,sys
import mpmath as mp
OUT=Path(__file__).resolve().parent

def euler_values(p,N,digits):
 mp.mp.dps=digits
 pairs=[(a,p+1-a) for a in range(p,1,-2)]
 vals=[mp.mpf(0)]*(len(pairs)+1); hn=mp.mpf(0); hs={b:mp.mpf(0) for a,b in pairs}
 tail=(1<<N)-1; c=1; den=mp.mpf(1<<N)
 for n in range(N):
  if n:
   hn+=mp.mpf(1)/n
   for b in hs: hs[b]+=mp.mpf(1)/(2*n-1)**b+mp.mpf(1)/(2*n)**b
  wt=(-1 if n%2 else 1)*mp.mpf(tail)/den
  vals[0]+=wt*hn/(2*n+1)**p
  for j,(a,b) in enumerate(pairs,1): vals[j]+=wt*hs[b]/(2*n+1)**a
  c=c*(N-n)//(n+1);tail-=c
 assert tail==0
 beta=lambda s:(mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))/mp.mpf(4)**s
 names=[f'S{p}']+[f'g{a},{b}' for a,b in pairs]+[f'pi^{p+1}']+[f'beta({2*j})*zeta({p+1-2*j})' for j in range(1,p//2)]+[f'beta({p})*log(2)']
 vals += [mp.pi**(p+1)]+[beta(2*j)*mp.zeta(p+1-2*j) for j in range(1,p//2)]+[beta(p)*mp.log(2)]
 return names,vals

if __name__=='__main__':
 p=int(sys.argv[1]) if len(sys.argv)>1 else 10
 t=time.time();names,vals=euler_values(p,1600,550)
 report={'status':'exploratory; no proof of equality or independence','p':p,'N':1600,'dps':550,'basket':names,'values':[mp.nstr(v,520) for v in vals]}
 print('evaluated',p,'in',time.time()-t,flush=True)
 for dps,tol,ceil in [(300,'1e-280',10**30),(440,'1e-420',10**30)]:
  mp.mp.dps=dps
  steps=30000 if dps==300 else 50000
  vec=mp.pslq(mp.matrix(vals),tol=mp.mpf(tol),maxcoeff=ceil,maxsteps=steps)
  print(dps,vec,flush=True)
  search={'dps':dps,'tolerance':tol,'maxcoeff':str(ceil),'maxsteps':steps,'vector':vec}
  report.setdefault('searches',[]).append(search)
  if vec is not None and vec[0]:
   mp.mp.dps=550
   residual=mp.fdot(vals,vec)
   search['retained_precision_residual']=mp.nstr(residual,70)
   # This rejects the known false first S12 vector; it is a numerical guard,
   # not a proof. Exact rational intervals are supplied by a separate program.
   if abs(residual)<mp.mpf('1e-440'):
    report['frozen_vector']=vec
    report['retained_precision_residual']=search['retained_precision_residual']
    break
   search['disposition']='rejected by retained-precision numerical audit'
 report['elapsed_seconds']=time.time()-t
 (OUT/f's{p}_search_replay.json').write_text(json.dumps(report,indent=2)+'\n')
 print('done',report['elapsed_seconds'],flush=True)
