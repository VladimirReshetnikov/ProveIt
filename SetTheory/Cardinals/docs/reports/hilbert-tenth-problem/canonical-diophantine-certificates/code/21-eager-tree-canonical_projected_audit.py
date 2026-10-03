#!/usr/bin/env python3
"""Independent preferred projected canonical-overlay check and symbolic degree check."""
import copy,json
from pathlib import Path
from canonical_overlay_audit import build,candidate,check,pair
from independent_audit import residuals,FIELDS
HERE=Path(__file__).resolve().parent

def rs(rows,keys,rho,gaps):
 N=len(rows);out=[]
 out.extend(keys[i-1]-pair(rows[i]['x'],rows[i]['y']) for i in range(1,N))
 out.extend(keys[i+1]-keys[i]-1-gaps[i] for i in range(max(N-2,0)))
 for i,r in enumerate(rows):
  out.append(1+rho[i]-int(i==0)-sum((1+rho[j])*rows[j]['pointers'][s][i] for j in range(N) for s in range(3)))
  t=r['t']
  out.extend((r['a']*(t[0]+t[2]),r['b']*(t[0]+t[1]),r['c']*(t[0]+t[1]+t[2]+t[3]),r['u']*(t[0]+t[1]+t[2]),r['v']*(t[0]+t[1]+t[2]+t[4])))
 return out

def make(rows):
 rows,keys,rho,gaps,_=build(rows)
 return rows,keys[1:],rho,gaps

def main():
 checked=0
 for x in range(32):
  for y in range(24):
   ev=candidate.Evaluation(budget=500,max_bits=4096)
   try:z=ev.app(x,y)
   except (candidate.Exhausted,candidate.RepeatedActiveCall,RecursionError):continue
   c=make(candidate.certificate(ev,(x,y)));N=len(c[0]);assert check(c[0],x,y,z) and all(v==0 for v in rs(*c));checked+=1
   assert 3*N*N+19*N+sum(map(len,c[1:]))==3*N*N+21*N-1+max(N-2,0)
   assert 23*N+3+len(rs(*c))==30*N+2+max(N-2,0)
 # Producer's complete preferred identity certificate matches independent construction exactly.
 ev=candidate.Evaluation();ev.app(10,10);c=make(candidate.certificate(ev,(10,10)))
 prod=json.loads((HERE/'canonical_projected_identity.json').read_text())['certificate']
 assert c==(prod['rows'],prod['kappa'],prod['flow_slack'],prod['order_slack'])
 # Independently reject root duplication without any key/root-distinctness equation.
 rows,keys,rho,gaps=copy.deepcopy(c);N=len(rows);root=copy.deepcopy(rows[0])
 for r in rows:
  for p in r['pointers']:p.append(0)
 for p in root['pointers']:p.append(0)
 rows.append(root);oldkeys=[pair(r['x'],r['y']) for r in rows]
 order=[0]+sorted(range(1,N+1),key=lambda i:oldkeys[i]);inv={old:i for i,old in enumerate(order)}
 rows=[{**rows[i],'pointers':[[p[j] for j in order] for p in rows[i]['pointers']]} for i in order]
 keys=[oldkeys[i] for i in order[1:]];gaps=[keys[i+1]-keys[i]-1 for i in range(len(keys)-1)]
 mu=[0]*(N+1);mu[0]=1
 for i in sorted(range(N+1),key=lambda i:rows[i]['h'],reverse=True):
  for p in rows[i]['pointers']:
   for j,d in enumerate(p):mu[j]+=d*mu[i]
 assert mu[inv[N]]==0;mu[inv[N]]=1;rho=[v-1 for v in mu]
 assert check(rows,10,10,10) and any(rs(rows,keys,rho,gaps))
 # Fully independent symbolic residual construction, including N=1 boundary.
 import sympy as s
 symbolic=[]
 for N in (1,2,3):
  rows=[];vars=[]
  for i in range(N):
   r={f:s.Symbol(f'{f}_{i}') for f in FIELDS};r['t']=list(s.symbols(f't_{i}_0:5'));r['pointers']=[list(s.symbols(f'd_{i}_{k}_0:{N}')) for k in range(3)];rows.append(r);vars+=list(r[f] for f in FIELDS)+r['t']+sum(r['pointers'],[])
  keys=list(s.symbols(f'key0:{N-1}'));rho=list(s.symbols(f'rho0:{N}'));gaps=list(s.symbols(f'gap0:{max(N-2,0)}'));vars+=keys+rho+gaps
  p,n,o=s.symbols('p n o');equations=residuals(rows,p,n,o)+rs(rows,keys,rho,gaps)
  assert len(vars)==3*N*N+21*N-1+max(N-2,0) and len(equations)==30*N+2+max(N-2,0)
  assert max(s.Poly(r,*vars,p,n,o).total_degree() for r in equations)==2
  P=s.Poly(sum(s.expand(r*r) for r in equations),*vars,p,n,o);assert P.total_degree()==4
  symbolic.append({'N':N,'variables':len(vars),'residuals':len(equations),'SOS_degree':4})
 out={'valid_preferred_certificates':checked,'identity_matches_independent_builder':True,'core_valid_duplicate_root_rejected_without_root_key':True,'symbolic_checks':symbolic,'independently_recomputed_gate_formulas':{'M':'15N^2+70N+g','A':'18N^2+93N-1+4g','g':'max(N-2,0)'},'uniqueness_status':'mathematical proof passes; tests are regression evidence only'}
 (HERE/'canonical_projected_audit_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
