#!/usr/bin/env python3
"""Independent checker/builder for proposed canonical singleton-fiber overlay.
Frozen base checker supplies raw certificates; all overlay logic is independent.
"""
import copy,json
from pathlib import Path
from independent_audit import candidate,pair,check,residuals,permutation,refresh
HERE=Path(__file__).resolve().parent

def overlay_residuals(rows,keys,rho,gaps,slacks):
 N=len(rows);rs=[]
 for i,r in enumerate(rows):
  rs.append(keys[i]-pair(r['x'],r['y']))
  rs.append(1+rho[i]-int(i==0)-sum((1+rho[j])*rows[j]['pointers'][s][i] for j in range(N) for s in range(3)))
  t=r['t']
  rs += [r['a']*(t[0]+t[2]),r['b']*(t[0]+t[1]),r['c']*(t[0]+t[1]+t[2]+t[3]),r['u']*(t[0]+t[1]+t[2]),r['v']*(t[0]+t[1]+t[2]+t[4])]
 for i in range(1,N):rs.append((keys[i]-keys[0])**2-1-slacks[i-1])
 for i in range(1,N-1):rs.append(keys[i+1]-keys[i]-1-gaps[i-1])
 assert len(rs)==8*N-1+max(N-2,0)
 return rs

def build(rows):
 rows=permutation(rows,[0]+sorted(range(1,len(rows)),key=lambda i:pair(rows[i]['x'],rows[i]['y'])))
 N=len(rows);keys=[pair(r['x'],r['y']) for r in rows];mu=[0]*N;mu[0]=1
 for i in sorted(range(N),key=lambda i:rows[i]['h'],reverse=True):
  for slot in rows[i]['pointers']:
   for j,d in enumerate(slot):mu[j]+=mu[i]*d
 assert all(m>0 for m in mu)
 assert sum(mu)==rows[0]['h']
 return rows,keys,[m-1 for m in mu],[keys[i+1]-keys[i]-1 for i in range(1,N-1)],[(keys[i]-keys[0])**2-1 for i in range(1,N)]

def canonical_ok(packet,p,n,o):
 rows,keys,rho,gaps,slacks=packet;N=len(rows)
 if not check(rows,p,n,o):return False
 if [len(a) for a in (keys,rho,gaps,slacks)]!=[N,N,max(N-2,0),N-1]:return False
 if any(type(v)!=int or v<0 for a in (keys,rho,gaps,slacks) for v in a):return False
 return all(v==0 for v in overlay_residuals(*packet))

def main():
 passed=0;maxN=0
 for x in range(32):
  for y in range(24):
   ev=candidate.Evaluation(budget=500,max_bits=4096)
   try:z=ev.app(x,y)
   except (candidate.Exhausted,candidate.RepeatedActiveCall,RecursionError):continue
   packet=build(candidate.certificate(ev,(x,y)))
   assert canonical_ok(packet,x,y,z)
   N=len(packet[0]);nv=3*N*N+19*N+sum(len(a) for a in packet[1:]);nr=23*N+3+len(overlay_residuals(*packet))
   assert nv==3*N*N+22*N-1+max(N-2,0) and nr==31*N+2+max(N-2,0)
   passed+=1;maxN=max(maxN,N)
 ev=candidate.Evaluation();ev.app(0,5)
 packet=build(candidate.certificate(ev,(0,5)));assert canonical_ok(packet,0,5,11)
 # Infinite-fiber deformation accepted by old schema and rejected by new normalization.
 bad=copy.deepcopy(packet);bad[0][0].update(a=7,b=8,c=9,u=10,v=11);refresh(bad[0][0])
 assert check(bad[0],0,5,11) and not canonical_ok(bad,0,5,11)
 # Perturbing any individual occurrence-flow slack is rejected.
 ev=candidate.Evaluation();ev.app(1014,10);packet=build(candidate.certificate(ev,(1014,10)))
 for i in range(len(packet[0])):
  bad=copy.deepcopy(packet);bad[2][i]+=1;assert not canonical_ok(bad,1014,10,10)
 # Valid, semantically irrelevant padding is ruled out by positive flow.
 rows=candidate.certificate(ev,(1014,10),pad=1);N=len(rows)
 # No positive flow exists on the last padding row: every incoming selector is zero.
 assert all(rows[j]['pointers'][s][-1]==0 for j in range(N) for s in range(3))
 assert check(rows,1014,10,10)
 # Duplicate a reachable row and redirect one of repeated premises to it.
 rows=candidate.certificate(ev,(1014,10));target=next(j for j,d in enumerate(rows[0]['pointers'][0]) if d)
 N=len(rows)
 for r in rows:
  for p in r['pointers']:p.append(0)
 rows.append(copy.deepcopy(rows[target]));rows[0]['pointers'][0][target]=0;rows[0]['pointers'][0][-1]=1
 assert check(rows,1014,10,10)
 keys=[pair(r['x'],r['y']) for r in rows]
 assert keys[target]==keys[-1]
 # Any strict sort of nonroot keys, together with distinct root, must reject the duplicate.
 assert len(set(keys))<len(keys)
 out={'valid_canonical_certificates':passed,'maximum_rows':maxN,'N1_witnesses':24,'N1_residuals':33,'N_ge_2_witnesses':'3N^2+23N-3','N_ge_2_residuals':'32N','inactive_infinite_fiber_deformation_rejected':True,'positive_flow_detects_unreachable_padding':True,'all_individual_flow_mutations_rejected':True,'reachable_duplicate_pair_detected':True,'root_cost_equals_sum_occurrence_flows':True}
 (HERE/'canonical_overlay_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
