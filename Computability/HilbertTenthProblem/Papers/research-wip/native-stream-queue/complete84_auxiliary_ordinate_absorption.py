#!/usr/bin/env python3
"""Fresh actual-source and bounded Pell checks; all predecessors are inert."""
import argparse
import hashlib
import json
from pathlib import Path

PINS={
 'complete84_scaled_strong_output.py':'8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete84_exterior_auxiliary_absorption.py':'46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9',
 'complete84_exterior_auxiliary_absorption.json':'ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b',
 'complete84_exterior_auxiliary_absorption.md':'69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de',
 'review_complete84_exterior_auxiliary_absorption.md':'df47a59713fca80a9a059bda9b2a5956774d67ebcd60b5ce99b54096414eee3a',
 'review_complete84_exterior_auxiliary_absorption_math.md':'bdf25d1eb78850aa434ead4cf5fb2b62c2c8318413c55c9bcd73d6ca55d0b0d4',
}
OMIT=['auxiliary_quotient','y_aux']
OLD_OMIT=['i','f']+OMIT
ADDED=['L16','auxiliary_R_f2','aux_coefficient_root','R16','scaled_f_square','norm_strong']
FACTORS=['norm_first','norm_main','norm_input','norm_index','norm_transport']
REQUIRED=[
 ['aux_y2','*','y_aux','y_aux'],['L16','*','f','f'],
 ['auxiliary_Tf','*','auxiliary_quotient','f'],['auxiliary_Tf_minus_one','-','auxiliary_Tf',1],
 ['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one'],['auxiliary_R_f2','*','r_lhs','L16'],
 ['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2'],['H2','*','aux_u_rhs','aux_u_rhs'],
 ['aux_square_gap','-','H2','aux_y2'],['c2','*','R10a','R10a'],['Ac2','*','A','c2'],
 ['aux_coefficient_root','*','i','Ac2'],['R16','*','aux_coefficient_root','aux_coefficient_root'],
 ['scaled_f_square','*','A','L16'],['norm_strong','-','scaled_f_square','R16'],
 ['L17','*','R16','aux_square_gap'],['norm_aux','+','L17','aux_y2'],
 ['norm_pair','*','norm_first','norm_main'],['norm_triple','*','norm_pair','norm_input'],
 ['norm_four','*','norm_triple','norm_aux'],['norm_product','*','norm_four','norm_index'],
 ['all_units','*','norm_product','norm_transport'],['seven_units','*','all_units','norm_strong'],
 ['polynomial','-','seven_units','A'],['R12','+','UM','sn2'],['UM','*','wn2','sn2'],
 ['A','+','a_square','a4m5'],['a_square','*','R12','R12'],['a4','*',4,'R12'],['a4m5','+','a4',3],
 ['gamma_sum','+','rho','sigma'],['odd_index','+','scaled_t','inner_bits'],['scaled_t','*','twice_cell_bits','x']]
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def num(v):return {():v} if v else {}
def var(n):return {(n,):1}
def add(a,b,s=1):
 d=dict(a)
 for m,c in b.items():d[m]=d.get(m,0)+s*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
 return {m:c for m,c in d.items() if c}
def power(a,n):
 r=num(1)
 for _ in range(n):r=mul(r,a)
 return r
def records(p):return [[list(m),c] for m,c in sorted(p.items())]
def census(packet,omitted):
 taint=set(omitted);outside=[];known=set(packet['free'])
 for n,o,a,b in packet['source']:
  ck(n not in known and o in ['+','-','*'],'SSA/op')
  ck(all(type(x)is int or type(x)is str and x in known for x in [a,b]),'topology')
  known.add(n)
  if a in taint or b in taint:taint.add(n)
  else:outside.append(n)
 return outside,[n for n in packet['free'] if n not in omitted]
def source_checks(p,old_outside):
 # All these cuts are independent of every auxiliary port. The four
 # named dependent products stay expanded; none is an unrelated cut atom.
 expanded=['norm_pair','norm_triple','c2','Ac2']
 cuts=set(old_outside)-set(expanded)
 def run(y):
  env={n:var('port:'+n) for n in p['free']};env['y_aux']=y
  for n,o,a,b in p['source']:
   if n in cuts:env[n]=var('cut:'+n);continue
   a=env[a] if type(a)is str else num(a);b=env[b] if type(b)is str else num(b)
   env[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return env[p['output']]
 y=var('port:y_aux');pos,neg,zero=run(y),run(mul(num(-1),y)),run({})
 D=var('cut:A');c=var('cut:R10a');R=var('cut:r_lhs');i=var('port:i');f=var('port:f');T=var('port:auxiliary_quotient')
 P5=num(1)
 for n in FACTORS:P5=mul(P5,var('cut:'+n))
 S=mul(mul(D,i),power(c,2));Q=power(S,2)
 V=add(mul(c,add(mul(T,f),num(1),-1)),mul(R,power(f,2)),-1)
 Ns=mul(D,add(power(f,2),mul(mul(D,power(i,2)),power(c,4)),-1))
 Na=add(mul(Q,add(power(V,2),power(y,2),-1)),power(y,2))
 expected=add(mul(mul(P5,Na),Ns),D,-1)
 reduced=mul(D,add(mul(mul(mul(mul(power(D,2),power(i,2)),power(c,4)),power(V,2)),mul(P5,add(power(f,2),mul(mul(D,power(i,2)),power(c,4)),-1))),num(1),-1))
 ck(pos==neg==expected,'all84 source even-y and independent factor identity')
 ck(zero==reduced,'all84 source zero-y contraction')
 ck(all(m.count('port:y_aux')%2==0 for m in pos),'all y exponents even')
 return dict(literal_rows_visited_per_pass=len(p['source']),valid_auxiliary_independent_cuts=sorted(cuts),
  dependent_products_expanded=expanded,actual_five_factors=FACTORS,scaled_strong_expanded=True,
  full_output_terms=len(pos),full_output_coefficients=records(pos),zero_y_coefficients=records(zero),
  all_ring_even_y_identity=True,all_ring_zero_y_identity=True,
  zero_y_formula='Delta*(Delta^2*i^2*c^4*V^2*P5*(f^2-Delta*i^2*c^4)-1)')
def pell(A,n):
 x,y=1,0;D=A*A-1
 for _ in range(n):x,y=A*x+D*y,x+A*y
 return x,y
def coeffs():
 out=[[1],[-3,4]]
 for m in range(1,12):
  a=out[-1];b=out[-2];new=[0]*(len(a)+1)
  for j,v in enumerate(a):new[j]-=2*v;new[j+1]+=4*v
  for j,v in enumerate(b):new[j]-=v
  out.append(new)
 return out
def value(p,z):
 a=0
 for v in reversed(p):a=a*z+v
 return a
def components():
 cs=coeffs();identities=[];parities=[];descents=[];growth=[];separation=[]
 for A in range(2,9):
  D=A*A-1
  for m,C in enumerate(cs):
   n=2*m+1;x,y=pell(A,n)
   ck(value(C,-D)==(-1)**m*y,'odd Chebyshev identity')
   ck(value(C,A*A)==x//A and x%A==0,'odd quotient polynomial')
   identities.append([A,m,value(C,-D)])
  for n in range(26):
   x,y=pell(A,n);ck((x%A==0)==(n%2==1),'parity classification')
   parities.append([A,n,x%A])
   if n:
    xp,yp=A*x-D*y,A*y-x
    ck((xp,yp)==pell(A,n-1) and xp>0 and 0<=yp<y,'Pell descent')
    descents.append([A,n,yp])
   if n>=2:
    ck(y>(2*A-1)**(n-1)>=(A+0)**(n-1),'strict growth')
    growth.append([A,n,y])
  for R in [3,5,7,9]:
   c=pell(A,R)[1];f=2*c+1
   for n in range(1,R,2):
    z=pell(A,n)[1]
    ck(0<c-z<c+z<2*c<f,'two signed congruences separated')
    separation.append([A,R,n,c,f])
 thresholds=[]
 for t in range(13):
  for L in [1,2,3,4,5,7,8,9,15,16,17,31,32,33,255,256,257,1024]:
   ceiling=(L-1).bit_length();bound=3*t+ceiling;R=bound+1
   for f in [2,3,5,11]:
    ck(f**(R-1)>=L*f**(3*t),'strict growth rules out R beyond cutoff')
   thresholds.append([t,L,bound])
 return dict(C_coefficients=cs,odd_index_identities=identities,parity_checks=parities,
  descent_checks=descents,growth_checks=growth,signed_small_index_separation=separation,
  cutoff_checks=thresholds,scope='Component arithmetic only; no genuine compiler histories or full native zeros')
def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 prior=read(root/'complete84_exterior_auxiliary_absorption.json')
 ck(prior['source_sha256']==PINS['complete84_exterior_auxiliary_absorption.py'],'prior helper binding')
 for n,h in prior['pins'].items():ck(sha((root/n).read_bytes())==h,'transitive pin '+n)
 p=read(root/'complete84_scaled_strong_output.json')['packet'];rows=p['source'];by={r[0]:r for r in rows}
 ck(len(rows)==len(by)==84 and rows==prior['authenticated_parent_source'],'full actual84 source')
 for r in REQUIRED:ck(by[r[0]]==r,'literal boundary '+r[0])
 old,oldfree=census(p,OLD_OMIT);new,newfree=census(p,OMIT)
 ck(old==prior['source_census']['computed_exterior_in_source_order'] and len(old)==64 and len(oldfree)==21,'inherited exterior census')
 ck(len(new)==70 and len(newfree)==23 and [n for n in new if n not in old]==ADDED,'full93 census')
 ck(set(newfree)==set(oldfree)|{'i','f'},'all added supplied ports')
 ck([r[0] for r in rows if 'y_aux' in r[2:]]==['aux_y2'],'only y consumer')
 proof=source_checks(p,old)
 return dict(status='PASS_AUXILIARY_ORDINATE_ABSORPTION',source_sha256=sha(Path(__file__).read_bytes()),
  pins=PINS,authenticated_transitive_pins=prior['pins'],parent_packet_sha256=sha(encode(p)),authenticated_parent_source=rows,
  census=dict(omitted_ports=OMIT,computed_in_source_order=new,free_values=newfree,computed_count=70,free_count=23,total=93,
   previous_computed=old,previous_free=oldfree,added_computed=ADDED,added_supplied=['i','f'],literal_boundary_rows=REQUIRED),
  source_identities=proof,finite_checks=components(),
  theorem=dict(positive_parent_growth='n>=R; y_aux>f^(R-1)',all93_absolute_bound='at most f^3',
   coefficient_norm='L=max(1,sum of absolute integer coefficients)',cutoff='R<=3*degree(G)+ceil(log2 L)',
   input_bound='2d*x+b<R',signed_nonzero_parent_map='y_aux=abs(G)',zero_G_sector='empty',
   identically_zero_G_degree_convention=0,canonical_auxiliary_assumed=False),
  scope=dict(predecessor_execution=False,generic_G_compiler=False,new_candidate_source=False,
   operation_saving_claim=False,global_minimum_claim=False,native_fixture_claim=False))
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True)
 g=a.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 args=a.parse_args();result=build(args.root)
 if args.output:
  with args.output.open('x') as f:f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(encode(result)==encode(read(args.expect)),'exact typed receipt')
 print(result['status'],'70 computed +23 free; complete even/zero-y source identities')
if __name__=='__main__':main()
