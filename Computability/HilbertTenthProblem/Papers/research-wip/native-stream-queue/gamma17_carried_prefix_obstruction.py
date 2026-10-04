#!/usr/bin/env python3
"""Fresh finite-field component checks; no predecessor execution or history claim."""
import argparse,hashlib,json,math
from pathlib import Path
PINS={
 'complete84_scaled_strong_output.json':'8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete83_gamma_small_prime_digit_rules.md':'b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e',
 'complete83_gamma_small_prime_digit_rules.json':'8c074efc32c1bf5795e8f6f300a25491fa79969d6a08ffe98b28022354074ff3',
 'complete83_gamma_native_three_power_control.md':'addac036d27190fcf61632df3e0a632815f1e039efd6b96dd3d778005f83e448',
 'complete84_odd_prime_compiler_transfer.md':'d308f5e2649ee31814f6c93060f4dd06a36df14f4f15749e984c8dd1880a88a2',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def digest(a):return hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def digits(n):
 ds=[]
 while n:ds.append(n%17);n//=17
 return ds[::-1] or [0]
def integer(ds):
 n=0
 for d in ds:n=17*n+d
 return n
def transitions():
 rows=[]
 for d in range(17):
  if 2*d<17:
   L=pow(10,2*d,17); U=sum(math.comb(2*d,j)*pow(9,j,17) for j in range(d,2*d+1))%17
   alpha=math.comb(2*d,d)*pow(pow(13,d,17),-1,17)%17
   beta=(U-L)*pow(L,-1,17)%17
  else:alpha=0;beta=(-pow(10,-1,17))%17
  rows.append([alpha,beta])
 need(rows==[[1,0],[8,9],[11,12],[5,10],[2,2],[5,6],[11,11],[8,2],[1,0]]+[[0,5]]*8,'transition table')
 return rows
def state(r,rows):
 T=U=1
 for d in digits(r):
  alpha,beta=rows[d];T,U=(T+beta*U)%17,alpha*U%17
 return T,U

def independent_lucas_tail(r):
 # Lucas digit product, with a separate three-state comparison to j>=r.
 nd=digits(2*r); rd=[0]*(len(nd)-len(digits(r)))+digits(r)
 counts={0:1}
 for pos,(n,bound) in enumerate(zip(nd,rd)):
  weight=9;new={} # Frobenius: 9^(17^j)=9 in F17 for every j.
  for relation,value in counts.items():
   for j in range(n+1):
    rel=relation if relation else (j>bound)-(j<bound)
    new[rel]=(new.get(rel,0)+value*math.comb(n,j)*pow(weight,j,17))%17
  counts=new
 G=(counts.get(0,0)+counts.get(1,0))*pow(pow(9,r,17),-1,17)%17
 C=1
 for n,d in zip(nd,rd):C=C*(math.comb(n,d) if d<=n else 0)%17
 return C,G

def physical_models(root,rows):
 packet=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
 needed={'r_lhs'}
 for name,op,l,r in reversed(packet['source']):
  if name in needed:needed.update(x for x in (l,r) if isinstance(x,str))
 cone=[row for row in packet['source'] if row[0] in needed]
 def packed(values):
  env=values.copy()
  for name,op,l,r in cone:
   a=env[l] if isinstance(l,str) else l;b=env[r] if isinstance(r,str) else r
   env[name]=a*b if op=='*' else a+b if op=='+' else a-b
  return env['r_lhs']
 records=[]
 for b,N,h,S,F0 in [(5,125,1,4,5),(5,625,5,4,5),(7,343,1,6,7),(7,2401,7,6,7)]:
  B=1<<b;q=B**N;J=(q-1)//(B-1);e=2;P=B**e;Q=5;spacing=6*h;swap=S*N//F0
  DC=3;DR=1;Dfield=DC+B*DR+B**h;imax=spacing*(Q-2)
  need(imax+h<min(swap,N-swap),'physical nonwrap')
  baseC=1+B**3+2*P*sum(B**(spacing*j) for j in range(Q-1));baseZ=baseC-B**3;baseF=Dfield*baseC
  values={'Bm1':B-1,'Jrep':J,'F':baseF,'Z':baseZ,'MC':B-2,'MF':B+3}
  R0=packed(values);r0=(R0-1)//2
  Gamma=P*(q*q-1)*(1+q*Dfield);G=Gamma*(B**swap-1)
  geometric=sum(B**(spacing*j) for j in range(Q-1));width=G*geometric
  endpoints=[r0-width,r0]
  need(endpoints[0]>0 and geometric*(B**spacing-1)==B**(spacing*(Q-1))-1,'exact endpoint/width')
  actual=[]
  for k in range(Q):
   move=2*P*(B**swap-1)*sum(B**(spacing*j) for j in range(k))
   v=values.copy();v['Z']+=move;v['F']+=Dfield*move
   R=packed(v);r=(R-1)//2
   need(R==R0-2*G*sum(B**(spacing*j) for j in range(k)) and R%32==31,'actual packing cut')
   actual.append(r)
  lo,hi=map(digits,endpoints);prefix=[]
  if len(lo)==len(hi):
   for d0,d1 in zip(lo,hi):
    if d0!=d1:break
    prefix.append(d0)
  prefix_value=integer(prefix);L=len(hi)-len(prefix)
  carried=bool(prefix) and any(d>=9 for d in prefix)
  need((not prefix) or endpoints[0]//17**L==endpoints[1]//17**L==prefix_value,'shared prefix')
  if carried:
   target=3*state(prefix_value,rows)[0]%17
   need(all(5*independent_lucas_tail(r)[1]%17==target for r in actual),'physical-formula interval invariance')
  else:target=None
  bound=(Q-1)*P*(Dfield+1)*q**3*B**(swap+imax)
  need(width<bound,'physical width bound')
  records.append({'b':b,'B':B,'N':N,'h':h,'S':S,'F0':F0,'e':e,'Q':Q,'spacing':spacing,'swap':swap,'DC':DC,'DR':DR,'Cbase_hex':hex(baseC),'Zbase_hex':hex(baseZ),'Fbase_hex':hex(baseF),'r0_hex':hex(r0),'width_hex':hex(width),'r_min_hex':hex(endpoints[0]),'Gamma_hex':hex(Gamma),'shared_prefix_base17':prefix,'suffix_length':L,'shared_prefix_is_carried':carried,'invariant_a_mod17_if_carried':target,'literal_packing_evaluations':Q,'scope':'diagnostic positive arithmetic model of the actual packing cone and allowed move formulas; not a compiled program, marked history or full zero'})
 return {'packing_cone':cone,'packing_cone_sha256':digest(cone),'models':records}

def build(root):
 for name,pin in PINS.items():need(hashlib.sha256((root/name).read_bytes()).hexdigest()==pin,'pin '+name)
 rows=transitions();block=[7]*7+[1]
 # Coefficients of the affine homogeneous block, not a sampled state test.
 alpha=1;beta=0
 for d in block:
  a,b=rows[d];beta=(beta+b*alpha)%17;alpha=a*alpha%17
 need((alpha,beta)==(1,3),'block coefficient identity')
 for r in range(257):
  T,U=state(r,rows);C,G=independent_lucas_tail(r)
  need(U==pow(13,-r,17)*C%17 and T==pow(13,-r,17)*G%17,'independent Lucas tail')
  if r<65:
   direct=sum(math.comb(2*r,r+j)*pow(9,j,17) for j in range(r+1))%17
   need(direct==G,'direct full binomial row')
 prefixes=[]
 for k in range(17):
  t=integer(block*k+[9]);T,U=state(t,rows)
  need((T,U)==((6+3*k)%17,0),'closed prefix')
  suffix=(15-t)%16;r=17*t+suffix;R=2*r+1
  C,G=independent_lucas_tail(r);a=5*G%17
  need(R%32==31 and C==0 and a==(1+9*k)%17,'actual-base formula extension')
  prefixes.append({'k':k,'prefix_digits':block*k+[9],'T':T,'suffix':suffix,'r':r,'R':R,'a_mod17':a,'Delta_mod17':(a+1)*(a+3)%17,'scope':'formula extension only; no compiler realization'})
 need({v['a_mod17'] for v in prefixes}==set(range(17)),'all states')
 fixtures=[]
 for R in [63,639,1014751,916447]:
  r=(R-1)//2;C,G=independent_lucas_tail(r);T,U=state(r,rows);a=5*G%17
  need(R%32==31 and pow(2,R,17)==9 and a in (14,16) and a==3*T%17,'bad formula fixture')
  fixtures.append({'R':R,'r_base17':digits(r),'a_mod17':a,'Delta_mod17':0,'central_mod17':C,'T':T,'population_R':R.bit_count(),'q32_scalar_range_population':32**2<R<32**4 and R.bit_count()==17,'scope':'noncompiler formula; no masks, convolution, alignment or positive input established'})
 cylinders=[]
 for entry in prefixes:
  t=integer(entry['prefix_digits']);L=2
  rs=[t*17**L+s for s in range(17**L) if (t*17**L+s)%4==3]
  residues={5*independent_lucas_tail(r)[1]%17 for r in rs}
  need(residues=={3*entry['T']%17},'carried-prefix invariance')
  cylinders.append({'k':entry['k'],'suffix_digits':L,'r_min':min(rs),'r_max':max(rs),'checked_suffixes':len(rs),'a_mod17':next(iter(residues))})
 return {'schema':'gamma17-carried-prefix-v1','pins':PINS,'prime':17,'actual_X':9,'normalized_z':13,'transition_table_alpha_beta':rows,'bad_T_states':[11,16],'block':block,'block_map':{'alpha':1,'beta':3},'all_state_prefixes':prefixes,'noncompiler_bad_formula_fixtures':fixtures,'synthetic_prefix_cylinders':cylinders,'physical_grid_component':physical_models(root,rows),'checks':{'independent_Lucas_tails':257,'whole_binomial_rows':65,'analytic_prefixes':17,'synthetic_suffixes':sum(v['checked_suffixes'] for v in cylinders)},'genuine_move_criterion':'If floor(r_min/17^L)=floor(r_max/17^L)=t and binom(2t,t)=0 mod17, then every genuine member in the interval has the same a mod17, because r=3 mod4 is preserved. No claim that every genuine grid meets this condition.','scope':{'full_history_materialized':False,'genuine_bad_history_constructed':False,'universal_avoidance_or_enforcement':False,'new_operation_bound':False,'prior_all_state_theorem_rederived_not_new':True}}
def equal(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(equal(r,json.loads(a.expect.read_text())),'receipt mismatch')
 print('PASS: exact17 normalized automaton, analytic prefixes and conditional cylinder invariance; no history claim')
if __name__=='__main__':main()
