#!/usr/bin/env python3
"""Fresh sparse compiler and finite Boolean checks; never imports predecessors."""
import argparse,hashlib,json,math
from pathlib import Path
PINS={'../../verification/explore_fixed_raw_universal_76.py': '011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0', 'complete75_half_binomial_compiler.py': 'd6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', '../../1980/FIXED_RAW_UNIVERSAL_81_PROOF.md': 'e8321ed4b6e3dd19fadcb33c3b6a3fd9aa487e9051463d4bdcd89884ae26803f', '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', 'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b', 'complete83_gamma_native_finite_prime_avoidance.md': '93aa3b61dcd03f7ce65acca9619f90c29710235ec2438cb4dd14000d8bdb8a96', 'complete83_gamma_native_three_power_control.md': 'addac036d27190fcf61632df3e0a632815f1e039efd6b96dd3d778005f83e448', 'gamma_parity_padding_scout.md': '0def681763b4039a7074bd13f33def941c2b215db8f90b4194400e84ffc4080c', 'complete75_gamma87_compiler_order_filters.md': '43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade'}
COLLECT=[
 '../../verification/explore_fixed_raw_universal_76.py','complete75_half_binomial_compiler.py',
 'complete75_half_binomial_compiler.md','../../1980/FIXED_RAW_UNIVERSAL_81_PROOF.md',
 '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md','../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md',
 'pell_kernel_half_binomial42.md','complete75_normalized_strong87.md',
 'complete83_gamma_native_finite_prime_avoidance.md','complete83_gamma_native_three_power_control.md',
 'gamma_parity_padding_scout.md','complete75_gamma87_compiler_order_filters.md',
 'complete84_scaled_strong_output.json','complete84_scaled_strong_output.md']
# Pins are inserted before release; all dependencies are read only as bytes/JSON.
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def val(n,p):
 need(n>0,'valuation domain');e=0
 while n%p==0:e+=1;n//=p
 return e
def prime(p):return p>=2 and all(p%i for i in range(2,math.isqrt(p)+1))
def params(p):
 need(prime(p) and p>=5,'odd prime >=5');o=1
 while pow(2,o,p)!=1:o+=1
 S=math.lcm(2,o);lam=val((1<<S)-1,p);w=1+val(S,3)
 need(S<=p-1 and S%2==0,'order spacing')
 return S,lam,w

def ceilpower(p,bound):
 v=1
 while v<bound:v*=p
 return v

def pad(windows,a):
 aa=a+1 if a%2==0 else a+2
 return windows+([(a,)*9] if len(windows)%2 else []),aa

def layout(windows,a,p):
 k=len(windows);need(k>=2 and len(set(windows))==k and all(len(v)==9 and all(0<=c<a for c in v) for v in windows),'window API')
 Ac=1<<max(2,(k+1).bit_length());start=k+3*a
 payload={(r,c,s):start+(2-r)*3*a+(2-c)*a+s for r in range(3) for c in range(3) for s in range(a)}
 coeff={i:1 for i in range(k)};mu=Ac-2
 for j,((r,c,s),e) in enumerate(payload.items(),1):
  coeff[e]=Ac**j;mu+=Ac**j
  for i,v in enumerate(windows):
   if v[3*r+c]==s:coeff[i]+=Ac**j
 ac=[]
 for j in range(1+9*a,1+9*a+4):
  v=Ac**j;ac.append(v);mu+=v
  for i in range(k):coeff[i]+=v
 padding=0;m=2*mu.bit_count()+12*a+2
 while m+1<k+9*a+5:mu+=Ac**(1+9*a+4+padding);padding+=1;m+=2
 dummy=list(range(start+9*a,start+9*a+m+1-k-9*a-4));need(dummy,'ignored dummy')
 old=list(range(k))+list(payload.values())+dummy;unit=max(old)+3*a+1
 anchors=[unit*j for j in [1,3,9,27]];E=max(anchors);positions=old+anchors
 for e,v in zip(anchors,ac):coeff[e]=v
 H=E+24*unit+3*a+1;T1=H+2*E+a+1;T2=T1+2*E+1;g=T2+E+1
 L=ceilpower(p,g+E+1);mass=(len(positions)+2)*(2*sum(coeff.values())+6)
 b=ceilpower(p,(max(4*mass+8,2*mu+4,32)-1).bit_length());rad=1<<b;d=b*L
 DC={}
 def add(e,v):DC[e]=DC.get(e,0)+v
 for e in [3*a,H+a,8*unit,24*unit]:add(e,1)
 for e,v in coeff.items():add(T1-e,v);add(T2-e,v)
 oldunit=(5+2*sum(v*pow(2,e,p) for e,v in DC.items())+4*pow(2,H,p))%p
 chi=int(oldunit==0)
 if chi:add(g,1)
 newunit=(5+2*sum(v*pow(2,e,p) for e,v in DC.items())+4*pow(2,H,p))%p
 MF={T1:mu,T2:mu}
 def mf(e,v):MF[e]=MF.get(e,0)+v
 for r in range(2):
  for c in range(3):
   for s in range(a):mf(payload[r,c,s],1)
 for r in range(3):
  for c in range(2):
   for s in range(a):mf(H+payload[r,c,s],1)
 for e in anchors[2:]:mf(e,1)
 need(newunit!=0 and b%2==L%2==d%2==1 and pow(2,b,p)==2,'prime unit and odd dimensions')
 need(g%2==0 and unit%2==1 and len(set(positions))==len(positions)==m+1,'layout')
 need(max(DC)+E<L and max(MF)<g and all(g+e not in MF for e in positions),'unchecked high correction')
 need(dummy[0]>1 and dummy[0]+1<E and all(e not in coeff for e in dummy),'extra bit')
 need(mass<=rad//4-2 and rad>=32,'strengthened mass')
 need(sum(v.bit_count() for v in MF.values())==m and min(MF)>0,'field population')
 # Every arbitrary low/upper dummy remains invisible at all old tested fields.
 for e in dummy:
  need(all(DC.get(t-e,0)==0 for t in MF),'dummy DC tests')
  need(all(t-e!=H for t in MF),'dummy DR tests')
 dc3=sum(v*((-1)**e) for e,v in DC.items())%3;dr3=(-1)**H%3
 need((dc3-dr3)%3==chi and (2-chi)%3!=0,'ternary unit')
 mc3=(1-sum((-1)**e for e in positions if e!=1)-2*((-1)**dummy[0]))%3
 mf3=(sum(v*((-1)**e) for e,v in MF.items())+4)%3
 need(mf3==2 and mc3==(2 if k%2 else 1 if a%2==0 else 0),'actual mask parity')
 return {'ell':p,'windows':[list(v) for v in windows],'alphabet':a,'selector_count':k,'native_count':len(positions),'dummy_count':len(dummy),'dummy':dummy[0],'b':b,'L':L,'d':d,'high_degree':g,'high_correction':chi,'old_unit':oldunit,'new_unit':newunit,'MC_mod3':mc3,'MF_native_mod3':mf3,'DC_minus_DR_mod3':(dc3-dr3)%3,'positions_sha256':sha(json.dumps(positions).encode()),'DC_sparse_sha256':sha(json.dumps(sorted(DC.items())).encode()),'scope':'fresh sparse finite window fixture; not a universal-program or full-history materialization'}

def boolean(p):
 S,lam,w=params(p);d=1;N=ceilpower(p,3**w*p**(2*lam)*d+1);M=d*N;T=N//p**lam;g=p**lam*d;mod=3**w*M
 need(T>3**w*g,'cardinality')
 weights=[pow(2,d*S*j,M) for j in range(T)];lookup={((a-1)//g)%T:j for j,a in enumerate(weights)}
 need(len(lookup)==T and all(a%g==1 for a in weights),'subgroup bijection')
 B=pow(2,d,mod);digest=hashlib.sha256();maximum=0
 for z in range(M):
  epsilon=int(z%p==0);zz=(z-epsilon*B)%M
  need(zz%p!=0,'unit choice')
  for residue in range(3**w):
   k=zz%g;kk=(k+(g*((residue-epsilon*B-k)*pow(g,-1,3**w)%(3**w))))
   need(0<kk<3**w*g<T and kk%p,'unit cardinality')
   sigma=((zz-kk)//g)%T;t0=((sigma-kk*(kk-1)//2)*pow(kk,-1,T))%T
   ids=[S*lookup[(t0+j)%T] for j in range(kk)]+([1] if epsilon else [])
   need(len(ids)==len(set(ids)) and max(ids)<N,'Boolean slots')
   need(sum(pow(B,j,mod) for j in ids)%M==z and sum(pow(B,j,mod) for j in ids)%(3**w)==residue,'both targets')
   digest.update(json.dumps([z,residue,ids],separators=(',',':')).encode()+b'\n');maximum=max(maximum,len(ids))
 # Independent bitset dynamic programming on the physical weights.
 mask=(1<<mod)-1;bits=1
 for j in [S*j for j in range(T)]+[1]:
  s=pow(B,j,mod);bits|=((bits<<s)|(bits>>(mod-s)))&mask
 need(bits==mask,'independent Boolean coverage')
 return {'ell':p,'S':S,'lambda':lam,'w':w,'d':d,'N':N,'modulus':mod,'all_targets':mod,'maximum_selected_bits':maximum,'selection_stream_sha256':digest.hexdigest(),'independent_DP_full':True,'scope':'small arithmetic component d=1, not compiler widths or histories'}

def valuations():
 out=[]
 for p in [5,7,11,13,17,31,1093]:
  S,lam,w=params(p)
  for ae in [0,1]:
   d=p**ae;N=p**(2*lam+2);M=d*N;T=N//p**lam;swap=S*T
   need(swap<N and pow(2,d*S*T,M)==1 and pow(2,d*S*(T//p),M)!=1,'exact group order')
   need(pow(2,d*swap,p**(ae+2*lam+2))==1 and pow(2,d*swap,p**(ae+2*lam+3))!=1,'swap prime valuation')
   need(pow(2,d*swap,3**w)==1 and pow(2,d*swap,3**(w+1))!=1,'swap ternary valuation')
   out.append({'ell':p,'S':S,'lambda':lam,'w':w,'d':d,'N':N,'swap':swap,'exact_order':T,'ell_swap_valuation':ae+2*lam+2,'ternary_swap_valuation':w})
 return out

def geometry():
 records=[]
 for p in [5,7,11,13,17,31,1093]:
  S,lam,w=params(p);F=p**lam
  for u in [1,w+1,w+3]:
   h=p;d=p;spacing=2*3**u*h;Q=3**max(u-w-1,0)*97 # synthetic capacity, no claimed factorization of a native minus factor
   H=ceilpower(p,max(F+1,F*((spacing//h)*(Q-2)+1)+1,3**w*p**(2*lam)*d//h+1))
   N=h*H;swap=S*N//F;imax=spacing*(Q-2);lowerlast=S*(N//F-1)
   need(imax+h<min(swap,N-swap) and lowerlast+h<N,'both grids nonwrapping and disjoint')
   need(1+h<N and pow(2,d*spacing,3**(u+1))==1,'optional slot and ternary geometric modulus')
   records.append({'ell':p,'u':u,'h':h,'d':d,'Q_synthetic':Q,'Htime':H,'swap':swap,'last_upper_source':imax,'last_lower':lowerlast})
 return records

def examples():
 out=[]
 for p,o in [(127,7),(43,14)]:
  need(prime(p) and pow(2,o,p)==1 and all(pow(2,j,p)!=1 for j in range(1,o)),'new order example')
  out.append({'prime':p,'exact_order_of_2':o})
 return out

def source(root):
 z=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet'];rows=z['source'];counts={o:sum(r[1]==o for r in rows) for o in ['*','+','-']}
 need(len(rows)==84 and counts['*']==47 and counts['+']+counts['-']==37 and len(z['witnesses'])==18,'actual unchanged84')
 return {'source_sha256':PINS['complete84_scaled_strong_output.json'],'operations':84,'M':47,'A':37,'positive_witnesses':18,'exact_degree_inherited':187,'rows_sha256':sha(json.dumps(rows,separators=(',',':')).encode()),'new_source_emitted':False,'numeral_recipe':{'Bm1':'2^d-1','Kconstant':'DC+2^d*DR','twice_cell_bits':'2d','inner_bits':'b','MC':'2^d-1-sum_(e in E,e!=1)2^(be)-2*2^(b e_star)','MF':'MF_native+2^d-1, where MF_native=MF_old+4'}}

def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def read(path):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate key');d[k]=v
  return d
 def bad(s):raise ValueError('noninteger/nonfinite JSON '+s)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)

def make(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 layouts=[]
 for p in [5,7,11,13,17,31,1093]:
  for windows,a in [([(0,)*9,(1,)*9],2),([(0,)*9,(1,)*9,(2,)*9],3)]:
   for padded in [False,True]:
    ww,aa=pad(windows,a) if padded else (windows,a);v=layout(ww,aa,p);v['parity_padded']=padded;layouts.append(v)
 return {'schema':'odd-prime-compiler-transfer-v1','pins':PINS,'actual_source':source(root),'sparse_layouts':layouts,'all_target_Boolean_components':[boolean(p) for p in [5,7,11,13,17]],'exact_valuation_components':valuations(),'finite_geometry_models':geometry(),'illustrative_ell7_prime_orders':examples(),'scope':{'actual_compiler_theorem':'new fixed numeral recipe for each fixed odd prime ell>=5; same ordinary input and actual84 DAG','full_program_numerals_or_histories_materialized':False,'predecessor_code_executed':False,'gamma83_language':'unresolved','finite_filter':'for each fixed u>=1 and adequate ell-power h, actual histories with gcd(Delta,2^(2*3^u*d*h)-1)=3; separate histories for separate requests'}}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();z=make(a.root)
 if a.output:
  with a.output.open('x') as f:json.dump(z,f,indent=2,sort_keys=True);f.write('\n')
 else:need(exact(z,read(a.expect)),'type-exact receipt')
 print('PASS: sparse odd-prime compiler transfer and bounded joint Boolean/geometry checks')
if __name__=='__main__':main()
