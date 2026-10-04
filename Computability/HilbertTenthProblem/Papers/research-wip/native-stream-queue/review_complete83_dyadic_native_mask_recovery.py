#!/usr/bin/env python3
"""Independent exact algebra and bounded arithmetic; predecessors inert."""
import argparse,collections,hashlib,json,math
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
STEM=Path('/tmp/complete83_dyadic_native_mask_recovery')
PINS={'.md':'6fc07e4989926e868587cc43a4140c8534cde57358859dfe940b9151be21ac94','.py':'4ea248a62a3866c2b30a51ba282fda198e2663b323eae0eb384bd77714eaeaeb','.json':'f094621d6314b1297c5317398c5dbac2de3980a57b039f0db1aa8f6187860469'}
def ck(b,m):
 if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def v(n):
 ck(n!=0,'v2(0)');n=abs(n);return (n&-n).bit_length()-1
def unique(pairs):
 d={}
 for k,x in pairs:ck(k not in d,'duplicate JSON key');d[k]=x
 return d
# Canonical integer polynomials: a monomial is a sorted tuple of variable names.
class P:
 def __init__(self,x=0):self.d=x if isinstance(x,dict)else ({():x}if x else {})
 @staticmethod
 def var(s):return P({(s,):1})
 def __add__(self,o):
  o=o if isinstance(o,P)else P(o);d=self.d.copy()
  for k,x in o.d.items():d[k]=d.get(k,0)+x
  return P({k:x for k,x in d.items()if x})
 __radd__=__add__
 def __neg__(self):return P({k:-x for k,x in self.d.items()})
 def __sub__(self,o):return self+-co(o)
 def __rsub__(self,o):return co(o)+-self
 def __mul__(self,o):
  o=co(o);d=collections.Counter()
  for a,x in self.d.items():
   for b,y in o.d.items():d[tuple(sorted(a+b))]+=x*y
  return P({k:x for k,x in d.items()if x})
 __rmul__=__mul__
 def __pow__(self,n):
  out=P(1)
  for _ in range(n):out=out*self
  return out
 def __eq__(self,o):return self.d==co(o).d
 def serial(self):return [[list(k),x]for k,x in sorted(self.d.items())]
def co(x):return x if isinstance(x,P)else P(x)
def algebra():
 packet=json.loads((ROOT/'complete83_shared_projection_scout.json').read_text(),object_pairs_hook=unique)['packet'];rows=packet['source'];known=set(packet['free']);ops=collections.Counter()
 for name,op,a,b in rows:
  ck(name not in known and op in '*+-','source definitions');ck(all(type(x)is int or x in known for x in(a,b)),'DAG');known.add(name);ops[op]+=1
 ck(len(rows)==83 and ops=={'*':46,'+':20,'-':17},'ledger');ck(len(packet['witnesses'])==18 and packet['ordinary_input']=='x','ports')
 defs={r[0]:r for r in rows};cache={x:P.var(x)for x in packet['free']};used=set()
 def calc(s):
  if type(s)is int:return P(s)
  if s not in cache:
   _,op,a,b=defs[s];a,b=calc(a),calc(b);cache[s]={'*':lambda:a*b,'+':lambda:a+b,'-':lambda:a-b}[op]();used.add(s)
  return cache[s]
 V={s:P.var(s)for s in packet['free']};J=V['Jrep'];q=V['Bm1']*J+1;F=V['F'];Z=V['Z'];alpha=V['alpha'];scale=V['twice_cell_bits']*V['x'];C=q-F-Z-alpha-scale
 expect={'q':q,'wn2':V['w']*q,'sn2':V['s']*q**3,'marked_rhs':C,'W':C-Z,'odd_index':scale+V['inner_bits'],'r_lhs':(q*q-Z-q*F)*(q*q-1)+(V['MC']+q*V['MF'])*J,'norm_transport':(V['Kconstant']+V['w'])*C+q-F-V['transport_quotient']*(q-1)}
 for name,p in expect.items():ck(calc(name)==p,'actual outer polynomial '+name)
 # Independent formal shifted-index and exceptional factor identities.
 q,F,Z,J,MC,MF,B,D,cell=[P.var(x)for x in ['q','F','Z','J','MC','MF0','B','Dmask','cell']]
 packed=(q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
 shifted=(q*q-(Z-1+q*F))*(q*q-1)+(MC*J+1)+q*(MF*J-1)
 ck(packed-shifted==q*((B-1)*J-(q-1)),'shifted packing exact difference')
 ck(packed-(Z+MC*J)==q*(q**3-q*Z-q*q*F-q+F+(MF+B-1)*J),'low residue quotient')
 rep=1+(B-1)*J;perZ=D*J;perF=cell*J
 perR=(rep*rep-perZ-rep*perF)*(rep*rep-1)+(B-1-D+rep*(MF+B-1))*J
 bracket=rep**3-rep*rep*perF-rep*perZ+(cell+MF)*J
 ck(perR+1==rep*bracket,'exception exact factorization')
 # The integer transport identity factors J before cancellation.
 K,w,z=[P.var(x)for x in ['K','w','z']]
 ck((K+w)*D*J+rep-cell*J-z*(rep-1)-1==J*((K+w)*D-cell+(1-z)*(B-1)),'transport J factor')
 return {'source_rows':len(rows),'M':ops['*'],'A':ops['+']+ops['-'],'positive_witnesses':18,'outer_dependency_rows_expanded':len(used),'eight_outer_targets_sha256':sha(json.dumps({s:p.serial()for s,p in expect.items()},sort_keys=True).encode()),'formal_identities':4,'whole_native_DAG_evaluated':False}
def binomial_cases():
 n=ties=0;branches=collections.Counter();hsh=hashlib.sha256()
 for r in range(3,2048,2):
  cs=[math.comb(2*r,r+j)for j in range(4)];p=r.bit_count();k,l,h=v(r+1),v(r+3),v(r-1)
  ck([v(x)for x in cs]==[p,p-k,p+h-k,p+h-k-l],'adjacent exact valuations')
  if k==1:ck(h>=2 and l>=2 and l<=p+1,'long third denominator')
  else:ck(h==1 and l==1,'short denominators')
  for t in range(4,17):
   for u in range(t+5,3*t+7):
    if p>=3*t+1:continue
    weights=[p,p-k+u,p+h-k+2*u,p+h-k-l+3*u]
    if k==u:ck(weights[:2]==[p,p] and min(weights[2:])>p,'exception tie');ties+=1;continue
    expected=0 if k<u else 1;ck(weights[expected]<min(x for j,x in enumerate(weights)if j!=expected),'unique minimum')
    mod=1<<(3*t+1);res=sum(cs[j]*pow(-(1<<u),j,mod)for j in range(4))%mod
    ck(res and v(res)==weights[expected]<3*t+1,'actual cubed-scale obstruction')
    branches['k=1'if k==1 else '1<k<u'if k<u else 'k>u']+=1;n+=1
    hsh.update(f'{r},{t},{u},{res}\n'.encode())
 return {'exact_nonexception_cases':n,'exact_tied_shapes':ties,'branches':dict(branches),'records_sha256':hsh.hexdigest(),'range':'odd 3<=r<2048; 4<=t<=16; t+5<=u<=3t+6; p<3t+1','all_u_claim':'proved by unique-minimum cases in note; finite evidence is not the proof'}
def rotation_cases():
 n=borrow=0;hsh=hashlib.sha256()
 for b in [5,6,8]:
  V=1<<b
  for L in range(6,10):
   # Abstract native words, not emitted universal-compiler layouts.
   for mask in range(1,1<<(L-5)):
    support=[0]+[e for e in range(2,L-3)if mask>>(e-2)&1]
    for star in support[1:]:
     D=sum(V**e for e in support)+2*V**star;B=V**L
     DC,DR=V**2,V**3;G=(DC+DR)*D
     gd=[G//V**j%V for j in range(L)]
     ck(G<B and max(gd)<=V//4-2 and DR>V and DC%V==0,'coefficient scalar hypotheses')
     for shift in range(b*L):
      Y=(D*pow(2,shift,B-1))%(B-1);yd=[Y//V**j%V for j in range(L)];ell=shift%b;bound=3*(1<<ell)if ell<b-1 else V//2+1
      ck(max(yd)<=bound,'all rotated digits');ck(max(gd[j]+yd[j]for j in range(L))<=V-2,'carry-free addition')
      plus=G+Y;A=plus-V*D
      ck(0<A<plus<B-1 and A%V==Y%V<=3*V//4<V-4,'positive representative/low-digit exclusion')
      take=0;hasborrow=False
      for j in range(L):
       raw=(plus//V**j)%V-((V*D)//V**j)%V-take;take=int(raw<0);hasborrow|=bool(take)
      ck(take==0,'no final underflow');borrow+=hasborrow
      n+=1;hsh.update(f'{b},{L},{D},{shift},{A%V},{int(hasborrow)}\n'.encode())
 ck(borrow>0,'explicit harmless internal borrowing exercised')
 return {'synthetic_cases':n,'cases_with_internal_borrow':borrow,'records_sha256':hsh.hexdigest(),'actual_compiler_instances':False}
def population_cases():
 n=0
 for bits in range(1,8):
  Q=1<<bits
  for S in range(1,Q+1):
   for T in range(1,Q-1):
    pc=((Q-S)*(Q-1)+T).bit_count();threshold=bits+T.bit_count()
    ck(pc<=threshold and (pc==threshold)==(S<Q and S&T==0),'inverse population boundary');n+=1
 return {'exhaustive_cases':n,'bits':[1,7]}
def build():
 for ext,h in PINS.items():ck(sha(Path(str(STEM)+ext).read_bytes())==h,'author pin '+ext)
 author=json.loads(Path(str(STEM)+'.json').read_text(),object_pairs_hook=unique)
 for name,h in author['pins'].items():ck(sha((ROOT/name).read_bytes())==h,'dependency pin '+name)
 paths={'modified_compiler_py':ROOT/'complete75_half_binomial_compiler.py','baseline_compiler_py':ROOT/'../../verification/explore_fixed_raw_universal_76.py','compiler_class_py':ROOT/'../../verification/explore_fixed_raw_universal_78.py','start_end_export_py':ROOT/'../../verification/explore_fixed_raw_universal_77.py','shifted_source_py':ROOT/'complete75_half_binomial.py'}
 # Literal code read as text only, linked to the mathematical layout argument.
 code={k:p.read_text()for k,p in paths.items()}
 for fragment in ['cc.MF_native_poly[0] = 4',"values['MF'] += 4",'4 * mass + 8','cc.radix_bits = baseline.next_five_power']:
  ck(fragment in code['modified_compiler_py'],'modified code guard')
 for fragment in ['L=next_five_power(high_degree+E+1)','for e in (3*a,H+a,8*anchor_unit,24*anchor_unit)','MFpoly={T1:mu,T2:mu}','H=E+24*anchor_unit+3*a+1']:
  ck(fragment in code['baseline_compiler_py'],'baseline code guard')
 ck('def DR(self):return 1<<(self.radix_bits*self.H)' in code['compiler_class_py'],'actual DR binding')
 ck('for e in self.positions if e!=1' in code['start_end_export_py'],'actual MC exclusion')
 ck("env['MF'] = z['MF'] + z['B'] - 1" in code['shifted_source_py'],'actual shifted MF binding')
 return {'author_pins':PINS,'dependency_pins':author['pins'],'compiler_code_pins':{k:sha(p.read_bytes())for k,p in paths.items()},'helper_sha256':sha(Path(__file__).read_bytes()),'source_algebra':algebra(),'binomial_valuations':binomial_cases(),'rotation_and_transport':rotation_cases(),'inverse_population':population_cases(),'scope':{'conditional_q_dyadic_W_zero':True,'new_universal_83':False,'predecessor_execution_or_import':False,'compiler_or_Pell_tuple_materialized':False}}
def main():
 ap=argparse.ArgumentParser();g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();s=json.dumps(build(),sort_keys=True,indent=2)+'\n'
 if a.output:
  with a.output.open('x')as f:f.write(s)
 else:ck(a.expect.read_text()==s,'exact receipt equality')
 print('PASS independent conditional dyadic native-mask proof evidence')
if __name__=='__main__':main()
