#!/usr/bin/env python3
"""Fresh source-byte, polynomial and radix-digit checks. No predecessor runs."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

AUTHOR=Path('/tmp/complete83_outer_family_two_primary')
PINS={'md':'fe9378a51f61d35147ec11dfed0aae8c0d0fc795d7e3afcec5cd22a01df9906b','py':'f595bb59d34f3ce0bb3a469ab7ea93feefe373ac5642ca0be5a78a1eb3b374d6','json':'0ec74608dfd8550c7478a39ff902351304e66ecc2d06f011f5cfdaab5e4d6e35'}

def ck(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def v2(n):
 ck(n>0,'positive valuation');return (n&-n).bit_length()-1

def formal():
 # Independent four-variable rational polynomials, including the entire mask symbol S.
 def mono(index):
  x=[0]*4;x[index]=1;return {tuple(x):Fraction(1)}
 def const(c):return {(0,0,0,0):Fraction(c)} if c else {}
 def plus(*polys):
  out={}
  for poly in polys:
   for e,c in poly.items():out[e]=out.get(e,0)+c
  return {e:c for e,c in out.items() if c}
 def scale(p,c):return {e:v*c for e,v in p.items() if v*c}
 def times(p,q):
  out={}
  for e,c in p.items():
   for f,d in q.items():
    g=tuple(ei+fi for ei,fi in zip(e,f));out[g]=out.get(g,0)+c*d
  return {e:c for e,c in out.items() if c}
 def power(p,n):
  out=const(1)
  for _ in range(n):out=times(out,p)
  return out
 Q,F,z,S=[mono(i) for i in range(4)];one=const(1);answers={}
 for shape in ('plus','minus'):
  q=scale(plus(power(Q,2),Q),Fraction(1,2)) if shape=='plus' else plus(scale(power(Q,2),2),scale(Q,-1))
  original=plus(times(plus(power(q,2),scale(z,-1),scale(times(q,F),-1)),plus(power(q,2),const(-1))),S)
  c=16 if shape=='plus' else 1
  target=scale(original,c)
  if shape=='plus':
   rows=[(8,1,0,0),(7,4,0,0),(6,6,-2,0),(5,4,-6,0),(4,-3,-6,-4),(3,-8,-2,-8),(2,-4,8,-4),(1,0,8,0),(0,0,0,16)]
  else:
   rows=[(8,16,0,0),(7,-32,0,0),(6,24,-8,0),(5,-8,12,0),(4,-3,-6,-4),(3,4,1,4),(2,-1,2,-1),(1,0,-1,0),(0,0,0,1)]
  expected=scale(S,c)
  for exponent,a,b,d in rows:
   coefficient=plus(const(a),scale(F,b),scale(z,d))
   expected=plus(expected,times(power(Q,exponent),coefficient))
  ck(target==expected,'complete formal polynomial '+shape)
  data=[[list(e),str(v)] for e,v in sorted(target.items())]
  answers[shape]={'terms':data,'sha256':sha(json.dumps(data,separators=(',',':')).encode())}
 return answers

def digits_case(d,K,shape,n,MC,MF,z,expected=None):
 B=1<<d;D=d*n;Q=1<<D;F=K*z
 H=64*(4*d*K+4*d+1);width=H.bit_length();threshold=3*width+5
 q=Q*(Q+1)//2 if shape=='plus' else Q*(2*Q-1)
 J=(q-1)//(B-1);mask=(MC+q*MF)*J
 ck(4<=F and F<=4*d*K and 1<=z<=4*d and MC%4==2 and 0<MC<B-1 and 0<MF<2*(B-1),'scalar domains')
 ck(n>=5 and Q>H and Q>=32 and d>=25,'digit domain')
 ck((B-1)*J==q-1 and 0<mask<2*q*q,'repunit/mask size')
 R=(q*q-z-q*F)*(q*q-1)+mask;r=(R-1)//2
 ck(R%4==3 and 0<R<q**4,'index interval')
 # Extract an entire base-Q expansion directly by quotient/remainder.
 scaled=R*16 if shape=='plus' else R
 qdigits=[];remaining=scaled
 while remaining:
  remaining,digit=divmod(remaining,Q);qdigits.append(digit)
 if shape=='plus':
  high=Q**4+4*Q**3+(6-2*F)*Q**2+(4-6*F)*Q-6*F-4*z-3
  deficits={4:None,5:6*F-3,6:2*F-5}
  carrymax=9
 else:
  high=16*Q**4-32*Q**3+(24-8*F)*Q**2+(12*F-8)*Q-6*F-4*z-3
  deficits={4:None,6:8*F-24,7:33};carrymax=8
 carry=scaled//Q**4-high;deficits[4]=6*F+4*z+3-carry
 ck(-1<=carry<=carrymax,'low-tail carry interval')
 for pos,deficit in deficits.items():
  ck(0<deficit<H<Q and qdigits[pos]==Q-deficit,'complement digit')
  ck(qdigits[pos].bit_count()==D-(deficit-1).bit_count()>=D-width,'complement population')
 if shape=='plus':ck(qdigits[7:]==[3,1],'plus high borrows terminate')
 else:ck(qdigits[5]==12*F-9 and qdigits[8:]==[15],'minus high borrows terminate')
 # Entire low window is read directly, including its first two carry-affected digits.
 low=[];lowword=R%(B**(n-1));remaining=lowword
 for _ in range(n-1):remaining,digit=divmod(remaining,B);low.append(digit)
 ck(remaining==0 and low[2:]==[MC]*(n-3),'all repeated MC digits')
 rep=(B**(n-1)-1)//(B-1)
 ck(lowword==(z+MC*rep)%(B**(n-1)),'low word identity')
 for offset in (1,5):
  value=(R+offset)%(B*B)
  ck(value>0 and (value//B) in (MC,MC+1),'denominator carry stops in cell one')
  ck(v2(R+offset)<2*d,'bounded valuations')
 shift=4 if shape=='plus' else 0
 highpositions=set(deficits)
 ck((n-1)*d+shift<=D and min(highpositions)*D>=4*D,'disjoint low/high support intervals')
 low_population=sum(x.bit_count() for x in low[2:]);high_population=sum(qdigits[j].bit_count() for j in highpositions)
 ck(scaled.bit_count()==R.bit_count() and R.bit_count()>=low_population+high_population,'disjoint population addition')
 pop=r.bit_count();lower=3*D-3*width+n-4
 ck(pop==R.bit_count()-1 and pop>=lower,'central population bound')
 t=v2(q)
 if n>=threshold:ck(pop>=3*D+1>=3*t+1,'eventual threshold')
 # Kummer's identity calculates coefficient valuations without creating binomials.
 coeff_v=[(r-j).bit_count()+(r+j).bit_count()-(2*r).bit_count() for j in range(4)]
 for alpha in (2*D+5,2*D+22):
  weighted=[coeff_v[j]+j*alpha for j in range(4)]
  ck(weighted[0]==pop and all(x>pop for x in weighted[1:]),'unique central minimum')
  ck(pop<=8*D+3<4*alpha,'all higher terms strictly higher')
 record={'d':d,'shape':shape,'K':str(K),'n':n,'MC_kind':'small' if MC==2 else 'dense','MF_kind':'low' if MF==B else 'high','z':z,'ell':width,'threshold':threshold,'epsilon':carry,'central_population':pop,'population_lower_bound':lower,'t':t,'denominator_k':v2(r+1),'denominator_ell':v2(r+3),'R_bits':R.bit_length()}
 if expected:
  for key,value in expected.items():ck(record[key]==value,'saved record '+key)
 return record

def build():
 ck(set(PINS)=={'md','json','py'},'wait for frozen author pins')
 authenticated=[]
 for ext,pin in PINS.items():
  path=AUTHOR.with_suffix('.'+ext);data=path.read_bytes();ck(sha(data)==pin,'author pin')
  authenticated.append({'name':path.name,'bytes':len(data),'sha256':pin})
 author=json.loads(AUTHOR.with_suffix('.json').read_text())
 ck(author['helper_sha256']==PINS['py'],'author helper binding')
 deps=[]
 for path,rec in author['dependencies'].items():
  data=Path(path).read_bytes();ck(sha(data)==rec['sha256'] and len(data)==rec['bytes'],'dependency pin')
  deps.append({'path':path,**rec})
 source_path=next(r['path'] for r in deps if r['path'].endswith('complete83_shared_projection_scout.json'))
 source=json.loads(Path(source_path).read_text())['packet']['source'];defs={r[0]:r for r in source}
 ck(len(source)==83,'source rows')
 for row in author['source_guard']['rows']:ck(defs[row[0]]==row,'literal binding')
 records=[]
 for old in author['digit_checks']['records']:
  d=old['d'];B=1<<d;shape=old['shape'];K=B+(2 if shape=='plus' else 1)
  MC=2 if old['MC_kind']=='small' else B-2;MF=B if old['MF_kind']=='low' else 2*B-3
  records.append(digits_case(d,K,shape,old['n'],MC,MF,old['z'],old))
 ck(len(records)==64,'saved cases')
 extras=[]
 for shape,residue in [('plus',4),('minus',3)]:
  d=25;B=1<<d;K=(B*(1<<6)//5)*5+residue
  width=(64*(4*d*K+4*d+1)).bit_length();threshold=3*width+5;nstar=threshold+(1-threshold)%4
  for n in (5,nstar,nstar+4):
   for z in (1,4*d-3):
    for MC in (2,B-2):extras.append(digits_case(d,K,shape,n,MC,2*B-3,z))
 return {'schema':'independent eventual outer-family two-primary review v1','source_sha256':sha(Path(__file__).read_bytes()),'author_pins':authenticated,'dependencies':deps,'formal_expansions':formal(),'saved_cases_reconstructed':records,'additional_synthetic_cases':extras,'status':'PASS','scope':{'actual_compiler_instantiated':False,'native_masks_decoded':False,'X_or_full_binomial_materialized':False,'odd_primary_success_claim':False,'full_source_zero_claim':False,'universal83_claim':False,'predecessor_program_run':False}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--expect',type=Path);p.add_argument('--output',type=Path,default=Path('/tmp/review_complete83_outer_family_two_primary.json'));a=p.parse_args()
 r=build();raw=(json.dumps(r,sort_keys=True,indent=2)+'\n').encode()
 if a.expect:ck(raw==a.expect.read_bytes(),'exact receipt replay')
 else:a.output.write_bytes(raw)
 print(json.dumps({'status':'PASS','saved_cases':len(r['saved_cases_reconstructed']),'extra_cases':len(r['additional_synthetic_cases']),'receipt_sha256':sha(raw)}))
if __name__=='__main__':main()
