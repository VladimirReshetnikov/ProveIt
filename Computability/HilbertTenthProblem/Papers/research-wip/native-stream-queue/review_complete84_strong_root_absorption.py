"""Independent strong-root source/zero/sign checks. Frozen code stays inert."""
import argparse,hashlib,json
from math import comb
from pathlib import Path
AUTHOR={
'complete84_strong_root_absorption.py':'3d17fb1bdf7e3942bedcc873ee87a244ef66aa1188eaafb732828965ebfc670c',
'complete84_strong_root_absorption.json':'424ba5aaa6e1ebc8525e4eaaaca7f7489282c7533d775dac86d10a659684986a',
'complete84_strong_root_absorption.md':'b73fb50aebb8de23a282aff91c389d74b4bd96dadd355c43eb7e7783c1b6abc2'}
SOURCE_SHA='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
SIGNED_SHA='c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00'
def ck(v,s):
 if not v:raise ValueError(s)
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def C(x):return {():x} if x else {}
def V(x):return {(x,):1}
def plus(a,b,s=1):
 d=dict(a)
 for k,c in b.items():d[k]=d.get(k,0)+s*c
 return {k:c for k,c in d.items() if c}
def times(a,b):
 d={}
 for k,c in a.items():
  for j,v in b.items():
   n=tuple(sorted(k+j));d[n]=d.get(n,0)+c*v
 return {n:c for n,c in d.items() if c}
def prod(*xs):
 r=C(1)
 for x in xs:r=times(r,x)
 return r
def power(x,n):return prod(*[x for _ in range(n)])
def records(x):return [[list(m),c] for m,c in sorted(x.items())]
def closed_chi(n):
 # Direct even binomial expansion, independent of the author's recurrence.
 A=V('A');disc=plus(power(A,2),C(1),-1);out={}
 for j in range(n//2+1):out=plus(out,prod(C(comb(n,2*j)),power(A,n-2*j),power(disc,j)))
 return out
def compose(p,q):
 r={}
 for m,c in p.items():
  ck(set(m)<={'A'},'univariate polynomial');r=plus(r,prod(C(c),power(q,len(m))))
 return r
def build(root,author,signedroot):
 for n,h in AUTHOR.items():ck(sha((author/n).read_bytes())==h,'author pin '+n)
 rec=read(author/'complete84_strong_root_absorption.json')
 ck(rec['source_sha256']==AUTHOR['complete84_strong_root_absorption.py'],'author helper binding')
 ck(len(rec['pins'])==9 and rec['pins']['complete84_scaled_strong_output.json']==SOURCE_SHA and rec['pins']['complete84_signed_quotient_absorption.json']==SIGNED_SHA,'source/lemma pins')
 for n,h in rec['pins'].items():
  at=signedroot if n.startswith('complete84_signed_quotient_absorption.') else root
  ck(sha((at/n).read_bytes())==h,'inert dependency '+n)
 p=read(root/'complete84_scaled_strong_output.json')['packet'];sg=read(signedroot/'complete84_signed_quotient_absorption.json')
 ck(p['source']==rec['authenticated_source']==sg['authenticated_parent_source'],'whole actual84 source')
 ck(sg['source_sha256']==rec['pins']['complete84_signed_quotient_absorption.py'],'signed helper binding')
 ck(sg['theorem']['normalized_rank']=='c=psi_p(A0), f=chi_m(A0), psi_m(A0)=i*c^2, p*c divides m, p=R','required normalized rank')
 ck(sg['theorem']['old85_bound']=='absolute values <c^4' and not sg['theorem']['positive_T_parent_restoration_used'],'signed exterior lemma scope')
 d={};dep={n:{n} for n in p['free']};aux={'i','f','auxiliary_quotient','y_aux'}
 for row in p['source']:
  ck(type(row)is list and len(row)==4,'binary row');n,o,a,b=row
  ck(n not in dep and type(n)is str and o in ['+','-','*'],'SSA/opcode')
  ck(all(type(v)is int or type(v)is str and v in dep for v in [a,b]),'actual source topology')
  d[n]=row;dep[n]=set().union(*[dep[v] for v in [a,b] if type(v)is str])
 outside=[n for n in d if not dep[n]&aux];free=[n for n in p['free'] if n not in aux]
 ck((len(d),len(p['free']),len(outside),len(free))==(84,25,64,21),'full literal source/interface')
 ck(sum(r[1]=='*' for r in p['source'])==47,'47M37A unchanged ledger')
 ck(outside==rec['source_evidence']['computed_exterior']==sg['census']['old_computed'],'computed85 interface')
 ck(free==rec['source_evidence']['supplied_exterior']==sg['census']['old_free'],'supplied85 interface')
 ck([r for r in p['source'] if 'f' in r[2:]]==[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']],'two f consumers')
 ck([r for r in p['source'] if 'auxiliary_quotient' in r[2:]]==[['auxiliary_Tf','*','auxiliary_quotient','f']],'one T consumer')
 # Exact positive Delta boundary uses only the unchanged positive ports.
 for row in [['wn2','*','w','q'],['sn2','*','s','n2'],['UM','*','wn2','sn2'],['R12','+','UM','sn2'],['a_square','*','R12','R12'],['a4','*',4,'R12'],['a4m5','+','a4',3],['A','+','a_square','a4m5']]:ck(d[row[0]]==row,'pre-equation positive discriminant')
 factors=['norm_first','norm_main','norm_input','norm_index','norm_transport'];cuts=factors+['A','R10a','r_lhs']
 ck(set(cuts)<=set(outside),'auxiliary-independent actual cuts')
 ancestors=set()
 def expand(sign=1,zero=False):
  memo={n:V(n) for n in p['free']+cuts}
  memo['f']={} if zero else prod(C(sign),V('f'))
  memo['auxiliary_quotient']=prod(C(sign),V('auxiliary_quotient'))
  def at(n):
   if type(n)is int:return C(n)
   if n not in memo:
    ancestors.add(n);_,o,a,b=d[n];x,y=at(a),at(b);memo[n]=times(x,y) if o=='*' else plus(x,y,1 if o=='+' else -1)
   return memo[n]
  return at(p['output'])
 full,negative,zero=expand(),expand(-1),expand(zero=True)
 Delta,c,R,i,f,T,y=[V(n) for n in ['A','R10a','r_lhs','i','f','auxiliary_quotient','y_aux']]
 P5=prod(*[V(n) for n in factors]);Q=power(prod(Delta,i,c,c),2)
 v=plus(prod(c,plus(prod(T,f),C(1),-1)),prod(R,f,f),-1)
 Na=plus(prod(Q,plus(power(v,2),power(y,2),-1)),power(y,2))
 Ns=plus(prod(Delta,f,f),Q,-1)
 ck(full==plus(prod(P5,Na,Ns),Delta,-1)==negative,'full source factor/sign identity')
 Na0=plus(prod(Q,plus(power(c,2),power(y,2),-1)),power(y,2))
 zeroform=prod(C(-1),Delta,plus(prod(Delta,i,i,c,c,c,c,P5,Na0),C(1)))
 ck(zero==zeroform and len(full)==17 and len(zero)==4 and len(ancestors)==24,'complete zero/sign output identities')
 ck(all('auxiliary_quotient' not in m and 'f' not in m for m in zero),'both f and T disappear at zero')
 ck(records(full)==rec['source_evidence']['full_coefficients'] and records(zero)==rec['source_evidence']['zero_f_coefficients'],'saved source coefficients')
 # Independent closed-binomial polynomials verify all recorded compositions.
 polynomials=[closed_chi(n) for n in range(37)];composition=[]
 for r in range(1,7):
  for s in range(1,7):
   value=compose(polynomials[s],polynomials[r]);ck(value==polynomials[r*s],'formal chi composition')
   composition.append([r,s,len(value)])
 ck(composition==rec['corroboration']['formal_composition_identities'],'36 composition records')
 for D,n in rec['corroboration']['strict_growth_cases']:
  value=sum(c0*D**len(m) for m,c0 in polynomials[n].items());ck(value>D**n,'strict growth')
 for t,L,bound in rec['corroboration']['cutoff_cases']:
  ceiling=0
  while 2**ceiling<L:ceiling+=1
  ck(bound==4*t+ceiling,'strict integer cutoff')
  for c0 in [max(2,bound),max(2,bound)+1]:ck(c0**c0>=L*c0**(4*t),'both cutoff endpoints')
 return dict(status='PASS_INDEPENDENT_STRONG_ROOT_ABSORPTION',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,inert_pins=rec['pins'],
  source_sha256_actual84=sha(enc(p['source'])),source_counts=dict(total=84,M=47,A=37,free_ports=25),computed_exterior=outside,supplied_exterior=free,
  actual_cuts=cuts,expanded_ancestors=sorted(ancestors),full_coefficients=records(full),zero_f_coefficients=records(zero),full_simultaneous_sign_identity=True,
  binomial_composition_records=composition,growth_cases=len(rec['corroboration']['strict_growth_cases']),cutoff_cases=len(rec['corroboration']['cutoff_cases']),
  scope=dict(fixed_integer_polynomial_only=True,zero_sector_empty_before_rank=True,sign_map_uses_signed_T_lemma=True,
   frozen_execution=False,new_complete_source=False,new_native_zero_fixture=False,exact84_degree_reaudit=False))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path);ap.add_argument('--signed-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();r=build(a.root,a.author_root or a.root,a.signed_root or a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(enc(r)==enc(read(a.expect)),'exact independent receipt')
 print(r['status'],'85 exterior ports; simultaneous sign and zero-f identities')
if __name__=='__main__':main()
