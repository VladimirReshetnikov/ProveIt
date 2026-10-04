#!/usr/bin/env python3
"""Pinned complete193 phase transfer that absorbs fixed target contexts."""
import argparse
import copy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path

PINS={
 'matrix193_gamma1_recode.py':'ae24e64539b450fd9c4db0b3e04ce440d00562dcfe532a43002d7c52da34757c',
 'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
 'matrix193_kernel_row_projection.md':'400aab15caa9462808cc2dc2ef68f013797a9bc656c97acecdd610de81a13c6e',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
I=(1,0,0,1); P=(1,2,0,1)
U_CONTEXT='[110'; V_CONTEXT='A0]'
SOURCE=[['scaled11','*',52500,'psi'],['target11','+','chi','scaled11'],['target12','*',-29036,'psi']]

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def pairs(items):
 out={}
 for k,v in items:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def bad(value):raise ValueError('nonfinite JSON '+value)
def read(path):return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def mul(a,b):
 x,y,z,t=a;u,v,w,s=b
 return x*u+y*w,x*v+y*s,z*u+t*w,z*v+t*s

def det(a):return a[0]*a[3]-a[1]*a[2]
def inv(a):
 need(det(a)==1,'SL2 inverse');return a[3],-a[1],-a[2],a[0]
def power(a,n):
 if n<0:a=inv(a);n=-n
 out=I
 while n:
  if n&1:out=mul(out,a)
  a=mul(a,a);n//=2
 return out

def diag(a,b):return [list(a[:2])+[0,0],list(a[2:])+[0,0],[0,0]+list(b[:2]),[0,0]+list(b[2:])]
def blocks(matrix):
 need(all(matrix[i][j]==0 for i,j in itertools.product(range(4),repeat=2) if (i<2)!=(j<2)),'block diagonal')
 return tuple(v for row in matrix[:2] for v in row[:2]),tuple(v for row in matrix[2:] for v in row[2:])
def word(w,codes):
 out=I
 for a in w:out=mul(out,codes[a])
 return out

def ej(j):return 1+4*j,2,-8*j*j,1-4*j

def stats(generators):
 values=[v for g in generators for row in g['matrix'] for v in row]
 return {'generators':len(generators),'entry_slots':len(values),'nonzero_entries':sum(v!=0 for v in values),'maximum_absolute_entry':max(map(abs,values)),'maximum_magnitude_bits':max(abs(v).bit_length() for v in values),'sum_magnitude_bits':sum(abs(v).bit_length() for v in values)}

def apply_source(source,env,outputs):
 values=dict(env)
 for name,op,left,right in source:
  a=left if type(left) is int else values[left];b=right if type(right) is int else values[right]
  values[name]=a*b if op in ('*','mul') else a+b
 return [values[x] for x in outputs]

def ledger(source,free,outputs):
 seen=set(free);deps={};M=A=0
 for n,op,a,b in source:
  need(n not in seen and op in ('*','+','mul','add'),'source row')
  for x in (a,b):need(type(x) is int or x in seen,'source closure')
  deps[n]=[x for x in (a,b) if type(x) is str];seen.add(n)
  M+=op in ('*','mul');A+=op in ('+','add')
 live=set();pending=list(outputs)
 while pending:
  x=pending.pop()
  if x not in live:live.add(x);pending.extend(deps.get(x,()))
 need(live==seen,'all source ports and operations live')
 return {'M':M,'A':A,'total':M+A,'outputs':outputs,'free':sorted(free),'source':source}

def product(names,lookup):
 upper=lower=I
 for name in names:
  a,b=blocks(lookup[name]['matrix']);upper=mul(upper,a);lower=mul(lower,b)
 return upper,lower

def verify(root):
 for name,pin in PINS.items():need(sha((root/name).read_bytes())==pin,'pin '+name)
 parent=read(root/'matrix193_gamma1_recode.json')
 need(parent['source_sha256']==PINS['matrix193_gamma1_recode.py'],'parent self source')
 packet=parent['packet'];codes={k:tuple(v) for k,v in packet['letters'].items()}
 L=inv(word(V_CONTEXT+'#',codes));R=inv(word(U_CONTEXT,codes));Li=inv(L);Ri=inv(R)
 old_by={g['name']:g for g in packet['generators']};new=[];phase_checks=0
 for tile in packet['tiles']:
  i=tile['id'];e=ej(i)
  for kind in ('A','B'):
   old=old_by[kind+str(i)];upper,lower=blocks(old['matrix'])
   expected=word(tile['h'],codes) if kind=='A' else inv(word(tile['g'],codes))
   expected_lower=e if kind=='A' else mul(mul(inv(P),inv(e)),P)
   need(upper==expected and lower==expected_lower,'actual parent tile producer')
   altered=mul(mul(Li,upper),L) if kind=='A' else mul(mul(R,upper),Ri)
   need((mul(L,altered)==mul(upper,L)) if kind=='A' else (mul(altered,R)==mul(R,upper)),'phase conjugation identity')
   new.append({'name':old['name'],'tile_id':i,'matrix':diag(altered,lower)});phase_checks+=1
 oldC,lowerC=blocks(old_by['C']['matrix']);need(oldC==inv(word('[J1]#',codes)) and lowerC==P,'parent central producer')
 newC=mul(mul(Li,oldC),Ri);need(mul(mul(L,newC),R)==oldC,'central bridge identity')
 new.append({'name':'C','tile_id':None,'matrix':diag(newC,lowerC)});phase_checks+=1
 new_by={g['name']:g for g in new};new=[new_by[g['name']] for g in packet['generators']]
 need(len(new)==193 and len({tuple(v for row in g['matrix'] for v in row) for g in new})==193,'complete distinct193')
 for old,g in zip(packet['generators'],new):
  a,b=blocks(g['matrix']);oa,ob=blocks(old['matrix']);need(b==ob and det(a)==det(b)==1,'unchanged lower/determinants')
  need(a[0]%5==a[3]%5==1 and a[2]%5==0,'Gamma1 congruence')
 ids=[t['id'] for t in packet['tiles']]
 samples=[[]]+[[i] for i in ids]+[[ids[i],ids[(7*i+3)%96]] for i in range(32)]+[[ids[i],ids[(i+19)%96],ids[(i+47)%96]] for i in range(16)]
 for seq in samples:
  names=['A'+str(i) for i in seq]+['C']+['B'+str(i) for i in reversed(seq)]
  oldtop,oldbottom=product(names,old_by);top,bottom=product(names,new_by)
  need(oldbottom==bottom==P and top==mul(mul(Li,oldtop),Ri),'complete shaped product transfer')
 witness=parent['accepting_witness'];need(witness['input']==U_CONTEXT+V_CONTEXT,'fixture input context split')
 top,bottom=product(witness['generator_word'],new_by)
 need(len(witness['generator_word'])==167 and top==I and bottom==P,'genuine transferred accepted product')
 W=word('01010111',codes);B=mul(W,W);a0=(B[0]+B[3])//2;D=(B[0]-a0,B[1],B[2],B[3]-a0)
 need(a0==391 and D==(-52500,29036,-94920,52500),'actual Pell391 matrix')
 need(mul(D,D)==(152880,0,0,152880),'quadratic power algebra')
 C=mul(L,R);F=mul(mul(L,D),R)
 need(mul(mul(Li,C),Ri)==I and mul(mul(Li,F),Ri)==D,'all-value coefficient transfer')
 generic=ledger(parent['projected_target']['generic_source'],{'A11','A12','C11','C12','chi','psi'},['target11','target12'])
 bare=ledger(SOURCE,{'chi','psi'},['target11','target12'])
 need((generic['total'],bare['M'],bare['A'],bare['total'])==(6,2,1,3),'paid target ledgers')
 coefficients={'A11':C[0],'A12':C[1],'C11':-F[0],'C12':-F[1]}
 signed=[(i-7,2*i-13) for i in range(16)]+[(Fraction(i-4,3),Fraction(2*i-7,5)) for i in range(12)]
 for chi,psi in signed:
  oldtarget=tuple(chi*c-psi*f for c,f in zip(C,F));target=tuple(chi*c-psi*f for c,f in zip(I,D))
  need(mul(mul(Li,oldtarget),Ri)==target,'whole signed/rational coefficient transfer')
  need(apply_source(generic['source'],dict(coefficients,chi=chi,psi=psi),generic['outputs'])==list(oldtarget[:2]),'generic full source')
  need(apply_source(SOURCE,{'chi':chi,'psi':psi},bare['outputs'])==list(target[:2]),'bare full source')
 chi,psi=1,0;powers=[]
 for x in range(13):
  target=power(B,-x);oldtarget=inv(word(U_CONTEXT+'01010111'*(2*x)+V_CONTEXT+'#',codes))
  need(mul(mul(Li,oldtarget),Ri)==target and list(target[:2])==apply_source(SOURCE,{'chi':chi,'psi':psi},bare['outputs']),'literal ordinary-input family')
  powers.append({'x':x,'chi':chi,'psi':psi,'target_first_row':list(target[:2])})
  chi,psi=391*chi+152880*psi,chi+391*psi
 # Whole-group collisions only: these are not asserted to be semigroup false targets.
 J=codes['J'];A=codes['A'];need(J==(1,9,0,1) and A==(-19,10,-40,21),'actual parabolic subgroup ports')
 collision_checks=0
 for p,q in ((0,1),(1,0),(1,1),(2,-3),(-5,7),(9,4),(-2,-1)):
  if q:a=power(A,9*q);b=power(J,10*q-20*p)
  else:a=I;b=J
  need(a!=b and p*a[0]+q*a[1]==p*b[0]+q*b[1],'linear first-row collision');collision_checks+=1
 # Numeric counterexample to mistakenly asserting an all-generator global conjugation.
 first=packet['generators'][0]['name'];oldtop,_=blocks(old_by[first]['matrix']);newtop,_=blocks(new_by[first]['matrix'])
 need(newtop!=mul(mul(Li,oldtop),Ri),'phase transfer is not a global two-sided homomorphism')
 result_packet={'schema':'directed193-fixed-context-phase-transfer-v1','U':U_CONTEXT,'V':V_CONTEXT,'L':list(L),'R':list(R),'alphabet':copy.deepcopy(packet['alphabet']),'letters':copy.deepcopy(packet['letters']),'separator':packet['separator'],'terminal':packet['terminal'],'rules':copy.deepcopy(packet['rules']),'tiles':copy.deepcopy(packet['tiles']),'generators':new,'ledger':stats(new)}
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packet':result_packet,'parent_statistics':stats(packet['generators']),'target_comparison':{'generic_six':generic,'absorbed_three':bare,'fixture_generic_coefficients':coefficients,'index_relation_paid':False,'membership_certificate_paid':False},'block':{'word':'01010111','W':list(W),'B':list(B),'D':list(D),'Pell_parameter':391,'checks':powers},'accepting_witness':{'ordinary_parameter':0,'input_word':witness['input'],'generator_word':witness['generator_word'],'product':diag(top,bottom),'target':diag(I,P)},'linear_projection_obstruction':{'scope':'Fixed integer affine functionals of the first row on the unchanged group H prime only','J':list(J),'A':list(A),'q_nonzero_exponents':{'A_power':'9q','J_power':'10q-20p'},'q_zero_pair':['I','J'],'not_a_false_input_claim':True},'evidence':{'complete_generators':193,'complete_entries':3088,'phase_matrix_identities':phase_checks,'shaped_product_checks':len(samples),'accepted_product_length':167,'signed_rational_checks':len(signed),'rational_checks':12,'Pell_literal_family_checks':13,'linear_projection_examples':collision_checks},'scope':'Arbitrary fixed contexts admit the proved phase transfer; one complete concrete fixture is saved. Program-specific generators differ from the original fixed universal S193. Correct index and unbounded membership remain unpaid.','new_universal_Diophantine_bound':False,'predecessor_code_executed':False}

def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
 mode=parser.add_mutually_exclusive_group(required=True);mode.add_argument('--expect',type=Path);mode.add_argument('--output',type=Path);args=parser.parse_args()
 result=verify(args.root.resolve())
 if args.expect:need(exact(result,read(args.expect)),'type-exact receipt')
 else:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','evidence':result['evidence'],'ledger':result['packet']['ledger'],'target_operations':3},sort_keys=True))
if __name__=='__main__':main()
