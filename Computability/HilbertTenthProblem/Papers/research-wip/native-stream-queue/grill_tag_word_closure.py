#!/usr/bin/env python3
"""Paid finite Grill word closure. External horizon; no universal decoder claim."""
if not __debug__:raise RuntimeError('Run this research checker without -O')
import argparse,hashlib,itertools,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path

def need(v,m):
 if not v:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def build(program,horizon,*,mode='scaled',square_boolean=False):
 need(type(program)is tuple and bool(program) and all(type(n)is int and n>=0 for n in program),'Nonempty exact natural tuple program required')
 need(type(horizon)is int and horizon>=1,'Positive external integer horizon required')
 need(type(mode)is str and mode in ('direct','scaled'),'Unknown circuit mode')
 need(type(square_boolean)is bool,'Exact Boolean required')
 rows=[];seen={}
 def gate(label,op,a,b):
  need(op in ('+','-','*'),'Operation')
  if type(a)is int and type(b)is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='+':
   if a==0:return b
   if b==0:return a
  if op=='-' and b==0:return a
  if op=='*':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if op in ('+','*') and repr(a)>repr(b):a,b=b,a
  key=(op,a,b)
  if key in seen:return seen[key]
  need(all(label!=r[0] for r in rows),'Duplicate label')
  rows.append((label,op,a,b));seen[key]=label;return label
 P0=gate('P0','+',gate('three_x','*',3,'x'),'Z0')
 scale=1 if mode=='direct' else P0;total=0;binary=0;bools=[];heads=[];scales=[scale];weighted=[]
 for i in range(horizon):
  d=gate(f'd{i}','-',f'D{i}',1);heads.append(d);a=2*4**program[i%len(program)]-1
  if mode=='direct':
   term=gate(f'T{i}','*',d,scale)
   R=gate(f'R{i}','+',1,gate(f'ad{i}','*',a,d))
   scale=gate(f'S{i+1}','*',scale,R)
  else:
   term=gate(f'T{i}','*',d,scale)
   scale=gate(f'A{i+1}','+',scale,gate(f'aT{i}','*',a,term))
  total=gate(f'acc{i}','+',total,term);weighted.append(term);scales.append(scale)
  binary=gate(f'B{i}','+',binary,gate(f'bit{i}','*',1<<i,d))
  dm=gate(f'dm{i}','-',d,1);bools.append(gate(f'boolean{i}','*',d,dm))
 if mode=='direct':
  final_scale=gate('scaled_width','*',P0,scale);final_total=gate('scaled_content','*',P0,total)
 else:final_scale=scale;final_total=total
 r0=gate('width_residual','-',final_scale,1<<horizon)
 content=gate('content_ZE','+','Z0',final_total)
 content=gate('content_sum','+',content,gate('three_B','*',3,binary))
 r1=gate('content_residual','-',content,1<<horizon)
 terms=[gate('width_square','*',r0,r0),gate('content_square','*',r1,r1)]
 terms += [gate(f'boolean_square{i}','*',b,b) if square_boolean else b for i,b in enumerate(bools)]
 out=terms[0]
 for i,v in enumerate(terms[1:],1):out=gate(f'sum{i}','+',out,v)
 counts=Counter(op for _,op,_,_ in rows)
 return dict(kind='grill_finite_word_closure',program=program,horizon=horizon,mode=mode,square_boolean=square_boolean,
  inputs=['x'],witnesses=['Z0']+[f'D{i}' for i in range(horizon)],source=rows,output=out,
  residuals=[r0,r1]+bools,boolean_residuals=bools,
  registers=dict(P0=P0,head_digits=heads,scales=scales,weighted_terms=weighted,total=total,binary=binary,final_width=final_scale,final_scaled_content=final_total),
  ledger=dict(operations=len(rows),M=counts['*'],A=counts['+']+counts['-'],positive_witnesses=horizon+1,residuals=horizon+2,exact_degree=2*horizon+2),
  scope='Positive integer x,Z0,D_i; fixed natural program and external horizon. Zero implies padded-input halt at or before horizon; a halt exactly at horizon gives zero. No fixed-arity or universal decoder claim.')

def checked(p):
 need(type(p)is dict,'Canonical packet required')
 q=build(p.get('program'),p.get('horizon'),mode=p.get('mode'),square_boolean=p.get('square_boolean'))
 need(exact(p,q),'Noncanonical full packet');return p

def execute(rows,values):
 env=dict(values)
 for n,op,a,b in rows:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return env

def evaluate(p,values,*,signed=False):
 p=checked(p);need(type(signed)is bool,'Exact signed flag required')
 need(type(values)is dict and values.keys()==set(p['inputs']+p['witnesses']),'Exact full coordinate assignment required')
 need(all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integers required (or signed=True for algebra checks)')
 return execute(p['source'],values)[p['output']]

def macro(w,n):
 need(type(w)is str and set(w)<=set('01'),'Binary word required')
 need(type(n)is int and n>=0,'Natural exponent required')
 return None if not w else w[1:]+('0'+'10'*n if w[0]=='1' else '')

def first_halt(program,w,limit):
 heads=[]
 for i in range(limit):
  if not w:return i,heads
  heads.append(int(w[0]));w=macro(w,program[i%len(program)])
 return (limit,heads) if not w else (None,heads)

def direct_values(program,heads):
 S=1;C=0;B=0;scales=[1]
 for i,d in enumerate(heads):
  C+=d*S;B+=(1<<i)*d;S*=1+(2*4**program[i%len(program)]-1)*d;scales.append(S)
 return S,C,B,scales

def decode_zero(p,values):
 need(evaluate(p,values)==0,'Positive zero required')
 t=p['horizon'];heads=[values[f'D{i}']-1 for i in range(t)]
 need(all(d in (0,1) for d in heads),'Boolean zero implication')
 S,C,B,scales=direct_values(p['program'],heads);P0=3*values['x']+values['Z0']
 need(P0*S==1<<t and P0>3*values['x'] and P0&(P0-1)==0,'Dyadic input proof')
 length=P0.bit_length()-1
 w=''.join(str((values['x']>>i)&1) for i in range(length))
 G=''.join('0'+'10'*p['program'][i%len(p['program'])] for i,d in enumerate(heads) if d)
 h=''.join(map(str,heads));need(w+G==h,'Global word equality')
 halt,actual_heads=first_halt(p['program'],w,t)
 need(halt is not None and actual_heads==heads[:halt],'Stop-at-first-empty soundness')
 return dict(input_word=w,head_word=h,appendant_word=G,initial_width=P0,scale=S,C=C,B=B,actual_first_halt=halt,external_horizon=t,
  has_posthalt_extension=halt<t,formal_widths=[str(Fraction(P0*s,1<<i)) for i,s in enumerate(scales)])

# An independent exact sparse polynomial implementation for complete source checks.
def add(a,b,sgn=1):
 c=dict(a)
 for k,v in b.items():c[k]=c.get(k,0)+sgn*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c=Counter()
 for ka,va in a.items():
  for kb,vb in b.items():c[tuple(sorted(ka+kb))]+=va*vb
 return {k:v for k,v in c.items() if v}
def constant(v):return {():v} if v else {}
def polynomial_source(p):
 e={n:{(n,):1} for n in p['inputs']+p['witnesses']}
 for n,o,a,b in p['source']:
  a=e[a] if type(a)is str else constant(a);b=e[b] if type(b)is str else constant(b)
  e[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 return e

def independent_polynomial(program,t,square_boolean):
 one=constant(1);x={('x',):1};z={('Z0',):1};P=add(mul(constant(3),x),z);S=one;C={};B={};booleans=[]
 for i in range(t):
  d=add({(f'D{i}',):1},one,-1);C=add(C,mul(S,d));B=add(B,mul(constant(1<<i),d))
  S=mul(S,add(one,mul(constant(2*4**program[i%len(program)]-1),d)))
  booleans.append(mul(d,add(d,one,-1)))
 r0=add(mul(P,S),constant(1<<t),-1)
 r1=add(add(add(z,mul(P,C)),mul(constant(3),B)),constant(1<<t),-1)
 F=add(mul(r0,r0),mul(r1,r1))
 for b in booleans:F=add(F,mul(b,b) if square_boolean else b)
 return F,[r0,r1]+booleans

def source_audit(p):
 known=set(p['inputs']+p['witnesses']);live={p['output']}
 for n,o,a,b in p['source']:
  need(n not in known and o in ('+','-','*'),'Gate definition')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Topological closure');known.add(n)
 for n,o,a,b in reversed(p['source']):
  need(n in live,'Dead emitted gate');live.update(v for v in (a,b) if type(v)is str)
 z=sum(p['program'][i%len(p['program'])]==0 for i in range(p['horizon']));t=p['horizon']
 M=(4*t+3-z if p['mode']=='scaled' else 5*t+3-z)+t*p['square_boolean'];A=6*t+4
 need(p['ledger']==dict(operations=M+A,M=M,A=A,positive_witnesses=t+1,residuals=t+2,exact_degree=2*t+2),'Full paid ledger')
 return z

def verify():
 counts=Counter();rng=random.Random(1061107);packets=[]
 programs=((0,),(1,),(0,1,1),(2,0,1))
 for program,t,mode,squared in itertools.product(programs,range(1,7),('direct','scaled'),(False,True)):
  p=build(program,t,mode=mode,square_boolean=squared);source_audit(p);counts['complete_ledgers_and_live_DAGs']+=1
  if t<=4:
   got=polynomial_source(p);want,rr=independent_polynomial(program,t,squared)
   need(got[p['output']]==want and all(got[r]==v for r,v in zip(p['residuals'],rr)),'Complete formal polynomial/residual identity')
   need(max(map(len,want))==2*t+2,'Exact formal degree');counts['full_formal_polynomial_identities']+=1;counts['formal_residual_identities']+=t+2
  for j in range(8):
   values={n:rng.randrange(-3,5) for n in p['inputs']+p['witnesses']};heads=[values[f'D{i}']-1 for i in range(t)]
   S,C,B,_=direct_values(program,heads);P0=3*values['x']+values['Z0'];r0=P0*S-(1<<t);r1=values['Z0']+P0*C+3*B-(1<<t)
   bs=[d*(d-1) for d in heads];want=r0*r0+r1*r1+sum(b*b if squared else b for b in bs)
   need(evaluate(p,values,signed=True)==want,'Complete signed output')
   counts['complete_signed_outputs']+=1
  if program==(0,1,1) and t in (1,3,6):packets.append(p)
 # Complete census of all Boolean head words in the declared finite cases.
 # The two rows uniquely determine P0, Z0 and x from the head word.
 zeros=[]
 for program,t in itertools.product(programs,range(1,10)):
  p=build(program,t)
  for heads in itertools.product((0,1),repeat=t):
   counts['enumerated_Boolean_head_words']+=1
   S,C,B,_=direct_values(program,heads)
   if (1<<t)%S:continue
   P0=(1<<t)//S;Z0=(1<<t)-P0*C-3*B
   if Z0<=0 or (P0-Z0)%3:continue
   x=(P0-Z0)//3
   if x<=0:continue
   v={'x':x,'Z0':Z0,**{f'D{i}':d+1 for i,d in enumerate(heads)}}
   need(evaluate(p,v)==0,'Census positive zero')
   result=decode_zero(p,v);zeros.append(dict(program=list(program),values=v,**result));counts['positive_zeros_soundly_decoded']+=1;counts['posthalt_zeros']+=result['has_posthalt_extension']
 # Converse on actual ordinary padded-input halting runs, with diverse widths.
 halts=[]
 for program,x,pad in itertools.product(programs,range(1,17),range(3)):
  ell=(3*x).bit_length()+pad;P0=1<<ell;Z0=P0-3*x
  w=''.join(str((x>>i)&1) for i in range(ell));halt,heads=first_halt(program,w,40)
  if halt is None:continue
  p=build(program,halt);v={'x':x,'Z0':Z0,**{f'D{i}':d+1 for i,d in enumerate(heads)}}
  need(evaluate(p,v)==0,'Actual halt converse');halts.append(dict(program=list(program),x=x,Z0=Z0,halt=halt));counts['actual_halt_converses']+=1
 # Non-Boolean arbitrary positive tuples cannot cancel a nonnegative factor.
 for program,t in itertools.product(programs[:3],range(1,5)):
  p=build(program,t)
  for x,z,heads in itertools.product(range(1,4),range(1,5),itertools.product((0,1,2),repeat=t)):
   v={'x':x,'Z0':z,**{f'D{i}':d+1 for i,d in enumerate(heads)}};S,C,B,_=direct_values(program,heads);P0=3*x+z
   rows=(P0*S==(1<<t) and z+P0*C+3*B==(1<<t) and all(d in (0,1) for d in heads))
   need((evaluate(p,v)==0)==rows,'Nonnegative integer conjunction');counts['positive_adversarial_tuples']+=1
 # Exact off-zero relation to the all-squared reference.
 for t in range(1,7):
  a=build((0,1,1),t);b=build((0,1,1),t,square_boolean=True)
  for j in range(8):
   v={n:rng.randrange(-4,5) for n in a['inputs']+a['witnesses']};es=execute(a['source'],v);bs=[es[n] for n in a['boolean_residuals']]
   need(evaluate(b,v,signed=True)-evaluate(a,v,signed=True)==sum(z*z-z for z in bs),'Boolean off-zero correction');counts['Boolean_square_corrections']+=1
 post=build((0,1,1),6);postv={'x':1,'Z0':1,**{f'D{i}':int(c)+1 for i,c in enumerate('100010')}}
 postproof=decode_zero(post,postv);need(postproof['actual_first_halt']==3 and postproof['formal_widths'][4]=='1/2','Posthalt counterexample')
 real=build((0,1,1),3);realv={'x':1,'Z0':1,'D0':2,'D1':1+Fraction(1,3333),'D2':1}
 realenv=execute(real['source'],realv);need(realenv[real['output']]==0,'Real-domain false zero')
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
  raise ValueError('Malformed accepted')
 for bad in ((),[0,1],(True,),(1.0,),(-1,),None):reject(lambda bad=bad:build(bad,3))
 for bad in (True,0,-1,1.0,None):reject(lambda bad=bad:build((0,1),bad))
 for bad in (True,1,None,'other'):reject(lambda bad=bad:build((0,),3,mode=bad))
 for bad in (0,1,1.0,None):reject(lambda bad=bad:build((0,),3,square_boolean=bad))
 p=build((0,1,1),3);v={'x':1,'Z0':1,'D0':2,'D1':1,'D2':1}
 for n in v:
  for bad in (True,1.0,0,-1,None):
   q=dict(v);q[n]=bad;reject(lambda q=q:evaluate(p,q))
 reject(lambda:evaluate(real,realv))
 for field in ('source','ledger','registers','residuals','witnesses','scope'):
  q=dict(p);q[field]=None;reject(lambda q=q:checked(q))
 for bad in (True,1.0):
  q=build((0,1,1),3);row=list(q['source'][0]);j=next(j for j in (2,3) if type(row[j])is int);row[j]=bad;q['source'][0]=tuple(row);reject(lambda q=q:checked(q))
 q=build((0,1,1),3);q['source'].clear();need(bool(build((0,1,1),3)['source']),'Fresh packet independence');counts['fresh_packet_copy_checks']+=1
 return normalized(dict(status='PASS_FINITE_GRILL_WORD_CLOSURE',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),counts=dict(counts),packets=packets,
  positive_zero_census=zeros,actual_halt_examples=halts,posthalt_fixture=dict(values=postv,proof=postproof),
  positive_real_false_zero=dict(program=[0,1,1],horizon=3,values={k:str(z) for k,z in realv.items()},identity='At x=Z0=1 and d=(1,delta,0), F=delta*(3333*delta-1); delta=1/3333 is a non-Boolean positive-real zero.'),
  scope='Fixed natural program, external positive horizon, t+1 strictly positive witnesses. Complete word closure implies actual first halt at some tau<=t; actual halt exactly at t gives a zero. Only the union over horizons is an exact padded-input halting relation. Direct/scaled circuits are the identical entire polynomial; no same-zero-set assertion with causal first-halt histories.'))
def normalized(x):return json.loads(json.dumps(x))
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify()
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
