#!/usr/bin/env python3
"""Independent free-algebra audit of curried-premise exchange emitters.

Only JSON and Python standard library. No compiler/runtime imports.
"""
from pathlib import Path
import argparse,itertools,json,hashlib
INC=['leaf','inc',1]
BREAK=['leaf','breakTo',1]

def read_word(path):
 d=json.loads(path.read_text())
 def flatten(x):
  if isinstance(x,str) and isinstance(d,dict) and x in d['rules']:
   a,b=d['rules'][x];return flatten(a)+flatten(b)
  if x=='node60':return [INC,INC]
  if x=='node61':return [INC]*4
  if isinstance(x,list)and len(x)==2:return flatten(x[0])+flatten(x[1])
  return [x]
 return flatten(d['root']) if isinstance(d,dict)else sum((flatten(t)for t in d),[])

def audit(word,mask,tag_swap=False):
 Z=('zero',);O=('succ',Z)
 def succ(t):return('succ',t)
 def I(a,b):return('I',a,b)
 def M(a,b):return succ(I(a,b))
 def U(a,B):return succ(succ(succ(I(B,a)))) if tag_swap else succ(succ(I(B,a)))
 def E(a,b):return succ(succ(I(a,b))) if tag_swap else succ(succ(succ(I(a,b))))
 def N(a):return I(a,O)
 def And(a,b):return N(I(a,N(b)))
 def Ex(a,b):return N(U(a,N(b)))
 names={'node49':'push','node55':'copyD','node58':'copyH','node70':'copyA',
  'node65':'cons','node72':'readH','node75':'readDCons',
  'node142':'copyGuard','node150':'compareGuard'}
 ops=['incT'if x==INC else 'close'if x==BREAK else names[x]for x in word]
 oldt,A,d,h,Y,X=(('atom',a)for a in('t','a','d','h','y','x'))
 T,D,H=oldt,d,h;stack=[];fields=[Y,X]
 assert ops[-3:]==['copyGuard','compareGuard','close']
 for op in ops[:-3]:
  if op=='push':stack.append(T);T=Z
  elif op in('copyD','copyH','copyA'):stack.append(T);T={'copyD':D,'copyH':H,'copyA':A}[op]
  elif op=='cons':T=I(stack.pop(),T)
  elif op=='incT':T=succ(T)
  elif op=='readH':H=('add',H,fields.pop(0))
  elif op=='readDCons':D=('add',D,fields.pop(0));T=I(T,D)
  else:raise AssertionError(op)
 assert not fields and len(stack)==10
 def heads(d,a,h):
  m1,e1,c1=M(h,d),E(h,a),M(a,d)
  e2,m2,c2=E(h,d),M(a,h),M(a,d)
  u1,u2,c3=U(d,a),U(d,I(a,h)),U(d,h)
  if mask&1:m1,e1=e1,m1
  if mask&2:e2,m2=m2,e2
  if mask&4:u1,u2=u2,u1
  return[I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
   I(m1,I(e1,c1)),I(e2,I(m2,c2)),Ex(d,E(h,d)),I(u1,I(u2,c3))]
 rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
 gamma=I(A,U(A,A));v=I(M(H,D),U(A,M(H,D)))
 point=I(A,M(A,D));S=U(D,And(I(M(H,D),point),I(M(A,D),A)))
 Q=U(A,I(S,N(point)))
 assert stack[:3]==[oldt,U(d,h),rho]
 gamma_parameters=[name for name,value in [('A',A),('D',D),('H',H)] if stack[-1]==I(value,U(value,value))]
 assert len(gamma_parameters)==1 and T==N(I(v,Q))
 vals={'D':D,'A':A,'H':H};matches=[]
 for i,actual in enumerate(stack[3:9]):
  choices=[]
  for perm in itertools.permutations(['D','A','H']):
   if heads(*(vals[x]for x in perm))[i]==actual:choices.append(dict(zip(['D','A','H'],perm)))
  assert choices,('head doesnot match any parameter-permuted instance',i+1)
  matches.append({'head':i+1,'parameter_maps':choices})
 return {'passed':True,'tag_swap':tag_swap,'exchange_mask':mask,'exchanged_heads':[h for b,h in enumerate([3,4,6])if mask>>b&1],
  'tokens':len(word),'diagonal_parameter':gamma_parameters[0],'pushed_entries_including_saved_top':10,'head_parameter_maps':matches,
  'fixed_heads_and_final_gate_exact':True,'trailing_guard_macros_exact':True,
  'scope':'Free-constructor algebra only; exact syntax of all generated formulas and stack ordering.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path);ap.add_argument('--mask',type=int,required=True);ap.add_argument('--tag-swap',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args()
 assert 0<=args.mask<8
 r=audit(read_word(args.input),args.mask,args.tag_swap);r['input_sha256']=hashlib.sha256(args.input.read_bytes()).hexdigest()
 if args.output:args.output.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
if __name__=='__main__':main()
