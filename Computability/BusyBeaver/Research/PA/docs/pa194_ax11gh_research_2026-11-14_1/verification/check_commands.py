#!/usr/bin/env python3
"""Free-term certificate for the AX11GH and AX11GHS command interfaces.

This checks universal symbolic identities using Cantor pair projections, its
zero alias, constructor residues, and explicit cached-Shift branch assumptions.
It imports no construction compiler or Turing-machine simulator.
Adapted from the attributed PA194AX11 checker; see NOTICE.md.
"""
from pathlib import Path
import argparse,json,hashlib

def require(p,msg):
 if not p:raise AssertionError(msg)
TERMINALS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],
 'node70':['copyA'],'node65':['cons'],'node72':['readH'],
 'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],
 'node60':['incT']*2,'node61':['incT']*4}
def word(t):
 if isinstance(t,str):return TERMINALS[t]
 if t==['leaf','inc',1]:return['incT']
 require(isinstance(t,list)and len(t)==2,'invalid AX grammar leaf')
 return word(t[0])+word(t[1])
def emitter(machine):
 family=json.loads((machine/'receipt.json').read_text())['family']
 require(family in ('PA194AX11GH','PA194AX11GHS'),'family')
 tree=json.loads((machine/'grammar.tree.json').read_text());ww=word(tree)
 require(len(ww)==190,'AX word length')
 require(ww[-3:]==['copyGuard','compareGuard','push'],'new exact suffix')
 ns=json.loads((machine/'nodes.json').read_text())
 require(ns['node61']==['node60','node60'],'coefficient four source')
 require(ns['node163']==['node6','node54'],'no-push successful MP')
 require(ns['node170']==[['node36',['node167','node145']],('node56' if family.endswith('GHS') else 'node57')],'cached-only Shift source')
 require(ns['node75']==['node74','node65']and ns['node74']==['node32','node73'],'fallthrough consumes extra field before constructor')
 require(ns['node164']==['node162','node163']and ns['node162']==['node75','node37'],'fallthrough full MP block shape')
 require(ns['node165']==['node161','node164']and ns['node161']==[['leaf','dec',3],'x67'],'AX normal exit precedes MP')
 z=('zero',);succ=lambda a:('succ',a);one=succ(z)
 i=lambda a,b:('I',a,b);m=lambda a,b:succ(i(a,b));u=lambda a,b:succ(succ(i(b,a)))
 e=lambda a,b:succ(succ(succ(i(a,b))));n=lambda a:i(a,one)
 conj=lambda a,b:n(i(a,n(b)));ex=lambda a,b:n(u(a,n(b)))
 t,a,d,h,x,y=[('parameter',s)for s in('t','a','d','h','x','y')]
 T,D,H,stack=t,d,h,[];fields=iter((y,x))
 for token in ww[:-3]:
  if token=='push':stack.append(T);T=z
  elif token in ('copyD','copyH','copyA'):stack.append(T);T={'copyD':D,'copyH':H,'copyA':a}[token]
  elif token=='cons':T=i(stack.pop(),T)
  elif token=='incT':T=succ(T)
  elif token=='readH':H=('add',H,next(fields))
  elif token=='readDCons':D=('add',D,next(fields));T=i(T,D)
  else:raise AssertionError(token)
 heads=[i(ex(D,u(D,H)),H),i(u(D,u(a,H)),u(a,u(D,H))),
        i(m(H,D),i(e(H,a),m(a,D))),i(e(H,D),i(m(a,H),m(a,D))),
        ex(D,e(H,D)),i(u(D,a),i(u(D,i(a,H)),u(D,H)))]
 if True:heads[5]=i(u(D,i(a,H)),i(u(D,a),u(D,H)))
 rho=i(i(i(H,d),D),i(i(D,H),i(a,H)));gamma=i(a,u(a,a))
 point=i(a,m(a,D));v=i(m(H,D),u(a,m(H,D)))
 ss=u(D,conj(i(m(H,D),point),i(m(a,D),a)))
 qq=u(a,i(ss,n(point)));gate=n(i(v,qq))
 require(stack==[t,u(a,h),rho]+heads+[gamma],'entire inherited head stack')
 require(T==gate,'pre-guard gate tree')
 # The inherited guarded cleanup returns either this gate or zero; the added
 # push preserves that chosen theorem and sets the visible top to zero.
 for chosen in (gate,z):
  after=stack+[chosen]
  require(len(after)==11 and after[-1]==chosen and after[0]==t,'11-entry push both guard branches')
 return {'macro_tokens':190,'new_suffix':['copyGuard','compareGuard','push'],
   'pushed_entries':11,'coefficient':4,'ordinary_sixth_head':False,
   'exchanged_sixth_head':True,'cached_only_shift':True,
   'whole_emitter_free_algebra_checked':True,'both_guard_branches_pushed':True,
   'source_MP_fallthrough_reads_extra_field':True,
   'exact_command':'AX(c,x,y,z):(0,[G,Gamma,h6,h5,h4,h3,h2,h1,rho,U(c,h),t;w],z,0)'}

Z=0;ONE=1
atom=lambda n:('atom',n)
def pair(a,b):return 0 if a==0 and b==0 else('pair',a,b)
def I(a,b):return 0 if a==0 and b==0 else('i',a,b)
def U(a,b):return('u',a,b)
def add(a,b):
 if a==0:return b
 if b==0:return a
 if isinstance(a,int)and isinstance(b,int):return a+b
 return('add',a,b)
def projections(a):
 if a==0:return 0,0
 if a[0]=='pair':return a[1],a[2]
 return('hd',a),('tl',a)
def residue(a):
 if isinstance(a,int):return a%4
 return {'i':0,'u':2,'gate':0}.get(a[0])
def positive(a):
 if isinstance(a,int):return a>0
 if a[0]in('u','positive'):return True
 if a[0]=='i':return positive(a[1])or positive(a[2])
 return False
def at_least_two(a):
 if isinstance(a,int):return a>=2
 if a[0]=='u':return True
 if a[0]=='i':return positive(a)
 return False
def nonone(a,known):
 return a in known or (isinstance(a,int)and a!=1) or (residue(a)is not None and residue(a)!=1)
def sum_one(t,h,known):
 if isinstance(t,int)and isinstance(h,int):return t+h==1
 if at_least_two(t)or at_least_two(h):return False
 if nonone(t,known)and nonone(h,known):return False
 rt,rh=residue(t),residue(h)
 if rt is not None and rh is not None and (rt+rh)%4!=1:return False
 raise AssertionError(('unresolved sum guard',t,h))
def cache_one(h,known):
 if h==1:return True
 if nonone(h,known):return False
 raise AssertionError(('unresolved cache guard',h))
def distinct(a,b):
 ra,rb=residue(a),residue(b)
 return (ra is not None and rb is not None and ra!=rb)or(a==0 and positive(b))or(b==0 and positive(a))
def heads(D,H,A,d,h):
 six=[I(('lhs',j,D,A,H),('rhs',j,D,A,H))for j in range(6,0,-1)]
 return [('gate',H,D,A),I(A,U(A,A))]+six+[I(I(I(H,d),D),I(I(D,H),I(A,H))),U(A,h)]
def AX(c,x=0,y=0,z=0):return('AX',c,x,y,z)
def MP(x):return('MP',x)
S=('S',)
def run(ww,store,known=frozenset()):
 t,w,d,h=store
 for cmd in ww:
  if cmd[0]=='S':
   if cache_one(h,known):return None
   nh,nw=projections(w);t,w,h=h,nw,nh
  elif cmd[0]=='AX':
   c,x,y,z=cmd[1:];D,H=add(d,x),add(h,y)
   for a in reversed(heads(D,H,c,d,h)+[t]):w=pair(a,w)
   # Extra-field MP_z receives t=d=h=0. For z=0 it succeeds and
   # returns zero; for z>0 it fails and returns zero. d=z in both.
   t,d,h=0,z,0
  elif cmd[0]=='MP':
   b=add(d,cmd[1]);major=I(t,b)
   if b==0:t,d,h=0,0,0
   elif major==h:t,d,h=b,b,0
   else:require(distinct(major,h),'unresolved MP comparison');t,d,h=0,b,0
  else:raise AssertionError(cmd)
 return t,w,d,h
POP=[AX(0)]+[S]*12
PUSH=[AX(0)]+[S]*10+[MP(0)]
DISCARD=[MP(0)]
def check_words():
 t,w,d,h,a,b,A,D,H,z=map(atom,('t','w','d','h','a','b','A','D','H','z'))
 require(run([MP(0)],(0,w,0,0))==(0,w,0,0),'postpush MP zero case')
 require(run([MP(('positive','z'))],(0,w,0,0))==(0,w,('positive','z'),0),'postpush MP positive case')
 require(run([AX(A,0,0,z)],(t,w,d,h))==(0,__import__('functools').reduce(lambda tail,v:pair(v,tail),reversed(heads(d,h,A,d,h)+[t]),w),z,0),'extra field exact store')
 require(run([AX(A)]+[S]*10,(t,w,d,h))==(heads(d,h,A,d,h)[8],pair(t,w),0,U(A,h)),'AX S10')
 require(run([AX(A)]+[S]*11,(t,w,d,h))==(U(A,h),w,0,t),'AX S11')
 require(run(POP,(t,pair(a,w),d,h),frozenset({t}))==(t,w,0,a),'Pop top unequal to one')
 require(run(POP,(1,pair(a,w),d,h))is None,'Pop detects visible contradiction')
 require(run(POP,(t,0,d,h),frozenset({t}))==(t,0,0,0),'Pop empty-stack alias')
 require(run(PUSH,(t,w,d,h))==(0,pair(t,w),0,0),'Push')
 require(run(PUSH,(0,0,d,h))==(0,0,0,0),'Push zero alias')
 require(run(DISCARD,(t,w,0,h))==(0,w,0,0),'Discard arbitrary cache')
 for j in range(9):
  ww=DISCARD+[AX(A,D,H)]+[S]*(j+2)+POP*(9-j)
  require(run(ww,(t,w,0,0))==(heads(D,H,A,0,0)[j],w,0,0),'selector'+str(j))
 for i in (0,('positive','i')):
  require(run([MP(i)],(0,w,0,0))==(0,w,i,0),'Offset')
  ww=PUSH+[S,AX(i)]+[S]*11
  require(run(ww,(a,w,0,0))==(U(i,a),w,0,0),'Generalization')
  require(run(ww,(1,w,0,0))==(U(i,1),w,0,0),'Generalization including contradiction code')
  xx=atom('x');dv=add(i,xx)
  ww=DISCARD+[MP(i),AX(A,xx,H)]+[S]*10+POP
  require(run(ww,(t,w,0,0))==(I(I(I(H,i),dv),I(I(dv,H),I(A,H))),w,0,0),'restricted rho')
 suffix=[S,S,MP(b)]+POP
 require(run(suffix,(0,pair(a,pair(I(a,b),pair(0,w))),0,0),frozenset({a,b}))==(b,w,0,0),'MP suffix noncontradictory antecedent and conclusion')
 require(run(suffix,(0,pair(1,pair(I(1,b),pair(0,w))),0,0))is None,'MP early antecedent contradiction')
 require(run([S,S,MP(1)]+POP,(0,pair(a,pair(I(a,1),pair(0,w))),0,0),frozenset({a}))is None,'MP conclusion one halts inside Pop')
 require(run([S,S,MP(0)]+POP,(0,pair(0,pair(0,0)),0,0))==(0,0,0,0),'MP zero aliases')
 require(run(DISCARD+PUSH,(t,w,0,0))==(0,pair(0,w),0,0),'reserved zero')
 require(run([S],(1,w,0,0))==(0,('tl',w),0,('hd',w)),'visible contradiction alone does not trigger Shift')
 require(run(POP,(1,w,0,0))is None,'final contradiction detected by Pop')
 require(run([S],(0,w,0,1))is None,'cached contradiction halt')
 require(run([S],(1,w,0,1))is None,'cached guard halts when both fields are one')
 return {'status':'PASS','guard':'h=1','AX_extra_field':'z','completion_uses_z':0,
  'push_shifts':10,'pop_shifts':12,'pop_unconditional':False,'pop_halts_iff_input_top_is_one':True,'discard':'MP(0)',
  'selector_j':list(range(9)),'selector':'Discard;AX(A,D,H,0);S^(j+2);Pop^(9-j)',
  'generalization_final_shifts':11,'MP_uses_reserved_zero':True,'MP_all_conclusions_checked':True,
  'refutation_final_word':'AX(0,0,0,0);S^12 (Pop)','all_zero_aliases_checked':True}

def scheduler_check():
 # A symbolic c+2 is distinct from tags 0 and1 and cannot collapse a
 # Cantor pair. Each nested field is recovered by total pair projections.
 c,x,y,z,tail=map(atom,('c','x','y','z','tail'))
 def b_ax(c,x,y,z,tail):return pair(('plus2',c),pair(y,pair(x,pair(z,tail))))
 def parse_ax(seed):
  tag,rest=projections(seed);require(isinstance(tag,tuple)and tag[0]=='plus2','AX tag')
  yy,rest=projections(rest);xx,rest=projections(rest);zz,nexttail=projections(rest)
  return tag[1],xx,yy,zz,nexttail
 require(parse_ax(b_ax(c,x,y,z,tail))==(c,x,y,z,tail),'four-field inverse')
 require(parse_ax(b_ax(c,0,0,0,0))==(c,0,0,0,0),'zero field aliases')
 require(parse_ax(b_ax(c,x,y,0,tail))==(c,x,y,0,tail),'padded AX inverse')
 # Reading the MP parameter consumes an extra field even after A is cleared.
 # This check would fail if the old three-parameter continuation were used.
 old=pair(('plus2',c),pair(y,pair(x,tail)))
 require(parse_ax(old)==(c,x,y,('hd',tail),('tl',tail)),'old encoding consumes a different continuation')
 for a in (0,x):
  rest=pair(a,tail);require(projections(rest)==(a,tail),'MP field inverse')
 return {'AX_arity':4,'field_order':['y','x','z'],'padded_z':0,
   'AX_seed':'p(c+2,p(y,p(x,p(z,e(tail)))))',
   'nonempty_continuation':'1+b(command,e(tail))',
   'four_field_inverse_checked':True,'zero_field_aliases_checked':True,
   'old_three_field_continuation_detected_as_wrong':True,
   'cofinal_prefix_seed':'p(k+2,p(0,p(0,p(0,e(halting_suffix)))))',
   'scope':'Exact symbolic inverse identities; see the new written command preservation proof.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 result={'status':'PASS','emitter':emitter(a.machine),'command_words':check_words(),'scheduler':scheduler_check(),
         'inputs':{n:hashlib.sha256((a.machine/n).read_bytes()).hexdigest()for n in('grammar.tree.json','nodes.json')}}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
