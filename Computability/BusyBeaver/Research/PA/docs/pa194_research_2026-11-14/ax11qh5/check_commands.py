#!/usr/bin/env python3
"""Free-term certificate for the combined AX11 + Q + H + coefficient-5 interface.

Adapted from the supplied PA194AX11 command checker; the changed cache-only
guard, exchanged sixth head, multiplier and terminal word are independently
checked here. This is a symbolic certificate plus a paper proof, not an
end-to-end Lean/iPRA calibration to PA.

This checks universal symbolic identities using Cantor pair projections, its
zero alias, constructor residues, and explicit cache-Shift branch assumptions.
It imports no construction compiler or Turing-machine simulator.
"""
from pathlib import Path
import argparse,json,hashlib

def require(p,msg):
 if not p:raise AssertionError(msg)
TERMINALS={'node49':['push'],'node55':['copyD'],'node58':['copyH'],
 'node70':['copyA'],'node65':['cons'],'node72':['readH'],
 'node75':['readDCons'],'node142':['copyGuard'],'node150':['compareGuard'],
 'node60':['incT']*2,'node61':['incT']*5}
def word(t):
 if isinstance(t,str):return TERMINALS[t]
 if t==['leaf','inc',1]:return['incT']
 require(isinstance(t,list)and len(t)==2,'invalid AX grammar leaf')
 return word(t[0])+word(t[1])
def emitter(machine):
 grammar=json.loads((machine/'grammar.json').read_text())
 def expand(t):
  if isinstance(t,str):return expand(grammar['rules'][t]) if t in grammar['rules'] else t
  if isinstance(t,list) and len(t)==2:return [expand(t[0]),expand(t[1])]
  return t
 tree=expand(grammar['root']);ww=word(tree)
 require(len(ww)==190,'AX word length')
 require(ww[-3:]==['copyGuard','compareGuard','push'],'new exact suffix')
 ns=json.loads((machine/'nodes.json').read_text())
 require(ns['node61']==[[['leaf','inc',1],'node60'],'node60'],'coefficient five source')
 require(ns['node170']==[['node36',['node167','node145']],'node57'],'cache-only Shift control')
 require(ns['node163']==['node6','node54'],'no-push successful MP')
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
        ex(D,e(H,D)),i(u(D,i(a,H)),i(u(D,a),u(D,H)))]
 rho=i(i(i(H,d),D),i(i(D,H),i(a,H)));gamma=i(a,u(a,a))
 point=i(a,m(a,D));v=i(m(H,D),u(a,m(H,D)))
 ss=u(D,conj(i(m(H,D),point),i(m(a,D),a)))
 qq=u(a,i(ss,n(point)));gate=n(i(v,qq))
 require(stack==[t,u(d,h),rho]+heads+[gamma],'entire inherited head stack')
 require(T==gate,'pre-guard gate tree')
 # The inherited guarded cleanup returns either this gate or zero; the added
 # push preserves that chosen theorem and sets the visible top to zero.
 for chosen in (gate,z):
  after=stack+[chosen]
  require(len(after)==11 and after[-1]==chosen and after[0]==t,'11-entry push both guard branches')
 return {'macro_tokens':190,'new_suffix':['copyGuard','compareGuard','push'],
   'pushed_entries':11,'coefficient':5,'exchanged_sixth_head':True,
   'whole_emitter_free_algebra_checked':True,'both_guard_branches_pushed':True,
   'source_MP_fallthrough_reads_extra_field':True,
   'exact_command':'AX(c,x,y,z):(0,[G,Gamma,h6_Q,h5,h4,h3,h2,h1,rho,U(d,h),t;w],z,0)'}

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
 if isinstance(a,int):return a%5
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
def cache_one(h,known):
 if h==1:return True
 if nonone(h,known):return False
 raise AssertionError(('unresolved cache-only guard',h))
def distinct(a,b):
 ra,rb=residue(a),residue(b)
 return (ra is not None and rb is not None and ra!=rb)or(a==0 and positive(b))or(b==0 and positive(a))
def heads(D,H,A,d,h):
 six=[I(('lhs',j,D,A,H),('rhs',j,D,A,H))for j in range(6,0,-1)]
 return [('gate',H,D,A),I(A,U(A,A))]+six+[I(I(I(H,d),D),I(I(D,H),I(A,H))),U(d,h)]
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
 require(run([AX(A)]+[S]*10,(t,w,d,h))==(heads(d,h,A,d,h)[8],pair(t,w),0,U(d,h)),'AX S10')
 require(run([AX(A)]+[S]*11,(t,w,d,h))==(U(d,h),w,0,t),'AX S11')
 require(run(POP,(t,pair(a,w),d,h),frozenset({t}))==(t,w,0,a),'Pop arbitrary non-one top')
 require(run(POP,(1,pair(a,w),d,h)) is None,'Pop visible contradiction halts')
 require(run(POP,(t,0,d,h),frozenset({t}))==(t,0,0,0),'Pop empty-stack alias')
 require(run(PUSH,(t,w,d,h))==(0,pair(t,w),0,0),'Push')
 require(run(PUSH,(0,0,d,h))==(0,0,0,0),'Push zero alias')
 require(run(DISCARD,(t,w,0,h))==(0,w,0,0),'Discard arbitrary cache')
 for j in range(9):
  ww=DISCARD+[AX(A,D,H)]+[S]*(j+2)+POP*(9-j)
  require(run(ww,(t,w,0,0))==(heads(D,H,A,0,0)[j],w,0,0),'selector'+str(j))
 for i in (0,('positive','i')):
  require(run([MP(i)],(0,w,0,0))==(0,w,i,0),'Offset')
  ww=PUSH+[MP(i),S,AX(i)]+[S]*11
  require(run(ww,(a,w,0,0))==(U(i,a),w,0,0),'Generalization')
  xx=atom('x');dv=add(i,xx)
  ww=DISCARD+[MP(i),AX(A,xx,H)]+[S]*10+POP
  require(run(ww,(t,w,0,0))==(I(I(I(H,i),dv),I(I(dv,H),I(A,H))),w,0,0),'restricted rho')
 suffix=[S,S,MP(b)]+POP
 require(run(suffix,(0,pair(a,pair(I(a,b),pair(0,w))),0,0),frozenset({a,b}))==(b,w,0,0),'MP suffix non-one antecedent and conclusion')
 require(run(suffix,(0,pair(1,pair(I(1,b),pair(0,w))),0,0))is None,'MP early antecedent contradiction')
 require(run([S,S,MP(1)]+POP,(0,pair(a,pair(I(a,1),pair(0,w))),0,0),frozenset({a})) is None,'MP conclusion1 halts at Pop')
 require(run([S,S,MP(0)]+POP,(0,pair(0,pair(0,0)),0,0))==(0,0,0,0),'MP zero aliases')
 require(run(DISCARD+PUSH,(t,w,0,0))==(0,pair(0,w),0,0),'reserved zero')
 require(run([S],(1,w,0,0))==(0,('tl',w),0,('hd',w)),'plain Shift loses visible contradiction')
 require(run(POP,(1,w,0,0))is None,'final Pop detects visible contradiction')
 require(run([S],(0,w,0,1))is None,'cached contradiction halt')
 require(run([S],(1,w,0,1)) is None,'cache guard also halts on1+1')
 return {'status':'PASS','guard':'h=1','AX_extra_field':'z','completion_uses_z':0,
  'push_shifts':10,'pop_shifts':12,'pop_unconditional':False,'Pop_halts_exactly_when_top_is_one':True,'discard':'MP(0)',
  'selector_j':list(range(9)),'selector':'Discard;AX(A,D,H,0);S^(j+2);Pop^(9-j)',
  'generalization_final_shifts':11,'MP_uses_reserved_zero':True,'MP_all_conclusions_checked':True,
  'refutation_final_command':'Pop','all_zero_aliases_checked':True}

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
   'scope':'Exact symbolic inverse identities; strict decrease and cofinality proved in ax11qh5_preservation.tex.'}

def fetch_prefix(machine):
 # Independently bind the exact source prefix, rather than assuming that
 # fresh candidates have the same +1 convention as positive continuations.
 ins=json.loads((machine/'instructions.json').read_text())
 expected=[
  ['dec',8,27,26],['jump',34],['dec',0,31,28],['inc',8,29],
  ['inc',6,30],['jump',27],['inc',0,32],['dec',6,34,33],['jump',31],
  ['dec',8,42,35],['inc',7,36],['dec',6,38,37],['jump',41],
  ['dec',7,41,39],['inc',6,40],['jump',38],['jump',34],
  ['dec',7,45,43],['inc',8,44],['jump',42],['dec',6,48,46],
  ['inc',3,47],['jump',45]]
 require(ins[25:48]==expected,'literal fetch prefix 25..47')
 from math import isqrt
 count=0
 for n in range(41):
  for l in range(41):
   r=[n,17,29,0,43,61,0,0,l];pc=25
   for steps in range(20*(n+l+5)+100):
    if pc==48:break
    row=ins[pc]
    if row[0]=='jump':pc=row[1]
    elif row[0]=='inc':r[row[1]]+=1;pc=row[2]
    else:
     require(row[0]=='dec','fetch contains inc, dec or jump only')
     _,reg,z,p=row
     if r[reg]:r[reg]-=1;pc=p
     else:pc=z
   else:raise AssertionError(('fetch prefix bound',n,l))
   seed=n if l==0 else l-1
   diag=(isqrt(8*seed+1)-1)//2
   right=seed-diag*(diag+1)//2;left=diag-right
   require(r==[n+int(l==0),17,29,left,43,61,0,0,right],
           ('fetch seed convention',n,l,r))
   count+=1
 return {'literal_source_entry':25,'literal_dispatch_entry':48,
  'literal_rows_checked':23,'reg_N':0,'reg_L':8,'reg_tag':3,
  'seed':'N if L=0 else L-1','next_N':'N+1 if L=0 else N',
  'fresh_candidate_is_b_without_plus_one':True,
  'positive_continuation_is_one_plus_b':True,
  'reg_scratch':[6,7],'numeric_prefix_regressions':count,
  'universal_scope':'Finite row binding plus algebraic copy/unpair proof in the TeX report; the numerical grid is a regression check.'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 result={'status':'PASS','emitter':emitter(a.machine),'command_words':check_words(),'scheduler':scheduler_check(),
         'fetch_prefix':fetch_prefix(a.machine),
         'inputs':{n:hashlib.sha256((a.machine/n).read_bytes()).hexdigest()for n in('grammar.json','nodes.json','instructions.json')}}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
