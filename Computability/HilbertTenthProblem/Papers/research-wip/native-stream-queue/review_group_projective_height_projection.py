#!/usr/bin/env python3
"""Independent complete-source and finite outer audit; no author code imports."""
import argparse, hashlib, json, random
from pathlib import Path
from fractions import Fraction
from collections import Counter
if not __debug__: raise RuntimeError('Run without -O')
PINS = {
'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5',
'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008',
'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb',
'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39',
'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
'group_range_projective_compiler.md': '2c71f229f791a12c63d701adcfe56dcfe44601e124566562fc67aeb8a2398f2f',
'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c',
'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952',
'group_projective_shifted_boundary.md': 'b5497bd97b09d8c4737229260c949676bdc511bf2da1985a9008918c156defe3',
'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e',
'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb',
}
AUTHOR_PINS = {
'.py':'a5c495aefb993e6b21ba4139bf7920c5365e224666a4d9c7aad71d47c7062f6f',
'.json':'15f23984754448c0c262b82ac259fb7d2df01d9f5d81cd4672015a3cf3e59b40',
'.md':'2ccd69682f00686caf7ba52088dd80f3f80b48b24c18d54d28dc8ff4af9fbfa0',
}
CODE = (3,2,3) + (1,)*13 + (7,6,7) + (5,)*13
P_NAME = 'controller__geometry_power'
def require(x, message):
 if not x: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def typed(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
# Independent sparse polynomial arithmetic for the complete outer cones.
def const(x): return {():x} if x else {}
def atom(x): return {((x,1),):1}
def add(a,b,sign=1):
 z=dict(a)
 for m,c in b.items():
  z[m]=z.get(m,0)+sign*c
  if not z[m]: del z[m]
 return z
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   mon=tuple(sorted(e.items()));z[mon]=z.get(mon,0)+c*d
 return {m:c for m,c in z.items() if c}
def power(a,n):
 z=const(1)
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
def total(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def scale(n,p): return mul(const(n),p)
def value(x,e): return e[x] if isinstance(x,str) else const(x)
def poly_cone(rows,free,target,cuts):
 defs={n:(o,a,b) for n,o,a,b in rows};env={n:atom(n) for n in free};env.update(cuts)
 def go(n):
  if type(n) is int:return const(n)
  if n not in env:
   op,a,b=defs[n];a,b=go(a),go(b);env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return env[n]
 return go(target)
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def account(p):
 free=p['free'];degree={n:1 for n in free};defs={};c=Counter()
 require(len(free)==len(set(free)),'unique input leaves')
 for n,o,a,b in p['source']:
  require(n not in degree and o in ('+','-','*'),'fresh legal gate')
  require(all(type(t) is int or type(t) is str and t in degree for t in (a,b)),'closed exact-type schedule')
  da,db=(degree.get(t,0) for t in (a,b));degree[n]=da+db if o=='*' else max(da,db)
  defs[n]=(a,b);c['M' if o=='*' else 'A']+=1
 seen=set();used=set();stack=[p['output']]
 while stack:
  n=stack.pop()
  if type(n) is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);stack.extend(defs[n])
 require(seen==set(defs) and used==set(free),'all gates and supplied leaves live')
 ans=dict(operations=len(defs),M=c['M'],A=c['A'],degree_upper=degree[p['output']])
 require(ans==p['ledger'],'literal full ledger')
 return ans
# Exact ring-expression DAG: addition is a sparse linear combination of
# nonlinear node IDs, sufficient for D=(D-u)+u without a proof cut.
class Ring:
 def __init__(self):self.memo={};self.next=1
 def leaf(self,key):
  if key not in self.memo:self.memo[key]=self.next;self.next+=1
  return ((self.memo[key],1),)
 def number(self,n):return ((0,n),) if n else ()
 def op(self,o,a,b):
  if o in ('+','-'):
   z=dict(a)
   for k,v in b:z[k]=z.get(k,0)+(v if o=='+' else -v)
   return tuple(sorted((k,v) for k,v in z.items() if v))
  if not a or not b:return ()
  if len(a)==1 and a[0][0]==0:return tuple((k,a[0][1]*v) for k,v in b)
  if len(b)==1 and b[0][0]==0:return tuple((k,b[0][1]*v) for k,v in a)
  return self.leaf(('*',tuple(sorted((a,b)))))
 def execute(self,p,env):
  e=dict(env)
  for n,o,a,b in p['source']:
   av=e[a] if isinstance(a,str) else self.number(a);bv=e[b] if isinstance(b,str) else self.number(b)
   e[n]=self.op(o,av,bv)
  return e

def source_checks(old,parent,child):
 require(parent['codes']==[list(CODE)] and parent['edges']==[[i,(i+1)%32,label] for i,label in enumerate(CODE)],'actual single macro cycle')
 require(parent['m']==32 and parent['alpha']==24 and parent['beta']==12,'fixed table and numerals')
 require(parent['source']!=old['source'],'new table is not saved default table')
 require(child['source']==[r for r in parent['source'] if r[0]!='D'],'only D producer removed')
 require(child['free']==['D' if n=='height_slack' else n for n in parent['free']],'one supplied-coordinate replacement')
 require([r for r in parent['source'] if 'height_slack' in r[2:]]==[['D','+','history__u','height_slack']],'all height-slack consumers')
 require(child['comparisons']==parent['comparisons'] and child['output']==parent['output']==old['polynomial_output'],'full finalizer/interface retained')
 require(parent['comparisons'][:5]==old['comparisons'][:5] and len(parent['comparisons'])==6,'six exact comparison interfaces')
 expected_free=old['parameters']+[x for x in old['auxiliaries'] if not x.startswith('controller__edge_hat')]+[f'controller__edge_hat{i+1}' for i in range(32)]
 require(parent['free']==expected_free,'all actual native/outer coordinates retained')
 # Every native arithmetic row is literally inherited, except the separately
 # proved tail quotient. New names may occur only in the reconstructed outer.
 dm={r[0]:r for r in parent['source']}
 native_start=next(i for i,r in enumerate(old['source']) if r[0]=='selection__bs_even')
 changed={'selection__q','controller__flow_right','range_body_scale','range_Bminus_shift','shifted_native_quotient','joint_edge_shift'}
 removed={'range_total_scale'}
 retained=0
 for row in old['source'][native_start:]:
  n=row[0]
  if n.startswith('controller__flow') or n in removed:continue
  if n in changed:continue
  require(n in dm and dm[n]==row,'unchanged native/outer suffix row '+n);retained+=1
 require(dm['shifted_native_quotient']==['shifted_native_quotient','+','selection__w','packed_z_product'],'actual tail quotient')
 # Check finalizer exactly, allowing only the two validated flow port names.
 expected=old['polynomial_finalizer'];actual=[dm[row[0]] for row in expected]
 flow_left,flow_right=parent['comparisons'][5]
 alias={'controller__flow_left':flow_left,'controller__flow_right':flow_right}
 require(actual==[[alias.get(x,x) if isinstance(x,str) else x for x in row] for row in expected],'literal entire unsquared finalizer')
 # Independent multivariate outer arithmetic, with P cut only after verifying
 # its defining repunit relation. D is the supplied child coordinate.
 pp=atom('P');dd=atom('D');bb=scale(16,dd);hh=[atom('H'+str(i)) for i in range(4)]
 zz=[add(atom('Zhat'+str(i)),const(1),-1) for i in range(8)]
 ee=[add(atom(f'controller__edge_hat{i+1}'),const(1),-1) for i in range(32)]
 jj=total(ee);ss=[total(e for e,label in zip(ee,CODE) if label==i+1) for i in range(8)]
 hb=total(mul(hh[(i//2)^1],power(pp,i)) for i in range(8))
 zb=total(mul(z,power(pp,i)) for i,z in enumerate(zz));sp=total(mul(s,power(pp,i)) for i,s in enumerate(ss))
 hc=total(mul(e,power(pp,i)) for i,e in enumerate(ee));mc=mul(jj,total(power(pp,i) for i in range(32)))
 rr=mul(add(scale(2,dd),const(1),-1),mc);tt=power(pp,40);t2=power(pp,72)
 H=add(add(hb,mul(power(pp,8),hc)),add(mul(tt,hb),mul(bb,t2)))
 M=add(add(mul(add(bb,const(1),-1),sp),mul(power(pp,8),mc)),add(mul(tt,rr),scale(2,t2)))
 Z=add(add(zb,mul(power(pp,8),hc)),mul(tt,hb));q=scale(32,mul(bb,t2))
 want={parent['cuts']['J']:jj,parent['cuts']['S']:sp,parent['cuts']['C']:hc,
       P_NAME:add(mul(add(bb,const(1),-1),jj),const(1)),
       flow_left:total(scale(i,e) for i,e in enumerate(ee)),
       flow_right:mul(bb,total(scale((i+1)%32,e) for i,e in enumerate(ee))),
       'controller__origin_mask':mc,'selection__Hbatch':hb,'selection__Zbatch':zb,
       'range_H':H,'range_M':M,'range_Z':Z,'selection__q':q,
       'selection__padded_A':add(scale(16,H),const(13)),
       'selection__padded_B':add(scale(16,M),const(10)),
       'selection__F3':add(scale(16,Z),const(8))}
 for i in range(4):
  want['history__delta'+str(i)]=add(add(zz[2*i],zz[2*i+1],-1),mul(add(dd,const(1),-1),add(ss[2*i],ss[2*i+1],-1)),-1)
 # Full literal endpoint polynomials include actual input x, not a free u cut.
 u=add(scale(24,atom('x')),const(13));c0=add(dd,const(1),-1)
 for i in range(4):
  want['history__left'+str(i)]=mul(bb,add(hh[i],want['history__delta'+str(i)]))
  want['history__right'+str(i)]=add(add(hh[i],mul(dd if i%2 else c0,pp)),add(c0,u) if i%2 else dd,-1)
 want['joint_bound_unit']=add(add(total(hh),total(atom('Zhat'+str(i)) for i in range(8))),add(atom('selection__bound_global'),pp,-1))
 for n,pol in want.items():
  cuts={} if n==P_NAME else {P_NAME:pp}
  require(poly_cone(child['source'],child['free'],n,cuts)==pol,'independent outer coefficient polynomial '+n)
 # The folded packing must be literally the usual four-field index at the
 # checked outer ports. This is an all-value coefficient identity.
 nq,nh,nm,nz=(atom(s) for s in ('q','H','M','Z'))
 F3=add(scale(16,nz),const(8));F1=add(scale(16,add(nh,nz,-1)),const(4));F2=add(scale(16,add(nm,nz,-1)),const(2))
 F0=add(add(add(nq,scale(16,nh),-1),scale(16,nm),-1),add(scale(16,nz),const(-15)))
 expected_r=total(mul(f,power(nq,i)) for i,f in enumerate((F0,F1,F2,F3)))
 got_r=poly_cone(child['source'],child['free'],'selection__bs_packed',dict(selection__q=nq,range_H=nh,range_M=nm,range_Z=nz))
 require(got_r==expected_r,'full factored native index coefficient identity')
 # Complete graph equality over any commutative ring, without residual cuts.
 ring=Ring();leaf={n:ring.leaf(('input',n)) for n in child['free']};ce=ring.execute(child,leaf)
 pe={n:leaf[n] for n in parent['free'] if n!='height_slack'}
 pe['height_slack']=ring.op('-',leaf['D'],ce['history__u']);pe=ring.execute(parent,pe)
 require(all(pe[n]==ce[n] for n,_,_,_ in child['source']),'all retained registers exact ring graph identity')
 return dict(literal_suffix_rows=retained,independent_outer_polynomials=len(want),native_index_polynomial=1,whole_graph_registers=len(child['source']),full_graph_identities=1)

def matmul(a,b):return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def matrix_checks():
 U=((1,1),(0,1));L=((1,0),(1,1));Um=((1,-1),(0,1));I=((1,0),(0,1));M=I
 for a in [L,Um,L]+[U]*13:M=matmul(a,M)
 require(M==((13,-1),(1,0)),'actual chronological macro matrix')
 require(matmul(M,M)==tuple(tuple(13*M[i][j]-I[i][j] for j in range(2)) for i in range(2)),'exact Cayley-Hamilton identity')
 inv=((0,1),(-1,13));v=(0,1);f0,f1=0,1
 for n in range(65):
  require(v==(f0,f1),'inverse power second column recurrence')
  require((v[0]==1)==(n==1),'bounded support for unique accepted power')
  v=(v[1],13*v[1]-v[0]);f0,f1=f1,13*f1-f0
 return dict(matrix=[list(r) for r in M],checked_inverse_powers=65,unbounded_uniqueness='Proved in companion by strict recurrence growth; finite powers are supplemental.')

def fixture(D,child):
 B=16*D;c=D-1;state=[1,13,1,13];trace=[tuple(state)];digits=[[] for _ in range(4)];selected=[[] for _ in range(8)];selectors=[[] for _ in range(8)]
 for label in CODE:
  slot=label-1
  for i in range(4):digits[i].append(c+state[i])
  for i in range(8):selectors[i].append(int(i==slot));selected[i].append(c+state[(i//2)^1] if i==slot else 0)
  state[slot//2]+=(1 if slot%2==0 else -1)*state[(slot//2)^1];trace.append(tuple(state))
 require(tuple(state)==(0,1,0,1),'true reference endpoint')
 encode=lambda xs:sum(a*B**i for i,a in enumerate(xs))
 H0=list(map(encode,digits));Z=list(map(encode,selected));S=list(map(encode,selectors));P=B**32;J=(P-1)//(B-1)
 require(min(v for ds in digits for v in ds)==D-14 and max(v for ds in digits for v in ds)==D+13,'exact genuine shifted range')
 original_beta=P+1-sum(H0)-sum(z+1 for z in Z)
 H=list(H0);H[1]-=24;H[3]-=24
 for i in (1,3):digits[i][0]-=24
 require(all(0<=a<2*D for ds in digits for a in ds),'all changed history digits in range')
 require(all(encode(ds)==h for ds,h in zip(digits,H)),'only initial digits altered')
 require(CODE[0]==3 and selectors[0][0]==selectors[1][0]==selectors[4][0]==selectors[5][0]==0,'altered initial odd sources are unselected')
 v={n:1 for n in child['free']};v.update(D=D,x=B-1,selection__bound_global=original_beta+48)
 for i,h in enumerate(H):v['H'+str(i)]=h
 for i,z in enumerate(Z):v['Zhat'+str(i)]=z+1
 for i in range(32):v['controller__edge_hat'+str(i+1)]=B**i+1
 require(min(v.values())>0,'positive actual supplied leaves')
 e=run(child['source'],v)
 for i,(a,b) in enumerate(child['comparisons']):
  if i!=4:require(e[a]==(e[b] if isinstance(b,str) else b),'actual outer residual '+str(i))
 require(e['joint_bound_unit']==1,'actual joint bound after +48')
 Hb=sum(H[(i//2)^1]*P**i for i in range(8));Mb=(B-1)*sum(s*P**i for i,s in enumerate(S));Zb=sum(z*P**i for i,z in enumerate(Z))
 Hc=sum(B**i*P**i for i in range(32));Mc=J*sum(P**i for i in range(32));T=P**40;T2=P**72
 h=Hb+P**8*Hc+T*Hb+B*T2;m=Mb+P**8*Mc+T*(2*D-1)*Mc+2*T2;z=Zb+P**8*Hc+T*Hb;Q=2*B*T2;q=16*Q
 require((e['range_H'],e['range_M'],e['range_Z'],e['selection__q'])==(h,m,z,q),'all actual full packed ports')
 require(h&m==z and 0<=min(h,m,z) and max(h,m,z)<Q,'full scalar AND and strict scale')
 fields=(16*(Q-h-m+z)-15,16*(h-z)+4,16*(m-z)+2,16*z+8)
 require(min(fields)>0 and sum(fields)==q-1,'strict positive native truth fields and checksum')
 require(all(not(a&b) for i,a in enumerate(fields) for b in fields[i+1:]),'actual four-field disjoint partition')
 r=sum(f*q**i for i,f in enumerate(fields));t=q.bit_length()-1
 require(q==1<<t and r.bit_count()==t and r%16==1,'exact native dyadic/population interface')
 require(e['selection__bs_packed']==r,'literal factored native index')
 # Do not construct X=2^(2r+1) or a Pell tuple. Only sufficient logarithmic
 # size inequalities are verified; the native component theorem supplies it.
 require(r>q and (2*r+1) > 3*t,'native exponent ensures X/q>q^2>Z0')
 require(e['history__u']==24*(B-1)+13 and D-e['history__u']<0,'wrong ordinary input and negative inverse')
 require(e[child['output']]!=0,'native placeholders are explicitly not full numerical zeros')
 digest=lambda n:sha(n.to_bytes(max(1,(n.bit_length()+7)//8),'big'))
 return dict(D=D,B=B,x=B-1,u=e['history__u'],restored_height_slack=D-e['history__u'],duration=32,
  shifted_range=[min(x for ds in digits for x in ds),max(x for ds in digits for x in ds)],first_odd=digits[1][0],
  outer_zero_rows=5,joint_bound_unit=1,q_bits=q.bit_length(),r_bits=r.bit_length(),population=t,
  packed_hashes=[digest(h),digest(m),digest(z)],native_placeholders_not_full_zero=True)

def verify(root,author):
 pins={}
 for n,h in PINS.items():
  require(sha((root/n).read_bytes())==h,'source/proof pin '+n);pins[n]=h
 for ext,h in AUTHOR_PINS.items():require(sha(author.with_suffix(ext).read_bytes())==h,'author pin '+ext)
 j=json.loads(author.with_suffix('.json').read_text());old=json.loads((root/'group_projective_label_aligned_lanes.json').read_text())['source']['source_example']
 require(j['pins']==PINS,'exact independently pinned dependency inventory')
 require(j['source_sha256']==AUTHOR_PINS['.py'],'author receipt source hash')
 parent,child=j['parent'],j['rejected_candidate'];lp,lc=account(parent),account(child)
 require((lp['operations'],lp['M'],lp['A'])==(464,192,272),'full parent cost')
 require((lc['operations'],lc['M'],lc['A'])==(463,192,271),'full rejected cost')
 source=source_checks(old,parent,child);matrix=matrix_checks();fixtures=[fixture(d,child) for d in (32,64,128)]
 # Independent whole signed and rational numerical regression, supplementing
 # the general complete ring identity above.
 rng=random.Random(93271);cases=0
 for rational in (False,True):
  for _ in range(6):
   v={n:Fraction(rng.randrange(-2,3),3) if rational else rng.randrange(-2,3) for n in child['free']}
   ce=run(child['source'],v);pv={n:v[n] for n in parent['free'] if n!='height_slack'};pv['height_slack']=v['D']-ce['history__u'];pe=run(parent['source'],pv)
   require(all(pe[n]==ce[n] for n,_,_,_ in child['source']),'whole finite pullback');cases+=1
 return dict(status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),pins=pins,author_pins=AUTHOR_PINS,
  ledgers=[lp,lc],witnesses=len(child['free'])-1,source=source,matrix=matrix,fixtures=fixtures,
  whole_evaluations=cases,rational_evaluations=6,scope='Independent complete literal source and graph audit plus outer arithmetic. The companion proves the full positive native extension without materializing it; no universal numerical bound.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author',type=Path,default=Path(__file__).with_name('group_projective_height_projection_obstruction'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.author)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 if a.expect:require(typed(r,json.loads(a.expect.read_text())),'exact typed review receipt')
 print(json.dumps(dict(status=r['status'],source=r['source'],ledgers=r['ledgers'],fixtures=len(r['fixtures']))))
if __name__=='__main__':main()
