#!/usr/bin/env python3
"""Complete fixed-table height-projection counterexample; saved sources only."""
import argparse,copy,hashlib,json,random
from pathlib import Path
from collections import Counter
from fractions import Fraction
if not __debug__:raise RuntimeError('Run without -O')
PINS={'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_shifted_boundary.md': 'b5497bd97b09d8c4737229260c949676bdc511bf2da1985a9008918c156defe3', 'group_range_projective_compiler.md': '2c71f229f791a12c63d701adcfe56dcfe44601e124566562fc67aeb8a2398f2f', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb'}
CODE=(3,2,3)+(1,)*13+(7,6,7)+(5,)*13
P='controller__geometry_power'
def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
class Emit:
 def __init__(self):self.rows=[];self.memo={}
 def op(self,o,a,b):
  if type(a)is int and type(b)is int:return a*b if o=='*'else a+b if o=='+'else a-b
  if o=='*'and(a==0 or b==0):return 0
  if o=='*'and a==1:return b
  if o=='*'and b==1:return a
  if o=='+'and a==0:return b
  if o in('+','-')and b==0:return a
  if o=='-'and a==b:return 0
  key=(o,tuple(sorted((a,b),key=repr))if o in('+','*')else(a,b))
  if key not in self.memo:
   n='height_probe__'+str(len(self.rows));self.memo[key]=n;self.rows.append([n,o,a,b])
  return self.memo[key]
 def total(self,xs):
  z=0
  for x in xs:z=self.op('+',z,x)
  return z
 def horner(self,cs):
  cs=list(cs)
  while len(cs)>1 and cs[-1]==0:cs.pop()
  z=cs[-1]
  for x in reversed(cs[:-1]):z=self.op('+',x,self.op('*',P,z))
  return z

def ledger(rows,free,output):
 defs={};degree={n:1 for n in free};c=Counter()
 for n,o,a,b in rows:
  need(n not in degree and o in('+','-','*'),'fresh typed row')
  need(all(type(v)is int or type(v)is str and v in degree for v in(a,b)),'closed source')
  ds=[degree[v]if type(v)is str else 0 for v in(a,b)];degree[n]=sum(ds)if o=='*'else max(ds);defs[n]=(a,b);c['M'if o=='*'else'A']+=1
 used=set();live=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:used.add(n)
  elif n not in live:live.add(n);todo.extend(defs[n])
 need(live==set(defs)and used==set(free),'every paid gate and coordinate live')
 return dict(operations=len(rows),M=c['M'],A=c['A'],degree_upper=degree[output])

def build(root):
 old=json.loads((root/'group_projective_label_aligned_lanes.json').read_text())['source']['source_example']
 need(old['m']==8 and old['alpha']==24 and old['beta']==12,'actual complete saved m8 template')
 n=len(CODE);need(n==32,'fixed code length');E=Emit();hats=[f'controller__edge_hat{i+1}'for i in range(n)]
 edges=[(i,i+1 if i+1<n else 0,l)for i,l in enumerate(CODE)]
 alias={'computed_J':E.op('-',E.total(hats),n)}
 for coord,key in[(0,'controller__flow_left'),(1,'controller__flow_right')]:
  z=E.op('-',E.total([E.op('*',e[coord],hat)for e,hat in zip(edges,hats)]),sum(e[coord]for e in edges))
  alias[key]=z if coord==0 else E.op('*','B',z)
 raw=[E.total([hat for hat,l in zip(hats,CODE)if l==label])for label in range(1,9)];counts=[CODE.count(label)for label in range(1,9)]
 for i in range(4):alias['history__dS'+str(i)]=E.op('-',E.op('-',raw[2*i],raw[2*i+1]),counts[2*i]-counts[2*i+1])
 S=E.op('-',E.horner(raw),E.horner(counts))
 p8='controller__lane_power3';p16=E.op('*',p8,p8);p32=E.op('*',p16,p16)
 r8='controller__lane_repunit2';r16=E.op('*',r8,E.op('+',p8,1));r32=E.op('*',r16,E.op('+',p16,1))
 alias['controller__edge_word']=E.op('-',E.horner(hats),r32)
 rows=[];removed=[];changed=[]
 for row in old['source']:
  n,o,a,b=row
  if n.startswith(('controller__flow','selection__Spack'))or n in alias or n=='range_total_scale':removed.append(n);continue
  r=list(row)
  if n=='selection__Mbatch':r[3]=S
  if n=='controller__origin_mask':r[3]=r32
  if n=='joint_scale':r[2:]=[p8,p32]
  if n=='range_body_scale':r[3]=p32
  if n=='range_Bminus_shift':r[3]=2
  if n=='selection__q':r[2:]=[32,'range_Bshift']
  if n=='shifted_native_quotient':r[3]='packed_z_product'
  if r!=row:changed.append([row,r])
  rows.append(r)
 rows+=E.rows+copy.deepcopy(old['polynomial_finalizer'])
 def sub(x):
  seen=set()
  while type(x)is str and x in alias:need(x not in seen,'acyclic alias');seen.add(x);x=alias[x]
  return x
 free=old['parameters']+[x for x in old['auxiliaries']if not x.startswith('controller__edge_hat')]+hats
 pending=rows;known=set(free);out=[]
 while pending:
  rest=[]
  for n,o,a,b in pending:
   a,b=sub(a),sub(b)
   if any(type(v)is str and v not in known for v in(a,b)):rest.append([n,o,a,b]);continue
   out.append([n,o,a,b]);known.add(n)
  need(len(rest)<len(pending),'acyclic schedule');pending=rest
 defs={r[0]:r for r in out};live=set();todo=[old['polynomial_output']]
 while todo:
  v=todo.pop()
  if v in defs and v not in live:live.add(v);todo+=defs[v][2:]
 out=[r for r in out if r[0]in live]
 parent=dict(source=out,free=free,output=old['polynomial_output'],comparisons=[[sub(a),sub(b)]for a,b in old['comparisons']],edges=[list(e)for e in edges],codes=[list(CODE)],m=32,alpha=24,beta=12,cuts=dict(J=sub('computed_J'),S=S,C=sub('controller__edge_word')),domain='all supplied coordinates strictly positive',source_scope='One actual 32-letter projective table, full product-scale/tail native and unsquared outer finalizer; not a universal alphabet.')
 parent['ledger']=ledger(out,free,parent['output']);parent['reconstruction']=dict(removed=removed,changed=changed)
 child=copy.deepcopy(parent);need(['D','+','history__u','height_slack']in out,'actual height definition')
 need([r[0]for r in out if'height_slack'in r[2:]]==['D'],'sole height-slack consumer')
 child['source']=[r for r in child['source']if r[0]!='D'];child['free']=['D'if v=='height_slack'else v for v in free];child['ledger']=ledger(child['source'],child['free'],child['output'])
 child['scope']='Rejected direct-D candidate. One fewer addition, but admits false positive ordinary inputs.'
 return parent,child

def execute(rows,values):
 env=dict(values)
 for n,o,a,b in rows:
  a=env[a]if type(a)is str else a;b=env[b]if type(b)is str else b;env[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return env

def outer(D):
 B=16*D;c0=D-1;u0=13;states=[(1,u0,1,u0)];Z=[0]*8;Hs=[0]*4;hats=[];power=1
 for label in CODE:
  state=states[-1]
  for i in range(4):Hs[i]+=(c0+state[i])*power
  lane=label-1;target=lane//2;src=target^1
  Z[lane]+=(c0+state[src])*power
  nxt=list(state);nxt[target]+=(1 if lane%2==0 else -1)*state[src];states.append(tuple(nxt));hats.append(power+1);power*=B
 need(states[-1]==(0,1,0,1),'genuine x0=0 endpoint')
 need(all(0<c0+v<2*D for st in states for v in st),'strict positive shifted digit range')
 Pval=power;J=(Pval-1)//(B-1);globalslack=Pval+1-sum(Hs)-sum(z+1 for z in Z)
 need(globalslack>0,'positive joint slack')
 values={'D':D,'x':B-1,'selection__bound_global':globalslack+48}
 for i,h in enumerate(Hs):values['H'+str(i)]=h-(24 if i%2 else 0)
 for i,z in enumerate(Z):values['Zhat'+str(i)]=z+1
 for i,h in enumerate(hats,1):values['controller__edge_hat'+str(i)]=h
 need(min(values.values())>0 and c0+u0-24>0,'all actual outer supplied coordinates positive')
 return values,dict(D=D,B=B,P=Pval,J=J,states=states,parent_Hs=Hs,Z=Z,old_joint_slack=globalslack)

def verify(root):
 need(len(PINS)==11,'eleven frozen dependencies')
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'pin '+n)
 parent,child=build(root);counts=Counter();rng=random.Random(243)
 need(child['ledger']['M']==parent['ledger']['M']and child['ledger']['A']==parent['ledger']['A']-1,'exact rejected one-addition projection')
 need(child['source']==[r for r in parent['source']if r[0]!='D'],'all rows literally retained after sole defining-gate deletion')
 need(child['comparisons']==parent['comparisons'],'every comparison unchanged')
 # Induction through the identical literal rows proves the full signed graph
 # identity once D=u+height_slack is restored by height_slack=D-u.
 # The evaluations below corroborate that exact source proof.
 for case in range(12):
  v={n:rng.randrange(-2,4)for n in child['free']}
  if case>=8:v={n:Fraction(x,3)for n,x in v.items()}
  y=execute(child['source'],v);pv={n:v[n]for n in parent['free']if n!='height_slack'};pv['height_slack']=v['D']-y['history__u'];x=execute(parent['source'],pv)
  need(all(x[n]==y[n]for n,o,a,b in child['source']),'complete signed coordinate identity');counts['whole_numeric_pullbacks']+=1;counts['rational_pullbacks']+=case>=8
 fixtures=[]
 for D in(32,64,128):
  supplied,context=outer(D);v={n:supplied.get(n,1)for n in child['free']};e=execute(child['source'],v)
  for i,(a,b)in enumerate(child['comparisons']):
   if i!=4:need(e[a]==e[b]if type(b)is str else e[a]==b,'all five actual outer comparisons')
  need(e['joint_bound_unit']==1,'actual joint scalar unit')
  B=context['B'];pv=context['P'];j=context['J'];c=child['cuts'];need(e[c['J']]==j and e[P]==pv,'actual common duration geometry')
  selector=[sum((h-1)for h,l in zip([supplied[f'controller__edge_hat{i+1}']for i in range(32)],CODE)if l==lab)for lab in range(1,9)]
  need(e[c['S']]==sum(s*pv**i for i,s in enumerate(selector)),'actual physical pack')
  need(e[c['C']]==sum((supplied[f'controller__edge_hat{i+1}']-1)*pv**i for i in range(32)),'actual edge pack')
  Q=2*B*pv**72;H=e['range_H'];M=e['range_M'];Z=e['range_Z']
  need(e['selection__q']==16*Q and 0<=min(H,M,Z)and max(H,M,Z)<Q and H&M==Z,'complete actual prescribed-scale AND')
  need(e['history__u']==13+24*(B-1)and D-e['history__u']<0,'positive ordinary input and negative restored height slack')
  # Native coordinates are placeholders only; do not assert a full numeric zero.
  need(e[child['output']]!=0,'outer fixture explicitly not a materialized native zero')
  digest=lambda z:sha(z.to_bytes((z.bit_length()+7)//8 or 1,'big'))
  fixtures.append(dict(D=D,B=B,x=B-1,u=e['history__u'],word_length=32,P_bits=pv.bit_length(),q_bits=e['selection__q'].bit_length(),AND=True,outer_comparisons=5,joint_unit=1,native_values_are_placeholders=True,restored_parent_slack=D-e['history__u'],packed_H_sha256=digest(H),packed_M_sha256=digest(M),packed_Z_sha256=digest(Z)))
  counts['genuine_outer_counterexamples']+=1
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,parent=parent,rejected_candidate=child,counts=dict(counts),outer_fixtures=fixtures,scope='Counterexample to deleting the input-dependent height constructor in this complete fixed-table architecture. Full native positive extensions are proved parametrically, not numerically materialized; no original valid parent or universal bound is refuted.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact receipt')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],parent=r['parent']['ledger'],child=r['rejected_candidate']['ledger'],outer=r['outer_fixtures'])))
if __name__=='__main__':main()
