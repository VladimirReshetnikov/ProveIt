"""A sparse prime-payload history with a paid ordinary-input power prefix.

The sole program parameter is fixed at3^e on a universal slice; ordinary x
controls the exact number of initial doublings. No expanded residue table
or uncounted variable exponent appears in the emitted arithmetic source.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from math import prod,isqrt
from pathlib import Path
import random

import korec_packed_counter_units as korec
import residue_affine_packed_history as history

t=history.native_host;ps=history.positive_scale;fields=history.fields
units=history.units;coupled=history.coupled
execute=history.execute;at=history.at
TABLE=korec.TABLE
PRIMES=(5,3,2,7,11,13,17,19)
FORMS=('raw','scaled','projected','units','coupled')


def isprime(n):return type(n) is int and n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def branches(table,primes):
 table=korec.normalize(table,len(primes))
 assert len(set(primes))==len(primes) and all(isprime(p) for p in primes)
 assert primes[1:3]==(3,2)
 # Fields: source,target,kind,prime,current coefficient,next coefficient,
 # current offset,next offset. Positive pure tests divide only the witness.
 answer=[(0,0,'I',2,1,2,1,2),(0,1,'I',2,1,2,1,2)]
 for q,(op,r,*targets) in enumerate(table):
  p=primes[r]
  if op=='I':answer.append((q+1,targets[0]+1,'I',p,1,p,1,p))
  else:
   pair=(p,1,p,1) if op=='D' else (p,p,p,p)
   answer.append((q+1,targets[0]+1,'D' if op=='D' else 'T',p,*pair))
   answer.append((q+1,targets[1]+1,'Z',p,p,p,1,1))
 return table,tuple(answer)


def raw(table=TABLE,primes=PRIMES,baseline=None,shared=True):
 primes=tuple(primes);table,edges=branches(table,primes);m=len(edges)
 pairs=sorted(set((v[4],v[5]) for v in edges));baseline=pairs[0] if baseline is None else tuple(baseline)
 assert baseline in pairs
 classes=[pair for pair in pairs if pair!=baseline];g=len(classes)
 G=t.Gates();o=G.emit;add=lambda seq,label:G.sum(seq,label) if seq else 0
 E=[o('-',f'edge{i}_hat',1,'edge') for i in range(m)];J=add(E,'selectors')
 W,R,S=[o('-',v+'_hat',1,v) for v in ('quotient','remainder','complement')]
 Z=[o('-',f'product{i}_hat',1,'selected') for i in range(g)]
 h=add(['program','input','final_payload','height_slack'],'height')
 radix_multiplier=1
 while radix_multiplier<max(4,m+1,len(table)+2,max(primes)+1):radix_multiplier*=2
 B=o('*',radix_multiplier,h,'radix');Bm=o('-',B,1,'radix_minus_one')
 P=o('+',o('*',Bm,J,'scale_minus_one'),1,'scale')
 rm=o('*',o('-',h,1,'height_minus_one'),J,'range_mask')
 groups=[add([E[i] for i,v in enumerate(edges) if (v[4],v[5])==pair],'class_selector') for pair in classes]
 def linear(coeffs,words,label):
  terms=[(w,c) for w,c in zip(words,coeffs) if c]
  if not terms:return 0
  # Group equal fixed coefficients before comparing literal schedules.
  grouped=[(add([w for w,c in terms if c==v],label+'_coefficient_group'),v) for v in sorted({c for _,c in terms})]
  original=list(G.source);cache=dict(G.cache)
  direct=add([o('*',c,w,label+'_coefficient') for w,c in grouped],label+'_direct')
  if min(c for _,c in grouped)<0 or max(c for _,c in grouped)>4*len(grouped)+4:return direct
  ds,dc=list(G.source),dict(G.cache);G.source=original;G.cache=cache
  running=0;parts=[]
  for i in range(max(c for _,c in grouped),0,-1):
   running=o('+',running,add([w for w,c in grouped if c==i],label+'_coefficient'),'suffix');parts.append(running)
  suffix=add(parts,label+'_suffix_sum')
  if len(ds)<=len(G.source):G.source=ds;G.cache=dc;return direct
  return suffix
 common=o('+',J,R,'common_offset')
 current=add([o('*',baseline[0],W,'current_base'),linear([p[0]-baseline[0] for p in classes],Z,'current_products'),common,
  linear([v[6]-1 for v in edges],E,'current_offsets')],'current')
 following=add([o('*',baseline[1],W,'next_base'),linear([p[1]-baseline[1] for p in classes],Z,'next_products'),common,
  linear([v[7]-1 for v in edges],E,'next_offsets')],'following')
 remainder_total=linear([v[3]-2 if v[2]=='Z' else 0 for v in edges],E,'remainder_total')
 remainders=o('+',R,S,'remainders')
 current_control=linear([v[0] for v in edges],E,'current_control')
 next_control=linear([v[1] for v in edges],E,'next_control')
 control_left=o('*',B,next_control,'control_left')
 control_right=o('+',current_control,o('*',len(table)+1,P,'halt_control'),'control_right')
 transport_left=o('+',o('*',B,following,'shift_payload'),'program','transport_left')
 transport_right=o('+',current,o('*',P,'final_payload','final_payload_scaled'),'transport_right')
 load_word=o('+',E[0],E[1],'load_word')
 load_count=o('+',o('*',Bm,o('-','loader_quotient_hat',1,'loader_quotient'),'loader_remainder'),'input','load_count')
 bound=add([J,'quotient_hat','remainder_hat','complement_hat']+[f'product{i}_hat' for i in range(g)]+['global_slack'],'global_bound')
 def powersum(n):
  if n==0:return 1,0
  if n==1:return P,1
  power,series=powersum(n//2)
  series=o('*',series,o('+',power,1,'power_plus_one'),'repeat_double');power=o('*',power,power,'repeat_square')
  if n%2:series=o('+',series,power,'repeat_odd');power=o('*',power,P,'repeat_power')
  return power,series
 if shared:
  PM,RM=powersum(m);Pg,_=powersum(g);_,Rg=powersum(g+1)
  ep=G.pack(E,P,'edges_pack');tail=o('+',R,o('*',P,S,'complement_lane'),'two_range_lanes')
  ah=o('+',ep,o('*',PM,o('+',o('*',W,Rg,'repeated_quotient'),o('*',o('*',Pg,P,'range_tail_power'),tail,'range_tail'),'H_inner'),'H_shift'),'joined_H')
  mask_rep=o('+',1,o('*',P,o('+',P,1,'range_repeat_inner'),'range_repeat_shift'),'three_range_repeat')
  gm=G.pack(groups,P,'group_pack') if groups else 0
  am=o('+',o('*',J,RM,'repeated_J'),o('*',PM,o('+',o('*',Bm,gm,'all_class_masks'),o('*',Pg,o('*',rm,mask_rep,'all_ranges'),'range_masks_shift'),'M_inner'),'M_shift'),'joined_M')
  zp=G.pack(Z,P,'product_pack') if Z else 0
  az=o('+',ep,o('*',PM,o('+',zp,o('*',Pg,o('+',W,o('*',P,tail,'range_tail_Z'),'Z_ranges'),'range_Z_shift'),'Z_inner'),'Z_shift'),'joined_Z')
 else:
  ah=G.pack(E+[W]*g+[W,R,S],P,'joined_H')
  am=G.pack([J]*m+[o('*',Bm,c,'class_mask') for c in groups]+[rm]*3,P,'joined_M')
  az=G.pack(E+Z+[W,R,S],P,'joined_Z')
 exponent=1;scale=P
 while exponent<m+g+3:scale=o('*',scale,scale,'scale_power');exponent*=2
 scale=o('*',B,scale,'native_scale')
 ns,np,_=t.native.source('and64_prescribed');p='native__';name=lambda v:p+v if isinstance(v,str) else v
 source=G.source+[(p+'q','*',16,scale),(p+'scaled_A','*',16,ah),(p+'padded_A','+',p+'scaled_A',12),
  (p+'scaled_B','*',16,am),(p+'padded_B','+',p+'scaled_B',10),(p+'scaled_Z','*',16,az),(p+'F3','+',p+'scaled_Z',8)]
 source += [(name(v),op,name(a),name(b)) for v,op,a,b in ns[7:]]
 aux=[f'edge{i}_hat' for i in range(m)]+[f'product{i}_hat' for i in range(g)]+['quotient_hat','remainder_hat','complement_hat','final_payload','height_slack','global_slack','loader_quotient_hat']+[name(v) for v in t.native.domains('and64_prescribed')[1]]
 comparisons=[(bound,P),(remainders,remainder_total),(control_left,control_right),
  (transport_left,transport_right),(load_word,load_count)]+[(name(a),name(b)) for a,b in np]
 # powersum exposes both ports; discard any unused temporary power/series.
 nodes={v:(a,b) for v,_,a,b in source};live=set();pending=[v for pair in comparisons for v in pair]
 while pending:
  v=pending.pop()
  if isinstance(v,str) and v in nodes and v not in live:live.add(v);pending.extend(nodes[v])
 assert all(v in live for v,_,_,_ in source if v.startswith(p))
 source=[row for row in source if row[0] in live]
 packet=ps.metadata(dict(source=source,comparisons=comparisons,
  parameters=['program','input'],auxiliaries=aux,table=table,primes=primes,edges=edges,classes=classes,baseline=baseline,
  radix_multiplier=radix_multiplier,scale_exponent=exponent,shared=shared,form='raw',
  interfaces=dict(h=h,B=B,J=J,P=P,W=W,R=R,S=S,range_mask=rm,joined_H=ah,joined_M=am,joined_Z=az,
   current=current,following=following,current_control=current_control,next_control=next_control,
   load_word=load_word,load_count=load_count,native_scale=scale)))
 ps.checked_source(source,packet['parameters'],aux)
 return packet


def build(table=TABLE,form='coupled',primes=PRIMES,baseline='auto',shared=True):
 assert form in FORMS
 if baseline=='auto':
  _,edges=branches(table,tuple(primes));pairs=sorted(set((v[4],v[5]) for v in edges))
  packet=min([raw(table,primes,p,shared) for p in pairs],key=lambda p:(p['operations'],p['multiplications'],p['baseline']))
 else:packet=raw(table,primes,baseline,shared)
 if form!='raw':packet=ps.rewrite(packet,'native__')
 if form in ('projected','units','coupled'):packet=fields.rewrite(packet,prefix='native__')
 if form in ('units','coupled'):packet=units.rewrite(packet,normalized=True)
 if form=='coupled':packet=coupled.rewrite(packet)
 return dict(packet,form=form)


def polynomial_source(packet):
 return units.polynomial_source(packet) if packet.get('native_norm_units') else t.polynomial_source(packet)


def ledger(packet):
 rec=units.ledger(packet) if packet.get('native_norm_units') else t.ledger(packet)
 return rec


def closure(packet):
 source,out=polynomial_source(packet);nodes={n:(a,b) for n,_,a,b in source};seen=set()
 def visit(n):
  if not isinstance(n,str) or n not in nodes or n in seen:return
  seen.add(n)
  for v in nodes[n]:visit(v)
 visit(out)
 assert seen==set(nodes),set(nodes)-seen
 return len(source)


def direct_outer(packet,v):
 E=[v[f'edge{i}_hat']-1 for i in range(len(packet['edges']))]
 Z=[v[f'product{i}_hat']-1 for i in range(len(packet['classes']))]
 W,R,S=[v[k+'_hat']-1 for k in ('quotient','remainder','complement')]
 J=sum(E);h=v['program']+v['input']+v['final_payload']+v['height_slack']
 B=packet['radix_multiplier']*h;P=(B-1)*J+1;rm=(h-1)*J
 G=[sum(e for e,row in zip(E,packet['edges']) if (row[4],row[5])==pair) for pair in packet['classes']]
 C=packet['baseline'][0]*W+sum((pair[0]-packet['baseline'][0])*z for pair,z in zip(packet['classes'],Z))
 N=packet['baseline'][1]*W+sum((pair[1]-packet['baseline'][1])*z for pair,z in zip(packet['classes'],Z))
 C+=sum(e*row[6] for e,row in zip(E,packet['edges']))+R
 N+=sum(e*row[7] for e,row in zip(E,packet['edges']))+R
 current=sum(e*row[0] for e,row in zip(E,packet['edges']));following=sum(e*row[1] for e,row in zip(E,packet['edges']))
 pack=lambda seq:sum(c*P**j for j,c in enumerate(seq))
 H=pack(E+[W]*len(Z)+[W,R,S]);M=pack([J]*len(E)+[(B-1)*g for g in G]+[rm]*3);A=pack(E+Z+[W,R,S])
 bound=J+W+R+S+sum(Z)+len(Z)+3+v['global_slack']
 L=E[0]+E[1];load=(B-1)*(v['loader_quotient_hat']-1)+v['input']
 residuals=[bound-P,R+S-sum(e*(row[3]-2) for e,row in zip(E,packet['edges']) if row[2]=='Z'),
  B*following-current-(len(packet['table'])+1)*P,
  B*N+v['program']-C-P*v['final_payload'],L-load]
 return dict(h=h,B=B,J=J,P=P,W=W,R=R,S=S,range_mask=rm,joined_H=H,joined_M=M,joined_Z=A,
  current=C,following=N,current_control=current,next_control=following,load_word=L,load_count=load,
  native_scale=B*P**packet['scale_exponent']),residuals


def payload_run(table,program,input_value,primes=PRIMES,limit=100):
 """Literal integer payload execution; the prefix uses exactly input steps."""
 primes=tuple(primes);table,edges=branches(table,primes)
 assert program>0 and input_value>0
 states=[(0,program)];selected=[];value=program
 for i in range(input_value):
  selected.append(0 if i<input_value-1 else 1);value*=2
  states.append((0 if i<input_value-1 else 1,value))
 q=0
 indices={}
 for i,row in enumerate(edges[2:],2):indices[(row[0],row[2])]=i
 for _ in range(limit):
  if q==len(table):break
  op,r,*targets=table[q];p=primes[r]
  branch=0 if op=='I' or value%p==0 else 1
  kind=op if branch==0 else 'Z'
  selected.append(indices[(q+1,kind)])
  if op=='I':value*=p
  elif op=='D' and branch==0:value//=p
  q=targets[branch];states.append((q+1,value))
 return states,selected


def pack_path(packet,states,selected,input_value):
 assert selected and len(states)==len(selected)+1 and states[-1][0]==len(packet['table'])+1
 W=[];R=[];S=[]
 for (q,value),(nxt,out),edge in zip(states,states[1:],selected):
  row=packet['edges'][edge];assert (q,nxt)==row[:2];p=row[3]
  if row[2]=='I':w=value-1;r=s=0;assert out==p*value
  elif row[2] in ('D','T'):
   assert value%p==0;w=value//p-1;r=s=0
   assert out==(value//p if row[2]=='D' else value)
  else:
   w,rem=divmod(value,p);assert 1<=rem<p and out==value
   r=rem-1;s=p-1-rem
  assert min(w,r,s)>=0;W.append(w);R.append(r);S.append(s)
 h=1
 while h<=max([states[0][1]+input_value+states[-1][1]]+W+R+S):h*=2
 B=packet['radix_multiplier']*h;P=B**len(selected);J=(P-1)//(B-1)
 pack=lambda seq:sum(v*B**i for i,v in enumerate(seq))
 ee=[pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))]
 zz=[pack([w if packet['edges'][edge][4:6]==pair else 0 for w,edge in zip(W,selected)]) for pair in packet['classes']]
 w,r,s=map(pack,(W,R,S));L=ee[0]+ee[1]
 assert (L-input_value)%(B-1)==0 and (L-input_value)//(B-1)>=0
 v=dict(program=states[0][1],input=input_value,final_payload=states[-1][1],
  height_slack=h-states[0][1]-input_value-states[-1][1],quotient_hat=w+1,remainder_hat=r+1,
  complement_hat=s+1,global_slack=P-J-w-r-s-sum(zz)-len(zz)-3,
  loader_quotient_hat=1+(L-input_value)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(ee)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(zz)})
 assert min(v.values())>0
 return v


def control_modulus(table,primes):
 K=len(table)+2
 while not isprime(K) or K in primes:K+=1
 return K,K*prod(primes)


def numerical_step(table,primes,value):
 """The total deterministic one-number map after the separately paid loader."""
 assert value>0
 K,_=control_modulus(table,primes);payload,state0=divmod(value-1,K);payload+=1
 if state0>=len(table):return K*(2*payload-1)+state0+1
 op,r,*targets=table[state0];p=primes[r]
 branch=0 if op=='I' or payload%p==0 else 1
 if op=='I':payload*=p
 elif op=='D' and branch==0:payload//=p
 return K*(payload-1)+targets[branch]+1


def residue_row(table,primes,residue):
 """Exact random-access positive residue table; never enumerate its modulus."""
 K,M=control_modulus(table,primes);assert 1<=residue<=M
 payload,state0=divmod(residue-1,K);payload+=1
 ratio_num=ratio_den=1
 if state0>=len(table):ratio_num=2
 else:
  op,r,*targets=table[state0]
  if op=='I':ratio_num=primes[r]
  elif op=='D' and payload%primes[r]==0:ratio_den=primes[r]
 assert M*ratio_num%ratio_den==0
 return M*ratio_num//ratio_den,numerical_step(table,primes,residue)


def raw_audit(packet,cases,seed):
 rng=random.Random(seed);source,out=polynomial_source(packet);ns,np,_=t.native.source('and64_prescribed')
 for case in range(cases):
  v={n:rng.randrange(1,4) if case<cases//2 else rng.randrange(-2,3) for n in packet['parameters']+packet['auxiliaries']}
  env=execute(source,v);oracle,rr=direct_outer(packet,v)
  assert all(at(env,name)==oracle[key] for key,name in packet['interfaces'].items())
  nv=dict(P=oracle['native_scale'],Hhat=oracle['joined_H']+1,Mhat=oracle['joined_M']+1,Zhat=oracle['joined_Z']+1,
   **{n:v['native__'+n] for n in t.native.domains('and64_prescribed')[1]})
  ne=execute(ns,nv);expected=rr+[at(ne,a)-at(ne,b) for a,b in np]
  assert expected==[at(env,a)-at(env,b) for a,b in packet['comparisons']]
  assert env[out]==sum(r*r for r in expected)
 return dict(complete_raw_identities=cases,signed=cases//2)


def shared_audit(packet,cases,seed):
 old=build(packet['table'],packet['form'],packet['primes'],packet['baseline'],False)
 assert old['parameters']==packet['parameters'] and old['auxiliaries']==packet['auxiliaries']
 s,o=polynomial_source(packet);os,oo=polynomial_source(old);rng=random.Random(seed)
 for case in range(cases):
  v={n:rng.randrange(1,4) if case<cases//2 else rng.randrange(-2,3) for n in packet['parameters']+packet['auxiliaries']}
  e=execute(s,v);oe=execute(os,v)
  assert e[o]==oe[oo]
  assert all(at(e,name)==at(oe,old['interfaces'][k]) for k,name in packet['interfaces'].items())
  assert [at(e,a)-at(e,b) for a,b in packet['comparisons']]==[at(oe,a)-at(oe,b) for a,b in old['comparisons']]
 return dict(complete_shared_packing_identities=cases,signed=cases//2,unshared_operations=len(os),shared_operations=len(s))


def path_audit():
 rng=random.Random(845631);tables=[(TABLE,PRIMES)]
 for m in range(1,7):
  for _ in range(4):
   k=rng.randrange(3,6);primes=PRIMES[:k]
   table=[]
   for q in range(m):
    op=rng.choice(('I','D','T'));table.append(tuple([op,rng.randrange(k)]+[rng.randrange(m+1) for _ in range(1 if op=='I' else 2)]))
   tables.append((tuple(table),primes))
 counts=Counter();rows=0;wrong=0
 for table,primes in tables:
  packet=build(table,'raw',primes)
  outer=[row for row in packet['source'] if not row[0].startswith('native__')]
  for code in range(3):
   for x in range(1,5):
    states,selected=payload_run(table,3**code,x,primes,limit=45)
    if states[-1][0]!=len(table)+1:continue
    values=pack_path(packet,states,selected,x);env=execute(outer,values);o,rr=direct_outer(packet,values)
    assert rr==[0]*5 and o['joined_H']&o['joined_M']==o['joined_Z']
    assert all(at(env,v)==o[k] for k,v in packet['interfaces'].items())
    assert all(at(env,a)==at(env,b) for a,b in packet['comparisons'][:5])
    # Independent counter-vector simulation begins after the arithmetic prefix.
    vector=[0]*len(primes);vector[1:3]=[code,x];q=0
    for (state,value),(dest,newvalue),eidx in zip(states[x:],states[x+1:],selected[x:]):
     assert state==q+1 and value==prod(p**v for p,v in zip(primes,vector))
     op,r,*targets=table[q];branch=0 if op=='I' or vector[r]>0 else 1
     if op=='I':vector[r]+=1
     elif op=='D' and branch==0:vector[r]-=1
     q=targets[branch]
     assert dest==q+1 and newvalue==prod(p**v for p,v in zip(primes,vector))
     counts[op+str(branch)]+=1
    assert q==len(table)
    # Changing ordinary x while preserving this exact chronology fails count.
    bad=dict(values,input=x+1,height_slack=values['height_slack']-1)
    if bad['height_slack']>0:
     bo,br=direct_outer(packet,bad);assert br[:4]==[0]*4 and br[4]==-1;wrong+=1
    counts['histories']+=1;rows+=len(selected)
 return dict(tables=len(tables),counts=dict(counts),chronological_rows=rows,wrong_input_counts_rejected=wrong,
  scope='Actual outer paths and differential payload/counter semantics; no full Pell witnesses materialized.')


def residue_audit():
 rng=random.Random(928417);checks=0
 contexts=[(TABLE,PRIMES),((('I',0,1),),PRIMES[:3]),((('D',2,0,1),),PRIMES[:3]),
  ((('T',1,1,2),('D',0,2,0)),PRIMES[:3])]
 for table,primes in contexts:
  K,M=control_modulus(table,primes)
  for _ in range(100):
   s=rng.randrange(1,M+1);a,d=residue_row(table,primes,s)
   for q in (0,1,2,7):assert numerical_step(table,primes,M*q+s)==a*q+d;checks+=1
 return dict(random_access_residue_identities=checks,default_control_modulus=control_modulus(TABLE,PRIMES)[0],
  default_combined_modulus=control_modulus(TABLE,PRIMES)[1],expanded_residue_rows_materialized=0)


def loader_no_wrap_audit():
 checked=aliases=0
 for B in (8,16,32,64,128):
  for program in range(1,min(20,B)):
   for ell in range(1,10):
    if program*2**ell>=B:continue
    L=(B**ell-1)//(B-1)
    for x in range(1,B-1):
     quotient,rem=divmod(L-x,B-1)
     feasible=quotient>=0 and rem==0
     assert feasible==(ell==x);checked+=1
    # At equal modulus but without the proved growth bound, aliases exist.
    alias=ell+B-1;Lalias=(B**alias-1)//(B-1)
    assert (Lalias-ell)%(B-1)==0 and program*2**alias>=B;aliases+=1
 return dict(bounded_count_congruences=checked,unbounded_aliases_excluded_by_growth=aliases)


def branch_guard_audit():
 cases=accepted=0
 for p in (2,3,5,7,11,13,17,19):
  for kind in ('I','D','T','Z'):
   for w in range(4):
    for r in range(p):
     for s in range(p):
      good=r+s==(p-2 if kind=='Z' else 0)
      if kind=='I':current=w+1+r;following=p*(w+1)+r
      elif kind=='D':current=p*(w+1)+r;following=w+1+r
      elif kind=='T':current=following=p*(w+1)+r
      else:current=following=p*w+1+r
      if good:
       assert current>0 and following>0
       if kind=='I':assert following==p*current
       elif kind=='D':assert current%p==0 and following==current//p
       elif kind=='T':assert current%p==0 and following==current
       else:assert current%p!=0 and following==current
       accepted+=1
      cases+=1
 return dict(quotient_remainder_component_assignments=cases,legal_components=accepted)


def verify():
 fixtures=[(TABLE,PRIMES),((('I',0,1),),PRIMES[:3]),((('D',2,0,1),),PRIMES[:3]),
  ((('T',1,1,2),('I',0,2)),PRIMES[:3]),((('I',2,1),),PRIMES[:3])]
 records=[];audits=[]
 for i,(table,primes) in enumerate(fixtures):
  packets={f:build(table,f,primes) for f in FORMS}
  for f,p in packets.items():closure(p);records.append(dict(fixture=i,form=f,ledger=ledger(p)))
  audits.append(dict(raw=raw_audit(packets['raw'],24,845900+i),
   scale=ps.identity_audit(packets['scaled'],16,846000+i),fields=fields.audit(packets['projected'],16,846100+i),
   ordinary_units=units.audit(packets['units']['normalized_parent'],16,846200+i),
   normalized_units=units.audit(packets['units'],16,846300+i),
   index=coupled.audit(packets['coupled']['coupled_parent'],16,846400+i),
   coupled=coupled.audit(packets['coupled'],16,846500+i),
   shared=[shared_audit(packets[f],16,846600+100*i+j) for j,f in enumerate(FORMS)]))
 packet=build();source,out=polynomial_source(packet)
 return dict(theorem='Complete ordinary-input universal polynomial from the literal U21 prime-payload machine and a paid power prefix.',
  default_ledger=ledger(packet),default_table=TABLE,default_primes=PRIMES,edges=packet['edges'],
  default_baseline=packet['baseline'],exceptional_pairs=packet['classes'],joined_lanes=len(packet['edges'])+len(packet['classes'])+3,
  ledgers=records,audits=audits,paths=path_audit(),residue_map=residue_audit(),prefix=loader_no_wrap_audit(),branch_guards=branch_guard_audit(),
  source=source,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
  source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest(),
  scope='One positive program parameter at3^e, ordinary x paid by the prefix. The body is a total residue-affine map; the loader is a separately counted branching prefix. No improvement to the established75/87 or U9/Korec counts is asserted.')


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(path.read_text())==result
 print(json.dumps({k:result[k] for k in ('default_ledger','paths','residue_map','prefix')},indent=2))
