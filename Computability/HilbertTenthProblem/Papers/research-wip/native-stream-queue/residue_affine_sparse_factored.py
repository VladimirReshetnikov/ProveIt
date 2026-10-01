"""Sparse universal prime-payload compiler with factored prime/action masks.

The literal U21, paid ordinary-input prefix and complete chronology are
inherited semantically; the selected quotient graph is newly factored.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import prod
from pathlib import Path
import random
import residue_affine_sparse_universal as parent

t=parent.t;ps=parent.ps;fields=parent.fields;units=parent.units;coupled=parent.coupled
execute=parent.execute;at=parent.at;TABLE=parent.TABLE;PRIMES=parent.PRIMES
FORMS=parent.FORMS;branches=parent.branches;payload_run=parent.payload_run
polynomial_source=parent.polynomial_source;ledger=parent.ledger;closure=parent.closure

def raw(table=TABLE,primes=PRIMES,shared=True):
 primes=tuple(primes);table,edges=branches(table,primes);m=len(edges)
 classes=sorted({v[3] for v in edges}-{2});k=len(classes);g=k+2
 G=t.Gates();o=G.emit;add=lambda seq,label:G.sum(seq,label) if seq else 0
 E=[o('-',f'edge{i}_hat',1,'edge') for i in range(m)];J=add(E,'selectors')
 W,R,S=[o('-',v+'_hat',1,v) for v in ('quotient','remainder','complement')]
 Z=[o('-',f'product{i}_hat',1,'selected') for i in range(g)]
 Zp=Z[:k];YI,YD=Z[k:]
 h=add(['program','input','final_payload','height_slack'],'height')
 radix_multiplier=1
 while radix_multiplier<max(4,m+1,len(table)+2,3*max(primes)+1):radix_multiplier*=2
 B=o('*',radix_multiplier,h,'radix');Bm=o('-',B,1,'radix_minus_one')
 P=o('+',o('*',Bm,J,'scale_minus_one'),1,'scale')
 rm=o('*',o('-',h,1,'height_minus_one'),J,'range_mask')
 groups=[add([E[i] for i,v in enumerate(edges) if v[3]==prime],'prime_selector') for prime in classes]
 groups += [add([E[i] for i,v in enumerate(edges) if v[2]==kind],'action_selector') for kind in ('I','D')]
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
 U=o('+',W,J,'positive_quotient_word')
 V=o('+',U,linear([p-2 for p in classes],Zp,'prime_difference'),'difference_word')
 # Compare direct zero-selector summation with its exact action complement.
 saved=list(G.source);cache=dict(G.cache)
 zero_word=add([E[i] for i,v in enumerate(edges) if v[2]=='Z'],'zero_word')
 direct_source=list(G.source);direct_cache=dict(G.cache);direct_zero=zero_word
 G.source=saved;G.cache=cache
 positive_test=add([E[i] for i,v in enumerate(edges) if v[2]=='T'],'positive_test_word')
 zero_word=o('-',o('-',o('-',J,groups[-2],'non_increment'),groups[-1],'non_decrement'),positive_test,'zero_complement')
 if len(direct_source)<=len(G.source):G.source=direct_source;G.cache=direct_cache;zero_word=direct_zero
 common=o('-',o('-',o('+',U,V,'common_quotient'),S,'common_remainder'),zero_word,'common_payload')
 current=o('-',common,YI,'current')
 following=o('-',common,YD,'following')
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
 bound=add([J,V,'quotient_hat','remainder_hat','complement_hat']+[f'product{i}_hat' for i in range(g)]+['global_slack'],'global_bound')
 def powersum(n):
  if n==0:return 1,0
  if n==1:return P,1
  power,series=powersum(n//2)
  series=o('*',series,o('+',power,1,'power_plus_one'),'repeat_double');power=o('*',power,power,'repeat_square')
  if n%2:series=o('+',series,power,'repeat_odd');power=o('*',power,P,'repeat_power')
  return power,series
 if shared:
  PM,RM=powersum(m);Pk,Rk=powersum(k);Pg,_=powersum(g)
  ep=G.pack(E,P,'edges_pack');tail=o('+',R,o('*',P,S,'complement_lane'),'two_range_lanes')
  ranges=o('+',W,o('*',P,tail,'range_tail'),'ranges')
  actions=o('*',V,o('+',P,1,'two_repeat'),'repeat_difference')
  hr=o('+',actions,o('*',o('*',P,P,'P2'),ranges,'range_shift'),'H_action_range')
  ah=o('+',ep,o('*',PM,o('+',o('*',U,Rk,'repeat_quotient'),o('*',Pk,hr,'action_shift'),'H_inner'),'H_shift'),'joined_H')
  mask_rep=o('+',1,o('*',P,o('+',P,1,'range_repeat_inner'),'range_repeat_shift'),'three_range_repeat')
  gm=G.pack(groups,P,'group_pack')
  am=o('+',o('*',J,RM,'repeated_J'),o('*',PM,o('+',o('*',Bm,gm,'all_class_masks'),o('*',Pg,o('*',rm,mask_rep,'all_ranges'),'range_masks_shift'),'M_inner'),'M_shift'),'joined_M')
  zp=G.pack(Z,P,'product_pack')
  az=o('+',ep,o('*',PM,o('+',zp,o('*',Pg,ranges,'range_Z_shift'),'Z_inner'),'Z_shift'),'joined_Z')
 else:
  ah=G.pack(E+[U]*k+[V,V]+[W,R,S],P,'joined_H')
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
  parameters=['program','input'],auxiliaries=aux,table=table,primes=primes,edges=edges,classes=classes,
  radix_multiplier=radix_multiplier,scale_exponent=exponent,shared=shared,form='raw',
  interfaces=dict(U=U,V=V,h=h,B=B,J=J,P=P,W=W,R=R,S=S,range_mask=rm,joined_H=ah,joined_M=am,joined_Z=az,
   current=current,following=following,current_control=current_control,next_control=next_control,
   load_word=load_word,load_count=load_count,native_scale=scale)))
 ps.checked_source(source,packet['parameters'],aux)
 return packet


def build(table=TABLE,form='coupled',primes=PRIMES,shared=True):
 assert form in FORMS
 packet=raw(table,primes,shared)
 if form!='raw':packet=ps.rewrite(packet,'native__')
 if form in ('projected','units','coupled'):packet=fields.rewrite(packet,prefix='native__')
 if form in ('units','coupled'):packet=units.rewrite(packet,normalized=True)
 if form=='coupled':packet=coupled.rewrite(packet)
 return dict(packet,form=form)


def direct_outer(packet,v):
 E=[v[f'edge{i}_hat']-1 for i in range(len(packet['edges']))]
 Z=[v[f'product{i}_hat']-1 for i in range(len(packet['classes'])+2)]
 k=len(packet['classes']);W,R,S=[v[n+'_hat']-1 for n in ('quotient','remainder','complement')]
 J=sum(E);U=W+J;V=U+sum((p-2)*z for p,z in zip(packet['classes'],Z))
 h=v['program']+v['input']+v['final_payload']+v['height_slack']
 B=packet['radix_multiplier']*h;P=(B-1)*J+1;rm=(h-1)*J
 groups=[sum(e for e,row in zip(E,packet['edges']) if row[3]==p) for p in packet['classes']]
 groups += [sum(e for e,row in zip(E,packet['edges']) if row[2]==kind) for kind in ('I','D')]
 zero=sum(e for e,row in zip(E,packet['edges']) if row[2]=='Z')
 C=U+V-S-zero-Z[k];N=U+V-S-zero-Z[k+1]
 current=sum(e*row[0] for e,row in zip(E,packet['edges']));following=sum(e*row[1] for e,row in zip(E,packet['edges']))
 pack=lambda seq:sum(c*P**j for j,c in enumerate(seq))
 H=pack(E+[U]*k+[V,V]+[W,R,S]);M=pack([J]*len(E)+[(B-1)*g for g in groups]+[rm]*3);A=pack(E+Z+[W,R,S])
 bound=J+V+W+R+S+sum(Z)+len(Z)+3+v['global_slack']
 L=E[0]+E[1];load=(B-1)*(v['loader_quotient_hat']-1)+v['input']
 residuals=[bound-P,R+S-sum(e*(row[3]-2) for e,row in zip(E,packet['edges']) if row[2]=='Z'),
  B*following-current-(len(packet['table'])+1)*P,
  B*N+v['program']-C-P*v['final_payload'],L-load]
 return dict(U=U,V=V,h=h,B=B,J=J,P=P,W=W,R=R,S=S,range_mask=rm,joined_H=H,joined_M=M,joined_Z=A,
  current=C,following=N,current_control=current,next_control=following,load_word=L,load_count=load,
  native_scale=B*P**packet['scale_exponent']),residuals


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
 zz=[pack([w+1 if packet['edges'][edge][3]==p else 0 for w,edge in zip(W,selected)]) for p in packet['classes']]
 vv=[(packet['edges'][edge][3]-1)*(w+1) for w,edge in zip(W,selected)]
 zz += [pack([v if packet['edges'][edge][2]==kind else 0 for v,edge in zip(vv,selected)]) for kind in ('I','D')]
 w,r,s=map(pack,(W,R,S));V=pack(vv);L=ee[0]+ee[1]
 assert V==w+J+sum((p-2)*z for p,z in zip(packet['classes'],zz))
 assert (L-input_value)%(B-1)==0 and (L-input_value)//(B-1)>=0
 v=dict(program=states[0][1],input=input_value,final_payload=states[-1][1],
  height_slack=h-states[0][1]-input_value-states[-1][1],quotient_hat=w+1,remainder_hat=r+1,
  complement_hat=s+1,global_slack=P-J-V-w-r-s-sum(zz)-len(zz)-3,
  loader_quotient_hat=1+(L-input_value)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(ee)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(zz)})
 assert min(v.values())>0
 return v


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
 old=build(packet['table'],packet['form'],packet['primes'],False)
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
 rng=random.Random(973610);tables=[(TABLE,PRIMES)]
 for m in range(1,7):
  for _ in range(5):
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


def factor_cell_audit():
 cases=legal=0
 for p in (2,3,5,7,11,13,17,19):
  for kind in ('I','D','T','Z'):
   for w in (-2,-1,0,1,2,7):
    for r in (-2,0,1,3):
     for s in (-2,0,1,3):
      U=w+1;V=(p-1)*U
      new_current=U+V-s-int(kind=='Z')-(V if kind=='I' else 0)
      new_next=U+V-s-int(kind=='Z')-(V if kind=='D' else 0)
      if kind=='I':old_current=w+1+r;old_next=p*(w+1)+r
      elif kind=='D':old_current=p*(w+1)+r;old_next=w+1+r
      elif kind=='T':old_current=old_next=p*(w+1)+r
      else:old_current=old_next=p*w+1+r
      delta=r+s-(p-2 if kind=='Z' else 0)
      assert new_current==old_current-delta and new_next==old_next-delta
      B=64
      assert B*new_next-new_current==B*old_next-old_current-(B-1)*delta
      if min(w,r,s)>=0 and delta==0:
       assert new_current>0 and new_next>0
       if kind=='I':assert new_next==p*new_current
       elif kind=='D':assert new_current%p==0 and new_next==new_current//p
       elif kind=='T':assert new_current%p==0 and new_next==new_current
       else:assert new_current%p and new_next==new_current
       legal+=1
      cases+=1
 return dict(signed_scalar_factor_corrections=cases,legal_branch_cases=legal)


def typed_lane_audit():
 # Exhaustive single-row mask graph, including wrong class/action outputs.
 checked=wrong=0
 for h in (4,8,16):
  B=64*h
  for p in (2,3,5,7,11,13,17,19):
   for kind in ('I','D','T','Z'):
    for w in range(h):
     U=w+1;Zp=U if p>2 else 0;V=U+(p-2)*Zp
     assert V==(p-1)*U and max(U,V)<B
     I=int(kind=='I');D=int(kind=='D')
     UI=V*I;UD=V*D
     assert U&((B-1)*int(p>2))==Zp
     assert V&((B-1)*I)==UI and V&((B-1)*D)==UD
     assert UI+UD<=V
     for bad in (UI+1,UD+1,Zp+1):assert bad>0;wrong+=1
     assert V&((B-1)*I)!=UI+1
     assert V&((B-1)*D)!=UD+1
     assert U&((B-1)*int(p>2))!=Zp+1
     checked+=1
 return dict(single_row_factor_graphs=checked,wrong_selected_outputs_rejected=wrong)


def verify():
 fixtures=[(TABLE,PRIMES),((('I',0,1),),PRIMES[:3]),((('D',2,0,1),),PRIMES[:3]),
  ((('T',1,1,2),('I',0,2)),PRIMES[:3]),((('I',2,1),),PRIMES[:3])]
 records=[];audits=[]
 for i,(table,primes) in enumerate(fixtures):
  packets={f:build(table,f,primes) for f in FORMS}
  for f,p in packets.items():closure(p);records.append(dict(fixture=i,form=f,ledger=ledger(p)))
  audits.append(dict(raw=raw_audit(packets['raw'],32,941000+i),
   scale=ps.identity_audit(packets['scaled'],24,942000+i),fields=fields.audit(packets['projected'],24,943000+i),
   ordinary_units=units.audit(packets['units']['normalized_parent'],24,944000+i),
   normalized_units=units.audit(packets['units'],24,945000+i),
   index=coupled.audit(packets['coupled']['coupled_parent'],24,946000+i),
   coupled=coupled.audit(packets['coupled'],24,947000+i),
   shared=[shared_audit(packets[f],24,948000+100*i+j) for j,f in enumerate(FORMS)]))
 packet=build();source,out=polynomial_source(packet);old=parent.build()
 assert packet['table']==old['table'] and packet['primes']==old['primes'] and packet['edges']==old['edges']
 return dict(theorem='Complete ordinary-input universal prime-payload compiler with factored prime/action masks.',
  default_ledger=ledger(packet),default_table=TABLE,default_primes=PRIMES,edges=packet['edges'],
  exceptional_primes=packet['classes'],joined_lanes=len(packet['edges'])+len(packet['classes'])+5,
  parent_ledger=ledger(old),literal_operation_saving=ledger(old)['product']['operations']-len(source),
  ledgers=records,audits=audits,paths=path_audit(),factor_cells=factor_cell_audit(),typed_lanes=typed_lane_audit(),
  inherited_prefix=parent.loader_no_wrap_audit(),inherited_residue_map=parent.residue_audit(),
  source=source,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
  source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest(),
  scope='One positive program parameter at3^e and ordinary input x. Exact accepted-outer semantics with fresh native extensions; no same-all-tuple polynomial identity with674.')


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(path.read_text())==result
 print(json.dumps({k:result[k] for k in ('default_ledger','literal_operation_saving','paths','factor_cells','typed_lanes')},indent=2))
