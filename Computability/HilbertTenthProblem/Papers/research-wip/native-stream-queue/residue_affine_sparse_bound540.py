"""Prune dominated pretyping bounds in the complete sparse universal compiler.

Raw rewriting precedes native normalization. Every fixed form has an exact
integer slack identity and a positive-zero bijection with its551 parent.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
from math import prod
import random
import residue_affine_sparse_factored as parent

t=parent.t;ps=parent.ps;fields=parent.fields;units=parent.units;coupled=parent.coupled
execute=parent.execute;at=parent.at;TABLE=parent.TABLE;PRIMES=parent.PRIMES
payload_run=parent.payload_run
FORMS=parent.FORMS;polynomial_source=parent.polynomial_source;ledger=parent.ledger
closure=parent.closure


def leaves(value):
 if isinstance(value,str):return {value}
 if isinstance(value,dict):return set().union(set(),*(leaves(v) for v in value.values()))
 if isinstance(value,(list,tuple)):return set().union(set(),*(leaves(v) for v in value))
 return set()


def rewrite(old):
 assert old['form']=='raw' and not old.get('dominated_sparse_bound')
 expected=parent.raw(old['table'],old['primes'],old['shared'])
 assert old==expected,'caller must be the full canonical raw sparse551 packet'
 k=len(old['classes']);g=k+2;J=old['interfaces']['J'];V=old['interfaces']['V']
 terms=[J,V,'quotient_hat','remainder_hat','complement_hat']+[f'product{i}_hat' for i in range(g)]+['global_slack']
 rows={n:(op,a,b) for n,op,a,b in old['source']}
 name=old['comparisons'][0][0];back=[]
 for i in range(len(terms)-1,1,-1):
  op,left,right=rows[name];assert op=='+' and right==terms[i]
  back.append(name);name=left
 assert rows[name]==('+',terms[0],terms[1]);back.append(name);chain=list(reversed(back))
 assert len(chain)==k+7
 for i,name in enumerate(chain[:-1]):
  assert {n for n,_,a,b in old['source'] if name in (a,b)}=={chain[i+1]}
 assert {n for n,_,a,b in old['source'] if 'global_slack' in (a,b)}=={chain[-1]}
 assert not set(chain)&leaves(old['interfaces'])
 assert not set(chain[:-1])&leaves(old['comparisons'])
 assert all(old['comparisons'][i][0] not in set(chain) for i in range(1,len(old['comparisons'])))
 replacement={chain[-3]:('+',V,f'product{k}_hat'),chain[-2]:('+',chain[-3],f'product{k+1}_hat'),chain[-1]:('+',chain[-2],'global_slack')}
 removed=set(chain[:-3])
 source=[(n,*replacement[n]) if n in replacement else (n,op,a,b) for n,op,a,b in old['source'] if n not in removed]
 packet=ps.metadata(dict(old,source=source,dominated_sparse_bound=True,sparse_bound_parent=old,
  bound_chain=chain,removed_bound_registers=sorted(removed),bound_operation_saving=k+4,
  bound_definition='V+increment_selected_hat+decrement_selected_hat+global_slack=P'))
 assert packet['operations']==old['operations']-k-4
 assert packet['multiplications']==old['multiplications']
 assert packet['auxiliaries']==old['auxiliaries'] and packet['comparisons']==old['comparisons']
 ps.checked_source(source,packet['parameters'],packet['auxiliaries'])
 return packet


def build(table=TABLE,form='coupled',primes=PRIMES,shared=True):
 assert form in FORMS
 packet=rewrite(parent.raw(table,primes,shared))
 if form!='raw':packet=ps.rewrite(packet,'native__')
 if form in ('projected','units','coupled'):packet=fields.rewrite(packet,prefix='native__')
 if form in ('units','coupled'):packet=units.rewrite(packet,normalized=True)
 if form=='coupled':packet=coupled.rewrite(packet)
 return dict(packet,form=form)


def dropped_sum(packet,values):
 J=sum(values[f'edge{i}_hat']-1 for i in range(len(packet['edges'])))
 return J+sum(values[n] for n in ('quotient_hat','remainder_hat','complement_hat'))+sum(values[f'product{i}_hat'] for i in range(len(packet['classes'])))


def lift_to_parent(packet,values):
 answer=dict(values);answer['global_slack']-=dropped_sum(packet,values);return answer


def project_from_parent(packet,values):
 answer=dict(values);answer['global_slack']+=dropped_sum(packet,values);return answer


def direct_outer(packet,values):
 ports,residuals=parent.direct_outer(packet,values)
 residuals[0]-=dropped_sum(packet,values)
 return ports,residuals


def pack_path(packet,states,selected,input_value):
 return project_from_parent(packet,parent.pack_path(packet,states,selected,input_value))


def identity_audit(packet,cases,seed):
 old=parent.build(packet['table'],packet['form'],packet['primes'],packet['shared'])
 finals=[False,True] if packet.get('native_norm_units') else [False]
 rng=random.Random(seed);identities=negative=positive=0
 for case in range(cases):
  values={n:rng.randrange(1,6) if case<cases//2 else rng.randrange(-3,4) for n in packet['parameters']+packet['auxiliaries']}
  if case<cases//4:values['global_slack']=1
  lifted=lift_to_parent(packet,values)
  assert project_from_parent(packet,lifted)==values
  if case<cases//2 and lifted['global_slack']<=0:negative+=1
  for sos in finals:
   bs,bo=units.polynomial_source(old,sum_of_squares=sos) if old.get('native_norm_units') else polynomial_source(old)
   ns,no=units.polynomial_source(packet,sum_of_squares=sos) if packet.get('native_norm_units') else polynomial_source(packet)
   a=execute(bs,lifted);b=execute(ns,values)
   assert a[bo]==b[no]
   assert all(a[name]==b[name] for name,_,_,_ in old['source'] if name not in set(packet['bound_chain'][:-1]))
   assert a[packet['bound_chain'][-2]]==b[packet['bound_chain'][-2]]+dropped_sum(packet,values)
   assert a[packet['bound_chain'][-3]]==b[packet['bound_chain'][-3]]+dropped_sum(packet,values)
   assert [at(a,l)-at(a,r) for l,r in old['comparisons']]==[at(b,l)-at(b,r) for l,r in packet['comparisons']]
   identities+=1
  original={n:rng.randrange(1,7) for n in packet['parameters']+packet['auxiliaries']}
  projected=project_from_parent(packet,original)
  assert min(projected.values())>0 and lift_to_parent(packet,projected)==original;positive+=1
 return dict(complete_source_residual_finalizer_identities=identities,signed_assignments=cases//2,
  positive_parent_projections=positive,nonpositive_offzero_parent_slacks=negative)


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
 return dict(complete_raw_oracle_identities=cases,signed=cases//2)

def pretyping_audit():
 rng=random.Random(540902);cases=nondyadic=negative_old=0
 fixtures=[(TABLE,PRIMES),((('I',2,1),),PRIMES[:3]),((('D',2,0,1),),PRIMES[:3]),
  ((('T',1,1,2),('I',0,2)),PRIMES[:3])]
 for table,primes in fixtures:
  packet=build(table,'raw',primes);k=len(packet['classes']);m=len(packet['edges'])
  for trial in range(128):
   v={n:1 for n in packet['parameters']+packet['auxiliaries']}
   v.update(program=rng.randrange(1,5),input=rng.randrange(1,5),final_payload=rng.randrange(1,5),height_slack=rng.randrange(1,5))
   ee=[rng.randrange(4) for _ in range(m)]
   if not sum(ee):ee[0]=1
   v.update({f'edge{i}_hat':e+1 for i,e in enumerate(ee)})
   h=sum(v[n] for n in ('program','input','final_payload','height_slack'));B=packet['radix_multiplier']*h
   J=sum(ee);P=(B-1)*J+1
   zp=[rng.randrange(3) for _ in range(k)]
   offset=J+sum((p-2)*z for p,z in zip(packet['classes'],zp))
   assert offset<=P-3
   W=P-3-offset if trial%4==0 else rng.randrange(P-2-offset)
   V=W+offset;left=P-V-3
   YI=rng.randrange(left+1);YD=rng.randrange(left-YI+1);beta=P-V-YI-YD-2
   rem=sum(e*(row[3]-2) for e,row in zip(ee,packet['edges']) if row[2]=='Z')
   R=(0,rem,rng.randrange(rem+1))[trial%3];S=rem-R
   v.update(quotient_hat=W+1,remainder_hat=R+1,complement_hat=S+1,global_slack=beta)
   v.update({f'product{i}_hat':z+1 for i,z in enumerate(zp+[YI,YD])})
   ports,rr=direct_outer(packet,v)
   assert rr[:2]==[0,0] and min(v.values())>0
   assert 0<=J<=ports['U']<=V<P and 0<=W<P
   assert all(0<=z<P for z in zp+[YI,YD,R,S])
   assert R+S<=(max(primes)-2)*J<(B-1)*J
   assert max(ports['joined_H'],ports['joined_M'],ports['joined_Z'])<P**(m+k+5)<ports['native_scale']
   outer=[row for row in packet['source'] if not row[0].startswith('native__')]
   env=execute(outer,v)
   assert all(at(env,name)==ports[key] for key,name in packet['interfaces'].items())
   negative_old+=lift_to_parent(packet,v)['global_slack']<=0
   nondyadic+=bool(P&(P-1));cases+=1
 return dict(untyped_positive_bound_cases=cases,nondyadic_scales=nondyadic,nonpositive_old_slacks_before_typing=negative_old)


def typed_inverse_audit():
 rng=random.Random(540903);cases=0
 for table,primes in [(TABLE,PRIMES),((('I',2,1),),PRIMES[:3]),((('D',0,0,1),),PRIMES[:3])]:
  packet=build(table,'raw',primes);k=len(packet['classes']);g=k+2
  for duration in range(1,6):
   for h in (4,8,16):
    for _ in range(12):
     B=packet['radix_multiplier']*h;P=B**duration;J=(P-1)//(B-1)
     selected=[rng.randrange(len(packet['edges'])) for _ in range(duration)]
     w=[rng.randrange(h) for _ in selected];r=[];s=[]
     for edge in selected:
      row=packet['edges'][edge];total=row[3]-2 if row[2]=='Z' else 0
      # Range typing also requires both remainders<h; choose h larger if needed.
      if total>2*(h-1):break
      low=max(0,total-h+1);high=min(h-1,total);rr=rng.randrange(low,high+1)
      r.append(rr);s.append(total-rr)
     if len(r)!=duration:continue
     pack=lambda values:sum(x*B**i for i,x in enumerate(values))
     ee=[pack([int(e==i) for e in selected]) for i in range(len(packet['edges']))]
     zp=[pack([ww+1 if packet['edges'][e][3]==p else 0 for ww,e in zip(w,selected)]) for p in packet['classes']]
     vv=[(packet['edges'][e][3]-1)*(ww+1) for ww,e in zip(w,selected)]
     yy=[pack([v if packet['edges'][e][2]==kind else 0 for v,e in zip(vv,selected)]) for kind in ('I','D')]
     W,R,S,V=map(pack,(w,r,s,vv));U=W+J
     beta_new=P-V-yy[0]-yy[1]-2
     beta_old=beta_new-(J+W+R+S+sum(zp)+k+3)
     floor=(B-2*max(primes)*h-max(primes)+1)*J-g-2
     assert beta_old>=floor>=2*max(primes)+3 and beta_new>0
     assert sum(zp)<=U and sum(yy)<=V
     assert U+V<=max(primes)*h*J and R+S<=(max(primes)-2)*J
     cases+=1
 return dict(arbitrary_typed_row_words=cases,scope='Typing/remainder assumptions only; control/payload chronology is not presumed for the inverse bound.')


def guards_audit():
 good=parent.raw();bad=[]
 for field in ('parameters','auxiliaries'):
  v=copy.deepcopy(good);v[field]=v[field][1:];bad.append(v)
 for name in (good['comparisons'][0][0],good['interfaces']['V'],good['interfaces']['P']):
  v=copy.deepcopy(good);v['source']=[(n,'-',a,b) if n==name else (n,op,a,b) for n,op,a,b in v['source']];bad.append(v)
 for name in ('global_slack',good['comparisons'][0][0]):
  v=copy.deepcopy(good);v['source'].append(('extra','+',name,1));bad.append(v)
 v=copy.deepcopy(good);v['interfaces']['extra']={'nested':[None,good['comparisons'][0][0]]};bad.append(v)
 v=copy.deepcopy(good);v['comparisons']=v['comparisons'][:1]+v['comparisons'][2:];bad.append(v)
 v=copy.deepcopy(good);v['classes']=list(reversed(v['classes']));bad.append(v)
 for v in bad:
  try:rewrite(v)
  except (AssertionError,KeyError,TypeError):pass
  else:raise AssertionError('incompatible parent accepted')
 try:rewrite(build(form='raw'))
 except AssertionError:pass
 else:raise AssertionError('duplicate rewrite accepted')
 return dict(incompatible_callers_rejected=len(bad)+1)


def path_audit():
 rng=random.Random(540904);tables=[(TABLE,PRIMES)]
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


def verify():
 fixtures=[(TABLE,PRIMES),((('I',0,1),),PRIMES[:3]),((('D',2,0,1),),PRIMES[:3]),
  ((('T',1,1,2),('I',0,2)),PRIMES[:3]),((('I',2,1),),PRIMES[:3])]
 records=[];audits=[]
 for i,(table,primes) in enumerate(fixtures):
  packets={f:build(table,f,primes) for f in FORMS}
  for j,(f,p) in enumerate(packets.items()):
   closure(p);old=parent.build(table,f,primes);l=ledger(p);bl=ledger(old)
   for name in ('product','SOS','polynomial'):
    if name in l:
     assert l[name]['operations']==bl[name]['operations']-len(p['classes'])-4
     assert l[name]['degree_upper_bound']==bl[name]['degree_upper_bound']
   records.append(dict(fixture=i,form=f,ledger=l,identity=identity_audit(p,32,541000+20*i+j)))
  audits.append(dict(raw=raw_audit(packets['raw'],32,542000+i),
   scale=ps.identity_audit(packets['scaled'],24,543000+i),fields=fields.audit(packets['projected'],24,544000+i),
   ordinary_units=units.audit(packets['units']['normalized_parent'],24,545000+i),
   normalized_units=units.audit(packets['units'],24,546000+i),
   index=coupled.audit(packets['coupled']['coupled_parent'],24,547000+i),coupled=coupled.audit(packets['coupled'],24,548000+i)))
 packet=build();source,out=polynomial_source(packet)
 assert len(source)==540
 return dict(theorem='Exact complete positive-zero slack bijection after removing dominated sparse pretyping bounds.',
  default_ledger=ledger(packet),parent_default_ledger=ledger(parent.build()),literal_operation_saving=11,
  default_table=TABLE,default_primes=PRIMES,removed_terms=['J','quotient_hat','remainder_hat','complement_hat']+[f'product{i}_hat' for i in range(len(packet['classes']))],
  ledgers=records,audits=audits,pretyping=pretyping_audit(),typed_inverse=typed_inverse_audit(),paths=path_audit(),guards=guards_audit(),
  source=source,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
  source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest(),
  scope='Same fixed U21 and positive program E=3^e with ordinary input x; unchanged chronology/native forms. The affine inverse can be negative off zero but is positive at every positive zero.')


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(path.read_text())==result
 print(json.dumps({k:result[k] for k in ('default_ledger','pretyping','typed_inverse','paths','guards')},indent=2))
