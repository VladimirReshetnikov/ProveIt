"""A 21-instruction universal counter compiler with computed fields and units.

The source pays register-based control codes, actual chronological transport,
strict range completion and all native field projections. The default is the
primary strongly universal U21 contraction, with one program parameter.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import prod
from pathlib import Path
import random

import korec_packed_counter_compiler as parent

t=parent.t;ps=parent.ps;fields=parent.fields;units=parent.units;coupled=parent.coupled
execute=parent.execute

# Delete the U22 restore instruction9; instruction8 becomes a pure test.
def contract_table():
 answer=[]
 for q,row in enumerate(parent.TABLE):
  if q==9:continue
  op,r,*targets=row
  if q==8:op='T';targets=[10,0]
  answer.append(tuple([op,r]+[v-1 if v>=10 else v for v in targets]))
 return tuple(answer)

TABLE=contract_table()
TUNED=(1,2,2,1,1,2,1,2,3,1,3,4,1,5,1,2,2,3,1,2,2)


def normalize(table,registers):
 assert type(registers) is int and registers>=3 and table
 table=tuple(tuple(row) for row in table)
 for row in table:
  assert row[0] in ('I','D','T') and len(row)==(3 if row[0]=='I' else 4)
  assert type(row[1]) is int and 0<=row[1]<registers
  assert all(type(v) is int and 0<=v<=len(table) for v in row[2:])
 return table

def raw(table=TABLE,registers=8,lambdas=None):
 table=normalize(table,registers)
 g=t.Gates();o=g.emit
 summ=lambda terms,label:g.sum(terms,label) if terms else 0
 edges=[]
 for q,row in enumerate(table):
  op,r,*targets=row
  for idx,dest in enumerate(targets):edges.append((q,dest,op if op=='I' else (('P' if op=='T' else 'D') if idx==0 else 'Z'),r))
 K=len(edges);m=len(table);c=2
 counts=[0]*registers; codes=[]
 for row in table:
  counts[row[1]]+=1;codes.append((row[1],counts[row[1]]))
 if lambdas is None and table==TABLE and registers==8:lambdas=TUNED
 if lambdas is not None:
  assert len(lambdas)==m and lambdas[0]==1
  assert all(type(v) is int and v>0 for v in lambdas)
  for reg in range(registers):assert sorted(lambdas[q] for q,row in enumerate(table) if row[1]==reg)==list(range(1,counts[reg]+1))
  codes=[(row[1],lam) for row,lam in zip(table,lambdas)]
 margin=0
 while 6+2*margin<=max(counts) or (1<<(5+2*margin).bit_length())<=max(counts)+2:margin+=1
 E=[o('-',f'edge{i}_hat',1,'edge') for i in range(K)]
 J=summ(E,'partition');W=o('-','counter_word_hat',1,'counter_word');Y=o('-','final_counter_hat',1,'final_counter')
 e=o('-','program_hat',1,'program');half=summ(['program_hat','input','height_slack'],'half_height');half=o('+',half,margin,'minimum_height');D=o('+',half,half,'counter_radix')
 powers=[1,D]
 for j in range(2,registers+1):powers.append(o('*',powers[j//2],powers[(j+1)//2],'D'+str(j)))
 B=o('*',c,powers[registers],'time_radix');Bm=o('-',B,1,'time_radix_minus_one')
 P=o('+',o('*',Bm,J,'scale_minus_one'),1,'scale')
 maskbase=o('*',o('-',half,1,'counter_half_minus_one'),summ(powers[:registers],'counter_repunit'),'counter_digit_mask')
 rm=o('*',maskbase,J,'range_mask')
 action={}
 for op in ('I','D','Z'):
  grouped=[summ([E[i] for i,v in enumerate(edges) if v[3]==r and (v[2]==op or v[2]=='P' and op in ('I','D'))],op+str(r)) for r in range(registers)]
  action[op]=summ([o('*',w,a,op+'_weighted') for w,a in zip(powers,grouped)],op+'_sum')
 zm=o('*',o('-',D,1,'counter_radix_minus_one'),action['Z'],'zero_mask') if action['Z']!=0 else 0
 initial=o('+',o('*',e,D,'initial_program'),o('*','input',powers[2],'initial_input'),'initial')
 left=o('+',o('*',B,o('+',W,action['I'],'after_counters'),'next_counters'),initial,'counter_left')
 right=summ([W,action['D'],o('*',P,Y,'final_counters')],'counter_right')
 def linear(coefficients):
  terms=[(e,c) for e,c in zip(E,coefficients) if c]
  if not terms:return 0
  if min(coefficients)<0:return summ([o('*',e,c,'signed_coefficient') for e,c in terms],'signed_sum')
  original=list(g.source);cache=dict(g.cache)
  direct=summ([o('*',e,c,'coefficient') for e,c in terms],'linear_sum')
  ds,dc=list(g.source),dict(g.cache)
  g.source=original;g.cache=cache
  running=0;parts=[]
  for i in range(max(coefficients),0,-1):
   running=o('+',running,summ([e for e,c in terms if c==i],'coefficient_group'),'coefficient_tail');parts.append(running)
  prefix=summ(parts,'weighted_sum')
  if len(ds)<=len(g.source):g.source=ds;g.cache=dc;return direct
  return prefix
 current=summ([action['I'],action['D'],action['Z']],'current_base')
 correction=[];next_terms=[]
 for reg in range(registers):
  corr=linear([codes[v[0]][1]-(2 if v[2]=='P' else 1) if codes[v[0]][0]==reg else 0 for v in edges])
  correction.append(o('*',powers[reg],corr,'current_correction'))
  word=linear([codes[v[1]][1] if v[1]<m and codes[v[1]][0]==reg else 0 for v in edges])
  next_terms.append(o('*',powers[reg],word,'target_weight'))
 current=o('+',current,summ(correction,'all_corrections'),'current_control')
 following=summ(next_terms,'following_control')
 initial_control=o('*',powers[codes[0][0]],codes[0][1],'initial_control')
 cl=o('+',o('*',B,following,'control_left'),initial_control,'control_initial');cr=current
 bound=summ(['counter_word_hat','global_slack'],'global_bound')
 def powersum(n):
  if n==1:return P,1
  power,series=powersum(n//2)
  series=o('*',series,o('+',power,1,'repeat_one'),'repeat_double')
  power=o('*',power,power,'repeat_square')
  if n%2:series=o('+',series,power,'repeat_odd');power=o('*',power,P,'repeat_power')
  return power,series
 PK,RK=powersum(K)
 ep=g.pack(E,P,'edge_pack')
 wp=o('*',PK,W,'counter_pack')
 az=o('+',ep,wp,'Z')
 ah=o('+',az,o('*',P,wp,'second_counter_pack'),'H')
 am=o('+',o('*',J,RK,'repeated_J'),o('*',PK,o('+',rm,o('*',P,zm,'zero_lane'),'counter_M'),'counter_M_shift'),'M')
 exp=1
 scale=P
 while exp<K+2:scale=o('*',scale,scale,'scale_power');exp*=2
 scale=o('*',B,scale,'native_scale')
 ns,np,_=t.native.source('and64_prescribed');p='native__';name=lambda x:p+x if isinstance(x,str) else x
 source=g.source+[(p+'q','*',16,scale),(p+'scaled_A','*',16,ah),(p+'padded_A','+',p+'scaled_A',12),(p+'scaled_B','*',16,am),(p+'padded_B','+',p+'scaled_B',10),(p+'scaled_Z','*',16,az),(p+'F3','+',p+'scaled_Z',8)]+[(name(n),op,name(a),name(b)) for n,op,a,b in ns[7:]]
 aux=[f'edge{i}_hat' for i in range(K)]+['counter_word_hat','final_counter_hat','height_slack','global_slack']+[name(v) for v in t.native.domains('and64_prescribed')[1]]
 packet=ps.metadata(dict(source=source,comparisons=[(bound,rm),(left,right),(cl,cr)]+[(name(a),name(b)) for a,b in np],parameters=['program_hat','input'],auxiliaries=aux,interfaces=dict(D=D,B=B,J=J,P=P,W=W,Y=Y,rm=rm,zm=zm,ah=ah,am=am,az=az,scale=scale),table=table,edges=edges,c=c,registers=registers,scale_exponent=exp,form='raw',codes=codes,minimum_half_margin=margin,outer_pairs=[(bound,rm),(left,right),(cl,cr)]))
 ps.checked_source(source,packet['parameters'],aux)
 return packet


def project_ports(old):
 """Exact graph projection; positivity uses this host's proved range margin."""
 assert old.get('native_coupled_linear') and not old.get('counter_computed_ports')
 p=old['core_prefix'];n=lambda x:p+x
 rows={v:(op,a,b) for v,op,a,b in old['source']}
 expected={n('input_A'):('+',n('F1'),n('F3')),n('input_B'):('+',n('F2'),n('F3')),
  n('shared_sum02'):('+',n('F0'),n('F2')),n('bs_Q'):('+',n('shared_sum02'),n('input_A')),
  n('bs_q'):('-',n('q'),n('bs_Q')),
  n('norm_unit_product2'):('*',n('norm_unit_product1'),n('bs_q'))}
 assert all(rows.get(v)==r for v,r in expected.items())
 pairs=[(n('input_A'),n('padded_A')),(n('input_B'),n('padded_B'))]
 assert all(old['comparisons'].count(pair)==1 for pair in pairs)
 deleted=set(expected)
 for v in (n('shared_sum02'),n('bs_Q'),n('bs_q')):
  assert {w for w,_,a,b in old['source'] if v in (a,b)}<=deleted
 for v in (n('F0'),n('F1'),n('F2')):
  assert v in old['auxiliaries']
  assert not any(v in pair for pair in old['comparisons'])
 assert not deleted & units.register_leaves(old.get('interfaces',{}))
 aliases={n('input_A'):n('padded_A'),n('input_B'):n('padded_B'),n('norm_unit_product2'):n('norm_unit_product1')}
 alias=lambda v:aliases.get(v,v)
 source=[(v,op,alias(a),alias(b)) for v,op,a,b in old['source'] if v not in deleted]
 source += [(n('F1'),'-',n('padded_A'),n('F3')),(n('F2'),'-',n('padded_B'),n('F3')),
  (n('free_00'),'-',n('q'),n('padded_A')),(n('free_00b'),'-',n('free_00'),n('F2')),
  (n('F0'),'-',n('free_00b'),1)]
 aux=[v for v in old['auxiliaries'] if v not in {n('F0'),n('F1'),n('F2')}]
 source=ps.sort_source(source,old['parameters']+aux)
 packet=ps.metadata(dict(old,source=source,auxiliaries=aux,
  comparisons=[(alias(a),alias(b)) for a,b in old['comparisons'] if (a,b) not in pairs],
  unit_factors=[v for v in old['unit_factors'] if v!=n('bs_q')],
  counter_computed_ports=True,port_parent=old,port_deleted_rows=sorted(deleted),
  port_removed_comparisons=pairs,form='fields'))
 ps.checked_source(source,packet['parameters'],aux)
 assert packet['operations']==old['operations']-1 and packet['multiplications']==old['multiplications']-1
 assert packet['equations']==old['equations']-2 and packet['witnesses']==old['witnesses']-3
 return packet


def outer_units(old,which=(0,1,2)):
 assert old.get('counter_computed_ports') and not old.get('counter_outer_units')
 assert tuple(which) in ((0,),(0,1,2))
 assert old['comparisons'][:-1]==old['outer_pairs']
 source=list(old['source']);factors=list(old['unit_factors']);last=old['unit_register']
 for i in which:
  a,b=old['outer_pairs'][i];factor='counter_outer_factor'+str(i)
  source.append((factor,'-',b,a))
  if i:
   plus=factor+'_one';source.append((plus,'+',factor,1));factor=plus
  factors.append(factor);new='counter_outer_product'+str(i)
  source.append((new,'*',last,factor));last=new
 result=ps.metadata(dict(old,source=source,
  comparisons=[pair for i,pair in enumerate(old['outer_pairs']) if i not in which]+[(last,1)],
  unit_register=last,unit_factors=factors,counter_outer_units=True,
  outer_unit_parent=old,outer_unit_indices=list(which),form='units' if len(which)==3 else 'range_unit'))
 ps.checked_source(source,result['parameters'],result['auxiliaries'])
 return result


def build(table=TABLE,form='units',registers=8,lambdas=None):
 assert form in ('raw','coupled','fields','range_unit','units')
 packet=raw(table,registers,lambdas)
 if form=='raw':return packet
 packet=ps.rewrite(packet,'native__');packet=fields.rewrite(packet,prefix='native__')
 packet=units.rewrite(packet,normalized=True);packet=coupled.rewrite(packet)
 packet=dict(packet,form='coupled')
 if form=='coupled':return packet
 packet=project_ports(packet)
 if form=='fields':return packet
 return outer_units(packet,(0,) if form=='range_unit' else (0,1,2))


def polynomial_source(packet,*,sum_of_squares=False):
 if not packet.get('native_norm_units'):return t.polynomial_source(packet)
 if len(packet['comparisons'])>1:return units.polynomial_source(packet,sum_of_squares=sum_of_squares)
 assert packet['comparisons']==[(packet['unit_register'],1)]
 source=list(packet['source'])+ [('counter_final','-',packet['unit_register'],1)]
 if sum_of_squares:source.append(('counter_final_square','*','counter_final','counter_final'))
 return source,'counter_final_square' if sum_of_squares else 'counter_final'


def degree_bound(packet,*,sum_of_squares=False):
 if not packet.get('native_norm_units'):return dict(degree_upper_bound=ps.degree_bound(packet),exact_degree_claimed=False)
 # Reuse the guarded literal main-norm cancellation. A dummy constant residual
 # supplies maximum0 only to the degree routine; no such row is emitted.
 probe=packet if len(packet['comparisons'])>1 else dict(packet,comparisons=[(0,0)]+packet['comparisons'])
 return units.degree_bound(probe,sum_of_squares=sum_of_squares)


def ledger(packet):
 result=dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')})
 for sos in (False,True):
  source,out=polynomial_source(packet,sum_of_squares=sos);counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
  result['SOS' if sos else 'product']=dict(operations=len(source),multiplications=counts['M'],
   additions_subtractions=counts['A'],output=out,**degree_bound(packet,sum_of_squares=sos))
 return result


def closure(packet):
 for sos in (False,True):
  source,out=polynomial_source(packet,sum_of_squares=sos);rows={v:(a,b) for v,_,a,b in source};seen=set()
  def visit(v):
   if not isinstance(v,str) or v not in rows or v in seen:return
   seen.add(v)
   for w in rows[v]:visit(w)
  visit(out)
  assert seen==set(rows),set(rows)-seen
 return len(source)


def direct_outer(packet,v):
 """Independent formulas, without consulting any emitted register."""
 half=v['program_hat']+v['input']+v['height_slack']+packet['minimum_half_margin'];D=2*half
 B=2*D**packet['registers'];E=[v[f'edge{i}_hat']-1 for i in range(len(packet['edges']))]
 J=sum(E);P=(B-1)*J+1;W=v['counter_word_hat']-1;Y=v['final_counter_hat']-1
 action={a:sum(E[i]*D**row[3] for i,row in enumerate(packet['edges'])
  if row[2]==a or row[2]=='P' and a in ('I','D')) for a in ('I','D','Z')}
 rm=(half-1)*sum(D**j for j in range(packet['registers']))*J;zm=(D-1)*action['Z']
 pack=lambda seq:sum(c*P**j for j,c in enumerate(seq))
 H,M,A=pack(E+[W,W]),pack([J]*len(E)+[rm,zm]),pack(E+[W,0])
 Q=B*P**packet['scale_exponent'];initial=(v['program_hat']-1)*D+v['input']*D**2
 code=lambda q:0 if q==len(packet['table']) else packet['codes'][q][1]*D**packet['codes'][q][0]
 current=sum(e*code(row[0]) for e,row in zip(E,packet['edges']))
 following=sum(e*code(row[1]) for e,row in zip(E,packet['edges']))
 rr=[v['counter_word_hat']+v['global_slack']-rm,
     B*(W+action['I'])+initial-W-action['D']-P*Y,
     B*following+code(0)-current]
 return dict(D=D,B=B,J=J,P=P,W=W,Y=Y,rm=rm,zm=zm,ah=H,am=M,az=A,scale=Q),rr


def run(table,program,input_value,registers=8,limit=80):
 table=normalize(table,registers);assert program>=0 and input_value>0
 q=0;v=[0]*registers;v[1:3]=[program,input_value];configs=[(q,tuple(v))];chosen=[]
 for _ in range(limit):
  if q==len(table):break
  op,r,*targets=table[q];branch=0 if op=='I' or v[r]>0 else 1
  if op=='I':v[r]+=1
  elif op=='D' and branch==0:v[r]-=1
  chosen.append((q,branch));q=targets[branch];configs.append((q,tuple(v)))
 return configs,chosen


def pack_history(packet,configs,chosen,program,input_value):
 assert chosen and configs[-1][0]==len(packet['table']) and len(configs)==len(chosen)+1
 margin=packet['minimum_half_margin'];half=1
 while half<=max([program+1+input_value+margin]+[v+2 for _,r in configs for v in r]):half*=2
 D=2*half;B=2*D**packet['registers'];P=B**len(chosen);J=(P-1)//(B-1)
 pack=lambda xs:sum(a*B**i for i,a in enumerate(xs))
 indices={(q,b):i for i,(q,b) in enumerate((q,b) for q,row in enumerate(packet['table']) for b in range(len(row)-2))}
 selected=[indices[c] for c in chosen]
 values={f'edge{i}_hat':1+pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))}
 rows=[]
 for (_,vec),edge in zip(configs,selected):
  vec=list(vec);_,_,op,r=packet['edges'][edge]
  if op in ('D','P'):vec[r]-=1
  assert min(vec)>=0
  rows.append(sum(v*D**j for j,v in enumerate(vec)))
 W=pack(rows);Y=sum(v*D**j for j,v in enumerate(configs[-1][1]));rm=(half-1)*sum(D**j for j in range(packet['registers']))*J
 shift=int(packet.get('counter_outer_units',False))
 values.update(program_hat=program+1,input=input_value,height_slack=half-program-1-input_value-margin,
  counter_word_hat=W+1,final_counter_hat=Y+1,global_slack=rm-W-1-shift)
 assert min(values.values())>0
 return values


def contraction_audit():
 rng=random.Random(98236);cases=steps=0
 for q,row in enumerate(TABLE):
  for j in range(40):
   before=[rng.randrange(6) for _ in range(8)];before[row[1]]=j%4
   old=list(before);state=q if q<9 else q+1
   op,r,*targets=parent.TABLE[state]
   branch=0 if op=='I' or old[r]>0 else 1
   if op=='I':old[r]+=1
   elif branch==0:old[r]-=1
   state=targets[branch];steps+=1
   if q==8 and branch==0:
    assert state==9 and parent.TABLE[state]==('I',6,10)
    old[6]+=1;state=10;steps+=1
   actual=list(before);op,r,*targets=row;branch=0 if op=='I' or actual[r]>0 else 1
   if op=='I':actual[r]+=1
   elif op=='D' and branch==0:actual[r]-=1
   dest=targets[branch];old_dest=dest if dest<9 else dest+1
   assert actual==old and state==old_dest;cases+=1
 return dict(U22_to_U21_checkpoints=cases,U22_steps=steps,table_instructions=len(TABLE),
  instruction_kinds=dict(Counter(row[0] for row in TABLE)),inherited_U32_audit=parent.contraction_audit())


def raw_audit(packet,cases,seed):
 rng=random.Random(seed);source,out=polynomial_source(packet);ns,np,_=t.native.source('and64_prescribed')
 at=lambda e,v:e[v] if isinstance(v,str) else v
 for j in range(cases):
  values={v:rng.randrange(1,4) if j<cases//2 else rng.randrange(-2,3)
          for v in packet['parameters']+packet['auxiliaries']}
  oracle,rr=direct_outer(packet,values);env=execute(source,values)
  assert all(at(env,v)==oracle[k] for k,v in packet['interfaces'].items())
  native=dict(P=oracle['scale'],Hhat=oracle['ah']+1,Mhat=oracle['am']+1,Zhat=oracle['az']+1,
   **{v:values['native__'+v] for v in t.native.domains('and64_prescribed')[1]})
  ne=execute(ns,native);residuals=rr+[at(ne,a)-at(ne,b) for a,b in np]
  assert residuals==[at(env,a)-at(env,b) for a,b in packet['comparisons']]
  assert env[out]==sum(r*r for r in residuals)
 return dict(complete_raw_identities=cases,signed=cases//2)


def projection_audit(packet,cases,seed):
 assert packet.get('counter_computed_ports') and not packet.get('counter_outer_units')
 rng=random.Random(seed);old=packet['port_parent'];p=packet['core_prefix']
 at=lambda e,v:e[v] if isinstance(v,str) else v
 negatives=0
 for j in range(cases):
  values={v:rng.randrange(1,5) if j<cases//2 else rng.randrange(-3,4)
          for v in packet['parameters']+packet['auxiliaries']}
  env=execute(packet['source'],values)
  lifted=dict(values,**{p+f:env[p+f] for f in ('F0','F1','F2')})
  negatives+=int(any(lifted[p+f]<=0 for f in ('F0','F1','F2')))
  before=execute(old['source'],lifted)
  assert before[p+'bs_q']==1
  for key in set(env)&set(before):assert env[key]==before[key],key
  for pair in packet['port_removed_comparisons']:assert at(before,pair[0])==at(before,pair[1])
  for sos in (False,True):
   source,out=polynomial_source(packet,sum_of_squares=sos);os,oo=polynomial_source(old,sum_of_squares=sos)
   assert execute(source,values)[out]==execute(os,lifted)[oo]
 return dict(complete_port_graph_identities=cases,both_finalizers=2*cases,signed=cases//2,
             nonpositive_off_zero_field_lifts=negatives)


def outer_unit_audit(packet,cases,seed):
 rng=random.Random(seed);old=packet['outer_unit_parent'];which=packet['outer_unit_indices']
 at=lambda e,v:e[v] if isinstance(v,str) else v
 for j in range(cases):
  values={v:rng.randrange(1,5) if j<cases//2 else rng.randrange(-3,4)
          for v in packet['parameters']+packet['auxiliaries']}
  lifted=dict(values,global_slack=values['global_slack']+1)
  oldenv=execute(old['source'],lifted);newenv=execute(packet['source'],values)
  residuals=[at(oldenv,a)-at(oldenv,b) for a,b in old['outer_pairs']]
  newf=[1-residuals[i] for i in which]
  assert newf==[newenv[f] for f in packet['unit_factors'][len(old['unit_factors']):]]
  assert all(oldenv[f]==newenv[f] for f in old['unit_factors'])
  native=prod(oldenv[f] for f in old['unit_factors']);factor=prod(newf)
  rs=[residuals[i] for i in range(3) if i not in which]
  source,out=polynomial_source(packet);actual=execute(source,values)[out]
  assert actual==native*factor*(1+sum(r*r for r in rs))-1
  os,oo=polynomial_source(old);previous=execute(os,lifted)[oo]
  assert actual==factor*(previous+1)-native*factor*sum(residuals[i]**2 for i in which)-1
  ss,so=polynomial_source(packet,sum_of_squares=True)
  assert execute(ss,values)[so]==sum(r*r for r in rs)+(native*factor-1)**2
 return dict(complete_unit_corrections=cases,both_finalizers=2*cases,signed=cases//2)


def history_audit():
 rng=random.Random(910582);contexts=[(TABLE,8)]
 for size in range(1,9):
  for repeat in range(8):
   k=3+repeat%4
   table=[]
   for q in range(size):
    op=rng.choice(('I','D','T'));r=rng.randrange(k)
    table.append(tuple([op,r]+[rng.randrange(size+1) for _ in range(1 if op=='I' else 2)]))
   contexts.append((tuple(table),k))
 counts=Counter();rows=0
 for table,k in contexts:
  packet=build(table,registers=k)
  outer=[row for row in packet['source'] if not row[0].startswith('native__') and not row[0].startswith('counter_outer_')]
  for program in range(3):
   for x in range(1,5):
    configs,chosen=run(table,program,x,k)
    if configs[-1][0]!=len(table):continue
    values=pack_history(packet,configs,chosen,program,x);env=execute(outer,values);v,rr=direct_outer(packet,values)
    assert rr==[-1,0,0] and v['ah']&v['am']==v['az']
    assert all((env[name] if isinstance(name,str) else name)==v[key] for key,name in packet['interfaces'].items())
    assert v['ah']>=v['az'] and v['am']>v['az'] and v['scale']>v['ah']+v['am']-v['az']
    D=v['D'];assert max(lam for _,lam in packet['codes'])<D-2
    for q,branch in chosen:counts[table[q][0]+str(branch)]+=1
    counts['halted_histories']+=1;rows+=len(chosen)
 return dict(tables=len(contexts),chronological_rows=rows,counts=dict(counts),
  scope='Literal halted counter runs, outer equations and joined AND only; no full Pell tuples materialized.')


def low_digit_audit():
 cases=0
 for D in (8,16,32,64):
  h=D//2
  for initial_reg in range(5):
   for max_lambda in range(1,D-2):
    start=1 if initial_reg==0 else 0
    codes={0}|set(range(1,max_lambda+1))
    assert (start-2)%D not in codes
    assert D-2 not in range(h+1)
    cases+=1
 # Exact popcount obstruction on positive fields with prescribed residues.
 masks=0
 for q in (16,32,64,128):
  for f1 in range(4,q,16):
   for f2 in range(2,q-f1,16):
    for f3 in range(8,q-f1-f2,16):
     f0=q-1-f1-f2-f3
     if f0<=0:continue
     r=f0+q*f1+q*q*f2+q**3*f3
     assert r%16==1 and r.bit_count()>=(q-1).bit_count()
     assert (r-2).bit_count()>=q.bit_length()+1
     masks+=1
 return dict(negative_transport_low_digit_cases=cases,checksum_one_negative_index_exclusions=masks)


def range_margin_audit():
 rng=random.Random(731948);cases=negative=notdyadic=0
 for k in (3,4,8):
  packet=build(registers=k,table=(('T',2,1,1),))
  for _ in range(64):
   E=[rng.randrange(4),rng.randrange(4)]
   if not sum(E):E[0]=1
   half=rng.randrange(4,20);D=2*half;B=2*D**k;J=sum(E)
   rm=(half-1)*sum(D**i for i in range(k))*J
   W=rng.randrange(rm-2)
   for sign in (-1,1):
    gamma=rm-W-1-sign
    v=dict(program_hat=1,input=1,height_slack=half-2,global_slack=gamma,
           counter_word_hat=W+1,final_counter_hat=1,edge0_hat=E[0]+1,edge1_hat=E[1]+1)
    z,rr=direct_outer(packet,v)
    assert rr[0]==-sign and min(v.values())>0
    assert z['ah']>=z['az'] and z['am']>z['az']
    assert z['scale']>z['ah']+z['am']-z['az']
    assert all(0<=z[a]<z['P']**4 for a in ('ah','am','az'))
    cases+=1;negative+=sign<0;notdyadic+=bool(D&(D-1))
 return dict(weak_range_pretyping_cases=cases,negative_range_units=negative,nondyadic_radices=notdyadic)


def guard_audit():
 p=build(form='coupled');rejected=0
 for key in ('input_A','bs_q','norm_unit_product2'):
  source=[(v,op,b,a) if v=='native__'+key else (v,op,a,b) for v,op,a,b in p['source']]
  try:project_ports(dict(p,source=source))
  except AssertionError:rejected+=1
  else:raise AssertionError('altered private source accepted')
 for which in ((1,),(1,2),()):
  try:outer_units(build(form='fields'),which)
  except AssertionError:rejected+=1
  else:raise AssertionError('unsupported unit specialization accepted')
 return dict(rejected_mutations=rejected)


def verify():
 fixtures=[(TABLE,8),((('I',0,1),),3),((('D',2,0,1),),3),
  ((('T',2,1,2),('I',3,2)),4),((('I',0,1),('T',0,2,3),('D',0,3,0)),3),
  (tuple(('I',0,q+1) for q in range(12)),3)]
 ledgers=[];audits=[]
 for i,(table,k) in enumerate(fixtures):
  forms={f:build(table,f,k) for f in ('raw','coupled','fields','range_unit','units')}
  for form,packet in forms.items():closure(packet);ledgers.append(dict(fixture=i,form=form,ledger=ledger(packet)))
  c=forms['coupled'];norm=c['coupled_parent']['index_parent']
  projected=norm['normalized_parent']['unit_parent']
  scaled=projected['computed_parent']
  audits.append(dict(raw=raw_audit(forms['raw'],24,961000+i),
   scale=ps.identity_audit(scaled,12,961100+i),fields=fields.audit(projected,12,961200+i),
   native_units=units.audit(norm['normalized_parent'],12,961300+i),
   normalized=units.audit(norm,12,961400+i),index=coupled.audit(c['coupled_parent'],12,961500+i),
   coupled=coupled.audit(c,12,961600+i),ports=projection_audit(forms['fields'],32,961700+i),
   range_units=outer_unit_audit(forms['range_unit'],32,961800+i),
   all_units=outer_unit_audit(forms['units'],32,961900+i)))
 default=build();source,out=polynomial_source(default)
 return dict(theorem='Exact positive fixed-program halting; default literal Korec U21 is strongly universal with one program parameter and ordinary positive input.',
  default_ledger=ledger(default),default_table=TABLE,default_lambdas=TUNED,
  contraction=contraction_audit(),ledgers=ledgers,audits=audits,histories=history_audit(),
  sign_checks=low_digit_audit(),pretyping=range_margin_audit(),guards=guard_audit(),default_source=source,default_output=out,
  default_parameters=default['parameters'],default_auxiliaries=default['auxiliaries'],
  default_source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(path.read_text())==result
 print(json.dumps({k:result[k] for k in ('default_ledger','contraction','histories','sign_checks','guards')},indent=2))
