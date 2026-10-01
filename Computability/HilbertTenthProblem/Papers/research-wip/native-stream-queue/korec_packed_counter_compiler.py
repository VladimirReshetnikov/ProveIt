"""One chronological counter word for a fixed finite register program.

The default is an explicit strongly universal Korec U22 contraction of U32.
Input register1 contains program_hat-1; register2 contains ordinary input.
No duration bound or existential input coding function is supplied for free.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import wang_b_packed_tape as t
import native_binary_positive_scale as ps
import native_binary_computed_fields as fields
import native_binary_norm_units as units
import native_binary_index_coupled_units as coupled
TABLE=(('D',1,1,2),('I',7,0),('I',6,3),('D',5,2,4),('D',6,5,3),('I',5,6),('D',7,7,8),('I',1,4),('D',6,9,0),('I',6,10),('D',4,0,11),('D',5,12,13),('D',5,14,15),('D',2,18,19),('D',5,16,17),('D',3,18,20),('I',4,11),('I',2,21),('D',4,0,22),('D',0,0,18),('I',0,0),('I',3,18))
def normalize(table,registers):
 assert isinstance(registers,int) and registers>=3 and table
 table=tuple(tuple(row) for row in table)
 for row in table:
  assert row[0] in ('I','D') and len(row)==(3 if row[0]=='I' else 4)
  assert isinstance(row[1],int) and 0<=row[1]<registers
  assert all(isinstance(v,int) and 0<=v<=len(table) for v in row[2:])
 return table

def build(table=TABLE, form='coupled', registers=8):
 assert form in ('raw','scaled','projected','units','coupled')
 table=normalize(table,registers)
 g=t.Gates();o=g.emit
 summ=lambda terms,label:g.sum(terms,label) if terms else 0
 edges=[]
 for q,row in enumerate(table):
  op,r,*targets=row
  for idx,dest in enumerate(targets):edges.append((q,dest,op if op=='I' else ('D' if idx==0 else 'Z'),r))
 K=len(edges);m=len(table);c=1<<(m+1).bit_length()
 E=[o('-',f'edge{i}_hat',1,'edge') for i in range(K)]
 J=summ(E,'partition');W=o('-','counter_word_hat',1,'counter_word');Y=o('-','final_counter_hat',1,'final_counter')
 e=o('-','program_hat',1,'program');half=summ(['program_hat','input','height_slack'],'half_height');D=o('+',half,half,'counter_radix')
 powers=[1,D]
 for j in range(2,registers+1):powers.append(o('*',powers[j//2],powers[(j+1)//2],'D'+str(j)))
 B=o('*',c,powers[registers],'time_radix');Bm=o('-',B,1,'time_radix_minus_one')
 P=o('+',o('*',Bm,J,'scale_minus_one'),1,'scale')
 maskbase=o('*',o('-',half,1,'counter_half_minus_one'),summ(powers[:registers],'counter_repunit'),'counter_digit_mask')
 rm=o('*',maskbase,J,'range_mask')
 action={}
 for op in ('I','D','Z'):
  grouped=[summ([E[i] for i,v in enumerate(edges) if v[2:]==(op,r)],op+str(r)) for r in range(registers)]
  action[op]=summ([o('*',w,a,op+'_weighted') for w,a in zip(powers,grouped)],op+'_sum')
 zm=o('*',o('-',D,1,'counter_radix_minus_one'),action['Z'],'zero_mask') if action['Z']!=0 else 0
 initial=o('+',o('*',e,D,'initial_program'),o('*','input',powers[2],'initial_input'),'initial')
 left=o('+',o('*',B,o('+',W,action['I'],'after_counters'),'next_counters'),initial,'counter_left')
 right=summ([W,action['D'],o('*',P,Y,'final_counters')],'counter_right')
 def weighted_state(column):
  groups=[0]+[summ([E[i] for i,v in enumerate(edges) if v[column]==q],'state_group') for q in range(1,m+1)]
  running=0; terms=[]
  for q in range(m,0,-1):
   running=o('+',running,groups[q],'state_suffix');terms.append(running)
  return summ(terms,'state_weight')
 current=weighted_state(0)
 following=weighted_state(1)
 cl=o('*',B,following,'control_left');cr=o('+',current,o('*',m,P,'halt'),'control_right')
 bound=summ([J,'counter_word_hat','global_slack'],'global_bound')
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
 packet=ps.metadata(dict(source=source,comparisons=[(bound,P),(left,right),(cl,cr)]+[(name(a),name(b)) for a,b in np],parameters=['program_hat','input'],auxiliaries=aux,interfaces=dict(D=D,B=B,J=J,P=P,W=W,Y=Y,rm=rm,zm=zm,ah=ah,am=am,az=az,scale=scale),table=table,edges=edges,c=c,registers=registers,scale_exponent=exp,form=form))
 ps.checked_source(source,packet['parameters'],aux)
 if form!='raw':packet=ps.rewrite(packet,p)
 if form in ('projected','units','coupled'):packet=fields.rewrite(packet,prefix=p)
 if form in ('units','coupled'):packet=units.rewrite(packet,normalized=True)
 if form=='coupled':packet=coupled.rewrite(packet)
 return packet


def polynomial_source(packet):
 return units.polynomial_source(packet) if packet.get('native_norm_units') else t.polynomial_source(packet)


def ledger(packet):
 return units.ledger(packet) if packet.get('native_norm_units') else t.ledger(packet)


execute=t.execute


def direct_outer(packet,values):
 """Independent scalar formulas; no emitted outer register is consulted."""
 v=values;half=v['program_hat']+v['input']+v['height_slack'];D=2*half
 B=packet['c']*D**packet['registers'];E=[v[f'edge{i}_hat']-1 for i in range(len(packet['edges']))]
 J=sum(E);P=(B-1)*J+1;W=v['counter_word_hat']-1;Y=v['final_counter_hat']-1
 action={a:sum(E[i]*D**row[3] for i,row in enumerate(packet['edges']) if row[2]==a) for a in ('I','D','Z')}
 rm=(half-1)*sum(D**j for j in range(packet['registers']))*J;zm=(D-1)*action['Z']
 pack=lambda seq:sum(c*P**j for j,c in enumerate(seq))
 joined=(pack(E+[W,W]),pack([J]*len(E)+[rm,zm]),pack(E+[W,0]))
 scale=B*P**packet['scale_exponent'];initial=(v['program_hat']-1)*D+v['input']*D**2
 current=sum(e*row[0] for e,row in zip(E,packet['edges']))
 following=sum(e*row[1] for e,row in zip(E,packet['edges']))
 rr=[J+v['counter_word_hat']+v['global_slack']-P,
     B*(W+action['I'])+initial-W-action['D']-P*Y,
     B*following-current-len(packet['table'])*P]
 return dict(D=D,B=B,J=J,P=P,W=W,Y=Y,rm=rm,zm=zm,ah=joined[0],am=joined[1],az=joined[2],scale=scale),rr


def run(table,program,input_value,registers=8,limit=200):
 """Literal register interpreter; returns complete configurations."""
 table=normalize(table,registers);assert program>=0 and input_value>0
 state=0;counters=[0]*registers;counters[1:3]=[program,input_value]
 configs=[(state,tuple(counters))];chosen=[]
 for _ in range(limit):
  if state==len(table):break
  op,r,*targets=table[state]
  branch=0 if op=='I' or counters[r]>0 else 1
  if op=='I':counters[r]+=1
  elif branch==0:counters[r]-=1
  chosen.append((state,branch));state=targets[branch]
  configs.append((state,tuple(counters)))
 return configs,chosen


def pack_history(packet,configs,chosen,program,input_value):
 """Positive outer coordinates for an actual finite halted computation.

 Native Pell auxiliaries are deliberately not materialized. Their existence
 is supplied by the proved native completion theorem, not by finite checks.
 """
 assert chosen and configs[-1][0]==len(packet['table']) and len(configs)==len(chosen)+1
 half=1
 while half<=max([program+1+input_value]+[v for _,r in configs for v in r]):half*=2
 D=2*half;B=packet['c']*D**packet['registers'];N=len(chosen);P=B**N;J=(P-1)//(B-1)
 pack=lambda xs:sum(a*B**i for i,a in enumerate(xs))
 edge_indices={(q,b):i for i,(q,b) in enumerate((q,b) for q,row in enumerate(packet['table']) for b in range(len(row)-2))}
 selected=[edge_indices[c] for c in chosen]
 values={f'edge{i}_hat':1+pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))}
 rows=[]
 for (_,counters),edge in zip(configs,selected):
  counters=list(counters);q,target,op,r=packet['edges'][edge]
  if op=='D':counters[r]-=1
  assert min(counters)>=0
  rows.append(sum(v*D**j for j,v in enumerate(counters)))
 W=pack(rows);Y=sum(v*D**j for j,v in enumerate(configs[-1][1]))
 values.update(program_hat=program+1,input=input_value,height_slack=half-program-1-input_value,
  counter_word_hat=W+1,final_counter_hat=Y+1,global_slack=P-J-W-1)
 assert min(values.values())>0
 return values


# Korec1996 Fig.1: test branches are positive then zero. State0 denotes halt.
U32={1:('T',1,2,6),2:('M',1,3),3:('I',7,1),4:('T',5,5,7),5:('M',5,6),
 6:('I',6,4),7:('T',6,8,4),8:('M',6,9),9:('I',5,10),10:('T',7,11,13),
 11:('M',7,12),12:('I',1,7),13:('T',6,14,1),14:('T',4,15,16),15:('M',4,1),
 16:('T',5,17,23),17:('M',5,18),18:('T',5,19,27),19:('M',5,20),20:('T',5,21,30),
 21:('M',5,22),22:('I',4,16),23:('T',2,24,25),24:('M',2,32),25:('T',0,26,32),
 26:('M',0,1),27:('T',3,28,29),28:('M',3,32),29:('I',0,1),30:('I',2,31),
 31:('I',3,32),32:('T',4,15,0)}
LABELS=(1,3,6,4,7,9,10,12,13,33,14,16,18,23,20,27,22,30,32,25,29,31,0)


def contraction_audit():
 rng=random.Random(910385);cases=steps=0
 for q,label in enumerate(LABELS[:-1]):
  if label==33:continue
  for repeat in range(32):
   registers=[rng.randrange(5) for _ in range(8)];registers[TABLE[q][1]]=repeat%4
   old=list(registers);oldstate=label
   # Stop at the next retained original control point after at least one step.
   while True:
    op,r,*targets=U32[oldstate]
    if op=='T':oldstate=targets[int(old[r]==0)]
    else:
     old[r]=old[r]+1 if op=='I' else max(0,old[r]-1);oldstate=targets[0]
    steps+=1
    if oldstate in LABELS:break
   new=list(registers);op,r,*targets=TABLE[q]
   if op=='I':new[r]+=1;newstate=targets[0]
   elif new[r]:new[r]-=1;newstate=targets[0]
   else:newstate=targets[1]
   if LABELS[newstate]==33:
    assert TABLE[newstate]==('I',6,10)
    new[6]+=1;newstate=10
   assert LABELS[newstate]==oldstate and new==old
   cases+=1
 return dict(original_Fig1_rows=32,compiled_instructions=22,checkpoint_cases=cases,original_steps=steps,
             q27_zero_target=29,internal_restore_label=33)


def raw_identity_audit(packet,cases,seed):
 rng=random.Random(seed);source,out=polynomial_source(packet);nsource,np,_=t.native.source('and64_prescribed')
 at=lambda e,v:e[v] if isinstance(v,str) else v
 for index in range(cases):
  values={v:rng.randrange(1,4) if index<cases//2 else rng.randrange(-2,3)
          for v in packet['parameters']+packet['auxiliaries']}
  oracle,rr=direct_outer(packet,values);env=execute(source,values)
  assert all(at(env,name)==oracle[key] for key,name in packet['interfaces'].items())
  nv=dict(P=oracle['scale'],Hhat=oracle['ah']+1,Mhat=oracle['am']+1,Zhat=oracle['az']+1,
          **{v:values['native__'+v] for v in t.native.domains('and64_prescribed')[1]})
  ne=execute(nsource,nv);expected=rr+[at(ne,a)-at(ne,b) for a,b in np]
  assert [at(env,a)-at(env,b) for a,b in packet['comparisons']]==expected
  assert env[out]==sum(r*r for r in expected)
 return dict(complete_raw_output_and_residual_identities=cases,signed_cases=cases//2)


def closure(packet):
 source,out=polynomial_source(packet);rows={n:(a,b) for n,_,a,b in source};seen=set()
 def visit(v):
  if not isinstance(v,str) or v not in rows or v in seen:return
  seen.add(v)
  for w in rows[v]:visit(w)
 visit(out)
 assert seen==set(rows)
 return len(source)


def history_audit():
 rng=random.Random(610587);contexts=[]
 # Include the actual universal table and varied partial computations that halt.
 contexts.append((TABLE,8))
 for size in range(1,9):
  for repeat in range(6):
   registers=3+repeat%4
   table=tuple(('I',rng.randrange(registers),rng.randrange(size+1)) if rng.randrange(2)
     else ('D',rng.randrange(registers),rng.randrange(size+1),rng.randrange(size+1)) for _ in range(size))
   contexts.append((table,registers))
 checked=rows=dec=zero=inc=0
 for table,registers in contexts:
  packet=build(table,'raw',registers)
  outer=[row for row in packet['source'] if not row[0].startswith('native__')]
  for program in range(3):
   for x in range(1,5):
    configs,selected=run(table,program,x,registers,limit=60)
    if configs[-1][0]!=len(table):continue
    values=pack_history(packet,configs,selected,program,x)
    actual=execute(outer,values);oracle,rr=direct_outer(packet,values)
    assert rr==[0,0,0] and oracle['ah']&oracle['am']==oracle['az']
    assert all(0<=oracle[v]<oracle['scale'] for v in ('ah','am','az'))
    assert all((actual[name] if isinstance(name,str) else name)==oracle[key] for key,name in packet['interfaces'].items())
    assert all(actual[a]==actual[b] for a,b in packet['comparisons'][:3])
    for q,branch in selected:
     action=table[q][0]
     if action=='I':inc+=1
     elif branch:zero+=1
     else:dec+=1
    checked+=1;rows+=len(selected)
 return dict(tables=len(contexts),positive_halted_histories=checked,chronological_rows=rows,
             increments=inc,positive_decrements=dec,zero_branches=zero,
             scope='Outer histories and joined AND only; no full Pell witnesses materialized.')


def adversarial_audit():
 # Each one-row forged edge preserves chronology and arithmetic counter transport.
 # Selecting zero on a nonzero register is excluded exactly by the zero AND lane.
 table=(('D',2,1,1),);packet=build(table,'raw',3);K=len(packet['edges'])
 checks=[]
 for x in range(1,9):
  half=16;D=2*half;B=packet['c']*D**3;P=B
  E=[0,1];W=x*D**2
  values=dict(program_hat=1,input=x,height_slack=half-1-x,counter_word_hat=W+1,
              final_counter_hat=W+1,global_slack=P-1-W-1,edge0_hat=1,edge1_hat=2)
  oracle,rr=direct_outer(packet,values)
  assert min(values.values())>0 and rr==[0,0,0] and oracle['ah']&oracle['am']!=oracle['az']
  checks.append('nonzero zero-branch')
 # A positive decrement at zero would require a negative post-decrement digit.
 # Borrowing from the next counter cannot pass its strict D/2 range lane.
 table=(('D',0,1,1),);packet=build(table,'raw',3)
 for x in range(1,9):
  half=16;D=2*half;B=packet['c']*D**3;P=B;W=x*D**2-1
  values=dict(program_hat=1,input=x,height_slack=half-1-x,counter_word_hat=W+1,
              final_counter_hat=W+1,global_slack=P-1-W-1,edge0_hat=2,edge1_hat=1)
  oracle,rr=direct_outer(packet,values)
  assert min(values.values())>0 and rr==[0,0,0] and oracle['ah']&oracle['am']!=oracle['az']
  checks.append('borrowed underflow')
 # Static balanced control admits disconnected cycles; chronological transport rejects them.
 table=(('I',0,2),('I',0,1));packet=build(table,'raw',3)
 # First row is the disconnected self-loop; final row is the genuine start-to-halt edge.
 half=16;D=2*half;B=packet['c']*D**3;P=B**2;W=D**2+(D**2+1)*B
 values=dict(program_hat=1,input=1,height_slack=14,counter_word_hat=W+1,final_counter_hat=D**2+3,
             global_slack=P-(B+1)-W-1,edge0_hat=B+1,edge1_hat=2)
 oracle,rr=direct_outer(packet,values)
 assert rr[:2]==[0,0] and rr[2]!=0 and oracle['ah']&oracle['am']==oracle['az']
 checks.append('disconnected control cycle')
 return dict(rejected_cases=len(checks),kinds=dict(Counter(checks)))


def verify():
 fixtures=[(TABLE,8),((('I',0,1),),3),((('D',2,0,1),),3),
           ((('I',3,1),('D',2,0,2)),4)]
 records=[];raws=[];rewrites=[]
 for index,(table,registers) in enumerate(fixtures):
  forms={form:build(table,form,registers) for form in ('raw','scaled','projected','units','coupled')}
  for form,packet in forms.items():
   closure(packet);records.append(dict(program=index,form=form,ledger=ledger(packet)))
  raws.append(raw_identity_audit(forms['raw'],32,618000+index))
  rewrites.append(dict(scale=ps.identity_audit(forms['scaled'],16,619000+index),
    fields=fields.audit(forms['projected'],16,620000+index),
    ordinary_units=units.audit(forms['units']['normalized_parent'],16,621000+index),
    normalized_units=units.audit(forms['units'],16,622000+index),
    index=coupled.audit(forms['coupled']['coupled_parent'],16,623000+index),
    coupled=coupled.audit(forms['coupled'],16,624000+index)))
 default=build();source,out=polynomial_source(default)
 return dict(theorem='Exact fixed-program halting with raw program/input; default Korec U22 is strongly universal.',
  default_ledger=ledger(default),default_table=TABLE,original_U32=U32,relabel=LABELS,
  original_contraction=contraction_audit(),ledgers=records,raw_identities=raws,rewrite_identities=rewrites,
  physical_histories=history_audit(),adversarial=adversarial_audit(),
  default_source=source,default_output=out,default_parameters=default['parameters'],
  default_auxiliaries=default['auxiliaries'],default_source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())


if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify()))
 receipt=Path(__file__).with_suffix('.json')
 if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(receipt.read_text())==result
 print(json.dumps({k:result[k] for k in ('default_ledger','original_contraction','physical_histories','adversarial')},indent=2))
