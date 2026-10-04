#!/usr/bin/env python3
"""All-input observer polarity plus literal compressed-program transport binding."""
if not __debug__:raise RuntimeError('Assertions required')
import array,hashlib,itertools,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ca'))
from physical_program import row_at
ca_raw=(ROOT/'ca/fixed_ca_cell.json').read_bytes();ca=json.loads(ca_raw)
program_raw=(ROOT/'ca/physical_program.json').read_bytes();p=json.loads(program_raw)
tab=(ROOT/'ca/radius_half_11_table_le.bin').read_bytes();table=array.array('H');table.frombytes(tab)
if sys.byteorder!='little':table.byteswap()
full=json.loads((ROOT/'ca/complete_table_verification.json').read_text())
assert full['circuit_sha256']==hashlib.sha256(ca_raw).hexdigest()
assert full['radius_half_complete_table_le_sha256']==hashlib.sha256(tab).hexdigest()
assert ca['halt_wire']==885 and ca['nand_gates'][861]==[884,884]
obs_index=next(i for i,n in enumerate(p['nodes'])if n.get('purpose')=='halt_observer_copy')
node=p['nodes'][obs_index-1];assert node=={'type':'COPY','m':910,'i':885}
start=p['prefix_rows'][obs_index-1];stop=p['prefix_rows'][obs_index]
assert stop==p['observer_row_index']==601515562 and stop-start==8137
# Independent eager expansion of only this small transport node.
XOR=[('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0)]
def shifted(rows,i):return[(k,j+i)for k,j in rows]
SWAP=[('DUP',0),('DUP',2)]+shifted(XOR,1)+[('DUP',1)]+XOR+shifted(XOR,1)
ops=[]
def emit_word(kind,i,width):
 if kind=='DUP':
  ops.extend(('MOVE_RIGHT',j)for j in range(width-1,i,-1));ops.append(('DUP',i));return width+1
 ops.append(('NAND',i));ops.extend(('MOVE_LEFT',j)for j in range(i+1,width-1));return width-1
width=emit_word('DUP',885,910)
for i in range(886,910):
 for kind,j in SWAP:width=emit_word(kind,i+j,width)
 assert width==911
assert len(ops)==8137
for j,op in enumerate(ops):assert row_at(p,start+j)==op
assert row_at(p,stop)==('DUP',910)
# Prove arbitrary unused-column contents cannot affect the result.
initialized=set(range(885,910))
for kind,i in ops:
 read=[i,i+1]if kind=='NAND'else[i+1]if kind=='MOVE_LEFT'else[i]
 assert all(j in initialized for j in read),(kind,i)
 initialized.update([i,i+1])
# Complete expected input bitplanes from the separately verified independent table.
N=2048**2;mask=(1<<N)-1;planes=[bytearray(N//8)for _ in range(11)];hb=bytearray(N//8)
for i,value in enumerate(table):
 v=value
 while v:
  k=(v&-v).bit_length()-1;planes[k][i>>3]|=1<<(i&7);v&=v-1
 if value==21:hb[i>>3]|=1<<(i&7)
fullf=[int.from_bytes(v,'little')for v in planes];fullh=int.from_bytes(hb,'little');cases=[]
for s0,s1 in itertools.product([0,1],repeat=2):
 f=[int.from_bytes(bytes(v[:256])*2048,'little')for v in planes]if s1 else fullf
 h=int.from_bytes(bytes(hb[:256])*2048,'little')if s1 else fullh
 phi=[mask if s1 else 0]+f+f+[mask if s0 and not s1 else 0]
 columns={885:h}|{886+i:mask^v for i,v in enumerate(phi)}
 for kind,i in ops:
  if kind=='NAND':a,b=mask^(columns[i]&columns[i+1]),0
  elif kind=='DUP':a=b=columns[i]
  elif kind=='MOVE_LEFT':a,b=columns[i+1],0
  else:a,b=0,columns[i]
  columns[i]=a;columns[i+1]=b
 assert columns[910]==h
 cases.append({'s0':s0,'s1':s1,'all_state_pairs':N,'observer_input_is_uncomplemented_h':True})
result={'status':'PASS_OBSERVER_PHYSICAL_INPUT_POLARITY_ALL_16777216_ASSIGNMENTS',
 'DAG_sha256':hashlib.sha256(ca_raw).hexdigest(),'program_sha256':hashlib.sha256(program_raw).hexdigest(),
 'DAG_halt_wire_index':885,'DAG_halt_gate_zero_based_index':861,'DAG_halt_gate_NAND_inputs':[884,884],
 'DAG_halt_wire_is_uncomplemented':'h=[f((1-s1)xL,xR)=21], proved by the separate complete-table comparison on all2^24 assignments',
 'transport_node':node,'transport_start_row':start,'transport_rows':len(ops),'observer_row':stop,'observer_physical_input_column':910,
 'all_transport_rows_match_independent_eager_expansion':True,'initial_unused_columns_never_read':True,'cases':cases,
 'local_write_branch':'The physical pair-DUP writes its first output exactly when its left input is1, as checked in all literal pair-DUP histories. No NOT footer lies between this transported h and the observer.',
 'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(ROOT/'atlas/observer_polarity_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'halt_wire':885,'transport_rows':8137,'observer_row':stop,'physical_column':910}))
