#!/usr/bin/env python3
"""Exact random-access adjacent-pair program; never expands its billions of rows.
Physical tile-level realization still requires the checked template atlas.
"""
if not __debug__:raise RuntimeError('Assertions required')
import bisect,collections,hashlib,itertools,json,pathlib,random
ROOT=pathlib.Path(__file__).resolve().parent
XOR=[('DUP',0),('DUP',2),('NAND',1),('DUP',1),('NAND',0),('NAND',1),('NAND',0)]
def shift(p,k):return[(t,i+k)for t,i in p]
SWAP=[('DUP',0),('DUP',2)]+shift(XOR,1)+[('DUP',1)]+shift(XOR,0)+shift(XOR,1)
def wordlen(op,m,i):return m-i if op=='DUP'else m-i-1
def swaplen(m,i):
 z=m;s=0
 for op,j in SWAP:s+=wordlen(op,z,i+j);z+=1 if op=='DUP'else-1
 assert z==m
 return s
SWAP_CONST=swaplen(2,0)-24*2
def copyswapprefix(m,i,t):
 assert 0<=t<=m-i-1
 return 24*(t*(m-i)-t*(t-1)//2)+SWAP_CONST*t

def length(n):
 t=n['type']
 if t=='ROW':return 1
 if t=='RANGE':return len(range(n['start'],n['stop'],n['step']))
 if t=='WORD':return wordlen(n['op'],n['m'],n['i'])
 if t=='SWAP':return 24*(n['m']-n['i'])+SWAP_CONST
 if t=='COPY':return n['m']-n['i']+copyswapprefix(n['m'],n['i'],n['m']-n['i']-1)
 if t=='GATE':return length({'type':'COPY','m':n['m'],'i':n['u']})+length({'type':'COPY','m':n['m']+1,'i':n['v']})+1
 raise ValueError(t)
def instruction(n,k):
 assert 0<=k<length(n)
 t=n['type']
 if t=='ROW':return n['op'],n['i']
 if t=='RANGE':return n['op'],n['start']+k*n['step']
 if t=='WORD':
  m,i,op=n['m'],n['i'],n['op']
  if op=='DUP':return('MOVE_RIGHT',m-1-k)if k<m-i-1 else('DUP',i)
  return('NAND',i)if k==0 else('MOVE_LEFT',i+k)
 if t=='SWAP':
  m=n['m'];i=n['i']
  for op,j in SWAP:
   node={'type':'WORD','op':op,'m':m,'i':i+j};L=length(node)
   if k<L:return instruction(node,k)
   k-=L;m+=1 if op=='DUP'else-1
  raise AssertionError()
 if t=='COPY':
  m,i=n['m'],n['i'];first={'type':'WORD','op':'DUP','m':m,'i':i};L=length(first)
  if k<L:return instruction(first,k)
  k-=L;low=0;high=m-i-1
  while low+1<high:
   mid=(low+high)//2
   if copyswapprefix(m,i,mid)<=k:low=mid
   else:high=mid
  return instruction({'type':'SWAP','m':m+1,'i':i+1+low},k-copyswapprefix(m,i,low))
 if t=='GATE':
  a={'type':'COPY','m':n['m'],'i':n['u']};b={'type':'COPY','m':n['m']+1,'i':n['v']}
  if k<length(a):return instruction(a,k)
  k-=length(a)
  if k<length(b):return instruction(b,k)
  return'NAND',n['m']
 raise ValueError(t)

def make_program():
 raw=(ROOT/'fixed_ca_cell.json').read_bytes();ca=json.loads(raw)
 nodes=[];B=40;W=24*B;K=W-2
 def add(node):
  if length(node):nodes.append(node)
 for j in range(24):add({'type':'RANGE','op':'MOVE_LEFT','start':j*B-1,'stop':j-1,'step':-1,'purpose':'gather_input'})
 for j,(u,v)in enumerate(ca['nand_gates']):add({'type':'GATE','m':24+j,'u':u,'v':v})
 width=24+len(ca['nand_gates']);base_output=width
 for port in ca['complemented_phi_outputs']+[ca['halt_wire']]:
  add({'type':'COPY','m':width,'i':port});width+=1
 observe_row=sum(map(length,nodes));observe_col=width-1
 add({'type':'ROW','op':'DUP','i':observe_col,'purpose':'halt_observer_copy'})
 for j in range(24):add({'type':'RANGE','op':'MOVE_LEFT','start':base_output+j-1,'stop':j-1,'step':-1,'purpose':'gather_outputs'})
 for j in reversed(range(24)):add({'type':'RANGE','op':'MOVE_RIGHT','start':j,'stop':j*B,'step':1,'purpose':'scatter_outputs'})
 prefix=[0]
 for n in nodes:prefix.append(prefix[-1]+length(n))
 return {'nodes':nodes,'prefix_rows':prefix,'program_rows':prefix[-1],'selected_slot_stride':B,'tile_slots':W,'active_columns':K,
  'storage_pitch':600,'instruction_row_height':400,'CA_macro_width':600*W,
  'CA_macro_height':400*(prefix[-1]+2),'rectangular_vertical_period':800*(prefix[-1]+2),
  'observer_row_index':observe_row,'observer_column_index':observe_col,
  'observer_local_head_state':[600+600*observe_col+102,400+400*observe_row+450,2],
  'initial_header_slot_entry':[600+600*(12*B),75,1],'fixed_start_local_head_state':[600+600*(12*B)+50,75,1],
  'maximum_live_compiler_word':width+6,'NAND_DAG_sha256':hashlib.sha256(raw).hexdigest()}
def row_at(program,k):
 assert 0<=k<program['program_rows']
 j=bisect.bisect_right(program['prefix_rows'],k)-1
 return instruction(program['nodes'][j],k-program['prefix_rows'][j])
def apply(word,op,i):
 assert 0<=i<len(word)-1
 p,q=word[i:i+2]
 word[i:i+2]={'NAND':[1-p*q,0],'DUP':[p,p],'MOVE_LEFT':[q,0],'MOVE_RIGHT':[0,p]}[op]
def expanded_word(word,op,i):
 if op=='DUP':word[i:i+1]=[word[i],word[i]]
 else:word[i:i+2]=[1-word[i]*word[i+1]]
def main():
 checks=0
 for m in range(2,8):
  for i in range(m-1):
   n={'type':'SWAP','m':m,'i':i};assert length(n)==swaplen(m,i)
   for word in itertools.product([0,1],repeat=m):
    physical=list(word)+[0]*8
    for k in range(length(n)):apply(physical,*instruction(n,k))
    expected=list(word);expected[i:i+2]=reversed(expected[i:i+2]);assert physical[:m]==expected;checks+=1
 for m in range(1,7):
  for i in range(m):
   n={'type':'COPY','m':m,'i':i}
   for word in itertools.product([0,1],repeat=m):
    physical=list(word)+[1]*8
    for k in range(length(n)):apply(physical,*instruction(n,k))
    assert physical[:m+1]==list(word)+[word[i]];checks+=1
 p=make_program();assert p['maximum_live_compiler_word']<=p['active_columns']
 # All node boundaries plus uniform pseudorandom exact-index queries.
 rng=random.Random(20261003);indices={0,p['program_rows']-1,p['observer_row_index']}
 for v in p['prefix_rows']:
  if v<p['program_rows']:indices.add(v)
  if v:indices.add(v-1)
 indices.update(rng.randrange(p['program_rows'])for _ in range(10000))
 for k in indices:
  op,i=row_at(p,k);assert op in['NAND','DUP','MOVE_LEFT','MOVE_RIGHT']and 0<=i<p['active_columns']-1
 assert row_at(p,p['observer_row_index'])==('DUP',p['observer_column_index'])
 p.update({'status':'PASS_EXACT_COMPRESSED_FIXED_CA_PAIR_PROGRAM','physical_atlas_complete':False,'small_exhaustive_semantic_checks':checks,'random_access_queries':len(indices),
  'swap_linear_constant':SWAP_CONST,'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
  'scope':'A concrete finite row program specified by exact arithmetic grammar and random-access decoder, not a dense expansion. Atlas assembly and marker routing remain separate obligations.'})
 (ROOT/'physical_program.json').write_text(json.dumps(p,indent=2)+'\n')
 print(json.dumps({k:p[k]for k in['status','program_rows','active_columns','CA_macro_width','CA_macro_height','observer_row_index','observer_column_index','maximum_live_compiler_word','small_exhaustive_semantic_checks']}))
if __name__=='__main__':main()
