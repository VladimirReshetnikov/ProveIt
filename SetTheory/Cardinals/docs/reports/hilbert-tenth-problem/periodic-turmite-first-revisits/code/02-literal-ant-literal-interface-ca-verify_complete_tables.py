#!/usr/bin/env python3
"""Independent complete 32-state/radius-half tables and bit-parallel DAG proof.
No compiler module is imported. All 2^24 input assignments are checked exactly.
"""
if not __debug__:raise RuntimeError('Assertions required')
import array,collections,hashlib,itertools,json,pathlib,sys,time
ROOT=pathlib.Path(__file__).resolve().parent
raw=(ROOT/'fixed_ca_cell.json').read_bytes();dag=json.loads(raw);tm=json.loads((ROOT/'u15_table.json').read_text())
qnames='ABCDEFGHIJKLMNO';table=[]
# An independently structured lookup, with explicit center-head and arrival cases.
for left,center,right in itertools.product(range(32),repeat=3):
 if center>1:
  transition=tm[qnames[(center//2)-1]+str(center&1)]
  out=center if transition is None else transition[0]
 else:
  out=center
  arrivals=[]
  for cell,d in[(left,'R'),(right,'L')]:
   if cell>1:
    tr=tm[qnames[(cell//2)-1]+str(cell&1)]
    if tr is not None and tr[1]==d:arrivals.append(2*(qnames.index(tr[2])+1)+center)
  if arrivals:out=arrivals[0]
 table.append(out)
assert len(table)==32768 and table[0]==0
assert all(table[(l*32+21)*32+r]==21 for l,r in itertools.product(range(32),repeat=2))
(ROOT/'radius_one_32_table.bin').write_bytes(bytes(table))
def pair(a,b):return 0 if a==b==0 else 1024+32*a+b
N=2048*2048;f=array.array('H',[0])*N
for a,b in itertools.product(range(32),repeat=2):f[a*2048+b]=pair(a,b)
for a,b,c in itertools.product(range(32),repeat=3):f[pair(a,b)*2048+pair(b,c)]=table[(a*32+b)*32+c]
if sys.byteorder!='little':f.byteswap()
fb=f.tobytes();(ROOT/'radius_half_11_table_le.bin').write_bytes(fb)
if sys.byteorder!='little':f.byteswap()
# All f table entries not explicitly assigned above are the total invalid-case0.
# Expected bitplanes are constructed directly from this independent dense table.
plane_bytes=[bytearray(N//8)for _ in range(11)];hbytes=bytearray(N//8)
for i,v in enumerate(f):
 while v:
  bit=(v&-v).bit_length()-1;plane_bytes[bit][i>>3]|=1<<(i&7);v&=v-1
 if f[i]==21:hbytes[i>>3]|=1<<(i&7)
expected=[int.from_bytes(b,'little')for b in plane_bytes];eh=int.from_bytes(hbytes,'little')
mask=(1<<N)-1
inputs=[]
for bit in range(22):
 if bit<3:bs=bytes([0xaa if bit==0 else 0xcc if bit==1 else 0xf0])*(N//8)
 else:
  run=1<<(bit-3);block=b'\0'*run+b'\xff'*run;bs=block*((N//8)//len(block))
 inputs.append(int.from_bytes(bs,'little'))
retain=dag['complemented_phi_outputs']+dag['f_outputs']+[dag['halt_wire']]
uses=collections.Counter(x for row in dag['nand_gates']for x in row);uses.update(retain)
records=[]
for s0,s1 in itertools.product([0,1],repeat=2):
 env={i:mask^inputs[11+i]for i in range(11)}
 env[11]=mask if s0==0 else 0;env[12]=mask if s1==0 else 0
 env.update({13+i:mask^inputs[i]for i in range(11)})
 remaining=uses.copy();peak=len(env);start=time.perf_counter()
 for k,(a,b)in enumerate(dag['nand_gates'],24):
  assert 0<=a<k and 0<=b<k
  env[k]=mask^(env[a]&env[b])
  for port in[a,b]:
   remaining[port]-=1
   if remaining[port]==0:del env[port]
  peak=max(peak,len(env))
 if s1:
  ef=[int.from_bytes(bytes(p[:256])*2048,'little')for p in plane_bytes]
  h=int.from_bytes(bytes(hbytes[:256])*2048,'little')
 else:ef=expected;h=eh
 want=[mask if s1 else 0]+ef+ef+[mask if s0 and not s1 else 0]
 assert all(env[p]==(mask^v)for p,v in zip(dag['complemented_phi_outputs'],want))
 assert all(env[p]==v for p,v in zip(dag['f_outputs'],ef))
 assert env[dag['halt_wire']]==h
 records.append({'s0':s0,'s1':s1,'state_pair_assignments':N,'peak_live_bitplanes':peak,'exact':True})
result={'status':'PASS_EXACT_ALL_16777216_BOOLEAN_CELL_INPUTS','circuit_sha256':hashlib.sha256(raw).hexdigest(),
 'radius_one_32_table_sha256':hashlib.sha256(bytes(table)).hexdigest(),'radius_half_complete_table_le_sha256':hashlib.sha256(fb).hexdigest(),
 'states':32,'halt_code':21,'pair_encoding_bits':11,'primary_triples':32768,'complete_radius_half_pairs':N,
 'complete_phi_assignments':4*N,'bit_parallel_cases':records,'NAND_gates':len(dag['nand_gates']),
 'scope':'Exact Boolean specification check, separate from physical ant atlas construction. U15 arbitrary-program input compiler not supplied.',
 'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(ROOT/'complete_table_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k]for k in['status','states','halt_code','NAND_gates','complete_phi_assignments']}))
