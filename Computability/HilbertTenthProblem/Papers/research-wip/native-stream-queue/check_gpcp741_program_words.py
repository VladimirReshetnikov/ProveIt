"""Literal existing program-frame check; no native Pell fixture."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json
import gpcp_program_frame741 as m
import gpcp_sparse_tm_compiler as sparse
p=m.build();codes=p['binary_prefix_code'];count=0
assert sparse.code_map(p['code_variant'])==codes
for q in (2,3):
 h=2;productions={(1,i):((i%q)+1,2) for i in range(1,q+1)}
 values,prefix,suffix=sparse.program_parameters(q,h,productions,q,q-1,p['code_variant'])
 image=m.transform_program(p,values)
 for x in range(1,32):
  for pad in (0,2):
   n=max(2,x.bit_length()+pad);bits=bin(x)[2:].zfill(n);Q=1<<(64*n);J=(Q-1)//((1<<64)-1)
   z=sum(((x>>j)&1)<<(64*j) for j in range(n))
   word=tuple(prefix)+sum((tuple(p['block_words'][int(bit)]) for bit in bits),())+tuple(suffix)
   literal=sparse.prefix.sentinel(word,codes)
   old=values['program_suffix_scale']*(values['program_prefix']*Q+p['block_values'][0]*J+(p['block_values'][1]-p['block_values'][0])*z)+values['program_suffix_value']
   new=image[m.NEW_PROGRAM[0]]*J+image[m.NEW_PROGRAM[1]]*z+image[m.NEW_PROGRAM[2]]
   assert literal==old==new
   count+=1
out=dict(status='PASS',literal_fixed_program_prefix_encoded_words=count,source_sha256=m.hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest(),scope='Actual existing program recipe and prefix-code words only; no native Pell witnesses.')
if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--write',action='store_true');args=a.parse_args()
 path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(out,indent=2)+'\n')
 else:assert json.loads(path.read_text())==out
 print(out)
