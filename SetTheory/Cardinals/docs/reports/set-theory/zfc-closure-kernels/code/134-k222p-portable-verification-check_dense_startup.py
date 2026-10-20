#!/usr/bin/env python3
"""Independent dense-array simulation of the complete canonical blank startup.

No constructor, sparse simulator, runtime module or table parser is imported.
Window exhaustion is an error. Since the initial tape is zero everywhere and
every visited position remains in the window, comparison with its complete
nonzero support also proves equality on the infinite exterior.
"""
from pathlib import Path
import argparse,hashlib,json
PIN='3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476'
def need(c,m):
 if not c:raise ValueError(m)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sparse-bootstrap',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 raw=a.table.read_bytes();need(hashlib.sha256(raw).hexdigest()==PIN,'Unexpected canonical table')
 rows={};start=[]
 for line in raw.decode().splitlines():
  if line.startswith('#! start '):start.append(int(line.split()[-1]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b) not in rows and d in ('L','R'),'Bad row');rows[q,b]=(w,1 if d=='R' else -1,z)
 need(start==[0] and len(rows)==444,'Wrong convention')
 left=-8192;right=8191;tape=bytearray(right-left+1);head=0;q=0
 for tick in range(409835):
  need(q!=222,'Halt during initialization');need(left<=head<=right,'Dense window exhausted')
  w,d,q=rows[q,tape[head-left]];tape[head-left]=w;head+=d
 one_positions=[left+i for i,b in enumerate(tape) if b]
 sparse=json.loads(a.sparse_bootstrap.read_text())
 need(q==22 and head==-5 and sparse['steps']==409835 and sparse['head']==head and sparse['k_state']==84,'Wrong complete endpoint')
 need(one_positions==sparse['one_cells'] and len(one_positions)==351,'Dense/sparse complete tape mismatch')
 result=dict(status='INDEPENDENT_CANONICAL_DENSE_STARTUP_PASS',steps=409835,state=q,head=head,one_cells=len(one_positions),exact_sparse_endpoint_equal=True,table_sha256=PIN,finite_allocated_window=[left,right],window_exhaustion_is_error=True)
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
