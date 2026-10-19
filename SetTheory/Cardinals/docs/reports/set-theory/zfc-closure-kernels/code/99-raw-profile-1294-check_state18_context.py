"""Exact local literal premises for state18_context_addendum.tex.

The pulse checks are universal over tape cells outside the declared local
window: any access to an unspecified cell is rejected by the checker. The
paper's complete increment proof additionally uses inherited induction
contracts. This executable does not claim a proof-kernel endpoint.
"""
from pathlib import Path
import json,sys,hashlib

HERE=Path(__file__).resolve().parent
default=HERE.parent/'runtime-evidence/reference/machine/zfc245_old.tm'
path=Path(sys.argv[1])if len(sys.argv)>1 else default
table={}
for line in path.read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),-1 if d=='L'else 1,int(t))

rows={(18,0):(0,-1,27),(27,1):(1,1,39),(39,0):(0,1,57),
      (27,0):(0,-1,32),(32,1):(1,1,46),(46,0):(0,1,39),
      (18,1):(0,1,28),(28,1):(1,1,28),(57,1):(0,1,73)}
for key,row in rows.items():assert table[key]==row,(key,table[key],row)

def pulse(known,steps):
 original=known.copy();q=18;h=0;trace=[]
 for i in range(steps):
  assert h in known,('read outside declared local window',h)
  bit=known[h];trace.append({'state':q,'head':h,'read':bit})
  w,d,q=table[q,bit];known[h]=w;h+=d
 assert(q,h)==(57,1),(q,h)
 assert known==original,(known,original)
 return trace+[{'state':q,'head':h}]

out={'status':'PASS_LITERAL_LOCAL_PREMISES','table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
     'rows_checked':len(rows),
     'ends1':{'known_cells':{-1:1,0:0},'literal_steps':3,'trace':pulse({-1:1,0:0},3)},
     'ends10_or_singleton0_with_marker':{'known_cells':{-2:1,-1:0,0:0},'literal_steps':5,'trace':pulse({-2:1,-1:0,0:0},5)},
     'one_pulse':{'write':0,'move':'R','target':28,'inherited_physical_register':6},
     'proof':'state18_context_addendum.tex','scope':'exact finite control reduction; all other tape cells unaccessed; inherited register and scanner induction contracts remain premises','proof_kernel_endpoint':False}
HERE.joinpath('state18-context-row-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
