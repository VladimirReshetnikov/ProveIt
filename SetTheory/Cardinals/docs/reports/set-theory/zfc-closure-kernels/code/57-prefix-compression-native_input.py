from pathlib import Path
import hashlib
import json
import re
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
from repair_search import prepare, BASE, ROOT, audit

out=Path(__file__).resolve().parent
omit={8202,8203,8204,8358,8359,8360}
table,check,retained,usage,costs=prepare(omit)
prog=ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
text=prog.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',text)
cases=[]
def visit(q,prefix):
 for b,e in enumerate(nodes[q]):
  pc=prefix+str(b)
  op,*a=e.split()
  if op=='CN': visit(int(a[0]),pc);continue
  r=int(a[0]) if a else None
  for zero in ((True,False) if op=='CD' else (None,)):
   phys=audit.NEWPHYS[r] if op in ('CI','CD') else -1
   nxt=audit.successor(pc,op,r,zero)
   effect=0 if op=='CI' else 1 if op=='CD' and not zero else -1
   cases.append([len(cases),pc,phys if op=='CD' else -1,int(zero) if zero is not None else -1,nxt or '-',int(nxt is None),effect,phys if effect>=0 else -1,int(op=='CH')])
visit(0,'')
assert len(cases)==8391
with (out/'native_cases.txt').open('w') as f:
 for row in cases:
  i=row[0]
  if i not in omit:f.write(' '.join(map(str,row+[costs[i]]))+'\n')
with (out/'native_table.txt').open('w') as f:
 for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])):
  f.write(f'{q} {b} {w} {d} {t}\n')
with (out/'native_usage.txt').open('w') as f:
 for (q,b),indices in sorted(usage.items(),key=lambda x:(int(x[0][0]),x[0][1])):
  f.write(f'{q} {b} '+','.join(map(str,sorted(indices)))+'\n')
print('Native search input emitted with exact baseline cost and lookup sets.')
