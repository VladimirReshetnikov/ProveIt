"""Replay every compact outer box and reconstruct its exact partition."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib,time
from sharp_outer_bound import best_upper,S
root=Path(__file__).resolve().parent;path=root/'sharp_outer_certificate.json';data=json.loads(path.read_text());start=time.time()
def require(c,msg):
 if not c:raise ArithmeticError(msg)
leaves=[tuple(map(F,row[:6]))for row in data['cells']]
require(len(leaves)==len(set(leaves)),'duplicate cells')
dom=tuple(map(F,data['domain_t']+data['domain_theta_over_pi']))
require(dom==(F(3413848,10**7),F(3484140,10**7),F(153,1000),F(1,2)),'unexpected domain')
tl,th,ql,qh=dom;remaining=set(leaves)
todo=[(tl,th,ql,qh,F(1),F(3,2)),(tl,th,ql,qh,F(3,2),F(2))];nodes=0
while todo:
 box=todo.pop();nodes+=1;require(nodes<=2*len(leaves)+2,'partition tree mismatch')
 if box in remaining:remaining.remove(box);continue
 widths=[box[1]-box[0],box[3]-box[2],(box[5]-box[4])**2]
 axis=max(range(3),key=lambda i:widths[i]);i=2*axis;mid=(box[i]+box[i+1])/2
 a=list(box);b=list(box);a[i+1]=mid;b[i]=mid;todo.extend([tuple(a),tuple(b)])
require(not remaining,'unused partition leaves')
maximum=F(0)
for j,(box,row)in enumerate(zip(leaves,data['cells']),1):
 value=F(best_upper(box),S)
 require(value<F(999,1000),'outer cell not strict')
 require(value<=F(row[6]),'stored upper bound is not reproducible')
 maximum=max(maximum,value)
require(F(999,1000)<F(1999,2000)**2,'eta conversion')
out=dict(all_cells_passed=True,cells=len(leaves),partition_nodes=nodes,maximum_squared_upper=str(maximum),eta='1999/2000',certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),seconds=time.time()-start)
(root/'compact_outer_replay.json').write_text(json.dumps(out,indent=2)+'\n')
print('Compact outer replay passes',len(leaves),'cells with eta=1999/2000.')
