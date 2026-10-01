"""Exact adaptive outer certificate with logarithmic spatial sharpening."""
from fractions import Fraction as F
from pathlib import Path
import json,time
from sharp_outer_bound import best_upper,S
ROOT=Path(__file__).resolve().parent
lo=F(3413848,10**7);hi=F(3484140,10**7);qlo=F(153,1000);qhi=F(1,2);target=F(999,1000)
stack=[(lo,hi,qlo,qhi,F(1),F(3,2),0),(lo,hi,qlo,qhi,F(3,2),F(2),0)]
accepted=[];visited=0;maximum=F(0);maxdepth=0;start=time.time()
while stack:
 *box,depth=stack.pop();box=tuple(box);visited+=1
 if visited>250000:raise RuntimeError('node cap: no complete certificate')
 try:v=F(best_upper(box),S)
 except (ArithmeticError,ValueError):v=F(2)
 if v<target:
  accepted.append([str(x) for x in box]+[str(v)]);maximum=max(maximum,v);maxdepth=max(maxdepth,depth)
 else:
  if depth>=60:raise RuntimeError('depth cap: no complete certificate')
  widths=[box[1]-box[0],box[3]-box[2],(box[5]-box[4])**2]
  axis=max(range(3),key=lambda i:widths[i]);i=2*axis;mid=(box[i]+box[i+1])/2
  b1=list(box);b2=list(box);b1[i+1]=mid;b2[i]=mid
  stack.extend([(*b1,depth+1),(*b2,depth+1)])
 if visited%1000==0:print('nodes',visited,'accepted',len(accepted),'pending',len(stack),'seconds',round(time.time()-start,1),flush=True)
volume=sum((F(c[1])-F(c[0]))*(F(c[3])-F(c[2]))*(F(c[5])-F(c[4])) for c in accepted)
if volume!=(hi-lo)*(qhi-qlo):raise RuntimeError('volume mismatch')
out={'all_cells_strict':True,'domain_t':[str(lo),str(hi)],'domain_theta_over_pi':[str(qlo),str(qhi)],'domain_X':['1','2'],'spatial_factors':20,'squared_ratio_target':str(target),'maximum_squared_ratio_upper':str(maximum),'accepted_cells':len(accepted),'visited_nodes':visited,'maximum_depth':maxdepth,'partition_rule':'max(dt,dq,dx_squared), first axis wins ties','cells':accepted,'seconds':time.time()-start}
(ROOT/'sharp_outer_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('SHARP OUTER PASS',len(accepted),'cells','maximum',float(maximum),'seconds',round(time.time()-start,1),flush=True)
