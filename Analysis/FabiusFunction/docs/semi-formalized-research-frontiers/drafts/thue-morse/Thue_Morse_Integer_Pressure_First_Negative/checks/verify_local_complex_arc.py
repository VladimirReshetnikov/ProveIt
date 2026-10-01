"""Adaptive exact local-arc certificate; all accepted cells are rational enclosures."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from fractions import Fraction as F
from pathlib import Path
import json,time,hashlib
from complex_interval_core import I,iv,S,tangent_circle,spatial_product
start=time.time();root=Path(__file__).resolve().parent
lo=F(3413848,10**7);hi=F(3484140,10**7);qmax=F(153,1000)
stack=[(lo,hi,F(0),qmax,0)];accepted=[];visited=0;maxq=F(0);maxdepth=0
while stack:
 tl,th,ql,qh,depth=stack.pop();visited+=1
 if visited>200000:raise RuntimeError('node budget exceeded; certificate remains incomplete')
 try:
  a=tangent_circle(tl,th,ql,qh);r2=a.square_mod()
  okay=a.re.lo>iv(F(303,1000)).hi and r2.lo>iv(F(348,1000)**2).hi and r2.hi<iv(F(38,100)**2).lo
  bounds=[]
  if okay:
   h1=spatial_product(a,F(1))
   for j in range(1,6):
    x=F(1,2**j);hn=spatial_product(a,1+x);hx=spatial_product(a,x);den=h1*hx
    ratio=hn/den;bounds.append(F(ratio.hi,S))
    if ratio.hi>=S:okay=False;break
 except ArithmeticError:okay=False
 if okay:
  mx=max(bounds);maxq=max(maxq,mx);maxdepth=max(maxdepth,depth)
  accepted.append([str(tl),str(th),str(ql),str(qh),str(mx)])
 else:
  if depth>=35:raise RuntimeError('depth exceeded; certificate remains incomplete')
  if th-tl>3*(qh-ql):
   mid=(tl+th)/2;stack.extend([(tl,mid,ql,qh,depth+1),(mid,th,ql,qh,depth+1)])
  else:
   mid=(ql+qh)/2;stack.extend([(tl,th,ql,mid,depth+1),(tl,th,mid,qh,depth+1)])
 if visited%1000==0:print('visited',visited,'accepted',len(accepted),'stack',len(stack),'seconds',round(time.time()-start,2),flush=True)
area=sum((F(c[1])-F(c[0]))*(F(c[3])-F(c[2]))for c in accepted)
if area!=(hi-lo)*qmax:raise ArithmeticError('domain area')
out=dict(all_cells_strict=True,domain_t=[str(lo),str(hi)],domain_theta_over_pi=['0',str(qmax)],accepted_cells=len(accepted),visited_nodes=visited,maximum_depth=maxdepth,maximum_Q_squared_upper=str(maxq),strict_domain_slack=True,cells=accepted,seconds=time.time()-start)
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('local_complex_arc_certificate.json', json.dumps(out,indent=2)+'\n')
print('LOCAL CERTIFICATE PASSES',len(accepted),'cells; max Q squared',float(maxq),'seconds',round(time.time()-start,2),flush=True)
