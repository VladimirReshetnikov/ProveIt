"""Exact Hilbert templates for two generalized modal-B presentations.
The retained restricted rho8 basis supplies K,S,Peirce uniformly.
"""
from pathlib import Path
import json,argparse
from hilbert_builder import Builder
HERE=Path(__file__).parent
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,default=HERE/'certificates');args=parser.parse_args()
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
def olddual(b,d,h):
 f=b.term('nat',1);x=b.quant_x(d,h);nx=b.n(x);nh=b.n(h)
 ph,px=b.hyp(nh),b.hyp(nx)
 ff=b.mp(ph,b.mp(b.h1(d,h),px));xx=b.mp(b.old_explosion(x),ff)
 nx_x=b.deduct(nx,xx);xx=b.mp(b.peirce(x,f),nx_x)
 return b.deduct(nh,xx)
def old_ba(b,d,a,h):
 p=b.u(d,h);np=b.n(p);pa=b.i(p,a)
 pp=b.hyp(np);ppa=b.compose(pp,b.old_explosion(a))
 lift=b.gen(d,b.deduct(np,ppa))
 xy=b.mp(b.h6(d,np,pa),lift)
 return b.compose(olddual(b,d,h),xy)
def dn(b,h):
 p=b.hyp(h);q=b.hyp(b.n(h));ff=b.mp(q,p)
 return b.deduct(h,b.deduct(b.n(h),ff))
def contra(b,p):
 _,a,c=b.terms[b.out(p)];aa=b.hyp(a);nc=b.hyp(b.n(c))
 ff=b.mp(nc,b.mp(p,aa));return b.deduct(b.n(c),b.deduct(a,ff))
def ba(b,d,a,h):
 return b.add('BA',(d,a,h),b.i(b.n(h),b.u(d,b.i(b.u(d,h),a))))
def bp(b,d,a,h):
 return b.add('BP',(d,a,h),b.i(h,b.u(d,b.i(b.u(d,b.n(h)),a))))
def new_h1(b,d,h,kind):
 f=b.term('nat',1);x=b.quant_x(d,h);nx=b.n(x);nh=b.n(h)
 if kind=='BA':dual=ba(b,d,f,h)
 else:
  double=dn(b,h)
  lifted=b.mp(b.h6(d,h,b.n(nh)),b.gen(d,double))
  contraposed=contra(b,lifted)
  l2=b.mp(b.h6(d,b.n(b.u(d,b.n(nh))),b.n(b.u(d,h))),b.gen(d,contraposed))
  dual=b.compose(bp(b,d,f,nh),l2)
 pn,ph=b.hyp(nx),b.hyp(nh)
 ff=b.mp(pn,b.mp(dual,ph));hh=b.mp(b.witness_explosion(h),ff)
 hh=b.mp(b.peirce(h,f),b.deduct(nh,hh))
 return b.deduct(nx,hh)
receipts=[]
for kind in ['BA','BP']:
 b=Builder();d,h,a=[b.term('parameter',x)for x in ['D','H','A']]
 p=old_ba(b,d,a,h)if kind=='BA'else b.compose(dn(b,h),old_ba(b,d,a,b.n(h)))
 receipts.append(b.dump(p,'Old calculus derives '+kind,OUT/f'old_to_{kind}.json'))
 b=Builder();d,h=[b.term('parameter',x)for x in ['D','H']]
 receipts.append(b.dump(new_h1(b,d,h,kind),kind+' plus H5X recovers old first head',OUT/f'{kind}_to_old.json'))
b=Builder();d,h,a=[b.term('parameter',x)for x in ['D','H','A']]
receipts.append(b.dump(b.compose(b.h5(d,h),b.old_explosion(a)),'Old witness to independent-consequent witness',OUT/'H5_to_H5X.json'))
b=Builder();d,h=[b.term('parameter',x)for x in ['D','H']];f=b.term('nat',1)
receipts.append(b.dump(b.h5x(d,f,h),'Independent-consequent witness to old witness',OUT/'H5X_to_H5.json'))
(OUT/'generation.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
