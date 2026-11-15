#!/usr/bin/env python3
"""Uniform certificates for the three-parameter 15-token positive head J_A."""
from pathlib import Path
import argparse,json
from hilbert_builder import Builder

def old_j(b,d,h):
 f=b.term('nat',1);x=b.quant_x(d,h);xh=b.i(x,h);nh=b.n(h)
 p=b.hyp(xh);q=b.hyp(nh)
 nx=b.compose(p,q);hh=b.mp(b.h1(d,h),nx)
 nh_h=b.deduct(nh,hh);hh=b.mp(b.peirce(h,f),nh_h)
 return b.deduct(xh,hh)

def generate(destination):
 destination.mkdir(parents=True,exist_ok=True);receipts=[]
 b=Builder();d=b.term('parameter','D');h=b.term('parameter','H');a=b.term('parameter','A')
 p=b.u(d,h);np=b.n(p);pa=b.i(p,a);x=b.u(d,np);y=b.u(d,pa)
 j=old_j(b,d,h)
 # Implication monotonicity from the old closed explosion proof.
 pnp=b.hyp(np);ppa=b.compose(pnp,b.old_explosion(a))
 lifted=b.gen(d,b.deduct(np,ppa))
 xy=b.mp(b.h6(d,np,pa),lifted)
 yh=b.i(y,h);pyh=b.hyp(yh);xh=b.compose(xy,pyh)
 hh=b.mp(j,xh);ja=b.deduct(yh,hh)
 receipts.append(b.dump(ja,'Original calculus derives every J_A instance',destination/'old_to_JA.json'))
 b=Builder();d=b.term('parameter','D');h=b.term('parameter','H');f=b.term('nat',1)
 x=b.quant_x(d,h);nx=b.n(x)
 j=b.add('joinJA',(d,f,h),b.i(b.i(x,h),h))
 pnx=b.hyp(nx);xh=b.compose(pnx,b.witness_explosion(h));hh=b.mp(j,xh)
 o=b.deduct(nx,hh)
 receipts.append(b.dump(o,'J_A at A=1 and h5X recover original O',destination/'JA_to_h1.json'))
 (destination/'generation.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps(receipts,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);generate(p.parse_args().output)
