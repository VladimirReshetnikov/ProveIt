#!/usr/bin/env python3
"""Build two universal certificates for the shorter disjunctive h1 head J.

Derived K/S/Peirce templates are the retained uniform rho8 theorems. The
source of Builder is the sibling construction's finite proof certificate
builder, copied as hilbert_builder.py so reproduction is self-contained.
"""
from pathlib import Path
import argparse,json
from hilbert_builder import Builder

def generate(destination):
 destination.mkdir(parents=True,exist_ok=True);receipts=[]
 # Original O=(X->1)->H proves J=(X->H)->H, without any explosion use.
 b=Builder();d=b.term('parameter','D');h=b.term('parameter','H');f=b.term('nat',1)
 x=b.quant_x(d,h);xh=b.i(x,h);nh=b.n(h)
 p=b.hyp(xh);q=b.hyp(nh)
 nx=b.compose(p,q)
 hh=b.mp(b.h1(d,h),nx)
 nh_h=b.deduct(nh,hh)
 hh=b.mp(b.peirce(h,f),nh_h)
 j=b.deduct(xh,hh)
 receipts.append(b.dump(j,'Original O derives the shorter head J',destination/'h1_to_J.json'))
 # J recovers O, using the independent h5X bootstrap; no original h1.
 b=Builder();d=b.term('parameter','D');h=b.term('parameter','H')
 x=b.quant_x(d,h);nx=b.n(x)
 j=b.add('joinJ',(d,h),b.i(b.i(x,h),h))
 p=b.hyp(nx)
 xh=b.compose(p,b.witness_explosion(h))
 hh=b.mp(j,xh)
 o=b.deduct(nx,hh)
 receipts.append(b.dump(o,'J plus h5X recovers original O',destination/'J_to_h1.json'))
 (destination/'generation.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print(json.dumps(receipts,indent=2))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);generate(p.parse_args().output)
