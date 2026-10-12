"""Adjacent-port witness, optionally with a huge binary gap."""
from __future__ import annotations
import argparse,json
from boundary_sources import CircleSource
from moment_kernel import compile_kernel_packed,packed_moment_weights,kernel_record,packing_shift
from oracles import block_oracle

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits',type=int,help='Use circle length 2**bits+2 (1 to 32768).')
    args=parser.parse_args()
    if args.bits is not None and not 1<=args.bits<=32768:parser.error('bits must be in [1,32768]')
    n=4 if args.bits is None else (1<<args.bits)+2
    source=CircleSource((n,),((0,0),(0,1)))
    size,pairs,term,mass,owners,counts=source.packet()
    weights=packed_moment_weights(size,term,mass)
    histogram=block_oracle(size,pairs,weights,1)
    kernel=compile_kernel_packed(*source.packet(),block_oracle)
    if kernel.pairs!=source.direct_pairs():raise AssertionError('independent source-order mismatch')
    integer=lambda n:n if n.bit_length()<=256 else hex(n)
    print(json.dumps({'scope':'Exact circle-interface witness; not a native AHT or knot certificate.',
        'coordinate_bits':n.bit_length(),'circle_length':integer(n),'packing_shift':packing_shift(4),
        'scalar_histogram':[{'weight':integer(w[0]),'orbits':integer(m)} for w,m in histogram],
        'kernel':kernel_record(kernel)},indent=2))

if __name__=='__main__':main()
