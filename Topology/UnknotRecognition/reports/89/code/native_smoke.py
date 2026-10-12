"""Opt-in verified native smoke test. Not run in this delivery.

Example:
  python code/native_smoke.py --fast-dir /path/to/ProveIt/Topology/UnknotRecognition/fast
"""
from __future__ import annotations
import argparse,json,sys,time
from pathlib import Path
from boundary_sources import CircleSource
from moment_kernel import compile_kernel_packed
from oracles import block_oracle
from proveit_adapter import make_oracle

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-dir',type=Path,required=True)
    parser.add_argument('--max-cycles',type=int,default=100000)
    parser.add_argument('--output',type=Path,default=Path('native_smoke.json'))
    args=parser.parse_args()
    if not (args.fast_dir/'fastunknot'/'weighted_orbits.py').is_file():parser.error('fast-dir does not contain the expected package')
    if args.max_cycles<1:parser.error('positive cycle cap required')
    sys.path.insert(0,str(args.fast_dir))
    cases=[CircleSource((1,),((0,0),)),CircleSource((11,7),((0,0),(0,1),(0,8),(1,3)),9)]
    for bits in (64,1024,16384):
        n=(1<<bits)+33;cases.append(CircleSource((n,),((0,0),(0,1),(0,n//2),(0,n-1)),n))
    records=[]
    for source in cases:
        proofs=[];oracle=make_oracle(max_cycles=args.max_cycles,certificates=proofs)
        start=time.perf_counter();result=compile_kernel_packed(*source.packet(),oracle);seconds=time.perf_counter()-start
        reference=compile_kernel_packed(*source.packet(),block_oracle)
        if result!=reference or result.pairs!=source.direct_pairs():raise AssertionError('native mismatch')
        records.append({'coordinate_bits':max(source.lengths).bit_length(),'ports':len(source.marks),
                        'verified_certificates':len(proofs),'seconds':seconds})
    args.output.write_text(json.dumps({'scope':'Native verified interval queries on circle interfaces, not knot recognition.',
                        'cases':records},indent=2)+'\n')
    print(f'Passed {len(records)} verified native cases; wrote {args.output}.')

if __name__=='__main__':main()
