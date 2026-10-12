from pathlib import Path
import argparse, json
from ranked_morse import *
from sources import *

def main():
    ap=argparse.ArgumentParser(description='Build and verify a compressed regular-cell 3-ball source.')
    ap.add_argument('--bits',type=int,default=1024)
    ap.add_argument('--output',type=Path,default=None)
    args=ap.parse_args()
    if not 3<=args.bits<=100000: ap.error('--bits must be in [3,100000]')
    N=(1<<args.bits)+1;step=2;facets=disk_fan(4)
    packet,metadata,bm=product_source(N,step,facets)
    prepared=prepare(packet);proof=product_proof(packet,N,step,facets)
    assert proof is not None and verify_modular(prepared,proof) and one_critical_vertex(prepared)
    assert surface_is_disk(facets)
    wire=dumps_certificate(packet,proof)
    p2,r2=loads_certificate(wire)
    assert verify_modular(prepare(p2),r2)
    if args.output:
        args.output.write_text(wire+'\n')
    print(json.dumps({'source':'modular path times independently validated triangulated disk',
       'N_bits':N.bit_length(),'families':len(packet.families),'covers':len(packet.covers),
       'matching_recipes':len(packet.matching),'critical_cells':prepared.counts,
       'certificate_bytes':len(wire.encode()),'rank_verified':True,
       'source_specific_PL_ball':True,'native_unknot_integration':False},indent=2))

if __name__=='__main__':main()
