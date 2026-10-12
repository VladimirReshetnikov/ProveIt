"""Replay an arithmetic Morse certificate. Does not authenticate source geometry."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
from ranked_morse import (loads_certificate,prepare,verify_affine,verify_modular,
                           AffineProof,one_critical_vertex)

def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--max-bytes',type=int,default=64*1024*1024)
    args=parser.parse_args()
    try:
        if args.max_bytes<=0 or args.certificate.stat().st_size>args.max_bytes:
            raise ValueError('input exceeds the configured byte limit')
        packet,proof=loads_certificate(args.certificate.read_text(encoding='utf-8'))
        prepared=prepare(packet)
        valid=(verify_affine if isinstance(proof,AffineProof) else verify_modular)(prepared,proof)
        print(json.dumps({'rank_valid':valid,'critical_cells':prepared.counts,
                          'one_critical_vertex':one_critical_vertex(prepared),
                          'source_geometry_authenticated':False,
                          'ball_or_knot_verdict':None},indent=2))
        return 0 if valid else 1
    except (OSError,ValueError,TypeError,KeyError,AttributeError) as exc:
        print(json.dumps({'certificate_rejected':True,'reason':str(exc),
                          'ball_or_knot_verdict':None}),file=sys.stderr)
        return 2

if __name__=='__main__':sys.exit(main())
