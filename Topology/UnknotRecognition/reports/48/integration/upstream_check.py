"""Opt-in check against a real fast/ checkout. NOT executed in the delivery run.

This script does not install packages or alter the checkout. It refuses to
substitute a local stand-in for fastunknot's imported modules.
"""
import argparse
import itertools
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from compressed_b3 import Builder, recognize, verify
from experiments.families import sleeve


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast',type=Path,required=True,help='real Topology/UnknotRecognition/fast directory')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    fast=args.fast.resolve()
    if not (fast/'fastunknot/compressed_words.py').is_file():
        parser.error('no actual fastunknot/compressed_words.py at the supplied path')
    sys.path.insert(0,str(fast))
    import fastunknot.braid as upstream_braid
    import fastunknot.compressed_words as upstream_words
    from fastunknot.diagram import DiagramError
    assert Path(upstream_words.__file__).resolve().parent==fast/'fastunknot'
    count=0
    for n in range(6):
        for word in itertools.product((1,-1,2,-2),repeat=n):
            b=Builder();data=b.data(b.word(word))
            out=recognize(data,arena_factory=upstream_words.WordArena,max_nodes=1000000,max_work=50000000)
            assert verify(data,out['certificate'],arena_factory=upstream_words.WordArena,
                          max_nodes=1000000,max_work=50000000)==out['status']
            try: expected=upstream_braid.braid_certificate(3,word)['status']
            except DiagramError:
                expected='LINK'
            assert out['status']==expected
            count+=1
    for negative in (False,True):
        data=sleeve(64,negative=negative)
        out=recognize(data,arena_factory=upstream_words.WordArena,max_nodes=1000000,max_work=50000000)
        assert verify(data,out['certificate'],arena_factory=upstream_words.WordArena,
                      max_nodes=1000000,max_work=50000000)==out['status']
    result=dict(status='passed',explicit_cases=count,compressed_cases=2,
                kernel_module=str(upstream_words.__file__),braid_module=str(upstream_braid.__file__),
                scope='Actual imported kernel and explicit braid gateway only; not the full upstream regression suite.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
