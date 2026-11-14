#!/usr/bin/env python3
"""Reconstruct and verify PA194QNS in a temporary directory.

No search, network or repository checkout is needed. The default replays both
physical engines; --quick omits them and reports the narrower scope explicitly.
"""
from pathlib import Path
import argparse, importlib.util, json, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent

def main():
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--receipt',type=Path)
    a=ap.parse_args()
    with tempfile.TemporaryDirectory(prefix='pa194qns-') as tmp:
        out=Path(tmp)/'machine'
        cmd=[sys.executable,'-B',str(HERE/'build.py'),'--output',str(out)]
        if a.quick:cmd.append('--quick')
        subprocess.run(cmd,check=True)
        for f in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','source.json','instructions.json','folds.json','sites.json','source_delta.json','table_delta.json','emitter_delta_from_sum_NS.json']:
            assert (out/f).read_bytes()==(HERE/'machine'/f).read_bytes(),f
        structural=Path(tmp)/'source_equivalence.json'
        subprocess.run([sys.executable,'-B',str(HERE/'verification/check_source_equivalence.py'),'--machine',str(out),'--out',str(structural)],check=True)
        independent=None
        if not a.quick:
            subprocess.run([sys.executable,'-B',str(HERE/'verification/check_literal.py'),str(out)],check=True)
            independent=json.loads((out/'independent/receipt.json').read_text())
        novelty=Path(tmp)/'novelty.json'
        subprocess.run([sys.executable,'-B',str(HERE/'comparison/check_candidate.py'),str(out/'machine.tm'),'--out',str(novelty)],check=True)
        n=json.loads(novelty.read_text());assert n['absent_from_corpus'] and n['compared_same_size_classes']==39
        result=dict(status='PASS',family='PA194QNS',full_physical_replay=not a.quick,
                    regenerated_bytes_equal=True,source_equivalence=json.loads(structural.read_text()),
                    construction=json.loads((out/'construction_receipt.json').read_text()),
                    independent=independent,novelty=n)
    text=json.dumps(result,indent=2)+'\n'
    if a.receipt:
        a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(text)
    print(text)

if __name__=='__main__':main()
