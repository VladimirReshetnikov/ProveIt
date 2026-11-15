#!/usr/bin/env python3
"""Rebuild all three tables in a temporary directory and replay certificates."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile

import build
import check_commands
import check_source

ROOT = Path(__file__).resolve().parent

def verify(output=None, quick=False):
    assert __debug__, 'Run without Python -O.'
    comparison = {}
    source_binding = {}
    with tempfile.TemporaryDirectory(prefix='pa194gd-rebuild-') as destination:
        for family in ('GD','GDH','GDHS'):
            fresh = Path(destination) / family
            receipt = build.build(family, fresh, not quick)
            compared = []
            for path in fresh.iterdir():
                if path.name == 'receipt.json':
                    continue
                frozen = ROOT / 'machines' / family / path.name
                if path.suffix == '.json':
                    assert json.loads(path.read_text()) == json.loads(frozen.read_text()), (family,path.name)
                else:
                    assert path.read_bytes() == frozen.read_bytes(), (family,path.name)
                compared.append(path.name)
            comparison[family] = {'files_equal':sorted(compared), 'receipt':receipt}
            source_binding[family] = check_source.check_machine(fresh,None,{'GD':'sum','GDH':'H','GDHS':'HS'}[family])
    emitter = check_commands.emitter_check()
    words = {}
    for detector in ('sum','cache'):
        check_commands.DETECTOR = detector
        words[detector] = check_commands.word_check()
    result = {'status':'PASS','full_source_contracts':not quick,
              'construction':comparison,'emitter':emitter,'derived_words':words,
              'independent_source_template_binding':source_binding,
              'scope':'Construction, source graph, simultaneous local folds, blank startup, symbolic instruction contracts, independent arithmetic-template binding, and algebraic command identities. Independent literal-row replay and the mathematical iPRA proof are separate.'}
    if output:
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','families':list(comparison),'full_source_contracts':not quick}))
    return result

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,help='Write a fresh report here.')
    p.add_argument('--quick',action='store_true',help='Skip universal source-contract replay.')
    a=p.parse_args()
    verify(a.output,a.quick)
