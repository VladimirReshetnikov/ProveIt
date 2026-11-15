#!/usr/bin/env python3
"""Replay the frozen startup research; --full includes both broad screens."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import re
import subprocess
import tempfile

import explore as x
from generate_edits import generate

BASE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Run without Python -O.')
    hashes = {
        'pa194.native.tm': 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54',
        'core193.native.tm': '50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53',
        'PA194H5XS_core193.native.tm': '37a89169d85dbb660f20caccd33085225181c553e47f276837025827fe640f87',
        'PA194JH5XS_core193.native.tm': '8e2196fcc1c50f6d5eb1f80704e596f037f99d66f3946f8f2ea138701b77dcd3',
    }
    for name, digest in hashes.items():
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == digest
    original = x.parse(BASE / 'pa194.native.tm')
    reduced = {(q,b):(w,d,88 if n==301 else n) for (q,b),(w,d,n) in original.items() if q!=301}
    reduced[88,0] = (0,False,51)
    reduced[51,0] = (0,True,122)
    assert reduced == x.parse(BASE / 'core193.native.tm')
    receipt = {'hashes_and_reconstruction': True, 'source_contracts': {}}
    for header in [38,39,40,48]:
        x.sr.frame = lambda p, extra=0, effect=x.sr.PLAIN: (
            84,False,(x.sr.BIT[1],),tuple(x.sr.BIT[b] for b in p)
            + (('r',0,1,header+extra-len(p)),x.sr.BIT[1],effect))
        r = x.sr.validate(reduced, x.contracts())
        assert r['ok'] == (header>=40)
        receipt['source_contracts'][header] = r
    with tempfile.TemporaryDirectory(prefix='runtime193-replay-') as tmp:
        tmp = Path(tmp)
        receipt['edit_lists'] = generate(tmp)
        sources = ['single','all38'] + (['multi','root38'] if args.full else [])
        for name in sources:
            subprocess.run(['g++','-O2','-std=c++17',str(BASE / f'search_startup_{name}.cpp'),'-o',str(tmp/name)],check=True)
        template = str(BASE / 'startup_any_frame_templates.tsv')
        cases = [
            ('single', [str(tmp/'single'),str(BASE/'core193.native.tm'),str(tmp/'single.tsv'),'200000','0','100000',template], {'edits':28,'successes':0,'simulations':5404,'halts':57,'rays':5347,'limits':0}),
            ('H5XS', [str(tmp/'all38'),str(BASE/'PA194H5XS_core193.native.tm'),str(BASE/'no_edits.tsv'),'200000','0','1',str(BASE/'no_seed_templates.tsv')], {'edits':1,'successes':0,'simulations':193,'halts':2,'rays':191,'limits':0,'drifts':0,'cycles':0}),
            ('JH5XS', [str(tmp/'all38'),str(BASE/'PA194JH5XS_core193.native.tm'),str(BASE/'no_edits.tsv'),'200000','0','1',str(BASE/'no_seed_templates.tsv')], {'edits':1,'successes':0,'simulations':193,'halts':2,'rays':191,'limits':0,'drifts':0,'cycles':0}),
        ]
        if args.full:
            cases += [
                ('combinations', [str(tmp/'multi'),str(BASE/'core193.native.tm'),str(tmp/'combinations.tsv'),'200000','0','100000',template], {'edits':15120,'successes':0,'simulations':2918160,'halts':24060,'rays':2882220,'limits':11880}),
                ('pairs', [str(tmp/'root38'),str(BASE/'core193.native.tm'),str(tmp/'pairs.tsv'),'200000','0','100000',template], {'edits':12167,'successes':0,'simulations':12167,'halts':0,'rays':8891,'limits':353,'drifts':2818,'cycles':105}),
            ]
        def run(case):
            name, command, expected = case
            p = subprocess.run(command,text=True,capture_output=True,check=True)
            assert not p.stdout.strip(), (name,p.stdout)
            line = [line for line in p.stderr.splitlines() if line.startswith('DONE ')][-1]
            actual = {k:int(v) for k,v in re.findall(r'(edits|successes|simulations|ticks|halts|rays|limits|drifts|cycles) (\d+)',line)}
            assert all(actual[k]==v for k,v in expected.items()), (name,actual,expected)
            return name,actual
        with ThreadPoolExecutor(max_workers=2) as executor:
            receipt['startup_checks'] = dict(executor.map(run,cases))
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
