#!/usr/bin/env python3
"""Replay all 8,390 source cases against the exact 242-state table.

The expanded option uses inherited symbolic induction code, copied unchanged.
The driver binds the actual table, sites, and imported reference files before
and after execution.  Python assertions must be enabled.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse
import gzip
import json
import sys
import time
from verify_local import read

ROOT = Path(__file__).resolve().parents[1]
TABLE_SHA = 'c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
SITES_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expanded', action='store_true')
    parser.add_argument('--out', type=Path, default=ROOT/'evidence')
    args = parser.parse_args()
    table_path = ROOT/'machine/zfc_return_fold242_old.tm'
    source_path = ROOT/'machine/sites_logical.json'
    assert digest(table_path) == TABLE_SHA
    assert digest(source_path) == SITES_SHA
    bound = [table_path, source_path, Path(__file__), ROOT/'code/verify_local.py']
    bound += sorted(p for p in (ROOT/'reference/inherited').rglob('*')
                    if p.is_file() and '__pycache__' not in str(p))
    before = {str(p.relative_to(ROOT)):digest(p) for p in bound}
    table = read(table_path)
    assert len(table) == 484 and len({q for q,b in table}) == 242
    assert all(t != 27 for w,d,t in table.values())
    sites = json.loads(source_path.read_text())
    assert len(sites) == 6459
    expected = sum(2 if op == 'CD' else 1 for p,op,r in sites)
    assert expected == 8390
    sys.path.insert(0, str(ROOT/'reference/inherited/code'))
    import full_symbolic_parametric as F
    from review_affine_source import full_inc, full_strip
    import parametric_prefix_affine as affine
    counts = Counter()
    rules = Counter()
    rows = set()
    records = []
    began = time.monotonic()
    if args.expanded:
        assert F.PADDING == 64
        F.m.TABLE = table
        F.m.prove_blocks()
        F.m.prove_word_identity()
    else:
        affine.PADDING = 64
        string_table = {(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()}
    for index,(p,op,r) in enumerate(sites):
        for zero in ((True,False) if op == 'CD' else (None,)):
            if args.expanded:
                result = F.case(p,op,r,zero,[[0,9]]*9)
                for event in result['trace']:
                    if 'state' in event:
                        rows.add((event['state'],event['read']))
                    rules[event['rule']] += 1
                counts['symbolic_rules'] += result['rules']
                record = {k:v for k,v in result.items() if k != 'trace'}
            else:
                # The affine register boxes use physical register indices.
                physical = (6,2,0,4,3,7,8,5,1)
                rr = physical[r] if op in ('CI','CD') else r
                branch = (rr,zero) if op == 'CD' else None
                extra = 0
                effect = None
                overflow = False
                if op == 'CI':
                    successor,overflow = full_inc(p)
                    effect = ('inc',rr)
                elif op == 'CD' and not zero:
                    successor,overflow = full_inc(p)
                    effect = ('dec',rr)
                    extra = 1
                elif op == 'CD':
                    successor,overflow = full_inc(full_strip(p,'0',1))
                elif op == 'CB':
                    successor,overflow = full_inc(full_strip(p,'0',r))
                elif op == 'CC':
                    successor = full_strip(p,'1',r)
                else:
                    assert op == 'CH'
                    successor = ''
                right = [('b',int(b)) for b in successor]
                right += [('r',0,1,64+extra+int(overflow)-len(successor)),
                          ('b',1),('box',('plain',effect))]
                rc,literal = affine.run(string_table,p,branch,
                    affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
                assert literal > 0
                rules.update(rc)
                counts['symbolic_rules'] += sum(rc.values())
                record = {'rules':sum(rc.values()),'minimum_literal_steps':literal}
            counts['cases'] += 1
            records.append({'index':index,'pc':p,'op':op,'r':r,'zero':zero,**record})
        if index % 1000 == 0:
            print('sites',index,'cases',counts['cases'],flush=True)
    assert counts['cases'] == expected
    if args.expanded:
        assert rows == set(table), ('uncovered_rows',sorted(set(table)-rows))
    after = {str(p.relative_to(ROOT)):digest(p) for p in bound}
    assert before == after, 'An input changed during verification.'
    report = {'status':'PASS_EXPANDED_RUNTIME' if args.expanded else 'PASS_AFFINE_RUNTIME',
              'complete':True,'working_states':242,'source_leaves':len(sites),
              'expected_cases':expected,'counts':dict(counts),'rules':dict(rules),
              'arbitrary_nine_natural_registers':True,
              'arbitrary_nonnegative_gap_above_padding':True,'padding':64,
              'arbitrary_nonempty_finite_spare_suffix':True,
              'positive_progress_checked':True,'table_sha256':TABLE_SHA,
              'sites_logical_sha256':SITES_SHA,
              'literal_rows_covered':len(rows) if args.expanded else None,
              'literal_rows':sorted(rows) if args.expanded else None,
              'input_bindings':before,'inputs_unchanged':True,
              'seconds':time.monotonic()-began,
              'scope':'Ordinary symbolic-induction certificate replay; not a proof-assistant kernel.'}
    args.out.mkdir(parents=True,exist_ok=True)
    name = 'expanded-runtime' if args.expanded else 'affine-runtime'
    (args.out/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
    with gzip.GzipFile(filename=str(args.out/(name+'-cases.json.gz')),mode='wb',mtime=0) as stream:
        stream.write((json.dumps(records,indent=2)+'\n').encode())
    print(json.dumps({k:v for k,v in report.items() if k not in ('input_bindings','literal_rows')},indent=2),flush=True)

if __name__ == '__main__':
    main()
