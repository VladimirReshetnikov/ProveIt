#!/usr/bin/env python3
"""Recheck the exact final source against either of the two new literal tables.

Every acceleration rule is rederived from the selected table by the retained
unary/list induction engine. This is an ordinary mathematical certificate,
not a proof-assistant endpoint. Python assertions must be enabled.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

PINS = {
    'basis': '014133f39c409277c239fa327db17800b4e886a5c7a5a73034ed87e4978820aa',
    'candidate': 'd017abe46023a4154085a2fe2c04c8d66bbbec53b81d193d520ad697d171cbd4',
    'source': 'c17ab40e032e79dca03eaa955a78dbcd65bd030795ecc232dc504aff1551cb20',
    'baseline_source': '1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f',
    'engine': 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'helper': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-dir', type=Path, required=True)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--limit', type=int, default=0,
                    help='Optional partial proof-construction prefix; never a universal PASS')
    args = ap.parse_args()
    require(args.limit >= 0, 'Negative prefix bound')
    table_hash = sha(args.table)
    require(table_hash in (PINS['basis'], PINS['candidate']), 'Unexpected literal table bytes')
    require(sha(args.sites) == PINS['source'], 'Unexpected source bytes')
    baseline_source = args.baseline_dir/'source/sites_logical.json'
    require(sha(baseline_source) == PINS['baseline_source'], 'Unexpected baseline source')
    engine_dir = args.baseline_dir/'upstream/zfc237/verification'
    require(sha(engine_dir/'symbolic_runtime.py') == PINS['engine'], 'Unexpected symbolic engine')
    require(sha(engine_dir/'independent_runtime.py') == PINS['helper'], 'Unexpected runtime helper')
    sys.path.insert(0, str(engine_dir))
    import symbolic_runtime as symbolic
    # Independent trie/ancestor checker: no discovery or compiler imports.
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import audit_source_graph as source_audit
    from check_fold235 import parse
    table, start, _ = parse(args.table)
    sites = json.loads(args.sites.read_text())
    before, before_meta = source_audit.graph(json.loads(baseline_source.read_text()))
    after, after_meta = source_audit.graph(sites)
    require(before == after and before_meta['leaves'] == after_meta['leaves'] == 6455,
            'Source operational graph changed')
    require(start == 95 and len(table) == (472 if table_hash == PINS['basis'] else 470),
            'Wrong state census or start')
    require(after_meta['guarded_cases'] == 8386, 'Wrong guarded case census')
    receipt = {
        'status': 'IN_PROGRESS', 'table_sha256': table_hash,
        'sites_sha256': sha(args.sites), 'baseline_source_sha256': sha(baseline_source),
        'engine_sha256': sha(symbolic.__file__), 'helper_sha256': sha(symbolic.r.__file__),
        'driver_sha256': sha(__file__), 'source_audit_sha256': sha(source_audit.__file__),
        'states': len(table)//2, 'rows': len(table),
        'source_graph_identical': True, 'expected_cases': 8386,
        'proof_construction_limit_per_case': 4000,
        'duration_slots': ['constant', 'gap', *[f'R{i}' for i in range(9)],
                           'first_spare', 'remaining_spare_list_width'],
        'scope': 'All independent natural primary register values at each zero/positive guard, '
                 'all nonnegative extra gaps, arbitrary first spare and arbitrary finite '
                 'spare tail. Exact whole tape, head and source successor; positive duration. '
                 'Ordinary mathematical proof, not a proof-assistant endpoint.',
        'limits_scope': 'The 4000-step limit bounds construction of the symbolic proof only. '
                        'No bound on concrete time, values, gap or spare-list length is imposed.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    cases, used = [], set()

    def save():
        receipt.update(cases=len(cases), seconds=time.monotonic()-started)
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')

    try:
        lemmas, blocks = symbolic.prove_blocks(table)
        receipt['list_induction_blocks'] = blocks
        print('Exact source graph and four arbitrary-context list schemas PASS', flush=True)
        for index, site in enumerate(sites):
            for positive in ((False, True) if site[1] == 'CD' else (False,)):
                answer = symbolic.case(table, lemmas, site, positive)
                used.update(answer.pop('rows'))
                answer.pop('trace')
                cases.append({'site_index': index, 'positive': positive, **answer})
                if len(cases) % 1000 == 0:
                    print('proved', len(cases), 'cases', round(time.monotonic()-started, 2),
                          'seconds', flush=True)
                    save()
                if args.limit and len(cases) >= args.limit and len(cases) < 8386:
                    receipt['status'] = 'PARTIAL_PREFIX_PASS'
                    save()
                    print(json.dumps(receipt, indent=2), flush=True)
                    return
        require(len(cases) == 8386, 'Incomplete proof')
        require(used == set(table), 'Not all literal rows were covered')
        case_path = args.output.with_name(args.output.stem+'_cases.json')
        case_path.write_text(json.dumps(cases, indent=2)+'\n')
        receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS',
                       symbolic_steps=sum(case['symbolic_steps'] for case in cases),
                       minimum_actual_steps=min(case['duration'][0] for case in cases),
                       maximum_symbolic_steps=max(case['symbolic_steps'] for case in cases),
                       all_rows_used=True, used_rows=sorted(used),
                       cases_file=case_path.name, cases_sha256=sha(case_path))
        save()
        print(json.dumps({k: v for k, v in receipt.items()
                          if k not in ('list_induction_blocks', 'used_rows')}, indent=2), flush=True)
    except Exception as exc:
        receipt.update(status='NOT_PROVED', site_index=locals().get('index'),
                       site=locals().get('site'), positive=locals().get('positive'),
                       error=repr(exc))
        save()
        raise


if __name__ == '__main__':
    main()
