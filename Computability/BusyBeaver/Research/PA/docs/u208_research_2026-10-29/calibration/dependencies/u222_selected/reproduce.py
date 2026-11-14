#!/usr/bin/env python3
"""Reconstruct and audit U222; --full repeats every symbolic runtime case.

Python 3.10+, standard library only. This does not invoke a solver, a network
service, or a proof-assistant kernel. All generated files go into a temporary
directory, except an optional report explicitly requested with --report.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(script, args, directory):
    print('Running '+script, flush=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    subprocess.run([sys.executable, '-B', str(ROOT/'code'/script), *map(str,args)],
                   cwd=directory, env=env, check=True)


def manifest_check():
    seen = set()
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        if not line:
            continue
        expected, name = line.split('  ', 1)
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Unsafe manifest path')
        require(name not in seen, 'Duplicate manifest path')
        seen.add(name)
        require(sha(ROOT/relative) == expected, 'Hash mismatch: '+name)
    require({'machine/u.tm','machine/u.native.tm','machine/sites.json',
             'paper/report.tex','paper/report.pdf','reproduce.py'} <= seen,
            'Manifest omits a principal deliverable')
    return len(seen)


def validate_runtime(report, sites, summary):
    expected = sum(2 if row[1] == 'CD' else 1 for row in sites)
    require(report['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Runtime failure')
    require(report['table_sha256'] == summary['native_sha256'], 'Wrong runtime table')
    require(report['sites_sha256'] == summary['source_sha256'], 'Wrong runtime source')
    require(report['working_states'] == summary['working_states'], 'Wrong runtime count')
    require(report['site_count'] == len(sites), 'Wrong site count')
    require(report['expected_cases'] == report['proved_cases'] == expected,
            'Incomplete runtime coverage')
    require(not report.get('failures', []), 'Runtime has failures')
    require(report['startup_status'] == 'CALIBRATED_DIRTY_ROOT_SEED',
            'Runtime did not establish calibrated startup')
    require(report['checker_sha256'] == sha(ROOT/'code/runtime/symbolic_runtime.py'),
            'Wrong symbolic checker')
    require(report['helper_sha256'] == sha(ROOT/'code/runtime/independent_runtime.py'),
            'Wrong symbolic helper')
    return expected


def validate_bootstrap(review, summary, sites, startup):
    require(review['status'] == 'INDEPENDENT_LITERAL_STARTUP_PASS', 'Startup failure')
    require(review['table_sha256'] == summary['native_sha256'], 'Wrong bootstrap table')
    require(review['sites_sha256'] == summary['source_sha256'], 'Wrong bootstrap source')
    require(review['working_states'] == review['graph_reachable_working_states']
            == summary['working_states'], 'State census failure')
    require(review['expected_symbolic_cases'] == sum(2 if r[1]=='CD' else 1 for r in sites),
            'Bootstrap case census differs')
    require(startup['status'] == 'CALIBRATED_DIRTY_ROOT_SEED', 'Uncalibrated startup')
    require(startup['registers'] == [4,0,0,0,0,0,0,0,0], 'Wrong logical seed')
    require(startup['spares'] == [1]*40 and startup['gap'] == 1, 'Wrong spare/gap seed')
    require(startup['state'] == 84 and startup['head'] == -8, 'Wrong startup position')
    require(review['startup_steps'] == review['first_calibrated_root']
            == startup['steps'] == 95714, 'Wrong startup duration')
    require(all(review[k] for k in ['every_startup_trace_row_replayed',
            'complete_finite_support_compared','four_induction_block_schema_rows_match']),
            'Missing bootstrap or block-schema check')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true',help='Repeat all 5,060 symbolic cases')
    ap.add_argument('--report',type=Path,help='Write a JSON receipt at this explicit path')
    args=ap.parse_args()
    start=time.monotonic()
    nfiles=manifest_check()
    summary=json.loads((ROOT/'machine/machine_summary.json').read_text())
    sites=json.loads((ROOT/'machine/sites.json').read_text())
    saved=json.loads((ROOT/'evidence/runtime.json').read_text())
    cases=validate_runtime(saved,sites,summary)
    with tempfile.TemporaryDirectory(prefix='u222-reproduce-') as folder:
        tmp=Path(folder)
        candidate=tmp/'machine'
        candidate.mkdir()
        run('build_source.py',['--baseline',ROOT/'inputs/k215_sites.json',
            '--recipe',ROOT/'inputs/source_recipe.json','--output',candidate/'sites.json'],tmp)
        run('build_table.py',['--baseline',ROOT/'inputs/k215.native.tm',
            '--recipe',ROOT/'inputs/table_recipe.json','--output',candidate],tmp)
        for name in ['sites.json','u.native.tm','u.tm','state_map.json','machine_summary.json']:
            require((candidate/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),
                    'Reconstruction differs: '+name)
        shutil.copyfile(ROOT/'machine/construction.json',candidate/'construction.json')
        run('audit_source.py',['--baseline',ROOT/'inputs/k215_sites.json',
            '--candidate',candidate,'--unshifted','--macro-dag',ROOT/'references/logic/DagPerm.v',
            '--out',tmp/'source_audit.json'],tmp)
        audit=json.loads((tmp/'source_audit.json').read_text())
        require(audit['status']=='PASS' and audit['matrix_code']=='c'
                and audit['clause_order']=='lower-first','Source audit failed')
        require(audit['inputs']['candidate_source_sha256']==summary['source_sha256'],
                'Source audit did not bind the exact source')
        require(audit['new_body_literal_binding']['bound_new_primitive_instructions']==737,
                'Wrong replacement length')
        require(audit['closed_splice']['retained_primitive_nodes']==3154,
                'Wrong retained source')
        bindings=audit['proved_macro_node_binding']['macro_nodes']
        require(set(bindings)=={'119','168','171','177','180','181','218'}
                and all(v['exact_CFG_match_modulo_primitive_normalization']
                        for v in bindings.values()),
                'Missing binding to all-natural macro proofs')
        require(sum(v['literal_cases'] for v in audit['literal_macro_contracts'].values())==1792,
                'Incomplete supplemental macro tests')
        run('review_native_bootstrap.py',['--table',candidate/'u.native.tm',
            '--sites',candidate/'sites.json','--startup',ROOT/'evidence/startup.json',
            '--out',tmp/'bootstrap.json'],tmp)
        bootreview=json.loads((tmp/'bootstrap.json').read_text())
        startup=json.loads((ROOT/'evidence/startup.json').read_text())
        validate_bootstrap(bootreview,summary,sites,startup)
        full=None
        if args.full:
            run('validate_native.py',[candidate/'u.native.tm',candidate/'sites.json',
                tmp/'runtime'],tmp)
            full=json.loads((tmp/'runtime/runtime.json').read_text())
            validate_runtime(full,sites,summary)
            fullstartup=json.loads((tmp/'runtime/startup.json').read_text())
            require(fullstartup==startup,'Regenerated startup differs')
            generated_cases=json.loads((tmp/'runtime/runtime_cases.json').read_text())
            published_cases=json.loads((ROOT/'evidence/runtime_cases.json').read_text())
            require(generated_cases==published_cases,'Regenerated case summaries differ')
        report={
            'status':'U222_FULL_REPRODUCTION_PASS' if args.full else 'U222_RECONSTRUCTION_AUDIT_PASS',
            'manifest_files_checked':nfiles,'working_states':summary['working_states'],
            'transition_rows':summary['transitions'],'source_occurrences':len(sites),
            'source_operations':dict(Counter(row[1] for row in sites)),
            'symbolic_cases':cases,'symbolic_cases_rerun':args.full,
            'saved_symbolic_report_checked':True,'exact_source_and_tables_reconstructed':True,
            'independent_source_audit_passed':True,'independent_blank_startup_replayed':True,
            'startup_steps':startup['steps'],'native_sha256':summary['native_sha256'],
            'dense_sha256':summary['dense_sha256'],'source_sha256':summary['source_sha256'],
            'seconds':round(time.monotonic()-start,3),
            'scope':'Executable reconstruction and verification; mathematical PA proof in paper/report.pdf; no new proof-assistant kernel certificate.'}
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
