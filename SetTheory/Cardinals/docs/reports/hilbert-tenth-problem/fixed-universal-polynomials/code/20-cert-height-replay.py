#!/usr/bin/env python3
"""Portable Report46 replay of explicitly inspected independent checkers only.

Frozen packets are immutable. The sole source-root edit is made to a temporary
copy of the independently authored audit checker, never to upstream source.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
HEIGHT = 'square-product82-height-release-20261004'
HAUDIT = 'square-product82-height-independent-audit-20261004'
FREE = 'free83-even-rank-obstruction-20261004'
EXP = 'square-product82-height-expansion-20261004'
EAUDIT = 'square-product82-height-expansion-audit-20261004'
INV = 'square-product82-inverse-all-orders-20261004'
IAUDIT = 'square-product82-inverse-all-orders-audit-20261004'
PRIME = 'free83-prime-collapse-independent-audit-20261004'
R45 = 'square-product82-report45-release-20261004'

def need(ok, label):
    if not ok:
        raise RuntimeError(label)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(base):
    return {str(p.relative_to(base)):sha(p) for p in sorted(base.rglob('*')) if p.is_file()}

def same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x,y) for x,y in zip(a,b))
    return a == b

def validate_manifests(base):
    checked = 0
    for name, field in [(HEIGHT,'sha256'),(FREE,'files'),(PRIME,'files'),(EXP,'sha256'),(INV,'sha256'),(R45,'sha256')]:
        obj = json.loads((base/name/'MANIFEST.json').read_text())
        for rel, pin in obj[field].items():
            need(sha(base/name/rel)==pin, 'nested manifest '+name+'/'+rel)
            checked += 1
    for name in [HAUDIT, EAUDIT, IAUDIT]:
        for line in (base/name/'MANIFEST.sha256').read_text().splitlines():
            pin, rel = line.split(maxsplit=1)
            need(sha(base/name/rel)==pin, 'audit manifest '+name+'/'+rel)
            checked += 1
    return checked

def run():
    expected = json.loads((ROOT/'PACKET_INVENTORY.json').read_text())['sha256']
    before = inventory(ROOT/'packets')
    need(same(before, expected), 'complete frozen packet inventory')
    manifest_checks = validate_manifests(ROOT/'packets')
    outputs = {}
    with tempfile.TemporaryDirectory(prefix='report46-replay-') as tmp:
        work = Path(tmp)
        frozen = work/'packets'
        shutil.copytree(ROOT/'packets', frozen)
        need(same(inventory(frozen), expected), 'byte-identical temporary scientific packets')
        # This inspected checker hashes source data at an old absolute root.
        # Change exactly that root in a separate temporary executable copy.
        original = frozen/HAUDIT/'check_independent.py'
        literal = "ROOT = Path('/workspace/shared/square-product82-report45-release-20261004')"
        script_text = original.read_text()
        need(script_text.count(literal)==1, 'unique inspected path substitution')
        executable = work/'height_audit_portable.py'
        portable_root = "ROOT = Path(__file__).resolve().parent / 'packets' / " + repr(R45)
        executable.write_text(script_text.replace(literal, portable_root, 1))
        adaptation = {
            'frozen_sha256':sha(original),
            'executed_copy_sha256':sha(executable),
            'change':'One exact ROOT assignment redirected to temporary copied Report45 packet',
            'scientific_packet_modified':False,
        }
        jobs = [
            ('height_author', frozen/HEIGHT/'height_check.py', frozen/HEIGHT/'HEIGHT_CHECKS.json'),
            ('auxiliary_minimum', frozen/HEIGHT/'auxiliary_minimum_check.py', frozen/HEIGHT/'AUX_CHECKS.json'),
            ('height_negative_controls', frozen/HEIGHT/'check_tamper.py', frozen/HEIGHT/'TAMPER_CHECKS.json'),
            ('height_independent_audit', executable, frozen/HAUDIT/'receipt.normal.json'),
            ('free83_nonextension', frozen/FREE/'check_independent.py', frozen/FREE/'CHECKS.json'),
            ('analytic_author', frozen/EXP/'expansion_check.py', frozen/EXP/'EXPANSION_CHECKS.json'),
            ('analytic_independent_audit', frozen/EAUDIT/'check_expansion.py', frozen/EAUDIT/'receipt.normal.json'),
            ('all_orders_inverse_author', frozen/INV/'disk_check.py', frozen/INV/'DISK_CHECKS.json'),
            ('all_orders_inverse_audit', frozen/IAUDIT/'check_inverse.py', frozen/IAUDIT/'receipt.normal.json'),
            ('prime_rank_source_reconciliation', frozen/PRIME/'check_independent.py', frozen/PRIME/'CHECKS.json'),
            ('report_elementary_lemmas', ROOT/'check_report_math.py', ROOT/'checks/REPORT_MATH.normal.json'),
        ]
        for name, script, receipt in jobs:
            records = []
            for optimized in [False, True]:
                flags = ['-O'] if optimized else []
                proc = subprocess.run([sys.executable, *flags, str(script)], cwd=work,
                                      text=True, capture_output=True, timeout=240)
                need(proc.returncode==0, name+' failed: '+proc.stderr)
                parsed = json.loads(proc.stdout)
                need(parsed.get('status')=='PASS', name+' PASS status')
                need(same(parsed,json.loads(receipt.read_text())), name+' type-exact frozen receipt')
                need(proc.stdout.encode()==receipt.read_bytes(), name+' byte-identical frozen receipt')
                records.append({'mode':'optimized' if optimized else 'normal',
                                'returncode':proc.returncode,
                                'stdout_sha256':hashlib.sha256(proc.stdout.encode()).hexdigest(),
                                'stderr':proc.stderr})
            need(records[0]['stdout_sha256']==records[1]['stdout_sha256'], name+' modes agree')
            outputs[name]=records
        need(same(inventory(frozen), expected), 'temporary frozen packets unchanged after replay')
    need(same(inventory(ROOT/'packets'),before), 'release scientific packets unchanged')
    return {
        'status':'PASS','packet_files':len(expected),'nested_manifest_checks':manifest_checks,
        'scientific_packets_unchanged':True,'portable_path_adaptation':adaptation,
        'execution':outputs,'upstream_repository_code_executed':False,
        'compiler_recipes_executed':False,'saved_arithmetic_schedules_executed':False,
        'full_genuine_witness_tuple_materialized':False,
        'scope':'Bounded corroboration and byte authentication; the manuscript proves unbounded claims.',
    }

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args=parser.parse_args()
    result=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(result)
    print(result,end='')

if __name__=='__main__':
    main()
