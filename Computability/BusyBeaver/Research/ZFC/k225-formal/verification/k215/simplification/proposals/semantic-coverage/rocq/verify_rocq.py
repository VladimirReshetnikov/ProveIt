#!/usr/bin/env python3
"""Fresh, local Coq/Rocq check of the abstract core and exact ThmDom client.

This is a seven-module calculus slice, not the binary-machine/ZFC endpoint.
Coq 8.18 uses only an import-prefix compatibility edit in private build copies.
Rocq 9 accepts the source imports as supplied.  No source axiom is introduced.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import time
import generate_rocq_core

ROOT = Path(__file__).resolve().parent
PIN = '2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(argv, log):
    start = time.perf_counter()
    p = subprocess.run(argv, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(p.stdout)
    result = dict(argv=[str(x) for x in argv], exit_code=p.returncode,
                  seconds=time.perf_counter() - start, log_sha256=sha(log))
    if p.returncode:
        raise RuntimeError(f'{argv}: {p.stdout}')
    return result, p.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, default=ROOT / 'verification')
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqchk', default='coqchk')
    ap.add_argument('--baseline', action='store_true', help='compile old replay for one-run comparison')
    args = ap.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise RuntimeError('Use a fresh, empty output directory: ' + str(out))
    out.mkdir(parents=True, exist_ok=True)
    version = subprocess.check_output([args.coqc, '--version'], text=True).strip()
    is8 = 'version 8.' in version
    generated = generate_rocq_core.render(ROOT / 'derivation_core.txt')
    if generated.encode() != (ROOT / 'DominatedImplication58.v').read_bytes():
        raise RuntimeError('The checked generic proof must reproduce byte-for-byte.')
    order = ['K230S/KCode230', 'K230L/Codes230', 'K215F/Codes222',
             'K215F/Thm222', 'K215F/DominatedImplication58',
             'K215F/DomRho8', 'K215F/ThmDom']
    receipt = dict(repository_pin=PIN, scope='calculus slice through K215F.ThmDom',
                   full_endpoint_rebuilt=False, compiler=version,
                   compatibility='From Stdlib Require -> From Coq Require' if is8 else 'none',
                   derivation_sha256=sha(ROOT / 'derivation_core.txt'), lanes={})
    lanes = ['proposed'] + (['baseline'] if args.baseline else [])
    for lane in lanes:
        work = out / lane
        for namespace in ['K230S', 'K230L', 'K215F']:
            (work / namespace).mkdir(parents=True)
        flags = sum((['-Q', str(work / ns), ns] for ns in ['K230S', 'K230L', 'K215F']), [])
        modules = {}
        lane_order = [p for p in order if lane == 'proposed' or not p.endswith('/DominatedImplication58')]
        for module in lane_order:
            src = (ROOT / 'DominatedImplication58.v' if module.endswith('/DominatedImplication58')
                   else ROOT / 'baseline/DomRho8.v' if lane == 'baseline' and module.endswith('/DomRho8')
                   else ROOT / 'source' / (module + '.v'))
            target = work / (module + '.v')
            data = src.read_bytes()
            if is8:
                data = data.replace(b'From Stdlib Require', b'From Coq Require')
            target.write_bytes(data)
            result, stdout = run([args.coqc, *flags, str(target)], target.with_suffix('.log'))
            result.update(source_sha256=sha(src), compiled_source_sha256=sha(target),
                          object_sha256=sha(target.with_suffix('.vo')),
                          object_bytes=target.with_suffix('.vo').stat().st_size,
                          source_bytes=src.stat().st_size,
                          source_lines=len(src.read_text().splitlines()),
                          closed_reports=stdout.count('Closed under the global context'))
            if module.endswith('/DomRho8') or module.endswith('/ThmDom'):
                if result['closed_reports'] < 1 or 'Axioms:' in stdout:
                    raise RuntimeError('Nonclosed or absent assumption report: ' + module)
            if module.endswith('/DominatedImplication58'):
                if result['closed_reports'] != 4 or 'Axioms:' in stdout:
                    raise RuntimeError('Generic core assumption audit failed')
            modules[module] = result
            print(lane, module, 'PASS', flush=True)
        check, stdout = run([args.coqchk, '-silent', '-o', *flags, 'K215F.ThmDom'], work / 'coqchk.log')
        if '* Axioms: <none>' not in stdout or 'unsafe (co)fixpoints: <none>' not in stdout:
            raise RuntimeError('Unexpected recursive kernel context: ' + stdout)
        item = dict(modules=modules, coqchk=check)
        if lane == 'proposed':
            probe = work / 'CheckTypes.v'
            shutil.copyfile(ROOT / 'CheckTypes.v', probe)
            check_types, stdout = run([args.coqc, *flags, str(probe)], work / 'types.log')
            if stdout.count('Closed under the global context') != 1 or 'Axioms:' in stdout:
                raise RuntimeError('Public API check failed')
            check_types.update(source_sha256=sha(probe), object_sha256=sha(probe.with_suffix('.vo')))
            item['public_api_probe'] = check_types
        receipt['lanes'][lane] = item
    receipt['status'] = 'PASS_CLOSED_CALCULUS_SLICE'
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], flush=True)


if __name__ == '__main__':
    main()
