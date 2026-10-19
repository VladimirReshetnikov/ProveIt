#!/usr/bin/env python3
"""Finite, explicitly bounded diagnostic for one more scanner contraction.

This does not certify a reduction. It records contexts violating the sufficient
three-zero local identity while replaying exact source instructions.
"""
from pathlib import Path
from hashlib import sha256
import argparse, collections, importlib.util, json, time

ROOT = Path(__file__).resolve().parent
ARCHIVE = ROOT.parent
HELPER = ROOT / 'scanner_support/check_combined243_literal.py'
spec = importlib.util.spec_from_file_location('literal', HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError(f'Cannot load the bundled literal helper: {HELPER}')
lit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lit)

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not run with Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, default=ARCHIVE / 'reference/combined243',
                    help='directory containing the pinned inherited combined243 table')
    ap.add_argument('--sites', type=Path, default=ARCHIVE / 'machine/sites_logical.json',
                    help='the unchanged combined243 logical source-site list')
    ap.add_argument('--output', type=Path, default=ROOT / 'scanner-probe-rerun.json')
    ap.add_argument('--step-limit', type=int, default=20000,
                    help='maximum literal transitions per finite source/guard fixture')
    a = ap.parse_args()
    if a.step_limit < 1:
        ap.error('--step-limit must be positive')
    tp = a.candidate / 'zfc_combined243_old.tm'
    if not tp.exists(): tp = a.candidate / 'machine_old.tm'
    table_sha = sha256(tp.read_bytes()).hexdigest()
    sites_sha = sha256(a.sites.read_bytes()).hexdigest()
    assert table_sha == lit.TABLE_SHA, 'The table is not the pinned combined243 baseline.'
    assert sites_sha == lit.SITES_SHA, 'The sites are not the pinned combined243 source.'
    table = lit.read_table(tp)
    sites = json.loads(a.sites.read_text())
    seen = collections.Counter()
    bad = []
    serial = 0
    ticks = 0
    start = time.monotonic()
    for index, (pc, op, r) in enumerate(sites):
        for zero in ((True, False) if op == 'CD' else (None,)):
            logical = [(17 * serial + 11 * j + 3 * index + 7) % 23 for j in range(9)]
            if op == 'CD': logical[r] = 0 if zero else 1 + (13 * serial + 7 * r) % 23
            spares = [(serial + 2 * j + 3) % 13 for j in range(1 + serial % 5)]
            span = 64 + 17 * (serial % 3)
            ones = lit.frame(0, pc, span, logical, spares)
            output, tail, extra, overflow = logical.copy(), spares.copy(), 0, False
            if op == 'CI': output[r] += 1; tail.append(1); successor, overflow = lit.increment(pc)
            elif op == 'CD' and not zero: output[r] -= 1; extra = 1; successor, overflow = lit.increment(pc)
            elif op == 'CD': successor, overflow = lit.increment(lit.strip(pc, '0', 1))
            elif op == 'CB': successor, overflow = lit.increment(lit.strip(pc, '0', r))
            elif op == 'CC': successor = lit.strip(pc, '1', r)
            else: successor = ''
            endhead = -int(overflow)
            expected = None if op == 'CH' else lit.frame(endhead, successor, span + extra + int(overflow), output, tail)
            q, head = 96, 0
            contexts = []
            for steps in range(1, a.step_limit + 1):
                key = q, int(head in ones)
                if key == (41, 0):
                    ctx = ''.join(str(int(head - j in ones)) for j in range(5))
                    seen[ctx] += 1
                    if not ctx.startswith('000'):
                        contexts.append(dict(step=steps, head=head, bits=ctx))
                w, direction, q = table[key]
                if w: ones.add(head)
                else: ones.discard(head)
                head += direction
                if op == 'CH' and q == 254: break
                if op != 'CH' and q == 96 and head == endhead and ones == expected: break
            else: raise AssertionError(('baseline failed', index, pc, op, r, zero))
            ticks += steps
            if contexts: bad.append(dict(index=index, pc=pc, op=op, r=r, zero=zero, contexts=contexts))
            serial += 1
    out = dict(status='FINITE_SCANNER_CONTRACTION_DIAGNOSTIC', cases=serial, literal_steps=ticks,
               bad_case_count=len(bad), context_counts=dict(seen), bad_cases=bad, seconds=time.monotonic()-start,
               table_sha256=table_sha, sites_sha256=sites_sha,
               helper_sha256=sha256(HELPER.read_bytes()).hexdigest(), step_limit=a.step_limit,
               scope='Finite deterministic fixtures for every source/guard case; records failures of a sufficient local contraction premise, not an impossibility theorem.')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k:v for k,v in out.items() if k!='bad_cases'}, indent=2))

if __name__ == '__main__': main()
