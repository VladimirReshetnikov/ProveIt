#!/usr/bin/env python3
"""Audit the 250 -> 248 -> 247 reduction and every symbolic instruction.

The --prior directory is the independently audited zfc-prefix250-report package.
That package's
attributed symbolic executor is reused under its mathematical box contracts,
with the selector contract justified for the changed row by the independent
finite transition identities checked here and the unbounded induction in
report.tex, Sections 3--5.  No bounded tape sample is used as the reason why the
deleted states are absent from future runtime.

Example:
  python3 -B verify_runtime247.py --reference250 /path/to/reference250 --output evidence
"""
import argparse
from collections import Counter
import hashlib
import importlib
import json
from pathlib import Path
import sys
import re

PREFIX250_OLD_SHA = 'fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43'
PROGRAM_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
AFFINE_SHA = '8c029463048fb544608dec93b6bba772ab21250377b8fbb2763cbab4f1ee35e7'
INDUCTION_SHA = '3484c0be3aaf34bd3677c0cc727eaba8655efd358f9338192a88be0d9c89ad8d'
SELECTORS = (60, 44, 31, 56, 38, 40, 28, 64, 69)
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(table, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n'
        for (q, b), (w, d, t) in sorted(table.items()))).encode('ascii')


def construct(baseline_path):
    raw = baseline_path.read_bytes()
    assert digest(raw) == PREFIX250_OLD_SHA
    baseline = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        key = int(q), int(b)
        assert key not in baseline
        baseline[key] = int(w), d, int(t)
    assert len(baseline) == 500

    # The only incoming edge into {1,3}, apart from its internal edges, is
    # (0,0).  No register-macro proof below uses that branch.
    incoming = sorted((q, b, w, d, t)
                      for (q, b), (w, d, t) in baseline.items()
                      if t in (1, 3) and q not in (1, 3))
    assert incoming == [(0, 0, 1, 'L', 1)]
    patched = {k: v for k, v in baseline.items() if k[0] not in (1, 3)}
    patched[0, 0] = (1, 'L', 2)
    assert len(patched) == 496
    assert not any(t in (1, 3) for w, d, t in patched.values())

    # Arbitrary-tape, one-step quotient: the two rows agree before redirecting
    # their sole external incoming edge. This check is independent of runtime.
    assert patched[0, 0] == patched[20, 0] == (1, 'L', 2)
    assert patched[0, 1] == patched[20, 1] == (0, 'L', 2)
    image = lambda q: 20 if q == 0 else q
    candidate = {(q, b): (w, d, image(t))
                 for (q, b), (w, d, t) in patched.items() if q != 0}
    for (q, b), (w, d, t) in patched.items():
        assert candidate[image(q), b] == (w, d, image(t))
    assert len(candidate) == 494
    states = {q for q, b in candidate}
    assert len(states) == 247 and 97 in states
    assert states == set(range(254)) - {0, 1, 3, 5, 8, 43, 59, 85} | {255}
    assert set(candidate) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in candidate.values()} - states == {254}
    old = encode(candidate, 97)
    order = [97] + sorted(states - {97})
    mapping = {q: j for j, q in enumerate(order)}
    canon = {(mapping[q], b): (w, d, 247 if t == 254 else mapping[t])
             for (q, b), (w, d, t) in candidate.items()}
    canonical = encode(canon, 0)
    return baseline, patched, candidate, mapping, old, canonical


def audit_macro_rows(baseline, candidate):
    # Each selector consumes one separator and then scans the corresponding
    # positive one-run. Its index drops at every consumed zero, so it reaches
    # q=0 precisely on the first one of the selected block. This row alone is
    # changed to q=20, with identical action on the guaranteed one.
    for r, q in enumerate(SELECTORS):
        assert candidate[q, 1] == baseline[q, 1] == (1, 'R', q)
        target = SELECTORS[r - 1] if r else 20
        assert candidate[q, 0] == (0, 'R', target)
        assert baseline[q, 0] == (0, 'R', SELECTORS[r - 1] if r else 0)
    assert candidate[20, 1] == baseline[0, 1] == (0, 'L', 2)
    # After erasing the selected first one, skip0 returns in q=2 before
    # reading the external context. For r>0, q=2 first crosses the selected
    # separator, q=4 scans left over a preceding positive one-run, and q=6
    # enters each next previous positive one-run (if any). At the initial
    # separator it returns q=6 before reading the external context.
    marking_return_rows = ((2, 0), (2, 1), (4, 0), (4, 1), (6, 1))
    for row in marking_return_rows:
        assert candidate[row] == baseline[row]
    assert candidate[2, 0] == (0, 'L', 2)
    assert candidate[2, 1] == (1, 'L', 4)
    assert candidate[4, 0] == (0, 'L', 6)
    assert candidate[4, 1] == (1, 'L', 4)
    assert candidate[6, 1] == (1, 'L', 4)

    # These form a closed set of internal arithmetic states for all three
    # proved prefix-carry lemmas.  State48's next exterior transition is
    # executed by the symbolic instruction checker. The same applies to112
    # at the old left boundary on a zero decrement.
    arithmetic = {73, 83, 95, 109, 75, 255, 97, 112, 131, 63, 48}
    for q in arithmetic:
        for b in (0, 1):
            assert candidate[q, b] == baseline[q, b]
    return dict(
        status='PASS', selectors=list(SELECTORS),
        changed_selector_row=[60, 0, 0, 'R', 20],
        marked_one_action=[20, 1, 0, 'L', 2],
        inherited_arithmetic_states=sorted(arithmetic),
        mathematical_premise='Each plain register block is 0 followed by a '
            'nonempty finite run of ones; the selected index is below 9; '
            'there is at least one spare block.',
        scope='Finite row identities supporting unbounded induction; '
            'not a bounded register-value experiment.')


class ObservedTable(dict):
    def __init__(self, table):
        super().__init__({(str(q), b): (w, d, str(t))
                          for (q, b), (w, d, t) in table.items()})
        self.used = Counter()

    def __getitem__(self, key):
        assert key[0] not in ('0', '1', '3'), ('deleted state', key)
        self.used[key] += 1
        return super().__getitem__(key)


def program_sites(program):
    """Exhaustively parse the complete source, checking all residue and nodes."""
    raw = program.read_bytes()
    assert digest(raw) == PROGRAM_SHA
    source = raw.decode('ascii').split('Definition p254_tab', 1)[1]
    body = source.split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    pattern = r'\((' + edge + r'),\s*(' + edge + r')\)'
    rows = re.findall(pattern, body)
    assert len(rows) == 6459
    assert not re.sub(r'[\s;]', '', re.sub(pattern, '', body))
    seen, sites = set(), []

    def visit(node, prefix, active):
        assert node not in active and 0 <= node < len(rows)
        seen.add(node)
        for bit, term in enumerate(rows[node]):
            kind, *arg = term.split()
            value = int(arg[0]) if arg else None
            pc = prefix + str(bit)
            if kind == 'CN':
                visit(value, pc, active | {node})
            else:
                if kind in ('CI', 'CD'):
                    assert value in range(9)
                    value = PHYSICAL[value]
                sites.append((pc, kind, value))
    visit(0, '', set())
    assert seen == set(range(6459)) and len(sites) == 6460
    assert len({pc for pc, kind, value in sites}) == 6460
    return sites


def increment(path):
    return None if '0' not in path else path[:path.rindex('0')] + '1'


def strip(path, bit, count):
    while path and count:
        count -= path[-1] == bit
        path = path[:-1]
    return path


def audit_all_sites(prior, program, table, certificate):
    sys.path.insert(0, str(prior / 'code'))
    assert digest((prior / 'code/affine_engine.py').read_bytes()) == AFFINE_SHA
    affine = importlib.import_module('affine_engine')
    sites = program_sites(program)
    table = ObservedTable(table)
    totals = Counter()
    cases, minimum, maximum = 0, 10**9, 0
    with certificate.open('w', encoding='utf-8') as record:
        for site, (pc, op, r) in enumerate(sites):
            for zero in ((True, False) if op == 'CD' else (None,)):
                branch = (r, zero) if op == 'CD' else None
                if op == 'CI' or op == 'CD' and not zero:
                    successor = increment(pc)
                elif op == 'CD':
                    successor = increment(strip(pc, '0', 1))
                elif op == 'CB':
                    successor = increment(strip(pc, '0', r))
                elif op == 'CC':
                    successor = strip(pc, '1', r)
                else:
                    successor = ''
                effect = ('inc', r) if op == 'CI' else (
                    ('dec', r) if op == 'CD' and not zero else None)
                extra = int(op == 'CD' and not zero)
                right = ([('r', 0, 1, 41 + extra), ('b', 1),
                          ('box', ('plain', effect))] if successor is None else
                         [('b', int(b)) for b in successor] +
                         [('r', 0, 1, 40 + extra - len(successor)), ('b', 1),
                          ('box', ('plain', effect))])
                target = affine.canon([('b', 1)], right)
                rules, literal = affine.run(table, pc, branch, target,
                                             halt=op == 'CH', fuel=1000)
                totals.update(rules)
                cases += 1
                minimum = min(minimum, literal)
                maximum = max(maximum, sum(rules.values()))
                record.write(json.dumps(dict(site=site, pc=pc, operation=op,
                    physical_register_or_control_count=r, zero_guard=zero,
                    successor_pc=None if op == 'CH' else successor,
                    halt=op == 'CH', literal_progress=literal,
                    rules=dict(rules)), separators=(',', ':')) + '\n')
    assert cases == 8391 and minimum > 0
    return dict(status='PASS', leaf_sites=len(sites), guarded_cases=cases,
                minimum_literal_progress=minimum,
                maximum_symbolic_rules=maximum, rule_totals=dict(totals),
                observed_rows=[dict(state=int(q), read=b, lookups=count)
                               for (q, b), count in sorted(table.used.items(),
                                     key=lambda kv: (int(kv[0][0]), kv[0][1]))],
                deleted_state_lookups=0,
                certificate_sha256=digest(certificate.read_bytes()),
                scope='Each accepted symbolic case holds for all n>=0, all '
                    'nine register values satisfying its guard, and every '
                    'finite nonempty spare suffix, under the proved macro '
                    'contracts and symbolic-rule soundness argument.')


def audit_induction_templates(prior, candidate, output):
    """Replay the audited 250 package's unbounded induction templates on 247."""
    path = prior / 'code/check_macro_inductions.py'
    assert path.exists(), ('The independent audit250 package is required: '
                           'its unbounded induction checker is absent.', str(path))
    assert digest(path.read_bytes()) == INDUCTION_SHA
    sys.path.insert(0, str(prior / 'code'))
    checker = importlib.import_module('check_macro_inductions')

    class MacroTable(dict):
        def __init__(self, table):
            super().__init__(table)
            self.rows = Counter()

        def __getitem__(self, key):
            assert key[0] not in (0, 1, 3), ('deleted macro state', key)
            self.rows[key] += 1
            return super().__getitem__(key)

    table = MacroTable(candidate)
    checker.TABLE = table
    checker.prove_blocks()
    word = checker.prove_word_identity()
    macros = checker.prove_macros()
    marks = checker.prove_marks()
    assert len(marks) == 9 and len(macros) == 3
    proof = dict(status='PASS', block_theorems=list(checker.BLOCK_PROOFS.values()),
                 word_identity=word, macro_theorems=macros, mark_theorems=marks,
                 observed_rows=[dict(state=q, read=b, lookups=count)
                      for (q, b), count in sorted(table.rows.items())],
                 deleted_state_lookups=0,
                 scope='Universal unary and structural finite-list induction '
                       'templates executed against the exact 247 table; '
                       'not a proof-assistant kernel endpoint.')
    output.write_text(json.dumps(proof, indent=2) + '\n', encoding='utf-8')
    return dict(status='PASS', block_theorems=len(checker.BLOCK_PROOFS),
                arithmetic_macros=3, selector_macros=9,
                deleted_state_lookups=0, certificate_sha256=digest(output.read_bytes()))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prior', '--reference250', dest='prior', type=Path, required=True)
    ap.add_argument('--baseline250', type=Path,
                    help='Original-label frozen 250 table (default: reference250/machine).')
    ap.add_argument('--candidate247', type=Path,
                    help='If supplied, verify these exact original-label 247 bytes.')
    ap.add_argument('--program', type=Path,
                    help='Complete literal Prog254.v (default: reference250/sources).')
    ap.add_argument('--output', type=Path, default=Path('evidence'))
    args = ap.parse_args()
    if not __debug__:
        raise SystemExit('Run without -O; assertions are part of the checker.')
    args.prior = args.prior.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    baseline_path = args.baseline250 or args.prior / 'machine/zfc_prefix250_old.tm'
    program = args.program or args.prior / 'sources/Prog254.v'
    baseline, patched, candidate, mapping, old, canonical = construct(baseline_path)
    if args.candidate247:
        assert args.candidate247.read_bytes() == old, 'Candidate bytes differ from exact construction.'
    (args.output / 'zfc_prefix247_old.tm').write_bytes(old)
    (args.output / 'zfc_prefix247.tm').write_bytes(canonical)
    macro = audit_macro_rows(baseline, candidate)
    inductions = audit_induction_templates(args.prior, candidate,
                             args.output / 'macro_inductions247.json')
    runtime = audit_all_sites(args.prior, program, candidate,
                             args.output / 'runtime247_cases.jsonl')
    result = dict(status='PASS', source250_sha256=PREFIX250_OLD_SHA,
                  patched248_sha256=digest(encode(patched, 97)),
                  candidate247_old_sha256=digest(old),
                  candidate247_canonical_sha256=digest(canonical),
                  canonical_start=0, canonical_halt=247,
                  canonical_dispatch=mapping[96], working_states=247,
                  removed_original_labels=[0, 1, 3],
                  changed_retained_row=[60, 0, 0, 'R', 20],
                  quotient_check_rows=len(patched),
                  macro_row_audit=macro, induction_templates=inductions,
                  program_sha256=digest(program.read_bytes()), runtime=runtime,
                  affine_engine_sha256=AFFINE_SHA,
                  induction_engine_sha256=INDUCTION_SHA,
                  proof_boundary='Conventional unbounded mathematical proof '
                      'and exhaustive symbolic checks; not a new kernel-checked '
                      'Lean or Rocq endpoint. Bootstrap checked separately.')
    (args.output / 'runtime247_result.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8')
    summary = {k: v for k, v in result.items() if k not in ('runtime',)}
    summary['runtime_summary'] = {k: v for k, v in runtime.items()
                                  if k != 'observed_rows'}
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
