#!/usr/bin/env python3
"""Render the generic dominated-implication core and unchanged Nat adapter.

Read the exact attributed 52-step Lean rendering and derivation as inert data.
Replace four local numeric fillers by reflexive terms and five truth arguments
by an arbitrary seed; check every explicit inference as free constructor syntax.
No original renderer/search is imported or executed. Lean remains the kernel.
The maintained CLI is --out LEAN_ROOT or --check (default).
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
TEMPLATES = HERE / 'dominated_implication_templates'
DEFAULT_OUT = (HERE / '../../../Lean').resolve()
SOURCE = 'verification/k215/simplification/phase9/upstream-merge/source-review/DomRho8.4fdc.lean'
INPUT_PINS = {
    SOURCE: 'c0c9eb59ad7076b7753b1a5d7d690e26f96936229fdd875dad926bb210d6fb13',
    'rho8cd/derivation.txt': '3cbf1ed6114ff44da836578e58c9d5308d347a8b1d664e83c1983e800d285776',
}
TEMPLATE_PINS = {
    'adapter.txt': '8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378',
    'core-prefix.txt': '22d93bd8644f3288ea0d490e6d7ce66e03366bf3a8e0397902f3d1ad71368139',
    'core-suffix.txt': 'c31f1521758c3b95d3f06ade403248cdb65e024ba7b0f0479bd29560fc43d973',
}
EXPECTED_CORE = '5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f'

if not __debug__:
    raise RuntimeError('Producer validation requires normal Python (without -O)')

def sha(b):
    return hashlib.sha256(b).hexdigest()

def tokens(s):
    return re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|τ|≼|[()]', s)

def imp(a, b):
    return ('imp', a, b)

def subst(t, env):
    return tuple(subst(x, env) for x in t) if isinstance(t, tuple) else env.get(t, t)

class Reader:
    def __init__(self, s, env=None, facts=None):
        self.ts = tokens(s)
        self.i = 0
        self.env = env or {}
        self.facts = facts or {}

    def pop(self, want=None):
        x = self.ts[self.i]
        self.i += 1
        assert want is None or x == want, (want, x, self.ts[self.i:])
        return x

    def group(self, fn):
        if self.ts[self.i] == '(':
            self.pop('(')
            out = fn()
            self.pop(')')
            return out
        return fn()

    def term(self):
        return self.group(self.atom)

    def atom(self):
        x = self.pop()
        if x in ('wim', 'L.imp'):
            return imp(self.term(), self.term())
        assert re.fullmatch(r'v\d+|[a-z]|τ|_', x), x
        return self.env.get(x, x)

    def guard(self, expected):
        def core():
            name = self.pop()
            u, a = expected
            if name == 'L.refl':
                val = self.term()
                assert u == a and (val == '_' or val == a), (name, expected, val)
            elif name == 'le_l':
                y = self.term()
                assert isinstance(a, tuple) and a[0] == 'imp' and a[2] == y
                self.guard((u, a[1]))
            elif name == 'le_r':
                x = self.term()
                assert isinstance(a, tuple) and a[0] == 'imp' and a[1] == x
                self.guard((u, a[2]))
            else:
                assert self.facts[name] == expected, (name, self.facts, expected)
            return expected
        return self.group(core)

    def proof(self):
        def core():
            name = self.pop()
            if name == 'h.mp':
                major, minor = self.proof(), self.proof()
                assert isinstance(major, tuple) and major[0] == 'imp'
                assert major[1] == minor, ('MP mismatch', major[1], minor)
                counts['mp'] += 1
                return major[2]
            if name == 'h.rho8':
                a, b, c, u = [self.term() for _ in range(4)]
                self.guard((u, a))
                counts['restricted_rows'] += 1
                return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
            if name == 'h.truth':
                counts['seed_uses'] += 1
                return 'τ'
            if name == 'under_antecedent':
                assert name in schemas
                self.pop('h')
                z, xy = self.term(), self.proof()
                assert isinstance(xy, tuple) and xy[0] == 'imp'
                return imp(imp(z, xy[1]), imp(z, xy[2]))
            if name in schemas:
                self.pop('h')
                args, conclusion, guards = schemas[name]
                env = dict(zip(args, [self.term() for _ in args]))
                for guard in guards:
                    self.guard(subst(guard, env))
                return subst(conclusion, env)
            assert name in self.facts, name
            return self.facts[name]
        return self.group(core)

    def end(self):
        assert self.i == len(self.ts), self.ts[self.i:]

def audit(text):
    global schemas, counts
    matches = list(re.finditer(r'private theorem (d\d+|under_antecedent|insert_middle|application_contract|application_transport|repeated_antecedent|composition_seed)\b', text))
    schemas = {}
    counts = dict(mp=0, restricted_rows=0, seed_uses=0)
    checked = []
    for index, match in enumerate(matches):
        name = match.group(1)
        end = matches[index+1].start() if index+1 < len(matches) else text.index('\nend\n', match.end())
        block = text[match.end():end]
        header, body = block.split(':=', 1)
        body = re.sub(r'/--.*?-/\s*$', '', body, flags=re.S).strip()
        args = []
        for group in re.findall(r'\(([^():]+) : A\)', header):
            args.extend(group.split())
        guard_text = re.findall(r'\(hb\d+ : (.*?)\)\s*:', header, re.S)
        guards = []
        for g in guard_text:
            r = Reader(g)
            u = r.term(); r.pop('≼'); a = r.term(); r.end()
            guards.append((u, a))
        # The conclusion starts at the final colon directly preceding T.
        conclusion_text = re.split(r':\s*T\s+', header)[-1]
        r = Reader(conclusion_text); conclusion = r.term(); r.end()
        facts = {f'hb{i}': g for i, g in enumerate(guards)}
        if name == 'under_antecedent':
            facts['hxy'] = imp('x', 'y')
        if name == 'composition_seed':
            assert body.startswith('by\n  have happ : T ')
            local, exact = body[len('by\n  have happ : T '):].split('\n  exact ', 1)
            local_type, local_proof = local.split(':=', 1)
            r = Reader(local_type); local_formula = r.term(); r.end()
            r = Reader(local_proof); actual_local = r.proof(); r.end()
            assert local_formula == actual_local
            facts['happ'] = local_formula
            body = exact
        r = Reader(body, facts=facts)
        actual = r.proof(); r.end()
        assert actual == conclusion, (name, actual, conclusion)
        schemas[name] = (args, conclusion, guards)
        checked.append(name)

    assert checked[:52] == [f'd{i}' for i in range(1, 53)]
    assert len(checked) == 58
    assert counts['seed_uses'] == 5
    assert not re.search(r'\b0\b|Nat\.|sorry|axiom |native_decide', text)
    assert subst(schemas['d52'][1], dict(zip(schemas['d52'][0], ['c','u','a','b']))) == imp(imp(imp('c','u'),'a'),imp(imp('a','c'),imp('b','c')))
    return checked, counts

def pinned(path, expected):
    raw = path.read_bytes()
    assert sha(raw) == expected, 'input bytes differ: ' + str(path)
    return raw.decode('utf-8')

def generate():
    inputs = {name: pinned(HERE / name, pin) for name, pin in INPUT_PINS.items()}
    templates = {name: pinned(TEMPLATES / name, pin) for name, pin in TEMPLATE_PINS.items()}
    source = inputs[SOURCE]
    body = source[source.index('private theorem d1 '):source.index('/-- Every rho8 instance')]
    fillers = {3: '(wim v1 v2)', 7: '(wim (wim v1 v2) v3)', 10: '(wim v1 v2)', 16: 'v0'}
    seeds = [4, 9, 13, 18, 22]
    for number, filler in fillers.items():
        match = re.search(r'(private theorem d%d .*?)(?=private theorem|\Z)' % number, body, re.S)
        block = match.group(1)
        assert len(re.findall(r'\b0\b', block)) == 2 and block.count('(Nat.zero_le _)') == 1
        block = re.sub(r'\b0\b', lambda _: filler, block).replace('(Nat.zero_le _)', '(L.refl _)')
        body = body[:match.start()] + block + body[match.end():]
    for number in seeds:
        match = re.search(r'(private theorem d%d .*?)(?=private theorem|\Z)' % number, body, re.S)
        block = match.group(1)
        assert len(re.findall(r'\b0\b', block)) == 1 and block.count('h.truth') == 1
        body = body[:match.start()] + re.sub(r'\b0\b', 'τ', block) + body[match.end():]
    body = body.replace(': Nat', ': A').replace(' ≤ ', ' ≼ ').replace('Nat.le_refl', 'L.refl')
    core = templates['core-prefix.txt'] + body + templates['core-suffix.txt']
    adapter = templates['adapter.txt']
    checked, counts = audit(core)
    assert sha(core.encode()) == EXPECTED_CORE, 'generated core differs from reviewed source'
    metrics = {
        'base_commit': '4fdc59197a45a6beb7e5a4ae7109fd13477b1d17',
        'input_raw_sha256': INPUT_PINS, 'template_raw_sha256': TEMPLATE_PINS,
        'generic_sha256': sha(core.encode()), 'adapter_sha256': sha(adapter.encode()),
        'generic_bytes': len(core.encode()), 'adapter_bytes': len(adapter.encode()),
        'combined_bytes': len((core + adapter).encode()),
        'generic_lines': len(core.splitlines()), 'adapter_lines': len(adapter.splitlines()),
        'numbered_helpers': 52, 'compatibility_helpers': 6,
        'reflexive_fillers': fillers, 'arbitrary_seed_detachments': seeds,
        'checked_private_lemmas': checked, 'counts': counts,
        'certificate_status': '58 explicit inference bodies and all relation guards checked; no zero normalization',
        'kernel_status': 'external build receipts; this Python script is not a proof kernel',
    }
    return core, adapter, metrics

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='write repo-layout Lean files under this directory')
    parser.add_argument('--check', action='store_true', help='check exact delivered source bytes')
    args = parser.parse_args()
    core, adapter, metrics = generate()
    target = (args.out or DEFAULT_OUT) / 'BusyBeaver/ZFC'
    outputs = {'DominatedImplication.lean': core, 'DomRho8.lean': adapter}
    if args.check or args.out is None:
        for name, text in outputs.items():
            assert (target / name).read_bytes() == text.encode(), 'maintained source bytes differ: ' + name
    else:
        target.mkdir(parents=True, exist_ok=True)
        for name, text in outputs.items():
            (target / name).write_bytes(text.encode())
        (args.out / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    print(json.dumps(metrics, indent=2))

if __name__ == '__main__':
    main()
