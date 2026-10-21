#!/usr/bin/env python3
"""Read-only free-constructor audit of the explicit scratch inference terms.

This is a source audit, not Lean elaboration or a trusted proof checker.
No implication terms are normalized, quotiented, or identified with truth.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'candidate/DominatedImplication.lean'

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

text = SOURCE.read_text()
baseline = (ROOT / 'inputs/DominatedImplication.baseline.lean').read_text()
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
    conclusion_text = re.search(r':\s*T\s+(.*)', header, re.S).group(1)
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

def header_of(s, name):
    return re.search(r'(?m)^theorem '+name+r'\b.*?:=', s, re.S).group(0)

for name in ['rho8_all', 'composition', 'lift_right']:
    assert header_of(text, name) == header_of(baseline, name), name
start = 'universe v\n'
end = '\nprivate theorem b1 '
base_prefix = baseline[baseline.index(start):baseline.index(end)]
new_prefix = text[text.index(start):text.index('\nprivate theorem d1 ')]
assert base_prefix == new_prefix
record = {
    'status': 'PASS_SOURCE_ONLY_FREE_CONSTRUCTOR_AUDIT',
    'source_sha256': sha(SOURCE.read_bytes()),
    'checked_private_lemmas': checked,
    'counts': counts,
    'matching': 'syntactic free implication constructors only; no zero collapse or semantic quotient',
    'public_headers_equal': ['rho8_all','composition','lift_right'],
    'language_restricted_rho8_withseed_section_prefix_exact': True,
    'kernel_execution': False,
    'supplied_producer_execution': False,
}
print(json.dumps(record, indent=2))
