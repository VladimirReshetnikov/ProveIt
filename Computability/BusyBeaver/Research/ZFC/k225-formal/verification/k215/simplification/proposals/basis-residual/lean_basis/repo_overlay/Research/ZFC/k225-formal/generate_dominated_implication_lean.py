#!/usr/bin/env python3
"""Check the pinned 58-step core, two-step S extension, and emit the Lean pair.

Only inert UTF-8 source/ancestry data is read; no upstream renderer is imported
or executed. Explicit MP and relation guards are checked as free constructor
syntax. This fixed-input diagnostic is not a proof kernel. The maintained CLI
is --out LEAN_ROOT or --check (default).
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = (HERE / '../../../Lean').resolve()
SOURCE = 'verification/k215/simplification/phase10/upstream-merge/source-review/inputs/DominatedImplication.upstream.lean'
ADAPTER = 'dominated_implication_templates/adapter.txt'
BASIS = 'dominated_implication_templates/basis.txt'
INPUT_PINS = {
    SOURCE: 'e91f5cf8e6583ba73221362bc21438b70897a8808329886dc615c166bb16edd7',
    'rho8cd/derivation_core.txt': 'f0a2e60d3574615aefa8ce987e783b69a89dd95516dc7238caa569b4a938f116',
    ADAPTER: '8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378',
    BASIS: 'bcb485a7c57e3bf552be99771570fe52193d3e92c0b81d3d0d0d1163e1558723',
}
EXPECTED_CORE = 'a128ddd54eebe7a49f75ea25c513c6229f1304fb51a9d9b07539a89b8a094656'

if not __debug__:
    raise RuntimeError('Producer validation requires normal Python (without -O)')

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def imp(a, b):
    return ('imp', a, b)

def row(a, b, c, u):
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))

def subst(term, env):
    return tuple(subst(x, env) for x in term) if isinstance(term, tuple) else env.get(term, term)

class Reader:
    def __init__(self, text, schemas, counts, facts=None):
        self.ts = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|≼|[()]', text)
        assert ''.join(self.ts) == re.sub(r'\s+', '', text), 'unsupported syntax'
        self.i = 0
        self.schemas, self.counts, self.facts = schemas, counts, facts or {}

    def pop(self, want=None):
        token = self.ts[self.i]
        self.i += 1
        assert want is None or token == want, (want, token)
        return token

    def group(self, parse):
        if self.ts[self.i] == '(':
            self.pop('(')
            result = parse()
            self.pop(')')
            return result
        return parse()

    def term(self):
        def atom():
            name = self.pop()
            if name in ('wim', 'L.imp'):
                return imp(self.term(), self.term())
            assert re.fullmatch(r'v\d+|[a-z]|_', name), name
            return name
        return self.group(atom)

    def guard(self, expected):
        def parse():
            name = self.pop()
            u, a = expected
            if name == 'L.refl':
                value = self.term()
                assert u == a and (value == '_' or value == a)
            elif name in ('le_l', 'le_r'):
                other = self.term()
                assert isinstance(a, tuple) and a[0] == 'imp'
                fixed, grown = (2, 1) if name == 'le_l' else (1, 2)
                assert a[fixed] == other
                self.guard((u, a[grown]))
            else:
                assert self.facts[name] == expected
        self.group(parse)

    def proof(self):
        def parse():
            name = self.pop()
            if name == 'h.mp':
                major, minor = self.proof(), self.proof()
                assert isinstance(major, tuple) and major[0] == 'imp'
                assert major[1] == minor, ('MP mismatch', major, minor)
                self.counts['mp'] += 1
                return major[2]
            if name == 'h.rho8':
                a, b, c, u = [self.term() for _ in range(4)]
                self.guard((u, a))
                self.counts['restricted_rows'] += 1
                return row(a, b, c, u)
            if name in self.schemas:
                self.pop('h')
                args, target, guards = self.schemas[name]
                env = dict(zip(args, [self.term() for _ in args]))
                for guard in guards:
                    self.guard(subst(guard, env))
                return subst(target, env)
            assert name in self.facts, name
            return self.facts[name]
        return self.group(parse)

    def end(self):
        assert self.i == len(self.ts), self.ts[self.i:]

def audit(core, inlined=False, with_basis=False):
    schemas, counts = {}, {'mp': 0, 'restricted_rows': 0}
    matches = list(re.finditer(r'private theorem (d\d+)\b', core))
    expected = [f'd{i}' for i in range(1, 59) if not inlined or i not in (56, 58)]
    assert [m.group(1) for m in matches] == expected
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else core.index('/-- Restricted rows', match.end())
        header, body = core[match.end():end].split(':=', 1)
        args = [a for group in re.findall(r'\(([^():]+) : A\)', header) for a in group.split()]
        facts, guards = {}, []
        for name, text in re.findall(r'\((hb\d+) : (.*?)\)\s*:', header, re.S):
            r = Reader(text, schemas, counts)
            u = r.term(); r.pop('≼'); a = r.term(); r.end()
            facts[name] = (u, a)
            guards.append((u, a))
        r = Reader(re.split(r':\s*T\s+', header)[-1], schemas, counts)
        target = r.term(); r.end()
        before = counts['mp']
        r = Reader(body.strip(), schemas, counts, facts)
        assert r.proof() == target, match.group(1)
        r.end()
        assert counts['mp'] == before + 1
        schemas[match.group(1)] = (args, target, guards)
    assert counts == {'mp': len(expected), 'restricted_rows': 23}
    assert not re.search(r'WithSeed|h\.truth|\b0\b|Nat\.|sorry|native_decide', core)
    assert not re.search(r'(?m)^\s*axiom\b', core)
    targets = {
        'rho8_all': row('a', 'b', 'c', 'u'),
        'composition': imp(imp('a', 'b'), imp(imp('b', 'c'), imp('a', 'c'))),
        'lift_right': imp(imp('x', 'a'), imp('x', 'b')),
    }
    if with_basis:
        targets.update({
            'basisK': imp('a', imp('b', 'a')),
            'basisPeirce': imp(imp(imp('a', 'b'), 'a'), 'a'),
            'basisS': imp(imp('a', imp('b', 'c')), imp(imp('a', 'b'), imp('a', 'c'))),
        })
    public = list(re.finditer(r'(?m)^theorem (\w+)\b', core))
    assert [m.group(1) for m in public] == list(targets)
    for index, match in enumerate(public):
        end = public[index + 1].start() if index + 1 < len(public) else core.index('\nend\n', match.end())
        body = core[match.end():end].split(':=', 1)[1]
        body = re.sub(r'/--.*?-/\s*$', '', body, flags=re.S).strip()
        r = Reader(body, schemas, counts, {'hab': imp('a', 'b')})
        assert r.proof() == targets[match.group(1)], match.group(1)
        r.end()
    total_mp = 61 if with_basis else 59
    assert counts == {'mp': total_mp, 'restricted_rows': 23}
    return {'private_steps': len(expected), 'private_mp': len(expected), 'restricted_rows': 23,
            'public_mp': total_mp - len(expected), 'seed_uses': 0, 'public_targets': list(targets)}

def render_core(raw_core):
    core = raw_core
    for name, args, pin in [
        ('d56', ['c', 'u', 'a', 'b'], '4c5c289425be0a601f699f48b4ed5b9be91dc1fcc0684d9dabbc16e78200f753'),
        ('d58', ['a', 'b', 'c'], 'd371f672d1b010dfe026b34443c53228f16864c5c7bd9cdacd84f10009f7cda4'),
    ]:
        match = re.search(r'private theorem ' + name + r'\b.*?(?=private theorem |/-- Restricted rows)', core, re.S)
        block = match.group()
        assert sha(block.encode()) == pin
        env = {f'v{i}': a for i, a in enumerate(args)}
        body = re.sub(r'\bv\d+\b', lambda m: env[m.group()], block.split(':=\n', 1)[1]).rstrip('\n')
        core = core[:match.start()] + core[match.end():]
        call = '  ' + name + ' h ' + ' '.join(args)
        assert core.count(call) == 1 and len(re.findall(r'\b' + name + r'\b', core)) == 1
        core = core.replace(call, body)
    before = ('The 58 lemmas\nbelow are one condensed-detachment derivation of the unrestricted row, composition and\n'
              'prefixing from modus ponens and the restricted rows alone, generated by')
    after = ('The 58-step\ncondensed-detachment derivation of the unrestricted row, composition and\n'
             'prefixing from modus ponens and the restricted rows alone was first rendered by')
    assert core.count(before) == 1 and not re.search(r'\bd(?:56|58)\b', core)
    return core.replace(before, after)

def generate():
    inputs = {}
    for name, expected in INPUT_PINS.items():
        raw = (HERE / name).read_bytes()
        assert sha(raw) == expected, 'input bytes differ: ' + name
        inputs[name] = raw.decode('utf-8')
    raw_checked = audit(inputs[SOURCE])
    core, adapter = render_core(inputs[SOURCE]), inputs[ADAPTER]
    assert sha(core.encode()) == EXPECTED_CORE, 'output differs from reviewed core'
    # Preserve the reviewed phase-eleven proof and append the small checked basis.
    audit(core, inlined=True)
    assert core.count('\nend\n') == 1
    core = core.replace('\nend\n', '\n' + inputs[BASIS] + 'end\n')
    core = core.replace('#print axioms lift_right',
        '#print axioms lift_right\n#print axioms basisK\n#print axioms basisPeirce\n#print axioms basisS')
    checked = audit(core, inlined=True, with_basis=True)
    metrics = {'input_raw_sha256': INPUT_PINS, 'generic_sha256': sha(core.encode()),
               'adapter_sha256': sha(adapter.encode()), 'generic_bytes': len(core.encode()),
               'adapter_bytes': len(adapter.encode()), 'combined_bytes': len((core + adapter).encode()),
               'generic_lines': len(core.splitlines()), 'adapter_lines': len(adapter.splitlines()),
               'raw_checked': raw_checked, 'checked': checked,
               'derivation_role': 'Pinned ancestry data; no renderer execution.',
               'kernel_status': 'External Lean receipts; this diagnostic is not a proof kernel.'}
    return core, adapter, metrics

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='write repo-layout Lean files under this directory')
    parser.add_argument('--check', action='store_true', help='check exact maintained source bytes')
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
