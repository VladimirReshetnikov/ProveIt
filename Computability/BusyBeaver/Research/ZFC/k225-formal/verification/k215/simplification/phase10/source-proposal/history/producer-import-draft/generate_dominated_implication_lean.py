#!/usr/bin/env python3
"""Render the generic dominated-implication core and unchanged Nat adapter.

The exact attributed 52-step input is instantiated by the historical CD
renderer, then checked as a free-constructor derivation: no zero identity is
available in the generic proof. The four discarded fillers use reflexivity,
and five truth detachments use an arbitrary seed. Lean checks the emitted
proofs. This producer is not part of the proof kernel.

The maintained CLI remains --out LEAN_ROOT or --check (the default).
The historical rho8cd/generate_domrho8_cd.py CLI is left unchanged.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
TEMPLATES = HERE / 'dominated_implication_templates'
DEFAULT_OUT = (HERE / '../../../Lean').resolve()
INPUT_PINS = {
    'rho8cd/generate_domrho8_cd.py': 'e08e99ee624854a7fc73d876acf29d2659c093c53a17805f41bab6fed3d6e01b',
    'rho8cd/derivation.txt': '3cbf1ed6114ff44da836578e58c9d5308d347a8b1d664e83c1983e800d285776',
}
TEMPLATE_PINS = {
    'adapter.txt': '8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378',
    'core-prefix.txt': '22d93bd8644f3288ea0d490e6d7ce66e03366bf3a8e0397902f3d1ad71368139',
    'core-suffix.txt': 'c31f1521758c3b95d3f06ade403248cdb65e024ba7b0f0479bd29560fc43d973',
}
EXPECTED_CORE = '5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f'
SEED = -2

if not __debug__:
    raise RuntimeError('Producer validation requires normal Python (without -O)')

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def pinned(path, expected):
    raw = path.read_bytes()
    assert digest(raw) == expected, 'input bytes differ: ' + str(path)
    return raw.decode('utf-8')

def mapped(t, fn):
    return tuple(mapped(x, fn) for x in t) if isinstance(t, tuple) else fn(t)

def generate():
    # Bind every executable byte before importing the historical renderer.
    for name, expected in INPUT_PINS.items():
        pinned(HERE / name, expected)
    templates = {n: pinned(TEMPLATES / n, h) for n, h in TEMPLATE_PINS.items()}
    spec = importlib.util.spec_from_file_location('rho8cd_attributed', HERE / 'rho8cd/generate_domrho8_cd.py')
    module = importlib.util.module_from_spec(spec)
    old_bytecode_setting = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        spec.loader.exec_module(module)
    finally:
        sys.dont_write_bytecode = old_bytecode_setting
    rows = module.read(HERE / 'rho8cd/derivation.txt')
    assert len(rows) == 54 and rows[0] == (-1, -1, module.Z, [])
    assert rows[1] == (-2, -2, module.ROW, [(1, 2)])

    class Generic(module.Syntax):
        def term(self, t, top=True):
            assert t != module.Z, 'numeric zero escaped into generic proof'
            return 'τ' if t == SEED else super().term(t, top)

        def le(self, u, a, hyps):
            if (u, a) in hyps:
                return 'hb%d' % hyps.index((u, a))
            if u == a:
                return '(L.refl _)'
            if isinstance(a, tuple) and module.subterm(u, a[0]):
                return '(le_l %s %s)' % (self.term(a[1], False), self.le(u, a[0], hyps))
            if isinstance(a, tuple) and module.subterm(u, a[1]):
                return '(le_r %s %s)' % (self.term(a[0], False), self.le(u, a[1], hyps))
            raise ValueError('no generic relation proof for %r' % ((u, a),))

        def lemma(self, name, formula, cons, major, minor):
            assert not major[4] and not minor[4], 'zero-normalization wrapper is forbidden'
            return super().lemma(name, formula, cons, major, minor).replace(': Nat', ': A').replace(' ≤ ', ' ≼ ')

    syntax = Generic(False)
    schemas = {'row': (module.ROW, [(1, 2)])}
    fillers = {'d3': (1, 2), 'd7': ((1, 2), 3), 'd10': (1, 2), 'd16': 0}
    seed_steps = {'d4', 'd9', 'd13', 'd18', 'd22'}
    blocks, records = [], []
    for ordinal, (name, target, guards, major, minor) in enumerate(module.steps(rows), 1):
        assert name == 'd%d' % ordinal
        choice = fillers.get(name, SEED)

        def materialize(premise):
            kind, parent, args, _old_guards, collapsed = premise
            assert not collapsed
            if kind == 'truth':
                assert name in seed_steps
                return premise, SEED
            formula, constraints = schemas[parent]
            replace = lambda x: choice if x == module.Z else x
            args = [mapped(a, replace) for a in args]
            instantiate = lambda t: mapped(t, lambda x: args[x])
            conditions = [tuple(instantiate(x) for x in pair) for pair in constraints]
            for u, a in conditions:
                syntax.le(u, a, guards)
            return (kind, parent, args, conditions, False), instantiate(formula)

        major, major_formula = materialize(major)
        minor, minor_formula = materialize(minor)
        # Literal constructor equality, not the upstream Z-collapse unifier.
        assert major_formula == (minor_formula, target), name
        schemas[name] = (target, guards)
        blocks.append(syntax.lemma(name, target, guards, major, minor))
        records.append({'name': name, 'major': major[1], 'minor': minor[1], 'guard_count': len(guards)})
    assert len(blocks) == 52 and schemas['d52'] == (module.ROW, [])
    body = '\n'.join(blocks) + '\n'
    assert not re.search(r'\b0\b|Nat\.|wim00|zero_le', body)
    core = templates['core-prefix.txt'] + body + templates['core-suffix.txt']
    adapter = templates['adapter.txt']
    assert digest(core.encode()) == EXPECTED_CORE, 'generated core differs from reviewed source'
    metrics = {
        'base_commit': '4fdc59197a45a6beb7e5a4ae7109fd13477b1d17',
        'input_raw_sha256': INPUT_PINS, 'template_raw_sha256': TEMPLATE_PINS,
        'generic_sha256': digest(core.encode()), 'adapter_sha256': digest(adapter.encode()),
        'generic_bytes': len(core.encode()), 'adapter_bytes': len(adapter.encode()),
        'combined_bytes': len((core + adapter).encode()),
        'generic_lines': len(core.splitlines()), 'adapter_lines': len(adapter.splitlines()),
        'numbered_helpers': len(blocks), 'compatibility_helpers': 6,
        'reflexive_fillers': sorted(fillers), 'arbitrary_seed_detachments': sorted(seed_steps),
        'certificate_status': '52 literal MP equations and all relation guards checked; no zero normalization',
        'kernel_status': 'external build receipts; this Python script is not a proof kernel',
        'steps': records,
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
