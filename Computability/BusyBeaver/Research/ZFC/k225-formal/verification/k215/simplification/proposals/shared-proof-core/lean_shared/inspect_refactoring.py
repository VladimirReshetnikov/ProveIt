#!/usr/bin/env python3
"""Verify producer fidelity, public headers and exact source simplification metrics."""
import argparse
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
FORMAL = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
GEN = Path('Computability/BusyBeaver/Research/ZFC/k225-formal/rho8cd')

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def digest(data):
    return hashlib.sha256(data).hexdigest()

def header(source, name):
    match = re.search(r'^theorem ' + re.escape(name) + r'\b.*?:=', source, re.M | re.S)
    if match is None:
        raise AssertionError(f'Missing theorem {name}')
    return ' '.join(match.group().split())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    oldcore = (repo / FORMAL / 'DominatedImplication.lean').read_text()
    oldluk = (repo / FORMAL / 'Lukasiewicz.lean').read_text()
    newcore = (HERE / 'BusyBeaver/ZFC/DominatedImplication.lean').read_text()
    newbasis = (HERE / 'BusyBeaver/ZFC/ImplicationalBasis.lean').read_text()
    newluk = (HERE / 'BusyBeaver/ZFC/Lukasiewicz.lean').read_text()
    tail_marker = 'namespace SetTheory.BusyBeaver.ZFC.Tarski\n'
    assert oldluk[oldluk.index(tail_marker):] == newluk[newluk.index(tail_marker):]
    start = 'structure Implicational '
    end = '\nvariable {imp '
    assert oldluk[oldluk.index(start):oldluk.index(end)] == newbasis[newbasis.index(start):newbasis.index(end)]
    for name in ['k', 'peirce', 'composition', 's']:
        assert header(oldluk, name) == header(newbasis, name), name
    for name in ['rho8_all', 'composition', 'lift_right']:
        assert header(oldcore, name) == header(newcore, name), name
    oldgen = load(repo / GEN / 'generate_domrho8_cd.py', 'old_generator')
    newgen = load(HERE / 'generation/generate_domrho8_cd.py', 'new_generator')
    rows, goals = newgen.read(HERE / 'generation/derivation_core.txt')
    assert newgen.render(rows, goals, 'core') == newcore
    rows, goals = oldgen.read(repo / GEN / 'derivation.txt')
    for mode in ['lean', 'rocq']:
        assert oldgen.render(rows, goals, mode) == newgen.render(rows, goals, mode)
    old_text = [oldcore, oldluk]
    new_text = [newcore, newbasis, newluk]
    before_bytes = sum(len(s.encode()) for s in old_text)
    after_bytes = sum(len(s.encode()) for s in new_text)
    before_lines = sum(len(s.splitlines()) for s in old_text)
    after_lines = sum(len(s.splitlines()) for s in new_text)
    # Exclude the common one-MP lift_right API wrapper.
    old_mps = oldcore.count('h.mp') - 1 + oldluk.count('(detach h')
    new_mps = newcore.count('h.mp') - 1
    result = {
        'original_modules': ['DominatedImplication.lean', 'Lukasiewicz.lean'],
        'new_modules': ['DominatedImplication.lean', 'ImplicationalBasis.lean', 'Lukasiewicz.lean'],
        'before_bytes': before_bytes, 'after_bytes': after_bytes,
        'saved_bytes': before_bytes - after_bytes,
        'byte_reduction_percent': 100 * (before_bytes-after_bytes) / before_bytes,
        'before_lines': before_lines, 'after_lines': after_lines,
        'saved_lines': before_lines - after_lines,
        'source_mp_nodes_before': old_mps, 'source_mp_nodes_after': new_mps,
        'mp_metric_scope': 'Shared numbered derivations plus new exchange and S extension; excludes common lift_right wrapper. This is not a minimal-proof lower bound or expanded proof-term count.',
        'old_cd_declarations': len(re.findall(r'^private theorem cd_', oldluk, re.M)),
        'public_headers_preserved': ['Implicational', 'k', 'peirce', 'composition', 's', 'rho8_all', 'lift_right'],
        'tarski_tail_byte_identical': True, 'core_regeneration_byte_identical': True,
        'legacy_lean_rocq_renderers_unchanged': True,
        'derivation_core_sha256': digest((HERE/'generation/derivation_core.txt').read_bytes())}
    patch = []
    changes = [(FORMAL/'DominatedImplication.lean', oldcore, newcore),
               (FORMAL/'Lukasiewicz.lean', oldluk, newluk),
               (FORMAL/'ImplicationalBasis.lean', '', newbasis),
               (GEN/'generate_domrho8_cd.py', (repo/GEN/'generate_domrho8_cd.py').read_text(),
                (HERE/'generation/generate_domrho8_cd.py').read_text())]
    for name, before, after in changes:
        patch += difflib.unified_diff(before.splitlines(keepends=True), after.splitlines(keepends=True),
                                     fromfile='a/'+str(name) if before else '/dev/null', tofile='b/'+str(name))
    (HERE/'integration.patch').write_text(''.join(patch))
    (HERE/'verification/source_metrics.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
