#!/usr/bin/env python3
"""Reconstruct PA194OM and PA194OMF from hash-bound, attributed inputs.

Uses the retained source resolver and local-fold utilities. The independent
literal-tape proof replay is verification/check_physical.py.
"""
from pathlib import Path
import argparse, hashlib, json, sys
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor'))
import support
from source import resolve

EXPECTED = {
    'PA194OM': 'a0473681d6d5fb68e5fccfc473f35bc67aa48083d847e349ba3c52865f293629',
    'PA194OMF': '6b5f79b2caeb4503c3d12886718caa3a363d241dd17735618fbf95727cc3f088',
}

def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def build(output):
    assert __debug__, 'Run with Python assertions enabled.'
    inputs = HERE / 'inputs'
    for name, digest in json.loads((inputs / 'manifest.json').read_text()).items():
        assert hashlib.sha256((inputs / name).read_bytes()).hexdigest() == digest, name
    nodes = json.loads((inputs / 'orh.nodes.json').read_text())
    grammar = json.loads((inputs / 'axiom.grammar.json').read_text())
    assert nodes['node75'] == ['node32', ['node53', ['node55', 'node65']]]
    assert nodes['node164'] == ['node162', 'node163']
    nodes['node164'] = ['node75', ['node37', ['node6', 'node54']]]
    sites, instructions = resolve(nodes, grammar)
    parent_sites = json.loads((inputs / 'ax11h.sites.json').read_text())
    parent_instructions = json.loads((inputs / 'ax11h.instructions.json').read_text())
    assert instructions == parent_instructions and len(sites) == 3671
    changed = [i for i, (a,b) in enumerate(zip(parent_sites, sites)) if a != b]
    assert changed == list(range(224, 291)) + list(range(3572, 3659))
    original = support.read_table(inputs / 'orh.raw.native.tm')
    folds = json.loads((inputs / 'folds.json').read_text())
    for key, target in {(100,0):213, (100,1):174, (174,0):28, (174,1):164}.items():
        w, d, _ = original[key]
        original[key] = w, d, target
    results = []
    for fast in (False, True):
        name = 'PA194OMF' if fast else 'PA194OM'
        raw = dict(original)
        if fast:
            # Direct history selector, followed by the two guarded shortcuts.
            raw = {key:(w,d,127 if target == 124 else target)
                   for key,(w,d,target) in raw.items()}
            raw.update({(127,0):(0,False,124), (124,0):(0,True,8),
                        (124,1):(1,True,59), (26,1):(1,True,91),
                        (101,0):(0,True,17)})
        rows, aliases = support.apply_folds(raw, folds)
        local = support.check_local_folds(raw, rows, aliases, folds)
        dense, labels = support.dense_table(rows, 194)
        startup = support.startup(rows, tuple(map(int, sites[25][0])))
        assert startup['steps'] == (58010 if fast else 58014)
        folder = output / name
        folder.mkdir(parents=True, exist_ok=True)
        for filename, table in [('raw.native.tm',raw), ('machine.native.tm',rows), ('machine.tm',dense)]:
            (folder / filename).write_text(support.table_text(table))
        digest = hashlib.sha256((folder / 'machine.tm').read_bytes()).hexdigest()
        assert digest == EXPECTED[name]
        for filename, value in [('nodes.json',nodes), ('grammar.json',grammar),
                 ('sites.json',sites), ('instructions.json',instructions),
                 ('folds.json',folds), ('local_folds.json',local), ('labels.json',labels)]:
            save(folder / filename, value)
        record = dict(name=name, working_states=194, transition_rows=388,
            raw_controls=201, fixed_controls=135, axiom_reader_controls=66,
            local_folds=7, source_sites=3671, source_outcomes=4778,
            source_instruction_graph_identical_to_ax11h=True,
            changed_source_addresses=changed, maximum_source_address_length=37,
            startup=startup, sha256=digest,
            proof_scope='Finite reconstruction, source graph binding, local fold identities and exact blank startup. Uniform physical simulation and arithmetic calibration are separate written proof obligations.')
        save(folder / 'receipt.json',record)
        results.append({k:v for k,v in record.items() if k not in ('changed_source_addresses','startup')})
    return results

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.output.resolve()),indent=2))
