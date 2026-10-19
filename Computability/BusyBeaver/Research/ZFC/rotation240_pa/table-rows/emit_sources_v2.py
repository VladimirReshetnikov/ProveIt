#!/usr/bin/env python3
"""Emit fresh finite row proofs; this program never invokes Lean or a checker."""
import argparse
import hashlib
import json
from pathlib import Path

REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
PARTITION = Path('/tmp/zfc-rotation240-coverage-production-generated-v1/generation.json')
PARTITION_SHA = '6c68ae7fecb2ff78e2ad63a43ebb7da38c11f71ecdc3bce8727a2c113f98c04b'
SITES = REPO / 'Computability/BusyBeaver/Research/ZFC/candidate-rotation240/sites_logical.json'
SITES_SHA = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
PARENTS = [
    ('CountedTreeRotation240', '/tmp/zfc-w6-counted-tree240-actual/run2/verification.json',
     '691d66e456980d914be15c2d0810f4397c5561153f6ccb31af676494d61d7aae',
     '8918d46a4f050622f8a2392f6ba7a0aeab97dabcd33dd2b2853ab3c5cefeb925', 3, 3),
    ('ControlTableBinding', '/tmp/zfc-w6-control-table-binding-actual/run3/verification.json',
     '5e845e33a2fdc08daaa242005da7e28074550082f99ccfc0bf6dbff6de85df9e',
     'df0b8c56ea6e9949d6d4efe544697ebc7373cef246efb6fd994f742c0c906b5c', 6, 9),
    ('BisimCertRotation240', '/tmp/zfc-w6-bisim-cert-actual/run1/verification.json',
     'f0184b236186e3ee3931b8e1c05e7da852f4de1acc2b6f0e2568fff6b6750def',
     'c3bb3eebbddad909a56dffe34cb786b1ca114e88412e3ba6f8d32eac61ce7a23', 2, 4),
]
PILOT_MODULE = 'BusyBeaver.ZFC.TableRowsRotation240Pilot'
PILOT_SOURCE_SHA = '22ed9f69ea3ca249b44e7cfae11842736bbd4dbcedbe4f5c848da92a8ffb36e3'
PILOT_AUDIT_SHA = '1ce38a72660e2e9b8d771164733ae658510a5dacc472d07cd069b82d8a836912'
PILOT_PATH = '111010010010101111110110'
NS = 'SetTheory.BusyBeaver.ZFC.TableRowsRotation240'
BASE = [f'BusyBeaver.ZFC.{x[0]}' for x in PARENTS]
CHECK = ('(checkRow CountedTreeRotation240.counted '
         '(PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR))')
TABLE_GOAL = ('PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR =\n'
              '    (ControlCatalogue.leafEntries TreeRotation240.tree).map\n'
              '      (ArithmeticControlTable.rowOf TreeRotation240.tree)')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pinned(path, digest):
    path = Path(path).resolve()
    assert sha(path) == digest, f'changed input: {path}'
    return {'path': str(path), 'sha256': digest}


def actual(module, path, digest, source_sha, probes, callers):
    desc = pinned(path, digest)
    r = json.loads(Path(path).read_text())
    assert r['status'] == 'PASS' and r['prepare_only'] is False
    assert (r['named_axiom_probes'], r['callers'], r['warnings']) == (probes, callers, 0)
    assert r['only_standard_axioms'] and r['source_object_recorded_before_audit']
    assert r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit']
    assert r['source']['sha256'] == source_sha
    for key in ('source', 'audit'):
        for path_key in ('path', 'snapshot'):
            pinned(r[key][path_key], r[key]['sha256'])
    assert len(r['commands']) == 2
    for c in r['commands']:
        assert c['exit_code'] == 0 and not c['timed_out'] and not c.get('interrupted')
        pinned(c['log'], c['log_sha256'])
    fresh = r['fresh_modules']
    assert len(fresh) == 1 and fresh[0]['module'] == module
    f = fresh[0]
    pinned(f['path'], f['sha256'])
    assert f['source_sha256'] == source_sha
    assert r['source_pass_object'] == dict(f, source_command_index=0)
    assert r['fresh_first_provider_before_audit'] == {k: f[k] for k in ('module', 'path', 'sha256')}
    return dict(desc, module=module, source=r['source'], audit=r['audit'], fresh=f)


def bits(path):
    return '[' + ', '.join('true' if b == '1' else 'false' for b in path) + ']'


def goal(path):
    return f'allSites {CHECK} ({bits(path)} : List Bool).reverse (descend TreeRotation240.tree {bits(path)}) = true'


def partition_data():
    pinned(PARTITION, PARTITION_SHA)
    pinned(SITES, SITES_SHA)
    p = json.loads(PARTITION.read_text())
    sites = json.loads(SITES.read_text())
    assert len(sites) == 6455 and sum(2 if s[1] == 'CD' else 1 for s in sites) == 8386
    paths = [s[0] for s in sites]
    assert paths == sorted(set(paths)) and all(set(x) <= {'0', '1'} for x in paths)
    cuts = [{k: c[k] for k in ('index', 'path', 'lo', 'hi', 'leaves', 'guards')}
            for c in p['cut_frontier']]
    joins = [{k: j[k] for k in ('index', 'path', 'left', 'right')} for j in p['join_plan']]
    assert len(cuts) == 530 and len(joins) == 529 and p['root'] == ['join', 528]
    assert [c['index'] for c in cuts] == list(range(530))
    assert [j['index'] for j in joins] == list(range(529))
    assert len({c['path'] for c in cuts}) == 530
    assert len({j['path'] for j in joins}) == 529
    cursor = 0
    for c in sorted(cuts, key=lambda c: c['lo']):
        assert c['lo'] == cursor and c['hi'] > cursor
        cursor = c['hi']
        selected = [i for i, path in enumerate(paths) if path.startswith(c['path'])]
        assert selected == list(range(c['lo'], c['hi']))
        assert c['leaves'] == len(selected)
        assert c['guards'] == sum(2 if sites[i][1] == 'CD' else 1 for i in selected)
    assert cursor == 6455
    seen = set()

    def visit(ref, path):
        kind, i = ref
        assert kind in ('cut', 'join') and (kind, i) not in seen
        seen.add((kind, i))
        row = (cuts if kind == 'cut' else joins)[i]
        assert row['path'] == path
        if kind == 'join':
            for bit, side in [('0', 'left'), ('1', 'right')]:
                child = row[side]
                assert child[0] != 'join' or child[1] < i
                visit(child, path + bit)

    visit(['join', 528], '')
    assert len(seen) == 1059 and sum(c['guards'] for c in cuts) == 8386
    assert cuts[508] == dict(index=508, path=PILOT_PATH, lo=6227, hi=6247, leaves=20, guards=26)
    return cuts, joins


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', required=True, type=Path)
    ap.add_argument('--cuts-per-module', required=True, type=int)
    ap.add_argument('--joins-per-module', required=True, type=int)
    ap.add_argument('--pilot-record', type=Path)
    ap.add_argument('--pilot-sha256')
    args = ap.parse_args()
    assert 1 <= args.cuts_per_module <= 530 and 1 <= args.joins_per_module <= 529
    assert (args.pilot_record is None) == (args.pilot_sha256 is None)
    out = args.out.resolve()
    assert not out.exists(), 'output must be a new scratch directory'
    parents = [actual(f'BusyBeaver.ZFC.{m}', p, h, s, n, c) for m, p, h, s, n, c in PARENTS]
    pilot = None
    if args.pilot_record is not None:
        pilot = actual(PILOT_MODULE, args.pilot_record, args.pilot_sha256, PILOT_SOURCE_SHA, 1, 1)
        assert pilot['audit']['sha256'] == PILOT_AUDIT_SHA
    cuts, joins = partition_data()
    units, texts, owners = [], {}, {}

    def add(short, kind, items, dependencies, declarations, use_pilot=False):
        index = len(units)
        module = f'BusyBeaver.ZFC.{short}'
        dependencies = sorted(set(dependencies))
        assert all(0 <= d < index for d in dependencies)
        imports = BASE + [units[d]['module'] for d in dependencies]
        if use_pilot:
            imports.append(PILOT_MODULE)
        imports = list(dict.fromkeys(imports))
        header = ''.join(f'import {m}\n' for m in imports)
        source = (header + '\nset_option autoImplicit false\n\n'
                  '/-! Fresh packed-row equality obligations. Historical binary coverage supplies only partition data. -/\n'
                  f'namespace {NS}\nopen SiteCoverage ControlTableBinding\n\n')
        audit = (f'import {module}\n\nset_option autoImplicit false\n\n'
                 'open SetTheory.BusyBeaver.ZFC\nopen SiteCoverage ControlTableBinding\n\n')
        probes = []
        for name, typ, proof in declarations:
            source += f'theorem {name} :\n    {typ} := {proof}\n\n'
            qualified = f'{NS}.{name}'
            probes.append(qualified)
            audit += f'#print axioms {qualified}\nexample :\n    {typ} := {qualified}\n\n'
        source += f'end {NS}\n'
        relsource = f'unit{index:03d}/{short}.lean'
        relaudit = f'unit{index:03d}/Audit.lean'
        texts[relsource], texts[relaudit] = source, audit
        descriptor = lambda rel: {'path': str(out / rel), 'sha256': hashlib.sha256(texts[rel].encode()).hexdigest()}
        units.append(dict(index=index, kind=kind, module=module, source=descriptor(relsource),
                          audit=descriptor(relaudit), imports=imports, dependencies=dependencies,
                          parent_modules=[units[d]['module'] for d in dependencies],
                          items=items, probes=probes, callers=len(probes),
                          reused_cut=508 if use_pilot else None))
        return index

    for start in range(0, 530, args.cuts_per_module):
        group = cuts[start:start + args.cuts_per_module]
        decls = []
        reuse = pilot is not None and any(c['index'] == 508 for c in group)
        for c in group:
            proof = ('by\n  exact SetTheory.BusyBeaver.ZFC.TableRowsRotation240Pilot.checked'
                     if pilot is not None and c['index'] == 508 else 'by\n  decide +kernel')
            decls.append((f'block_{c["index"]}', goal(c['path']), proof))
        index = add(f'TableRowsRotation240Batch{start // args.cuts_per_module:03d}',
                    'cut', [c['index'] for c in group], [], decls, reuse)
        for c in group:
            owners[('cut', c['index'])] = index

    for start in range(0, 529, args.joins_per_module):
        group = joins[start:start + args.joins_per_module]
        current = len(units)
        deps, decls = [], []
        for j in group:
            refs = [tuple(j['left']), tuple(j['right'])]
            deps.extend(owners[r] for r in refs if owners[r] != current)
            names = [f'{NS}.{"block" if k == "cut" else "join"}_{i}' for k, i in refs]
            proof = (f'allSites_join {CHECK} ({bits(j["path"])} : List Bool).reverse\n'
                     f'  (descend TreeRotation240.tree {bits(j["path"] + "0")})\n'
                     f'  (descend TreeRotation240.tree {bits(j["path"] + "1")})\n'
                     f'  {names[0]} {names[1]}')
            decls.append((f'join_{j["index"]}', goal(j['path']), proof))
            owners[('join', j['index'])] = current
        add(f'TableRowsRotation240Join{start // args.joins_per_module:03d}',
            'join', [j['index'] for j in group], deps, decls)

    all_goal = f'allSites {CHECK} [] TreeRotation240.tree = true'
    table_proof = ('ControlTableBinding.packed_table_eq TreeRotation240.tree CountedTreeRotation240.counted\n'
                   '  BisimCertRotation240.tableR BisimCertRotation240.countR\n'
                   '  CountedTreeRotation240.counted_eq\n'
                   '  (by simpa only [BisimCertRotation240.countR] using CountedTreeRotation240.catalogue_length.symm)\n'
                   '  all_rows')
    final = add('TableRowsRotation240', 'final', [], [owners[('join', 528)]],
                [('all_rows', all_goal, f'{NS}.join_528'), ('table_eq', TABLE_GOAL, table_proof)])
    assert sum(len(u['probes']) for u in units) == 1061
    manifest = dict(status='SOURCE_ONLY_UNCOMPILED', generator=pinned(__file__, sha(__file__)),
                    partition=pinned(PARTITION, PARTITION_SHA), sites=pinned(SITES, SITES_SHA),
                    parents=parents, pilot=pilot, reused_cut=508 if pilot else None,
                    cuts_per_module=args.cuts_per_module, joins_per_module=args.joins_per_module,
                    cut_frontier=cuts, join_plan=joins, root=['join', 528],
                    leaves=6455, guard_cases=8386, cuts=530, joins=529,
                    fresh_row_checks=529 if pilot else 530,
                    generated_units=len(units), generated_probes=1061, generated_callers=1061,
                    final_unit=final, final_module=units[final]['module'], units=units,
                    scope='Exact finite packed table equality only; no new internal binary simulation or PA endpoint.',
                    proof_reuse='Only the explicitly pinned new row pilot may be reused; no historical binary-site proof is imported.',
                    options={'autoImplicit': False, 'new_proof_limit_overrides': []},
                    compiler_or_checker_executed=False)
    out.mkdir(parents=True)
    for rel, content in texts.items():
        target = out / rel
        target.parent.mkdir(exist_ok=True)
        target.write_text(content)
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(out / 'manifest.json')


if __name__ == '__main__':
    main()
