#!/usr/bin/env python3
"""Prepare, but do not compile or apply, a source-only K215 abbreviation patch.

Uses pinned local repository files; writes all output outside the checkout.
"""
from pathlib import Path
import argparse
import ast
import difflib
import hashlib
import json
import re

BASE = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
BLOCK = re.compile(
    r'allSites \(KSim.checkEdge tm215\) \[([^\]]*)\]\s*'
    r'\(descend KSource215.t215 \[([^\]]*)\]\) = true')
HELPER = '''/-- Check a source subtree while writing its complete prefix only once. -/
abbrev checkedSubtree (test : List Bool → Edge → Bool) (t : Tree)
    (prefix : List Bool) : Prop :=
  allSites test prefix.reverse (descend t prefix) = true

'''

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    if out == repo or repo in out.parents:
        raise RuntimeError('Output must be outside the repository')
    if out.exists() and any(out.iterdir()):
        raise RuntimeError('Use a fresh empty output directory')
    out.mkdir(parents=True, exist_ok=True)
    pins = json.loads((Path(__file__).parent / 'source-pins.json').read_text())
    patches, rows, blocks = [], [], 0
    for relative, expected in pins['sources'].items():
        source = repo / relative
        before = source.read_bytes()
        if sha(before) != expected:
            raise RuntimeError('Source pin mismatch: ' + relative)
        old = before.decode()
        if source.name == 'SiteCoverage.lean':
            needle = 'def leafCount : Tree → Nat\n'
            if old.count(needle) != 1:
                raise RuntimeError('Expected unique insertion point')
            new = old.replace(needle, HELPER + needle)
        else:
            def replace(match):
                nonlocal blocks
                reverse_prefix, prefix = match.groups()
                if reverse_prefix.split(', ') != prefix.split(', ')[::-1]:
                    raise RuntimeError('Literal prefixes are not reversals')
                blocks += 1
                return ('checkedSubtree (KSim.checkEdge tm215) '
                        'KSource215.t215 [' + prefix + ']')
            new = BLOCK.sub(replace, old)
        after = new.encode()
        target = out / 'proposed' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(after)
        patches.append(''.join(difflib.unified_diff(
            old.splitlines(keepends=True), new.splitlines(keepends=True),
            fromfile='a/' + relative, tofile='b/' + relative)))
        rows.append({'path': relative, 'before_bytes': len(before),
                     'after_bytes': len(after), 'before_sha256': sha(before),
                     'after_sha256': sha(after)})
    if blocks != 105:
        raise RuntimeError('Expected exactly 105 block theorem statements')
    batch = [r for r in rows if r['path'].split('/')[-1].startswith('KSites215Batch')]
    report = {
        'base_commit': pins['base_commit'],
        'status': 'Uncompiled source-only proposal; no proof-size or timing claim.',
        'block_statements_rewritten': blocks,
        'old_batch_bytes': sum(r['before_bytes'] for r in batch),
        'new_batch_bytes': sum(r['after_bytes'] for r in batch),
        'batch_statement_bytes_saved': sum(r['before_bytes'] - r['after_bytes'] for r in batch),
        'helper_added_bytes': len(HELPER.encode()),
        'net_selected_source_bytes_saved': sum(r['before_bytes'] - r['after_bytes'] for r in rows),
        'files': rows,
    }
    (out / 'abbreviate-subtree-statements.patch').write_text(''.join(patches))
    (out / 'measurement.json').write_text(json.dumps(report, indent=2) + '\n')
    generator = pins['generator']
    generator_path = generator['path']
    old_generator = (repo / generator_path).read_text()
    if sha(old_generator.encode()) != generator['sha256']:
        raise RuntimeError('Generator source pin mismatch')
    old_statement = ('return f"allSites {TEST} {bl(tuple(reversed(P)))}\\n'
                     '      (descend {T} {bl(P)}) = true"')
    if old_generator.count(old_statement) != 1:
        raise RuntimeError('Expected one generator statement formatter')
    new_generator = old_generator.replace(
        old_statement, 'return f"checkedSubtree {TEST} {T} {bl(P)}"').replace(
        '`allSites (checkEdge tm215) revPrefix (descend t215 P) = true`,',
        '`checkedSubtree (checkEdge tm215) t215 P`,')
    ast.parse(new_generator)
    target = out / 'proposed' / generator_path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(new_generator)
    (out / 'generator-wiring.patch').write_text(''.join(difflib.unified_diff(
        old_generator.splitlines(keepends=True), new_generator.splitlines(keepends=True),
        fromfile='a/'+generator_path, tofile='b/'+generator_path)))
    (out / 'generator-wiring.json').write_text(json.dumps({
        'path': generator_path, 'before_sha256': sha(old_generator.encode()),
        'after_sha256': sha(new_generator.encode()),
        'excluded_from_ten_Lean_file_metrics': True,
        'status': 'Python syntax parsed; generator not executed; resulting Lean changes uncompiled.'
    }, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))

if __name__ == '__main__':
    main()
