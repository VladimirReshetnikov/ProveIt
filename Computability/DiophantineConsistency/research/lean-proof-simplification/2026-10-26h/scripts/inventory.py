#!/usr/bin/env python3
"""Reproduce the source inventory; this is a textual survey, not a Lean parser."""
import argparse
import csv
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path


def code_only(text):
    """Blank nested Lean comments and strings while retaining line positions."""
    out = list(text)
    i, depth, string, line = 0, 0, False, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if line:
            if c == '\n':
                line = False
            else:
                out[i] = ' '
        elif depth:
            if pair == '/-':
                out[i:i + 2] = '  '
                depth += 1
                i += 1
            elif pair == '-/':
                out[i:i + 2] = '  '
                depth -= 1
                i += 1
            elif c != '\n':
                out[i] = ' '
        elif string:
            if c == '\\' and i + 1 < len(text):
                out[i:i + 2] = '  '
                i += 1
            else:
                if c == '"':
                    string = False
                if c != '\n':
                    out[i] = ' '
        elif pair == '--':
            out[i:i + 2] = '  '
            line = True
            i += 1
        elif pair == '/-':
            out[i:i + 2] = '  '
            depth = 1
            i += 1
        elif c == '"':
            out[i] = ' '
            string = True
        i += 1
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    repo, dest = args.repository.resolve(), args.output.resolve()
    base = repo / 'Computability/DiophantineConsistency'
    dest.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    tracked = subprocess.check_output(
        ['git', '-C', str(repo), 'ls-tree', '-r', '--name-only', 'HEAD', '--',
         'Computability/DiophantineConsistency'], text=True).splitlines()
    tracked_lean = [p for p in tracked if p.endswith('.lean')]
    rows, tactics, duplicate_names = [], Counter(), defaultdict(list)
    names = ['simp', 'simp_all', 'simpa', 'omega', 'linarith', 'nlinarith', 'ring',
             'ring_nf', 'norm_num', 'native_decide', 'decide', 'exact_mod_cast',
             'grind', 'aesop', 'sorry', 'admit', 'axiom']
    for p in sorted((base / 'Lean').rglob('*.lean')):
        raw = p.read_bytes()
        text = raw.decode('utf-8')
        code = code_only(text)
        rel = p.relative_to(base).as_posix()
        role = 'audit' if '/checks/' in rel or p.stem.endswith(('Checks', 'Audit')) else 'library'
        if rel == 'Lean/DiophantineConsistency.lean':
            role = 'entrypoint'
        local = Counter({t: len(re.findall(r'\b' + t + r'\b', code)) for t in names})
        if rel.startswith('Lean/DiophantineConsistency/'):
            tactics.update(local)
        for m in re.finditer(r'(?m)^private (?:theorem|lemma|def) (\S+)', code):
            duplicate_names[m.group(1)].append({'path': rel, 'line': code[:m.start()].count('\n') + 1})
        rows.append({'path': rel, 'role': role, 'lines': len(text.splitlines()),
                     'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                     'imports': re.findall(r'(?m)^import\s+([\w.]+)', code),
                     'header_generated_word': bool(re.search(r'(?i)generated', text[:2500])),
                     'token_counts': dict(local)})
    module_rows = [r for r in rows if r['path'].startswith('Lean/DiophantineConsistency/')]
    summary = {
        'repository': 'https://github.com/VladimirReshetnikov/ProveIt', 'commit': commit,
        'lean_toolchain': (repo / 'lean-toolchain').read_text().strip(),
        'mathlib_revision': next(p['rev'] for p in json.loads((repo / 'lake-manifest.json').read_text())['packages'] if p['name'] == 'mathlib'),
        'all_tracked_lean_files_in_requested_subtree': len(tracked_lean),
        'active_lean_tree_files': len(rows),
        'main_module_directory_files': len(module_rows),
        'main_module_directory_physical_lines': sum(r['lines'] for r in module_rows),
        'main_directory_audit_files': sum(r['role'] == 'audit' for r in module_rows),
        'all_active_audit_files': sum(r['role'] == 'audit' for r in rows),
        'main_directory_token_counts_excluding_comments_and_strings': dict(tactics),
        'duplicate_private_names': {k: v for k, v in sorted(duplicate_names.items()) if len(v) > 1},
        'method': 'Physical line/byte counts are exact. Token and duplicate-name counts are textual indicators, not semantic duplication or kernel audits. Generated-word flag is only a discovery heuristic.',
    }
    (dest / 'source-inventory.json').write_text(json.dumps({'summary': summary, 'files': rows}, indent=2) + '\n')
    with (dest / 'source-inventory.csv').open('w', newline='') as f:
        fields = ['path', 'role', 'lines', 'bytes', 'sha256', 'header_generated_word']
        w = csv.DictWriter(f, fieldnames=fields, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)
    (dest / 'source-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'duplicate_private_names'}, indent=2))


if __name__ == '__main__':
    main()
