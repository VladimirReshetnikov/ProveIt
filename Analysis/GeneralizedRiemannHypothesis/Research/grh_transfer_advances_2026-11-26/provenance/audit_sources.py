#!/usr/bin/env python3
"""Reproduce the limited static source audit; does not invoke Lean's kernel."""
from pathlib import Path
import argparse
import json
import re
import shutil
import subprocess


def strip_comments_and_strings(s):
    out, i, depth, string = [], 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                depth += 1
                i += 2
            elif s.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if s[i] == '\n':
                    out.append('\n')
                i += 1
        elif string:
            if s[i] == '\\':
                i += 2
            elif s[i] == '"':
                string = False
                i += 1
            else:
                if s[i] == '\n':
                    out.append('\n')
                i += 1
        elif s.startswith('/-', i):
            depth = 1
            i += 2
            out.append(' ')
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        elif s[i] == '"':
            string = True
            i += 1
            out.append(' ')
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', nargs='?', type=Path,
                        default=Path(__file__).with_name('grh-lean'))
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('static_audit.json'))
    args = parser.parse_args()
    repo = args.repository
    result = {
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
        'lean_available': shutil.which('lean'), 'lake_available': shutil.which('lake'),
        'limitations': 'Static lexical and import-graph checks only; no local Lean kernel build or independent-checker replay.'}
    for edition in ['grh', 'grh-compact']:
        src = repo / edition / 'src'
        modules = {str(p.relative_to(src)).removesuffix('.lean').replace('/', '.'): p
                   for p in src.rglob('*.lean')}
        code = {m: strip_comments_and_strings(p.read_text()) for m, p in modules.items()}
        deps = {m: re.findall(r'^\s*import\s+(\S+)', t, re.M) for m, t in code.items()}
        closure, external, todo = set(), set(), ['Main']
        while todo:
            m = todo.pop()
            if m in closure:
                continue
            if m not in modules:
                external.add(m)
                continue
            closure.add(m)
            todo.extend(deps[m])
        tokens = {}
        for m, t in code.items():
            hits = [{'token': x.group(), 'line': t.count('\n', 0, x.start()) + 1}
                    for x in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|implemented_by|native_decide)\b', t)]
            if hits:
                tokens[m] = hits
        result[edition] = {
            'source_files': len(modules),
            'source_lines': sum(len(p.read_text().splitlines()) for p in modules.values()),
            'main_local_import_closure_files': len(closure),
            'external_imports': sorted(external),
            'forbidden_tokens_outside_comments_strings': tokens,
            'challenge_imported': any('Challenge' in ds for ds in deps.values())}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
