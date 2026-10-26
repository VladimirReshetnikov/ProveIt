#!/usr/bin/env python3
"""Read-only source inventory. No compiler, network, or repository changes."""
import argparse
import hashlib
import json
import re
from pathlib import Path

def inventory(repo):
    base = repo / 'Computability/DiophantineConsistency'
    if not base.is_dir():
        raise SystemExit('Repository lacks Computability/DiophantineConsistency')
    rows = []
    for p in sorted(base.rglob('*.lean')):
        raw = p.read_bytes()
        s = raw.decode('utf-8')
        rows.append(dict(
            path=p.relative_to(repo).as_posix(), bytes=len(raw),
            lines=len(s.splitlines()), sha256=hashlib.sha256(raw).hexdigest(),
            imports=re.findall(r'^import (.+)$', s, re.M),
            lexical_declarations=len(re.findall(
                r'^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*'
                r'(?:theorem|lemma|def|abbrev|structure|inductive)\s', s, re.M)),
            sorry_tokens=len(re.findall(r'\bsorry\b', s)),
            native_decide_tokens=len(re.findall(r'\bnative_decide\b', s))))
    return dict(method='UTF-8 source and regex inventory; token counts include '
                       'comments and are not proof audits',
                total_files=len(rows), total_lines=sum(x['lines'] for x in rows),
                total_bytes=sum(x['bytes'] for x in rows), files=rows)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('--umbrella', action='store_true',
                        help='Report local import closure of the main umbrella')
    args = parser.parse_args()
    result = inventory(args.repository)
    if args.umbrella:
        rows = {r['path'].split('/Lean/')[1][:-5].replace('/', '.'): r
                for r in result['files'] if r['path'].startswith('Computability/DiophantineConsistency/Lean/')
                and '/checks/' not in r['path']}
        seen, stack = set(), ['DiophantineConsistency']
        while stack:
            module = stack.pop()
            if module in seen or module not in rows:
                continue
            seen.add(module)
            for line in rows[module]['imports']:
                stack.extend(line.split())
        result = dict(
            method='Static direct-import transitive closure restricted to '
                   'primary Lean modules, not cross-project dependencies',
            root='DiophantineConsistency',
            primary_modules_including_umbrella=len(rows),
            reachable_including_umbrella=len(seen),
            not_reached=sorted(set(rows) - seen),
            separate_checks_directory_files=sum(r['path'].startswith('Computability/DiophantineConsistency/Lean/checks/')
                                               for r in result['files']),
            caveat='An umbrella build alone does not build the listed '
                   'unreachable modules or the separate checks directory.')
    print(json.dumps(result, indent=2))
