#!/usr/bin/env python3
"""Reproducible, lexical source census; not a Lean parser or axiom audit.

Usage: python3 inventory.py /path/to/ProveIt /path/to/output-directory
Nested comments and strings are masked before token/declaration counts.
Physical line counts include comments and whitespace. No files are modified.
"""
import argparse
import csv
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

def code_only(s):
    out = list(s)
    i = 0
    while i < len(s):
        start = i
        if s.startswith('--', i):
            i = s.find('\n', i)
            if i < 0:
                i = len(s)
        elif s.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(s) and depth:
                if s.startswith('/-', i): depth += 1; i += 2
                elif s.startswith('-/', i): depth -= 1; i += 2
                else: i += 1
        elif s[i] == '"':
            i += 1
            while i < len(s):
                if s[i] == '\\': i += 2
                elif s[i] == '"': i += 1; break
                else: i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(s))):
            if out[j] != '\n': out[j] = ' '
    return ''.join(out)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    repo = args.repo.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    scope = repo / 'Computability/DiophantineConsistency'
    base = scope / 'Lean'
    rows, decls = [], []
    tokens = Counter()
    imported_by = Counter()
    tracked = ['omega', 'nlinarith', 'linarith', 'ring', 'ring_nf', 'simp_all',
               'native_decide', 'sorry', 'admit', 'axiom']
    for path in sorted(base.rglob('*.lean')):
        data = path.read_bytes()
        text = data.decode('utf-8')
        code = code_only(text)
        rel = path.relative_to(repo).as_posix()
        row = dict(path=rel, bytes=len(data), physical_lines=len(text.splitlines()),
                   nonblank_code_lines=sum(bool(x.strip()) for x in code.splitlines()),
                   sha256=hashlib.sha256(data).hexdigest())
        words = Counter(re.findall(r'\b\w+\b', code))
        for word in tracked:
            row[word] = words[word]
            tokens[word] += words[word]
        row['maxHeartbeats_settings'] = len(re.findall(r'\bset_option\s+maxHeartbeats\b', code))
        row['maxRecDepth_settings'] = len(re.findall(r'\bset_option\s+maxRecDepth\b', code))
        for m in re.finditer(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+(\S+)', code, re.M):
            decls.append(dict(path=rel, line=code[:m.start(2)].count('\n')+1, kind=m[1], name=m[2]))
        for imp in re.findall(r'^import\s+([^\n]+)', code, re.M):
            for name in imp.split(): imported_by[name] += 1
        rows.append(row)
    sha = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    extra = sorted(p.relative_to(repo).as_posix() for p in scope.rglob('*.lean') if not p.is_relative_to(base))
    summary = dict(commit=sha, scope=str(base.relative_to(repo)), files=len(rows),
        physical_lines=sum(r['physical_lines'] for r in rows),
        nonblank_code_lines=sum(r['nonblank_code_lines'] for r in rows),
        bytes=sum(r['bytes'] for r in rows), lexical_theorem_declarations=len(decls),
        tokens=dict(tokens), maxHeartbeats_settings=sum(r['maxHeartbeats_settings'] for r in rows),
        maxRecDepth_settings=sum(r['maxRecDepth_settings'] for r in rows),
        largest_files=sorted(rows, key=lambda r:r['physical_lines'], reverse=True)[:20],
        most_imported=imported_by.most_common(20),
        additional_lean_files_outside_maintained_tree=len(extra),
        interpretation='Lexical census, not elaborated declaration counting, proof-length measurement, or axiom audit.')
    (out/'inventory_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    (out/'declarations.json').write_text(json.dumps(decls, indent=2)+'\n')
    (out/'other_lean_paths.txt').write_text('\n'.join(extra)+'\n')
    with (out/'files.csv').open('w', newline='') as f:
        writer=csv.DictWriter(f, fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)
    print(json.dumps({k:v for k,v in summary.items() if k not in ['largest_files','most_imported']}, indent=2))

if __name__ == '__main__':
    main()
