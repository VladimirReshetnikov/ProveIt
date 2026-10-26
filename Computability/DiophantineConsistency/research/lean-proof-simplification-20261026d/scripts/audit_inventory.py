#!/usr/bin/env python3
"""Reproduce a lexical Lean inventory; this is not a Lean parser or verifier."""
from __future__ import annotations
import argparse
import collections
import csv
import hashlib
import json
import re
from pathlib import Path


def strip_comments(text: str) -> str:
    """Preserve newlines and strings; handle Lean's nested block comments."""
    out = []
    i, depth = 0, 0
    quoted = False
    while i < len(text):
        pair = text[i:i+2]
        char = text[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(char)
            i += 1
            if char == '\\' and i < len(text):
                out.append(text[i])
                i += 1
            elif char == '"':
                quoted = False
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end-i))
            i = end
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        else:
            out.append(char)
            quoted = char == '"'
            i += 1
    return ''.join(out)


TACTICS = ['simp', 'simp_all', 'simpa', 'omega', 'ring', 'ring_nf',
           'nlinarith', 'linarith', 'norm_num', 'decide', 'native_decide',
           'exact_mod_cast', 'push_cast', 'fin_cases', 'aesop']


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('--output', type=Path, default=Path('inventory'))
    args = parser.parse_args()
    source = args.repository / 'Computability/DiophantineConsistency/Lean'
    rows = []
    declarations = []
    decl_pattern = re.compile(
        r'^\s*(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
        r'(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s({:]+)', re.M)
    for path in sorted(source.rglob('*.lean')):
        raw = path.read_text()
        clean = strip_comments(raw)
        relative = path.relative_to(source).as_posix()
        ds = list(decl_pattern.finditer(clean))
        # Declaration spans are lexical estimates and may include trailing commands.
        for j, match in enumerate(ds):
            end = ds[j+1].start() if j+1 < len(ds) else len(clean)
            declarations.append(dict(file=relative, kind=match[1], name=match[2],
                start_line=clean.count('\n', 0, match.start())+1,
                lexical_span_lines=clean[match.start():end].count('\n')))
        row = dict(file=relative, sha256=hashlib.sha256(raw.encode()).hexdigest(),
            physical_lines=len(raw.splitlines()),
            nonblank_code_lines=sum(bool(line.strip()) for line in clean.splitlines()),
            theorem_lemma_count=sum(d[1] in ('theorem','lemma') for d in ds),
            declarations=len(ds),
            mathlib_tactic_import=bool(re.search(r'^import Mathlib\.Tactic\s*$', clean, re.M)),
            max_heartbeats_options=len(re.findall(r'\bset_option\s+maxHeartbeats\b',clean)),
            sorry_admit_tokens=len(re.findall(r'\b(?:sorry|admit)\b',clean)),
            axiom_commands=len(re.findall(r'^\s*axiom\b',clean,re.M)),
            generated_marker=bool(re.search(r'generated|auto-generated',raw[:1500],re.I)))
        row.update({name+'_tokens':len(re.findall(r'(?<![\w.])'+name+r'(?![\w])',clean))
                    for name in TACTICS})
        rows.append(row)
    args.output.mkdir(parents=True, exist_ok=True)
    with (args.output/'files.csv').open('w', newline='') as out:
        writer = csv.DictWriter(out, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    with (args.output/'declarations.csv').open('w', newline='') as out:
        writer = csv.DictWriter(out, fieldnames=list(declarations[0]))
        writer.writeheader()
        writer.writerows(declarations)
    numeric = [key for key,value in rows[0].items() if isinstance(value,(int,bool))]
    def totals(selected):
        return {'files':len(selected),**{key:sum(row[key] for row in selected) for key in numeric}}
    modules = [row for row in rows if row['file'].startswith('DiophantineConsistency/')]
    summary = {
        'method':'Lexical inventory, with nested comments removed. Not an elaboration or axiom audit.',
        'active_lean_tree':totals(rows),
        'main_module_directory':totals(modules),
        'largest_files':sorted(rows, key=lambda row:row['physical_lines'],reverse=True)[:20],
    }
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({key:value for key,value in summary.items() if key!='largest_files'},indent=2))


if __name__ == '__main__':
    main()
