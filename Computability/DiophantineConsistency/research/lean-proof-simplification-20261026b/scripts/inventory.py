#!/usr/bin/env python3
"""Reproduce source-size and dependency measurements for the review.

No compilation or proof verification is implied by these lexical measurements.
Nested Lean block comments and strings are masked before token counting.
"""
import argparse
import csv
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path


def mask_noncode(s):
    out = list(s)
    i, depth, string = 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if s[i] == '\\' and i+1 < len(s):
                out[i:i+2] = '  '; i += 2
            else:
                if s[i] == '"': string = False
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j == -1: j = len(s)
            out[i:j] = ' '*(j-i); i = j
        elif s[i] == '"':
            out[i] = ' '; string = True; i += 1
        else: i += 1
    return ''.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repository', type=Path)
    ap.add_argument('--output', type=Path, default=Path('evidence'))
    args = ap.parse_args()
    repo = args.repository.resolve()
    base = repo/'Computability/DiophantineConsistency/Lean'
    dest = args.output; dest.mkdir(parents=True, exist_ok=True)
    revision = subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'], text=True).strip()
    rows = []
    edges = []
    decls = []
    for path in sorted(base.rglob('*.lean')):
        text = path.read_text(); code = mask_noncode(text)
        rel = str(path.relative_to(repo))
        row = {'path':rel, 'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
               'bytes':path.stat().st_size, 'lines':len(text.splitlines()),
               'code_lines':sum(bool(x.strip()) for x in code.splitlines()),
               'is_check':path.stem.endswith(('Checks','Audit')) or 'checks' in path.parts}
        for token in ('theorem','lemma','def','structure','inductive','simp','simp_all',
                      'rw','omega','nlinarith','ring','ring_nf','norm_num','decide',
                      'native_decide','sorry','admit'):
            row[token] = len(re.findall(r'\b'+token+r'\b',code))
        row['heartbeats_settings'] = len(re.findall(r'set_option\s+maxHeartbeats\b',code))
        row['recdepth_settings'] = len(re.findall(r'set_option\s+maxRecDepth\b',code))
        row['declared_axioms'] = len(re.findall(r'^\s*(?:private\s+)?axiom\b',code,re.M))
        rows.append(row)
        module = '.'.join(path.relative_to(base).with_suffix('').parts)
        for match in re.finditer(r'^\s*import\s+([^\n]+)',code,re.M):
            for imported in match.group(1).split(): edges.append((module,imported))
        for match in re.finditer(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|structure|inductive)\s+([^\s:({]+)',code,re.M):
            decls.append({'path':rel,'line':code[:match.start()].count('\n')+1,'kind':match.group(1),'name':match.group(2)})
    with (dest/'source_metrics.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
    with (dest/'imports.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['module','imports']);w.writerows(edges)
    (dest/'declarations.json').write_text(json.dumps(decls,indent=2)+'\n')
    numeric = [k for k in rows[0] if k not in ('path','sha256','is_check')]
    summary={'revision':revision,'scope':str(base.relative_to(repo)),
             'measurement':'Lexical counts, not elaboration time or kernel proof-term size.',
             'files':len(rows),'core_files':sum(not r['is_check'] for r in rows),
             'check_files':sum(r['is_check'] for r in rows),
             'totals':{k:sum(r[k] for r in rows) for k in numeric},
             'core_totals':{k:sum(r[k] for r in rows if not r['is_check']) for k in numeric},
             'largest_files':sorted(rows,key=lambda r:r['lines'],reverse=True)[:20],
             'most_imported_local':Counter(t for _,t in edges if t.startswith('DiophantineConsistency.')).most_common(20)}
    (dest/'source_inventory.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('largest_files','most_imported_local')},indent=2))


if __name__ == '__main__': main()
