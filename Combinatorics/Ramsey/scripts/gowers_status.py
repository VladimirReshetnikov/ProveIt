#!/usr/bin/env python3
"""Emit a source-level ledger of numbered Gowers catalogue statements.

This is an inventory, not a kernel audit. Exact companion theorem signatures
are distinguished from conditional implications and auxiliary results.
"""
from pathlib import Path
from collections import Counter
import json
import re

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
PAPER = ROOT / 'Combinatorics/Ramsey/Papers/sz-thm-gowers-proof/sz-thm-gowers-proof.tex'
paper_text = PAPER.read_text()
headings = {}
for match in re.finditer(r'^(Theorem|Lemma|Corollary|Proposition)\s+(\d+\.\d+)',
                         paper_text, re.M):
    name = match[1].lower() + '_' + match[2].replace('.', '_')
    headings.setdefault(name, []).append(paper_text.count('\n', 0, match.start()) + 1)
texts = {p: p.read_text() for p in sorted(SOURCE.glob('*.lean'))}
numbered = r'(?:theorem|lemma|corollary|proposition)_\d+_\d+'
rows = []
for source, text in texts.items():
    for match in re.finditer(r'^def (' + numbered + r')\s*:\s*Prop\s*:=', text, re.M):
        name = match[1]
        exact = []
        related = []
        for p, content in texts.items():
            for companion in re.finditer(r'^theorem (' + re.escape(name) + r'_\w+)\b', content, re.M):
                entry = {'name': companion[1], 'file': str(p.relative_to(ROOT)),
                         'line': content.count('\n', 0, companion.start()) + 1}
                header = content[companion.end():].split(':=', 1)[0]
                if re.fullmatch(r'\s*:\s*' + re.escape(name) + r'\s*', header):
                    exact.append(entry)
                else:
                    related.append(entry)
        rows.append({'statement': name, 'file': str(source.relative_to(ROOT)),
                     'line': text.count('\n', 0, match.start()) + 1,
                     'paper_heading_lines': headings.get(name, []),
                     'status': 'exact_companion' if exact else 'open',
                     'exact_companions': exact, 'related_theorems': related})
rows.sort(key=lambda r: tuple(map(int, r['statement'].split('_')[-2:])))
catalogue_names = {row['statement'] for row in rows}
print(json.dumps({'scope': 'Source inventory of numbered Prop definitions; compile companions before treating them as verified. Related theorems may be conditional, restricted cases, or counterexamples. This does not certify fidelity to the paper.',
                  'paper': str(PAPER.relative_to(ROOT)),
                  'paper_statements_without_catalogue_entries': sorted(set(headings) - catalogue_names),
                  'catalogue_entries_without_paper_headings': sorted(catalogue_names - set(headings)),
                  'counts': dict(Counter(row['status'] for row in rows)),
                  'statements': rows}, indent=2))
