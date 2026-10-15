#!/usr/bin/env python3
"""Emit a source-level ledger of numbered Gowers catalogue statements.

This is an inventory, not a kernel audit. Exact companion theorem signatures
are distinguished from conditional implications and auxiliary results. Simple
companion aliases inherit their target signature classification.
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
                entry = {'name': companion[1], 'file': p.relative_to(ROOT).as_posix(),
                         'line': content.count('\n', 0, companion.start()) + 1}
                header = content[companion.end():].split(':=', 1)[0]
                if re.fullmatch(r'\s*:\s*' + re.escape(name) + r'\s*', header):
                    exact.append(entry)
                else:
                    related.append(entry)
        # Simple aliases retain their target's signature classification. Resolve
        # after scanning theorem headers so file order and alias chains are harmless.
        aliases = []
        for p, content in texts.items():
            for alias in re.finditer(r'^alias (' + re.escape(name) +
                                     r'_\w+)\s*:=\s*(\w+)\s*$', content, re.M):
                entry = {'name': alias[1], 'file': p.relative_to(ROOT).as_posix(),
                         'line': content.count('\n', 0, alias.start()) + 1}
                aliases.append((entry, alias[2]))
        occurrences = Counter(entry['name'] for entry in exact + related)
        occurrences.update(entry['name'] for entry, _ in aliases)
        while aliases:
            pending = []
            for entry, target in aliases:
                if occurrences[target] != 1:
                    raise ValueError(f"Missing or ambiguous companion alias target: {target}")
                kinds = [kind for kind, entries in ((True, exact), (False, related))
                         for candidate in entries if candidate['name'] == target]
                if not kinds:
                    pending.append((entry, target))
                elif len(kinds) != 1:
                    raise ValueError(f"Ambiguous companion alias target: {target}")
                else:
                    (exact if kinds[0] else related).append(entry)
            if len(pending) == len(aliases):
                raise ValueError(f"Unresolved companion aliases: {pending}")
            aliases = pending
        rows.append({'statement': name, 'file': source.relative_to(ROOT).as_posix(),
                     'line': text.count('\n', 0, match.start()) + 1,
                     'paper_heading_lines': headings.get(name, []),
                     'status': 'exact_companion' if exact else 'open',
                     'exact_companions': exact, 'related_theorems': related})
rows.sort(key=lambda r: tuple(map(int, r['statement'].split('_')[-2:])))
catalogue_names = {row['statement'] for row in rows}
print(json.dumps({'scope': 'Source inventory of numbered Prop definitions; compile companions before treating them as verified. Related theorems may be conditional, restricted cases, or counterexamples. This does not certify fidelity to the paper.',
                  'paper': PAPER.relative_to(ROOT).as_posix(),
                  'paper_statements_without_catalogue_entries': sorted(set(headings) - catalogue_names),
                  'catalogue_entries_without_paper_headings': sorted(catalogue_names - set(headings)),
                  'counts': dict(Counter(row['status'] for row in rows)),
                  'statements': rows}, indent=2))
