#!/usr/bin/env python3
"""Source-only Lean inventory; this is not a parser or a kernel proof check.

Usage: python3 scan_source.py /path/to/grh-lean > source_scan.json
The input must be a local checkout. This program never fetches or modifies it.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys


def erase_comments_strings(text):
    """Preserve newlines while erasing nested Lean comments and strings."""
    out = []
    i = depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
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
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_string:
            if text[i] == '\\':
                out.extend('  ')
                i += 2
            else:
                if text[i] == '"':
                    in_string = False
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        elif text[i] == '"':
            in_string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


TOKENS = ('sorry', 'axiom', 'admit', 'unsafe', 'implemented_by',
          'native_decide', 'Lean.ofReduceBool', 'run_tac', 'run_elab',
          'elab', 'macro')


def edition_scan(root, edition):
    base = root / edition / 'src'
    modules = {'.'.join(p.relative_to(base).with_suffix('').parts): p
               for p in base.rglob('*.lean')}
    clean = {m: erase_comments_strings(p.read_text())
             for m, p in modules.items()}
    findings = {token: [] for token in TOKENS}
    for m, text in clean.items():
        for token in TOKENS:
            for match in re.finditer(r'(?<!\w)' + re.escape(token) + r'(?!\w)', text):
                findings[token].append({
                    'path': str(modules[m].relative_to(root)),
                    'line': 1 + text.count('\n', 0, match.start())})
    seen, external, pending = set(), set(), ['Main']
    while pending:
        m = pending.pop()
        if m in seen:
            continue
        if m not in modules:
            external.add(m)
            continue
        seen.add(m)
        pending.extend(q for line in clean[m].splitlines()
                       if line.startswith('import ')
                       for q in line[7:].split())
    return {
        'lean_files': len(modules),
        'lines': sum(len(p.read_text().splitlines()) for p in modules.values()),
        'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(modules.values())},
        'lexical_findings': findings,
        'import_closure_from_Main': len(seen),
        'external_import_roots': sorted(external),
        'files_not_imported_from_Main': sorted(set(modules) - seen),
    }


def main():
    root = Path(sys.argv[1]).resolve()
    commit = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    print(json.dumps({
        'commit': commit,
        'scope': 'All .lean files in each edition src directory; Challenge.lean is outside scope.',
        'limitations': 'Lexical and import inventory only. Not a Lean parser, elaborator, kernel replay, '
                       'declaration-level proof-dependency analysis, or mathematical verification.',
        'editions': {e: edition_scan(root, e) for e in ('grh', 'grh-compact')}
    }, indent=2))


if __name__ == '__main__':
    main()
