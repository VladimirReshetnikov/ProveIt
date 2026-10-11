#!/usr/bin/env python3
"""Find fully qualified declaration names declared in two GowersSzemeredi modules.

Two modules that declare the same name each build green; Lean rejects the pair
only where both are imported, i.e. in the facade `GowersSzemeredi.lean`. This
source-level scan finds such pairs without building the facade.

Scope tracking: `namespace A.B` and named or anonymous `section`s go on one
stack, since Lean closes both with `end`; only namespaces contribute to the
prefix. Block comments, `private` declarations and instances are skipped. Only
modules in the facade's import closure are scanned, since an orphan module
cannot clash. It is a regex proxy: it cannot see clashes created by `export`
or against Mathlib names.

Usage: python check_gowers_duplicates.py [DIR]   (exit 1 if a duplicate is found)
"""
from pathlib import Path
import collections
import re
import sys

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s:({\[]+)')


IMPORT = re.compile(r'^import GowersSzemeredi\.(\S+)', re.M)


def facade_closure(root):
    """Module files reachable from the facade, or every module if there is none."""
    root = Path(root)
    facade = root.parent / 'GowersSzemeredi.lean'
    if not facade.exists():
        return sorted(root.glob('*.lean'))
    todo = IMPORT.findall(facade.read_text(encoding='utf-8'))
    found = set()
    while todo:
        mod = todo.pop()
        path = root / (mod.replace('.', '/') + '.lean')
        if mod in found or not path.exists():
            continue
        found.add(mod)
        todo.extend(IMPORT.findall(path.read_text(encoding='utf-8')))
    return sorted(root / (m.replace('.', '/') + '.lean') for m in found)


def scan(root):
    seen = collections.defaultdict(list)
    for path in facade_closure(root):
        stack = []
        depth = 0
        for lineno, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
            outside = depth == 0
            depth = max(0, depth + line.count('/-') - line.count('-/'))
            if not outside:
                continue
            if m := re.match(r'^namespace\s+(\S+)', line):
                stack.append(('ns', m.group(1)))
            elif re.match(r'^section\b', line):
                stack.append(('sec', ''))
            elif re.match(r'^end\b', line):
                if stack:
                    stack.pop()
            elif not line.startswith('private ') and (m := DECL.match(line)):
                name = m.group(2)
                if name.startswith('_root_.'):
                    full = name[len('_root_.'):]
                else:
                    prefix = '.'.join(n for kind, n in stack if kind == 'ns')
                    full = f'{prefix}.{name}' if prefix else name
                seen[full].append(f'{path.name}:{lineno}')
    return {name: sites for name, sites in seen.items() if len(sites) > 1}


def main():
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    root = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).resolve().parent.parent / 'Lean' / 'GowersSzemeredi')
    dups = scan(root)
    for name, sites in sorted(dups.items()):
        print(name, ' '.join(sites))
    print(f'{len(dups)} duplicated names')
    sys.exit(1 if dups else 0)


if __name__ == '__main__':
    main()
