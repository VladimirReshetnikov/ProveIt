# -*- coding: utf-8 -*-
"""Check that every module in the Lean tree is reachable from the
library root `FabiusFunction.lean`.

The root is hand-maintained and lists only what is needed to reach the
whole tree transitively, so a newly added *leaf* module that nothing
imports is easy to forget.  Such a module is never elaborated by
`lake build FabiusFunction`, and a whole-library build then reports
success while silently skipping it.

Exit status is 1 when anything is unreachable or phantom, so this can
gate a commit alongside `audit_crosswalk_names.py`.
"""
import io, os, re, sys
from pathlib import Path

FRONTIER_ROOT = Path(__file__).resolve().parent
FABIUS_ROOT = FRONTIER_ROOT.parent.parent
ROOT = FABIUS_ROOT / 'Lean'
PKG = os.path.join(ROOT, 'FabiusFunction')
FACADE = os.path.join(ROOT, 'FabiusFunction.lean')

imp = re.compile(r'^\s*import\s+FabiusFunction\.([A-Za-z0-9_.]+)')


def imports_of(path):
    out = []
    with io.open(path, encoding='utf-8', errors='replace') as fh:
        for line in fh:
            m = imp.match(line)
            if m:
                out.append(m.group(1))
            elif line.strip() and not line.startswith('import') \
                    and not line.startswith('--'):
                break
    return out


modules = set()
for root, _dirs, files in os.walk(PKG):
    for fn in files:
        if fn.endswith('.lean'):
            rel = os.path.relpath(os.path.join(root, fn), PKG)
            modules.add(rel[:-5].replace(os.sep, '.'))

# Breadth-first closure from the facade.
seen = set()
stack = list(imports_of(FACADE))
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    path = os.path.join(PKG, *m.split('.')) + '.lean'
    if os.path.exists(path):
        stack.extend(imports_of(path))

unreachable = sorted(modules - seen)
phantom = sorted(seen - modules)

print('modules on disk:           %d' % len(modules))
print('reachable from the facade: %d' % len(seen & modules))
print('UNREACHABLE (never built): %d' % len(unreachable))
for m in unreachable:
    print('  UNREACHABLE  %s' % m)
if phantom:
    print('imported but missing on disk: %d' % len(phantom))
    for m in phantom:
        print('  PHANTOM      %s' % m)

sys.exit(1 if (unreachable or phantom) else 0)
