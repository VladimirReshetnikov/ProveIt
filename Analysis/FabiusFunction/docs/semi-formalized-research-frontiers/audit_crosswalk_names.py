# -*- coding: utf-8 -*-
"""Check every Fabius.* name cited in the frontier volumes against the
names that actually exist in the Lean corpus.

The corpus is scanned with a namespace stack, so declarations are
recorded under their FULLY QUALIFIED names, and the set of namespace
paths is recorded too.  A citation resolves if it names a declaration
or a namespace.  Dotted citations such as `Fabius.SaddleExpansion.expCoeff`
and `Fabius.IsOriginalFabius.mk_of_derivative_law` are matched whole
rather than truncated at the first dot, which is what previously made
them look missing.

Exit status is 1 when anything is unresolved, so this can gate a commit.
"""
import io, os, re, sys

LEAN = (r'C:/ProveIt/.claude/worktrees/fabius-function-formalization-4a6355'
        r'/Analysis/FabiusFunction/Lean/FabiusFunction')
DOCS = (r'C:/ProveIt/.claude/worktrees/fabius-function-formalization-4a6355'
        r'/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers')

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+'
    r"([A-Za-z_][A-Za-z0-9_.']*)")
NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
NS_END = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")

# 1. Corpus: fully qualified declarations, and every namespace path.
defined = set()
namespaces = set()
for root, _dirs, files in os.walk(LEAN):
    for fn in sorted(files):
        if not fn.endswith('.lean'):
            continue
        stack = []
        with io.open(os.path.join(root, fn), encoding='utf-8',
                     errors='replace') as fh:
            for line in fh:
                m = NS_OPEN.match(line)
                if m:
                    stack.extend(m.group(1).split('.'))
                    namespaces.add('.'.join(stack))
                    continue
                m = NS_END.match(line)
                if m:
                    parts = m.group(1).split('.')
                    if stack[-len(parts):] == parts:
                        del stack[-len(parts):]
                    continue
                m = DECL.match(line)
                if m:
                    defined.add('.'.join(stack + [m.group(1)]))

# A declaration named `A.b` inside `namespace N` is also reachable as
# `N.A.b`; record every suffix-qualified spelling so citations that
# open an intermediate namespace still resolve.
resolvable = set(defined) | set(namespaces)
for full in list(defined) + list(namespaces):
    parts = full.split('.')
    for i in range(len(parts)):
        resolvable.add('.'.join(parts[i:]))

# 2. Citations.  Dotted names are captured whole.
CITE = re.compile(r"Fabius\.((?:[A-Za-z0-9_'\\]|\.(?=[A-Za-z_]))+)")
cited = {}
for root, _dirs, files in os.walk(DOCS):
    for fn in sorted(files):
        if not fn.endswith('.tex'):
            continue
        path = os.path.join(root, fn)
        with io.open(path, encoding='utf-8', errors='replace') as fh:
            for i, line in enumerate(fh, 1):
                for m in CITE.finditer(line):
                    name = m.group(1).replace('\\_', '_')
                    name = name.rstrip('\\').rstrip('.')
                    if not name:
                        continue
                    cited.setdefault(name, []).append(
                        (os.path.relpath(path, DOCS), i))

missing = {n: locs for n, locs in cited.items() if n not in resolvable}

print('corpus declarations found: %d' % len(defined))
print('corpus namespaces found:   %d' % len(namespaces))
print('distinct Fabius.* names cited in docs: %d' % len(cited))
print('cited but NOT found in corpus: %d' % len(missing))
print()
for n in sorted(missing):
    locs = missing[n]
    where = '; '.join('%s:%d' % (f, l) for f, l in locs[:3])
    print('MISSING  %-58s  %s' % (n, where))

sys.exit(1 if missing else 0)
