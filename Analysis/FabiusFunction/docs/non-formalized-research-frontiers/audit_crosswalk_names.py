# -*- coding: utf-8 -*-
"""Check every Fabius.* declaration cited in the frontier volumes
against the declarations that actually exist in the Lean corpus."""
import io, os, re

LEAN = (r'C:/ProveIt/.claude/worktrees/fabius-function-formalization-4a6355'
        r'/Analysis/FabiusFunction/Lean/FabiusFunction')
DOCS = (r'C:/ProveIt/.claude/worktrees/fabius-function-formalization-4a6355'
        r'/Analysis/FabiusFunction/docs/non-formalized-research-frontiers')

# 1. Collect every declaration name defined in the corpus.
decl = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+'
    r'([A-Za-z_][A-Za-z0-9_.\']*)')
defined = set()
for root, _dirs, files in os.walk(LEAN):
    for fn in files:
        if not fn.endswith('.lean'):
            continue
        with io.open(os.path.join(root, fn), encoding='utf-8',
                     errors='replace') as fh:
            for line in fh:
                m = decl.match(line)
                if m:
                    defined.add(m.group(1))

# 2. Collect every Fabius.* name cited in the .tex volumes.
cite = re.compile(r'Fabius\.([A-Za-z0-9_\\\']+)')
cited = {}
for root, _dirs, files in os.walk(DOCS):
    for fn in files:
        if not fn.endswith('.tex'):
            continue
        path = os.path.join(root, fn)
        with io.open(path, encoding='utf-8', errors='replace') as fh:
            for i, line in enumerate(fh, 1):
                for m in cite.finditer(line):
                    # LaTeX escapes underscores as \_ ; undo that.
                    name = m.group(1).replace('\\_', '_').rstrip('\\')
                    cited.setdefault(name, []).append(
                        (os.path.relpath(path, DOCS), i))

missing = {n: locs for n, locs in cited.items() if n not in defined}

print('corpus declarations found: %d' % len(defined))
print('distinct Fabius.* names cited in docs: %d' % len(cited))
print('cited but NOT found in corpus: %d' % len(missing))
print()
for n in sorted(missing):
    locs = missing[n]
    where = '; '.join('%s:%d' % (f, l) for f, l in locs[:3])
    print('MISSING  %-58s  %s' % (n, where))
