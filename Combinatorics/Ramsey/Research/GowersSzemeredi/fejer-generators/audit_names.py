"""Names cited by ``LeanProofs.GowersSzemeredi.X in the audit files, checked against the corpus by text.

usage: python -X utf8 audit_names.py [git-rev]
Without a revision the working tree is read; with one (e.g. HEAD~12) the files at that revision.
A name `A.B.c` counts as declared when some .lean file of the corpus has a header for `A.B.c`, or for
`B.c` / `c` inside `namespace A` / `namespace A.B`, or when `c` is a field / constructor of a structure
`A.B` (checked loosely: `c` appears in the structure body), or an `alias`.
Prints the missing names with the audit files that cite them.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
GSREL = 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
REV = sys.argv[1] if len(sys.argv) > 1 else None


def git(*a):
    return subprocess.run(['git', '-C', str(ROOT), *a], capture_output=True, text=True, encoding='utf8').stdout


def files():
    if REV:
        names = git('ls-tree', '-r', '--name-only', REV, '--', 'Combinatorics/Ramsey').split('\n')
    else:
        names = git('ls-files', '--', 'Combinatorics/Ramsey').split('\n')
    return [n for n in names if n.endswith('.lean')]


def read(n):
    if REV:
        return git('show', f'{REV}:{n}')
    p = ROOT / n
    return p.read_text(encoding='utf8') if p.exists() else ''


HD = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(?:nonrec )?"
                r"(?:theorem|lemma|def|abbrev|structure|instance|class|inductive|alias|opaque|axiom)\s+([^\s(:{\[]+)",
                re.M)
NS = re.compile(r"^\s*(namespace|end|section)\b\s*(\S*)", re.M)
CITE = re.compile(r"``LeanProofs\.GowersSzemeredi\.([\w'.₀-₉?!]+)")

declared = set()
fields = {}
texts = {}
for n in files():
    t = read(n)
    texts[n] = t
    # walk namespaces line by line
    stack = []
    for line in t.split('\n'):
        m = re.match(r"^\s*namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"^\s*section\b\s*(\S*)", line)
        if m:
            stack.append(None)
            continue
        m = re.match(r"^\s*end\b\s*(\S*)", line)
        if m and stack:
            stack.pop()
            continue
        m = HD.match(line)
        if m:
            nm = m.group(1)
            prefix = '.'.join(x for x in stack if x)
            full = (prefix + '.' + nm) if prefix else nm
            declared.add(full)
            declared.add(nm)
            for k in range(len(full.split('.'))):
                declared.add('.'.join(full.split('.')[k:]))

cited = {}
for n, t in texts.items():
    if 'Audit' not in n and 'inspect_gowers' not in n:
        continue
    for m in CITE.finditer(t):
        cited.setdefault(m.group(1), set()).add(Path(n).name)

# structure fields / constructors: X.mk, X.field
struct_bodies = {}
for n, t in texts.items():
    for m in re.finditer(r"^structure\s+(\S+)[^\n]*\n((?:[ \t]+[^\n]*\n|\n)*)", t, re.M):
        struct_bodies[m.group(1)] = m.group(2)

missing = []
for nm, where in sorted(cited.items()):
    full = 'LeanProofs.GowersSzemeredi.' + nm
    if nm in declared or full in declared:
        continue
    parts = nm.split('.')
    if len(parts) >= 2:
        s, f = '.'.join(parts[:-1]), parts[-1]
        if s in struct_bodies and (f == 'mk' or re.search(r'\b' + re.escape(f) + r'\b', struct_bodies[s])):
            continue
    missing.append((nm, where))
print(len(cited), 'cited names;', len(missing), 'not found')
for nm, where in missing:
    print(f'  {nm}  <- {" ".join(sorted(where))}')
