"""What the final theorems use, and what could leave the real final route.

usage: python -X utf8 regions3.py [--moves]
Inputs (from UsedRanges3.lean): used_ranges3.txt, decl_needs3.txt.
Real route = closure of Proofs18CoverFejerAllDegrees; its 10 real-only (bridge) modules are live and
not edited. A module is live when it holds a used declaration (equation / congr_simp lemmas stored
away from their base declaration are ignored: Lean regenerates them anywhere).
Prints: cone lines vs closure lines; dead modules and lines; for each live module, the declarations
that would have to move out (they need a dead module), closed under use inside the route.
"""
import collections
import re
import sys
from pathlib import Path

SCR = Path(__file__).parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
mods = {p.stem for p in GS.glob('*.lean')}
src = {m: (GS / f'{m}.lean').read_text(encoding='utf8') for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}
nlines = {m: src[m].count('\n') for m in mods}


def clo(roots):
    s, st = set(roots), list(roots)
    while st:
        for d in imp.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


REAL = clo(['Proofs18CoverFejerAllDegrees'])
stub_roots = re.findall(r'^import GowersSzemeredi\.(\S+)', (SCR / 'StubFinal.lean').read_text(encoding='utf8'), re.M)
STUB = clo(stub_roots)
REAL_ONLY = REAL - STUB
EQ = re.compile(r'\.(eq_\d+|eq_def|eq_unfold|congr_simp)$')
AUX = re.compile(r'\.(_proof_\d+(_\d+)?|match_\d+(_\d+)?|_cstage\d|_sunfold|proof_\d+|_unsafe_rec|eq_\d+|eq_def|eq_unfold|'
                 r'congr_simp|_simp_\d+(_\d+)?|_sizeOf_\d+|_sizeOf_inst|splitter|casesOn|rec|recOn|noConfusion|'
                 r'noConfusionType|ctorIdx|mk\.inj|mk\.injEq|mk\.noConfusion|mk\.sizeOf_spec|mk\._flat_ctor|inj|injEq)$')
short = lambda m: m.split('.', 1)[1] if m.startswith('GowersSzemeredi.') else m

owner, needs, same = {}, {}, {}
for l in open(SCR / 'decl_needs3.txt', encoding='utf8'):
    if ' | ' not in l:
        continue
    head, ms, sm = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    owner[n] = short(m)
    needs[n] = [(short(x.split(':', 1)[0]), x.split(':', 1)[1]) for x in ms.split()]
    same[n] = sm.split()


def base(n):
    """The source declaration an auxiliary constant belongs to."""
    prev = None
    while prev != n:
        prev = n
        n = AUX.sub('', n)
    n = re.sub(r'^_private\.[\w.]+?\.0\.', '', n)
    return n


# planned evacuations: `remap.txt` lines `FullDeclName NewModule` (auxiliary constants follow their base)
REMAP = {}
if (SCR / 'remap.txt').exists():
    for l in open(SCR / 'remap.txt', encoding='utf8'):
        if l.strip() and not l.startswith('#'):
            a, b = l.split()
            REMAP[a] = b
if REMAP:
    moved_to = {n: REMAP[base(n)] for n in owner if base(n) in REMAP}
    for n, m in moved_to.items():
        old = owner[n]
        owner[n] = m
        # what the moved declaration used in its old module and stays behind: a need on that module
        stay = [c for c in same.get(n, []) if c not in moved_to]
        same[n] = [c for c in same.get(n, []) if c in moved_to]
        needs[n] = needs.get(n, []) + [(old, c) for c in stay]
        # same-module uses inside the old module become cross-module needs on the new one
        for u in list(owner):
            if owner[u] == old and n in same.get(u, []) and u not in moved_to:
                same[u].remove(n)
                needs[u].append((m, n))
    for u in owner:
        needs[u] = [(moved_to.get(c, dm), c) for dm, c in needs[u]]
owned = collections.defaultdict(set)
for n, m in owner.items():
    owned[m].add(n)


def artifact(mod, c):
    b = EQ.sub('', c)
    return b != c and b not in owned[mod]


used = set()
ranges = {}
for l in open(SCR / 'used_ranges3.txt', encoding='utf8'):
    p = l.split()
    if len(p) < 4:
        continue
    m, n, a, b = short(p[0]), p[1], int(p[2]), int(p[3])
    if artifact(m, n):
        continue
    used.add(n)
    if a:
        ranges.setdefault(m, []).append((a, b))

cone_lines = 0
for m, rs in ranges.items():
    covered = set()
    for a, b in rs:
        covered |= set(range(a, b + 1))
    cone_lines += len(covered)
usedm = {owner[n] for n in used if n in owner}
live = (usedm & REAL) | REAL_ONLY | {'Proofs18CoverFejerAllDegrees'}
dead = REAL - live
L = lambda S: sum(nlines[m] for m in S)
print(f'real route: {len(REAL)} modules, {L(REAL)} lines; used declarations cover {cone_lines} lines')
print(f'live modules {len(live)} ({L(live)} lines), dead modules {len(dead)} ({L(dead)} lines)')

# declarations of live editable modules that need a dead module directly
users = collections.defaultdict(set)
for n, ns in needs.items():
    for (dm, c) in ns:
        users[c].add(n)
    for c in same[n]:
        users[c].add(n)
seed = set()
for U in live - REAL_ONLY:
    for n in owned[U]:
        if any(dm in dead and not artifact(dm, c) for dm, c in needs.get(n, [])):
            seed.add(n)
moved = set(seed)
st = list(seed)
while st:
    c = st.pop()
    for u in users.get(c, ()):
        if u not in moved and owner.get(u) in live - REAL_ONLY:
            moved.add(u)
            st.append(u)
bad = sorted(n for n in moved if n in used)
print(f'declarations that would move out of live modules: {len(moved)} '
      f'({len({base(n) for n in moved})} source declarations); used among them: {len(bad)}')
for n in bad[:20]:
    print('   USED', owner[n], n)
PAPER = re.compile(r'(^|\.)(lemma|theorem|corollary|proposition)_\d+_\d+')
by = collections.defaultdict(set)
for n in moved:
    by[owner[n]].add(base(n).split('LeanProofs.GowersSzemeredi.')[-1])
if '--moves' in sys.argv:
    for U in sorted(by, key=lambda u: -len(by[u])):
        names = sorted(by[U])
        paper = [x for x in names if PAPER.search(x)]
        print(f'{U}: {len(names)} {"PAPER " + " ".join(paper) if paper else ""}')
        print('    ' + ' '.join(names[:12]) + (' …' if len(names) > 12 else ''))
paper_all = sorted({x for U in by for x in by[U] if PAPER.search(x)})
print(f'{len(by)} live modules would lose declarations; paper-named among the moved: {len(paper_all)}')
print('   ' + ' '.join(paper_all[:40]))

# per dead region (connected through imports among dead modules): lines, frontier edges, moves
parent = {d: d for d in dead}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for m in dead:
    for d in imp.get(m, []):
        if d in dead:
            parent[find(m)] = find(d)
regions = collections.defaultdict(set)
for d in dead:
    regions[find(d)].add(d)
rows = []
for r, comp in regions.items():
    edges = [(u, d) for u in live - REAL_ONLY for d in imp.get(u, []) if d in comp]
    seed_r = {n for u in live - REAL_ONLY for n in owned[u]
              if any(dm in comp and not artifact(dm, c) for dm, c in needs.get(n, []))}
    mv, st2 = set(seed_r), list(seed_r)
    while st2:
        c = st2.pop()
        for u in users.get(c, ()):
            if u not in mv and owner.get(u) in live - REAL_ONLY:
                mv.add(u)
                st2.append(u)
    srcs = sorted({base(n).split('LeanProofs.GowersSzemeredi.')[-1] for n in mv
                   if not artifact(owner[n], n)})
    paper = [x for x in srcs if PAPER.search(x)]
    rows.append((L(comp), len(comp), len(edges), len(srcs), paper, sorted(comp)[:4], srcs[:6]))
rows.sort(key=lambda x: -x[0])
if '--region' in sys.argv:
    target = sys.argv[sys.argv.index('--region') + 1]
    comp = regions[find(target)]
    print(f'\nregion of {target}: {len(comp)} modules, {L(comp)} lines')
    for d in sorted(comp):
        print(f'   {nlines[d]:5} {d}  <- imported by {" ".join(sorted(u for u in REAL if d in imp.get(u, [])))}')
    edges = [(u, d) for u in live - REAL_ONLY for d in imp.get(u, []) if d in comp]
    ro = [(u, d) for u in REAL_ONLY for d in imp.get(u, []) if d in comp]
    print(f'   cut edges: {edges}')
    print(f'   real-only importers (cannot cut): {ro}')
    seed_r = {n for u in live - REAL_ONLY for n in owned[u]
              if any(dm in comp and not artifact(dm, c) for dm, c in needs.get(n, []))}
    mv, st2 = set(seed_r), list(seed_r)
    while st2:
        c = st2.pop()
        for u in users.get(c, ()):
            if u not in mv and owner.get(u) in live - REAL_ONLY:
                mv.add(u)
                st2.append(u)
    byr = collections.defaultdict(set)
    for n in mv:
        if not artifact(owner[n], n):
            byr[owner[n]].add(base(n).split('LeanProofs.GowersSzemeredi.')[-1])
    for u, ns in sorted(byr.items()):
        print(f'   move from {u}: {" ".join(sorted(ns))}')
    sys.exit(0)
print('\nregion lines/modules | cut edges | declarations to move | paper-named | sample')
for row in rows[:30]:
    print(f'{row[0]:6} {row[1]:3} | {row[2]:3} edges | {row[3]:3} moves | '
          f'{"PAPER " + " ".join(row[4][:3]) if row[4] else "-"} | {" ".join(row[5])} || {" ".join(row[6])}')
