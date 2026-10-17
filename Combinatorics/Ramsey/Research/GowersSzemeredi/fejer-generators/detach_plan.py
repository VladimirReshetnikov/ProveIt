"""Plan (and optionally apply) the detachment of dead regions from the real final route.

usage: python -X utf8 detach_plan.py MEMBER [MEMBER ...] [--apply]
Each MEMBER names a module of a dead region (see regions3.py). For the union R of their regions:
- every import U -> D with U in the route and D in R is cut;
- modules are then revisited in import order:
  * a route module (live, editable) gets direct imports of the modules its declarations need
    (decl_needs3) that it can no longer reach;
  * a bridge module (real-only, not loadable here) keeps its whole closure except R; the plan
    refuses regions with instances or simp lemmas, the only uses a bridge could make of R
    without naming it (names the bridges mention are roots of the cone, hence live);
  * a module outside the real route keeps exactly its closure (environment unchanged as a set);
  additions are minimal (none reachable from another);
- regions that would need declarations to move are refused (regions3.py lists those).
Prints the edits, the lines leaving the real route, and the edited modules with a local olean.
--apply writes the import edits and detach_rebuild.txt (edited modules with oleans, topo order).
"""
import collections
import re
import sys
from pathlib import Path

SCR = Path(__file__).parent
ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
GS = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
OLE = ROOT / '.lake/build/lib/lean/GowersSzemeredi'
APPLY = '--apply' in sys.argv
KEEP_FLAG = '--keep-closures' in sys.argv
members = [a for a in sys.argv[1:] if not a.startswith('--')]
sys.argv = [sys.argv[0]]
code = open(SCR / 'regions3.py', encoding='utf8').read().split("# per dead region")[0]
exec(compile(code.replace("print(", "(lambda *a, **k: None)("), 'regions3', 'exec'))

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
R = set()
for mem in members:
    assert mem in dead, f'{mem} is not dead'
    R |= {d for d in dead if find(d) == find(mem)}
attr = [m for m in R if re.search(r'^\s*(@\[[^\]]*\b(simp|instance)\b|instance\b|attribute \[(?!local\b))', src[m], re.M)]
if attr:
    print('REFUSED: the region declares instances or attributes:', attr)
    sys.exit(1)
editable = live - REAL_ONLY
cut = [(u, d) for u in sorted(editable) for d in imp.get(u, []) if d in R]
ro = [(u, d) for u in REAL_ONLY for d in imp.get(u, []) if d in R]
if ro:
    print('REFUSED: bridge modules import the region:', ro)
    sys.exit(1)
seeds = [n for u in editable for n in owned[u]
         if any(dm in R and not artifact(dm, c) for dm, c in needs.get(n, []))]
closure_mv, st_mv = set(seeds), list(seeds)
while st_mv:
    c_mv = st_mv.pop()
    for u_mv in users.get(c_mv, ()):
        if u_mv not in closure_mv and owner.get(u_mv) in editable:
            closure_mv.add(u_mv)
            st_mv.append(u_mv)
moves = [n for n in closure_mv if not artifact(owner[n], n)]
if moves:
    print('REFUSED: declarations would have to move:', sorted({base(n) for n in moves})[:20])
    sys.exit(1)

order, seen = [], set()


def visit(m):
    if m in seen:
        return
    seen.add(m)
    for d in imp.get(m, []):
        visit(d)
    order.append(m)


for m in sorted(mods):
    visit(m)


def closure(g, roots):
    s, st = set(roots), list(roots)
    while st:
        for d in g.get(st.pop(), []):
            if d not in s:
                s.add(d)
                st.append(d)
    return s


KEEP = KEEP_FLAG
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                  r"(?:theorem|lemma|def|abbrev|structure|instance|alias|inductive|class)\s+([^\s(:{\[]+)", re.M)


def declared_names(m):
    """Short names a module declares: declarations, structure fields, namespaces."""
    s = src[m]
    ns = {n for d in DECL.findall(s) for n in d.split('.')}
    for blk in re.finditer(r'^structure\s+[^\n]*\n((?:[ \t]+[^\n]*\n|\n)+)', s, re.M):
        ns |= set(re.findall(r"^\s+([A-Za-z_][\w']*)\s*:", blk.group(1), re.M))
    for nsp in re.findall(r'^\s*namespace\s+(\S+)', s, re.M):
        ns |= set(nsp.split('.'))
    return {n for n in ns if len(n) >= 3}


decl_of = {m: declared_names(m) for m in mods}
where = collections.defaultdict(set)
for m_, ns_ in decl_of.items():
    for n_ in ns_:
        where[n_].add(m_)
tok_cache = {}


def tokens(m):
    if m not in tok_cache:
        t = re.sub(r'--[^\n]*', ' ', re.sub(r'/-.*?-/', ' ', src[m], flags=re.S))
        tok_cache[m] = {p for w in re.findall(r"[A-Za-z_][\w'.₀-₉?!]*", t) for p in w.split('.')}
    return tok_cache[m]


old_clo = {m: closure(imp, imp.get(m, [])) for m in mods}
new_imp = {m: [d for d in imp.get(m, []) if not (m in editable and d in R)] for m in mods}
edits = collections.defaultdict(list)
for u, d in cut:
    edits[u].append(('-', d))
for m in order:
    reach = closure(new_imp, new_imp[m])
    if m in editable:
        want = {dm for n in owned[m] for dm, c in needs.get(n, []) if not artifact(dm, c)} - {m}
        assert not (want & R), (m, want & R)
    elif m in REAL_ONLY:
        want = old_clo[m] - R
    elif m in REAL:
        continue
    elif KEEP:
        want = old_clo[m]
    else:
        # outside the route: only lost modules whose names the module mentions, where the name is
        # not declared by any module it still sees
        lost_all = old_clo[m] - reach
        if not lost_all:
            continue
        seen_mods = reach | {m}
        mentioned = {n for x in lost_all for n in decl_of[x] if not (where[n] & seen_mods)} & tokens(m)
        want = {x for x in lost_all if decl_of[x] & mentioned}
    lost = want - reach
    if not lost:
        continue
    cl = {y: closure(new_imp, [y]) for y in lost}   # final: everything in `lost` precedes m
    add = [x for x in sorted(lost) if not any(x in cl[y] for y in lost if y != x)]
    new_imp[m] += add
    edits[m] += [('+', a) for a in add]
if KEEP:
    for m in mods:
        if m not in REAL:
            assert closure(new_imp, new_imp[m]) == old_clo[m], m
new_real = closure(new_imp, ['Proofs18CoverFejerAllDegrees'])
assert not (new_real & R)
left = REAL - new_real
print(f'region: {len(R)} modules, {L(R)} lines: {" ".join(sorted(R))}')
print(f'real route: {len(REAL)} -> {len(new_real)} modules; {L(REAL)} -> {L(new_real)} lines '
      f'(leaving: {" ".join(sorted(left))})')
rebuild = [m for m in order if m in edits and (OLE / f'{m}.olean').exists()]
for m in order:
    if m in edits:
        tag = '' if (OLE / f'{m}.olean').exists() else ' (no olean)'
        where = 'route' if m in REAL else 'outside'
        print(f'  [{where}] {m}{tag}: ' + ' '.join(f'{s}{d}' for s, d in edits[m]))
print(f'{len(edits)} modules edited, {len(rebuild)} with a local olean to rebuild')
if APPLY:
    for m, es in edits.items():
        p = GS / f'{m}.lean'
        s = p.read_text(encoding='utf8')
        lines = s.split('\n')
        rm = {f'import GowersSzemeredi.{d}' for sign, d in es if sign == '-'}
        add = [f'import GowersSzemeredi.{d}' for sign, d in es if sign == '+']
        for r in rm:
            assert lines.count(r) == 1, (m, r)
        last = max(i for i, l in enumerate(lines) if l.startswith('import '))
        new = []
        for i, l in enumerate(lines):
            if l not in rm:
                new.append(l)
            if i == last:          # additions go where the import block ended, removed or not
                new.extend(add)
        assert sum(1 for l in new if l.startswith('import ')) > 0, m
        p.write_text('\n'.join(new), encoding='utf8', newline='\n')
    (SCR / 'detach_rebuild.txt').write_text(' '.join(rebuild), encoding='utf8')
    print('applied; rebuild list in detach_rebuild.txt')
