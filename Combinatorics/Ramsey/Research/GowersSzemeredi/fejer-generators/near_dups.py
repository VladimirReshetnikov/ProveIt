"""Near-duplicate declarations (parametric copies) on the final route.

usage: python -X utf8 near_dups.py [MINLINES]
Declarations (theorem/lemma) with >= MINLINES non-blank, non-comment lines are shingled on token
6-grams (shingles in > 40 declarations dropped); pairs with Jaccard >= 0.25 are compared line by
line (difflib).  Prints pairs with line ratio >= 0.5, and the total of min(len) over a greedy
matching (each declaration used once) as the size of the prize.
"""
import collections, difflib, os, re, sys
GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
MIN = int(sys.argv[1]) if len(sys.argv) > 1 else 15
src = lambda m: open(os.path.join(GS, m + '.lean'), encoding='utf8').read()
def imports(m):
    return re.findall(r'^import GowersSzemeredi\.(\S+)', src(m), re.M)
seen, st = {'Proofs18CoverFejerAllDegrees'}, ['Proofs18CoverFejerAllDegrees']
while st:
    x = st.pop()
    for d in imports(x):
        if d not in seen:
            seen.add(d); st.append(d)
HD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|structure|instance|example)\s*([^\s(:{\[]*)", re.M)
TOK = re.compile(r"[\w'.₀-₉]+|[^\s\w]")
decls = []
for m in sorted(seen):
    s = re.sub(r'/-.*?-/', lambda t: '\n' * t.group(0).count('\n'), src(m), flags=re.S)
    hs = list(HD.finditer(s))
    for k, h in enumerate(hs):
        if h.group(1) not in ('theorem', 'lemma'):
            continue
        e = hs[k + 1].start() if k + 1 < len(hs) else len(s)
        lines = [re.sub(r'--.*', '', l).strip() for l in s[h.start():e].split('\n')]
        lines = [l for l in lines if l and not l.startswith(('end ', 'namespace ', 'section', 'open ', '/-!', 'set_option', 'variable'))]
        if len(lines) >= MIN:
            toks = TOK.findall(' '.join(lines))
            sh = {tuple(toks[i:i + 6]) for i in range(len(toks) - 5)}
            decls.append((m, h.group(2), lines, sh))
df = collections.Counter(x for d in decls for x in d[3])
idx = collections.defaultdict(list)
for i, d in enumerate(decls):
    for x in d[3]:
        if df[x] <= 40:
            idx[x].append(i)
co = collections.Counter()
for x, l in idx.items():
    for a in range(len(l)):
        for b in range(a + 1, len(l)):
            co[(l[a], l[b])] += 1
pairs = []
for (a, b), c in co.items():
    A, B = decls[a], decls[b]
    sa = {x for x in A[3] if df[x] <= 40}; sb = {x for x in B[3] if df[x] <= 40}
    if not sa or not sb or c / len(sa | sb) < 0.25:
        continue
    r = difflib.SequenceMatcher(None, A[2], B[2], autojunk=False).ratio()
    if r >= 0.5:
        pairs.append((min(len(A[2]), len(B[2])) * r, r, a, b))
pairs.sort(reverse=True)
used, tot = set(), 0
for w, r, a, b in pairs:
    A, B = decls[a], decls[b]
    mark = ''
    if a not in used and b not in used:
        used.add(a); used.add(b); tot += min(len(A[2]), len(B[2])); mark = '*'
    print(f'{mark}{r:.2f} {len(A[2]):4} {A[0]}.{A[1]}  ~  {len(B[2]):4} {B[0]}.{B[1]}')
print(len(decls), 'declarations scanned;', len(pairs), 'pairs; greedy prize (sum of min len):', tot)
