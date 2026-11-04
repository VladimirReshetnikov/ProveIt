"""Call graph of literal-zero hypotheses in Compact44.

For each theorem whose binders include `(hz : InternalZero (literal ...`,
record which other such theorems it calls with `hz` as an argument, and
whether `hz` is also used in some other way (a "leaf" use). Prints the leaf
theorems reachable from FixedGraphMarkedHaltDraft.graph_halts, with the
other leaf lemmas each one calls.
"""
import os, re, sys, collections
D = r'C:\ProveIt\Computability\DiophantineConsistency\Lean\DiophantineConsistency\Compact44'
decl = re.compile(r'^(?:private )?theorem (\w+)', re.M)
thms = {}  # qualified name -> (file, body, binder)
for f in os.listdir(D):
    if not f.endswith('.lean'):
        continue
    t = open(os.path.join(D, f), encoding='utf-8').read()
    ns = re.findall(r'^namespace ([\w.]+)', t, re.M)
    ns = ns[0] if ns else ''
    starts = [(m.start(), m.group(1)) for m in decl.finditer(t)]
    for i, (s, n) in enumerate(starts):
        e = starts[i+1][0] if i+1 < len(starts) else len(t)
        chunk = t[s:e]
        k = chunk.find(':= by')
        if k < 0:
            k = chunk.find(':=')
        head, body = chunk[:k], chunk[k:]
        if re.search(r'\(hz : InternalZero \(literal', head):
            short = ns.split('.')[-1] + '.' + n
            thms[short] = (f, body)
names = set(thms)
calls = collections.defaultdict(set)
leafuse = {}
for n, (f, body) in thms.items():
    other = 0
    stmts = []
    for raw in body.split('\n'):
        ind = len(raw) - len(raw.lstrip())
        if stmts and raw.strip() and ind > stmts[-1][0] and not stmts[-1][1].rstrip().endswith(' by'):
            stmts[-1] = (stmts[-1][0], stmts[-1][1] + ' ' + raw.strip())
        else:
            stmts.append((ind, raw))
    for _, line in stmts:
        if not re.search(r'\bhz\b', line):
            continue
        hit = [m for m in names if re.search(r'\b' + re.escape(m) + r'\b', line)]
        hit += [m for m in names if re.search(r'(?<![\w.])' + re.escape(m.split('.')[1]) + r'\b', line)
                and thms[m][0] == f]
        if hit:
            calls[n] |= set(hit)
        else:
            other += 1
    leafuse[n] = other
root = sys.argv[1] if len(sys.argv) > 1 else 'FixedGraphMarkedHaltDraft.graph_halts'
seen, stack = set(), [root]
while stack:
    x = stack.pop()
    if x in seen or x not in thms:
        continue
    seen.add(x)
    stack.extend(calls[x])
print('reachable hz-theorems:', len(seen))
for n in sorted(seen):
    if True:
        print('LEAF' if leafuse[n] else '    ', end=' ')
        print(f'{n:55s} file={thms[n][0]} other-uses={leafuse[n]} calls={sorted(calls[n])}')
