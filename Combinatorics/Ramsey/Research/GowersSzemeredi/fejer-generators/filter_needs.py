"""decl_needs2.txt (with constant names) -> decl_needs_real.txt (modules only), dropping
dependencies on equation lemmas stored in a module that does not define their base declaration
(Lean regenerates those on demand wherever they are needed)."""
import collections
import re

own = collections.defaultdict(set)
rows = []
for l in open('decl_needs2.txt', encoding='utf8'):
    head, ms, same = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    own[m].add(n)
    rows.append((m, n, ms.split(), same))
EQ = re.compile(r'\.(eq_\d+|eq_def|eq_unfold)$')
art = 0
with open('decl_needs_real.txt', 'w', encoding='utf8') as out:
    for m, n, ms, same in rows:
        keep = set()
        for x in ms:
            mod, c = x.split(':', 1)
            b = EQ.sub('', c)
            if b != c and b not in own[mod]:
                art += 1
                continue
            keep.add(mod)
        out.write(f"{m} {n} | {' '.join(sorted(keep))} | {same}\n")
print(art, 'artifact dependencies dropped')
