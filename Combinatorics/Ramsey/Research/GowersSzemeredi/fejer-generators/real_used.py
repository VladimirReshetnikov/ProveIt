"""used_ranges.txt without equation-lemma artifacts.

Lean generates `f.eq_1`, `f.eq_def`, ... on demand and stores them in the module that first needed
them, even when `f` lives elsewhere (e.g. `Fin.consEquiv.eq_1` in a corpus module).  Such a constant
does not make its storing module necessary: any module can regenerate it.  Writes
used_ranges_real.txt keeping only constants whose base declaration is defined in the same module.
usage: real_used.py used_ranges.txt decl_needs.txt
"""
import re
import sys

own = {}
for l in open(sys.argv[2], encoding='utf8'):
    m, n = l.split(' | ')[0].split(' ', 1)
    own.setdefault(m, set()).add(n)
EQ = re.compile(r'\.(eq_\d+|eq_def|eq_unfold|eq_1)$')
kept = dropped = 0
with open('used_ranges_real.txt', 'w', encoding='utf8') as out:
    for l in open(sys.argv[1], encoding='utf8'):
        m, n = l.split()[:2]
        b = EQ.sub('', n)
        if b != n and b not in own.get(m, set()):
            dropped += 1
            continue
        kept += 1
        out.write(l)
print(kept, 'kept,', dropped, 'equation-lemma artifacts dropped')
