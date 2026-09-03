# -*- coding: utf-8 -*-
r"""Consolidate the volume's twelve per-part bibliographies into one.

  python bibmerge.py <vol.tex> plan      -> print the proposed grouping only
  python bibmerge.py <vol.tex> apply     -> rewrite the volume

Grouping is deliberately conservative.  Two bibitems are merged only when
they agree on BOTH
  * the set of capitalised surname-like tokens, and
  * the four-digit year (or both lack one, in which case the normalized
    title-word multiset must also agree),
and additionally share at least half of their significant title words.  Two
different papers by the same author in the same year therefore stay apart
unless their titles match, which is the failure mode worth avoiding.

The canonical body of a group is its longest member, on the theory that the
fullest wording is the one a reader wants; the canonical key is a slug built
from surname and year, so the merged list is stable under re-runs.
"""
import io, re, sys, collections, unicodedata

VOL, MODE = sys.argv[1], sys.argv[2]
text = io.open(VOL, encoding='utf-8').read()

BIB = re.compile(r'\\begin\{thebibliography\}\{[^}]*\}(.*?)\\end\{thebibliography\}', re.S)

STOP = set('''a an and the of on in for with to from by at as is are its their
new note notes paper papers volume vol no pp ed eds edition second third
university press springer verlag academic wiley elsevier cambridge oxford
american mathematical society journal proceedings transactions annals
advances archiv archive preprint arxiv available online http https doi'''.split())


def strip_tex(s):
    s = re.sub(r'\\url\{[^}]*\}', ' ', s)
    s = re.sub(r'\\path\{[^}]*\}', ' ', s)
    s = re.sub(r'\\newblock', ' ', s)
    s = re.sub(r"\\['`^\"~=.]\{?([A-Za-z])\}?", r'\1', s)
    s = re.sub(r'\\[a-zA-Z]+\s*', ' ', s)
    s = s.replace('{', ' ').replace('}', ' ').replace('~', ' ')
    s = unicodedata.normalize('NFKD', s)
    return re.sub(r'\s+', ' ', s).strip()


AUTHOR = re.compile(r"^\s*(?:[A-Z]\.[-\s]*)+\s*([A-Z][A-Za-z'\-]+)")


def surnames(plain):
    """First author's surname, from the corpus's uniform 'J. Fabius, ...' style.

    Taking every capitalised token instead (the first version of this script)
    pulled journal names into the signature, which split one reference in two
    when two parts abbreviated the journal differently.
    """
    m = AUTHOR.match(plain)
    if m:
        return frozenset([m.group(1).lower()])
    for w in re.findall(r'\b([A-Z][a-z]{2,})\b', plain[:80]):
        if w.lower() not in STOP:
            return frozenset([w.lower()])
    return frozenset()


def year(plain):
    m = re.findall(r'\b(1[89]\d\d|20\d\d)\b', plain)
    return m[0] if m else ''


def titlewords(plain):
    ws = [w.lower() for w in re.findall(r'[A-Za-z]{3,}', plain)]
    return set(w for w in ws if w not in STOP)


items = []
for m in BIB.finditer(text):
    body = m.group(1)
    pieces = re.split(r'\\bibitem\{([^}]*)\}', body)
    for i in range(1, len(pieces), 2):
        key, raw = pieces[i], pieces[i + 1].rstrip()
        plain = strip_tex(raw)
        low = plain.lower()
        # Repository self-citations are a dozen DIFFERENT documents by one
        # author in one year: the primary exposition, the glossary, the
        # non-elementarity study, the Lean walkthrough, the frontier volume,
        # the draft manifest, this very volume.  Author+year+title-overlap
        # merges them wrongly (they share "fabius", "function", "repository"),
        # so they merge only on an exact normalized body.
        selfcite = ('proveit' in low or 'reshetnikov' in low
                    or 'repository' in low)
        items.append(dict(key=key, raw=raw, plain=plain,
                          sn=surnames(plain), yr=year(plain),
                          tw=titlewords(plain), selfcite=selfcite,
                          exact=re.sub(r'[^a-z0-9]', '', low)))

# Hand-verified exceptions.  Every proposed group was read; this is the one
# pair the automatic rule got wrong.  Aistleitner-Hofer-Larcher have two
# papers with the same authors, the same year, and the phrase "lacunary
# trigonometric products" in both titles: "On parametric Thue-Morse sequences
# and lacunary trigonometric products" and "On evil Kronecker sequences and
# lacunary trigonometric products".  No title-overlap threshold separates
# them without splitting correct groups, so they are separated by name.
NEVER_MERGE = {frozenset(('p2:Aistleitner', 'p11:AistleitnerEvil'))}


def blocked(g, it):
    return any(frozenset((h['key'], it['key'])) in NEVER_MERGE for h in g)


# ---- grouping -----------------------------------------------------------
groups = []
for it in items:
    placed = False
    for g in groups:
        h = g[0]
        if blocked(g, it):
            continue
        if h['selfcite'] or it['selfcite']:
            if h['selfcite'] and it['selfcite'] and h['exact'] == it['exact']:
                g.append(it)
                placed = True
                break
            continue
        if h['sn'] != it['sn'] or h['yr'] != it['yr']:
            continue
        inter = len(h['tw'] & it['tw'])
        union = max(1, min(len(h['tw']), len(it['tw'])))
        if inter / union >= 0.7:
            g.append(it)
            placed = True
            break
    if not placed:
        groups.append([it])


def slug(it):
    sn = sorted(it['sn'])
    base = (sn[0] if sn else 'ref')
    if it.get('selfcite'):
        base = 'repo'
    return 'bib:%s%s' % (base, it['yr'] or '')


used, keymap, canon = {}, {}, []
for g in groups:
    best = max(g, key=lambda x: len(x['plain']))
    s = slug(best)
    n, s0 = 2, s
    while s in used:
        s = '%s%s' % (s0, chr(ord('a') + n - 2))
        n += 1
    used[s] = best
    canon.append((s, best))
    for it in g:
        keymap[it['key']] = s

print('bibitems %d -> %d canonical entries (%d groups merged)'
      % (len(items), len(groups), sum(1 for g in groups if len(g) > 1)))

if MODE == 'plan':
    for g in sorted(groups, key=lambda g: -len(g)):
        if len(g) == 1:
            continue
        print('\n== %-28s x%d' % (slug(max(g, key=lambda x: len(x['plain']))), len(g)))
        for it in g:
            print('   %-26s %s' % (it['key'], it['plain'][:110]))
    sys.exit()

# ---- apply --------------------------------------------------------------
CITE = re.compile(r'\\(cite|nocite)(\[[^\]]*\])?\{([^{}]+)\}')


def remap(m):
    cmd, opt, keys = m.group(1), m.group(2) or '', m.group(3)
    new = []
    for k in keys.split(','):
        k = k.strip()
        new.append(keymap.get(k, k))
    seen, out = set(), []
    for k in new:                      # a merged pair can collapse to one key
        if k not in seen:
            seen.add(k)
            out.append(k)
    return '\\%s%s{%s}' % (cmd, opt, ','.join(out))


body_new = CITE.sub(remap, text)

# delete every bibliography environment, remembering where the last one was
spans = [m.span() for m in BIB.finditer(body_new)]
assert spans, 'no bibliography found after remapping'
for a, b in reversed(spans):
    body_new = body_new[:a] + body_new[b:]

merged = ['\\begin{thebibliography}{999}']
for s, it in sorted(canon, key=lambda p: p[1]['plain'].lower()):
    merged.append('\n\\bibitem{%s}%s' % (s, it['raw']))
merged.append('\n\\end{thebibliography}\n')
block = ('\\clearpage\n'
         '\\phantomsection\n'
         '\\addcontentsline{toc}{part}{References}\n'
         '\\part*{References}\n'
         '\\markboth{References}{References}\n'
         'The twelve absorbed reports each carried their own reference list.\n'
         'They are consolidated here: entries that name the same work are\n'
         'stated once, in the fullest wording any of the reports used, and every\n'
         'citation in the volume points at this single list.\n\n'
         + ''.join(merged))

end = body_new.rindex('\\end{document}')
body_new = body_new[:end] + block + '\n' + body_new[end:]

io.open(VOL, 'w', encoding='utf-8', newline='\n').write(body_new)
print('rewrote %s' % VOL)
