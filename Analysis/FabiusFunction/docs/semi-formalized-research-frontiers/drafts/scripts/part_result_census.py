# -*- coding: utf-8 -*-
"""Per-part census of result environments and their proof status."""
import io, re, sys, collections

KINDS = ('theorem', 'proposition', 'lemma', 'corollary', 'definition',
         'conjecture', 'problem', 'example', 'algorithm', 'principle',
         'status', 'remark', 'warning')
OPEN = re.compile(r'\\begin\{(' + '|'.join(KINDS) + r')\}')
PROOF = re.compile(r'\\begin\{proof\}')
PART = re.compile(r'\\part\*?\{')

lines = io.open(sys.argv[1], encoding='utf-8').read().split('\n')
bounds = [i for i, l in enumerate(lines) if PART.match(l)] + [len(lines)]
names = [re.sub(r'\\part\*?\{(.*)', r'\1', lines[i])[:46] for i in bounds[:-1]]

hdr = ('part', 'thm', 'prop', 'lem', 'cor', 'def', 'conj', 'prob', 'proofs')
print('%-48s %4s %4s %4s %4s %4s %4s %4s %6s' % hdr)
tot = collections.Counter()
for k in range(len(bounds) - 1):
    seg = '\n'.join(lines[bounds[k]:bounds[k + 1]])
    c = collections.Counter(OPEN.findall(seg))
    c['proof'] = len(PROOF.findall(seg))
    tot.update(c)
    print('%-48s %4d %4d %4d %4d %4d %4d %4d %6d'
          % (names[k], c['theorem'], c['proposition'], c['lemma'],
             c['corollary'], c['definition'], c['conjecture'], c['problem'],
             c['proof']))
print('%-48s %4d %4d %4d %4d %4d %4d %4d %6d'
      % ('TOTAL', tot['theorem'], tot['proposition'], tot['lemma'],
         tot['corollary'], tot['definition'], tot['conjecture'],
         tot['problem'], tot['proof']))
print()
print('status macros used:')
for m in ('statusproved', 'statusderived', 'statusexisting', 'statusnumerical',
          'statusconditional', 'statusconjectural', 'statusopen'):
    n = len(re.findall(r'\\' + m + r'(?![A-Za-z])', '\n'.join(lines)))
    if n:
        print('  %-20s %3d' % ('\\' + m, n))
