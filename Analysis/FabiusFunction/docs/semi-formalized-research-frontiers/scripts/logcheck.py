# -*- coding: utf-8 -*-
r"""Report the real quality gates from a pdflatex log.

Written because a grep for '^!' reports ZERO errors on a run made with
-file-line-error, where LaTeX prints "file.tex:128: LaTeX Error: ...".
That blindness hid a broken preamble through several builds here.
"""
import io, re, sys, collections

log = io.open(sys.argv[1], encoding='utf-8', errors='replace').read()
lines = log.split('\n')

# both spellings: classic "! ..." and -file-line-error "path:NN: ..."
err = [l for l in lines
       if l.startswith('! ')
       or re.match(r'^\S+\.(tex|sty|cls|def):\d+: ', l)]
undef = [l for l in lines if 'Reference' in l and 'undefined' in l]
undefcite = [l for l in lines if 'Citation' in l and 'undefined' in l]
unusedbib = [l for l in lines if 'There were undefined citations' in l]
undefcs = [l for l in lines if 'Undefined control sequence' in l]
multi = [l for l in lines if 'multiply defined' in l or 'multiply-defined' in l]
dupdest = [l for l in lines if 'destination with the same identifier' in l]
crefmiss = [l for l in lines if 'cref reference format' in l]
nofile = [l for l in lines if 'not found' in l or 'No file' in l]
overfull = re.findall(r'Overfull \\hbox \((\d+(?:\.\d+)?)pt', log)
big = [float(x) for x in overfull if float(x) > 15]

print('errors                : %d' % len(err))
for l in err[:15]:
    print('    %s' % l[:150])
print('undefined references  : %d' % len(undef))
print('undefined citations   : %d%s'
      % (len(undefcite), '  (+ summary line)' if unusedbib else ''))
for l in undefcite[:8]:
    print('    %s' % l[:150])
print('undefined control seqs: %d' % len(undefcs))
for l in undefcs[:8]:
    print('    %s' % l[:150])
print('multiply defined      : %d' % len(multi))
print('duplicate destinations: %d' % len(dupdest))
print('missing cref formats  : %d' % len(crefmiss))
print('missing files         : %d' % len([l for l in nofile if 'No file' not in l]))
print('overfull hboxes       : %d total, %d over 15pt (max %.1fpt)'
      % (len(overfull), len(big), max(big) if big else 0.0))
if undef:
    keys = collections.Counter(re.findall(r"Reference `([^']+)' on page", log))
    print('  first undefined keys : %s'
          % ', '.join(k for k, _ in keys.most_common(10)))
