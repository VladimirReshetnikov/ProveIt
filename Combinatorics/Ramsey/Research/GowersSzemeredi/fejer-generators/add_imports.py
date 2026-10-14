import json, os, re, sys
GS = sys.argv[2]
added = []
for g in json.load(open(sys.argv[1], encoding='utf8')):
    for x in g['imports']:
        p = os.path.join(GS, x + '.lean')
        t = open(p, encoding='utf8').read()
        line = 'import GowersSzemeredi.' + g['host']
        if re.search('^' + re.escape(line) + '$', t, re.M):
            continue
        last = list(re.finditer(r'^import .*$', t, re.M))[-1]
        t = t[:last.end()] + '\n' + line + t[last.end():]
        open(p, 'w', encoding='utf8', newline='\n').write(t)
        added.append(x + ' -> ' + g['host'])
print('\n'.join(added))
