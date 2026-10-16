"""inline_have.py restricted to private helpers, lambda-free arguments and results that keep every
line within 100 characters.  usage: python -X utf8 inline_have_guarded.py single_use.json MAXLINES"""
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / 'inline_have.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
ih = {'__name__': 'ih', '__file__': str(HERE / 'inline_have.py')}
exec(compile(src, 'inline_have.py', 'exec'), ih)
ph, GS, PAPER, rewrites = ih['ph'], ih['GS'], ih['PAPER'], ih['rewrites']


def ok_text(old, new):
    oldset = set(old.split('\n'))
    return all(len(l) <= 100 for l in new.split('\n') if l not in oldset)


def main():
    res = json.load(open(sys.argv[1], encoding='utf8'))
    maxlines = int(sys.argv[2])
    scratch = HERE / 'inline_have_scratch.lean'
    for x in res:
        if x['kind'] not in ('lemma', 'theorem') or not x['private'] or x['user_mod'] != x['mod'] \
                or PAPER.search(x['name'].split('.')[-1]):
            continue
        p = GS / f"{x['mod']}.lean"
        s = p.read_text(encoding='utf8')
        # the single use line must not pass a lambda argument
        short = x['name'].split('.')[-1]
        use = [l for l in s.split('\n') if re.search(r"(?<![\w'.])" + re.escape(short) + r"(?![\w'])", l)
               and not re.match(r'\s*(private )?(lemma|theorem) ', l)]
        if any(re.search(r'\bfun\b|=>|↦', l) for l in use):
            continue
        texts = [t for t in rewrites(s, x, maxlines) if ok_text(s, t)]
        if not texts:
            continue
        for k, new in enumerate(texts):
            if ph.compiles(new, scratch):
                p.write_text(new, encoding='utf8', newline='\n')
                print(f"{x['mod']}.{x['name']}: inlined (form {k}, {x['lines']} lines)", flush=True)
                break
        else:
            print(f"{x['mod']}.{x['name']}: kept", flush=True)


main()
