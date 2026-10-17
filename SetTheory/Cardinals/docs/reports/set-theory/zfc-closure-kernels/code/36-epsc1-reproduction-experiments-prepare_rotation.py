"""Prepare a canonical substring grammar search; no logical rows are changed."""
from pathlib import Path
import argparse, json, sys
from functools import cache

BASE = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', type=Path, default=BASE/'experiments/baseline268/grammar.json')
parser.add_argument('--output', type=Path, default=BASE/'experiments/rotation')
args = parser.parse_args()
sys.path.insert(0, str(BASE/'sources/proveit/Computability/BusyBeaver/Research/ZFC'))
import recover_wade_dag as recover
import theory_backend_experiment as theory

nodes,names=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
g=json.loads(args.baseline.read_text())
word=tuple(g['primitive_word'])
strings=[]; ids={}
for n in range(1,len(word)+1):
    for i in range(len(word)-n+1):
        s=word[i:i+n]
        if s not in ids:
            ids[s]=len(strings); strings.append(s)
known={}
for i,(a,b) in enumerate(g['productions']):
    def decode(t):
        return known[t] if t in known else tuple(theory.expand(nodes,t))
    aa,bb=decode(a),decode(b)
    known[300+i]=aa+bb
    known.setdefault(('split',aa+bb),len(aa))
root=decode(g['residual'][-1])
for t in reversed(g['residual'][:-1]):
    a=decode(t);known.setdefault(('split',a+root),len(a));root=a+root
assert root==word
available={tuple(theory.expand(nodes,q)):q for q in list(theory.MACROS)+[161,179,184]}
@cache
def depth(q):
    e=nodes[q][0]
    return 1+(depth(int(e.split()[1])) if e.startswith('ENode ') else 0)
out=args.output;out.mkdir(parents=True,exist_ok=True)
with (out/'input.txt').open('w') as f:
    f.write(f'{len(strings)} {ids[word]} 105 55 5 1\n')
    for s in strings:
        q=available.get(s,-1)
        f.write(f'{len(s)} {int(q>=0)} {depth(q) if q>=0 else 0} {known.get(("split",s),1)}')
        for k in range(1,len(s)):
            f.write(f' {ids[s[:k]]} {ids[s[k:]]}')
        f.write('\n')
(out/'strings.json').write_text(json.dumps({'strings':strings,'available':{str(ids[s]):q for s,q in available.items() if s in ids},'root':ids[word]}))
print('Prepared',len(strings),'distinct substrings of',len(word),'macros')
