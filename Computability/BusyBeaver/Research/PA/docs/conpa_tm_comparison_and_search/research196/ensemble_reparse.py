#!/usr/bin/env python3
"""Reparse the promising fusion words against a union of grammar dictionaries."""
from pathlib import Path
exec(Path(__file__).with_name('fuse_h2.py').read_text().split("joint='joint'")[0])
sys.path.insert(0,'research_ipra/newsearch')
import rotation_search as rs
for j in range(12):
    intern(read_grammar(BASE/'work/optimize196'/f'transport_candidates_local_{j}.json'))
axexpanded=rs.expand('x67')
axpath=next(p for p,t in rs.nodes(rs.INITIAL) if t==axexpanded)
d=json.loads(Path('research_ipra/newsearch/repairbase.json').read_text())
trie={}
for p,op,arg in d['sites']:
    cur=trie
    for b in p:cur=cur.setdefault(b,{})
    cur['leaf']=('leaf',op,arg)
def tree(x):return x['leaf'] if 'leaf' in x else (tree(x[0]),tree(x[1]))
t=tree(trie)
for b in axpath:t=t[b]
rev={rs.expand(s):s for s in MACROS if isinstance(s,str)}
def compress(t):
    if t in rev:return rev[t]
    return tuple(map(compress,t)) if isnode(t) else t
intern(compress(t))
for p in (Path(__file__).resolve().parent/'fused_unconditional').glob('assembled_*.json'):
    intern(read_grammar(p))
byfirst.clear()
for q,w in enumerate(words):byfirst[w[0]].append(q)
print('dictionary',len(trees),'baseline',parse(v.read_source(ROOT)[1],128)[0],flush=True)
OUT=Path(__file__).resolve().parent/'fused_unconditional_ensemble';OUT.mkdir(exist_ok=True)
cs=json.loads((OUT.parent/'fused_unconditional/candidates.json').read_text())
best=999;found=[];start=time.time()
for j,c in enumerate(cs):
    word=[tuple(w) if isinstance(w,list) else w for w in c['word']]
    score,p=parse(word,128)
    print(j,'cost',c['cost'],'->',score,'secs',time.time()-start,flush=True)
    if score<best:best=score
    found.append({'cost':score,'parts':[encode(trees[q]) if isnode(trees[q]) else {'terminal':trees[q]} for q in p],'meta':c['meta'],'word':word})
    (OUT/'candidates.json').write_text(json.dumps(found))
(OUT/'receipt.json').write_text(json.dumps({'best':best,'count':len(cs),'dictionary':len(trees),'seconds':time.time()-start}))
