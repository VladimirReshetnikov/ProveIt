#!/usr/bin/env python3
"""Conservative bounded tape windows observed by the symbolic contract checker.

Variable run lengths and opaque register files are overapproximated, and
self-sweeping controls are excluded. Candidate survivors must subsequently
pass the full source contracts and startup, which are the correctness gate.
"""
import sys,json,itertools,functools
from pathlib import Path
P=Path(__file__).resolve().parents[2]/'machine_195s8'
sys.path.insert(0,str(P/'reference_pa195'))
import build_verify as v
c=v.c
rows=v.table(P/'pa195_scanner8.native.tm')
t=c.read_grammar(P/'grammar.json')
sites,cfg,cs=c.source(t)
L,R=map(int,sys.argv[1:3]) if len(sys.argv)>2 else (3,1)
W=L+R+1
eligible=set(q for q,b in rows)-c.BOXSTATES-{84}
eligible={q for q in eligible if all(rows[q,b][2]!=q for b in (0,1))}
contexts={q:set() for q in eligible}

@functools.lru_cache(maxsize=16384)
def prefixes(seg,k):
    if k<=0:return {()}
    if not seg:return {(0,)*k}
    x=seg[0];tail=seg[1:]
    if x[0]=='b':return {(x[1],)+a for a in prefixes(tail,k-1)}
    if x[0]=='x':return set(itertools.product((0,1),repeat=k))
    assert x[0]=='r'
    _,b,a,z=x
    if a==0:
        assert z>=0
        z=min(k,z)
        return {(b,)*z+t for t in prefixes(tail,k-z)}
    # All possible lengths >= max(0,z), a sound superset of a*n+z.
    out=set()
    for n in range(min(k,max(0,z)),k+1):
        out.update({(b,)*n+t for t in prefixes(tail,k-n)})
    return out

def observe(s):
    q,onl,left,right=s
    if q not in eligible:return
    if onl:
        for a in prefixes(left,L+1):
            for b in prefixes(right,R):
                win=tuple(reversed(a[1:]))+(a[0],)+b
                contexts[q].add(sum(x<<i for i,x in enumerate(win)))
    else:
        for a in prefixes(left,L):
            for b in prefixes(right,R+1):
                win=tuple(reversed(a))+b
                contexts[q].add(sum(x<<i for i,x in enumerate(win)))

rv=c.validate(rows,cs,observe=observe)
assert rv['ok'],rv
q,h,ones=74,0,set()
for tick in range(59164):
    if q in eligible:
        contexts[q].add(sum(int(h+j in ones)<<(j+L) for j in range(-L,R+1)))
    b=int(h in ones);w,d,q=rows[q,b]
    (ones.add if w else ones.discard)(h);h+=1 if d else -1
assert (q,h)==(84,-2)
out={'window_left':L,'window_right':R,'candidates':sorted(eligible),
     'contexts':{q:sorted(ss) for q,ss in contexts.items()},
     'rows':[[q,b,w,int(d),n] for (q,b),(w,d,n) in sorted(rows.items())],
     'contracts':rv,'startup_steps':59164}
Path(__file__).with_name('contexts.json').write_text(json.dumps(out,indent=2)+'\n')
states=sorted(set(q for q,b in rows))
print(json.dumps({'eligible':len(eligible),'empty_contexts':[q for q in eligible if not contexts[q]],'patterns':sum(map(len,contexts.values())),'runtime':rv}))
with Path(__file__).with_name('contexts.txt').open('w') as f:
    f.write(f'{L} {R} {len(states)} {len(eligible)}\n')
    for q in states:
        f.write(str(q)+' '+ ' '.join(' '.join(map(str,[w,int(d),n])) for w,d,n in [rows[q,0],rows[q,1]])+'\n')
    for q in sorted(eligible):f.write(f'{q} {len(contexts[q])} '+ ' '.join(map(str,sorted(contexts[q])))+'\n')
