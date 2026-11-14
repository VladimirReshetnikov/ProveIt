import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent/'tooling'))
import source_language as s
import independent_runtime as r
HERE=Path(__file__).parent
table=r.table(HERE/'upstream/data/pa196.tm')
rows=json.loads((HERE/'sites.json').read_text())
graph,checks=s.graph_arithmetic(rows)
assert graph==s.graph_intervals(rows)
def frame(path,vs,gap=48):
    cells={31,32+gap}
    cells.update(32+i for i,b in enumerate(path) if b=='1')
    h=33+gap
    for v in vs:
        cells.update(range(h+1,h+v+2));h+=v+2
    return cells
def chunks(cells):return [sum(1<<(x-64*i) for x in cells if 64*i<=x<64*(i+1)) for i in range(4)]
tests=[];uncovered=set(table)
for i,(path,op,arg) in enumerate(rows):
 for positive in ([False,True] if op=='CD' else [False]):
    v=[0]*9
    if positive:v[arg]=1
    physical=[v[j] for j in sorted(range(9),key=lambda j:r.PHY[j])]+[0]
    a=frame(path,physical);out=physical.copy();gap=48
    effect,targets=graph[i]
    if op=='CH':b=set();halt=1
    else:
        halt=0;j=targets[int(positive)] if op=='CD' else targets[0]
        if op=='CI':out[r.PHY[arg]]+=1;out.append(1)
        if op=='CD' and positive:out[r.PHY[arg]]-=1;gap+=1
        b=frame(rows[j][0],out,gap)
    q=75;h=32;tape=a.copy();used=set()
    for t in range(5000):
        if t and ((halt and q==196) or (not halt and q==75 and h==32 and tape==b)):break
        rb=int(h in tape);used.add((q,rb));w,d,q=table[q,rb]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    else:raise RuntimeError((i,positive,q,h))
    tests.append(dict(site=i,pos=positive,start=chunks(a),goal=chunks(b),halt=halt,steps=t,used=used))
ordered=[];remaining=list(range(len(tests)))
while uncovered:
    k=max(remaining,key=lambda k:len(tests[k]['used']&uncovered))
    got=tests[k]['used']&uncovered
    if not got:break
    ordered.append(k);uncovered-=got;remaining.remove(k)
ordered+=remaining
with open(HERE/'macro_tests.txt','w') as f:
 print(len(tests),file=f)
 for k in ordered:
    x=tests[k];print(x['site'],int(x['pos']),x['halt'],x['steps'],*x['start'],*x['goal'],*[sum(1<<(q-64*k) for q in {q for q,b in x['used']} if 64*k<=q<64*(k+1)) for k in range(4)],file=f)
native=list(dict.fromkeys(q for q,b in r.table(HERE/'tooling/pa196.native.tm')))
core={int(l.split()[0]) for l in (HERE/'protected-core.txt').read_text().splitlines()}
drops=[i for i,n in enumerate(native) if n in core]
(HERE/'drops.txt').write_text(' '.join(map(str,drops))+'\n')
print({'cases':len(tests),'cover_tests':len(ordered)-len(remaining),'uncovered':sorted(uncovered),'drops':drops,'max_parent_steps':max(x['steps'] for x in tests)})
