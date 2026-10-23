"""Independent semantic checker for directed-signal Wang tableaux.

This file does not import the builder or any received program. The controlled
machines are finite halting test cases, not alleged halting runs of K215.
"""
from pathlib import Path
from itertools import product
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
rows=[]
for line in (HERE/'upstream/k215.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split(); rows.append((int(q),int(b),int(w),1 if d=='R' else -1,int(t)))
base={(q,b):(w,d,t) for q,b,w,d,t in rows}
base.update({(215,b):(b,0,215) for b in (0,1)})
L,Q,R,V,H=434,435,436,437,438

def h(q,b):return 2*(q+1)+b

def colors(table):
    rs=sorted({t for w,d,t in table.values() if d==1})
    ls=sorted({t for w,d,t in table.values() if d==-1})
    return ({q:6+i for i,q in enumerate(rs)},
            {q:6+len(rs)+i for i,q in enumerate(ls)})

def valid(tile,table=base):
    west,north,east,south=tile
    rs,ls=colors(table)
    if north==V:return south==V and west in (0,1,4) and east in (0,1,2)
    if north==H:return west==east==1 and south in (L,Q,R)
    if north==L:return (west,east,south)==(2,2,0)
    if north==Q:return (west,east,south)==(2,3,1)
    if north==R:return (west,east,south) in ((3,4,h(93,0)),(4,4,0))
    if north in (0,1):
        if west==east==0:return south in (north,H)
        if east==0:
            return any(west==color and south==h(q,north) for q,color in rs.items())
        if west==0:
            return any(east==color and south==h(q,north) for q,color in ls.items())
        return False
    if not 2<=north<=433:return False
    q,b=divmod(north-2,2); w,d,t=table[q,b]
    if q==215:return west==east==0 and south in (north,H)
    if south!=w:return False
    return (west==0 and east==rs[t]) if d==1 else (west==ls[t] and east==0)

def enumerate_semantic():
    """Independent by-current-symbol candidates, not builder tile classes."""
    rs,ls=colors(base); answer=[]
    for north in range(439):
        if north==V:
            candidates=product((0,1,4),(0,1,2),(V,))
        elif north==H:candidates=((1,1,s) for s in (L,Q,R))
        elif north==L:candidates=((2,2,0),)
        elif north==Q:candidates=((2,3,1),)
        elif north==R:candidates=((3,4,h(93,0)),(4,4,0))
        elif north in (0,1):
            candidates=[(0,0,north),(0,0,H)]
            candidates += [(color,0,h(q,north)) for q,color in rs.items()]
            candidates += [(0,color,h(q,north)) for q,color in ls.items()]
        else:
            q,b=divmod(north-2,2); w,d,t=base[q,b]
            if q==215:candidates=[(0,0,north),(0,0,H)]
            elif d==1:candidates=[(0,rs[t],w)]
            else:candidates=[(ls[t],0,w)]
        for west,east,south in candidates:
            tile=(west,north,east,south)
            assert valid(tile)
            answer.append(tile)
    assert len(answer)==len(set(answer))==942
    start=(2,Q,3,1);forbidden=(5,0,0,0)
    return [start,forbidden]+sorted(set(answer)-{start})

def controls():
    out=[]
    # All four movement pairs, with real first action and a moved-into halt.
    for d1,d2,b1,b2 in product((-1,1),(-1,1),(0,1),(0,1)):
        table=dict(base)
        table[93,0]=(b1,d1,1)
        table[1,0]=(b2,d2,215);table[1,1]=(b2,d2,215)
        out.append(table)
    # Longer left/right sweep, including a return to already written cells.
    table=dict(base)
    for q,d,t in [(93,-1,1),(1,-1,2),(2,1,3),(3,1,4),(4,1,215)]:
        for b in (0,1):table[q,b]=(1-b,d,t)
    out.append(table)
    return out

def run(table):
    tape={};head=0;q=0;hist=[]
    for _ in range(20):
        hist.append((dict(tape),head,q))
        if q==215:return hist
        w,d,t=table[q,tape.get(head,0)];tape[head]=w;head+=d;q=t
    raise AssertionError('Control did not halt within its explicit bound')

def test_helix(table,width_extra,height_extra):
    hist=run(table);rs,ls=colors(table)
    low=min(x for _,x,_ in hist);high=max(x for _,x,_ in hist)
    # At least two permanently untouched blank cells beside each V seam.
    xs=3-low; width=xs+high+4+width_extra
    height=len(hist)+1+height_extra
    cells=[];edges=[]
    for t in range(height):
        row=[V];edge=[None]*width
        tape,head,q=hist[min(max(t-1,0),len(hist)-1)]
        for x in range(1,width):
            if t==0:row.append(H)
            elif t==1:row.append(L if x<xs else Q if x==xs else R)
            else:row.append(h(q,tape.get(x-xs,0)) if x==head+xs else tape.get(x-xs,0))
        if t==0:
            for x in range(1,width):edge[x]=(1,1)
        elif t==1:
            for x in range(1,width):edge[x]=(2,2) if x<xs else (2,3) if x==xs else (3,4) if x==xs+1 else (4,4)
        else:
            for x in range(1,width):edge[x]=(0,0)
            if q!=215:
                w,d,nq=table[q,tape.get(head,0)];at=head+xs
                if d==1:edge[at]=(0,rs[nq]);edge[at+1]=(rs[nq],0)
                else:edge[at]=(ls[nq],0);edge[at-1]=(0,ls[nq])
        cells.append(row);edges.append(edge)
    tiles=[[None]*width for _ in range(height)]
    for t in range(height):
        for x in range(1,width):
            west,east=edges[t][x]
            tiles[t][x]=(west,cells[t][x],east,cells[(t+1)%height][x])
        # The seam joins the previous strip's time t-1 to this strip's time t.
        tiles[t][0]=(edges[(t-1)%height][-1][1],V,edges[t][1][0],V)
    N=width*height;word=[None]*N
    for t in range(height):
        for x in range(width):word[(-(x-xs)-width*(t-1))%N]=tiles[t][x]
    assert word[0]==(2,Q,3,1) and word.count(word[0])==1
    for i,(west,north,east,south) in enumerate(word):
        assert valid(word[i],table),(i,word[i])
        assert east==word[(i-1)%N][0]
        assert south==word[(i-width)%N][1]
    return N

if __name__=='__main__':
    ordered=enumerate_semantic();given=json.loads((HERE/'wang943_tiles.json').read_text())
    assert ordered==[tuple(x) for x in given]
    total=0;helices=0
    for table in controls():
        for dw,dh in product(range(5),range(5)):
            total+=test_helix(table,dw,dh);helices+=1
    receipt=dict(status='PASS',independently_counted_tiles=len(ordered),
                 independent_semantic_count=942,forbidden_added=1,
                 exact_order_matches=True,controlled_machines=17,
                 padded_helices=helices,local_tiles_and_both_overlaps_checked=total,
                 source_sha256=sha256((HERE/'upstream/k215.tm').read_bytes()).hexdigest(),
                 scope='Finite controlled tests only, not a K215 halting claim or kernel proof.')
    (HERE/'wang943_independent_language_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
