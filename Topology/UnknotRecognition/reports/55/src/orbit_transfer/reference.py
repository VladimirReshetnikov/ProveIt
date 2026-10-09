"""Small research AHT scheduler and eager-vector control, NOT maintained dispatch.

The scheduler adapts the published AHT rules and ProveIt's MIT-0 implementation
at b365341b1939c69a26b31bb5d05a097d4572692c. Its restart merger is deliberately
simple. Production's adaptive merger, resource dispatch, and geometric code are
not copied. Use native traces when integrating. Literal graphs are an independent
small-instance correctness oracle, not an algorithm for binary universes.
"""
from __future__ import annotations
from math import gcd
from .trace import normalize, check_trace


def make_trace(size, pairings, *, version=2, max_cycles=100000):
    if type(size) is not int or size < 0 or version not in (1,2):
        raise ValueError('invalid universe or proof version')
    rows = [normalize(x,size) for x in pairings]
    original = [list(x) for x in rows]
    n, total, cycles, events = size, 0, 0, []
    while n:
        cycles += 1
        if cycles > max_cycles: raise RuntimeError('reference cycle allowance exhausted')
        for i in range(len(rows)-1,-1,-1):
            a,b,c,d,s = rows[i]
            if a == c and (s == 1 or a == b):
                events.append(dict(op='delete',index=i)); rows.pop(i)
        occupied=[]
        for lo,hi in sorted((lo,hi+1) for a,b,c,d,_ in rows
                             for lo,hi in ((a,b),(c,d))):
            if occupied and lo <= occupied[-1][1]:
                occupied[-1]=(occupied[-1][0],max(hi,occupied[-1][1]))
            else: occupied.append((lo,hi))
        gaps=[]; end=0
        for lo,hi in occupied:
            if end < lo: gaps.append((end,lo))
            end=hi
        if end < n: gaps.append((end,n))
        if gaps:
            events.append(dict(op='contract',gaps=[[a,b-1] for a,b in gaps]))
            def shifted(v): return v-sum(b-a for a,b in gaps if b <= v)
            rows=[tuple(shifted(v) for v in row[:4])+(row[4],) for row in rows]
            lost=sum(b-a for a,b in gaps); n-=lost; total+=lost
        if not n: break
        for i,(a,b,c,d,s) in enumerate(rows):
            if s == -1 and b >= c:
                events.append(dict(op='trim',index=i))
                left=(a+d-1)//2; rows[i]=(a,left,a+d-left,d,-1)
        while True:
            merged=False
            for i in range(len(rows)):
                a,b,c,d,s=rows[i]; p=c-a
                if s != 1 or not 0 < p <= b-a+1: continue
                for j in range(i+1,len(rows)):
                    aa,bb,cc,dd,ss=rows[j]; q=cc-aa
                    if ss != 1 or not 0 < q <= bb-aa+1: continue
                    g=gcd(p,q)
                    if min(d,dd)-max(a,aa)+1 >= p+q-(g if version==2 else 0):
                        events.append(dict(op='merge',left=i,right=j))
                        lo,hi=min(a,aa),max(d,dd)
                        rows[i]=(lo,hi-g,lo+g,hi,1); rows.pop(j)
                        merged=True; break
                if merged: break
            if not merged: break
        ci=max(range(len(rows)),key=lambda j:(rows[j][3],-rows[j][2],
                                             -rows[j][0],int(rows[j][4]==-1)))
        carrier=rows[ci]; ca,cb,cc,cd,cs=carrier
        for i,row in enumerate(rows):
            a,b,c,d,s=row
            if i == ci or not cc <= c <= d <= cd: continue
            domain=cc <= a <= b <= cd
            if cs == -1:
                sp,tp=int(domain),1
                if domain: a,b=ca+cd-b,ca+cd-a
                c,d=ca+cd-d,ca+cd-c
                s=s*(-1)*(-1 if domain else 1)
            else:
                p=cc-ca; tp=(c-cc)//p+1; sp=(a-cc)//p+1 if domain else 0
                a-=sp*p; b-=sp*p; c-=tp*p; d-=tp*p
            events.append(dict(op='transmit',transmitter=ci,target=i,
                               source_power=sp,target_power=tp))
            rows[i]=normalize((a,b,c,d,s),n)
        cut=max([cc]+[row[3]+1 for i,row in enumerate(rows) if i != ci])
        if not cc <= cut < n or cd != n-1:
            raise ArithmeticError('reference did not expose a suffix')
        events.append(dict(op='truncate',index=ci,new_size=cut))
        lost=n-cut
        if cut==cc: rows.pop(ci)
        elif cs==1: rows[ci]=(ca,cb-lost,cc,cut-1,1)
        else: rows[ci]=(ca+lost,cb,cc,cut-1,-1)
        n=cut
    return dict(version=version,size=size,pairings=original,orbit_count=total,
                operations=events)


def literal_components(size, pairings):
    if size > 100000: raise ValueError('literal oracle only for small universes')
    parent=list(range(size))
    def find(x):
        while parent[x] != x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    for raw in pairings:
        a,b,c,d,s=normalize(raw,size)
        for x in range(a,b+1):
            y=x+c-a if s==1 else a+d-x
            left,right=find(x),find(y)
            parent[left]=right
    groups={}
    for x in range(size): groups.setdefault(find(x),[]).append(x)
    return list(groups.values())


def eager_histogram(size, pairings, proof, intervals, dimension):
    """Independent numerical, dense-vector replay control, with value coalescing.

    An interval is (lo, hi, sequence_of_dimension_integer_weights). Includes
    source proof replay and input preparation; excludes trace discovery.
    """
    checked=check_trace(size,pairings,proof)
    zero=(0,)*dimension
    def sweep(n,pieces):
        events={0:[0]*dimension,n:[0]*dimension}
        for lo,hi,value,multiplier in pieces:
            if lo==hi or not multiplier: continue
            for x,sgn in ((lo,multiplier),(hi,-multiplier)):
                change=events.setdefault(x,[0]*dimension)
                for j,v in enumerate(value): change[j]+=sgn*v
        points=sorted(events); current=[0]*dimension; out=[]
        for lo,hi in zip(points,points[1:]):
            for j,v in enumerate(events[lo]): current[j]+=v
            v=tuple(current)
            if out and out[-1][2]==v: out[-1]=(out[-1][0],hi,v)
            else: out.append((lo,hi,v))
        return out
    runs=sweep(size,[(a,b,tuple(v),1) for a,b,v in intervals]); hist={}
    for ev in checked.operations:
        if ev.kind=='contract':
            points=sorted({0,ev.old_size}|{p for a,b,_ in runs for p in (a,b)}
                          |{p for a,b in ev.gaps for p in (a,b)})
            output=[]; j=0; lost=0
            for lo,hi in zip(points,points[1:]):
                while runs[j][1] <= lo: j+=1
                value=runs[j][2]
                if any(a<=lo<b for a,b in ev.gaps):
                    hist[value]=hist.get(value,0)+hi-lo; lost+=hi-lo
                else: output.append((lo-lost,hi-lost,value))
            runs=output
        else:
            pieces=[]; cut=ev.new_size
            for lo,hi,value in runs:
                if lo<cut: pieces.append((lo,min(hi,cut),value,1))
                left=max(lo,cut)
                if left>=hi: continue
                if ev.kind=='reflection':
                    pieces.append((ev.parameter+ev.old_size-hi,
                                   ev.parameter+ev.old_size-left,value,1))
                else:
                    p=ev.parameter; base=cut-p; q,r=divmod(hi-left,p)
                    pieces.append((base,cut,value,q))
                    start=base+(left-base)%p; first=min(r,cut-start)
                    pieces.append((start,start+first,value,1))
                    pieces.append((base,base+r-first,value,1))
            runs=sweep(cut,pieces)
    return hist


def sparse_eager_histogram(size, pairings, proof, intervals):
    """Stronger sparse-payload control: interval values are dictionaries.

    Returns histogram keys as sorted (coordinate,value) tuples. Empty coordinates
    are omitted. This is an experimental control, not a production dispatch path.
    """
    checked=check_trace(size,pairings,proof)
    def sweep(n,pieces):
        events={0:{},n:{}}
        def add(target,value,factor):
            for key,v in value.items():
                updated=target.get(key,0)+factor*v
                if updated: target[key]=updated
                else: target.pop(key,None)
        for lo,hi,value,multiplier in pieces:
            if lo==hi or not multiplier: continue
            add(events.setdefault(lo,{}),value,multiplier)
            add(events.setdefault(hi,{}),value,-multiplier)
        points=sorted(events); current={}; out=[]
        for lo,hi in zip(points,points[1:]):
            add(current,events[lo],1)
            if out and out[-1][2]==current: out[-1]=(out[-1][0],hi,out[-1][2])
            else: out.append((lo,hi,current.copy()))
        return out
    runs=sweep(size,[(a,b,dict(v),1) for a,b,v in intervals]); hist={}
    for ev in checked.operations:
        if ev.kind=='contract':
            points=sorted({0,ev.old_size}|{p for a,b,_ in runs for p in (a,b)}
                          |{p for a,b in ev.gaps for p in (a,b)})
            output=[]; j=0;lost=0
            for lo,hi in zip(points,points[1:]):
                while runs[j][1]<=lo:j+=1
                value=runs[j][2]
                if any(a<=lo<b for a,b in ev.gaps):
                    key=tuple(sorted(value.items())); hist[key]=hist.get(key,0)+hi-lo;lost+=hi-lo
                else:output.append((lo-lost,hi-lost,value))
            runs=output
        else:
            pieces=[];cut=ev.new_size
            for lo,hi,value in runs:
                if lo<cut:pieces.append((lo,min(hi,cut),value,1))
                left=max(lo,cut)
                if left>=hi:continue
                if ev.kind=='reflection':
                    pieces.append((ev.parameter+ev.old_size-hi,ev.parameter+ev.old_size-left,value,1))
                else:
                    p=ev.parameter;base=cut-p;q,r=divmod(hi-left,p)
                    pieces.append((base,cut,value,q))
                    start=base+(left-base)%p;first=min(r,cut-start)
                    pieces.append((start,start+first,value,1))
                    pieces.append((base,base+r-first,value,1))
            runs=sweep(cut,pieces)
    return hist
