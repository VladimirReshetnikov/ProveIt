"""Local binary source-coloring lifts for connected periods or detached repeats.

The general normalizer's global coloring/address exporter is not included. These
verified local operators are its precise lifting primitives, not a native noose.
"""
from .model import Graph,components

def coloring_value(g:Graph,c):
    if len(c)!=g.n or any(type(x)is not int or x not in (0,1) for x in c):raise ValueError('invalid coloring')
    q=0;f=0
    for a,b in g.edges:
        if c[a]!=c[b]:q+=1
        else:f|=1<<c[a]
    return q,f

def lift_colors(g:Graph,n:int,colors:list,k:int=3,*,detached:bool=False):
    if type(n)is not int or n<1 or not colors or len(colors)>n:raise ValueError('invalid repeat counts')
    if not detached:
        g.validate_tile()
        if len(components(g)[1])!=1:raise ValueError('a serial lifted period must be connected')
    else:
        if g.left or g.right:raise ValueError('detached graph has named ports')
    values=[coloring_value(g,c) for c in colors]
    if sum(q for q,f in values)>k:raise ValueError('coloring exceeds threshold')
    for a,b in zip(colors,colors[1:]):
        if not detached and [a[x] for x in g.right]!=[b[x] for x in g.left]:raise ValueError('seam colors disagree')
    repeats=[1]*len(colors)
    if n>len(colors):
        try:z=next(i for i,(q,f) in enumerate(values) if q==0)
        except StopIteration:raise ValueError('no zero-cost repetition to lift') from None
        repeats[z]+=n-len(colors)
    runs=[dict(colors=list(c),repeat_hex=hex(r)) for c,r in zip(colors,repeats)]
    if not verify_runs(g,n,runs,k,detached=detached):raise AssertionError('produced lift did not replay')
    return runs

def verify_runs(g:Graph,n:int,runs:list,k:int=3,*,detached:bool=False)->bool:
    try:
        if type(n)is not int or n<1 or not runs:return False
        count=0;cost=0;prev=None
        for run in runs:
            c=run['colors'];r=int(run['repeat_hex'],16)
            if r<1:return False
            q,f=coloring_value(g,c);count+=r;cost+=q*r
            if not detached:
                left=[c[x] for x in g.left];right=[c[x] for x in g.right]
                if prev is not None and prev!=left:return False
                if r>1 and left!=right:return False
                prev=right
        return count==n and cost<=k
    except (ValueError,TypeError,KeyError,IndexError):return False
