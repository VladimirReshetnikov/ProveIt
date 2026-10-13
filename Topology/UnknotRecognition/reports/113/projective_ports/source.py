"""Source-exact compilers and support-reducing extreme-ray recovery.

These validate rational equations and combinatorial constraints, not 3-manifold
links, geometric embeddedness, peripheral markings, or knot-diagram ancestry.
"""
from dataclasses import dataclass
from .exact import Q, matrix, rational, dot, nullspace, primitive
from .model import Block


@dataclass(frozen=True)
class Source:
    n: int
    equations: tuple
    conflicts: tuple=()

    def __post_init__(self):
        b=Block(self.n,self.equations,((0,)*self.n,),self.conflicts)
        object.__setattr__(self,'equations',b.equations)
        object.__setattr__(self,'conflicts',b.conflicts)


@dataclass(frozen=True)
class Compilation:
    source: Source
    blocks: tuple
    local_to_source: tuple
    masters: tuple=()
    kind: str='two-block'

    def query(self,c,zeros=()):
        c=tuple(rational(v) for v in c); zeros=frozenset(zeros)
        if len(c)!=self.source.n or any(type(j) is not int or not 0<=j<self.source.n for j in zeros):
            raise ValueError('invalid source query')
        masterset=set(self.masters)
        costs=tuple(tuple(Q(0) if j in masterset else c[j] for j in ids) for ids in self.local_to_source)
        zz=tuple(tuple(k for k,j in enumerate(ids) if j in zeros) for ids in self.local_to_source)
        cc=tuple(c[j] for j in self.masters) if self.kind=='variable' else (Q(0),)*self.blocks[0].d
        return costs,cc,zz

    def reconstruct(self,vectors):
        if len(vectors)!=len(self.blocks): raise ValueError('wrong block count')
        result=[None]*self.source.n
        for ids,x in zip(self.local_to_source,vectors):
            if len(ids)!=len(x): raise ValueError('wrong local vector size')
            for j,v in zip(ids,x):
                v=rational(v)
                if result[j] is not None and result[j]!=v:
                    raise ValueError('master copies disagree')
                result[j]=v
        if any(v is None for v in result): raise ValueError('uncovered source coordinate')
        return tuple(result)


def _partition(n,bags):
    bags=tuple(tuple(b) for b in bags)
    flat=[j for b in bags for j in b]
    if any(type(j) is not int or not 0<=j<n for j in flat) or len(flat)!=len(set(flat)):
        raise ValueError('bags overlap or have invalid indices')
    return bags


def compile_two_block(source,left):
    """Unsigned ports from sign-separated cross rows of one source matrix."""
    left=tuple(left); right=tuple(j for j in range(source.n) if j not in left)
    bags=_partition(source.n,(left,right))
    if not left or not right: raise ValueError('two nonempty bags required')
    owner={j:i for i,bag in enumerate(bags) for j in bag}
    local=[[],[]];ports=[[],[]];conf=[[],[]]
    for row in source.equations:
        parts=[tuple(row[j] for j in bag) for bag in bags]
        live=[i for i,part in enumerate(parts) if any(part)]
        if len(live)<2:
            if live: local[live[0]].append(parts[live[0]])
            continue
        a,b=parts
        if all(v>=0 for v in a) and all(v<=0 for v in b):
            ports[0].append(a); ports[1].append(tuple(-v for v in b))
        elif all(v<=0 for v in a) and all(v>=0 for v in b):
            ports[0].append(tuple(-v for v in a)); ports[1].append(b)
        else:
            raise ValueError('cross row is not sign-separated')
    for a,b in source.conflicts:
        if owner[a]!=owner[b]: raise ValueError('cross-block conflict')
        i=owner[a]; conf[i].append((bags[i].index(a),bags[i].index(b)))
    if not ports[0]:
        # A dummy identically zero port represents independent local blocks.
        ports=[[(0,)*len(left)],[(0,)*len(right)]]
    blocks=tuple(Block(len(bags[i]),tuple(local[i]),tuple(ports[i]),tuple(conf[i])) for i in range(2))
    return Compilation(source,blocks,bags)


def private_components(source,masters):
    """Connected components after deleting masters from row/conflict supports."""
    masters=tuple(masters)
    _partition(source.n,(masters,))
    remaining=set(range(source.n))-set(masters); parent={j:j for j in remaining}
    def root(j):
        while parent[j]!=j:
            parent[j]=parent[parent[j]]; j=parent[j]
        return j
    def join(s):
        s=[j for j in s if j in remaining]
        for j in s[1:]: parent[root(j)]=root(s[0])
    for row in source.equations: join(j for j,v in enumerate(row) if v)
    for pair in source.conflicts: join(pair)
    groups={}
    for j in sorted(remaining): groups.setdefault(root(j),[]).append(j)
    return tuple(tuple(v) for v in groups.values()) or ((),)


def compile_variable_separator(source, masters, bags=None):
    """Duplicate nonnegative master coordinates; reject nonlocal constraints."""
    masters=tuple(masters)
    if not masters: raise ValueError('at least one master coordinate required')
    if bags is None: bags=private_components(source,masters)
    bags=_partition(source.n,(masters,)+tuple(bags))[1:]
    if set(masters).union(*(set(b) for b in bags))!=set(range(source.n)):
        raise ValueError('partition omits source coordinates')
    if not bags: raise ValueError('at least one block required')
    ids=tuple(tuple(b)+masters for b in bags)
    owner={j:i for i,b in enumerate(bags) for j in b}; masterset=set(masters)
    equations=[[] for _ in bags]; conflicts=[[] for _ in bags]
    for row in source.equations:
        owners={owner[j] for j,v in enumerate(row) if v and j not in masterset}
        if len(owners)>1: raise ValueError('source row crosses private blocks')
        targets=owners if owners else range(len(bags))
        for i in targets: equations[i].append(tuple(row[j] for j in ids[i]))
    for a,b in source.conflicts:
        owners={owner[j] for j in (a,b) if j not in masterset}
        if len(owners)>1: raise ValueError('source conflict crosses private blocks')
        targets=owners if owners else range(len(bags))
        for i in targets: conflicts[i].append((ids[i].index(a),ids[i].index(b)))
    blocks=[]
    for i,indices in enumerate(ids):
        p=tuple(tuple(Q(j==g) for j in indices) for g in masters)
        blocks.append(Block(len(indices),tuple(equations[i]),p,tuple(conflicts[i])))
    return Compilation(source,tuple(blocks),ids,masters,'variable')


def synchronized_source(blocks, objectives, master=None):
    """Literal common-port equations: useful as a small global test oracle."""
    blocks=tuple(blocks); objectives=tuple(objectives)
    if not blocks or len({b.d for b in blocks})!=1: raise ValueError('invalid synchronized blocks')
    if len(objectives)!=len(blocks): raise ValueError('wrong objective count')
    if master is not None and len(master)!=blocks[0].d: raise ValueError('wrong master objective length')
    offsets=[]; n=0
    for b in blocks: offsets.append(n); n+=b.n
    rows=[];pairs=[];c=[Q(0)]*n
    for i,(b,off,cc) in enumerate(zip(blocks,offsets,objectives)):
        if len(cc)!=b.n: raise ValueError('invalid cost')
        for row in b.equations:
            full=[Q(0)]*n; full[off:off+b.n]=row; rows.append(tuple(full))
        pairs.extend((a+off,h+off) for a,h in b.conflicts)
        c[off:off+b.n]=map(rational,cc)
        if i:
            for p,q in zip(blocks[0].ports,b.ports):
                full=[Q(0)]*n
                full[:blocks[0].n]=p
                full[off:off+b.n]=[-v for v in q]; rows.append(tuple(full))
    if master is not None:
        for j in range(blocks[0].n):
            c[j]+=sum((rational(a)*row[j] for a,row in zip(master,blocks[0].ports)),Q(0))
    return Source(n,tuple(rows),tuple(pairs)),tuple(c),tuple(offsets)


def extreme_witness(source, vector, objective, *, check=lambda:None):
    """Polynomial support descent, retaining positivity and all coordinate zeros."""
    x=tuple(rational(v) for v in vector); c=tuple(rational(v) for v in objective)
    if len(x)!=source.n or len(c)!=source.n or any(v<0 for v in x) or not any(x):
        raise ValueError('invalid source vector')
    if any(dot(row,x) for row in source.equations) or any(x[a] and x[b] for a,b in source.conflicts):
        raise ValueError('source equations or compatibility fail')
    if dot(c,x)<=0: raise ValueError('positive objective required')
    total=sum(x,Q(0));x=tuple(v/total for v in x); trace=[]
    while True:
        check(); s=tuple(j for j,v in enumerate(x) if v)
        rows=[tuple(row[j] for j in s) for row in source.equations]
        if len(nullspace(rows,len(s)))==1: break
        z=primitive(nullspace(rows+[(Q(1),)*len(s)],len(s))[0])
        if dot(tuple(c[j] for j in s),z)<0: z=tuple(-v for v in z)
        step=min(x[j]/(-v) for j,v in zip(s,z) if v<0)
        updated=list(x)
        for j,v in zip(s,z): updated[j]+=step*v
        trace.append({'support':s,'direction':z,'step':str(step)})
        x=tuple(updated)
    return {'coordinates':primitive(x),'descent':tuple(trace)}
