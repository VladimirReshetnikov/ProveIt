"""Source-bound rank-one column-cut compilation and validated local models."""
from dataclasses import dataclass
from fractions import Fraction as F
from .exact import nullspace, primitive, rref, dot

@dataclass(frozen=True)
class Node:
    names: tuple[str,...]  # globally unique original nonnegative coordinates
    ports: tuple[int,...]  # edge ID is its nonroot child node number
    matrix: tuple[tuple[F,...],...]
    pairs: tuple[tuple[int,int],...]=()

@dataclass(frozen=True)
class Model:
    parent: tuple[int,...]  # node 0 is root, parent[0] == -1
    nodes: tuple[Node,...]

    def validate(self):
        n=len(self.nodes)
        if n==0 or len(self.parent)!=n or self.parent[0]!=-1:
            raise ValueError('invalid rooted tree')
        if any(type(p) is not int or not 0<=p<n for p in self.parent[1:]):
            raise ValueError('invalid parent')
        for v in range(1,n):
            seen=set()
            u=v
            while u!=0:
                if u in seen:
                    raise ValueError('parent cycle')
                seen.add(u)
                u=self.parent[u]
        names=[]
        for v,node in enumerate(self.nodes):
            expected=set(i for i in range(1,n) if self.parent[i]==v)
            if v:
                expected.add(v)
            if set(node.ports)!=expected or len(node.ports)!=len(expected):
                raise ValueError('port incidence mismatch')
            if any(not isinstance(name,str) or not name for name in node.names):
                raise ValueError('invalid coordinate name')
            names.extend(node.names)
            k=len(node.names)+len(node.ports)
            if any(len(row)!=k for row in node.matrix):
                raise ValueError('matrix width mismatch')
            for row in node.matrix:
                for a in row:
                    if not isinstance(a,(int,F)) or isinstance(a,bool):
                        raise ValueError('exact rational entries required')
            for i,j in node.pairs:
                if type(i) is not int or type(j) is not int or not 0<=i<j<len(node.names):
                    raise ValueError('conflicts must be local original-coordinate pairs')
        if len(set(names))!=len(names):
            raise ValueError('source columns must occur exactly once')
        return self

    def order(self):
        children=[[] for _ in self.nodes]
        for v,p in enumerate(self.parent[1:],1):
            children[p].append(v)
        order=[]
        stack=[0]
        while stack:
            v=stack.pop()
            order.append(v)
            stack.extend(children[v])
        return tuple(reversed(order))

    def names(self):
        return tuple(x for n in self.nodes for x in n.names)


def _column_basis(A, cols):
    m=len(A)
    transposed=[[F(A[i][j]) for i in range(m)] for j in cols]
    basis,_=rref(transposed,m)
    return basis


def intersection_line(A,S,T):
    """Return primitive intersection generator, or reject dimension > one."""
    m=len(A)
    U=_column_basis(A,S)
    V=_column_basis(A,T)
    equations=[[u[i] for u in U]+[-v[i] for v in V] for i in range(m)]
    K=nullspace(equations,len(U)+len(V))
    # U,V are bases: the relation space maps injectively to the intersection.
    if len(K)>1:
        raise ValueError('cut intersection dimension exceeds one')
    if not K:
        return tuple(0 for _ in range(m))
    return primitive([dot([u[i] for u in U],K[0][:len(U)]) for i in range(m)],True)


def compile_source(A, n, bags, parent, pairs=()):
    """Exact compiler. Decomposition discovery is NOT performed here.

    A is m by n and bags partition columns. Every forbidden pair must remain
    in one bag. Each displayed column-space cut is checked, including empty
    intersections. Returns (local model, primitive cut generators).
    """
    A=tuple(tuple(F(x) for x in row) for row in A)
    if any(len(row)!=n for row in A):
        raise ValueError('source width mismatch')
    bags=tuple(tuple(b) for b in bags)
    parent=tuple(parent)
    if sorted(j for b in bags for j in b)!=list(range(n)):
        raise ValueError('bags must partition source columns')
    owner={j:v for v,b in enumerate(bags) for j in b}
    for i,j in pairs:
        if not 0<=i<j<n or owner[i]!=owner[j]:
            raise ValueError('a forbidden pair crosses a bag boundary')
    skeleton=[]
    for v,b in enumerate(bags):
        ports=tuple(([v] if v else [])+[i for i in range(1,len(bags)) if parent[i]==v])
        skeleton.append(Node(tuple(str(j) for j in b),ports,()))
    model=Model(parent,tuple(skeleton)).validate()
    sub=[set(b) for b in bags]
    for v in model.order():
        if v:
            sub[parent[v]].update(sub[v])
    w={}
    for v in range(1,len(bags)):
        w[v]=intersection_line(A,sorted(sub[v]),sorted(set(range(n))-sub[v]))
    nodes=[]
    for v,node in enumerate(skeleton):
        rows=[]
        for r,row in enumerate(A):
            rows.append(tuple(row[j] for j in bags[v])+tuple(
                (-1 if e==v else 1)*w[e][r] for e in node.ports))
        for q,e in enumerate(node.ports):
            if not any(w[e]):
                z=[F(0)]*(len(bags[v])+len(node.ports))
                z[len(bags[v])+q]=F(1)
                rows.append(tuple(z))
        where={j:i for i,j in enumerate(bags[v])}
        localpairs=tuple((where[i],where[j]) if where[i]<where[j] else (where[j],where[i])
                         for i,j in pairs if owner[i]==v)
        nodes.append(Node(node.names,node.ports,tuple(rows),localpairs))
    return Model(parent,tuple(nodes)).validate(),w


def source_from_model(model):
    """Eliminate all free scalar ports; return equations on original columns.

    Used by independent small-model oracles. This does not assert source
    ancestry for an arbitrary user-created model.
    """
    model.validate()
    names=model.names()
    idx={s:i for i,s in enumerate(names)}
    nx=len(names); ne=len(model.nodes)-1
    X=[]; P=[]
    for node in model.nodes:
        for row in node.matrix:
            xx=[F(0)]*nx; pp=[F(0)]*ne
            for j,s in enumerate(node.names):
                xx[idx[s]]=row[j]
            for j,e in enumerate(node.ports):
                pp[e-1]=row[len(node.names)+j]
            X.append(xx); P.append(pp)
    left=nullspace([[P[i][e] for i in range(len(P))] for e in range(ne)],len(P))
    A=[tuple(dot(a,[X[r][j] for r in range(len(X))]) for j in range(nx)) for a in left]
    pairs=tuple(sorted((idx[node.names[i]],idx[node.names[j]])) for node in model.nodes for i,j in node.pairs)
    return tuple(A),names,tuple(pairs)


def verify_source_compilation(A,n,bags,parent,pairs,model,generators):
    """Polynomial exact source replay; does not call the source compiler.

    Rank tests certify each one-dimensional intersection and each proposed
    generator's membership. Local rows are then compared with original rows.
    """
    from .exact import rank
    try:
        model.validate()
        A=tuple(tuple(F(x) for x in row) for row in A)
        bags=tuple(tuple(b) for b in bags);parent=tuple(parent)
        if any(len(row)!=n for row in A) or sorted(j for b in bags for j in b)!=list(range(n)):
            return False
        if parent!=model.parent or len(bags)!=len(model.nodes):return False
        if set(generators)!=set(range(1,len(bags))):return False
        owner={j:v for v,b in enumerate(bags) for j in b}
        if any(not 0<=i<j<n or owner[i]!=owner[j] for i,j in pairs):return False
        sub=[set(b) for b in bags]
        for v in model.order():
            if v:sub[parent[v]].update(sub[v])
        whole_rank=rank(A,n)
        for e in range(1,len(bags)):
            S=sorted(sub[e]);T=sorted(set(range(n))-sub[e])
            AS=[[row[j] for j in S] for row in A];AT=[[row[j] for j in T] for row in A]
            rs=rank(AS,len(S));rt=rank(AT,len(T));lam=rs+rt-whole_rank
            w=tuple(generators[e])
            if len(w)!=len(A) or any(type(z) is not int for z in w):return False
            if lam==0:
                if any(w):return False
            elif lam==1:
                if not any(w) or primitive(w,True)!=w:return False
                if rank([row+[w[i]] for i,row in enumerate(AS)],len(S)+1)!=rs:return False
                if rank([row+[w[i]] for i,row in enumerate(AT)],len(T)+1)!=rt:return False
            else:return False
        for v,node in enumerate(model.nodes):
            if node.names!=tuple(str(j) for j in bags[v]):return False
            k=len(node.names)+len(node.ports)
            expected=[]
            for r,row in enumerate(A):
                expected.append(tuple(row[j] for j in bags[v])+tuple(
                    (-1 if e==v else 1)*generators[e][r] for e in node.ports))
            for j,e in enumerate(node.ports):
                if not any(generators[e]):
                    row=[F(0)]*k;row[len(node.names)+j]=F(1);expected.append(tuple(row))
            where={j:i for i,j in enumerate(bags[v])}
            ep=tuple(tuple(sorted((where[i],where[j]))) for i,j in pairs if owner[i]==v)
            if tuple(expected)!=node.matrix or ep!=node.pairs:return False
        return True
    except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):
        return False
