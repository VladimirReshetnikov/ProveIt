"""Polynomial sufficient forcing with actual source-equation provenance.

One-sided matching consequences force their positive coordinates to zero.
This is not a complete LP support solver; a mixed-sign fixed point falls
back to ordinary complete discovery. The checker reconstructs source rows
and never imports this forest or elimination code.
"""
from fractions import Fraction

from .normal_sector import _rref,_source_hash


def _closure(rows,check):
    forced=set();steps=[]
    while True:
        before=len(forced)
        for index,row in enumerate(rows):
            check()
            active=[(i,value)for i,value in enumerate(row)if value and i not in forced]
            if not active:continue
            sign=1 if active[0][1]>0 else -1
            if any(sign*value<0 for _,value in active):continue
            added=[i for i,_ in active];forced.update(added)
            steps.append((index,sign,added))
        if len(forced)==before:return forced,steps


def _kernel_equations(basis,width,check):
    # The existing canonical nullspace gauge has one rightmost unit free
    # coordinate per basis row. Recover its RREF constraints without another
    # solve just to decide whether source provenance compilation is useful.
    free=[next(i for i in range(width-1,-1,-1)if row[i])for row in basis]
    result=[]
    for pivot in range(width):
        check()
        if pivot in free:continue
        row=[Fraction(int(i==pivot))for i in range(width)]
        for column,vector in zip(free,basis):row[column]=-vector[pivot]
        result.append(row)
    return result


def _add(left,right,scale=1):
    result=left.copy()
    for key,value in right.items():
        result[key]=result.get(key,0)+scale*value
        if not result[key]:del result[key]
    return result


def _source_constraints(prepared,support,check):
    index={7*t+4+q:i for i,(t,q)in enumerate(support)}
    m=len(prepared['matching']);n=4*len(prepared['tetrahedra'])
    adjacency=[[]for _ in range(n)];edges=[];constraints=[]
    for number,equation in enumerate(prepared['matching']):
        check()
        triangles={4*(i//7)+i%7:value for i,value in equation.items()if i%7<4 and value}
        label={index[i]:value for i,value in equation.items()if i in index and value}
        proof={number:Fraction(1)}
        if not triangles:
            if label:constraints.append((label,proof))
            continue
        if len(triangles)!=2 or sorted(triangles.values())!=[-1,1]:
            raise ArithmeticError('unexpected source triangle incidence')
        a=next(i for i,value in triangles.items()if value==1)
        b=next(i for i,value in triangles.items()if value==-1)
        edges.append((a,b,label,proof))
        adjacency[a].append((b,label,proof))
        adjacency[b].append((a,{i:-v for i,v in label.items()},{number:Fraction(-1)}))
    potentials=[None]*n;paths=[None]*n
    for start in range(n):
        check()
        if potentials[start]is not None:continue
        potentials[start]={};paths[start]={};queue=[start]
        for a in queue:
            check()
            for b,label,proof in adjacency[a]:
                if potentials[b]is None:
                    potentials[b]=_add(potentials[a],label)
                    paths[b]=_add(paths[a],proof);queue.append(b)
    for a,b,label,proof in edges:
        check()
        row=_add(_add(potentials[a],label),potentials[b],-1)
        if row:constraints.append((row,_add(_add(paths[a],proof),paths[b],-1)))
    width=len(support)
    augmented=[[Fraction(row.get(i,0))for i in range(width)]+
               [Fraction(proof.get(i,0))for i in range(m)]for row,proof in constraints]
    # Only Q columns pivot; the remaining columns track the same exact row
    # operations as source-equation combinations.
    return _rref(augmented,width,check)[0]


def matching_support(kernel,check):
    """Return retained original indices and a replayable sufficient proof."""
    width=len(kernel.support)
    equations=_kernel_equations(kernel.basis,width,check)
    forced,_=_closure(equations,check)
    if not forced:return list(range(width)),None
    augmented=_source_constraints(kernel.prepared,kernel.support,check)
    rows=[row[:width]for row in augmented]
    actual,steps=_closure(rows,check)
    if rows!=equations or actual!=forced:
        raise ArithmeticError('source equation provenance disagrees with matching kernel')
    records=[]
    for index,sign,added in steps:
        check();combination=[]
        for number,value in enumerate(augmented[index][width:]):
            check()
            if value:
                value*=sign
                combination.append([number,value.numerator,value.denominator])
        records.append(dict(row_combination=combination,forced_indices=added))
    proof=dict(schema='normal-sector-matching-support-v1',source_sha256=_source_hash(kernel.triangulation),
        allowed_types=[list(x)for x in kernel.support],steps=records)
    return [i for i in range(width)if i not in forced],proof
