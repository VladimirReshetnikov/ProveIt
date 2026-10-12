"""Polynomial sufficient forcing with actual source-equation provenance.

One-sided matching consequences force their positive coordinates to zero.
This is not a complete LP support solver; a mixed-sign fixed point falls
back to ordinary complete discovery. The checker reconstructs source rows
and never imports this forest or elimination code.
"""
from fractions import Fraction
from itertools import combinations, product

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


def _pair_step(rows,forced,check):
    """Find a one-sided consequence in a two-row span, with exact bounds."""
    if len(rows)<2 or not rows or len(forced)==len(rows[0]):return None
    for i,j in combinations(range(len(rows)),2):
        for sa,sb in product((1,-1),repeat=2):
            check();lower=Fraction(0);upper=None
            for k,(a,b)in enumerate(zip(rows[i],rows[j])):
                check()
                if k in forced:continue
                a*=sa;b*=sb
                if not b:
                    if a<0:break
                elif b>0:lower=max(lower,-a/Fraction(b))
                else:upper=-a/Fraction(b) if upper is None else min(upper,-a/Fraction(b))
                if upper is not None and lower>upper:break
            else:
                scale=lower+1 if upper is None else (lower+upper)/2
                added=[]
                for k,(a,b)in enumerate(zip(rows[i],rows[j])):
                    check()
                    if k not in forced and sa*a+scale*sb*b>0:added.append(k)
                if added:return [(i,Fraction(sa)),(j,scale*sb)],added
    return None


def _combined_closure(rows,check):
    """Polynomial sufficient closure; larger row spans may still be needed."""
    forced,single=_closure(rows,check)
    steps=[([(index,Fraction(sign))],added)for index,sign,added in single]
    while True:
        pair=_pair_step(rows,forced,check)
        if pair is None:return forced,steps
        combination,added=pair;forced.update(added);steps.append(pair)
        while True:
            before=len(forced)
            for index,row in enumerate(rows):
                check()
                active=[(i,x)for i,x in enumerate(row)if x and i not in forced]
                if not active:continue
                sign=1 if active[0][1]>0 else -1
                if any(sign*x<0 for _,x in active):continue
                added=[i for i,_ in active];forced.update(added)
                steps.append(([(index,Fraction(sign))],added))
            if len(forced)==before:break


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
    forced,_=_combined_closure(equations,check)
    if not forced:return list(range(width)),None
    augmented=_source_constraints(kernel.prepared,kernel.support,check)
    rows=[row[:width]for row in augmented]
    actual,steps=_combined_closure(rows,check)
    if rows!=equations or actual!=forced:
        raise ArithmeticError('source equation provenance disagrees with matching kernel')
    records=[]
    for coefficients,added in steps:
        check();combination=[]
        for number in range(len(kernel.prepared['matching'])):
            check()
            value=sum(scale*augmented[index][width+number]for index,scale in coefficients)
            if value:
                combination.append([number,value.numerator,value.denominator])
        records.append(dict(row_combination=combination,forced_indices=added))
    proof=dict(schema='normal-sector-matching-support-v1',source_sha256=_source_hash(kernel.triangulation),
        allowed_types=[list(x)for x in kernel.support],steps=records)
    return [i for i in range(width)if i not in forced],proof
