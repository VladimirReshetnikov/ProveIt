"""Polynomial universality test for a fixed bank of double-cover characters.

Characters are identified with vectors by the nonsingular symplectic form.
Universality here concerns essential SEPARATING simple curves on Sigma_g.
"""
from __future__ import annotations
from .binary import symplectic, rank


def analyze_bank(genus: int, characters):
    if type(genus) is not int or genus < 2: raise ValueError('genus >= 2 required')
    values=tuple(characters)
    if any(type(x) is not int or not 0<x<1<<(2*genus) for x in values):
        raise ValueError('characters must be nonzero 2g-bit vectors')
    n=len(values)
    parent=list(range(n)); sizes=[1]*n
    def find(a):
        while parent[a]!=a:
            parent[a]=parent[parent[a]];a=parent[a]
        return a
    def union(a,b):
        a,b=find(a),find(b)
        if a!=b:
            if sizes[a]<sizes[b]: a,b=b,a
            parent[b]=a; sizes[a]+=sizes[b]
    pivots={}; basis_indices=[]; representations=[]
    for i,original in enumerate(values):
        x=original; coordinates=0
        while x:
            p=x.bit_length()-1
            if p not in pivots: break
            row,mask=pivots[p]
            x^=row; coordinates^=mask
        if x:
            j=len(basis_indices);basis_indices.append(i)
            pivots[x.bit_length()-1]=(x,coordinates^(1<<j))
            representations.append(1<<j)
        else:
            representations.append(coordinates)
            for j,index in enumerate(basis_indices):
                if (coordinates>>j)&1: union(i,index)
    d=len(basis_indices)
    gram=[]
    for j,index in enumerate(basis_indices):
        row=0
        for k,other in enumerate(basis_indices):
            if symplectic(values[index],values[other],genus):
                row|=1<<k;union(index,other)
        gram.append(row)
    blocks={}
    for i in range(n): blocks.setdefault(find(i),[]).append(i)
    blocks=sorted(blocks.values(),key=lambda b:b[0])
    gram_rank=rank(gram); radical_dimension=d-gram_rank
    coisotropic=d+radical_dimension==2*genus
    connected=len(blocks)==1
    return {'schema':'double-cover-bank-v1','genus':genus,'characters':list(values),
            'basis_indices':basis_indices,'coordinate_masks':representations,
            'span_dimension':d,'gram_rank':gram_rank,'radical_dimension':radical_dimension,
            'orthogonal_blocks':blocks,'coisotropic':coisotropic,'indecomposable':connected,
            'universal_for_separating_simple_curves':connected and coisotropic}
