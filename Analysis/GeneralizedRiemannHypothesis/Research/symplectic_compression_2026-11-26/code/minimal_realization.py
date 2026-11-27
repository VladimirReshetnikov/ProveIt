#!/usr/bin/env python3
"""Construct minimal symplectic realizations of two prescribed Gram blocks.

Input JSON: {"q": 2, "H1": [[0]], "H0": [[0]], "M": [[0]]}
Optional "n" requests ambient dimension 2*n; otherwise the minimum is used.
Output F1, F0, J satisfy F1^T J F1=H1, F0^T J F0=H0,
F1^T J F0=M, and both F1 and F0 have full column rank.

Prime fields and GF(4)=GF(2)[x]/(x^2+x+1) are supported.  In GF(4),
0,1,2,3 encode 0,1,x,x+1; addition is XOR, not integer reduction mod 4.
This algorithm chooses a maximal relation space in the combined radical,
then embeds the quotient by exact symplectic Gram--Schmidt elimination.
The construction is deterministic, not a uniform random sampler.

Usage:
  python3 minimal_realization.py input.json --output realization.json
  python3 minimal_realization.py --self-test
"""
import argparse
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys

from check_complete_law import mul4


class Field:
    def __init__(self, q):
        if isinstance(q, bool) or not isinstance(q, int) or q < 2:
            raise ValueError("q must be prime or 4")
        if q != 4 and any(q % p == 0 for p in range(2, isqrt(q)+1)):
            raise ValueError("implemented fields are prime fields and GF(4)")
        self.q = q

    def add(self, x, y):
        return x ^ y if self.q == 4 else (x+y) % self.q

    def neg(self, x):
        return x if self.q == 4 else -x % self.q

    def sub(self, x, y):
        return self.add(x, self.neg(y))

    def mul(self, x, y):
        return mul4(x, y) if self.q == 4 else x*y % self.q

    def inv(self, x):
        if x == 0:
            raise ValueError("zero has no multiplicative inverse")
        return next(v for v in range(1,4) if mul4(x,v)==1) if self.q == 4 else pow(x,-1,self.q)

    def dot(self, x, y):
        ans = 0
        for a, b in zip(x, y):
            ans = self.add(ans, self.mul(a,b))
        return ans

    def addvec(self, x, y):
        return [self.add(a,b) for a,b in zip(x,y)]

    def scale(self, c, x):
        return [self.mul(c,a) for a in x]


def eye(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]


def columns_to_matrix(columns, height):
    return [[v[i] for v in columns] for i in range(height)]


def rref(rows, field, width=None):
    a = [list(row) for row in rows]
    h = len(a)
    w = len(a[0]) if a else (width or 0)
    if any(len(row)!=w for row in a):
        raise ValueError("matrix rows have inconsistent lengths")
    pivots = []
    for j in range(w):
        r = len(pivots)
        p = next((i for i in range(r,h) if a[i][j]!=0),None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        a[r] = field.scale(field.inv(a[r][j]), a[r])
        for i in range(h):
            if i != r:
                c = a[i][j]
                a[i] = [field.sub(x,field.mul(c,y)) for x,y in zip(a[i],a[r])]
        pivots.append(j)
        if len(pivots)==h:
            break
    return a, pivots


def matrix_rank(rows, field, width=None):
    return len(rref(rows,field,width)[1])


def nullspace(rows, field, width=None):
    a, pivots = rref(rows,field,width)
    w = len(a[0]) if a else (width or 0)
    out = []
    for free in range(w):
        if free in pivots:
            continue
        v = [0]*w
        v[free] = 1
        for i,p in enumerate(pivots):
            v[p] = field.neg(a[i][free])
        out.append(v)
    return out


def inverse(a, field):
    d = len(a)
    if any(len(row)!=d for row in a):
        raise ValueError("inverse requires a square matrix")
    red,piv = rref([list(row)+ident for row,ident in zip(a,eye(d))],field,width=2*d)
    if piv[:d]!=list(range(d)):
        raise ValueError("matrix is singular")
    return [row[d:] for row in red]


def matmul(a, b, field, output_width=None):
    p = len(b[0]) if b else (output_width or 0)
    if any(len(row)!=len(b) for row in a):
        raise ValueError("matrix multiplication dimensions do not match")
    return [[field.dot(row,[b[k][j] for k in range(len(b))]) for j in range(p)] for row in a]


def extend_basis(basis, candidates, dimension, field):
    out = [list(v) for v in basis]
    added = []
    if matrix_rank(columns_to_matrix(out,dimension),field)!=len(out):
        raise ArithmeticError("initial vectors are not independent")
    for v in candidates:
        if matrix_rank(columns_to_matrix(out+[v],dimension),field)>len(out):
            out.append(list(v))
            added.append(list(v))
    return added


def bilinear(x, y, g, field):
    return field.dot(x,[field.dot(row,y) for row in g])


def hyperbolic_pairs(g, field):
    d = len(g)
    work = eye(d)
    pairs = []
    while True:
        found = next(((i,j) for i in range(len(work)) for j in range(i+1,len(work))
                      if bilinear(work[i],work[j],g,field)!=0),None)
        if found is None:
            return pairs
        i,j = found
        u = work[i]
        v = field.scale(field.inv(bilinear(u,work[j],g,field)),work[j])
        new = []
        for k,w in enumerate(work):
            if k in (i,j):
                continue
            # w -> w + <v,w> u - <u,w> v, orthogonal to u and v.
            w1 = field.addvec(w,field.scale(bilinear(v,w,g,field),u))
            w1 = field.addvec(w1,field.scale(field.neg(bilinear(u,w,g,field)),v))
            new.append(w1)
        pairs.append((u,v))
        work = new


def validate_matrix(a, height, width, field, name):
    if not isinstance(a,list) or len(a)!=height:
        raise ValueError(f"{name} must have {height} rows")
    for row in a:
        if not isinstance(row,list) or len(row)!=width:
            raise ValueError(f"{name} must have {width} columns")
        if any(isinstance(x,bool) or not isinstance(x,int) or not 0<=x<field.q for x in row):
            raise ValueError(f"{name} entries must be integer field labels in [0,{field.q-1}]")


def validate_alternating(h, field, name):
    d = len(h)
    validate_matrix(h,d,d,field,name)
    if any(h[i][i]!=0 for i in range(d)):
        raise ValueError(f"{name} must have zero diagonal, also in characteristic 2")
    if any(field.add(h[i][j],h[j][i])!=0 for i in range(d) for j in range(d)):
        raise ValueError(f"{name} is not alternating")


def realize(q, h1, h0, m, n=None):
    field = Field(q)
    if not isinstance(h1,list) or not isinstance(h0,list):
        raise ValueError("H1 and H0 must be matrices")
    a,b = len(h1),len(h0)
    validate_alternating(h1,field,"H1")
    validate_alternating(h0,field,"H0")
    validate_matrix(m,a,b,field,"M")
    d = a+b
    g = [list(h1[i])+list(m[i]) for i in range(a)]
    g += [[field.neg(m[i][j]) for i in range(a)]+list(h0[j]) for j in range(b)]

    radical = nullspace(g,field,width=d)
    r1 = [v+[0]*b for v in nullspace([row[:a] for row in g],field,width=a)]
    r0 = [[0]*a+v for v in nullspace([row[a:] for row in g],field,width=b)]
    c = extend_basis(r1+r0,radical,d,field)
    relations = [field.addvec(r1[i],r0[i]) for i in range(min(len(r1),len(r0)))] + c
    keep = extend_basis(relations,radical,d,field)
    pairs = hyperbolic_pairs(g,field)
    s = len(pairs)
    nmin = s+max(len(r1),len(r0))
    if n is None:
        n = nmin
    if isinstance(n,bool) or not isinstance(n,int) or n < nmin:
        raise ValueError(f"requested n={n!r}; the exact minimum n is {nmin}")
    if len(keep)!=max(len(r1),len(r0)):
        raise ArithmeticError("radical quotient has incorrect dimension")

    basis = [v for pair in pairs for v in pair] + relations + keep
    if len(basis)!=d:
        raise ArithmeticError("adapted basis has incorrect length")
    change = columns_to_matrix(basis,d)
    images = []
    for i in range(s):
        e,f = [0]*(2*n),[0]*(2*n)
        e[i],f[n+i] = 1,1
        images += [e,f]
    images += [[0]*(2*n) for _ in relations]
    for j in range(len(keep)):
        v = [0]*(2*n)
        v[s+j] = 1
        images.append(v)
    f = matmul(columns_to_matrix(images,2*n),inverse(change,field),field,output_width=d)
    f1 = [row[:a] for row in f]
    f0 = [row[a:] for row in f]
    jform = [[0]*(2*n) for _ in range(2*n)]
    for i in range(n):
        jform[i][n+i] = 1
        jform[n+i][i] = field.neg(1)

    # Verify the output using the original prescribed matrices, not the adapted basis.
    fcols = [[f[i][j] for i in range(2*n)] for j in range(d)]
    actual_gram = [[bilinear(x,y,jform,field) for y in fcols] for x in fcols]
    if actual_gram!=g:
        raise ArithmeticError("output does not realize the prescribed Gram matrix")
    rank1,rank0,rankf = matrix_rank(f1,field,a),matrix_rank(f0,field,b),matrix_rank(f,field,d)
    if rank1!=a or rank0!=b:
        raise ArithmeticError("one of the output frames is not injective")
    if rankf!=d-len(relations):
        raise ArithmeticError("output has the wrong relation-space dimension")
    if any(any(field.dot(row,v)!=0 for row in f) for v in relations):
        raise ArithmeticError("listed relations do not vanish")
    gram_rank = matrix_rank(g,field,d)
    if gram_rank!=2*s or gram_rank+len(radical)!=d:
        raise ArithmeticError("symplectic decomposition has incorrect rank")
    return {
        "q":q,
        "field_encoding":"0,1,x,x+1 encoded as 0,1,2,3; x^2+x+1=0" if q==4 else f"integers modulo {q}",
        "H1":h1,"H0":h0,"M":m,"n":n,"F1":f1,"F0":f0,"J":jform,
        "relation_basis":relations,
        "certificate":{
            "all_equalities_verified":True,"a":a,"b":b,"rank_Gamma":gram_rank,
            "radical_dimension":len(radical),"t1":len(r1),"t0":len(r0),
            "minimum_n":nmin,"minimum_ambient_dimension":2*nmin,
            "actual_ambient_dimension":2*n,"rank_F1":rank1,"rank_F0":rank0,
            "rank_combined_frame":rankf,"overlap_dimension":len(relations),
            "maximum_possible_overlap":len(radical)-max(len(r1),len(r0)),
        }
    }


def self_test():
    records = []
    tested = 0
    for q in (2,3,4):
        minus_one = 1 if q==4 else (-1)%q
        z2 = [[0,0],[0,0]]
        j2 = [[0,1],[minus_one,0]]
        deg3 = [[0,1,0],[minus_one,0,0],[0,0,0]]
        cases = [(z2,z2),(j2,j2),(deg3,[[0]])]
        for h1,h0 in cases:
            a,b = len(h1),len(h0)
            count=0
            for flat in product(range(q),repeat=a*b):
                m = [list(flat[i*b:(i+1)*b]) for i in range(a)]
                result = realize(q,h1,h0,m)
                cert = result["certificate"]
                if cert["minimum_n"]>0:
                    try:
                        realize(q,h1,h0,m,cert["minimum_n"]-1)
                    except ValueError:
                        pass
                    else:
                        raise AssertionError("subminimal realization was accepted")
                if count==0:
                    realize(q,h1,h0,m,cert["minimum_n"]+1)
                count+=1
            records.append({"q":q,"a":a,"b":b,"rank_H1":matrix_rank(h1,Field(q)),
                            "rank_H0":matrix_rank(h0,Field(q)),"all_cross_matrices":count})
            tested+=count
    # Small exact overlap cases and zero-dimensional interfaces.
    same_line = realize(2,[[0]],[[0]],[[0]])
    assert same_line["F1"]==same_line["F0"]
    assert same_line["certificate"]["minimum_n"]==1
    assert same_line["certificate"]["overlap_dimension"]==1
    same_plane = realize(3,[[0,1],[2,0]],[[0,1],[2,0]],[[0,1],[2,0]])
    assert same_plane["F1"]==same_plane["F0"]
    assert same_plane["certificate"]["minimum_n"]==1
    assert same_plane["certificate"]["overlap_dimension"]==2
    for q in (2,3,4):
        realize(q,[],[],[])
        realize(q,[],[[0]],[])
        realize(q,[[0]],[],[[]])
    # Nonstandard form coefficients force actual GF(4) multiplication/inversion.
    gf4 = realize(4,[[0,2,3],[2,0,1],[3,1,0]],[[0,3],[3,0]],[[2,1],[3,2],[1,3]])
    assert gf4["certificate"]["all_equalities_verified"]
    return {"status":"PASS","exhaustive_cross_matrix_instances":tested,
            "additional_edge_cases":12,"cases":records,
            "checks":"prescribed Gram identities; separate injectivity; minimal dimension; maximal overlap; rejected undersized ambient spaces; optional larger dimension; GF(4) coefficients"}


def main():
    parser = argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("input",nargs="?",default="-",help="input JSON filename, or - for stdin")
    parser.add_argument("--output",help="write result JSON to this path")
    parser.add_argument("--self-test",action="store_true",help="run exact constructive checks")
    args = parser.parse_args()
    try:
        if args.self_test:
            result = self_test()
        else:
            spec = json.load(sys.stdin) if args.input=="-" else json.loads(Path(args.input).read_text())
            result = realize(spec["q"],spec["H1"],spec["H0"],spec["M"],spec.get("n"))
    except (ValueError,KeyError,TypeError) as exc:
        parser.error(str(exc))
    output = json.dumps(result,indent=2)+"\n"
    if args.output:
        Path(args.output).write_text(output)
    else:
        print(output,end="")


if __name__=="__main__":
    main()
