#!/usr/bin/env python3
"""Exact finite rank audits for the paired-square and guarded scalar series.

The finite alphabets are one-relator fixtures, not numerical universal
alphabets.  The note proves the abstract universal-subgroup statements.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import group_affine_guarded_mortality9 as parent

gram=parent.gram
projective=parent.projective
reset4=parent.reset4
free=parent.parent.free


def row_times(row,matrix):
    return tuple(sum(row[k]*matrix[k][j] for k in range(len(row)))
                 for j in range(len(matrix[0])))


def determinant(matrix):
    """Fraction-free exact elimination, with row pivoting."""
    a=[list(row) for row in matrix];n=len(a);previous=1;sign=1
    assert all(len(row)==n for row in a)
    if not n:return 1
    for k in range(n-1):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];sign=-sign
        value=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*value-a[i][k]*a[k][j]
                assert numerator%previous==0
                a[i][j]=numerator//previous
            a[i][k]=0
        previous=value
    return sign*a[-1][-1]


def inverse(matrix):
    n=len(matrix)
    a=[[Fraction(v) for v in row]+[Fraction(i==j) for j in range(n)]
       for i,row in enumerate(matrix)]
    for j in range(n):
        pivot=next(i for i in range(j,n) if a[i][j])
        a[j],a[pivot]=a[pivot],a[j]
        scale=a[j][j];a[j]=[v/scale for v in a[j]]
        for i in range(n):
            if i!=j:
                scale=a[i][j];a[i]=[v-scale*w for v,w in zip(a[i],a[j])]
    result=tuple(tuple(row[n:]) for row in a)
    assert gram.mm(matrix,result)==gram.ident(n)==gram.mm(result,matrix)
    return result


class Basis:
    def __init__(self):self.rows={}
    def add(self,vector):
        row=list(map(Fraction,vector))
        for pivot,old in sorted(self.rows.items()):
            factor=row[pivot]
            row=[v-factor*w for v,w in zip(row,old)]
        pivot=next((i for i,v in enumerate(row) if v),None)
        if pivot is None:return False
        scale=row[pivot];self.rows[pivot]=tuple(v/scale for v in row)
        return True


def span_words(alphabet,start,observable=False):
    """Forward words only; dependent vectors need not be expanded."""
    basis=Basis();assert basis.add(start)
    result=[((),start)];at=0
    while at<len(result):
        word,vector=result[at];at+=1
        for token,matrix in alphabet.items():
            value=row_times(vector,matrix) if observable else gram.mv(matrix,vector)
            if basis.add(value):
                # Later letters multiply on the left in chronological words.
                newword=(token,)+word if observable else word+(token,)
                result.append((newword,value))
    return result


def chronological_matrix(word,alphabet):
    result=gram.ident(len(next(iter(alphabet.values()))))
    for token in word:result=gram.mm(alphabet[token],result)
    return result


def exact_hankel(alphabet,column,row):
    prefixes=span_words(alphabet,column)
    suffixes=span_words(alphabet,row,True)
    H=tuple(tuple(gram.dot(observed,state) for _,state in prefixes)
            for _,observed in suffixes)
    for word,vector in prefixes:
        assert vector==gram.mv(chronological_matrix(word,alphabet),column)
    for word,vector in suffixes:
        assert vector==row_times(row,chronological_matrix(word,alphabet))
    direct=0
    for suffix,observed in suffixes:
        for prefix,state in prefixes:
            assert gram.dot(observed,state)==gram.dot(row,gram.mv(
                chronological_matrix(prefix+suffix,alphabet),column))
            direct+=1
    assert len(prefixes)==len(suffixes)
    det=determinant(H);assert det
    return dict(rank=len(prefixes),prefixes=[w for w,_ in prefixes],
                suffixes=[w for w,_ in suffixes],Hankel_minor=H,
                determinant=det,direct_concatenation_checks=direct)


def fixture_alphabet(relator_index):
    relator=free.defining_relator(relator_index)
    assert relator and free.reduce_word(relator)==relator
    tokens=(1,-1,2,-2,3,-3)
    pairs={token:reset4.pair_matrices(reset4.fibre_pair((token,),(relator,)))
           for token in tokens}
    physical={token:projective.lift(pair) for token,pair in pairs.items()}
    assert all(gram.mm(physical[k],physical[-k])==gram.ident(6) for k in (1,2,3))
    return relator,pairs,physical


def algebra_checks():
    upper=gram.sym(projective.U);lower=gram.sym(projective.B);I=gram.ident(3)
    N=tuple(tuple(upper[i][j]-I[i][j] for j in range(3)) for i in range(3))
    assert gram.mm(N,N)==((0,0,2),(0,0,0),(0,0,0))
    assert gram.mm(gram.mm(N,N),N)==((0,0,0),)*3
    e=(1,0,0);b=gram.mv(lower,e);bb=gram.mv(lower,b)
    assert determinant(tuple(zip(e,b,bb)))==-2*12**3
    start=(1,0,-2);out=(0,0,4)
    reachable=tuple(zip(start,gram.mv(parent.CF,start),gram.mv(parent.CT,start)))
    observable=(out,row_times(out,parent.CT),row_times(row_times(out,parent.CT),parent.CF))
    assert determinant(reachable)==3 and determinant(observable)==-192
    return dict(upper_nilpotent_square=gram.mm(N,N),lower_orbit_determinant=-2*12**3,
                control_reachable_determinant=3,control_observable_determinant=-192)


def commutator_checks():
    """Rational inverse lifts are span arguments, not new stream letters."""
    cases=0
    for index in (1,2,3):
        relator,pairs,physical=fixture_alphabet(index)
        lifted={token:parent.fixed_letter(physical[token]) for token in (1,2,3)}
        inverses={token:inverse(matrix) for token,matrix in lifted.items()}
        def group_word(word):
            value=gram.ident(9)
            for token in word:value=gram.mm(value,lifted[token] if token>0 else inverses[-token])
            return value
        # Raw fibre words: (1,R), and diag(R)*(1,R)^-1.
        for isolated in ((3,),relator+(-3,)):
            for diagonal in ((1,),(2,)):
                word=free.commutator(isolated,diagonal)
                value=group_word(word)
                pair=reset4.pair_matrices(reset4.fibre_pair(word,(relator,)))
                expected=reset4.blocks((projective.lift(pair),gram.ident(3)))
                assert value==expected
                assert pair[0]==gram.I2 or pair[1]==gram.I2
                cases+=1
        # The actual negative token has its own positive control scale.
        assert parent.fixed_letter(physical[-1])!=inverses[1]
    return dict(exact_rational_commutator_lifts=cases,
                inverse_lifts_are_not_added_alphabet_letters=True)


def rank_checks():
    records=[];physical_example=guard_example=None;direct=0
    for index in (1,2,3):
        relator,pairs,physical=fixture_alphabet(index)
        for t in (3,13,37,61):
            six=exact_hankel(physical,projective.column(t),projective.ROW)
            guarded={0:parent.input_letter(t),
                     **{token:parent.fixed_letter(a) for token,a in physical.items()}}
            nine=exact_hankel(guarded,parent.START,parent.ROW)
            assert six['rank']==6 and nine['rank']==9
            direct+=six['direct_concatenation_checks']+nine['direct_concatenation_checks']
            def digest(value):return hashlib.sha256(str(value).encode()).hexdigest()
            records.append(dict(relator_index=index,t=t,physical_rank=6,guarded_rank=9,
                physical_determinant_bits=abs(six['determinant']).bit_length(),
                physical_determinant_sha256=digest(six['determinant']),
                guarded_determinant_bits=abs(nine['determinant']).bit_length(),
                guarded_determinant_sha256=digest(nine['determinant'])))
            if physical_example is None:physical_example=six;guard_example=nine
    # Subdirectness alone is insufficient: the pure diagonal group has
    # identical physical blocks, so its scalar uses only three coordinates.
    I=gram.I2
    diagonal={1:projective.lift((projective.U,projective.U)),
              2:projective.lift((projective.B,projective.B))}
    degenerate=exact_hankel(diagonal,projective.column(37),projective.ROW)
    guarded_diagonal={0:parent.input_letter(37),
                      **{k:parent.fixed_letter(a) for k,a in diagonal.items()}}
    reduced=exact_hankel(guarded_diagonal,parent.START,parent.ROW)
    assert degenerate['rank']==3 and reduced['rank']==6
    return dict(records=records,physical_example=physical_example,guarded_example=guard_example,
                direct_concatenation_checks=direct,
                diagonal_boundary=dict(physical_rank=3,guarded_rank=6),
                universal_numerical_alphabet_instantiated=False)


def scalar_checks():
    rng=random.Random(960104);count=0
    for index in (1,2,3):
        _,pairs,physical=fixture_alphabet(index)
        tokens=tuple(physical)
        for _ in range(128):
            t=rng.randrange(3,100);word=tuple(rng.choice(tokens) for _ in range(rng.randrange(8)))
            pair=(gram.I2,gram.I2)
            for token in word:pair=tuple(gram.mm(a,b) for a,b in zip(pairs[token],pair))
            actual=sum(gram.mv(a,(-1,t))[0]**2 for a in pair)
            assert gram.dot(projective.ROW,gram.mv(chronological_matrix(word,physical),projective.column(t)))==actual
            assert parent.run((0,0)+word,t,physical)==actual
            count+=1
    return dict(independent_dense_projective_scalar_checks=count)


def verify():
    return dict(status='PASS_GROUP_GUARDED_MORTALITY_RANK_OBSTRUCTION',
                algebra=algebra_checks(),commutators=commutator_checks(),
                ranks=rank_checks(),scalars=scalar_checks(),
                scope='Exact scalar-series linear ranks six and nine under the proved subgroup hypotheses. '
                      'No lower bound for different zero-equivalent scalars, other guards, nonlinear encodings, '
                      'mortality dimensions in general, or Diophantine operation counts.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write_receipt:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
