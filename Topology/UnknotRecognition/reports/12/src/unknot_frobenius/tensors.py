"""Exact tensor-described interfaces with exponentially many hidden indices.

A vector of length 2^m is a sum of weighted product tensors. Pairings are
contracted by distributivity, never by enumerating the 2^m coordinates.
This is a restricted representation, not a claim that arbitrary scanned
Khovanov complexes admit bounded tensor descriptions.
"""
from __future__ import annotations
from dataclasses import dataclass
from .subset import subset_product, validate
from .blocks import Matrix, InterfaceData, matrix, add, shape

@dataclass(frozen=True)
class TensorTerm:
    weight: int
    factors: tuple[tuple[int, int], ...]

@dataclass(frozen=True)
class TensorVector:
    variables: int
    modes: int
    terms: tuple[TensorTerm, ...]

    def __post_init__(self):
        if type(self.modes) is not int or self.modes < 0:
            raise ValueError('modes must be nonnegative')
        validate(0,self.variables)
        for term in self.terms:
            if len(term.factors)!=self.modes:
                raise ValueError('tensor term has the wrong number of modes')
            validate(term.weight,self.variables)
            for pair in term.factors:
                if len(pair)!=2:
                    raise ValueError('binary tensor factor required')
                for x in pair: validate(x,self.variables)

    def is_radical_by_weights(self) -> bool:
        """A sufficient, efficiently checked radical-valued certificate."""
        return all(not (term.weight&1) for term in self.terms)

    def pairing(self, other: 'TensorVector') -> int:
        if (self.variables,self.modes)!=(other.variables,other.modes):
            raise ValueError('incompatible tensor vector dimensions')
        b=self.variables
        result=0
        for t in self.terms:
            for u in other.terms:
                value=subset_product(t.weight,u.weight,b)
                for (a0,a1),(b0,b1) in zip(t.factors,u.factors):
                    if not value: break
                    local=subset_product(a0,b0,b)^subset_product(a1,b1,b)
                    value=subset_product(value,local,b)
                result^=value
        return result

    def coordinate(self, index: int) -> int:
        """Random access to one coordinate, used only for small test oracles."""
        if type(index) is not int or not 0<=index<(1<<self.modes):
            raise ValueError('index outside tensor vector')
        result=0
        for term in self.terms:
            value=term.weight
            for j,pair in enumerate(term.factors):
                value=subset_product(value,pair[(index>>j)&1],self.variables)
            result^=value
        return result

    def expand(self, *, maximum_modes=16) -> tuple[int, ...]:
        """Explicit test oracle; production contraction does NOT call this."""
        if self.modes>maximum_modes:
            raise MemoryError('explicit expansion refused by configured limit')
        return tuple(self.coordinate(i) for i in range(1<<self.modes))


def tensor_interface(u_columns: tuple[TensorVector,...], v_rows: tuple[TensorVector,...],
                     c_columns: tuple[TensorVector,...], d_rows: tuple[TensorVector,...],
                     e: Matrix) -> InterfaceData:
    """Schur interface for A=I+UV on R_b^(2^m), without enumerating 2^m.

    U is certified radical-valued using each term's weight. All outer
    dimensions are explicit. The output is the small interface, whose
    checked evaluation uses nilpotent block inversion.
    """
    vectors=u_columns+v_rows+c_columns+d_rows
    if not all((u_columns,v_rows,c_columns,d_rows)):
        raise ValueError('all interface dimensions must be positive')
    b,m=vectors[0].variables,vectors[0].modes
    if any((v.variables,v.modes)!=(b,m) for v in vectors):
        raise ValueError('all tensors must share variables and modes')
    r,p,q=len(u_columns),len(d_rows),len(c_columns)
    if len(v_rows)!=r or shape(e)!=(p,q):
        raise ValueError('interface matrix shape mismatch')
    if not all(v.is_radical_by_weights() for v in u_columns):
        raise ValueError('U needs radical weights on every tensor term')
    for row in e:
        for x in row: validate(x,b)
    core=matrix([[v.pairing(u) for u in u_columns] for v in v_rows])
    left=matrix([[d.pairing(u) for u in u_columns] for d in d_rows])
    right=matrix([[v.pairing(c) for c in c_columns] for v in v_rows])
    background=add(e,matrix([[d.pairing(c) for c in c_columns] for d in d_rows]))
    return InterfaceData(core,left,right,background)


def transform_local(vector: TensorVector, operators: tuple[Matrix,...]) -> TensorVector:
    """Apply a Kronecker product of 2x2 operators without increasing term count."""
    if len(operators)!=vector.modes or any(shape(t)!=(2,2) for t in operators):
        raise ValueError('one 2x2 operator is required per mode')
    b=vector.variables;terms=[]
    for term in vector.terms:
        factors=[]
        for t,(a,z) in zip(operators,term.factors):
            factors.append(tuple(subset_product(row[0],a,b)^subset_product(row[1],z,b) for row in t))
        terms.append(TensorTerm(term.weight,tuple(factors)))
    return TensorVector(b,vector.modes,tuple(terms))


def separable_background_interface(background_factors: tuple[Matrix,...],
                                   u_columns: tuple[TensorVector,...], v_rows: tuple[TensorVector,...],
                                   c_columns: tuple[TensorVector,...], d_rows: tuple[TensorVector,...],
                                   e: Matrix) -> InterfaceData:
    """A=(tensor_j A_j)+UV, each A_j invertible over the coefficient ring."""
    from .blocks import unit_inverse
    if not u_columns:
        raise ValueError('positive interface dimension required')
    b=u_columns[0].variables
    inverses=tuple(unit_inverse(t,b) for t in background_factors)
    bu=tuple(transform_local(u,inverses) for u in u_columns)
    bc=tuple(transform_local(c,inverses) for c in c_columns)
    return tensor_interface(bu,v_rows,bc,d_rows,e)
