#!/usr/bin/env python3
"""Fixed-coefficient convolution compiler for multi-bit state cells.

Only the local compiler and conditional aligned word composition are
claimed. Constants are fixed by the relation; no universal SLP count.
"""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import random
import sys

from explore_boolean_affine_mask import compile_relation

OUT=Path(__file__).with_suffix('.json')


@dataclass(frozen=True)
class CellCompiler:
    sites: int
    state_bits: int
    clauses: int
    clause_radix: int
    constant: int
    coefficients: tuple
    clause_mask: int
    inner_radix: int
    inner_bits: int
    cell_radix: int
    cell_bits: int
    target_degree: int
    maximum_degree: int
    coefficient_mass: int
    convolution: tuple
    guard: int
    state_mask: int
    field_mask: int

    def cell(self,bits):
        assert len(bits)==self.clauses and all(bit in (0,1) for bit in bits)
        return 2*sum(bit*self.inner_radix**j for j,bit in enumerate(bits))

    def scalar(self,actual_bits):
        assert len(actual_bits)==len(self.coefficients)
        return self.constant+sum(c*b for c,b in zip(self.coefficients,actual_bits))


def compile_cells(sites,state_bits,allowed):
    assert sites>=1 and state_bits>=1
    arity=sites*state_bits
    base=compile_relation(arity,allowed,zero_last=True)
    forbidden=list(base.forbidden)
    # Repeating the forbidden zero clause preserves the relation and
    # ensures enough independent cell bit positions for all state bits.
    forbidden += [(0,)*arity]*max(0,state_bits-len(forbidden))
    m=len(forbidden);A=base.clause_radix;G=A**m
    constant=G;coefficients=[0]*arity;mu=0
    for j,pattern in enumerate(forbidden):
        weight=A**j
        constant+=weight*(sum(pattern)-1)
        mu+=(A//2)*weight
        for i,bit in enumerate(pattern):coefficients[i]+=(1-2*bit)*weight
    assert m>=state_bits and constant>0 and min(coefficients)>0
    if m==len(base.forbidden):
        assert constant==base.constant and tuple(coefficients)==base.coefficients and mu==base.mask
    mass=2*constant+2*m*sum(coefficients)
    R=4
    while R<max(mass,2*mu)+2:R*=2
    t=R.bit_length()-1;target=state_bits-1;maximum=state_bits+m-2
    B=R**(maximum+1);d=t*(maximum+1)
    convolution=tuple(sum(coefficients[s*state_bits+i]*R**(target-i)
                          for i in range(state_bits)) for s in range(sites))
    guard=2*constant*R**target
    allowed_cell_bits=2*sum(R**j for j in range(m))
    cmask=(B-1)-allowed_cell_bits;fmask=2*mu*R**target
    assert (B-1)^allowed_cell_bits==cmask
    assert cmask.bit_count()==d-m and fmask.bit_count()==m
    assert cmask%2==1 and fmask%2==0 and cmask<B and fmask<B
    return CellCompiler(sites,state_bits,m,A,constant,tuple(coefficients),mu,R,t,B,d,
                        target,maximum,mass,convolution,guard,cmask,fmask)


def check_cells(compiled,allowed,all_bits):
    g,k,m=compiled.sites,compiled.state_bits,compiled.clauses
    assert len(all_bits)==g and all(len(row)==m for row in all_bits)
    encoded=[compiled.cell(row) for row in all_bits]
    actual=tuple(bit for row in all_bits for bit in row[:k])
    F=compiled.guard+sum(coef*cell for coef,cell in zip(compiled.convolution,encoded))
    polynomial=[0]*(compiled.maximum_degree+1)
    polynomial[compiled.target_degree]=2*compiled.constant
    for s,row in enumerate(all_bits):
        for i in range(k):
            coefficient=compiled.coefficients[s*k+i]
            for j,bit in enumerate(row):
                polynomial[compiled.target_degree+j-i]+=2*coefficient*bit
    assert sum(polynomial)<=compiled.coefficient_mass<=compiled.inner_radix-2
    assert all(0<=a<=compiled.inner_radix-2 for a in polynomial)
    assert F==sum(a*compiled.inner_radix**j for j,a in enumerate(polynomial))
    target=F//compiled.inner_radix**compiled.target_degree%compiled.inner_radix
    assert target==polynomial[compiled.target_degree]==2*compiled.scalar(actual)
    assert 0<F<=compiled.cell_radix-2
    assert (F&compiled.field_mask==0)==(actual in allowed)
    assert all(0<=cell<compiled.cell_radix and cell%2==0 and cell&compiled.state_mask==0 for cell in encoded)
    return encoded,F,actual in allowed


def dummy_assignments(g,k,m):
    count=g*(m-k)
    if count<=7:
        return list(product((0,1),repeat=count))
    # Reproducible sparse, dense and random patterns for larger dummy sets.
    choices={(0,)*count,(1,)*count}
    for i in range(count):
        choices.add(tuple(int(j==i) for j in range(count)))
    rng=random.Random(20260922+g*10000+k*100+m)
    for _ in range(8):choices.add(tuple(rng.randrange(2) for _ in range(count)))
    return sorted(choices)


def verify_small_relations():
    compilations=state_assignments=cell_cases=padded=0
    maximum_cell_bits=0
    for arity in range(1,4):
        domain=tuple(product((0,1),repeat=arity))
        for truth in range(0,1<<len(domain),2):
            allowed=frozenset(z for i,z in enumerate(domain) if truth>>i&1)
            for k in range(1,arity+1):
                if arity%k:continue
                g=arity//k;cc=compile_cells(g,k,allowed)
                compilations+=1;padded+=cc.clauses>len(domain)-len(allowed)
                maximum_cell_bits=max(maximum_cell_bits,cc.cell_bits)
                dummies=dummy_assignments(g,k,cc.clauses)
                for actual in domain:
                    state_assignments+=1
                    for dummy in dummies:
                        rows=[];pos=0
                        for s in range(g):
                            count=cc.clauses-k
                            rows.append(actual[s*k:(s+1)*k]+dummy[pos:pos+count]);pos+=count
                        check_cells(cc,allowed,rows);cell_cases+=1
    assert compilations==274 and state_assignments==2116 and padded>0
    return dict(compilations=compilations,state_assignments=state_assignments,
                state_and_dummy_cell_cases=cell_cases,padded_clause_compilations=padded,
                maximum_cell_bits=maximum_cell_bits,
                scope='Every zero-forbidden relation of arity1..3 at every equal-block factorization; exhaustive dummies when at most7 dummy bits')


def verify_state_validity_and_packing():
    # Three genuine symbols encoded by 01,10,11. Both tuple positions must
    # be genuine symbols; dummy bits must not turn state00 into a symbol.
    valid=((0,1),(1,0),(1,1))
    allowed=frozenset(a+b for a in valid for b in valid if a!=b)
    cc=compile_cells(2,2,allowed);rng=random.Random(719)
    cell_cases=invalid_zero_rejections=packed_cases=0;records=[]
    for actual in product((0,1),repeat=4):
        for filler in (0,1):
            rows=[tuple(actual[s*2:(s+1)*2])+(filler,)*(cc.clauses-2) for s in range(2)]
            _,_,passed=check_cells(cc,allowed,rows);cell_cases+=1
            if (0,0) in (actual[:2],actual[2:]):
                assert not passed;invalid_zero_rejections+=1
    for length in range(1,6):
        for _ in range(40):
            cells=[];fields=[];statuses=[];raw=[]
            for i in range(length):
                rows=[tuple(rng.randrange(2) for _ in range(cc.clauses)) for _ in range(cc.sites)]
                encoded,F,passed=check_cells(cc,allowed,rows)
                cells.append(encoded);fields.append(F);statuses.append(passed);raw.append(rows)
            J=sum(cc.cell_radix**i for i in range(length));q=cc.cell_radix**length
            planes=[sum(cells[i][s]*cc.cell_radix**i for i in range(length)) for s in range(cc.sites)]
            Fword=cc.guard*J+sum(d*c for d,c in zip(cc.convolution,planes))
            assert Fword==sum(fields[i]*cc.cell_radix**i for i in range(length))
            assert 0<Fword<q and (Fword&(cc.field_mask*J)==0)==all(statuses)
            assert all(plane& (cc.state_mask*J)==0 for plane in planes)
            M=J*(cc.state_mask+q*cc.field_mask)
            assert M.bit_count()==cc.cell_bits*length and M%2==1
            assert (q*q).bit_length()-1+M.bit_count()==(q**3).bit_length()-1
            S=planes[0]+q*Fword;r=(q*q-S)*(q*q-1)+M
            assert r%2==1 and 0<S<q*q
            assert (r.bit_count()==3*cc.cell_bits*length)==all(statuses)
            packed_cases+=1
    records.append(dict(sites=cc.sites,state_bits=cc.state_bits,clauses=cc.clauses,
                        dummy_bits_per_cell=cc.clauses-cc.state_bits,inner_bits=cc.inner_bits,
                        cell_bits=cc.cell_bits,state_mask_weight=cc.state_mask.bit_count(),
                        field_mask_weight=cc.field_mask.bit_count()))
    return dict(exact_valid_symbols=[list(v) for v in valid],cell_cases=cell_cases,
                invalid_zero_state_rejections=invalid_zero_rejections,packed_cases=packed_cases,
                examples=records,
                scope='Conditional aligned word arithmetic and inverse-mask identity; no kernel/bootstrap or cyclic-neighbor interface')


def verify():
    return dict(status='PASS_MULTIBIT_AFFINE_CELL',small_relations=verify_small_relations(),
                state_validity_and_words=verify_state_validity_and_packing(),
                proof='../1980/EXPLORATION_MULTIBIT_AFFINE_CELL.md',
                universal_certificate_improvement=False,
                scope='Fixed-coefficient local compiler, state/dummy projection, mask weight balance, and conditional aligned word composition only')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['small_relations'])
