#!/usr/bin/env python3
"""Complete78: duplicated unary bands and native synchronization.

Default execution compares the saved receipt. Use --write to regenerate it.
Compiler audits use exact sparse radix polynomials; selected packed examples
materialize the full outer arithmetic, but never the enormous Pell witnesses.
"""
from dataclasses import dataclass
from functools import cached_property
from itertools import product
from pathlib import Path
import argparse
import json
import random
import sympy as sp
import explore_fixed_raw_universal_80 as previous

NAMES=[name for name in previous.NAMES if name!='align']
CONSTANTS=list(previous.CONSTANTS)
SYM={name:previous.SYM[name] for name in NAMES+CONSTANTS+['x']}
OUTER=[row for row in previous.OUTER if row[0] not in ('Pm1','alignment')]
CORE=list(previous.CORE)
ADAPTER=list(previous.ADAPTER)
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=[pair for pair in previous.EQUALITIES if pair!=('alignment','Pm1')]


def source_residuals():
    return [source for index,source in enumerate(previous.source_residuals()) if index!=2]


def verify_source():
    env=previous.fixed_environment(SYM)
    previous.previous.bridge.baseline.run_schedule(SCHEDULE,env)
    original=previous.source_residuals()
    indexed=[(ix,source) for ix,source in enumerate(original) if ix!=2]
    U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=original[14]*(U*U-SYM['y_aux']**2)
    records=[]
    for (old_index,source),(left,right) in zip(indexed,EQUALITIES):
        actual=sp.expand(env[left]-env[right])
        adjust=correction if old_index==15 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0
        records.append(dict(original_index=old_index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=previous.previous.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==78 and counts=={'+':36,'*':42}
    assert len(OUTER)==21 and len(CORE)==43 and len(ADAPTER)==14
    assert len(NAMES)==32 and len(EQUALITIES)==len(indexed)==20
    used=set().union(*(source.free_symbols for _,source in indexed))
    assert previous.SYM['align'] not in used
    assert {SYM[name] for name in NAMES}<=used
    assert CORE==previous.CORE and ADAPTER==previous.ADAPTER
    aliases={name:value for name,value in previous.fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols<={SYM[name] for name in CONSTANTS} for value in aliases.values())
    return dict(operations=78,multiplications=42,additions_subtractions=36,
                positive_existential_unknown_count=32,positive_unknowns=NAMES,equations=20,
                fixed_constants=CONSTANTS,raw_parameters=['x>0'],
                primitive_instructions=primitives,sources=records,
                fixed_aliases={name:sp.sstr(value) for name,value in aliases.items()},
                ledger={'outer':21,'retained_kernel':43,'fixed_base_bridge':14},
                deleted_instructions=[list(row) for row in previous.OUTER if row[0] in ('Pm1','alignment')],
                retained_period_divisor=True,complete_fixed_index_raw_input_universal_certificate=True)


def add_term(poly,exponent,coefficient):
    poly[exponent]=poly.get(exponent,0)+coefficient


@dataclass
class Compiled:
    windows: tuple
    a: int
    A: int
    coeff: dict
    mu: int
    padding: int
    m: int
    positions: tuple
    payload: dict
    dummy: tuple
    anchors: tuple
    anchor_unit: int
    H: int
    T1: int
    T2: int
    L: int
    R: int
    radix_bits: int
    d: int
    DCpoly: dict
    MFpoly: dict

    @cached_property
    def B(self):return 1<<self.d

    def materialize(self,poly):
        return sum(value<<(self.radix_bits*exponent) for exponent,value in poly.items())

    @cached_property
    def DC(self):return self.materialize(self.DCpoly)

    @cached_property
    def DR(self):return 1<<(self.radix_bits*self.H)

    @cached_property
    def MF(self):return self.materialize(self.MFpoly)

    @cached_property
    def MC(self):
        return self.B-1-sum(1<<(self.radix_bits*e) for e in self.positions if e not in (0,1))

    def cell(self,bits):
        return sum(bit<<(self.radix_bits*e) for bit,e in zip(bits,self.positions))

    def bits(self,state,fill=0):
        result={e:0 for e in self.positions}
        if state is not None:
            result[state]=1
            for r,c in product(range(3),repeat=2):
                result[self.payload[r,c,self.windows[state][3*r+c]]]=1
            for e in self.anchors:result[e]=1
        for e in self.dummy:result[e]=fill
        return tuple(result[e] for e in self.positions)

    def local_field(self,rows):
        field={}
        center,right,nxt=rows
        for e,bit in zip(self.positions,center):
            if bit:
                for degree,coefficient in self.DCpoly.items():add_term(field,degree+e,coefficient)
        for e,bit in zip(self.positions,right):
            if bit:add_term(field,self.H+e,1)
        for e,bit in zip(self.positions,nxt):
            if bit:add_term(field,e,1)
        assert max(field,default=0)<self.L and max(field.values(),default=0)<=self.R-2
        return field

    def mask_ok(self,field):
        return all(field.get(e,0)&mask==0 for e,mask in self.MFpoly.items())

    def truth(self,rows):
        center,right,nxt=[dict(zip(self.positions,row)) for row in rows]
        selected=[i for i in range(len(self.windows)) if center[i]]
        if len(selected)>1:return False
        for (r,c,s),e in self.payload.items():
            expected=int(bool(selected) and self.windows[selected[0]][3*r+c]==s)
            if center[e]!=expected:return False
        if any(center[e]!=int(bool(selected)) for e in self.anchors):return False
        for r,c,s in product(range(3),range(2),range(self.a)):
            if center[self.payload[r,c+1,s]]!=right[self.payload[r,c,s]]:return False
        for r,c,s in product(range(2),range(3),range(self.a)):
            if center[self.payload[r+1,c,s]]!=nxt[self.payload[r,c,s]]:return False
        u1,u2,v1,v2=self.anchors
        return center[u1]==nxt[v1] and center[u2]==nxt[v2]

    def constants(self):
        return dict(B=self.B,DC=self.DC,DR=self.DR,CS=self.R,MC=self.MC,MF=self.MF,cell_bits=self.d)


def compile_windows(windows,a):
    windows=tuple(tuple(w) for w in windows);k=len(windows)
    assert k>=2 and len(set(windows))==k and all(len(w)==9 for w in windows)
    assert all(0<=s<a for w in windows for s in w)
    A=1<<max(2,(k+1).bit_length())
    start=k+3*a
    payload={(r,c,s):start+(2-r)*3*a+(2-c)*a+s
             for r,c,s in product(range(3),range(3),range(a))}
    # Clause coefficients for selectors and tile copies, then four occupancy links.
    coeff={i:1 for i in range(k)};mu=A-2
    for j,((r,c,s),e) in enumerate(payload.items(),1):
        coeff[e]=A**j;mu+=A**j
        for i,w in enumerate(windows):
            if w[3*r+c]==s:coeff[i]+=A**j
    anchor_coeff=[]
    for j in range(1+9*a,1+9*a+4):
        value=A**j;anchor_coeff.append(value);mu+=value
        for i in range(k):coeff[i]+=value
    padding=0;m=2*mu.bit_count()+12*a+2
    next_clause=1+9*a+4
    while m+2<k+9*a+4:
        mu+=A**(next_clause+padding);padding+=1;m+=2
    dummy=tuple(range(start+9*a,start+9*a+(m+2-k-9*a-4)))
    old_positions=tuple(range(k))+tuple(payload.values())+dummy
    anchor_unit=max(old_positions)+3*a+1
    anchors=tuple(mult*anchor_unit for mult in (1,3,9,27))
    positions=old_positions+anchors
    for e,value in zip(anchors,anchor_coeff):coeff[e]=value
    assert len(set(positions))==len(positions)==m+2
    E=max(positions)
    H=E+24*anchor_unit+3*a+1
    T1=H+2*E+a+1;T2=T1+2*E+1;L=T2+E+2
    target=max(2*(m+2)*(2*sum(coeff.values())+5),2*mu)+4
    radix_bits=(target-1).bit_length();R=1<<radix_bits;d=radix_bits*L
    DCpoly={}
    for e in (3*a,H+a,8*anchor_unit,24*anchor_unit):add_term(DCpoly,e,1)
    for e,value in coeff.items():
        add_term(DCpoly,T1-e,value);add_term(DCpoly,T2-e,value)
    MFpoly={T1:mu,T2:mu}
    for r,c,s in product(range(2),range(3),range(a)):add_term(MFpoly,payload[r,c,s],1)
    for r,c,s in product(range(3),range(2),range(a)):add_term(MFpoly,H+payload[r,c,s],1)
    for e in anchors[2:]:add_term(MFpoly,e,1)
    assert sum(v.bit_count() for v in MFpoly.values())==m
    assert all(0<value<R for value in DCpoly.values())
    assert max(DCpoly)<L and max(MFpoly)<L and min(MFpoly)>0
    return Compiled(windows,a,A,coeff,mu,padding,m,positions,payload,dummy,anchors,
                    anchor_unit,H,T1,T2,L,R,radix_bits,d,DCpoly,MFpoly)


def verify_compiler(cc):
    E=max(cc.positions);K=len(cc.positions);a=cc.a
    assert K*(2*sum(cc.coeff.values())+5)<=cc.R//2-2
    assert cc.mu<cc.R//2
    assert cc.H>E+24*cc.anchor_unit+3*a
    assert cc.T1-E>cc.H+E+a and cc.T2-cc.T1>2*E
    assert cc.L>cc.T2+E+1 and cc.L>2*E
    vertical=[(cc.payload[r,c,s],cc.payload[r+1,c,s])
              for r,c,s in product(range(2),range(3),range(a))]
    horizontal=[(cc.H+cc.payload[r,c,s],cc.payload[r,c+1,s],cc.payload[r,c,s])
                for r,c,s in product(range(3),range(2),range(a))]
    u1,u2,v1,v2=cc.anchors
    tests=[]
    for target in (cc.T1,cc.T2):
        tests.append((target,lambda site,e:cc.coeff.get(e,0) if site==0 else 0))
    for target,source in vertical:
        tests.append((target,lambda site,e,source=source,target=target:int(site==0 and e==source or site==2 and e==target)))
    for target,csource,rsource in horizontal:
        tests.append((target,lambda site,e,csource=csource,rsource=rsource:int(site==0 and e==csource or site==1 and e==rsource)))
    for target,source in ((v1,u1),(v2,u2)):
        tests.append((target,lambda site,e,source=source,target=target:int(site==0 and e==source or site==2 and e==target)))
    basis=0
    for site in range(3):
        for e in cc.positions:
            for target,expected in tests:
                actual=(cc.DCpoly.get(target-e,0) if site==0 else int(target-e==cc.H) if site==1 else int(target==e))
                assert actual==expected(site,e),(site,e,target,actual,expected(site,e))
                basis+=1
    support=set(cc.positions);clean=anchors=0
    for shift in range(cc.L):
        touched=[(target-shift)%cc.L in support for target in (cc.T1,cc.T2)]
        assert not all(touched)
        clean+=1
        populated=all((target-shift)%cc.L in support for target in (v1,v2))
        assert populated==(shift==0)
        anchors+=1
    parity=0
    for ell in range(cc.radix_bits):
        for present in (0,1):
            assert ((1+(present<<ell))&1==0)==(ell==0 and present==1)
            parity+=1
    # Every possible rotation coefficient fits without radix carries.
    assert K*(2*sum(cc.coeff.values())+5)+(cc.R//2)<=cc.R-2
    rng=random.Random(7800+len(cc.windows)+a);raw=canonical=defects=0
    for _ in range(60):
        rows=[tuple(rng.randrange(2) for _ in cc.positions) for _ in range(3)]
        assert cc.mask_ok(cc.local_field(rows))==cc.truth(rows);raw+=1
    states=[None]+(list(range(len(cc.windows))) if len(cc.windows)<=5 else [0,1,len(cc.windows)-1])
    for triple in product(states,repeat=3):
        for fill in (0,1):
            rows=[cc.bits(state,fill) for state in triple]
            assert cc.mask_ok(cc.local_field(rows))==cc.truth(rows);canonical+=1
    defect_states=list(range(len(cc.windows))) if len(cc.windows)<=5 else [0,1,len(cc.windows)-1]
    for state in defect_states:
        base=cc.bits(state)
        for e in list(cc.payload.values())+list(cc.anchors):
            row=list(base);row[cc.positions.index(e)]^=1
            rows=[tuple(row),base,base]
            assert not cc.mask_ok(cc.local_field(rows)) and not cc.truth(rows)
            defects+=1
    return dict(alphabet=len(cc.windows),original_tiles=a,native_positions=K,
                dummy_positions=len(cc.dummy),zero_clause_padding=cc.padding,
                mask_population=cc.m,inner_bits=cc.radix_bits,cell_bits=cc.d,
                inner_cell_length=cc.L,anchors=list(cc.anchors),
                linear_basis_checks=basis,all_inner_shifts_clean_band_checks=clean,
                all_inner_shifts_anchor_checks=anchors,all_bit_residue_parity_checks=parity,
                malformed_native_triples=raw,canonical_or_empty_triples=canonical,
                rejected_center_copy_or_anchor_defects=defects,
                canonical_states_sampled=states,defect_states_sampled=defect_states)


def verify_outer():
    # These are compiler/interface examples, not the full universal alphabet.
    records=[]
    for N,h,x in ((3,1,1),(5,2,1)):
        word=[1]+[0]*(N-1)
        windows=[previous.cyclic_window(word,i,h) for i in range(N)]
        assert len(set(windows))==N
        alphabet=[windows[x],windows[0]]+[window for i,window in enumerate(windows) if i not in (0,x)]
        cc=compile_windows(alphabet,2)
        rows=[cc.bits(alphabet.index(window)) for window in windows]
        cells=[cc.cell(row) for row in rows];B=cc.B
        pack=lambda values:sum(value<<(cc.d*i) for i,value in enumerate(values))
        C=pack(cells);right=pack([cells[(i-1)%N] for i in range(N)])
        nxt=pack([cells[(i-h)%N] for i in range(N)])
        F=pack([cc.materialize(cc.local_field([rows[i],rows[(i-1)%N],rows[(i-h)%N]])) for i in range(N)])
        assert F==cc.DC*C+cc.DR*right+nxt
        q=1<<(cc.d*N);P=1<<(cc.d*h);W=1<<(cc.d*x);u=cc.d*x
        J=(q-1)//(B-1);Z=C-cc.R-W
        kR,remainder=divmod(B*C-right,q-1);assert remainder==0 and kR>0
        kY,remainder=divmod(P*C-nxt,q-1);assert remainder==0 and kY>0
        zquot=cc.DR*kR+kY
        assert 0<Z<C<q and Z%2==0 and 0<F<q-1
        assert Z&(cc.MC*J)==0 and F&(cc.MF*J)==0
        assert cc.MC.bit_count()+cc.MF.bit_count()==cc.d
        assert C<=(B-2)*J and q-C>=J+1 and J>=W>u
        r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
        assert r%2==1 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
        values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,F=F,alpha=q-C-u,zquot=zquot,
                    r=r,Z=Z,W=W,x=x)
        env=previous.fixed_environment({**cc.constants(),**values})
        previous.previous.bridge.baseline.run_schedule(OUTER,env)
        assert env['bounded']+u==q
        for left,rightname in EQUALITIES[:6]:
            if left!='raw_bound':assert env[left]==env[rightname]
        assert min(values.values())>0
        records.append(dict(N=N,h=h,x=x,cell_bits=cc.d,q_bits=q.bit_length(),
                            index_bits=r.bit_length(),index_population=r.bit_count(),
                            positive_outer_equations=6,index_parity=r%2))
    return dict(materialized_positive_outer_cases=len(records),examples=records,
                scope='Generic cyclic-window compiler/interface tests; actual universal completeness uses the retained machine theorem with N>=4',
                full_kernel='Fresh positive converse proved; astronomical Pell coordinates not materialized')


def verify():
    alphabets=[([(0,)*9,(1,)*9],2),
               ([previous.cyclic_window([1,0,0],i,1) for i in range(3)],2),
               ([previous.cyclic_window([1,0,0,0,0],i,2) for i in range(5)],2),
               (list(product(range(2),repeat=9))[:100],2),
               ([(0,)*9,(1,)*9,(2,)*9],3)]
    return dict(status='PASS_FIXED_RAW_UNIVERSAL78',source=verify_source(),
                compilers=[verify_compiler(compile_windows(windows,a)) for windows,a in alphabets],
                outer=verify_outer(),marker_link=previous.previous.verify_marker_link(),
                proof='../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md',
                review='Author and independent complete proof/source reviews pass; mathematical and exact-computation evidence, not proof-assistant formalization',
                scope='Complete fixed-index raw-input certificate; native anchors recover period alignment before local semantics')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['compilers']);print(result['outer'])
