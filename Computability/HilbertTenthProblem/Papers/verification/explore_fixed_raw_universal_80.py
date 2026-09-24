#!/usr/bin/env python3
"""Complete80: native window copies make the successor coefficient one."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import random
import sys
import sympy as sp
import explore_fixed_raw_universal_81 as previous

NAMES=list(previous.NAMES)
CONSTANTS=[name for name in previous.CONSTANTS if name!='DY']
SYM={name:previous.SYM[name] for name in NAMES+CONSTANTS+['x']}
OUTER=[(name,op,left,'P' if right=='kp' else right)
       for name,op,left,right in previous.OUTER if name!='kp']
CORE=list(previous.CORE)
ADAPTER=list(previous.ADAPTER)
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=list(previous.EQUALITIES)


def fixed_environment(values):
    return dict(values,Bm1=values['B']-1,Kconstant=values['DC']+values['B']*values['DR'])


def source_residuals():
    return [sp.expand(s.subs(previous.SYM['DY'],1)) for s in previous.source_residuals()]


def verify_source():
    env=fixed_environment(SYM)
    previous.bridge.baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[14]*(u*u-SYM['y_aux']**2);records=[]
    for ix,((lhs,rhs),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[lhs]-env[rhs]);adjust=correction if ix==15 else 0
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[lhs,rhs],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=previous.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==80 and counts=={'+':37,'*':43}
    assert len(OUTER)==23 and len(CORE)==43 and len(ADAPTER)==14
    assert len(NAMES)==len(set(NAMES))==33 and len(EQUALITIES)==len(sources)==21
    assert CORE==previous.CORE and ADAPTER==previous.ADAPTER
    assert sp.expand(env['kinner']-SYM['DC']-SYM['B']*SYM['DR']-SYM['P'])==0
    assert {SYM[name] for name in NAMES}<=set().union(*(s.free_symbols for s in sources))
    aliases={name:value for name,value in fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(v).free_symbols<={SYM[n] for n in CONSTANTS} for v in aliases.values())
    return dict(operations=80,multiplications=43,additions_subtractions=37,
                positive_existential_unknown_count=33,positive_unknowns=NAMES,equations=21,
                raw_parameters=['x>0'],fixed_constants=CONSTANTS,
                fixed_aliases={n:sp.sstr(v) for n,v in aliases.items()},
                primitive_instructions=primitives,sources=records,
                ledger={'outer':23,'retained_kernel':43,'fixed_base_bridge':14},
                retained_alignment=True,successor_coefficient=1,
                complete_fixed_index_raw_input_universal_certificate=True)


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
    H: int
    T: int
    R: int
    B: int
    d: int
    DC: int
    DR: int
    MF: int
    MC: int

    def cell(self,bits):
        assert len(bits)==len(self.positions) and all(x in (0,1) for x in bits)
        return sum(bit*self.R**e for bit,e in zip(bits,self.positions))

    def bits(self,state,fill=0):
        result={e:0 for e in self.positions}
        if state is not None:
            result[state]=1
            for r,c in product(range(3),repeat=2):
                result[self.payload[r,c,self.windows[state][3*r+c]]]=1
        for e in self.dummy:result[e]=fill
        return tuple(result[e] for e in self.positions)

    def truth(self,rows):
        center,right,nxt=[dict(zip(self.positions,row)) for row in rows]
        chosen=[i for i in range(len(self.windows)) if center[i]]
        if len(chosen)>1:return False
        for (r,c,s),e in self.payload.items():
            expected=int(bool(chosen) and self.windows[chosen[0]][3*r+c]==s)
            if center[e]!=expected:return False
        for r,c,s in product(range(3),range(2),range(self.a)):
            if center[self.payload[r,c+1,s]]!=right[self.payload[r,c,s]]:return False
        for r,c,s in product(range(2),range(3),range(self.a)):
            if center[self.payload[r+1,c,s]]!=nxt[self.payload[r,c,s]]:return False
        return True

    def constants(self):
        return dict(DC=self.DC,DR=self.DR,B=self.B,CS=self.R,MC=self.MC,MF=self.MF,cell_bits=self.d)


def compile_windows(windows,a):
    windows=tuple(tuple(w) for w in windows);k=len(windows)
    assert k>=2 and len(set(windows))==k and all(len(w)==9 for w in windows)
    assert all(0<=s<a for w in windows for s in w)
    A=1<<max(2,(k+1).bit_length())
    start=k+3*a
    payload={(r,c,s):start+(2-r)*3*a+(2-c)*a+s
             for r,c,s in product(range(3),range(3),range(a))}
    coeff={i:1 for i in range(k)}
    mu=A-2
    for j,((r,c,s),e) in enumerate(payload.items(),1):
        coeff[e]=A**j;mu+=A**j
        for i,w in enumerate(windows):
            if w[3*r+c]==s:coeff[i]+=A**j
    base_population=mu.bit_count()+12*a
    padding=max(0,k+9*a-2-base_population)
    for j in range(1+9*a,1+9*a+padding):mu+=A**j
    m=mu.bit_count()+12*a
    dummy=tuple(range(start+9*a,start+9*a+(m+2-k-9*a)))
    positions=tuple(range(k))+tuple(payload.values())+dummy
    assert len(set(positions))==len(positions)==m+2
    E=max(positions);H=E+3*a+1;T=H+2*E+a+1
    target=max((m+2)*(sum(coeff.values())+4),mu)+2
    R=1<<(target-1).bit_length()
    B=R**(T+E+1);d=B.bit_length()-1
    DC=R**(3*a)+R**(H+a)+sum(v*R**(T-e) for e,v in coeff.items())
    DR=R**H
    vertical=[payload[r,c,s] for r,c,s in product(range(2),range(3),range(a))]
    horizontal=[H+payload[r,c,s] for r,c,s in product(range(3),range(2),range(a))]
    MF=mu*R**T+sum(R**e for e in vertical+horizontal)
    MC=B-1-sum(R**e for e in positions if e not in(0,1))
    assert MF.bit_count()==m and MC.bit_count()==d-m
    assert 0<MC<=B-2 and MC%2==1 and 0<MF<=B-2 and MF%2==0
    assert all(0<v<B for v in(DC,DR,1))
    return Compiled(windows,a,A,coeff,mu,padding,m,positions,payload,dummy,H,T,R,B,d,DC,DR,MF,MC)


def verify_compiler(cc):
    a=cc.a;K=len(cc.positions);E=max(cc.positions);checks=0
    assert cc.R-2>=K*(sum(cc.coeff.values())+4)
    assert cc.H>E+3*a and cc.T-E>cc.H+E+a
    vertical=[(cc.payload[r,c,s],cc.payload[r+1,c,s])
              for r,c,s in product(range(2),range(3),range(a))]
    horizontal=[(cc.H+cc.payload[r,c,s],cc.payload[r,c+1,s],cc.payload[r,c,s])
                for r,c,s in product(range(3),range(2),range(a))]
    # Linear-basis identities plus the raw coefficient bound cover every typed bit cube.
    for site,D in enumerate((cc.DC,cc.DR,1)):
        for e in cc.positions:
            field=D*cc.R**e
            assert field//cc.R**cc.T%cc.R==(cc.coeff.get(e,0) if site==0 else 0)
            checks+=1
            for dest,source in vertical:
                expected=int(site==0 and e==source or site==2 and e==dest)
                assert field//cc.R**dest%cc.R==expected
                checks+=1
            for dest,csource,rsource in horizontal:
                expected=int(site==0 and e==csource or site==1 and e==rsource)
                assert field//cc.R**dest%cc.R==expected
                checks+=1
    rng=random.Random(8000+len(cc.windows));raw=canonical=defects=0
    for _ in range(100):
        rows=[tuple(rng.randrange(2) for _ in cc.positions) for _ in range(3)]
        cells=[cc.cell(row) for row in rows]
        field=cc.DC*cells[0]+cc.DR*cells[1]+cells[2]
        assert 0<=field<=cc.B-2
        assert (field&cc.MF==0)==cc.truth(rows)
        raw+=1
    states=[None]+(list(range(len(cc.windows))) if len(cc.windows)<=7 else [0,1,len(cc.windows)-1])
    for triple in product(states,repeat=3):
        for fill in(0,1):
            rows=[cc.bits(i,fill) for i in triple]
            field=sum(D*cc.cell(row) for D,row in zip((cc.DC,cc.DR,1),rows))
            assert (field&cc.MF==0)==cc.truth(rows)
            canonical+=1
    # A center copy changed while its selector remains fixed must fail, for any neighbors.
    for state in range(len(cc.windows)):
        base=cc.bits(state)
        for e in cc.payload.values():
            bad=list(base);bad[cc.positions.index(e)]^=1
            rows=[tuple(bad),base,base]
            field=sum(D*cc.cell(row) for D,row in zip((cc.DC,cc.DR,1),rows))
            assert field&cc.MF!=0 and not cc.truth(rows)
            defects+=1
    for row in [tuple(0 for _ in cc.positions),tuple(1 for _ in cc.positions)]+[cc.bits(i,1) for i in states]:
        assert 0<=cc.cell(row)<=cc.B-2
        assert (cc.cell(row)&cc.MC==0)==(row[0]==row[1]==0)
    # Independently exhaust the homogeneous unary clause semantics.
    unary=0;k=len(cc.windows)
    selector_cases=list(product(range(2),repeat=k)) if k<=8 else [tuple(0 for _ in range(k)),tuple(1 for _ in range(k))]+[tuple(int(i==j) for i in range(k)) for j in range(k)]
    for selected in selector_cases:
        occupancy=sum(selected)
        assert (occupancy&(cc.A-2)==0)==(occupancy<=1)
        for r,c,s in product(range(3),range(3),range(a)):
            expected=sum(selected[i] for i,w in enumerate(cc.windows) if w[3*r+c]==s)
            for bit in range(2):
                if occupancy<=1:assert ((expected+bit)&1==0)==(expected==bit)
                assert expected+bit<cc.A
                unary+=1
    return dict(alphabet=len(cc.windows),original_tiles=a,native_positions=K,mask_population=cc.m,
                dummy_positions=len(cc.dummy),zero_clause_padding=cc.padding,
                inner_bits=cc.R.bit_length()-1,cell_bits=cc.d,successor_coefficient=1,
                linear_basis_checks=checks,arbitrary_native_triples=raw,
                canonical_or_empty_triples=canonical,rejected_center_copy_defects=defects,
                unary_clause_cases=unary,canonical_states_sampled=states,
                all_selector_subsets_exhausted=(k<=8))


def cyclic_window(word,i,h):
    N=len(word)
    return tuple(word[(i-dx-h*dy)%N] for dy in(-1,0,1) for dx in(-1,0,1))


def verify_outer():
    records=[];count=corrupt=0
    for N,h,x in((5,2,1),(7,2,2),(7,3,3)):
        word=[1]+[0]*(N-1)
        windows=[cyclic_window(word,i,h) for i in range(N)]
        assert len(set(windows))==N
        alphabet=[windows[x],windows[0]]+[w for i,w in enumerate(windows) if i not in(0,x)]
        cc=compile_windows(alphabet,2)
        for fill in(0,1):
            rows=[cc.bits(alphabet.index(w),fill) for w in windows]
            cells=[cc.cell(row) for row in rows];B=cc.B
            pack=lambda values:sum(v*B**i for i,v in enumerate(values))
            C=pack(cells);right=pack([cells[(i-1)%N] for i in range(N)])
            nxt=pack([cells[(i-h)%N] for i in range(N)])
            F=cc.DC*C+cc.DR*right+nxt
            assert F==pack([cc.DC*cells[i]+cc.DR*cells[(i-1)%N]+cells[(i-h)%N] for i in range(N)])
            q,P,W,u=B**N,B**h,B**x,cc.d*x
            J=(q-1)//(B-1);Z=C-cc.R-W
            assert 0<Z<C<q and Z%(2)==0 and 0<F<q-1
            assert Z&(cc.MC*J)==F&(cc.MF*J)==0
            assert C<=(B-2)*J and q-C>=J+1 and J>=W>u
            kR,rem=divmod(B*C-right,q-1);assert rem==0 and kR>0
            kY,rem=divmod(P*C-nxt,q-1);assert rem==0 and kY>0
            zquot=cc.DR*kR+kY
            r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
            assert r%2==1 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
            values=dict(q=q,P=P,W=W,C=C,Z=Z,v=q//P,Jrep=J,align=(P-1)//(B-1),
                        F=F,alpha=q-C-u,zquot=zquot,r=r,x=x)
            env=fixed_environment({**cc.constants(),**values})
            previous.bridge.baseline.run_schedule(OUTER,env)
            assert env['bounded']+u==q
            for lhs,rhs in EQUALITIES[:7]:
                if lhs!='raw_bound':assert env[lhs]==env[rhs],(lhs,rhs)
            assert min(values.values())>0
            # The extra native bits are linked copies, not unchecked dummy successors.
            badrows=list(rows);changed=list(badrows[0]);slot=cc.positions.index(next(iter(cc.payload.values())))
            changed[slot]^=1;badrows[0]=tuple(changed)
            badcells=[cc.cell(row) for row in badrows]
            badC=pack(badcells);badZ=badC-cc.R-W
            badF=cc.DC*badC+cc.DR*pack([badcells[(i-1)%N] for i in range(N)])+pack([badcells[(i-h)%N] for i in range(N)])
            assert badZ&(cc.MC*J)==0 and badF&(cc.MF*J)!=0
            badr=(q*q-badZ-q*badF)*(q*q-1)+(cc.MC+q*cc.MF)*J
            assert badr.bit_count()<3*cc.d*N
            corrupt+=1
            count+=1
            if fill==0:records.append(dict(N=N,h=h,x=x,cell_bits=cc.d,q_bits=q.bit_length(),
                                           index_bits=r.bit_length(),central_valuation=r.bit_count(),
                                           index_parity=r%2))
    return dict(positive_outer_cases=count,rejected_packed_copy_defects=corrupt,examples=records,
                fixed_input_bridge='Unchanged14-operation bridge and81 positive proof; huge main/auxiliary Pell values not materialized.')


def verify():
    small=[[(0,)*9,(1,)*9],[(0,)*9,(1,)*9,tuple(i%2 for i in range(9))],
           [cyclic_window([1,0,0,0,0],i,2) for i in range(5)],
           list(product(range(2),repeat=9))[:40]]
    return dict(status='PASS_FIXED_RAW_UNIVERSAL80',source=verify_source(),
                compilers=[verify_compiler(compile_windows(ws,2)) for ws in small],
                outer=verify_outer(),marker_link=previous.verify_marker_link(),
                proof='../1980/FIXED_RAW_UNIVERSAL_80_PROOF.md',
                review='Author and independent complete proof/source reviews pass; symbolic and finite evidence, not proof-assistant formalization.',
                scope='Complete fixed-index raw-input certificate using a new window-copy compiler; full arithmetic source checked; universal and positive obligations proved in the note.')


if __name__=='__main__':
    result=verify()
    output=Path(__file__).with_suffix('.json')
    if sys.argv[1:]==['--write']:
        output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(output.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['compilers']);print(result['outer'])
