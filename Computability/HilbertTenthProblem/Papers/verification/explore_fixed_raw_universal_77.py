#!/usr/bin/env python3
"""Complete77: kernel parity supplies Start, with an odd-index Delta bridge.

Default execution compares the receipt. Use --write to regenerate it.
"""
from collections import Counter
from functools import cached_property
from itertools import product
from pathlib import Path
import argparse
import json
import sympy as sp
import explore_fixed_raw_universal_78 as previous

NAMES=list(previous.NAMES)
CONSTANTS=[name for name in previous.CONSTANTS if name!='CS']+['inner_bits']
SYM={name:previous.SYM[name] for name in NAMES+CONSTANTS if name!='inner_bits'}
SYM['x']=previous.SYM['x']
SYM['inner_bits']=sp.Symbol('inner_bits',positive=True,integer=True)
OUTER=[(name,op,'Z','W') if name=='marked_rhs' else (name,op,left,right)
       for name,op,left,right in previous.OUTER if name!='marker_partial']
CORE=list(previous.CORE)
ADAPTER=[]
for name,op,left,right in previous.ADAPTER:
    if name=='ap1':ADAPTER.append(('odd_index','+','scaled_t','inner_bits'))
    elif name=='index_product':ADAPTER.append((name,'*','delta','A'))
    elif name=='index_rhs':ADAPTER.append((name,'+','odd_index','index_product'))
    else:ADAPTER.append((name,op,left,right))
SCHEDULE=OUTER+CORE+ADAPTER
EQUALITIES=list(previous.EQUALITIES)


def source_residuals():
    result=previous.source_residuals()
    result[5]=sp.expand(result[5].subs(previous.SYM['CS'],0))
    a=SYM['a'];Delta=a*a+4*a+3
    result[16]=sp.expand(SYM['kappa']-SYM['cell_bits']*SYM['x']-SYM['inner_bits']-SYM['delta']*Delta)
    return result


def verify_source():
    env=previous.previous.fixed_environment(SYM)
    previous.previous.previous.bridge.baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();U=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(U*U-SYM['y_aux']**2)
    records=[]
    for ix,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=previous.previous.previous.bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==77 and counts=={'+':35,'*':42}
    assert len(NAMES)==32 and len(EQUALITIES)==len(sources)==20
    assert len(OUTER)==20 and len(CORE)==43 and len(ADAPTER)==14
    assert CORE==previous.CORE
    assert {ix for ix,(old,new) in enumerate(zip(previous.source_residuals(),sources)) if sp.expand(old-new)!=0}=={5,16}
    assert sp.expand(env['raw_bound']-SYM['C']-SYM['alpha']-SYM['cell_bits']*SYM['x'])==0
    assert sp.expand(env['odd_index']-SYM['cell_bits']*SYM['x']-SYM['inner_bits'])==0
    assert {SYM[name] for name in NAMES}<=set().union(*(s.free_symbols for s in sources))
    aliases={name:value for name,value in previous.previous.fixed_environment(SYM).items() if name not in SYM}
    assert all(sp.sympify(value).free_symbols<={SYM[name] for name in CONSTANTS} for value in aliases.values())
    return dict(operations=77,multiplications=42,additions_subtractions=35,
                positive_existential_unknown_count=32,positive_unknowns=NAMES,equations=20,
                fixed_constants=CONSTANTS,raw_parameters=['x>0'],
                primitive_instructions=primitives,sources=records,
                ledger={'outer':20,'retained_kernel':43,'fixed_base_bridge':14},
                changed_source_indices=[5,16],start_selector=0,end_selector=1,
                exact_input_exponent='cell_bits*x+inner_bits',raw_bound_exponent='cell_bits*x')


class Compiled(previous.Compiled):
    @cached_property
    def MC(self):
        return self.B-1-sum(1<<(self.radix_bits*e) for e in self.positions if e!=1)

    def constants(self):
        return dict(B=self.B,DC=self.DC,DR=self.DR,MC=self.MC,MF=self.MF,
                    cell_bits=self.d,inner_bits=self.radix_bits)


def compile_windows(windows,a):
    windows=tuple(tuple(w) for w in windows);k=len(windows)
    assert k>=2 and len(set(windows))==k and all(len(w)==9 for w in windows)
    assert all(0<=s<a for w in windows for s in w)
    A=1<<max(2,(k+1).bit_length());start=k+3*a
    payload={(r,c,s):start+(2-r)*3*a+(2-c)*a+s
             for r,c,s in product(range(3),range(3),range(a))}
    coeff={i:1 for i in range(k)};mu=A-2
    for j,((r,c,s),e) in enumerate(payload.items(),1):
        coeff[e]=A**j;mu+=A**j
        for i,w in enumerate(windows):
            if w[3*r+c]==s:coeff[i]+=A**j
    anchor_coeff=[]
    for j in range(1+9*a,1+9*a+4):
        value=A**j;anchor_coeff.append(value);mu+=value
        for i in range(k):coeff[i]+=value
    padding=0;m=2*mu.bit_count()+12*a+2;next_clause=1+9*a+4
    while m+1<k+9*a+4:
        mu+=A**(next_clause+padding);padding+=1;m+=2
    dummy=tuple(range(start+9*a,start+9*a+(m+1-k-9*a-4)))
    old_positions=tuple(range(k))+tuple(payload.values())+dummy
    anchor_unit=max(old_positions)+3*a+1
    anchors=tuple(mult*anchor_unit for mult in (1,3,9,27));positions=old_positions+anchors
    for e,value in zip(anchors,anchor_coeff):coeff[e]=value
    assert len(set(positions))==len(positions)==m+1
    E=max(positions);H=E+24*anchor_unit+3*a+1
    T1=H+2*E+a+1;T2=T1+2*E+1;L=T2+E+2
    L+=L%2
    target=max(2*(m+1)*(2*sum(coeff.values())+5),2*mu)+4
    radix_bits=(target-1).bit_length()
    if radix_bits%2==0:radix_bits+=1
    R=1<<radix_bits;d=radix_bits*L
    DCpoly={}
    for e in (3*a,H+a,8*anchor_unit,24*anchor_unit):previous.add_term(DCpoly,e,1)
    for e,value in coeff.items():
        previous.add_term(DCpoly,T1-e,value);previous.add_term(DCpoly,T2-e,value)
    MFpoly={T1:mu,T2:mu}
    for r,c,s in product(range(2),range(3),range(a)):previous.add_term(MFpoly,payload[r,c,s],1)
    for r,c,s in product(range(3),range(2),range(a)):previous.add_term(MFpoly,H+payload[r,c,s],1)
    for e in anchors[2:]:previous.add_term(MFpoly,e,1)
    assert sum(value.bit_count() for value in MFpoly.values())==m
    assert all(0<value<R for value in DCpoly.values())
    assert max(DCpoly)<L and max(MFpoly)<L and min(MFpoly)>0
    assert radix_bits%2==1 and L%2==d%2==0
    return Compiled(windows,a,A,coeff,mu,padding,m,positions,payload,dummy,anchors,
                    anchor_unit,H,T1,T2,L,R,radix_bits,d,DCpoly,MFpoly)


def pell(A,index):
    chi,psi=1,0;D=A*A-1
    for _ in range(index):chi,psi=A*chi+D*psi,chi+A*psi
    return chi,psi


def verify_delta_bridge():
    residues=projection=positive=0
    for a in range(2,101):
        A=a+2;D=A*A-1
        for v in range(1,a+1):
            chi,psi=pell(A,v)
            expected=v if v%2 else v*A
            assert 0<expected<D and psi%D==expected
            assert chi*chi-D*psi*psi==1
            residues+=1
            for u in range(1,min(a+1,2*A)):
                if psi%D==u:assert v==u and v%2==1
                projection+=1
    examples=[]
    for b,L in ((1,4),(3,2),(3,4),(5,2)):
        d=b*L
        for x in (1,2,3):
            u=d*x+b;W=2**u;a=2**(u+3);A=a+2;D=A*A-1;J0=u+2
            mu,kappa=pell(A,u);_,c=pell(A,J0)
            delta,rem=divmod(kappa-u,D);assert rem==0
            rho,rem=divmod(mu-a*kappa-W,4*a+3);assert rem==0
            phi=c-kappa
            assert min(kappa,mu,delta,phi,rho)>0
            assert kappa==d*x+b+delta*D and c==kappa+phi
            assert mu*mu==1+D*kappa*kappa
            assert mu==W+a*kappa+rho*(4*a+3)
            assert W==(2**b)*(2**d)**x and u%2==1
            positive+=1
            examples.append(dict(b=b,L=L,d=d,x=x,u=u,positive=True))
    return dict(exact_recurrence_residue_cases=residues,bounded_index_projection_pairs=projection,
                positive_four_equation_examples=positive,examples=examples,
                scope='Bridge identities and positivity; example parameters are not asserted to be full packed kernels')


def verify_marker_bijection():
    edges={'V':('L',),'L':('L','I'),'I':('I','Q'),'Q':('R',),'R':('R','V')}
    counts=Counter()
    for N in range(1,19):
        for initial in edges:
            def visit(word):
                if len(word)==N:
                    if initial not in edges[word[-1]]:return
                    starts={i for i in range(N) if tuple(word[(i+j)%N] for j in (-1,0,1))==('I','I','Q')}
                    ends={i for i in range(N) if tuple(word[(i+j)%N] for j in (-1,0,1))==('L','I','I')}
                    mapping={}
                    for start in starts:
                        end=start;steps=0
                        while word[(end-1)%N]=='I':
                            end=(end-1)%N;steps+=1;assert steps<N
                        assert end in ends and steps>=1
                        back=end;backsteps=0
                        while word[(back+1)%N]=='I':
                            back=(back+1)%N;backsteps+=1;assert backsteps<N
                        assert back==start and backsteps==steps
                        mapping[start]=end
                        counts['paired_markers']+=1
                        counts['runs_crossing_numeric_origin']+=int(end>start)
                    assert set(mapping.values())==ends and len(mapping)==len(set(mapping.values()))
                    if len(ends)==1:assert len(starts)==1
                    counts['unique_end_words']+=int(len(ends)==1)
                    counts['multiple_marker_words']+=int(len(ends)>1)
                    counts['short_unmarked_I_runs']+=sum(tuple(word[(i+j)%N] for j in (-1,0,1))==('L','I','Q') for i in range(N))
                    counts['closed_phase_words']+=1
                    return
                for nxt in edges[word[-1]]:visit(word+[nxt])
            visit([initial])
    return dict(counts)


def verify_outer():
    records=[]
    for N,h,x in ((3,1,1),(5,2,1)):
        word=[1]+[0]*(N-1)
        windows=[previous.previous.cyclic_window(word,i,h) for i in range(N)]
        assert len(set(windows))==N
        alphabet=[windows[0],windows[x]]+[window for i,window in enumerate(windows) if i not in (0,x)]
        cc=compile_windows(alphabet,2)
        rows=[cc.bits(alphabet.index(window)) for window in windows]
        cells=[cc.cell(row) for row in rows];B=cc.B
        pack=lambda values:sum(value<<(cc.d*i) for i,value in enumerate(values))
        C=pack(cells);right=pack([cells[(i-1)%N] for i in range(N)])
        nxt=pack([cells[(i-h)%N] for i in range(N)])
        F=pack([cc.materialize(cc.local_field([rows[i],rows[(i-1)%N],rows[(i-h)%N]])) for i in range(N)])
        assert F==cc.DC*C+cc.DR*right+nxt
        q=1<<(cc.d*N);P=1<<(cc.d*h);W=1<<(cc.d*x+cc.radix_bits)
        raw=cc.d*x;u=raw+cc.radix_bits;J=(q-1)//(B-1);Z=C-W
        kR,rem=divmod(B*C-right,q-1);assert rem==0 and kR>0
        kY,rem=divmod(P*C-nxt,q-1);assert rem==0 and kY>0
        zquot=cc.DR*kR+kY
        assert 0<Z<C<q and Z%2==1 and 0<F<q-1 and u%2==1
        assert cc.MC%2==0 and cc.MF%2==0
        assert Z&(cc.MC*J)==0 and F&(cc.MF*J)==0
        assert cc.MC.bit_count()+cc.MF.bit_count()==cc.d
        assert C<=(B-2)*J and q-C>=J+1 and J>=B**x>raw
        assert u<q+cc.radix_bits<2*q and W==cc.R*B**x
        r=(q*q-Z-q*F)*(q*q-1)+(cc.MC+q*cc.MF)*J
        assert r%2==Z%2==1 and q*q<=r<q**4 and r.bit_count()==3*cc.d*N
        values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,F=F,alpha=q-C-raw,zquot=zquot,
                    r=r,Z=Z,W=W,x=x)
        env=previous.previous.fixed_environment({**cc.constants(),**values})
        previous.previous.previous.bridge.baseline.run_schedule(OUTER,env)
        assert env['bounded']+raw==q
        for left,rightname in EQUALITIES[:6]:
            if left!='raw_bound':assert env[left]==env[rightname]
        assert min(values.values())>0
        # Check the low bit under every rotation. The packing identity r=Z mod2
        # then identifies exactly the unique Start position in these examples.
        for rotation in range(N):
            shifted=cells[rotation:]+cells[:rotation]
            assert (shifted[0]&1)==int(rotation==0)
        records.append(dict(N=N,h=h,x=x,inner_bits=cc.radix_bits,cell_bits=cc.d,
                            input_index=u,q_bits=q.bit_length(),index_bits=r.bit_length(),
                            index_population=r.bit_count(),index_parity=r%2,positive_outer_equations=6))
    return dict(materialized_positive_outer_cases=len(records),examples=records,
                scope='Generic cyclic-window compiler/interface tests; actual universal completeness uses the retained machine theorem with N>=4',
                full_kernel='Fresh positive converse proved; astronomical Pell coordinates not materialized')


def verify():
    alphabets=[([(0,)*9,(1,)*9],2),
               ([previous.previous.cyclic_window([1,0,0],i,1) for i in range(3)],2),
               (list(product(range(2),repeat=9))[:100],2),
               ([(0,)*9,(1,)*9,(2,)*9],3)]
    compilers=[]
    for windows,a in alphabets:
        cc=compile_windows(windows,a)
        result=previous.verify_compiler(cc)
        assert len(cc.positions)==cc.m+1 and cc.radix_bits%2==1 and cc.L%2==cc.d%2==0
        result.update(start_selector=0,end_selector=1,masked_marker_slots=1)
        compilers.append(result)
    return dict(status='PASS_FIXED_RAW_UNIVERSAL77',source=verify_source(),compilers=compilers,
                delta_bridge=verify_delta_bridge(),marker_bijection=verify_marker_bijection(),
                outer=verify_outer(),proof='../1980/FIXED_RAW_UNIVERSAL_77_PROOF.md',
                review='Author and independent complete proof/source reviews pass; mathematical and exact-computation evidence, not proof-assistant formalization',
                scope='Complete fixed-index raw-input certificate; origin Start follows from necessary kernel parity, with a unique-End marker bijection')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();receipt=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['compilers']);print(result['outer']);print(result['delta_bridge']);print(result['marker_bijection'])
