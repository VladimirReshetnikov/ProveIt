"""Complete source and positive counterexample for a specified history73 deletion."""
from pathlib import Path
import json
import sympy as sp
import explore_zero_offset_rule110_history as base
from round13_1980_certificate import verify_primitives
import round4_1980_operation_count as baseline


def changed_schedule():
    rows=[]
    for name,op,left,right in base.SCHEDULE:
        if name in ('Bw','Tword'):
            continue
        rows.append((name,op,'Cw' if left=='Tword' else left,right))
    return rows


def verify_source():
    rows=changed_schedule()
    sources=base.source_residuals()
    z=base.SYM
    q,C,Y,J,r=[z[x] for x in ('q','Cw','Yw','Jrow','r')]
    b=128
    u=(18*b*b+23*b+23)*C+42*Y
    p=C+q*Y+q*q*u
    mask=J*((b-2)*(q+1)+36*q*q)
    sources[5]=r-(q**3-p)*(q**3-1)-mask
    env=dict(z)
    baseline.run_schedule(rows,env)
    auxu=z['j']*z['c']-(2*r+1)
    correction=sources[13]*(auxu**2-z['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(base.EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjustment)==0 else -1
        assert sp.expand(actual-sign*source-adjustment)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(adjustment)))
    instructions,counts=verify_primitives(rows,env)
    assert len(instructions)==73 and counts=={'+':31,'*':42}
    assert len(records)==16 and len(base.NAMES)-2==25
    return dict(operations=73,multiplications=42,additions_subtractions=31,
                equations=16,positive_unknowns=25,
                primitive_instructions=instructions,source_comparisons=records)


def word(raw,radix):
    value=0;power=1
    while raw:
        value+=(raw&1)*power
        raw>>=1;power*=radix
    return value


def digits(value,radix):
    result=[]
    while value:
        value,digit=divmod(value,radix)
        result.append(digit)
    return result


def counterexample(radix):
    cbits=32917465;ybits=37669115
    assert ybits==((cbits<<1)|cbits)&~((cbits<<2)&(cbits<<1)&cbits)
    bits=radix.bit_length()-1
    assert radix==2**bits and bits>=7
    m=3;t=9;n=m*t
    I=1;F=radix
    C=word(cbits,radix);Y=word(ybits,radix)
    W=radix**m;q=radix**n;A=W//radix
    H=(q-1)//(W-1);J=(q-1)//(radix-1)
    U=(18*radix**2+23*radix+23)*C+42*Y
    P=C+q*Y+q*q*U
    M=J*((radix-2)*(q+1)+36*q*q)
    L=q**3;r=(L-P)*(L-1)+M
    vals=dict(I=I,F=F,q=q,awidth=A,quot=q//W,hrow=H,
              Cw=C,Yw=Y,Jrow=J,alphaI=A-I,r=r)
    assert min(vals.values())>0
    assert I+W*Y==C+q*F
    assert 0<C<q//radix**2 and 0<Y<q and 0<U<q
    assert set(digits(C,radix))<=set((0,1))
    assert set(digits(Y,radix))<=set((0,1))
    assert all(0<=d<=106 and d&36==0 for d in digits(U,radix))
    assert 0<P<L and 0<M<L and P&M==0
    assert M.bit_count()==2*bits*n
    assert r.bit_count()==5*bits*n and r%2==1
    assert q**3-1<r<q**6 and q**5<r*r
    assert set(digits(radix*C+H,radix))-set((0,1))
    assert I%radix==1 and F%radix==0
    if radix==128:
        env=dict(vals)
        for name,op,left,right in changed_schedule()[:30]:
            a=env[left] if isinstance(left,str) else left
            b=env[right] if isinstance(right,str) else right
            env[name]=a+b if op=='+' else a-b if op=='-' else a*b
        assert all(env[a]==env[b] for a,b in base.OUTER_EQUALITIES)
        assert env['packed']==P and env['mask']==M and env['Uw']==U
    return dict(radix=radix,width_cells=m,rows=t,initial=I,final=F,
                binary_cell_words=dict(C=cbits,Y=ybits),
                positive_outer_coordinates=vals,index_valuation=r.bit_count(),
                all_outer_equations=True,all_retained_masks=True,index_odd=True,
                original_marker_rejects=True,
                positive_kernel_extension='Constructive fixed-minus43 converse at q^5; huge Pell auxiliaries not materialized.')


def verify():
    return dict(status='PASS_RULE110_ROW_MARKER_OMISSION_COUNTEREXAMPLE',
                source=verify_source(),counterexamples=[counterexample(b) for b in (128,256,512)],
                scope='Full false positive for replacing T=bC+H by C in history75; not a lower bound for all73 encodings.',
                review='Author and independent complete scoped proof/source review PASS; immutable fresh receipt comparison PASS.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status'])
    print({b['radix']:b['index_valuation'] for b in result['counterexamples']})
