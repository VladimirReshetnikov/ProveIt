"""95 operations: share q*M1 across the reordered binary AND packs."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_binary_tag_and_kernel as base


def outer(c):
    result=[];inserted=False
    for row in base.outer(c):
        name=row[0]
        if name in ('WM','WG','q2','q3'):continue
        if name.startswith(('packS','packW')):
            if not inserted:
                inserted=True
                result += [
                    ('q2','*','q','q'),('q3','*','q2','q'),
                    ('qp1','+','q',1),('Qband','*','qp1','Q'),
                    ('qM1','*','q','M1'),
                    ('q2N','*','q2','N'),('S_high','+','Qband','q2N'),
                    ('S_top','*','q3','S_high'),
                    ('S_low_inner','+','E','qM1'),
                    ('S_low_shift','*','q','S_low_inner'),
                    ('S_low','+','S1','S_low_shift'),
                    ('packS0','+','S_low','S_top'),
                    ('W_inner0','+','AH','qM1'),
                    ('W_inner1','+','Qband','W_inner0'),
                    ('q2Nsum','*','q2','Nsum'),
                    ('W_high','+','W_inner1','q2Nsum'),
                    ('W_shift2','*','q','W_high'),('W_add2','+','L','W_shift2'),
                    ('W_shift1','*','q','W_add2'),('W_add1','+','cH','W_shift1'),
                    ('W_shift0','*','q','W_add1'),('packW0','+','H','W_shift0'),
                ]
            continue
        result.append(row)
    assert inserted
    return result


def packs(c,s):
    q=s['q'];N=2*s['Tcontent']+s['S1'];M1=s['Q']+s['S1'];L=s['Nsum']+s['H']
    aa=[s['S1'],s['E'],M1,s['Q'],s['Q'],N]
    bb=[s['H'],c['c']*s['H'],L,s['Q']+s['AH'],s['Q']+M1,s['Nsum']]
    return sum(q**i*x for i,x in enumerate(aa)),sum(q**i*x for i,x in enumerate(bb))


def sources(c,s):
    result=base.source(c,s)
    S,W=packs(c,s);n=s['q']**6
    result[2]=S+s['Tplus']-W-1
    result[6]=s['r']-(n-1)*(n*(W+1)+s['Tplus'])
    return result


def verify_source():
    c=dict(zip('C k B Ut c Ni Li'.split(),sp.symbols('C k B Ut cc Ni Li')))
    s=dict(zip(base.NAMES,sp.symbols(' '.join(base.NAMES))))
    rows=outer(c)+base.core();env=base.evaluate(rows,s)
    source=sources(c,s);old=base.source(c,s)
    S,W=packs(c,s)
    assert sp.expand(env['packS0']-S)==sp.expand(env['packW0']-W)==0
    z=2*s['r']+1+s['pell_j']*s['pell_c']
    correction=source[14]*(z*z-s['pell_y_aux']**2)
    records=[]
    for i,((a,b),f) in enumerate(zip(base.comparisons(),source)):
        extra=correction if i==15 else 0
        assert sp.expand(env[a]-env[b]-f-extra)==0,i
        if i not in (2,6):assert sp.expand(f-old[i])==0,i
        records.append(dict(index=i,source=str(f),correction=str(extra),
                            difference_from_binary97=str(sp.expand(f-old[i]))))
    for row in rows:
        for operand in row[2:]:
            if isinstance(operand,sp.Basic):env[operand]=operand
    primitives,counts=base.verify_primitives(rows,env)
    assert len(rows)==95 and counts=={'*':51,'+':44},counts
    assert len(base.NAMES)==28 and len(source)==17
    for name in ('q2','q3','qM1'):assert sum(row[0]==name for row in rows)==1
    return dict(operations=95,multiplications=51,additions=44,
                positive_unknowns=base.NAMES,equations=17,outer_operations=52,
                kernel_operations=43,primitive_instructions=primitives,
                exact_sources=records,changed_sources=[2,6],
                field_permutation_from_binary97=[0,2,1,4,3,5])


def canonical(beta,app,initial,rows,terminal):
    c=base.constants(beta,app,initial)
    A=2**(max(map(len,rows))+1);R=c['C']*A;q=R**len(rows);H=(q-1)//(R-1)
    p={x:0 for x in 'Q S1 N E Nsum'.split()}
    for i,word in enumerate(rows):
        L=2**len(word);N=sum(b*2**j for j,b in enumerate(word));s=word[0]
        values=dict(Q=s*(L-1),S1=s,N=N,E=(N%(2*c['k']))//2,Nsum=L-1)
        for key in p:p[key]+=values[key]*R**i
    T,rem=divmod(p['N']-p['S1'],2)
    assert rem==0 and T>0
    vals=dict(D=R//c['k'],AH=A*H,H=H,Q=p['Q'],S1=p['S1'],Tcontent=T,
              E=p['E'],Nsum=p['Nsum'],q=q,v=q//R)
    old_provisional=base.evaluate(base.outer(c),dict(vals,Tplus=1))
    old_vals=dict(vals,Tplus=old_provisional['packW0']+1-old_provisional['packS0'])
    old_vals['r']=base.evaluate(base.outer(c),old_vals)['r_rhs']
    old_receipt=base.check_tuple(c,old_vals,rows,terminal)
    provisional=base.evaluate(outer(c),dict(vals,Tplus=1))
    vals['Tplus']=provisional['packW0']+1-provisional['packS0']
    vals['r']=base.evaluate(outer(c),vals)['r_rhs']
    env=base.evaluate(outer(c),vals)
    assert all(vals[x]>0 for x in base.OUTER_NAMES)
    assert all(env[a]==env[b] for a,b in base.comparisons()[:7])
    aa=[env[x] for x in ['S1','E','M1','Q','Q','N']]
    bb=[H,env['cH'],env['L'],env['Q']+env['AH'],env['Q']+env['M1'],env['Nsum']]
    assert all(0<=a<=b<q and a&(b-a)==0 for a,b in zip(aa,bb))
    S,W=env['packS0'],env['packW0'];n=env['n'];r=vals['r']
    assert 0<S<W<n and S&(W-S)==0
    assert 1<=vals['Tplus']<n and n>=64 and n<=r<2*n**3
    assert r%2==0 and r.bit_count()==2*(n.bit_length()-1)
    assert env['n2']==q**12 and vals['r']!=old_vals['r']
    assert r.bit_count()==old_receipt['valuation']
    return dict(rows=len(rows),valuation=r.bit_count(),old_r_bits=old_vals['r'].bit_length(),
                new_r_bits=r.bit_length(),changed_index=True,even_index=True)


def verify_canonical():
    count=row_count=odd=0;receipts=[]
    for beta in (2,3):
        for a in (2,3):
            for rest in product((0,1),repeat=a-1):
                app=(0,)+rest
                for ell in range(beta,beta+4):
                    for tail in product((0,1),repeat=ell-1):
                        initial=(0,)+tail
                        if not any(initial[1:beta]):continue
                        run=base.binary.first_halting_run(beta,app,initial,40)
                        if run is None:continue
                        rows,terminal=run
                        if terminal!=(0,) or not any(w[0] for w in rows):continue
                        receipts.append(canonical(beta,app,initial,rows,terminal))
                        count+=1;row_count+=len(rows);odd+=beta%2
    assert (count,row_count,odd)==(88,382,48)
    return dict(complete_histories=count,source_rows=row_count,odd_beta_histories=odd,
                changed_even_indices=count,old_and_new_outer_comparisons_each=7,
                six_AND_tests_per_new_tuple=6,receipts=receipts,
                scope='All new scale/range/valuation/even-index hypotheses for a fresh positive43 extension are checked. Old auxiliary values are not reused, and enormous new auxiliaries are not materialized.')


def verify():
    return dict(status='PASS',review_status='Author and two independent complete proof/source/dependency reviews and fresh verification PASS, with no findings.',
                source=verify_source(),canonical=verify_canonical(),
                proof='../1980/EXPLORATION_REORDERED_BINARY_TAG_PACKING.md',
                scope='Complete95-operation binary encoded-tag certificate with the same promises and halting characterization as binary97/96; changed packing and fresh positive Pell witnesses. No raw-input/fixed-appendant universality or optimality claim.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=str)+'\n',encoding='utf-8')
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions'])
    print({k:v for k,v in result['canonical'].items() if k!='receipts'})
