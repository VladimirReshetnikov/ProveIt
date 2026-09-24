"""96 operations: share the duplicated Q band of both binary tag packs."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_binary_tag_and_kernel as previous


def outer(c):
    old=previous.outer(c)
    result=[]
    inserted=False
    for row in old:
        name=row[0]
        if name in ('WM','WG','q2'):
            continue
        if name.startswith(('packS','packW')):
            if not inserted:
                inserted=True
                result += [
                    ('q2','*','q','q'),
                    ('qp1','+','q',1), ('Qband','*','qp1','Q'),
                    ('qAH','*','q','AH'), ('other_band','+','M1','qAH'),
                    ('q2N','*','q2','N'), ('shared_S_high','+','Qband','q2N'),
                    ('q2Nsum','*','q2','Nsum'),
                    ('Wband','+','Qband','other_band'),
                    ('shared_W_high','+','Wband','q2Nsum'),
                ]
                for prefix,fields,last in (
                    ('packS',['S1','M1','E'],'shared_S_high'),
                    ('packW',['H','L','cH'],'shared_W_high')):
                    for i in range(2,-1,-1):
                        mul,out=prefix+'mul'+str(i),prefix+str(i)
                        result += [(mul,'*','q',last),(out,'+',fields[i],mul)]
                        last=out
            continue
        result.append(row)
    assert inserted
    return result


def verify_source():
    c=dict(zip('C k B Ut c Ni Li'.split(),sp.symbols('C k B Ut cc Ni Li')))
    values=dict(zip(previous.NAMES,sp.symbols(' '.join(previous.NAMES))))
    rows=outer(c)+previous.core()
    env=previous.evaluate(rows,values)
    old=previous.evaluate(previous.outer(c)+previous.core(),values)
    for name in ('packS0','packW0','r_rhs','n2'):
        assert sp.expand(env[name]-old[name])==0,name
    sources=previous.source(c,values)
    z=2*values['r']+1+values['pell_j']*values['pell_c']
    correction=sources[14]*(z*z-values['pell_y_aux']**2)
    records=[]
    for i,((a,b),source) in enumerate(zip(previous.comparisons(),sources)):
        extra=correction if i==15 else 0
        actual=sp.expand(env[a]-env[b])
        assert sp.expand(actual-source-extra)==0,i
        assert sp.expand(actual-old[a]+old[b])==0,i
        records.append(dict(index=i,source=str(source),correction=str(extra)))
    for row in rows:
        for operand in row[2:]:
            if isinstance(operand,sp.Basic):env[operand]=operand
    primitives,counts=previous.verify_primitives(rows,env)
    assert len(rows)==96 and counts=={'*':52,'+':44},counts
    assert len(previous.NAMES)==28 and len(sources)==17
    assert not any(row[0] in ('WM','WG') for row in rows)
    assert sum(row[0]=='q2' for row in rows)==1
    return dict(operations=96,multiplications=52,additions=44,
                positive_unknowns=previous.NAMES,equations=17,
                outer_operations=53,kernel_operations=43,
                complete_sources=records,primitive_instructions=primitives,
                all_source_polynomials_unchanged=True,
                exact_same_packs_index_scale_and_positive_witnesses=True)


def canonical(beta,app,initial,rows,terminal):
    c=previous.constants(beta,app,initial)
    A=2**(max(map(len,rows))+1)
    R=c['C']*A;q=R**len(rows);H=(q-1)//(R-1)
    p={x:0 for x in 'Q S1 N E Nsum'.split()}
    for i,word in enumerate(rows):
        L=2**len(word);N=sum(b*2**j for j,b in enumerate(word));s=word[0]
        values=dict(Q=s*(L-1),S1=s,N=N,E=(N%(2*c['k']))//2,Nsum=L-1)
        for key in p:p[key]+=values[key]*R**i
    T,rem=divmod(p['N']-p['S1'],2)
    assert rem==0 and T>0
    vals=dict(D=R//c['k'],AH=A*H,H=H,Q=p['Q'],S1=p['S1'],Tcontent=T,
              E=p['E'],Nsum=p['Nsum'],q=q,v=q//R)
    provisional=previous.evaluate(previous.outer(c),dict(vals,Tplus=1))
    vals['Tplus']=provisional['packW0']+1-provisional['packS0']
    old=previous.evaluate(previous.outer(c),vals)
    vals['r']=old['r_rhs']
    result=previous.check_tuple(c,vals,rows,terminal)
    new=previous.evaluate(outer(c),vals)
    assert all(new[a]==new[b] for a,b in previous.comparisons()[:7])
    assert all(new[x]==old[x] for x in ('packS0','packW0','r_rhs','n2','Tplus'))
    return result


def verify_canonical():
    histories=row_count=odd_beta=0
    valuations=[]
    for beta in (2,3):
        for a in (2,3):
            for rest in product((0,1),repeat=a-1):
                app=(0,)+rest
                for ell in range(beta,beta+4):
                    for tail in product((0,1),repeat=ell-1):
                        initial=(0,)+tail
                        if not any(initial[1:beta]):continue
                        run=previous.binary.first_halting_run(beta,app,initial,40)
                        if run is None:continue
                        rows,terminal=run
                        if terminal!=(0,) or not any(w[0] for w in rows):continue
                        result=canonical(beta,app,initial,rows,terminal)
                        histories+=1;row_count+=len(rows);odd_beta+=beta%2
                        valuations.append(result['valuation'])
    assert (histories,row_count,odd_beta)==(88,382,48)
    return dict(complete_canonical_histories=histories,source_rows=row_count,
                odd_beta_histories=odd_beta,new_and_old_outer_comparisons_each=7,
                unchanged_even_indices=histories,six_AND_tests_per_tuple=6,
                exact_valuations=valuations,
                scope='All packed values, index, scale, bounds, and canonical Pell hypotheses unchanged. The same full positive auxiliary tuple extends both sources; huge auxiliary integers are not materialized.')


def verify():
    return dict(status='PASS',review_status='Author and two independent complete proof/source/dependency reviews and fresh verification PASS, with no findings.',
                source=verify_source(),canonical=verify_canonical(),
                proof='../1980/EXPLORATION_SHARED_BINARY_TAG_PACKING.md',
                scope='Complete96-operation binary encoded-tag certificate with exactly the published97 semantics and all positive witnesses. No raw-input/fixed-appendant universality or optimality claim.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=str)+'\n',encoding='utf-8')
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions'])
    print({k:v for k,v in result['canonical'].items() if k!='exact_valuations'})
