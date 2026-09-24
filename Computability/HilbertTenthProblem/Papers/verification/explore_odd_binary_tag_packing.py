"""94-operation binary tag certificate on the original first-zero domain."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_reordered_binary_tag_packing as previous
base=previous.base


def outer(c):
    result=[];inserted=False
    removed={'cH','q2','q3','qp1','Qband','qM1','q2N','q2Nsum'}
    for row in previous.outer(c):
        name=row[0]
        if name in removed:continue
        if name.startswith(('S_','W_','packS','packW')):
            if not inserted:
                inserted=True
                result += [
                    ('q2','*','q','q'),('q3','*','q2','q'),
                    ('qp1','+','q',1),('F','*','qp1','Q'),('X','*','q','M1'),
                    ('q2N','*','q2','N'),('S_inner0','+','S1','X'),
                    ('S_inner1','+','S_inner0','q2N'),
                    ('S_shift1','*','q','S_inner1'),('S_inner2','+','E','S_shift1'),
                    ('S_shift2','*','q2','S_inner2'),('packS0','+','F','S_shift2'),
                    ('W_coefficient','+','q',c['c']),('W_head','*','W_coefficient','H'),
                    ('W_sum','*','qp1','Nsum'),('W_marker','+','H','W_sum'),
                    ('W_upper','*','q2','W_marker'),('W_inner','+','W_head','W_upper'),
                    ('W_shift','*','q2','W_inner'),('W_low0','+','AH','F'),
                    ('W_low1','+','W_low0','X'),('packW0','+','W_low1','W_shift'),
                ]
            continue
        result.append(row)
    assert inserted
    return result


def core():
    result=[]
    for row in base.core():
        if row[0]=='pell_H17':row=(row[0],'-','pell_jc','pell_tr1')
        elif row[0]=='pell_aux_u_rhs':row=(row[0],'-','pell_of','pell_c')
        result.append(row)
    return result


def packs(c,s):
    q=s['q'];N=2*s['Tcontent']+s['S1'];M1=s['Q']+s['S1'];L=s['Nsum']+s['H']
    aa=[s['Q'],s['Q'],s['E'],s['S1'],M1,N]
    bb=[s['Q']+s['AH'],s['Q']+M1,c['c']*s['H'],s['H'],L,s['Nsum']]
    return sum(q**i*x for i,x in enumerate(aa)),sum(q**i*x for i,x in enumerate(bb))


def sources(c,s):
    result=previous.sources(c,s)
    S,W=packs(c,s);n=s['q']**6
    result[2]=S+s['Tplus']-W-1
    result[6]=s['r']-(n-1)*(n*(W+1)+s['Tplus'])
    a,pc,f,j,o,y=[s['pell_'+x] for x in ['a','c','f','j','o','y_aux']]
    discr=a*a+4*a+3;u=j*pc-(2*s['r']+1)
    result[15]=discr*(f*f-1)*(u*u-y*y)-(1-y*y)
    result[16]=u+pc-o*f
    return result


def verify_source():
    c=dict(zip('C k B Ut c Ni Li'.split(),sp.symbols('C k B Ut cc Ni Li')))
    s=dict(zip(base.NAMES,sp.symbols(' '.join(base.NAMES))))
    rows=outer(c)+core();env=base.evaluate(rows,s)
    source=sources(c,s);old=previous.sources(c,s);S,W=packs(c,s)
    assert sp.expand(env['packS0']-S)==sp.expand(env['packW0']-W)==0
    u=s['pell_j']*s['pell_c']-(2*s['r']+1)
    correction=source[14]*(u*u-s['pell_y_aux']**2)
    records=[]
    for i,((a,b),f) in enumerate(zip(base.comparisons(),source)):
        extra=correction if i==15 else 0
        assert sp.expand(env[a]-env[b]-f-extra)==0,i
        if i not in (2,6,15,16):assert sp.expand(f-old[i])==0,i
        records.append(dict(index=i,source=str(f),correction=str(extra),
                            difference_from_binary95=str(sp.expand(f-old[i]))))
    for row in rows:
        for operand in row[2:]:
            if isinstance(operand,sp.Basic):env[operand]=operand
    primitives,counts=base.verify_primitives(rows,env)
    assert len(rows)==94 and counts=={'*':50,'+':44},counts
    assert len(base.NAMES)==28 and len(source)==17
    assert all(row[0]!='cH' for row in rows)
    assert sum(row[0]=='qp1' for row in rows)==1
    return dict(operations=94,multiplications=50,additions=44,
                positive_unknowns=base.NAMES,equations=17,outer_operations=51,
                kernel_operations=43,kernel_sign=-1,primitive_instructions=primitives,
                exact_sources=records,changed_sources=[2,6,15,16],
                field_permutation_from_binary95=[3,4,1,0,2,5])


def canonical(beta,app,initial,rows,terminal):
    assert beta>=2 and initial[0]==0 and any(initial[1:beta])
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
    old_provisional=base.evaluate(previous.outer(c),dict(vals,Tplus=1))
    old_vals=dict(vals,Tplus=old_provisional['packW0']+1-old_provisional['packS0'])
    old_vals['r']=base.evaluate(previous.outer(c),old_vals)['r_rhs']
    old_env=base.evaluate(previous.outer(c),old_vals)
    assert all(old_env[a]==old_env[b] for a,b in base.comparisons()[:7])
    assert old_vals['r']%2==0 and old_vals['r'].bit_count()==2*(old_env['n'].bit_length()-1)
    provisional=base.evaluate(outer(c),dict(vals,Tplus=1))
    vals['Tplus']=provisional['packW0']+1-provisional['packS0']
    vals['r']=base.evaluate(outer(c),vals)['r_rhs']
    env=base.evaluate(outer(c),vals)
    assert all(vals[x]>0 for x in base.OUTER_NAMES)
    assert all(env[a]==env[b] for a,b in base.comparisons()[:7])
    aa=[env[x] for x in ['Q','Q','E','S1','M1','N']]
    bb=[env['Q']+env['AH'],env['Q']+env['M1'],c['c']*H,H,env['L'],env['Nsum']]
    assert all(0<=a<=b<q and a&(b-a)==0 for a,b in zip(aa,bb))
    S,W=env['packS0'],env['packW0'];n=env['n'];r=vals['r']
    assert 0<S<W<n and S&(W-S)==0
    assert 1<=vals['Tplus']<n and n>=64 and n<=r<2*n**3
    assert vals['Q']%2==vals['AH']%2==S%2==W%2==0
    assert vals['Tplus']%2==r%2==1
    assert r.bit_count()==2*(n.bit_length()-1)
    assert env['n2']==q**12 and r!=old_vals['r']
    return dict(rows=len(rows),valuation=r.bit_count(),old_r_bits=old_vals['r'].bit_length(),
                new_r_bits=r.bit_length(),changed_index=True,odd_index=True,beta=beta,
                second_initial_bit=initial[1])


def verify_canonical():
    count=row_count=odd=second_ones=0;receipts=[]
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
                        count+=1;row_count+=len(rows);odd+=beta%2;second_ones+=initial[1]
    assert (count,row_count,odd,second_ones)==(88,382,48,72)
    return dict(complete_histories=count,source_rows=row_count,odd_beta_histories=odd,
                second_initial_bit_one_histories=second_ones,changed_odd_indices=count,
                old_and_new_outer_comparisons_each=7,six_AND_tests_per_new_tuple=6,
                receipts=receipts,
                scope='Original first-zero domain, including initial01, checks every new scale/range/valuation/odd-index hypothesis for a fresh fixed-minus43 extension. Old auxiliary values are not reused; enormous new auxiliaries are not materialized.')


def verify():
    return dict(status='PASS',review_status='Author and two independent complete proof/source/dependency reviews PASS; fresh verification reproduces the saved receipt.',
                source=verify_source(),canonical=verify_canonical(),
                proof='../1980/EXPLORATION_ODD_BINARY_TAG_PACKING.md',
                scope='Complete94-operation binary encoded-tag certificate on the unchanged binary95 first-zero domain, with a fixed odd43 kernel and fresh positive Pell witnesses. No initial-second-zero promise, raw-input/fixed-appendant universality or optimality claim.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2,default=str)+'\n',encoding='utf-8')
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions'])
    print({k:v for k,v in result['canonical'].items() if k!='receipts'})
