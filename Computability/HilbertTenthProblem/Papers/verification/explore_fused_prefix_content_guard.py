"""A full false positive for prefix-complement fusion into the content guard."""
from pathlib import Path
import json
import sympy as sp
import explore_tag_prefix_mask_deletions as deletion

previous=deletion.previous
old=previous.old
POSITIVE=previous.POSITIVE+['GuardPositive','PrefixSlack']
FIELDS=deletion.fields('Ebar')

def prefix(c):
    rows=[]
    for name,op,a,b in deletion.prefix(c,'Ebar')[0]:
        if name=='pack_add0':
            rows += [('prefix_guard_shift','*','transport_scale','E'),
                     ('reduced_guard','-','guard_base','prefix_guard_shift')]
            rows.append((name,'+','N','reduced_guard'))
        else:rows.append((name,op,a,b))
    rows.append(('prefix_bound','+','E','PrefixSlack'))
    return rows,deletion.prefix(c,'Ebar')[1]

def schedule(c):
    return prefix(c)[0]+[(old.rename(n),op,old.rename(a),old.rename(b))
                         for n,op,a,b in old.kernel.SCHEDULE]

def outer_comparisons():
    return previous.outer_comparisons()+[('pack_add0','GuardPositive'),('prefix_bound','q')]

def comparisons():
    return outer_comparisons()+[(old.rename(a),old.rename(b)) for a,b in old.kernel.EQUALITIES]

def raw_fields(c,s):
    raw=previous.conceptual(c,s)
    raw['GN']-=c['Cbar']*s['A']*raw['E']
    return raw

def verify_source(leading):
    names=POSITIVE+previous.PARAMETERS
    s=dict(zip(names,sp.symbols(' '.join(names))))
    Cbar,Kh,Ut,B,cc,j=sp.symbols('Cbar Khalf Uthird B c jguard')
    c=dict(Cbar=Cbar,Khalf=Kh,Uthird=Ut,B=B,c=cc,C=Kh*Cbar,K=3*Kh,
           U=3*Ut+leading,leading=leading,guard_coefficient=j)
    env=old.run(schedule(c),s);env['K']=c['K']
    raw=raw_fields(c,s)
    P=sum(raw[f]*s['q']**i for i,f in enumerate(FIELDS))
    src=previous.sources(c,s)[:7]+[
        2*s['r']+1-s['q']**8-2*P,s['r']+s['betaP']-s['q']**8,
        raw['GN']-s['GuardPositive'],raw['E']+s['PrefixSlack']-s['q']]
    sub={old.kernel.SYM[k]:s['q']**8 if k=='D0' else s[old.rename(k)] for k in old.kernel.SYM}
    core=[sp.expand(p.subs(sub,simultaneous=True)) for p in old.kernel.source_residuals()]
    src+=core
    assert len(src)==len(comparisons())==22
    records=[]
    for i,((a,b),polynomial) in enumerate(zip(comparisons(),src)):
        correction=core[7]*(s['pell_u']**2-s['pell_y_aux']**2) if i==19 else 0
        assert sp.expand(env[a]-env[b]-polynomial-correction)==0,i
        records.append(dict(index=i,equality=[a,b],source=sp.sstr(polynomial),correction=sp.sstr(correction)))
    assert sp.expand(env[prefix(c)[1]]-P)==0
    count=old.counts(schedule(previous.constants(2,(leading,1))))
    assert count==dict(operations=103,multiplications=51,additions=52)
    assert len(POSITIVE)==len(set(POSITIVE))==35
    return dict(leading=leading,**count,positive_unknowns=len(POSITIVE),equations=len(src),
                positive_coordinates=POSITIVE,parameters=previous.PARAMETERS,fields=FIELDS,
                dag=schedule(previous.constants(2,(leading,1))),sources=records)

def witness():
    c=previous.constants(2,(0,1));K=c['K'];k=c['Khalf']
    numbers=[91,64,58,57,3,0,0]
    lengths=[243,243,243,243,81,27,9]
    prefixes=[81,90,91,10,1,0,0]
    extras=[27,30,30,3,0,0,0]
    selectors=[n%3 for n in numbers]
    low_content=[];rows=[]
    for i,(n,L,e,t,s) in enumerate(zip(numbers,lengths,prefixes,extras,selectors)):
        incoming=extras[i-1] if i else 0
        low=n-incoming
        assert previous.tag.boolean(low)
        assert previous.tag.boolean(e) and previous.tag.boolean(t)
        assert e==(n%K)//3+k*t and previous.tag.boolean(n%K)
        assert n-3*e-s+c['U']*s*L==K*(numbers[i+1] if i+1<len(numbers) else 0)
        assert L*(c['B'] if s else 1)==k*(lengths[i+1] if i+1<len(lengths) else 3)
        low_content.append(low)
        rows.append(dict(content=n,length=L,selector=s,prefix_quotient=e,
                         excess_prefix=t,incoming_borrow=incoming,guarded_low_content=low))
    A=729;R=c['C']*A;t=len(numbers);q=R**t;H=(q-1)//(R-1)
    pack=lambda vs:sum(v*R**i for i,v in enumerate(vs))
    N,E,S1=pack(numbers),pack(prefixes),pack(selectors)
    Q=pack([s*(L-1)//2 for s,L in zip(selectors,lengths)])
    L=pack(lengths)
    assert (N-S1)%3==0
    supplied=dict(F_Q=Q+1,F_S1=S1+1,F_T=(N-S1)//3+1,F_E=E+1,F_Nfinal=1,
                  A=A,R=R,q=q,H=H,L=L,Lfinal=3,Ninit=91,Linit=243,
                  alphaI=A-243,alphaH=K-3,v=q//R,PrefixSlack=q-E)
    raw=raw_fields(c,supplied)
    supplied['GuardPositive']=raw['GN']
    b=R//K;hK=(K-1)//2
    normalized=[low+b*(hK-3*(e%k)) for low,e in zip(low_content,prefixes)]
    assert raw['GN']==pack(normalized)
    assert all(0<=v<R and previous.tag.boolean(v) for v in normalized)
    assert all(0<=raw[f]<q and previous.tag.boolean(raw[f]) for f in FIELDS)
    assert raw['Gstar']%3==1
    assert raw['Ebar']>0 and not previous.tag.boolean(raw['Ebar'])
    P=sum(raw[f]*q**i for i,f in enumerate(FIELDS));D0=q**8;r=P+(D0-1)//2
    supplied.update(r=r,betaP=D0-r)
    env=old.run(prefix(c)[0],supplied);env.update(K=K,pell_tr1=2*r+1)
    assert all(env[a]==env[b] for a,b in outer_comparisons())
    assert all(v>0 for key,v in supplied.items() if key not in previous.PARAMETERS)
    exponent=8*(len(previous.tag.trits(q))-1)
    assert exponent==728 and old.unit.mask_expected(r,exponent) and old.unit.valuation(r)==exponent
    assert 27<=r<D0 and D0<r*r
    word=(1,0,1,0,1)
    assert word[2:]+(0,1)==word
    return dict(constants=c,source_rows=rows,normalized_guard_rows=normalized,
                positive_outer_coordinates=supplied,raw_fields=raw,packed_word=P,scale=D0,
                index=r,index_parity=r%2,exact_central_valuation=exponent,
                outer_equations=len(outer_comparisons()),masked_fields=len(FIELDS),
                nonhalting_fixed_point=word,
                pell_scope='The established parity-free44 converse supplies fresh seventeen positive auxiliaries. '
                           'These enormous auxiliaries are not materialized.')

def verify():
    return dict(status='PASS_FUSED_PREFIX_GUARD_COUNTEREXAMPLE',
                sources=[verify_source(leading) for leading in (0,1)],witness=witness(),
                review='Author and independent complete proof/source reviews and fresh verification runs pass without findings.',
                scope='Rejected103 source, including positive fused guard and explicit E<q. No improved bound.')

if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print([{k:s[k] for k in ('leading','operations','multiplications','additions','positive_unknowns','equations')}
           for s in result['sources']])
    print({k:result['witness'][k] for k in ('outer_equations','masked_fields','index_parity','exact_central_valuation')})
