#!/usr/bin/env python3
"""Division-free nine-variable selective/sparse carry constructions.
Only Python standard library. Upstream mathematical data is parsed, not executed.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,hashlib,sys,math,collections
from circuit import DAG
sys.path.insert(0,str(Path(__file__).resolve().parent/'upstream'))
from verify_selective import port_polynomial
ROOT=Path(__file__).resolve().parent
KAPPA=2134940
NATURAL=['epsilon','g0','h0','s0','w0','phi','i0','j0','n']
POSITIVE=['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus']

def positive_source(source):
    """Factorial-weight the original positive-coordinate residuals exactly."""
    n=len(source['variables']); blocks={}
    for eq in source['equations']:
        terms=collections.defaultdict(dict)
        for term in eq['terms']:
            alpha=term['powers'][:n]
            if sum(alpha)>2:raise ValueError('nonquadratic source')
            pair=tuple([0]*(2-sum(alpha))+[i+1 for i,e in enumerate(alpha) for _ in range(e)])
            fac=math.factorial(2-sum(alpha))*math.prod(math.factorial(e) for e in alpha)
            es=tuple(term['powers'][n:])
            terms[pair][es]=terms[pair].get(es,0)+fac*term['coefficient']
        blocks[eq['number']]={p:{e:c for e,c in poly.items() if c} for p,poly in terms.items()}
    return blocks

def build(positive=False,certificate=False,bridge='calibrated'):
    if bridge != 'calibrated': raise ValueError('Congruence normalization is certified for the calibrated bridge only')
    code=json.loads((ROOT/'upstream/code_positive.json').read_text())
    source=json.loads((ROOT/'upstream/upstream_parent_quartic31.json').read_text())
    blocks=positive_source(source)
    data={'ports':source['constants'],'rows':[]}
    for index,terms in blocks.items():
        row={'original_row_one_based':index,'terms':[]}
        for pair,poly in terms.items():
            alpha=[pair.count(i+1) for i in range(len(source['variables']))]
            row['terms'].append({'alpha':alpha,'port_polynomial':poly})
        data['rows'].append(row)
    d=DAG(); A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const;save=d.save
    variables=POSITIVE if positive else NATURAL;vv={n:d.var(n) for n in variables}
    if positive:
        v={n:vv[n] for n in ('g','h','s','w','i','j')}
        v.update({n:S(vv[n+'_plus'],c(1)) for n in ('epsilon','phi','n')})
    else:
        v={n:A(vv[n+'0'],c(1)) for n in ('g','h','s','w','i','j')}
        v.update({n:vv[n] for n in ('epsilon','phi','n')})
    v['g']=save('packed_g',M(c(2),v['g']))
    v['h']=save('even_h',M(c(2),v['h']))
    ep=vv['epsilon_plus'] if positive else A(v['epsilon'],c(1))
    b=save('b',M(c(2),P(ep,2)) if bridge=='two' else A(ep,c(1)))
    B=save('B',M(d.fixed('base_scale'),P(b,2)))
    ws=code['weights'][1:]; W=max(ws);Q=max(code['targets']);Kcode=Q+2*W;Ecode=Kcode+W+2
    recipes={};coefs={};rows={};bits=[1064921,1070004,1064921,1064922];maxbound=0
    for row in data['rows']:
        terms=[]
        for term in row['terms']:
            poly=term['port_polynomial']
            rec=[{'powers':list(es),'coefficient':co} for es,co in sorted(poly.items())]
            key=json.dumps(rec,sort_keys=True)
            if key not in recipes:recipes[key]=(f'a{len(recipes):03d}',rec)
            name=recipes[key][0]
            if name not in coefs:coefs[name]=c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.fixed(name)
            terms.append((term['alpha'],coefs[name]))
            bound=sum(abs(t['coefficient'])*(1<<sum(a*b for a,b in zip(t['powers'],bits))) for t in rec)
            maxbound=max(maxbound,bound)
        rows[row['original_row_one_based']]=terms
    @lru_cache(None)
    def chunk(pos,digit):
        if not digit:return c(1)
        if digit==1:return B if pos==0 else P(chunk(pos-1,1),16)
        return M(chunk(pos,digit-1),chunk(pos,1))
    @lru_cache(None)
    def bp(n):
        if n<0:raise ValueError("negative fixed exponent")
        out=[];pos=0
        while n:
            if n%16:out.append(chunk(pos,n%16))
            n//=16;pos+=1
        return M(*out)
    Dcode=save('Dcode',A(*(M(co,bp(target-sum(x*w for x,w in zip(alpha,ws)))) for row,target in zip(code['order'],code['targets']) for alpha,co in rows[row])))
    ell=save('ell',A(*(bp(w) for w in ws)))
    targets=save('targets',A(*(bp(q) for q in code['targets'])))
    N0=save('N0',bp(W+1));L=save('L',M(c(2),b,bp(Ecode)) if bridge=='calibrated' else bp(Ecode))
    mask=save('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Thigh=save('Thigh',M(S(B,c(2)),targets))
    Tc=save('Tcode',A(mask,M(Thigh,N0)))
    Jc=save('Jcode',A(M(c(2),P(A(c(1),v['g'],ell),2),Dcode),targets))
    Sc=save('Scode',A(v['g'],M(Jc,N0)))
    if bridge in ('two','calibrated'):
        R=save('R',A(P(L,2),M(A(Sc,Tc),L),S(S(L,c(1)),Sc)))
        Hpop=2*W+Kcode+3+len(code['targets'])
        if not (Hpop==5947 and len(ws)==31 and KAPPA%2==0):raise ValueError('parity-calibrated instance changed')
        if bridge=='two':
            threshold_exp=17*KAPPA//2-9
            N=save('N',M(d.fixed('threshold_scale'),bp((Hpop-17)//2),P(ep,3)))
        else:
            threshold_exp=15*KAPPA//2-10
            N=save('N',M(d.fixed('threshold_scale'),bp((Hpop-15)//2)))
    else:
        N=save('N',L);threshold_exp=None
        R=save('R',M(S(N,c(1)),A(M(A(Sc,Tc,c(1)),N),Tc,c(1))))
    Gcap=save('Gcap',M(c(32),b,bp(W)))
    N2=P(N,2);U=save('U',M(N2,v['w']));Y=save('Y',M(N2,v['s']));MM=save('M',M(R,Y))
    PP=save('P',M(c(2),P(MM,2),U));K=save('K',A(R,c(1),M(v['h'],S(PP,c(1)))))
    aa=save('A',M(MM,A(U,c(1))));B1=save('B1',A(M(c(2),R),c(1)));W1=save('W1',M(b,v['w']))
    C=save('C',A(M(c(2),R),W1,vv['phi_plus']) if positive else A(B1,W1,v['phi']))
    J=save('J',S(M(c(4),aa),c(5)));Qp=save('Q',S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Am1=S(P(aa,2),c(1));C2=P(C,2);D=save('D',A(M(Am1,C2),c(1)))
    Er=save('E',M(v['i'],J,D,C2));F=save('F',A(M(Am1,P(Er,2)),c(1)))
    G=save('G',A(aa,M(F,S(A(M(C,D),c(1)),aa))));H=save('H',A(B1,M(v['j'],C)))
    I=save('I',A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
    V0=save('V0',M(PP,K));a0=save('a0',A(S(P(V0,2),P(K,2)),c(1)));a1=save('a1',M(c(2048**2),D,F,I))
    margin=save('margin',S(M(S(P(K,2),M(c(4),P(S(C,M(K,Y)),2))),Gcap),M(c(8),v['g'],P(K,2))))
    u=save('u',M(J,F));vc=save('v',A(M(Qp,F),M(J,S(H,C))))
    t0=save('t0',M(v['i'],J,C));e2=P(t0,2)
    Lm=save('major_L',S(A(M(C,D),c(1)),aa))
    Ns=save('major_Nstar',A(M(c(2),G),Lm))
    Dm1=S(D,c(1));D2=P(D,2)
    N2m=save('major_N2',M(c(2),e2,Dm1,Lm))
    N1m=save('major_N1',A(M(D,N2m),M(c(3),C)))
    N3m=save('major_N3',M(c(2),e2,S(Lm,C)))
    N4m=save('major_N4',M(c(2),e2,C))
    corr=save('major_correction',A(M(c(256),v['i'],A(e2,c(2))),c(2048)))
    tp=S(S(M(c(1024),D2),M(c(512),D)),c(128))
    Tm=save('major_T',A(M(t0,S(S(S(S(M(tp,Ns),M(c(64),N1m)),M(c(40),N2m)),M(c(28),N3m)),M(c(21),N4m))),corr))
    V1=save('V1',M(Tm,H));Md=save('Mdiv',A(Qp,S(H,C)))
    Om=save('Omega',M(u,S(M(c(2),margin),c(1))))
    E0=save('E0',S(A(M(u,v['n']),vc),M(Om,Md)))
    root_bound=save('root_bound',A(V0,V1))
    Th=save('Theta',S(E0,M(Om,root_bound)))
    if certificate:
        D3,D4,D8,D16=(P(D,z) for z in (3,4,8,16))
        r1=save('major_r1',S(c(3),aa))
        r2=save('major_r2',A(M(c(3),C,D),r1))
        r3=save('major_r3',A(M(c(2),e2,S(aa,c(1)),D2),r2))
        r4=save('major_r4',A(M(c(2),e2,S(S(c(1),aa),C),D3),r3))
        tn=save('major_tnum',S(S(S(S(S(S(M(c(1024),P(D,6)),M(c(512),P(D,5))),M(c(128),D4)),M(c(64),D3)),M(c(40),D2)),M(c(28),D)),c(21)))
        dn=save('major_dnum',A(M(c(33792),P(D,5)),M(c(10560),D4),M(c(4928),D3),M(c(2464),D2),M(c(1176),D),c(441)))
        rn=save('major_Rnum',A(M(t0,A(M(c(64),r1,D3),M(c(40),r2,D2),M(c(28),r3,D),M(c(21),r4))),M(corr,D4)))
        Xm=save('major_X',M(e2,D3,Dm1))
        deltaT8=save('deltaT8',A(M(e2,dn,P(Ns,2)),M(c(1024**2),D8,S(M(Xm,P(Lm,2)),M(c(4),D,G,A(M(C,D),c(1))))),M(c(2),t0,tn,Ns,rn),P(rn,2)))
        delta1_8=save('delta1_D8',A(M(P(H,2),deltaT8),M(c(2048**2),D,F,D8,S(P(H,2),c(1)))))
        delta0=save('delta0',S(P(K,2),c(1)))
        B8=save('B_D8',A(M(D8,S(P(E0,2),M(c(2),E0,Om,root_bound))),M(P(Om,2),A(M(D8,delta0),delta1_8))))
        # Exact two-defect expansion of D^16 times the two-root norm.
        out=save('F9_D16',A(P(B8,2),M(c(4),P(Om,2),V0,V1,D8,B8),M(c(4),P(Om,4),A(M(D16,delta0,P(V1,2)),M(D8,a0,delta1_8)))))
    else:
        inner=save('inner',S(P(Th,2),M(P(Om,2),A(a0,a1))))
        out=save('F9',S(P(inner,2),M(c(4),P(Om,4),a0,a1)))
    nodes,out,names=d.prune(out);counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return dict(schema='proveit-congruence-majorant-nine-v1',domain='positive integers' if positive else 'nonnegative integers',bridge=bridge,variables=variables,W=W,Qcode=Q,Kcode=Kcode,Ecode=Ecode,weights=ws,targets=code['targets'],target_order=code['order'],base_scale_exponent=KAPPA,threshold_scale_exponent=threshold_exp,coefficient_bound_exponent=maxbound.bit_length(),port_bit_lengths=bits,coefficient_recipes=[{'name':name,'terms':rec} for name,rec in recipes.values()],nodes=nodes,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),degree_certificate_variant=certificate,fixed_binding='../COEFFICIENT_BINDING.json',proof='../PROOF.md')

def degree_certificate(body):
    rows=[];unresolved=[]
    for idx,n in enumerate(body['nodes']):
        if n['kind']=='variable':row=(1,{(0,0):1})
        elif n['kind']=='literal':row=(0,{(0,0):n['value']})
        elif n['kind']=='fixed':row=(0,{(1,0):1} if n['name']=='base_scale' else {(0,1):1} if n['name']=='threshold_scale' else None)
        else:
            da,ca=rows[n['left']];db,cb=rows[n['right']]
            if n['kind']=='mul':
                if ca is None or cb is None:row=(da+db,None)
                else:
                    cs={}
                    for a,x in ca.items():
                        for b,y in cb.items():
                            ex=tuple(i+j for i,j in zip(a,b));cs[ex]=cs.get(ex,0)+x*y
                    row=(da+db,{a:x for a,x in cs.items() if x})
            else:
                sign=1 if n['kind']=='add' else -1
                if da>db:row=(da,ca)
                elif db>da:row=(db,None if cb is None else {a:sign*x for a,x in cb.items()})
                elif ca is None or cb is None:row=(da,None)
                else:
                    cs=ca.copy()
                    for a,x in cb.items():cs[a]=cs.get(a,0)+sign*x
                    cs={a:x for a,x in cs.items() if x}
                    if not cs and da>0:unresolved.append(idx)
                    row=(da,cs)
        rows.append(row)
    dg,head=rows[body['output']]
    if head is None or not head or not all(x>0 for x in head.values()):raise ValueError('degree final leader is not explicitly positive')
    if unresolved:raise ValueError('unresolved degree cancellations: '+str(unresolved))
    def encode(head):return None if head is None else [{'base_scale_power':a[0],'threshold_scale_power':a[1],'scalar_odd_part':str(x//(x&-x)), 'scalar_power_of_two':(x&-x).bit_length()-1} for a,x in head.items()]
    return dict(exact_degree=dg,diagonal_leading_coefficient=encode(head),named_degrees={n:rows[i][0] for n,i in body['named_nodes'].items()},named_leaders={n:encode(rows[i][1]) for n,i in body['named_nodes'].items()},unresolved_positive_degree_cancellations=unresolved,method='Multivariate upper bounds attained by explicit nonzero diagonal leader; all positive-degree leading cancellations resolved by identities.')

def main():
    (ROOT/'generated').mkdir(exist_ok=True);ledger={}
    for bridge in ('calibrated',):
        for positive in (False,True):
            label=bridge+'_'+('positive' if positive else 'natural')
            body=build(positive,False,bridge);certbody=build(positive,True,bridge);degree=degree_certificate(certbody)
            degree['certificate_degree']=degree['exact_degree']
            degree['multiplier_degree']=16*degree['named_degrees']['D']
            degree['exact_degree']-=degree['multiplier_degree']
            degree['certificate_multiplier']='D^16'
            degree['certificate_diagonal_leading_coefficient']=degree['diagonal_leading_coefficient']
            dhead=degree['named_leaders']['D'][0]
            if dhead['scalar_odd_part']!='1':raise ValueError('degree multiplier leading coefficient changed')
            degree['diagonal_leading_coefficient']=[dict(base_scale_power=h['base_scale_power']-16*dhead['base_scale_power'],threshold_scale_power=h['threshold_scale_power']-16*dhead['threshold_scale_power'],scalar_odd_part=h['scalar_odd_part'],scalar_power_of_two=h['scalar_power_of_two']-16*dhead['scalar_power_of_two']) for h in degree['certificate_diagonal_leading_coefficient']]
            for suffix,b in [('',body),('_certificate',certbody)]:
                b['exact_degree']=degree['certificate_degree'] if suffix else degree['exact_degree']
                if suffix:b['primary_exact_degree']=degree['exact_degree']
                (ROOT/f'generated/{label}{suffix}.json').write_text(json.dumps(b,separators=(',',':'))+'\n')
            (ROOT/f'generated/{label}_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
            ledger[label]={'degree':degree['exact_degree'],'operations':body['total_operations'],'operation_counts':body['operation_counts'],'certificate_operations':certbody['total_operations']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
