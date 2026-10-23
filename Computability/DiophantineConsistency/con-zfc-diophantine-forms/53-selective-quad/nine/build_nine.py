#!/usr/bin/env python3
"""Division-free nine-variable selective/sparse carry constructions.
Only Python standard library. Upstream mathematical data is parsed, not executed.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,hashlib,sys
from circuit import DAG
sys.path.insert(0,str(Path(__file__).resolve().parent/'upstream'))
from verify_selective import port_polynomial, shifted_source
ROOT=Path(__file__).resolve().parent
KAPPA=2134940
NATURAL=['epsilon','g0','h0','s0','w0','phi','i0','j0','n']
POSITIVE=['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus']

def build(positive=False,certificate=False,bridge='three'):
    code=json.loads((ROOT/'upstream/code_v1.json').read_text())
    source=json.loads((ROOT/'upstream/upstream_parent_quartic31.json').read_text())
    blocks=shifted_source(source)
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
    Jc=save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),Dcode),targets))
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
    V0=save('V0',M(PP,K));a0=save('a0',A(S(P(V0,2),P(K,2)),c(1)));a1=save('a1',M(c(64),D,F,I))
    margin=save('margin',S(M(S(P(K,2),M(c(4),P(S(C,M(K,Y)),2))),Gcap),M(c(8),v['g'],P(K,2))))
    u=save('u',M(J,F));vc=save('v',A(M(Qp,F),M(J,S(H,C))))
    t0=save('t0',M(v['i'],J,C));S0=save('S0',M(t0,S(S(M(c(8),P(D,2)),M(c(4),D)),c(1))))
    GH=save('GH',M(G,H));V1=save('V1',M(S0,GH));Md=save('Mdiv',A(Qp,S(H,C)))
    Om=save('Omega',M(u,S(M(c(2),margin),c(1))))
    E0=save('E0',S(A(M(u,v['n']),vc),M(Om,Md)))
    Th=save('Theta',S(E0,M(Om,V0,V1)))
    if certificate:
        err=save('dferror',S(M(P(t0,2),A(M(c(8),D),c(1))),M(c(64),D)))
        delta=save('deltaV',A(M(err,P(GH,2)),M(c(64),D,F,S(P(H,2),c(1)))))
        inner=save('inner',S(A(S(P(E0,2),M(c(2),E0,Om,V0,V1)),M(P(Om,2),P(V0,2),delta)),M(P(Om,2),a0)))
    else:inner=save('inner',S(P(Th,2),M(P(Om,2),A(a0,M(P(V0,2),a1)))))
    out=save('F9',S(P(inner,2),M(c(4),P(Om,4),P(V0,2),a0,a1)))
    nodes,out,names=d.prune(out);counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return dict(schema='proveit-selective-sparse-nine-v1',domain='positive integers' if positive else 'nonnegative integers',bridge=bridge,variables=variables,W=W,Qcode=Q,Kcode=Kcode,Ecode=Ecode,weights=ws,targets=code['targets'],target_order=code['order'],base_scale_exponent=KAPPA,threshold_scale_exponent=threshold_exp,coefficient_bound_exponent=maxbound.bit_length(),port_bit_lengths=bits,coefficient_recipes=[{'name':name,'terms':rec} for name,rec in recipes.values()],nodes=nodes,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),degree_certificate_variant=certificate,fixed_binding='../COEFFICIENT_BINDING.json',proof='../PROOF.md')

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
    for bridge in ('three','two','calibrated'):
        for positive in (False,True):
            label=bridge+'_'+('positive' if positive else 'natural')
            body=build(positive,False,bridge);certbody=build(positive,True,bridge);degree=degree_certificate(certbody)
            for suffix,b in [('',body),('_certificate',certbody)]:
                b['exact_degree']=degree['exact_degree'];(ROOT/f'generated/{label}{suffix}.json').write_text(json.dumps(b,separators=(',',':'))+'\n')
            (ROOT/f'generated/{label}_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
            ledger[label]={'degree':degree['exact_degree'],'operations':body['total_operations'],'operation_counts':body['operation_counts'],'certificate_operations':certbody['total_operations']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
