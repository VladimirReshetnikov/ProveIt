#!/usr/bin/env python3
"""Division-free nine-variable selective/sparse carry constructions.
Only Python standard library. Upstream mathematical data is parsed, not executed.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,hashlib,sys
from circuit import DAG
from source_algebra import shifted_source
ROOT=Path(__file__).resolve().parent
KAPPA=2134940
NATURAL=['b','g','h','s','w','C','i','j','n']
POSITIVE=NATURAL

def build(positive=True,certificate=False,bridge='calibrated',absorb=True,encoding='hybrid'):
    if bridge != 'calibrated':raise ValueError('Only the proved calibrated source is provided')
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
    v=vv.copy() if positive else {n:A(node,c(1)) for n,node in vv.items()}
    if absorb:v['j']=S(vv['j'],c(1)) if positive else vv['j']
    ep=v['b']
    b=save('b',v['b'])
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
    def sparse(pairs):
        terms=sorted(pairs);e,r=terms.pop()
        while terms:
            en,cn=terms.pop();r=A(M(r,bp(e-en)),cn);e=en
        return M(r,bp(e))
    if encoding=='direct' or certificate:
        Dcode=save('Dcode',A(*(M(co,bp(target-sum(x*w for x,w in zip(alpha,ws)))) for row,target in zip(code['order'],code['targets']) for alpha,co in rows[row])))
    else:
        def fixed_recipe(poly):
            rec=[{'powers':list(es),'coefficient':co} for es,co in sorted(poly.items())]
            key=json.dumps(rec,sort_keys=True)
            if key not in recipes:recipes[key]=(f'a{len(recipes):03d}',rec)
            name=recipes[key][0]
            if name not in coefs:coefs[name]=c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.fixed(name)
            return coefs[name]
        raw=json.loads((ROOT/'upstream/source60.json').read_text())
        u0=bp(W);coords=[bp(W-w) for w in ws]
        env={name:(A(z,u0),1) for name,z in zip(raw['variables'],coords)}
        for ip,name in enumerate(raw['constants']):
            ex=[0]*4;ex[ip]=1;env[name]=(fixed_recipe({tuple(ex):1}),0)
        def get(x):return (c(x),0) if isinstance(x,int) else env[x]
        def align(z,t):return M(z[0],P(u0,t-z[1]))
        for name,op,aa,bb in raw['source']:
            aa,bb=get(aa),get(bb)
            if op=='*':env[name]=(M(aa[0],bb[0]),aa[1]+bb[1])
            else:
                t=max(aa[1],bb[1]);env[name]=((A if op=='+' else S)(align(aa,t),align(bb,t)),t)
        rowvals={ri:S(align(get(aa),2),align(get(bb),2)) for ri,(aa,bb) in enumerate(raw['comparisons'],1)}
        rowvals[15]=A(rowvals[15],M(env['beta'][0],env['J'][0],u0))
        parts=[];direct=[]
        for ri,target in zip(code['order'],code['targets']):
            if target<2*W:
                direct.extend((target-sum(x*w for x,w in zip(alpha,ws)),co) for alpha,co in rows[ri]);continue
            correction=[]
            for pair,poly in blocks[ri].items():
                if pair[0]==pair[1]:
                    if any(co%2 for co in poly.values()):raise ValueError('odd diagonal weight')
                    half={ex:co//2 for ex,co in poly.items()}
                    coord=u0 if pair[0]==0 else coords[pair[0]-1]
                    correction.append(M(fixed_recipe(half),P(coord,2)))
            parts.append((target-2*W,A(rowvals[ri],*correction)))
        Dcode=save('Dcode',A(sparse(parts),sparse(direct)))

    ell=save('ell',A(*(bp(w) for w in ws)))
    targets=save('targets',A(*(bp(q) for q in code['targets'])))
    N0=save('N0',bp(W+1));L=save('L',M(b,bp(Ecode)) if bridge=='calibrated' else bp(Ecode))
    mask=save('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Thigh=save('Thigh',M(S(B,c(2)),targets))
    Tc=save('Tcode',A(mask,M(Thigh,N0)))
    Jc=save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),Dcode),targets))
    Sc=save('Scode',A(v['g'],M(Jc,N0)))
    if bridge in ('two','calibrated'):
        R=save('R',A(M(A(Sc,Tc),L),S(S(L,c(1)),Sc)))
        Hpop=2*W+Kcode+3+len(code['targets'])
        if not (Hpop==5947 and len(ws)==31 and KAPPA%2==0):raise ValueError('parity-calibrated instance changed')
        if bridge=='two':
            threshold_exp=17*KAPPA//2-9
            N=save('N',M(d.fixed('threshold_scale'),bp((Hpop-17)//2),P(ep,3)))
        else:
            threshold_exp=15*KAPPA//2-11
            N=save('N',M(d.fixed('threshold_scale'),bp((Hpop-15)//2)))
    else:
        N=save('N',L);threshold_exp=None
        R=save('R',M(S(N,c(1)),A(M(A(Sc,Tc,c(1)),N),Tc,c(1))))
    Gcap=save('Gcap',M(c(32),b,bp(W)))
    N2=P(N,2);U=save('U',M(N2,v['w']));Y=save('Y',M(N2,v['s']));MM=save('M',M(R,Y))
    PP=save('P',M(c(2),P(MM,2),U));K=save('K',A(R,c(1),M(v['h'],S(PP,c(1)))))
    aa=save('A',M(MM,A(U,c(1))));B1=save('B1',A(M(c(2),R),c(1)));W1=save('W1',M(b,v['w']))
    C=save('C',v['C'])
    J=save('J',S(M(c(4),aa),c(5)));Qp=save('Q',S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Am1=S(P(aa,2),c(1));C2=P(C,2);D=save('D',A(M(Am1,C2),c(1)))
    Er=save('E',M(v['i'],J,D,C2));F=save('F',A(M(Am1,P(Er,2)),c(1)))
    G=save('G',A(aa,M(F,S(A(M(C,D),c(1)),aa))));H=save('H',A(C,M(F,A(B1,M(v['j'],C))))) if absorb else save('H',A(B1,M(v['j'],C)))
    GH=save('GH',M(G,H))
    I=save('I',A(S(P(GH,2),P(H,2)),c(1)))
    V0=save('V0',M(PP,K));a0=save('a0',A(S(P(V0,2),P(K,2)),c(1)));a1=save('a1',M(c(64),D,F,I))
    margin=save('margin',S(M(S(P(K,2),M(c(4),P(S(C,M(K,Y)),2))),Gcap),M(c(8),v['g'],P(K,2))))
    t0=save('t0',M(v['i'],J,C));S0=save('S0',M(t0,S(S(M(c(8),P(D,2)),M(c(4),D)),c(1))))
    GH=save('GH',M(G,H));V1=save('V1',M(S0,GH))
    divisor=J if absorb else M(J,F)
    numerator=Qp if absorb else A(M(Qp,F),M(J,S(H,C)))
    Om=save('Omega',M(divisor,margin))
    offset=save('offset',P(W1,2))
    E0=save('E0',A(M(divisor,A(v['n'],offset)),numerator))
    Vsum=save('Vsum',A(V0,V1))
    Th=save('Theta',S(E0,M(Om,Vsum)))
    if certificate:
        err=save('dferror',S(M(P(t0,2),A(M(c(8),D),c(1))),M(c(64),D)))
        delta=save('deltaV',A(M(err,P(GH,2)),M(c(64),D,F,S(P(H,2),c(1)))))
        defect=save('defect',A(S(P(K,2),c(1)),delta,M(c(2),V0,V1)))
        inner=save('inner',A(S(P(E0,2),M(c(2),E0,Om,Vsum)),M(P(Om,2),defect)))
    else:
        scaled0=save('scaled0',M(P(Om,2),a0));scaled1=save('scaled1',M(P(Om,2),a1))
        inner=save('inner',S(P(Th,2),A(scaled0,scaled1)))
    out=save('F9',S(P(inner,2),M(c(4),P(Om,4),a0,a1) if certificate else M(c(4),scaled0,scaled1)))
    nodes,out,names=d.prune(out);counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return dict(schema='proveit-free-carrier-nine-v1',primary=bool(absorb and positive and not certificate),domain='positive integers' if positive else 'nonnegative integers',bridge=bridge,absorb=absorb,encoding=encoding,variables=variables,W=W,Qcode=Q,Kcode=Kcode,Ecode=Ecode,weights=ws,targets=code['targets'],target_order=code['order'],base_scale_exponent=KAPPA,threshold_scale_exponent=threshold_exp,coefficient_bound_exponent=maxbound.bit_length(),port_bit_lengths=bits,coefficient_recipes=[{'name':name,'terms':rec} for name,rec in recipes.values()],nodes=nodes,output=out,named_nodes=names,operation_counts=counts,total_operations=sum(counts.values()),degree_certificate_variant=certificate,fixed_binding='../COEFFICIENT_BINDING.json',proof='../PROOF.md')

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
        for absorb in (False,True):
          for positive in (False,True):
            label=bridge+'_'+('absorbed' if absorb else 'original')+'_'+('positive' if positive else 'natural')
            body=build(positive,False,bridge,absorb);certbody=build(positive,True,bridge,absorb);degree=degree_certificate(certbody)
            for suffix,b in [('',body),('_certificate',certbody)]:
                b['exact_degree']=degree['exact_degree'];(ROOT/f'generated/{label}{suffix}.json').write_text(json.dumps(b,separators=(',',':'))+'\n')
            (ROOT/f'generated/{label}_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
            ledger[label]={'degree':degree['exact_degree'],'operations':body['total_operations'],'operation_counts':body['operation_counts'],'certificate_operations':certbody['total_operations']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
