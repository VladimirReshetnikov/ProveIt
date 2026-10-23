#!/usr/bin/env python3
"""Authored sparse two-block Jones circuits. Upstream scripts are not executed."""
from pathlib import Path
from collections import Counter
import json, hashlib, itertools, math
from collections import defaultdict
from circuit import DAG
from b4_support import quadratic_norm
ROOT=Path(__file__).resolve().parent
KAPPA=2134940

def source(d,variant,code):
    data=json.loads((ROOT/'upstream/parent_quartic31.json').read_text())
    A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const; save=d.save
    variables=['epsilon','g','h','s','w','phi','i','j','z1','z2','z3','residue','normroot']
    v={name:d.var(name) for name in variables}
    ws=code['weights'][1:];W=max(ws);H=max(code['targets']);Kh=H+2*W
    E=H+3*W+2
    if (E+W)%2:E+=1
    b=save('b',M(c(2),P(v['epsilon'],2)))
    base=save('B',M(d.fixed('base_scale'),P(b,2)))
    # These are fixed recipes, not free parameters; complete bindings accompany the DAG.
    recipes={}; coef={}; rows={}
    # Derive the original package31 residuals under x_i = n_i + 1.
    # In particular, do not silently apply package45's extra transport shift.
    for row in data['equations']:
        shifted=defaultdict(int)
        for term in row['terms']:
            powers=term['powers']; active=[i for i,e in enumerate(powers[:31]) if e]
            for ks in itertools.product(*(range(powers[i]+1) for i in active)):
                mon=[0]*31+powers[31:];co=term['coefficient']
                for i,k in zip(active,ks):mon[i]=k;co*=math.comb(powers[i],k)
                shifted[tuple(mon)]+=co
        by_alpha=defaultdict(dict)
        for mon,co in shifted.items():
            if co:
                alpha=mon[:31];fac=math.factorial(2-sum(alpha))*math.prod(math.factorial(e) for e in alpha)
                by_alpha[alpha][mon[31:]]=co*fac
        terms=[]
        for alpha,poly in sorted(by_alpha.items()):
            rec=[{'powers':list(es),'coefficient':co} for es,co in sorted(poly.items())]
            key=json.dumps(rec,sort_keys=True)
            if key not in recipes:recipes[key]=(f'a{len(recipes):03d}',rec)
            name=recipes[key][0]
            if name not in coef:coef[name]=c(rec[0]['coefficient']) if len(rec)==1 and rec[0]['powers']==[0]*4 else d.fixed(name)
            terms.append((alpha,coef[name]))
        rows[row['number']]=terms
    # Windowed fixed powers share each small power across irregular exponents.
    from functools import lru_cache
    @lru_cache(None)
    def chunk(pos,digit):
        if digit==0:return c(1)
        if digit==1:return base if pos==0 else P(chunk(pos-1,1),16)
        return M(chunk(pos,digit-1),chunk(pos,1))
    @lru_cache(None)
    def bp(n):
        if n<0:raise ValueError("negative radix power")
        out=[];pos=0
        while n:
            if n%16:out.append(chunk(pos,n%16))
            n//=16;pos+=1
        return M(*out)
    terms=[]
    for row,target in zip(code['order'],code['targets']):
        for alpha,co in rows[row]:terms.append(M(co,bp(target-sum(x*w for x,w in zip(alpha,ws)))))
    D=save('Dcode',A(*terms));ell=save('ell',A(*(bp(w) for w in ws)))
    targets=save('targets',A(*(bp(h) for h in code['targets'])))
    N0=save('N0',bp(W+1));L=save('block',M(c(2),b,bp(E)))
    mask=save('mask',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Tc=save('Tcode',A(mask,M(S(base,c(2)),targets,N0)))
    Jc=save('Jcode',A(M(c(2),P(A(c(1),v['g']),2),D),targets))
    Sc=save('Scode',A(v['g'],M(Jc,N0)))
    R=save('R',A(P(L,2),M(A(Sc,Tc),L),S(S(L,c(1)),Sc)))
    N=save('N',M(d.fixed('threshold_scale'),bp((E+W+8)//2)))
    cap=save('cap',M(b,bp(W)));Gcap=save('Gcap',M(c(32),cap))
    meta={'variables':variables,'W':W,'H':H,'Kh':Kh,'E':E,'base_scale_exponent':KAPPA,'threshold_scale_exponent':(15*KAPPA-20)//2,
      'coefficient_recipes':[{'name':name,'terms':r} for name,r in recipes.values()],
      'weights':ws,'target_order':code['order'],'targets':code['targets'],'source_parent_sha256':hashlib.sha256((ROOT/'upstream/parent_quartic31.json').read_bytes()).hexdigest()}
    return v,b,N,R,cap,Gcap,meta

def build(variant='signed_seeded',certificate=False,code=None):
    if variant not in ('signed','signed_seeded') or certificate:raise ValueError('Use signed or signed_seeded; the independent nine-variable construction is a sibling package.')
    if code is None:code=json.loads((ROOT/'CODE.json').read_text())
    d=DAG();A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const;save=d.save
    seeded=variant=='signed_seeded'
    v,b,N,R,cap,Gcap,meta=source(d,variant,code)
    omega=save('omega',P(v['w'],2))
    N2=P(N,2);U=save('U',M(N2,omega));Y=save('Y',M(N2,v['s']));MM=save('M',M(R,Y))
    PP=save('P',M(c(2),P(MM,2),U));K=save('K',A(R,c(1),M(v['h'],S(PP,c(1)))))
    aa=save('A',M(MM,A(U,c(1))));B1=save('B1',A(M(c(2),R),c(1)));W1=save('W1',M(b,omega))
    C=save('C',A(B1,W1,v['phi']));J=save('J',S(M(c(4),aa),c(5)))
    Q=save('Q',S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Am1=S(P(aa,2),c(1));C2=P(C,2);D=save('D',A(M(Am1,C2),c(1)))
    E=save('Eratio',M(v['i'],J,D,C2));F=save('F',A(M(Am1,P(E,2)),c(1)))
    G=save('G',A(aa,M(F,S(A(M(C,D),c(1)),aa))));H=save('H',A(B1,M(v['j'],C)))
    I=save('I',A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
    a0=save('a0',A(M(S(P(PP,2),c(1)),P(K,2)),c(1)));a1=save('a1',M(D,F,I))
    u=save('u',M(J,F));vc=save('v',A(M(Q,F),M(J,S(H,C))))
    delta=save('delta',S(C,M(K,Y)))
    Delta=save('Delta',S(M(v['g'],S(cap,v['g']),P(K,2)),P(M(cap,delta),2)))
    stack=a0 if seeded else c(1)
    for k,(value,shift) in enumerate([(v['s'],-4),(v['phi'],8),(Delta,-4)],1):
        stack=save('Cguard'+str(k),M(stack,A(c(1),M(A(M(c(12),value),c(shift)),stack,P(v['z'+str(k)],2)))))
    save('Cguard',stack)
    Z=save('Znonzero',M(*(v[n] for n in ['epsilon','w','i','z1','z2','z3']),*([a0] if seeded else [])))
    den=save('Smerge',M(Z,P(u,5)));rr=A(vc,M(u,v['residue']));u2=P(u,2)
    target=save('Tmerge',M(S(S(P(rr,3),M(u2,rr)),P(u,3)),A(P(rr,2),M(c(23),u2))))
    center=save('Xnorm',S(M(den,v['normroot']),target));den2=P(den,2)
    A0=save('A0norm',M(den2,stack))
    if seeded:
        A1=save('A1norm',M(den2,P(stack,2),a1))
        out=S(P(S(S(P(center,2),A0),A1),2),M(c(4),A0,A1))
    else:
        w2=M(stack,A(P(PP,2),P(K,2),c(2)))
        A1=save('A1norm',M(den2,P(stack,2),a0));A2=save('A2norm',M(den2,P(w2,2),a1))
        out=quadratic_norm(d,center,[A0,A1,A2])
    nodes,out,names=d.prune(out)
    meta.update(schema='proveit-selective-sparse-two-block-jones-v2',variant=variant,certificate=certificate,domain='unrestricted integers',nodes=nodes,output=out,named_nodes=names,
       operation_counts=dict(Counter(n['kind'] for n in nodes if n['kind'] in ['add','sub','mul'])),coefficient_binding='../FIXED_BINDING.json')
    meta['operations']=sum(meta['operation_counts'].values())
    return meta

def degree_certificate(body,prime=1000003):
    rows=[]
    for n in body['nodes']:
        if n['kind']=='variable':row=(1,{():1})
        elif n['kind']=='literal':row=(0,{():n['value']%prime})
        elif n['kind']=='fixed':row=(0,{((n['name'],1),):1})
        else:
            da,ca=rows[n['left']];db,cb=rows[n['right']];cs={}
            if n['kind']=='mul':
                for a,x in ca.items():
                    for b,y in cb.items():
                        ex=dict(a)
                        for name,power in b:ex[name]=ex.get(name,0)+power
                        key=tuple(sorted(ex.items()));cs[key]=(cs.get(key,0)+x*y)%prime
                row=(da+db,cs)
            else:
                dg=max(da,db)
                for degree,coeff,sgn in [(da,ca,1),(db,cb,1 if n['kind']=='add' else -1)]:
                    if degree==dg:
                        for a,x in coeff.items():cs[a]=(cs.get(a,0)+sgn*x)%prime
                row=(dg,cs)
        rows.append((row[0],{a:x for a,x in row[1].items() if x}))
    dg,head=rows[body['output']]
    if len(head)!=1 or not all(k in ['base_scale','threshold_scale'] for k,_ in next(iter(head))):raise ValueError('unresolved leading coefficient')
    return {'exact_degree':dg,'modulus':prime,'leading_fixed_monomial':dict(next(iter(head))),'leading_scalar':next(iter(head.values())),
      'named_degrees':{name:rows[idx][0] for name,idx in body['named_nodes'].items()}}

def main():
    (ROOT/'generated').mkdir(exist_ok=True);ledger={}
    for v in ['signed','signed_seeded']:
        body=build(v);dg=degree_certificate(body);body['exact_degree']=dg['exact_degree']
        (ROOT/f'generated/{v}_degree.json').write_text(json.dumps(dg,indent=2)+'\n')
        (ROOT/f'generated/{v}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        ledger[v]={'operations':body['operations'],'operation_counts':body['operation_counts'],'degree':dg['exact_degree'],'W':body['W'],'H':body['H'],'E':body['E']}
    (ROOT/'generated/LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n');print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
