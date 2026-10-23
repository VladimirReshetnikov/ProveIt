#!/usr/bin/env python3
"""Fixed-polynomial B4 Jones front end and signed14 finalizer.
All fixed powers are division-free binary circuits. No implicit witnesses.
"""
from pathlib import Path
import json
from circuit import DAG, canonical_keys
from b4_support import coding_blocks_b4, geometric_pair, quadratic_norm
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'sun/sources/data'
WEIGHTS=ROOT.parent/'root_checks/bose_chowla_31_optimized.json'
VARIABLES=['epsilon','g','h','s','w','phi','i','j','z1','z2','z3','z4','residue','normroot']
INDEX_EXPONENT=4269855
KAPPA=4269877

def construct(count=14):
    assert count in (13,14)
    variables=[v for v in VARIABLES if count==14 or v!='z4']
    constants=json.loads((SOURCE/'constants.json').read_text())
    ws=json.loads(WEIGHTS.read_text())['weights_with_zero'][1:]
    t=max(ws)
    keys,aliases=canonical_keys(constants)
    d=DAG(); A,M,S,P,c=d.plus,d.times,d.minus,d.power,d.const
    v={name:d.var(name) for name in variables}
    save=d.save
    b=save('b',M(c(2),P(v['epsilon'],2)))
    base=save('base',M(d.fixed('base_scale'),P(b,4)))
    qcode,ell,Dcode,top=coding_blocks_b4(d,base,keys,ws)
    for name,val in [('qcode',qcode),('ell',ell),('Dcode',Dcode),('top',top)]:save(name,val)
    N0=save('N0',M(top,base))
    N1=save('N1',M(c(2),P(top,8),base))
    N=save('N',M(N0,N1))
    mask=save('Mcode',S(S(N0,c(1)),M(S(b,c(1)),ell)))
    Tcode=save('Tcode',A(mask,M(S(base,c(2)),qcode,N0)))
    _,geo=geometric_pair(d,base,8*t+1)
    Jcode=save('Jcode',A(M(c(2),P(A(c(1),v['g']),4),Dcode),M(base,geo)))
    Scode=save('Scode',A(v['g'],M(Jcode,N0)))
    R=save('R',M(S(N,c(1)),A(M(A(Scode,Tcode,c(1)),N),Tcode,c(1))))
    Gcap=save('Gcap',M(c(32),b,top))
    omega=save('omega',P(v['w'],2));N2=P(N,2)
    U=save('U',M(N2,omega)); Y=save('Y',M(N2,v['s'])); MM=save('M',M(R,Y))
    PellP=save('P',M(c(2),P(MM,2),U));K=save('K',A(R,c(1),M(v['h'],S(PellP,c(1)))))
    AA=save('A',M(MM,A(U,c(1))));B1=save('B1',A(M(c(2),R),c(1)))
    W1=save('W1',M(b,omega));C=save('C',A(B1,W1,v['phi']));J=save('J',S(M(c(4),AA),c(5)))
    Q=save('Q',S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Aminus=S(P(AA,2),c(1));C2=P(C,2)
    D=save('D',A(M(Aminus,C2),c(1)));E=save('E',M(v['i'],J,D,C2))
    F=save('F',A(M(Aminus,P(E,2)),c(1)))
    GG=save('G',A(AA,M(F,S(A(M(C,D),c(1)),AA))))
    H=save('H',A(B1,M(v['j'],C)));I=save('I',A(M(S(P(GG,2),c(1)),P(H,2)),c(1)))
    a0=save('a0',A(M(S(P(PellP,2),c(1)),P(K,2)),c(1)))
    a1=save('a1',M(D,F,I))
    margin=save('margin',S(M(P(K,2),Gcap),A(M(c(4),P(S(C,M(K,Y)),2),Gcap),M(c(8),v['g'],P(K,2)))))
    cap=save('cap',M(b,top))
    merged=save('Delta',S(M(v['g'],S(cap,v['g']),P(K,2)),P(M(cap,S(C,M(K,Y))),2)))
    guards=[(v['g'],-4),(v['s'],-4),(v['phi'],8),(margin,-4)] if count==14 else [(v['s'],-4),(v['phi'],8),(merged,-4)]
    stack=c(1)
    for k,(value,shift) in enumerate(guards,1):
        disc4=A(M(c(12),value),c(shift))
        factor=A(c(1),M(disc4,stack,P(v['z'+str(k)],2)))
        stack=save('Cguard'+str(k),M(stack,factor))
    save('Cguard',stack)
    divisor=save('Ddiv',M(J,F));dividend=save('Tdiv',A(M(Q,F),M(J,S(H,C))))
    Z=save('Znonzero',M(*(v[name] for name in ['epsilon','w','i']+['z'+str(j) for j in range(1,count-9)])))
    denom=save('Smerge',M(Z,P(divisor,5)))
    r=A(dividend,M(divisor,v['residue']));div2=P(divisor,2)
    target=save('Tmerge',M(S(S(P(r,3),M(div2,r)),M(div2,divisor)),A(P(r,2),M(c(23),div2))))
    w1=save('weight1',stack)
    w2=save('weight2',M(w1,A(P(PellP,2),P(K,2),c(2))))
    center=save('Xnorm',S(M(denom,v['normroot']),target));denom2=P(denom,2)
    aa0=save('A0norm',M(denom2,stack))
    aa1=save('A1norm',M(denom2,P(w1,2),a0));aa2=save('A2norm',M(denom2,P(w2,2),a1))
    out=save('signed'+str(count)+'_b4',quadratic_norm(d,center,[aa0,aa1,aa2]))
    nodes,output,names=d.prune(out)
    body={'schema':'proveit-jones-b4-signed'+str(count)+'-v1','domain':'unrestricted integers',
      'variables':variables,'t':t,'L':4*t,'m':8*t+1,'Ecode':9*t+2,'witness_weights':ws,
      'nodes':nodes,'output':output,'named_nodes':names,
      'operation_counts':{k:sum(x['kind']==k for x in nodes) for k in ('add','sub','mul')},
      'path_base':'directory containing this JSON file',
      'fixed_binding':'../../sun/sources/data/INSTANCE.json',
      'fixed_recipes':{'source_coefficients':'../../sun/sources/data/constants.json','base_scale':f'2^{KAPPA}'},
      'proof':['../FIXED_POLYNOMIAL_CARRY_PROOF.md','../SIGNED_B4_PROOF.md']+(['../THIRTEEN_GUARD_PROOF.md'] if count==13 else [])}
    assert [n['name'] for n in nodes if n['kind']=='variable']==variables
    return body,aliases

def degree_certificate(body,prime=1000003):
    # Exact nonvanishing of a symbolic diagonal leading term is certified by
    # a scalar modulo p times a fixed positive base_scale power.
    rows=[]
    for n in body['nodes']:
        if n['kind']=='variable':row=(1,{():1})
        elif n['kind']=='literal':row=(0,{():n['value']%prime})
        elif n['kind']=='fixed':row=(0,{((n['name'],1),):1})
        else:
            da,ca=rows[n['left']];db,cb=rows[n['right']]
            if n['kind']=='mul':
                cs={}
                for a,x in ca.items():
                    for b,y in cb.items():
                        ex=dict(a)
                        for name,power in b:ex[name]=ex.get(name,0)+power
                        key=tuple(sorted(ex.items()))
                        cs[key]=(cs.get(key,0)+x*y)%prime
                row=(da+db,cs)
            else:
                dg=max(da,db);cs={}
                for degree,coeff,sgn in [(da,ca,1),(db,cb,1 if n['kind']=='add' else -1)]:
                    if degree==dg:
                        for a,x in coeff.items():cs[a]=(cs.get(a,0)+sgn*x)%prime
                row=(dg,cs)
        rows.append((row[0],{a:x for a,x in row[1].items() if x}))
    deg,head=rows[body['output']]
    assert len(head)==1 and next(iter(head.values()))!=0
    mon,scalar=next(iter(head.items()))
    assert all(name=='base_scale' for name,power in mon)
    return {'exact_degree':deg,'formula':'370432*t+84456' if len(body['variables'])==14 else '370496*t+84272','modulus':prime,
      'leading_fixed_monomial':dict(mon),'leading_scalar_modulus':scalar,
      'named_degrees':{name:rows[idx][0] for name,idx in body['named_nodes'].items()}}

def main():
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    ledger={}
    for count in (13,14):
        body,aliases=construct(count);certificate=degree_certificate(body)
        expected=(370432*body['t']+84456) if count==14 else (370496*body['t']+84272)
        assert certificate['exact_degree']==expected
        body['exact_degree']=certificate['exact_degree']
        (out/f'signed{count}_b4.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        (out/f'DEGREE_CERTIFICATE_{count}.json').write_text(json.dumps(certificate,indent=2)+'\n')
        ledger[count]={'degree':certificate['exact_degree'],'t':body['t'],'operations':body['operation_counts'],'total':sum(body['operation_counts'].values())}
    (out/'coefficient_aliases.json').write_text(json.dumps(aliases,indent=2)+'\n')
    (out/'LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print(json.dumps(ledger,indent=2))
if __name__=='__main__':main()
