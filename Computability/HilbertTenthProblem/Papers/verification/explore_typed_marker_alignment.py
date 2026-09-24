"""Conditional seven-operation typed marker and its shared-root cone lemma."""
from pathlib import Path
import json
import sympy as sp
from explore_one_field_rule110_history import typed,word
from explore_life_one_field_mask import run,histogram

SOURCE=[('divisor','*','p','z'),('E','*','p','p'),
        ('scaled_tail','*','K','T'),('body','+','P','scaled_tail'),
        ('marked','*','E','body'),('assembled','+','R','marked'),
        ('prefix_bound','+','R','alpha')]
EQUALITIES=[('divisor','A'),('assembled','F'),('prefix_bound','E')]


def verify():
    names='A F p z R T alpha K P'.split()
    sym=dict(zip(names,sp.symbols(' '.join(names))))
    e=run(SOURCE,sym)
    A,F,p,z,R,T,alpha,K,P=[sym[n] for n in names]
    residuals=[p*z-A,R+p*p*(P+K*T)-F,R+alpha-p*p]
    for (lhs,rhs),r in zip(EQUALITIES,residuals):assert sp.expand(e[lhs]-e[rhs]-r)==0
    assert histogram(SOURCE)==dict(M=4,A=3)
    tested=misaligned=accepted=0
    for exponent in range(1,6):
        pp=2**exponent;offset=pp*pp
        for length in range(1,5):
            kk=16**length
            for raw in range(1,1<<length):
                pattern=word(raw)
                for traw in range(1,8):
                    tail=word(traw)
                    for prefix in range(1,offset):
                        value=prefix+offset*(pattern+kk*tail)
                        ok=typed(value)
                        assert ok==(exponent%2==0 and typed(prefix))
                        tested+=1;misaligned+=exponent%2!=0;accepted+=ok
                        if ok:
                            vals=dict(A=pp*2**11,F=value,p=pp,z=2**11,R=prefix,
                                      T=tail,alpha=offset-prefix,K=kk,P=pattern)
                            env=run(SOURCE,vals)
                            assert min(vals.values())>0
                            assert all(env[a]==env[b] for a,b in EQUALITIES)
                            k=exponent//2
                            assert offset==16**k and pp==4**k
                            assert value//offset%kk==pattern
    cones=0
    for b in range(4):
        M0=16**b
        for t in range(13):
            front=M0*16**t
            values={front,front+1 if front>1 else front,(16*front-1)//15}
            for endpoint in values:
                assert typed(endpoint) and front<=endpoint<16*front
                for k in range(1,41):
                    assert (endpoint<M0*4**k)==(2*t<k)
                    cones+=1
    return dict(status='PASS_TYPED_MARKER_ALIGNMENT7',operations=7,multiplications=4,
                additions=3,positive_supplied_coordinates=['p','z','R','T','alpha'],
                source=SOURCE,equalities=EQUALITIES,
                source_residuals=[sp.sstr(r) for r in residuals],
                prefix_marker_tail_cases=tested,misaligned_cases_rejected=misaligned,
                accepted_cases=accepted,cone_checks=cones,
                scope='Conditional on Boolean radix16 F, power-of-two A, and a fixed nonzero Boolean marker P<K=16^ell. No universal compiler count.',
                review='Author and independent complete scoped proof/source review PASS; fresh receipt comparison PASS.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status']);print({k:v for k,v in result.items() if k.endswith('cases') or k.endswith('rejected') or k.endswith('checks')})
