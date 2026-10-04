"""Fresh residue evidence for an even-radix boundary, never executing prior code."""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path

PINS = {
 'complete83_shared_projection_scout.json':'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'complete83_shared_projection_math.md':'1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
 'review_complete83_shared_projection_math.md':'8ed2a92dfdc4a8a4c799cdef86adda5af467050704eaefc451eea14ffbed80bb',
 'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
}

def check(p, message):
    if not p:
        raise ValueError(message)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def unique(pairs):
    d = {}
    for k,v in pairs:
        check(k not in d, 'duplicate JSON key')
        d[k] = v
    return d

def factorial_v(n,p):
    result=0
    while n:
        n//=p
        result+=n
    return result

def binomial_v(n,k,p):
    return factorial_v(n,p)-factorial_v(k,p)-factorial_v(n-k,p)

def direct_v(n,p):
    check(n>0,'valuation domain')
    v=0
    while n%p==0:
        n//=p
        v+=1
    return v

def build(root):
    for name,digest in PINS.items():
        check(sha((root/name).read_bytes())==digest,'pin '+name)
    packet=json.loads((root/'complete83_shared_projection_scout.json').read_text(),object_pairs_hook=unique)['packet']
    rows=packet['source']
    check(len(rows)==83,'83 rows')
    check(Counter(r[1] for r in rows)=={'*':46,'+':20,'-':17},'ledger')
    seen=set(packet['free'])
    check(len(seen)==25 and len(packet['witnesses'])==18,'ports')
    for name,op,left,right in rows:
        check(name not in seen,'unique producer')
        check(all(isinstance(v,int) or v in seen for v in (left,right)),'ordered DAG')
        seen.add(name)
    guards=[['repunit','*','Bm1','Jrep'],['q','+','repunit',1],
      ['wn2','*','w','q'],['n2','*','Lbig','q'],['sn2','*','s','n2'],
      ['r_lhs','+','rproduct','mask'],['gam','*','sigma','a4m5'],
      ['shared_main_partial','+','D1','shared_projection'],
      ['exponent_rhs','+','exponent_partial','shared_projection']]
    byname={r[0]:r for r in rows}
    for row in guards:
        check(byname.get(row[0])==row,'interface '+row[0])
    finite_v=0
    for n in range(1,160):
        for k in range(n+1):
            for p in (2,3,19):
                check(binomial_v(n,k,p)==direct_v(comb(n,k),p),'Legendre verification')
                finite_v+=1
    cases=0
    digest=hashlib.sha256()
    for q in range(2,29,2):
        modulus=2*q**3
        for r in range(3,44):
            for w in (1,2,5,11):
                X=q*w
                cs=[comb(2*r,r+j) for j in range(r+1)]
                full=sum(c*X**j for j,c in enumerate(cs))
                short=sum(cs[j]*X**j for j in range(4))
                check(full%2==0,'even half-binomial')
                check((full-short)%modulus==0,'four-term truncation')
                check((full//2%q**3==0)==(short%modulus==0),'scale equivalence')
                digest.update(f'{q},{r},{w},{full%modulus}\n'.encode())
                cases+=1
    # No gigantic X, Y, Pell root, or universal-program tuple is materialized.
    Bm1,K,twiced,b,MC,MF=15,28,8,1,14,19
    J,x,F,Z,alpha=5,1,6,29,32
    q=Bm1*J+1
    C=q-F-Z-alpha-twiced*x
    W=C-Z
    u=twiced*x+b
    R=(q*q-Z-q*F)*(q*q-1)+(MC+q*MF)*J
    r=(R-1)//2
    offset=(1<<u)-W
    check((q,C,W,u,R,r,offset)==(76,1,-28,9,30562815,15281407,540),'diagnostic outer')
    check(R%4==3 and 3*q+1<R and R+2<q**4,'pretyping scalar bounds')
    check((pow(2,R,q)-offset)%q==0,'q divides X')
    Xres=(pow(2,R,q*(q-1))-offset)%(q*(q-1))
    wres=Xres//q
    check((Xres,wres)==(4028,53),'w residue')
    check(((K+wres)*C+q-F-1)%(q-1)==0,'positive transport numerator residue')
    vals={str(p):[binomial_v(2*r,r+j,p) for j in range(4)] for p in (2,19)}
    check(vals=={'2':[16,8,9,8],'19':[3,3,3,3]},'four coefficient valuations')
    check(all(v>=7 for v in vals['2']) and all(v>=3 for v in vals['19']),'scale')
    check(2*q**3==2**7*19**3,'scale factorization')
    # Explicitly retain failed native-mask diagnostics; this is not a compiler slice.
    mask_failures=[(Z-1)&(MC*J+1), F&((MF-Bm1)*J-1)]
    check(mask_failures==[4,2],'non-native diagnostic')
    return {'schema':'complete83_even_radix_boundary_v1','source_sha256':sha(Path(__file__).read_bytes()),
      'pins':PINS,'interface':{'rows':83,'M':46,'A':37,'positive_witnesses':18,'literal_guards':len(guards),'predecessor_evaluation':False},
      'checks':{'small_Legendre_cases':finite_v,'complete_truncation_cases':cases,'records_sha256':digest.hexdigest()},
      'diagnostic':{'fixed':[Bm1,K,twiced,b,MC,MF],'J':J,'x':x,'F':F,'Z':Z,'alpha':alpha,'q':q,'C':C,'W':W,'u':u,'R':R,'r':r,'X':'2^R-540','X_mod_q_times_q_minus_one':Xres,'w_mod_q_minus_one':wres,'binomial_valuations':vals,'failed_native_AND_values':mask_failures,'full_positive_zero':'parametric proof only','valid_compiler_claim':False},
      'scope':{'all_valid_slice_zeros_have_even_q':True,'half_binomial_identity':True,'four_term_scale_equivalence':True,'new_universal_bound':False,'giant_witness_tuple_materialized':False}}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--root',required=True,type=Path)
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--output',type=Path)
    g.add_argument('--expect',type=Path)
    args=p.parse_args()
    result=json.dumps(build(args.root),sort_keys=True,indent=2)+'\n'
    if args.output:
        with args.output.open('x') as f: f.write(result)
    else:
        check(args.expect.read_text()==result,'exact receipt')
    print('PASS: even-radix boundary and q76 scalar residues; no universal-bound claim')

if __name__=='__main__':
    main()
