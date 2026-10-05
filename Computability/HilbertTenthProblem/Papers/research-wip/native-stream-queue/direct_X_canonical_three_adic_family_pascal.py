"""Fresh scalar evidence only: no source arrays, old imports or scientific replays."""
from pathlib import Path
import argparse
import hashlib
import json
import math

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'

def require(test,message):
    if not test:raise ValueError(message)

def val(n,p):
    require(n!=0,'nonzero valuation')
    count=0
    while n%p==0:n//=p;count+=1
    return count

def canonical_mod(R,modulus):
    r=(R-1)//2
    X=pow(2,R,2*modulus)
    coefficient=math.comb(2*r,r)
    term=1;answer=0
    for j in range(r+1):
        answer=(answer+coefficient*term)%(2*modulus)
        if j<r:
            numerator=coefficient*(r-j)
            require(numerator%(r+j+1)==0,'adjacent binomial division')
            coefficient=numerator//(r+j+1)
            term=term*X%(2*modulus)
    require(answer%2==0,'integral Y')
    return answer//2

def collect():
    coefficient_comparisons=0
    for r in range(1,26):
        for j in range(r+1):
            expanded=sum(math.comb(2*r-k-1,r-1)*math.comb(k,j)
                         for k in range(j,r+1))
            require(expanded==math.comb(2*r,r+j),'polynomial identity')
            coefficient_comparisons+=1
    valuations=[];coefficient_valuation_cases=0
    for e in range(1,8):
        P=3**e;r=P-2;R=2*P-3
        A=math.comb(2*r-1,r-1)
        require(val(A,3)==e-1,'constant depth')
        least_other=None
        for j in range(r+1):
            expected=e-val((j+2)*(j+3)*(j+4),3)
            require(val(A,3)==expected,'exact coefficient depth')
            if j:
                depth=expected+2*j
                require(depth>e-1,'unique least valuation')
                least_other=depth if least_other is None else min(least_other,depth)
            coefficient_valuation_cases+=1
            if j<r:
                numerator=A*(r-j)
                require(numerator%(2*r-j-1)==0,'Taylor coefficient division')
                A=numerator//(2*r-j-1)
        modulus=3**(e+2)
        residue=canonical_mod(R,modulus)
        require(val(residue,3)==e-1,'full sum depth')
        valuations.append({'e':e,'R':R,'modulus':modulus,'Y_residue':residue,
                           'exact_v3':e-1,'least_nonconstant_depth':least_other})
    orders=[]
    for modulus,order,exponent,tests in [(31,30,6,[15,10,6]),(601,75,42,[25,15])]:
        require(pow(2,25,modulus)==1,'radix divisor')
        require(pow(3,order,modulus)==1,'order multiple')
        proper=[{'exponent':j,'residue':pow(3,j,modulus)} for j in tests]
        require(all(t['residue']!=1 for t in proper),'exact order')
        image=pow(3,exponent,modulus)
        require(2*image%modulus==1,'inverse-two residue')
        orders.append({'modulus':modulus,'order':order,'inverse_two_exponent':exponent,
                       'inverse_two':image,'proper_divisor_checks':proper})
    require(31*601*1801==2**25-1,'factorization')
    family=[]
    for k in [2,4,6,8,10,12]:
        q=2*3**k;e=3*k+2;R=2*3**e-3
        lo=(2*q-1)*(q*q-1);hi=q**3*(q-1)
        require(lo<R<hi and R%16==15,'family sizes')
        pc=R.bit_count()
        require(pc>=5 and e-1>=3*k,'family scales')
        family.append({'k':k,'q':q,'R':R,'pc_R':pc,'v3_Y_proved':e-1,
                       'v2_Y_proved':pc-2,'lower_margin':R-lo,'upper_margin':hi-R,
                       'full_sum_evaluated':False})
    sources=[
        (WIP/'direct_X_short_period_lucas_obstruction_pascal.md',None),
        (WIP/'direct_X_short_period_lucas_obstruction_v2_pascal.md',None),
        (WIP/'direct_X_canonical_resonance_repair_aristotle.md',None),
        (WIP/'complete75_half_binomial_compiler.md',65),
        (ROOT/'Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md',165),
        (Path('/tmp/direct_X_single_prime_radix_root.json'),None)]
    digest=lambda b:hashlib.sha256(b).hexdigest()
    dependencies=[]
    for path,end in sources:
        data=path.read_bytes();lines=data.splitlines(keepends=True)
        end=len(lines) if end is None else end
        require(end<=len(lines),'read endpoint')
        dependencies.append({'path':str(path),'sha256':digest(data),
                             'first_line':1,'last_line':end,
                             'read_span_sha256':digest(b''.join(lines[:end]))})
    return {'status':'PASS: exact valuation and infinite scalar scale family, excluded by every inherited compiler radix',
            'note_sha256':digest(Path(__file__).with_suffix('.md').read_bytes()),
            'helper_sha256':digest(Path(__file__).read_bytes()),
            'dependencies':dependencies,'polynomial_coefficient_comparisons':coefficient_comparisons,
            'coefficient_valuation_cases':coefficient_valuation_cases,
            'direct_canonical_residues':valuations,'order_checks':orders,'scalar_family_controls':family,
            'root_contribution':'Congruence conflict modulo31/601 and binding25|d to original compiler recipe; independently checked here.',
            'limits':['Only new scalar formulas executed','No saved source array evaluation or propagation',
                      'No predecessor/frozen/helper import or execution','No actual compiler zero',
                      'No universal83 or operation count claim','No general canonical no-wrap resolution']}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True)
    args=parser.parse_args();result=collect()
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['polynomial_coefficient_comparisons','coefficient_valuation_cases']}))
    print('full scalar residues',[(x['e'],x['exact_v3']) for x in result['direct_canonical_residues']])

if __name__=='__main__':main()
