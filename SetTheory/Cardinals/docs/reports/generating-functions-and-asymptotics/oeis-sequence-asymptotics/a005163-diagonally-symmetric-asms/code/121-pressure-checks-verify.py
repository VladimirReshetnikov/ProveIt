#!/usr/bin/env python3
"""Offline exact verification companion to report121; active guards under -O."""
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from math import comb, factorial
import exact as e
import pressure as pr
ROOT=Path(__file__).resolve().parent
RANGES={'determinant_derivative_n_max':12,'pfaffian_polynomial_n_max':13,
        'interlacing_n_max':13,'matrix_enumeration_n_max':6,'kernel_grid_size':14,
        'rational_matrix_n_max':12,'generalized_matrix_n_max':8,
        'generalized_a':['-1/2','0','1/2','1','2','3','4'],'product_n_max':16,
        'pressure_n_max':8,'pressure_t':['13/4','10/3','7/2','15/4'],
        'mixed_word_sizes':[4,8,12],
        'mixed_words':['A','AT','AAATTT','H','HH','AH','ATH','AHT','AHTH','HHAT','AHHTH','HHHH'],
        'profile_offsets':[-6,6]}

LIMITATIONS=[
 'Finite calculations are independent consistency checks, not proofs of limits or all-size interlacing.',
 'The sparse polynomial identities certify algebraic identities in arbitrary parameters; positivity and analytic conclusions require the report proofs.',
 'The mean inequalities are certified for every positive fugacity at the finite checked sizes by exact polynomial coefficient signs.',
 'Integral checking covers the exact substitution, partial fractions, and elementary evaluation, not an independent numerical quadrature.',
 'The determinant product checks do not certify bibliographic novelty or the analytic Stirling remainder.',
 'Pressure, linear free energy, limiting statistics and root-measure convergence require the separate analytic proof; no full asymptotic equivalent, logarithmic power or amplitude follows from these computations.'
]
FIXTURE_KEYS=['schema_version','report','ranges','provenance','small_z','minus_determinants','ell_at_3','stirling_coefficients','integral','limitations']
PROVENANCE={
 'DSASM_source':'https://arxiv.org/html/2309.08446v3',
 'DSASM_inputs':'Original skew kernel and Pfaffian for Z_n; direct symmetric ASM definition',
 'minus_source':'https://arxiv.org/pdf/1204.3424',
 'minus_location':'Theorem 4.4, b=3; plus norms (3.5b,d)',
 'matrix_source':'Shifted moment/Jacobi identities derived in report121; not a verbatim formula from the Pascal paper',
 'date':'2026-10-02','network_requirement':'None','dependencies':'Python standard library only'}
INVENTORY=['README.md','exact.py','fixtures.json','inventory.json','mutation_tests.py','pressure.py','verify.py']

def exact_json(path,code):
    def pairs(items):
        out={}
        for k,v in items:
            e.need(k not in out,code+'_DUPLICATE_KEY',k); out[k]=v
        return out
    try: return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    except e.Failure: raise
    except (OSError,ValueError) as ex: raise e.Failure(code,str(ex)) from None

def keys(value,wanted,code): e.need(type(value) is dict and set(value)==set(wanted),code)
def rational(value,code):
    e.need(type(value) is str and len(value)<500 and re.fullmatch(r'-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?',value),code)
    q=F(value); e.need(str(q)==value,code+'_CANONICAL'); return q

def load_fixture():
    f=exact_json(ROOT/'fixtures.json','FIXTURE_JSON'); keys(f,FIXTURE_KEYS,'FIXTURE_SCHEMA')
    e.need(type(f['schema_version']) is int and f['schema_version']==1,'FIXTURE_VERSION')
    e.need(f['report']=='report121','FIXTURE_REPORT')
    e.need(f['ranges']==RANGES and all(type(f['ranges'][k]) is type(v) for k,v in RANGES.items()),'FIXTURE_RANGES')
    e.need(f['provenance']==PROVENANCE,'FIXTURE_PROVENANCE')
    e.need(f['limitations']==LIMITATIONS,'FIXTURE_LIMITATIONS')
    keys(f['small_z'],[str(n) for n in range(7)],'FIXTURE_SMALL_Z_SCHEMA')
    for n,p in f['small_z'].items():
        e.need(type(p) is list and len(p)==int(n)+1 and all(type(v) is int and 0<=v<10**8 for v in p),'FIXTURE_SMALL_Z_VALUE')
    keys(f['minus_determinants'],[str(n) for n in range(1,17)],'FIXTURE_MINUS_SCHEMA')
    for v in f['minus_determinants'].values(): rational(v,'FIXTURE_MINUS_VALUE')
    keys(f['ell_at_3'],[str(n) for n in range(1,13)],'FIXTURE_ELL_SCHEMA')
    for v in f['ell_at_3'].values(): rational(v,'FIXTURE_ELL_VALUE')
    e.need(f['stirling_coefficients']==['-3/4','3/4','-961/1152'],'FIXTURE_STIRLING')
    e.need(f['integral']=='(sqrt(3)-1)/4','FIXTURE_INTEGRAL')
    return f

def integrity():
    actual=sorted(p.name for p in ROOT.iterdir())
    e.need(actual==INVENTORY,'INVENTORY_UNEXPECTED_OR_MISSING',repr(actual))
    for p in ROOT.iterdir(): e.need(p.is_file() and not p.is_symlink(),'INVENTORY_FILE_TYPE',p.name)
    m=exact_json(ROOT/'inventory.json','INVENTORY_JSON'); keys(m,['schema_version','files'],'INVENTORY_SCHEMA')
    e.need(type(m['schema_version']) is int and m['schema_version']==1,'INVENTORY_VERSION')
    keys(m['files'],[x for x in INVENTORY if x!='inventory.json'],'INVENTORY_FILES_SCHEMA')
    for name,record in m['files'].items():
        keys(record,['sha256','bytes'],'INVENTORY_RECORD_SCHEMA')
        e.need(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None,'INVENTORY_HASH_FORMAT')
        e.need(type(record['bytes']) is int and record['bytes']>0,'INVENTORY_SIZE_FORMAT')
        data=(ROOT/name).read_bytes()
        e.need(len(data)==record['bytes'],'INVENTORY_SIZE_MISMATCH',name)
        e.need(hashlib.sha256(data).hexdigest()==record['sha256'],'INVENTORY_HASH_MISMATCH',name)
    return len(m['files'])

def run_math(f):
    result={}; result['symbolic']=e.arbitrary_parameter_identities()
    cases=0
    for a in map(F,RANGES['generalized_a']):
        for n in range(1,RANGES['generalized_matrix_n_max']+1): e.rational_matrices(n,a); cases+=1
    result['rational_matrices']={'generalized_cases':cases,'a':RANGES['generalized_a'],'n_max':8,'arbitrary_parameter_polynomial_identities':True}
    p={n:e.pfaffian_polynomial(n) for n in range(RANGES['pfaffian_polynomial_n_max']+1)}
    for n,pn in p.items():
        e.need(all(c.denominator==1 and c>=0 for c in pn) and len(pn)==n//2+1 and pn[-1]==1,'PFAFFIAN_COEFFICIENTS',str(n))
    # Original bivariate coefficient extraction vs original combinatorial coefficient sum.
    grid=RANGES['kernel_grid_size']
    for i in range(grid):
        for j in range(grid):
            e.need(e.kernel(i,j,F(1))==e.original_pfaffian_entry(i,j),'KERNEL_ORIGINAL_ENTRY',f'{i},{j}')
            for t in [F(0),F(3),F(5,2)]:
                expected=e.original_pfaffian_entry(i,j)+(t-1)*(int(j==i+1)-int(i==j+1))
                e.need(e.kernel(i,j,t)==expected,'KERNEL_PARAMETER_ENTRY',f'{i},{j},{t}')
    result['kernel']={'grid':[grid,grid],'fugacities_squared':['0','1','5/2','3']}
    derivatives=[]
    for n in range(1,RANGES['determinant_derivative_n_max']+1):
        V,J,Q=e.rational_matrices(n,F(2))
        H=[[e.kernel(i,j+1,F(3)) for j in range(n)] for i in range(n)]
        B=[[e.kernel(i,j+1,F(3))-e.kernel(i,j+1,F(2)) for j in range(n)] for i in range(n)]
        dn=e.determinant(H); derivative=e.determinant_derivative(H,B); ell=derivative/dn
        e.need(dn==2**n*e.determinant(e.add(e.eye(n),V)),'KERNEL_CALIBRATION',str(n))
        e.need(dn==e.pe(p[n],3)*e.pe(p[n+1],3),'PFAFFIAN_ADJACENT_VALUE',str(n))
        ep=e.pe(e.pd(p[n]),3)/e.pe(p[n],3)+e.pe(e.pd(p[n+1]),3)/e.pe(p[n+1],3)
        e.need(ell==ep,'PFAFFIAN_ADJACENT_DERIVATIVE',str(n))
        r=[F(1,2)]+[F(1,2**(k+1))+(-1)**k for k in range(1,n)]
        T=e.toeplitz(r,n); W=e.mm(T,V)
        e.need(ell==e.trace(e.mm(Q,W))==F(n,2)-e.trace(e.mm(T,Q)),'CALIBRATION_TRACE',str(n))
        d2=[(i+1)*(i+2) for i in range(n)]
        A=[[F(1,2) if i==j else F(1,2**(abs(i-j)+2))*(F(d2[i],d2[j]) if i<j else 1) for j in range(n)] for i in range(n)]
        G=[[F((-1)**(i-j))*(F(d2[i],d2[j]) if i<j else 1) for j in range(n)] for i in range(n)]
        e.need(ell==F(3*n,4)-e.trace(e.mm(A,Q))-e.trace(e.mm(G,Q))/2,'SINGULAR_TRACE_DECOMPOSITION',str(n))
        e.need(str(ell)==f['ell_at_3'][str(n)],'FIXTURE_ELL_MATH',str(n))
        derivatives.append({'n':n,'D_at_3':str(dn),'D_prime_at_3':str(derivative),'ell':str(ell),'A_trace':str(e.trace(e.mm(A,Q))),'G_trace':str(e.trace(e.mm(G,Q)))})
    result['derivatives']=derivatives
    masks={0:{0:1}}; enum=[]
    for n in range(0,RANGES['matrix_enumeration_n_max']+1):
        masks[n],corners=e.asm_masks(n)
        z=[0]*(n+1)
        for mask,count in masks[n].items(): z[mask.bit_count()]+=count
        e.need(z==f['small_z'][str(n)],'FIXTURE_ENUMERATION_MATH',str(n))
        e.need(all(not count or k%2==n%2 for k,count in enumerate(z)),'ENUMERATION_PARITY',str(n))
        e.need(list(map(F,z[n%2::2]))==p[n],'ENUMERATION_PFAFFIAN',str(n))
        if n:
            corner={mask>>1:c for mask,c in masks[n].items() if mask&1}
            e.need(corner==masks[n-1] and corners==sum(masks[n-1].values()),'CORNER_DELETION',str(n))
        enum.append({'n':n,'z':z,'DSASM_count':sum(z),'corner_count':corners,'joint_masks':len(masks[n])})
    result['enumeration']=enum
    inter=[]; q={n:e.q_from_pfaffian(n,pn) for n,pn in p.items()}
    for n in range(1,RANGES['interlacing_n_max']+1):
        cert=e.interlaces(q[n],q[n-1]); cert['n']=n
        den=e.pm(p[n],p[n-1]); numerator=e.pa(e.ps(den,n%2-(n-1)%2),[0]+e.ps(e.pa(e.pm(e.pd(p[n]),p[n-1]),e.ps(e.pm(e.pd(p[n-1]),p[n]),-1)),2))
        plus=e.pa(den,numerator); minus=e.pa(den,e.ps(numerator,-1))
        e.need(all(c>=0 for c in plus+minus),'MEAN_ALL_POSITIVE_FUGACITIES',str(n))
        cert['mean_bound_numerator_coefficients']={'one_plus_delta':list(map(str,plus)),'one_minus_delta':list(map(str,minus))}
        mean=lambda k,t:F(k%2)+2*t*e.pe(e.pd(p[k]),t)/e.pe(p[k],t)
        cert['mean_difference_at_t3']=str(mean(n,F(3))-mean(n-1,F(3)))
        if n<=RANGES['determinant_derivative_n_max']:
            ell=F(f['ell_at_3'][str(n)]); mn=mean(n,F(3)); mn1=mean(n+1,F(3))
            e.need(mn+mn1==1+6*ell,'ADJACENT_MEAN_IDENTITY',str(n))
            e.need(3*ell<=mn<=3*ell+1,'INDIVIDUAL_MEAN_BRACKET',str(n))
        inter.append(cert)
    # Shared roots, including multiplicities, must not be rejected or silently dropped.
    shared=[([0,-1,0,1],[0,0,1],1),([0,0,0,1],[0,0,1],2)]
    for a,b,degree in shared: e.need(e.interlaces(a,b)['gcd_degree']==degree,'SHARED_ROOT_REGRESSION')
    result['interlacing']={'cases':inter,'shared_root_positive_controls':2,'arithmetic':'Exact rational Sturm chains; no float root decisions'}
    products=[]; minus_numerator=F(1); plus_numerator=F(1); denominator=F(1)
    ratios={0:F(1)}
    for n in range(1,RANGES['product_n_max']+1):
        V=[[F(comb(i+j+2,i)) for j in range(n)] for i in range(n)]
        minus=e.determinant(e.add(e.eye(n),e.scale(V,-1))); plus=e.determinant(e.add(e.eye(n),V))
        denominator*=factorial(n-1)*e.rising(F(3),n-1); plus_numerator*=e.plus_H(n-1)
        e.need(plus==plus_numerator/denominator,'ROSENGREN_PLUS',str(n))
        if n%2: e.need(minus==0,'ROSENGREN_MINUS_ODD',str(n))
        else:
            m=n//2; minus_numerator*=9*e.minus_J(m-1)**2
            e.need(minus==(-1)**m*minus_numerator/denominator,'ROSENGREN_MINUS_EVEN',str(n))
            ratios[m]=abs(minus)/plus
            e.need(ratios[m]/ratios[m-1]==9*e.minus_J(m-1)**2/(e.plus_H(n-2)*e.plus_H(n-1)),'ROSENGREN_RATIO',str(n))
        e.need(str(minus)==f['minus_determinants'][str(n)],'FIXTURE_MINUS_MATH',str(n))
        products.append({'n':n,'minus':str(minus),'plus':str(plus),'ratio':str(abs(minus)/plus)})
    result['products']=products; result['stirling']=e.stirling(); result['integral']=e.integral_algebra()
    result['pressure']=pr.run(RANGES)
    return result

def run():
    count=integrity(); f=load_fixture()
    return {'status':'PASS','report':'report121','schema_version':1,'closed_inventory_files':count+1,'ranges':RANGES,'checks':run_math(f),'limitations':LIMITATIONS}

def main():
    try: print(json.dumps(run(),sort_keys=True,indent=2)); return 0
    except e.Failure as ex: print(json.dumps({'status':'FAIL','diagnostic':ex.code,'detail':ex.detail},sort_keys=True)); return 1
    except Exception as ex: print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(ex).__name__+': '+str(ex)},sort_keys=True)); return 2
if __name__=='__main__': sys.exit(main())
