#!/usr/bin/env python3
"""Cross-paper checks, including expressions read from the final TeX.

Requires Python 3.10+ and SymPy. Run from any working directory.
The small parser is deliberately limited to the polynomial expressions used here;
it is NOT a general TeX parser. Finite tests are reported as finite tests.
Reads the current sources (Papers/1980, Papers/1982). The rounding check
16e44 < 47216*5^58+9728 < 17e44 is left to round4_1982_checks.py, which covers
it with a tighter interval. The control-character check runs over all six
article sources.
"""
from __future__ import annotations
import importlib.util
import json
import math
from pathlib import Path
import re
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application, convert_xor
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
REPORT={}

def require(test: bool, message: str) -> None:
    if not test: raise AssertionError(message)

def polynomial_tex(text: str) -> sp.Expr:
    """Parse only a polynomial expression in the particular source alphabet."""
    text=re.sub(r'\\(?:Bigl|Bigr|bigl|bigr|left|right|quad|qquad|allowbreak)\b','',text)
    text=text.replace('\\\\',' ').replace('&',' ').replace('\\,',' ')
    greek={r'\lambda':'lam',r'\theta':'theta',r'\ell':'l'}
    for a,b in greek.items(): text=text.replace(a,' '+b+' ')
    require('\\' not in text,f'Unsupported control sequence: {text}')
    text=text.translate(str.maketrans({'{':'(', '}':')','[':'(',']':')'}))
    tokens=re.findall(r'lam|theta|[a-zA-Z]|[0-9]+|[()+*/^\-]',text)
    require(''.join(tokens)==re.sub(r'\s+','',text),'Unexpected TeX expression token')
    names={n:sp.Symbol(n) for n in set(tokens) if n.isalpha()}
    return parse_expr(' '.join(tokens),local_dict=names,
        transformations=standard_transformations+(convert_xor,implicit_multiplication_application))

def read_r(text: str) -> list[sp.Expr]:
    expressions=re.findall(r'\\begin\{aligned\}\s*r=\{\}&(.*?)\\end\{aligned\}',text,re.S)
    require(len(expressions)==2,f'Expected two r formulas, got {len(expressions)}')
    return [polynomial_tex(s.rstrip().rstrip(',')) for s in expressions]

def check_source_packing() -> None:
    t80=(ROOT/'1980/jones1980_corrected.tex').read_text(encoding='utf-8')
    t82=(ROOT/'1982/jones1982_corrected.tex').read_text(encoding='utf-8')
    b,q,g,e,l,z,lam,theta,x,n,r,s,w=sp.symbols('b q g e l z lam theta x n r s w')
    S1=g; T1=q**3-1-(b-1)*l
    S2=e+l*q**2; T2=theta*lam
    S3=2*(e-z*lam)*(1+x*b**5+g)**4+lam*b**5*(1+q**4)
    T3=(b**5-2)*q
    S=S1+S2*q**3+S3*q**7
    T=T1+T2*q**3+T3*q**7
    target=S*(n*n-n)+(T+1)*(n*n-1)
    for k,formula in enumerate(read_r(t80)+read_r(t82),1):
        require(sp.expand(formula-target)==0,f'r formula {k} does not match packing derivation')
    pcount=0
    for t in (t80,t82):
        p=re.findall(r'(?<![a-z])p=(.*?),\\(?:q?quad)',t)
        require(len(p)==1,'Cannot locate p definition uniquely')
        pp=polynomial_tex(p[0])
        require(sp.expand(pp-2*(r*n*n*s)**2*(n*n*w))==0,'p scaling mismatch')
        pcount+=1
    old=t80.replace(r'\lambda b^5q^4\bigr)q^7',r'\lambda b^5q^4\bigr)q^4')
    old=old.replace(r'+(b^5-2)q^8\Bigr](n^2-1)',r'+(b^5-2)q^5\Bigr](n^2-1)')
    old_r=read_r(old)[0]
    discrepancy=S3*(q**4-q**7)*(n*n-n)+(b**5-2)*(q**5-q**8)*(n*n-1)
    require(sp.expand(old_r-target-discrepancy)==0,'Old-error polynomial does not match')
    require(sp.expand(discrepancy)!=0,'Old and corrected r formulas unexpectedly agree')
    # An identity counterexample, explicitly not a full Diophantine witness.
    evaluation={b:2,q:2,g:1,e:2,l:1,z:1,lam:1,theta:1,x:1,n:2**16}
    difference=int(discrepancy.subs(evaluation))
    require(difference!=0,'Discrepancy example failed')
    # Guard against damaging valid Pell alternatives in future edits.
    require(r'a+f^2(d^2-a)' in t80,'1980 valid d^2 Pell alternative lost')
    require(r'a+f^{2}(d^{2}-a)' in t82,'1982 valid d^2 Pell alternative lost')
    REPORT['final_source_formulas']={
        'r_formulas_read_and_verified':4,'p_formulas_read_and_verified':pcount,
        'old_r_discrepancy_identity':True,
        'non_witness_identity_counterexample_difference':str(difference),
        'p_corrected_to_old_ratio':'n^4',
        'valid_d_squared_pell_alternatives_retained':True}

def check_quadratic_elimination() -> None:
    path=HERE/'jones1982_verification.py'
    spec=importlib.util.spec_from_file_location('round1_jones1982_verification',path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    inventory,formulas=module.quadratic_certificate()
    names=inventory['retained_names']+inventory['helper_names']+['x','z','u','y','L','kappa']
    syms={name:sp.Symbol(name) for name in names}
    B,C1,D,D1,E,F,G,H,I,K,M,N,P,R,S,T,U,Y,c,e,g,h,i,j,l,m,o,s,t,w,alpha,Delta,gamma,lam,phi,eps=[syms[v] for v in inventory['retained_names']]
    x,z,u,y,L,kappa=[syms[k] for k in ['x','z','u','y','L','kappa']]
    tau=syms['tau']; slack8=syms['slack8']; slack21=syms['slack21']
    b=eps+x; A=M*(U+1); C=2*R+1+C1+phi; Q=1+lam*(B-1)
    defs={
        'LB':lam*B,'b2':b*b,'J1':2*A*B-B*B-1,'AC1':A*C1,
        'c2':c*c,'c4':c**4,'Q2':Q**2,'Q3':Q**3,'Q4':Q**4,
        'c4Q3':c**4*Q**3,'Nsq':N*N,'MU':M*U,'PK':P*K,
        'YK':Y*K,'AC':A*C,'Csq':C*C,'AE':A*E,'Fsq':F*F,'GH':G*H}
    sub={syms[k]:v for k,v in defs.items()}
    targetS=g+(l+e*Q)*Q+(-2*c**4*(z*(lam+Q)-e)+B*lam*(1+Q))*2*z*Q**3
    targetT=Q-1-(b-1)*l+(B-2*z)*lam*(1+Q)*Q+(B-2)*Q*2*z*Q**3
    targets={
        'D2':B-kappa*b**4,
        'D3':D1-Q-C1*(A-B)-alpha*(2*A*B-B**2-1),
        'D4':D1**2-(A**2-1)*C1**2-1,
        'D5':C1-L-Delta*(A-1),'D6':c-1-x*B-g,
        'D8':e+2*z*b*l+2*z*B*c**4+slack8-2*z*Q,
        'D9':l-u-t*(B-2*z),'D10':e-y-m*(B-2*z),
        'D16 S':S-targetS,'D16 T':T-targetT,'D17':N-16*z*Q**5,
        'D18':R-S*(N*N-N)-(T+1)*(N*N-1),
        'D19':P-2*M*M*U,'D20':tau*tau-(P*P-1)*K*K-1,
        'D21':4*(C-K*Y)**2+slack21-K*K,
        'D22':K-R-1-h*(P-1),'D23':M-R*Y,
        'D26':U-N*N*w,'D27':Y-N*N*s,
        'D30':D-b*w-C*(A-2)-gamma*(4*A-5),
        'D31':I-D-o*F,'D32':D*D-(A*A-1)*C*C-1,
        'D33':E-i*C*C,'D34':F*F-(A*A-1)*E*E-1,
        'D35':G-A-F*F*(F*F-A),'D36':H-2*R-1-j*C,
        'D37':I*I-(G*G-1)*H*H-1}
    checked=[]
    for name,formula in formulas.items():
        expr=sp.sympify(formula,locals=syms).subs(sub,simultaneous=True)
        expected=0 if name.startswith('helper ') else targets[name]
        require(sp.expand(expr-expected)==0,f'Quadratic helper elimination mismatch: {name}')
        checked.append(name)
    require(len(checked)==46,'Certificate equation count changed')
    REPORT['extended_quadratic_certificate_audit']={
        'unknowns':inventory['total_unknowns'],'helper_equations_and_reduced_residuals_checked':checked,
        'equations':len(checked),'maximum_degree_including_x':inventory['maximum_degree_including_x'],
        'sum_of_squares_degree':4,
        'scope':'Algebraic elimination of every retained quadratic-certificate residual; not a formal proof of the existence lemmas.'}

def check_binary_bridge() -> None:
    count=0
    for top in range(256):
        for lower in range(top+1):
            odd=math.comb(top,lower)%2==1
            subset=(lower&top)==lower
            no_carry=(lower&(top-lower))==0
            require(odd==subset==no_carry,'Lucas/Kummer/mask bridge failed')
            count+=1
    REPORT['binary_bridge']={'cases':count,'range':'0 <= lower <= top <= 255',
        'identity':'binomial(top,lower) odd iff (lower & top)=lower iff lower and top-lower add without binary carries'}

def check_pell_congruence() -> None:
    count=0
    for A in range(2,21):
        chi,psi=1,0
        for n in range(1,13):
            chi,psi=A*chi+(A*A-1)*psi,chi+A*psi
            require(chi*chi-(A*A-1)*psi*psi==1,'Pell equation failed')
            for V in range(1,A+1):
                modulus=2*A*V-V*V-1
                require((chi-V**n-(A-V)*psi)%modulus==0,'Pell exponential congruence failed')
                count+=1
    REPORT['pell_congruence']={'cases':count,'parameters':'2<=A<=20; 1<=n<=12; 1<=V<=A',
        'identity':'chi_A(n) = V^n + (A-V) psi_A(n) modulo 2AV-V^2-1',
        'V_2_modulus':'4A-5'}

def check_zero_divisibility() -> None:
    count=0
    for a in range(65):
        for b in range(65):
            qs=[q for q in range(b+1) if b==a*q] # t=b-q is then forced
            expected=(b==0) if a==0 else (b%a==0)
            require(len(qs)==int(expected),'Divisibility witness not singlefold')
            count+=1
    REPORT['zero_safe_singlefold_divisibility']={'input_pairs':count,
        'range':'0<=a,b<=64, every possible witness examined because q+t=b',
        'formula':'exists q,t>=0: b=a*q and b=q+t','zero_zero_witness':[0,0]}

def check_source_characters() -> None:
    years=('1974','1976','1978','1980','1982','1984')
    for year in years:
        text=(ROOT/year/f'jones{year}_corrected.tex').read_text(encoding='utf-8')
        require(not any(ord(ch)<32 and ch not in '\t\n\r' for ch in text),'Control character in source')
    REPORT['source_control_characters']={'articles':len(years),'status':'PASS'}

def main() -> None:
    check_source_packing(); check_quadratic_elimination(); check_binary_bridge()
    check_pell_congruence(); check_zero_divisibility(); check_source_characters()
    REPORT['status']='PASS'
    text=json.dumps(REPORT,indent=2,ensure_ascii=False)+'\n'
    (HERE/'corpus_cross_review_results.json').write_text(text,encoding='utf-8',newline='\n')
    print(text)
if __name__=='__main__': main()
