#!/usr/bin/env python3
"""Independent exact arithmetic, boundary adversaries, and explicit n=0 witnesses.
No author or earlier program is imported or executed. Inert DAG arithmetic only.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import gcd,lcm,isqrt
import json,itertools,hashlib
ROOT=Path('/workspace/shared/five-signal-diophantine58-20261004')
OUT=Path('/workspace/shared/five-signal-certificate58-independent-audit-20261004')

def cpow(n,imag=4):
    a,b=1,0
    for _ in range(n):a,b=3*a-imag*b,imag*a+3*b
    return a,b

def inherited_geometry(g):
    # Independent rational normalized coordinates and complex division by p.
    D=sum(g);xi=Q(g[0],D)-Q(1,3);yi=Q(g[0]+g[1],D)-Q(2,3)
    px,py=Q(4,205),Q(-26,615);radius=Q(4,1845)
    deficit=radius-xi*xi-yi*yi
    er=(xi*px+yi*py)/radius;ei=(yi*px-xi*py)/radius
    if deficit:return deficit>0
    q=lcm(er.denominator,ei.denominator);d=q;n=0
    while d%5==0:d//=5;n+=1
    if d!=1:return True
    u,v=cpow(n,-4)
    return (er,ei)!=(Q(u,5**n),Q(v,5**n))

def outer_data(g):
    D=sum(g);A=3*g[0]-D;B=3*(g[0]+g[1])-2*D
    delta=4*D*D-205*(A*A+B*B);U=6*A-13*B;V=13*A+6*B
    h=gcd(gcd(abs(U),abs(V)),2*D);u,v,q=U//h,V//h,2*D//h
    r=q;n=0
    while r%5==0:r//=5;n+=1
    P=5**n;b=4*P+1;T=(3+4*b)**n;C,S=cpow(n)
    assert (T-C-b*S)%(b*b+1)==0
    kap=(T-C-b*S)//(b*b+1);k,s=divmod(r,5);t=5-s
    assert 1<=s<=4 and 1<=t<=4 and min(P+C,P-C,P+S,P-S)>=0
    J=delta*delta+(r-1)**2+(u-C)**2+(v+S)**2
    return dict(D=D,A=A,B=B,delta=delta,U=U,V=V,h=h,u=u,v=v,q=q,n=n,r=r,P=P,b=b,T=T,C=C,S=S,k=k,s=s,t=t,kap=kap,J=J)

def gap_for_eta(er,ei):
    px,py=Q(4,205),Q(-26,615)
    xi,yi=px*er-py*ei,px*ei+py*er
    x,y=Q(1,3)+xi,Q(2,3)+yi
    gg=[x,y-x,1-y];den=lcm(*(z.denominator for z in gg))
    out=tuple(int(z*den) for z in gg)
    assert min(out)>0
    return out

def pair(a,b):return (a+b)*(a+b+1)//2+b

def unpair(z):
    d=(isqrt(8*z+1)-1)//2;b=z-d*(d+1)//2
    return d-b,b

def code(g):return 1+pair(g[0]-1,pair(g[1]-1,g[2]-1))

def decode(z):
    a,j=unpair(z-1);b,c=unpair(j)
    return a+1,b+1,c+1

def egcd(a,b):
    if b==0:return abs(a),1 if a>=0 else -1,0
    d,x,y=egcd(b,a%b);return d,y,x-(a//b)*y

def bezout(u,v,q):
    d,a,b=egcd(u,v);h,c,e=egcd(d,q);assert h==1
    return c*a,c*b,e

def pell_at(base,n):
    x,y=1,0;d=base*base-1
    for _ in range(n):x,y=base*x+d*y,x+base*y
    return x,y

def positive_power_zero(base,prefix):
    # Entirely explicit index-one Pell certificate, constructed independently.
    # For parameter w+1, y_w is divisible by w since x_j=1,y_j=j mod w.
    w=base;a,yw=pell_at(w+1,w);assert yw%w==0
    g=yw//w;u=2*a*a-1;v=2*a
    residue=((1-a)*pow(u,-1,4))%4
    beta=a+u*residue
    if beta<2:residue+=4;beta+=4*u
    assert beta%4==1 and beta>1
    M=2*a*base-base*base-1
    values={'out':1,'aMinus1':a-1,'betaMinus1':beta-1,'w':w,'M':M,'g':g,
      'x':a,'y':1,'u':u,'v':v,'s':beta,'t':1,'qb':(beta-1)//4,'qv':v,'strict':M-base}
    naturals={'dwb':0,'dwk':w-1,'dyk':0,'alpha1':0,'alpha2':residue,
      'sigma1':0,'sigma2':residue,'tau1':0,'tau2':0,'rho1':0,'rho2':0}
    values.update({k+'.Plus':v+1 for k,v in naturals.items()})
    assert len(values)==26 and min(values.values())>0
    return {prefix+'.'+k:v for k,v in values.items()}

def full_witness(g,one,quartic,force_rejected=False):
    data=outer_data(g);assert data['n']==0 and data['delta']>=0
    w={}
    def pos(k,v):assert v>0;w[k]=v
    def nat(k,v):assert v>=0;w[k+'.Plus']=v+1
    def sign(k,v):w[k+'.Positive']=max(v,0)+1;w[k+'.Negative']=max(-v,0)+1
    if one:
        for k,v in enumerate(g,1):pos('gap.'+str(k),v)
        nat('decode.inner',pair(g[1]-1,g[2]-1))
    nat('radius.delta',data['delta']);pos('fraction.h',data['h']);pos('fraction.q',data['q'])
    sign('fraction.u',data['u']);sign('fraction.v',data['v'])
    for k,v in enumerate(bezout(data['u'],data['v'],data['q']),1):sign('bezout.'+str(k),v)
    nat('valuation.n',0);w.update(positive_power_zero(5,'power5'))
    w.update(positive_power_zero(23,'power_complex'))
    pos('valuation.r',data['r']);nat('valuation.k',data['k']);pos('valuation.s',data['s'])
    if not quartic:pos('valuation.t',data['t'])
    sign('complex.C',1);sign('complex.S',0);sign('complex.quotient',0)
    for k,v in enumerate((2,0,1,1),1):nat('complex.bound.'+str(k),v)
    pos('acceptance.positive',max(1,data['J']) if force_rejected else data['J'])
    return w

def eval_dag(d,inputs,w):
    assert set(inputs)==set(d['inputs']) and set(w)==set(d['witnesses'])
    assert min(inputs.values())>0 and min(w.values())>0
    values={'i:'+k:v for k,v in inputs.items()}|{'w:'+k:v for k,v in w.items()}
    def read(ref):return int(ref[2:]) if ref.startswith('c:') else values[ref]
    for k,(op,a,b) in enumerate(d['gates']):
        av,bv=read(a),read(b)
        values['g:'+str(k)]=av+bv if op=='+' else av-bv if op=='-' else av*bv
    failures={name:read(a)-read(b) for name,a,b in d['equations'] if read(a)!=read(b)}
    result=read(d['output']);assert result==sum(v*v for v in failures.values())
    return result,failures

def main():
    statistics={};fixtures=[]
    for g in [(217,167,231),(233,171,211),(1,1,1),(193,243,179),(231,191,193),(1,1,10)]:
        d=outer_data(g);actual=d['delta']>=0 and d['J']>0
        assert actual==inherited_geometry(g)
        fixtures.append({'gaps':g,'valid':actual,**{k:d[k] for k in ('delta','h','u','v','q','n','r','C','S','J')}})
    count=0
    for g in itertools.product(range(1,26),repeat=3):
        d=outer_data(g);assert (d['delta']>=0 and d['J']>0)==inherited_geometry(g);count+=1
    statistics['positive_gap_box_1_to_25']=count
    orbit_count=0
    for n in range(101):
        for direction in (-1,1):
            c,s=cpow(n,4*direction)
            assert gcd(gcd(abs(c),abs(s)),5**n)==1
            if n:assert (c%5,s%5)==(3,1 if direction<0 else 4)
            g=gap_for_eta(Q(c,5**n),Q(s,5**n))
            for scale in (1,2,7):
                gg=tuple(scale*x for x in g);d=outer_data(gg)
                expect=n>0 and direction>0
                assert d['delta']==0 and (d['J']>0)==expect and inherited_geometry(gg)==expect
                orbit_count+=1
    statistics['orbit_orientation_scaled_cases']=orbit_count
    rational_count=0
    for numerator in range(-20,21):
        for denominator in range(1,21):
            tt=Q(numerator,denominator);er=(1-tt*tt)/(1+tt*tt);ei=2*tt/(1+tt*tt)
            g=gap_for_eta(er,ei);d=outer_data(g)
            assert d['delta']==0 and (d['J']>0)==inherited_geometry(g)
            rational_count+=1
    statistics['rational_circle_parameter_cases']=rational_count
    extraction=[]
    for n in range(4):
        P=5**n;b=4*P+1;T=(3+4*b)**n;solutions=[]
        for c in range(-P,P+1):
            for s in range(-P,P+1):
                if (T-c-b*s)%(b*b+1)==0:solutions.append((c,s))
        assert solutions==[cpow(n)]
        extraction.append({'n':n,'P':P,'tested_pairs':(2*P+1)**2,'unique_pair':solutions[0]})
    for z in range(1,20001):assert code(decode(z))==z
    for g in itertools.product(range(1,21),repeat=3):assert decode(code(g))==g
    statistics['cantor_code_roundtrips']=20000;statistics['cantor_gap_roundtrips']=8000
    # Exhaustive small primitive-fraction check, including all zero components.
    primitive_count=0
    for U in range(-12,13):
        for V in range(-12,13):
            for denominator in range(1,21):
                h=gcd(gcd(abs(U),abs(V)),denominator);u,v,q=U//h,V//h,denominator//h
                a,b,c=bezout(u,v,q);assert a*u+b*v+c*q==1
                assert lcm(Q(U,denominator).denominator,Q(V,denominator).denominator)==q
                primitive_count+=1
    statistics['gcd_denominator_cases']=primitive_count
    # Explicit malformed candidates demonstrate each essential guard's purpose.
    malformed=[]
    P,b,T,C,S,kap=1,5,1,27,0,-1
    assert T-C-b*S==kap*(b*b+1) and P-C<0
    malformed.append({'removed_condition':'upper extraction bound','forbidden_eta':'1','C':C,'S':S,'P':P,'quotient':kap,'reason_blocked':'P-C=-26 is not natural'})
    malformed.append({'removed_condition':'primitive Bezout','forbidden_eta':'1','u':5,'v':0,'q':5,'n':1,'C':3,'S':4,'false_acceptance_sum':20,'reason_blocked':'5 divides every possible Bezout linear combination'})
    assert (5-1)**2+(3-1)**2+(-4+0)**2==36
    malformed.append({'removed_condition':'positive nonzero residue','forbidden_eta':'(3-4i)/5','q':5,'n':0,'P':1,'r':5,'s':5,'t':0,'false_acceptance_sum':36,'reason_blocked':'t=0 is outside positive domain; alternative s=0 is also forbidden'})
    malformed.append({'removed_condition':'strict acceptance positivity','forbidden_eta':'1','J':0,'reason_blocked':'J=0 is outside positive domain'})
    outside=outer_data((1,1,10));assert outside['delta']<0 and outside['J']>0
    malformed.append({'removed_condition':'natural radius slack','gaps':[1,1,10],'delta':outside['delta'],'reason_blocked':'negative deficit cannot be radius.delta.Plus-1 with positive leaf'})
    full=[];explicit_witnesses=[]
    for path in sorted((ROOT/'evidence').glob('*.dag.json')):
        dag=json.loads(path.read_text());one=path.name.startswith('one-');quartic='quartic' in path.name
        for g in [(1,1,1),(193,243,179),(231,191,193)]:
            witness=full_witness(g,one,quartic)
            inp={'code':code(g)} if one else dict(zip(('g1','g2','g3'),g))
            result,failed=eval_dag(dag,inp,witness);assert result==0 and not failed
            explicit_witnesses.append({'variant':path.name,'inputs':inp,'gaps':g,'positive_witnesses':witness,'output':result})
            neutral=[];blocked=0
            for key in witness:
                mutated=dict(witness);mutated[key]+=1
                out,fail=eval_dag(dag,inp,mutated)
                if out:blocked+=1
                else:
                    neutral.append(key)
                    assert key.startswith('bezout.')
                    component=int(key.split('.')[1]);factor=(outer_data(g)['u'],outer_data(g)['v'],outer_data(g)['q'])[component-1]
                    assert factor==0
            full.append({'variant':path.name,'gaps':g,'code':code(g) if one else None,'complete_positive_witness_zero':True,
              'witness_count':len(witness),'max_witness_decimal_digits':max(len(str(x)) for x in witness.values()),
              'single_leaf_plus_one_rejected':blocked,'neutral_zero_coefficient_bezout_leaves':neutral})
        g=(217,167,231);w=full_witness(g,one,quartic,True)
        inp={'code':code(g)} if one else dict(zip(('g1','g2','g3'),g))
        result,failed=eval_dag(dag,inp,w);assert result==1 and failed=={'acceptance.strict':-1}
        # A complete positive malformed witness: all equations except the C
        # upper bound hold on the rejected tangency input. The guard catches it.
        malicious=dict(w)
        malicious.update({'complex.C.Positive':28,'complex.C.Negative':1,
          'complex.bound.1.Plus':29,'complex.bound.2.Plus':1,
          'complex.quotient.Positive':1,'complex.quotient.Negative':2,
          'acceptance.positive':676})
        result,failed=eval_dag(dag,inp,malicious)
        assert result==676 and failed=={'complex.C_upper':-26}
        if one:
            g=(1,1,1);w=full_witness(g,True,quartic);inp={'code':code(g)+1}
            result,failed=eval_dag(dag,inp,w);assert result==4 and failed=={'decode.outer_cantor':2}
    # Independent corollary witnesses: both output classes contain unbounded code rays.
    code_rays=[{'t':t,'accepted_code':code((t,t,t)),'rejected_code':code((217*t,167*t,231*t))} for t in (1,2,10,100)]
    receipt={'all_checks_passed':True,'method':'Own exact integers/Fractions; all physical validity comparisons inherit the prior proven disk-minus-inverse-orbit predicate. No physical simulator, author checker, emitter, saved program, or Lean execution.',
      'statistics':statistics,'fixtures':fixtures,'bounded_extraction_exhaustion':extraction,'malformed_guard_counterexamples':malformed,
      'full_exponent_zero_dag_tests':full,'univariate_sign_corollary_code_rays':code_rays,
      'limits':'Finite tests support but do not replace the all-input proofs. Nonzero-exponent outer tests use directly calculated power outputs; the all-exponent POWER equivalence is theorem-dependent.'}
    (OUT/'arithmetic-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (OUT/'full-positive-witnesses.json').write_text(json.dumps(explicit_witnesses,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'statistics':statistics,'fixtures':fixtures,'full_dag_tests':len(full),'all_checks_passed':True},indent=2))
if __name__=='__main__':main()
