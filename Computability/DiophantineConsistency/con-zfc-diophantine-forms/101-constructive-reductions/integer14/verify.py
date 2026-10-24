#!/usr/bin/env python3
"""Exact norm identities, leading forms, literal graphs, and finite diagnostics.

Python 3.10+, standard library only. No network or unbounded search.
Finite checks do not prove the imported compiler/calibration theorem.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse, hashlib, json, random, sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream/verification'))
from exact_polynomial import Ring
from check_integrated import coefficients, Fp, formal_conjugate_norm, evaluate_dag
from build import build,cleared_norm4

def require(ok,msg):
    if not ok: raise ValueError(msg)

def generic_norm():
    direct=Ring(['x','r0','r1','r2','r3'])
    x,*roots=[direct.var(n) for n in direct.names]
    P=direct.scalar(1)
    for signs in product((-1,1),repeat=4):
        P=P*(x-sum((s*r for s,r in zip(signs,roots)),direct.scalar(0)))
    require(all(all(e%2==0 for e in m[1:]) for m in P.terms), 'radical sign invariance')
    R=Ring(['x','A','B','D','Cn','delta'])
    target={}
    for m,co in P.terms.items():
        xx,aa,bb,dd,cc=m
        require(cc<=16, 'denominator exponent')
        mon=(xx,aa//2,bb//2,dd//2,cc//2,8-cc//2)
        target[mon]=target.get(mon,0)+co
    xx,A,B,D,Cn,de=[R.var(n) for n in R.names]
    actual=cleared_norm4(xx,A,B,D,Cn,de)
    require(actual.terms==target,'every generic norm coefficient')
    return {'conjugate_factors':16,'nonzero_coefficients':len(target),'identity':'delta^8 F16(x;A,B,D,Cn/delta)'}

def defects_and_degrees():
    R=Ring(['U','M','V','Q','a','I','ell','k','X','c'])
    U,M,V,Q,a,I,ell,k,X,c=[R.var(n) for n in R.names]
    H=4*a+3;Delta=a*a+H;L=ell*k;F0=(a+2)*I
    Df=1+Delta*I*I;Dt=1+ell*(ell+1)*k*k;Dm=1+Delta*c*c;b0=X+a*c
    checks=[
      4*U*U*((Q*V*V-1)-(Q-1)*V*V)-4*U*U*(V*V-1),
      4*U*U*Dt-(U*(2*L+k))**2-U*U*(4-k*k),
      4*U*U*Df-(2*U*F0)**2-4*U*U*(1-I*I),
      4*M*M*Dm-(2*M*b0)**2-4*M*M*(1+H*c*c-2*a*c*X-X*X)]
    require(all(not p.terms for p in checks),'four centered-root defects')
    # Exact selected coefficients in the homogeneous leading forms.
    R=Ring(['j','w','v','h','r','c','z','C','n','beta'])
    j,w,v,h,r,c,z,C,n,beta=[R.var(s) for s in R.names]
    q=6*beta*j;W=12*w;X=q*W;Y=q*v;a=X*Y;i=2*r
    Rt=q**4*z-q**3*W*C;k=Rt+h*a;eta=-Y*k
    Q=a**4*i*i*c**4;V=-a*a*i*i*c**4*Rt;L=X*Y*Y*k;F0=a*i*c*c
    U=16*q*q*a
    top540=2**28*U**16*Q**8*V**8*L**4*F0**2*eta**8*n*(n+c)
    mon540=(240,82,94,12,34,68,8,0,2,240)
    require(top540.terms.get(mon540)==2**530*3**322,'actual-slice degree540 coefficient')
    weights=(1,1,1,1,1,1,1,1,1,0)
    require(top540.weighted_degree(weights)==540,'degree540 homogeneous form')
    U=8*q*q*a
    top568=2**8*U**16*Q**8*V**8*L**8*eta**8
    mon568=(256,88,104,16,32,64,8,0,0,256)
    require(top568.terms.get(mon568)==2**520*3**344,'actual-slice degree568 coefficient')
    require(top568.weighted_degree(weights)==568,'degree568 homogeneous form')
    # Integer arithmetic certifies the factor-degree tally from the proven
    # Laurent-series error bounds; the inequalities' proof is in PROOF.md.
    root_degrees=(25,17,13,7);error_degrees=(3,5,5,4)
    require(max(error_degrees)<7,'all square-root corrections are below center remainder')
    require(8*25+4*17+2*13+2*7+8*22==484,'centered norm degree')
    require(8*25+8*17+8*22==512,'one-center norm degree')
    return {'defect_identities':4,'root_degrees':root_degrees,'correction_degree_bounds':error_degrees,
      'norm_degrees':[484,512], 'final_degrees':[540,568],
      'selected_coefficients':['2^530 3^322 beta^240','2^520 3^344 beta^256'],
      'leading_form_terms':[len(top540.terms),len(top568.terms)]}

def independent_front(inputs,ports,prime,centered):
    x={k:Fp(v,prime) for k,v in inputs.items()};p={k:Fp(v,prime) for k,v in ports.items()}
    J=1+6*x['j'];q=1+p['beta']*J;W=4*(3*x['w']+1);X=W*q;Y=x['v']*q
    a=(X+1)*Y;E=a-Y;H=4*a+3;Delta=(a+1)*(a+3)
    C=x['C'];F=p['K0']*C+W*C-x['z']*q+x['z']
    alpha=q-C-F;R=((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
    k=R+1+x['h']*E;c=x['c'];eta=c-Y*k;zeta=(Y+1)*k-c
    I=(2*x['r']+1)*c*c;Df=(a+2)**2*I*I-I*I+1;Q=(Delta*I)**2;delta=Q-1
    V=Df*c*x['T']-Df*R-c;Cy=(delta+1)*V*V-1;ell=X*Y*Y;L=ell*k
    Dtau=L*L+L*k+1;Dmain=1+Delta*c*c;b0=a*c+X;F0=(a+2)*I
    Uc=p['cone_A']*F;Zc=p['cone_B']*C;G=Uc*Zc-(Uc+Zc-q)**2;Peta=eta*zeta
    gv=x['v']**2*G
    guard=gv*Peta-(gv+Peta-1-x['t']**2)**2-(1+x['p1']**2+x['p2']**2+x['p3']**2+x['p3'])
    S=guard*guard
    if centered:
        M=4*q*q;U=M*H
        center=U*x['n']+2*U*V+2*U*L+U*k+2*U*F0+2*M*b0+2*H*(x['v']-q*q)
        A=4*U*U*Df;B=4*U*U*Dtau;Dm=4*M*M*Dmain;Cn=4*U*U*Cy
    else:
        M=2*q*q;U=M*H
        center=U*x['n']+U*V+M*b0+H*(x['v']-q*q)
        A=U*U*Df;B=U*U*Dtau;Dm=M*M*Dmain;Cn=U*U*Cy
    return {k:v.value for k,v in locals().copy().items() if isinstance(v,Fp)}

def diagnostics(packet,ports,centered):
    rng=random.Random(540 if centered else 568);primes=(1000000007,1000000009,1000000033)
    count=0
    while count<36:
        p=primes[count%len(primes)];inputs={n:rng.randrange(-31,32) for n in packet['variables']}
        if count==0:inputs['v']=0
        if count==1:inputs['c']=0
        if count==2:inputs['v']=inputs['c']=0
        f=independent_front(inputs,ports,p,centered)
        if f['delta']==0:continue
        values=evaluate_dag(packet,inputs,ports,p)
        for n,idx in packet['named_registers'].items():
            if n in f:require(values[idx]==f[n], 'independent register '+n)
        roots=[f['A'],f['B'],f['Dm'],f['Cn']*pow(f['delta'],p-2,p)%p]
        norm=pow(f['delta'],8,p)*formal_conjugate_norm(f['center'],roots,p)%p
        target=(norm+f['S']+norm*f['S'])%p
        require(values[packet['output']]==target,'four-conjugate literal transcription')
        count+=1
    return {'samples':count,'primes':primes,'scope':'finite transcription diagnostics, not semantic proof'}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output');args=parser.parse_args()
    norm=generic_norm();degree=defects_and_degrees();ports,binding=coefficients(HERE/'upstream')
    results=[]
    for centered in (True,False):
        packet=build(centered);path=HERE/(packet['name']+'.json')
        require(packet==json.loads(path.read_text()),'byte-independent graph regeneration')
        counts=Counter(n[0] for n in packet['nodes'] if n[0] in ('add','sub','mul'))
        require(sum(counts.values())==packet['operations']==(160 if centered else 147),'exact gate count')
        used={n[1] for n in packet['nodes'] if n[0]=='variable'}
        require(used==set(packet['variables']) and len(used)==14,'fourteen independent live coordinates')
        require(all(n[0] in ('integer','coefficient','variable','add','sub','mul') for n in packet['nodes']),'polynomial gate vocabulary')
        diag=diagnostics(packet,ports,centered)
        results.append({'name':packet['name'],'variables':14,'degree':packet['exact_degree'],
           'operations':packet['operations'],'operation_counts':dict(counts),
           'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'diagnostics':diag})
    out={'status':'PASS','generic_norm':norm,'degree_certificate':degree,'fixed_coefficients':binding,'equations':results}
    if args.output:Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
