"""Independent algebra/source checks. No claim to test Con(ZFC) or giant coefficients."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,random

ROOT=Path(__file__).resolve().parent

def run(source, values):
    out=dict(values)
    for name,op,a,b in source:
        a=out[a] if isinstance(a,str) else a
        b=out[b] if isinstance(b,str) else b
        out[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return out

def formula(v):
    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,Z,delta,rho,sigma=(
        v[n] for n in ['Jrep','F','alpha','transport_quotient','f','h','i',
        'auxiliary_quotient','s','w','tau_root','eta','zeta','y_aux','Z','delta','rho','sigma'])
    q=v['Bm1']*J+1
    U=w*q; Y=s*q**3; E=U*Y; k=eta+zeta
    c=k*Y+eta; a=E+Y; H=4*a+3; D=a*a+H
    d=U+a*c+(rho+sigma)*H
    C=q-F-Z-alpha-v['fixed_2d']; W=C-Z
    kap=v['fixed_2d_plus_b']+delta*D
    mu=W+a*kap+rho*H
    R=(q*(q-F)-Z)*(q*q-1)+(v['MC']+q*v['MF'])*J
    V=c*(T*f-1)-R*f*f
    B=(i*D*c*c)**2
    L=E*k*Y
    factors=[tau*tau-L*(L+k),d*d-D*c*c,mu*mu-D*kap*kap,
             B*(V*V-y*y)+y*y,k-h*E-R,
             (v['Kconstant']+w)*C+q-F-z*(q-1),D*f*f-B]
    ans=1
    for x in factors:ans*=x
    return ans-D

def main():
    p=json.loads((ROOT/'k215_native82_source.json').read_text())
    old=json.loads((ROOT/'complete84_scaled_strong_output.json').read_text())['packet']
    assert len(p['source'])==82
    oldrows={r[0]:r for r in old['source']}
    assert oldrows['scaled_t']==['scaled_t','*','twice_cell_bits','x']
    assert oldrows['odd_index']==['odd_index','+','scaled_t','inner_bits']
    names=p['positive_witnesses']+p['fixed_numerals']
    random.seed(21582)
    for test in range(120):
        v={n:random.randint(-3,5) for n in names}
        if test>=80:v={n:Fraction(x,random.randint(1,3)) for n,x in v.items()}
        got=run(p['source'],v)['polynomial']
        assert got==formula(v)
        vo={n:v[n] for n in p['positive_witnesses']}
        vo.update({n:v[n] for n in ['Bm1','Kconstant','MC','MF']})
        vo.update(x=1,twice_cell_bits=v['fixed_2d'],inner_bits=v['fixed_2d_plus_b']-v['fixed_2d'])
        assert got==run(old['source'],vo)['polynomial']
    # Exact topological source correspondence is the general folding argument.
    rename={'scaled_t':'fixed_2d','twice_cell_bits':'fixed_2d','odd_index':'fixed_2d_plus_b'}
    folded=[[n,o,rename.get(a,a),rename.get(b,b)] for n,o,a,b in old['source']
            if n not in ['scaled_t','odd_index']]
    assert folded==p['source']
    print(json.dumps({'status':'PASS','scope':'source identity and finite algebra only',
      'gates':82,'M':46,'A':36,'source_constant_fold_identity':True,
      'integer_and_rational_comparisons':120,
      'coefficient_admissibility_tested':False,'kernel_checked':False},indent=2))

if __name__=='__main__':main()
