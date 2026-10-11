"""Independent endpoint finite-part audit of root's m=0 cotangent resolvent law."""
from pathlib import Path
import mpmath as mp
import argparse
import json
mp.mp.dps=100
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results/latest/resolvent_contact_checks.json')
args=parser.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)

def audit(p,z):
    sig=-2*mp.pi*1j
    xi=(z-mp.pi*1j)/(z+mp.pi*1j)
    c=2*mp.pi*1j/(z+mp.pi*1j)**2
    b=mp.mpf('.01'); K=82
    # Ordinary Laurent expansion of -psi^(p), independently multiplied by R.
    coeff={-p-1:(-1)**p*mp.factorial(p)}
    for k in range(p,K+p+1):
        if k==0: coeff[0]=mp.euler
        else: coeff[k-p]=(-1)**k*mp.zeta(k+1)*mp.factorial(k)/mp.factorial(k-p)
    rp={k:c*(2*mp.pi*1j)**k/mp.factorial(k)*
           (mp.polylog(-k,xi)/xi if xi else 1) for k in range(1,K+1)}
    products={}
    for j,v in coeff.items():
        for k,w in rp.items():
            e=j+k
            if e<=K-p-1: products[e]=products.get(e,0)+v*w
    local=mp.fsum(v*(mp.log(b) if e==-1 else b**(e+1)/(e+1))
                  for e,v in products.items())
    def R(x):
        w=mp.exp(2*mp.pi*1j*x)
        return (w-1)/((z+mp.pi*1j)*(1-xi*w))
    direct=local+mp.quad(lambda x:-mp.polygamma(p,x)*R(x),[b,mp.mpf('.1'),mp.mpf('.4'),1])
    # Expected all-Stieltjes formula specialized to m=0, with order derivative
    # evaluated as a geometrically convergent logarithmic Dirichlet sum.
    terms=[];logterms=[];power=mp.mpc(1)
    for n in range(1,1500):
        term=n**p*power
        terms.append(term);logterms.append(mp.log(n)*term)
        if n>50 and abs(term)<mp.mpf('1e-115'):break
        power*=xi
    Hp=mp.harmonic(p) if p else 0
    expected=c*sig**p*((Hp-mp.euler-mp.log(sig))*mp.fsum(terms)-mp.fsum(logterms))
    err=abs(direct-expected)
    assert err<mp.mpf('1e-78'),(p,z,err)
    return {'p':p,'z':str(z),'absolute_error':mp.nstr(err,10),
            'direct_finite_part':mp.nstr(direct,50)}
rows=[audit(p,z) for z in [mp.pi*1j,1+2j,-mp.mpf('.5')+3j] for p in [1,2,3]]
result={'status':'all checks passed','digits':mp.mp.dps,'checks':rows,
        'qualification':'Independent endpoint Laurent completion plus quadrature, compared to the all-index law at m=0. Floating-point diagnostic, not a proof.'}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'cases':len(rows),'worst_error':max(float(x['absolute_error']) for x in rows)},indent=2))
