"""Independent exact identities, inert DAG checks, and finite-field rays."""
import gzip,hashlib,json,random
from collections import Counter
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:raise ValueError(message)

def verify():
    pins=json.loads((ROOT/'READONLY_PINS.json').read_text())
    for rel,digest in pins.items():
        require(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest,'read-only source pin: '+rel)
    data=json.loads((ROOT/'thirteen_positive_degree126.json').read_text())
    rows=data['source']; names=set(data['witnesses']+data['fixed_numerals'])
    require(len(data['witnesses'])==13 and len(rows)==91,'size')
    for name,kind,a,b in rows:
        require(name not in names and kind in '+-*','row')
        require(all(type(x)==int or x in names for x in (a,b)),'topology')
        names.add(name)
    live={data['output']}
    for name,kind,a,b in reversed(rows):
        require(name in live,'dead gate')
        live.update(x for x in (a,b) if isinstance(x,str))
    require(set(data['witnesses']+data['fixed_numerals'])<=live,'dead leaf')
    require(Counter(r[1] for r in rows)==Counter({'*':51,'+':24,'-':16}),'counts')
    M,C,V,y=s.symbols('M C V y');Q=M*C
    Z=C*(V**2-1)+(Q-1)*y*(2-M*y)
    require(s.expand(M*Z-(Q*V**2-(Q-1)*(M*y-1)**2-1))==0,'quotient identity')
    W,U,S,g,tau=s.symbols('W U S g tau')
    norm=(W**2+U**2*g**2-S**2*tau**2)**2-4*W**2*U**2*g**2
    require(s.expand(norm-s.prod(W-a*U*g-b*S*tau for a in [-1,1] for b in [-1,1]))==0,'norm identity')
    H,l,b,G,z,k=s.symbols('H ell b G z k')
    W=U*b+H*(U*l+z);A=1+l*(l+k);D0=b*b-G
    C2=U*U*D0+2*U*H*b*z+H*H*(2*U*l*z+z*z-U*U*l*k-U*U)
    rhs=4*U**4*H**2*l**2*D0+4*U**2*H*b*l*C2+C2**2-4*U**4*H**2*G*(l*k+1)
    require(s.expand((W*W+U*U*G-U*U*H*H*A)**2-4*W*W*U*U*G-rhs)==0,'degree cancellation identity')
    ports={};hashes={}
    for name,rel in data['coefficient_payloads'].items():
        raw=gzip.decompress((ROOT/rel).read_bytes());ports[name]=int.from_bytes(raw,'little');hashes[name]=hashlib.sha256(raw).hexdigest()
    parent_checks=json.loads((ROOT/'upstream/low_degree/CHECKS.json').read_text())['coefficient_files']
    for n,file in [('beta','beta.bin'),('K0','K.bin'),('MC','MC.bin'),('MF','MF_source.bin')]:
        require(hashes[n]==parent_checks[file],'coefficient hash')
    def add(a,b,p,sign=1):
        c=[0]*max(len(a),len(b))
        for i,v in enumerate(a):c[i]=v
        for i,v in enumerate(b):c[i]=(c[i]+sign*v)%p
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    def mul(a,b,p):
        c=[0]*(len(a)+len(b)-1)
        for i,v in enumerate(a):
            for j,w in enumerate(b):c[i+j]=(c[i+j]+v*w)%p
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    rays=[]
    for p in [1000003,1000033,1000037]:
        for tscale,yscale in [(3,1),(4,2)]:
            vals={name:[v%p] for name,v in ports.items()}
            vals.update({name:[0,tscale if name=='t' else yscale if name=='y' else 1] for name in data['witnesses']})
            for name,kind,a,b in rows:
                aa=[a%p] if type(a)==int else vals[a];bb=[b%p] if type(b)==int else vals[b]
                vals[name]=mul(aa,bb,p) if kind=='*' else add(aa,bb,p,1 if kind=='+' else -1)
            beta=ports['beta']%p; q0=beta;E0=pow(beta,4,p);c0=2*pow(beta,3,p)%p;I0=c0*c0%p
            H0=4*E0%p;U0=4*pow(beta,4,p)%p;l0=E0*c0%p
            N68=4*pow(U0,4,p)*pow(H0,3,p)*pow(l0,3,p)*(2*tscale-2)%p
            Nt0=(beta-2)-beta
            Z22=E0*(c0*c0-E0*E0*yscale*yscale)%p
            leader=-N68*E0*E0*I0*I0*Z22*Nt0%p
            require(len(vals['N'])==69 and vals['N'][-1]==N68,'main norm degree ray')
            require(len(vals['Z'])==23 and vals['Z'][-1]==Z22,'quotient degree ray')
            require(len(vals['out'])==127 and vals['out'][-1]==leader and leader!=0,'output degree ray')
            rays.append({'prime':p,'t_scale':tscale,'y_scale':yscale,'degree':126,'leader':leader})
    residue_checks=0
    for m in range(2,25):
        xp,yp=1,0
        for r in range(1,32):
            xp,yp=m*xp+(m*m-1)*yp,xp+m*yp
            if r%4==3:
                require(yp%(m*m)==m*m-1,'canonical residue')
                residue_checks+=1
    result={'operations':91,'operation_counts':dict(Counter(r[1] for r in rows)),
        'positive_variables':13,'exact_degree':126,'readonly_pins_verified':len(pins),'universal_symbolic_identities':3,
        'finite_field_rays':rays,'odd_pell_residue_checks':residue_checks,'coefficient_hashes':hashes,
        'circuit_sha256':hashlib.sha256((ROOT/'thirteen_positive_degree126.json').read_bytes()).hexdigest(),
        'limits':'Finite checks verify transcription, not compiler soundness or consistency. Exact degree is proved in PROOF.md.'}
    return result
if __name__=='__main__':
    report=verify();(ROOT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
