#!/usr/bin/env python3
"""Portable exact artifact checks; not a replacement for the unbounded proof.

Python standard library only. Explicit exceptions remain active under python -O.
"""
from pathlib import Path
from itertools import product, zip_longest
from collections import Counter
import argparse, gzip, hashlib, importlib.util, json, random, zipfile
import build
from five_square_norm import cleared_norm5, five_square_norm
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok: raise ValueError(msg)

def sha(b): return hashlib.sha256(b).hexdigest()

# Exact finite-field polynomial arithmetic via carry-free integer convolution.
# Packing coefficients into byte-wide radix digits never loses information:
# the chosen digit bound strictly exceeds every unreduced convolution sum.
def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def add(a,b,p,subtract=False):
    sign=-1 if subtract else 1
    return trim([(x+sign*y)%p for x,y in zip_longest(a,b,fillvalue=0)])

def mul(a,b,p):
    if a==[0] or b==[0]: return [0]
    bound=min(len(a),len(b))*(p-1)**2
    width=max(1,(bound.bit_length()+7)//8)
    aa=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in a),'little')
    bb=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in b),'little')
    size=len(a)+len(b)-1
    raw=(aa*bb).to_bytes(size*width,'little')
    return trim([int.from_bytes(raw[i*width:(i+1)*width],'little')%p for i in range(size)])

def evaluate_line(packet,coefficients,p=1009):
    vals=[]
    zeros={'C','z','t'}
    for node in packet['nodes']:
        op=node[0]
        if op=='integer': v=[node[1]%p]
        elif op=='coefficient': v=[coefficients[node[1]]%p]
        elif op=='variable': v=[0] if node[1] in zeros else [0,1]
        elif op=='add': v=add(vals[node[1]],vals[node[2]],p)
        elif op=='sub': v=add(vals[node[1]],vals[node[2]],p,True)
        elif op=='mul': v=mul(vals[node[1]],vals[node[2]],p)
        else: raise ValueError('unknown operation')
        vals.append(v)
    return vals[packet['output']]

def topology(packet):
    nodes=packet['nodes']; live=set()
    for i,node in enumerate(nodes):
        if node[0] in ('add','sub','mul'):
            require(0<=node[1]<i and 0<=node[2]<i,'non-topological node')
        else: require(node[0] in ('integer','variable','coefficient'),'non-polynomial gate')
    def walk(i):
        if i in live:return
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            walk(nodes[i][1]); walk(nodes[i][2])
    walk(packet['output'])
    require(len(live)==len(nodes),'dead supplied node')
    variables={n[1] for n in nodes if n[0]=='variable'}
    require(variables==set(packet['variables']) and len(variables)==12,'variable census')
    ports={n[1] for n in nodes if n[0]=='coefficient'}
    require(ports=={'beta','K0','MC','MF','cone_A','cone_B'},'whole tuple missing')
    counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
    require(dict(counts)==packet['operation_counts'],'operation detail')
    require(sum(counts.values())==packet['operations'],'operation total')
    return dict(counts)

# Independent sparse Z-polynomial implementation for the two new identities.
class Poly:
    nv=5
    def __init__(self,terms=None): self.t={k:v for k,v in (terms or {}).items() if v}
    @classmethod
    def const(cls,n): return cls({(0,)*cls.nv:n})
    @classmethod
    def var(cls,i):
        key=[0]*cls.nv;key[i]=1;return cls({tuple(key):1})
    def coerce(self,x): return x if isinstance(x,Poly) else Poly.const(x)
    def __add__(self,x):
        x=self.coerce(x);t=self.t.copy()
        for k,v in x.t.items():t[k]=t.get(k,0)+v
        return Poly(t)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.t.items()})
    def __sub__(self,x):return self+-self.coerce(x)
    def __rsub__(self,x):return self.coerce(x)+-self
    def __mul__(self,x):
        x=self.coerce(x);t={}
        for a,av in self.t.items():
            for b,bv in x.t.items():
                key=tuple(i+j for i,j in zip(a,b));t[key]=t.get(key,0)+av*bv
        return Poly(t)
    __rmul__=__mul__
    def __pow__(self,k):
        require(isinstance(k,int) and k>=0,'power exponent')
        a=Poly.const(1)
        for _ in range(k):a=a*self
        return a
    def __eq__(self,x):return self.t==self.coerce(x).t

def identities():
    u,D,H,unused1,unused2=[Poly.var(i) for i in range(5)]
    # Independent quadratic-algebra multiplication of (u+d)^powers.
    def qm(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    z=(u,Poly.const(1));z2=qm(z,z);z3=qm(z2,z)
    for carrier in ('pure19','monotone31'):
        if carrier=='pure19':
            actual=qm((z2[0]+3*H**2,z2[1]),(z3[0]-19*H**3,z3[1]))
            q=u*u+D+3*H*H;c0=u*(u*u+3*D)-19*H**3;c1=3*u*u+D
        else:
            actual=qm((z2[0]+31*H**2,z2[1]),(z3[0]+H*H*u+H**3,z3[1]+H*H))
            q=u*u+D+31*H*H;c0=u*(u*u+3*D+H*H)+H**3;c1=3*u*u+D+H*H
        expected=(q*c0+2*u*D*c1,q*c1+2*u*c0)
        require(actual==expected,'quintic algebra identity')
    delta,S,V,W,L=[Poly.var(i) for i in range(5)]
    cy=(delta+1)*V*V-1
    left=delta*(S*V+W-L)**2-S*S*cy
    right=delta*(2*S*V*(W-L)+(W-L)**2)+S*S*(1-V*V)
    require(left==right,'centered pairing identity')
    return {'carrier_identities':2,'centered_pairing_terms':len(left.t)}

def arithmetic_checks():
    rng=random.Random(246013)
    count=0
    for _ in range(40):
        x=rng.randrange(-30,31);roots=[rng.randrange(-7,8) for _ in range(5)]
        ds=[a*a for a in roots];expected=1
        for signs in product((-1,1),repeat=5):
            expected*=x-sum(s*y for s,y in zip(signs,roots))
        require(five_square_norm(x,*ds)==expected,'norm against conjugate product')
        delta=rng.choice((-5,-2,1,2,5))
        got=cleared_norm5(x,ds[0],ds[1],ds[2],ds[3],delta*ds[4],delta)
        require(got==delta**16*expected,'cleared norm against conjugate product')
        count+=1
    # Exhaust every front residue that can affect the key unit certificates.
    residues=0
    for yy,cc,rr,ss,kk in product(range(3),repeat=5):
        XX=2; aa=(XX+1)*yy;HH=4*aa+3;DD=aa*aa+HH
        II=ss*rr*cc*cc; QQ=DD*DD*II*II
        dm=1+DD*cc*cc;df=1+DD*II*II;ell=XX*yy*yy
        dt=1+ell*(ell+1)*kk*kk;uu=(-XX-aa*cc)%3
        BB=(5*uu**4+10*uu*uu*dm+dm*dm+9*HH*HH*uu*uu+3*HH*HH*dm-38*HH**3*uu)
        require((dm%3,df%3,dt%3,BB%3,QQ%3)==(1,1,1,1,0),'prime-three residues')
        residues+=1
    # Finite illustration only; universal intersectivity is proved in PROOF.md.
    roots=0
    for m in range(1,1001):
        require(any(((a*a+3)*(a*a*a-19))%m==0 for a in range(m)),'intersective fixture')
        roots+=1
    return {'norm_square_fixtures':count,'front_residue_fixtures':residues,'intersective_moduli':roots}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'CHECKS.json')
    args=parser.parse_args()
    prov=json.loads((ROOT/'PROVENANCE.json').read_text())
    require(sha((ROOT/'source_interpolation.zip').read_bytes())==prov['source_archive_sha256'],'source archive digest')
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    coefficients={};payloads={}
    for name,meta in binding['payloads'].items():
        raw=gzip.decompress((ROOT/'coefficients'/meta['file']).read_bytes())
        require(sha(raw)==meta['raw_sha256'],'coefficient hash '+name)
        number=int.from_bytes(raw,'little')
        require(len(raw)==meta['raw_bytes'] and number.bit_length()==meta['bits'],'coefficient size '+name)
        coefficients[name]=number;payloads[name]=sha(raw)
    require(coefficients['beta']==(1<<1064921)-1,'literal beta recipe')
    require(coefficients['cone_A']==1<<1113 and coefficients['cone_B']==1<<666104,'cone recipes')
    # The named coefficient convention is immutable, not inferred from file size.
    require(binding['MF_convention']=='MF_native + beta, already shifted','MF convention')
    points=[];expected={'integer':(209,2848,(2848,1760,1408)),
                       'rational':(215,2336,(2400,1440,1152)),
                       'centered':(216,2304,(2512,1592,1248))}
    for carrier in ('pure19','monotone31'):
        for variant in ('integer','rational','centered'):
            packet=build.build(variant=variant,carrier=carrier)
            file=ROOT/'equations'/(packet['name']+'.json')
            frozen=json.loads(file.read_text())
            require(frozen==packet,'literal rebuild '+packet['name'])
            topology(frozen)
            ops,degree,exps=expected[variant]
            require(packet['operations']==ops+(carrier=='monotone31') and packet['exact_degree']==degree,'expected frontier')
            line=evaluate_line(frozen,coefficients)
            want=(pow(2,exps[0],1009)*pow(3,exps[1],1009)*pow(coefficients['beta']%1009,exps[2],1009))%1009
            require(want!=0 and len(line)-1==degree and line[-1]==want,'exact line degree/leader '+packet['name'])
            points.append({'name':packet['name'],'variables':12,'operations':packet['operations'],'degree':degree,
                           'modulus':1009,'leading_coefficient':line[-1],'sha256':sha(file.read_bytes())})
    # Mutation control for the actual frozen artifact, independent of assertions.
    corrupt=json.loads(json.dumps(packet));corrupt['nodes'][0][1]='wrong_variable'
    rejected=False
    try:topology(corrupt)
    except ValueError:rejected=True
    require(rejected,'mutation control failed')
    report={'status':'PASS','proof_scope':'finite artifact checks; universal proof is PROOF.md and stated inherited dependencies',
            'source_archive_sha256':prov['source_archive_sha256'],'coefficient_raw_sha256':payloads,
            'points':points,'exact_identities':identities(),'finite_arithmetic':arithmetic_checks(),
            'negative_controls':{'changed_variable_rejected':rejected}}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','points':[(p['operations'],p['degree']) for p in points],
                      'checks_file':str(args.output)},indent=2))

if __name__=='__main__':main()
