#!/usr/bin/env python3
"""Division-free circuits for the 12- and 13-positive-variable mergers.

The four coefficient ports must be bound to one authenticated native compiler
tuple.  This file contains no free machine index and never expands the ports.
Run with Python 3.10+. Optional --symbolic checks use an exact sparse
polynomial implementation included below; no third-party package is needed.
"""
from collections import Counter
from pathlib import Path
import argparse, json, random

HERE=Path(__file__).resolve().parent
OUT=HERE.parent/'data'
FIXED=['beta','K0','MC','MF']

class Circuit:
    def __init__(self, witnesses):
        self.witnesses=witnesses
        self.source=[]
        self.known=set(witnesses+FIXED)
    def g(self,name,op,a,b):
        assert name not in self.known and op in ['+','-','*']
        assert all(isinstance(x,int) or x in self.known for x in [a,b])
        self.source.append([name,op,a,b]);self.known.add(name);return name
    def sq(self,name,a):return self.g(name,'*',a,a)
    def packet(self,name,comparisons=None,output=None,degrees=None):
        needed=set(([output] if output else [])+[x for row in (comparisons or []) for x in row if isinstance(x,str)])
        kept=[]
        for row in reversed(self.source):
            if row[0] in needed:
                kept.append(row);needed.update(x for x in row[2:] if isinstance(x,str))
        source=list(reversed(kept)); assert set(self.witnesses+FIXED)<=needed
        counts=Counter(row[1] for row in source)
        p={'name':name,'witnesses':self.witnesses,'witness_domain':'strictly positive integers',
           'fixed_numerals':FIXED,'source':source,'ledger':{'operations':len(source),
             'multiplications':counts['*'],'additions_subtractions':counts['+']+counts['-'],
             'all_gates_live':True,'all_ports_live':True},
           'coefficient_contract':'One whole authenticated blank-native tuple (beta,K0,MC,shifted MF).',
           'coefficient_binding':'COEFFICIENT_BINDING.json'}
        if output:p.update(output=output,exact_degree=degrees)
        else:p.update(comparisons=comparisons,residual_exact_degrees=degrees)
        return p

def common(c):
    g=c.g; s=c.sq
    g('rep','*','beta','J');g('q','+','rep',1);s('q2','q');g('q3','*','q2','q')
    g('X','*','w','q');g('Y','*','s','q3');g('E','*','X','Y');g('k','+','eta','zeta')
    g('kY','*','k','Y');g('c','+','kY','eta');s('c2','c');g('a','+','E','Y')
    g('four_a','*',4,'a');g('H','+','four_a',3);s('a2','a');g('Delta','+','a2','H')
    g('qF','-','q','F');g('C','-','qF','alpha');g('Gpre','*','rep','qF');g('G','+','Gpre','alpha')
    g('q2m1','-','q2',1);g('Rlo','*','G','q2m1');g('qMF','*','q','MF')
    g('mask','+','MC','qMF');g('Rhi','*','mask','J');g('R','+','Rlo','Rhi')
    g('hE','*','h','E');g('k_hE','-','k','hE');g('Nk','-','k_hE','R')
    g('Kw','+','K0','w');g('KwC','*','Kw','C');g('Ntpre','+','KwC','qF')
    g('zrep','*','z','rep');g('Nt','-','Ntpre','zrep')
    g('L0','*','E','kY');g('L0k','+','L0','k');g('Aminus1','*','L0','L0k');g('A','+','Aminus1',1)
    g('I','*','i','c2');s('I2','I')
    g('Bc','*','Delta','c2');g('B','+','Bc',1)
    g('ac','*','a','c');g('Xu','+','X','ac');g('Hu','*','H','u');g('W','+','Xu','Hu')
    g('p','*','H','c');s('p2','p');s('p4','p2');s('W2','W')
    g('r0','+','W2','B');g('r1','*',2,'W');s('r1sq','r1');g('Br1sq','*','B','r1sq')

def norm_finalize(c,real,imag):
    c.sq('norm_real_square',real);c.sq('norm_imag_square',imag)
    c.g('B_norm_imag_square','*','B','norm_imag_square')
    c.g('resultant','-','norm_real_square','B_norm_imag_square')

def construct12():
    c=Circuit(['J','F','alpha','z','h','i','T','s','w','eta','zeta','u']);g=c.g;s=c.sq
    common(c)
    g('Dminus1','*','Delta','I2');g('D','+','Dminus1',1);g('Q','*','Delta','Dminus1');g('d','-','Q',1);s('d2','d')
    s('T2','T');g('v02','*','c2','T2');g('QD','*','Q','D');g('P','*','QD','v02')
    g('RD','*','R','D');g('b','+','c','RD');s('b2','b');g('Z','*','Q','b2')
    g('PZsum','+','P','Z');g('e','-','PZsum',1);g('a0','*','P','Z')
    g('kI2','*','k','I2');g('Mbase','+','kI2','T2');g('M','*',2,'Mbase');s('M2','M')
    g('M2A','*','M2','A');g('N','*','d','M2A');g('S','-','N','e');g('NplusE','+','N','e')
    # H8(v) is monic. Evaluate p^8 H8((W+sqrt(B))/p) as a pair.
    g('dp2','*','d','p2');g('d2p4','*','dp2','dp2')
    g('dNplusE','*','dp2','NplusE');g('ell','*',2,'dNplusE')
    s('S2','S');g('foura0','*',4,'a0');g('topconstant','+','S2','foura0')
    g('scaledconstant','*','d2p4','topconstant')
    s('r0sq','r0');g('rpair2real','+','r0sq','Br1sq')
    g('ellr0','*','ell','r0');g('vpre','-','rpair2real','ellr0');g('vreal','+','vpre','scaledconstant')
    g('twor0','*',2,'r0');g('vimagcore','-','twor0','ell');g('vimag','*','r1','vimagcore')
    g('dSp2','*','dp2','S');g('ureal','+','r0','dSp2')
    g('coefpre','*','a0','d2p4');g('coef','*',16,'coefpre')
    s('vreal2','vreal');s('vimag2','vimag');g('Bvimag2','*','B','vimag2');g('vpair2real','+','vreal2','Bvimag2')
    s('ureal2','ureal');g('upair2real','+','ureal2','Br1sq');g('coefupair','*','coef','upair2real')
    g('hreal','-','vpair2real','coefupair')
    g('vrealvimag','*','vreal','vimag');g('urealr1','*','ureal','r1');g('coefur','*','coef','urealr1')
    g('himaghalf','-','vrealvimag','coefur');g('himag','*',2,'himaghalf')
    norm_finalize(c,'hreal','himag')
    system=c.packet('merger12_system',comparisons=[['Nk',1],['Nt',1],['norm_real_square','B_norm_imag_square']],degrees=[7,2,1520])
    g('guard','+','resultant',1);g('Nkt','*','Nk','Nt');g('all','*','Nkt','guard');g('polynomial','-','all',1)
    poly=c.packet('merger12_product',output='polynomial',degrees=1529)
    return system,poly

def construct13():
    c=Circuit(['J','F','alpha','z','f','h','i','T','s','w','eta','zeta','u']);g=c.g;s=c.sq
    common(c)
    s('f2','f');g('f2minus1','-','f2',1);g('K','*','Delta','f2minus1');g('d','-','K',1)
    g('Tf','*','T','f');g('Tfminus1','-','Tf',1);g('cTf','*','c','Tfminus1')
    g('Rf2','*','R','f2');g('V','-','cTf','Rf2');s('V2','V');g('KV2','*','K','V2');g('e','-','KV2',1)
    g('dA','*','d','A');g('dAminusE','-','dA','e');g('d2AminusDE','*','d','dAminusE')
    g('scaledC','*','p2','d2AminusDE');g('pairSreal','+','r0','scaledC')
    g('d2A','*','d','dA');g('d2Ap2','*','d2A','p2');g('fourD2Ap2','*',4,'d2Ap2')
    s('pairSreal2','pairSreal');g('pairSsquare_real','+','pairSreal2','Br1sq')
    g('subtractReal','*','fourD2Ap2','r0');g('hreal','-','pairSsquare_real','subtractReal')
    g('twopairS','*',2,'pairSreal');g('imagCore','-','twopairS','fourD2Ap2');g('himag','*','r1','imagCore')
    norm_finalize(c,'hreal','himag')
    system=c.packet('merger13_system',comparisons=[['Nk',1],['Nt',1],['I2','K'],['norm_real_square','B_norm_imag_square']],degrees=[7,2,22,288])
    g('strong_diff','-','I2','K');g('Ns','+','strong_diff',1)
    g('guard','+','resultant',1);g('Nkt','*','Nk','Nt');g('NktS','*','Nkt','Ns')
    g('all','*','NktS','guard');g('polynomial','-','all',1)
    poly=c.packet('merger13_product',output='polynomial',degrees=319)
    return system,poly

def evaluate(p,values,mod=None):
    vs=dict(values)
    for n,op,a,b in p['source']:
        a=a if isinstance(a,int) else vs[a];b=b if isinstance(b,int) else vs[b]
        v=a+b if op=='+' else a-b if op=='-' else a*b
        vs[n]=v if mod is None else v%mod
    return vs

def degree_bounds(p):
    ds={x:1 for x in p['witnesses']};ds.update({x:0 for x in FIXED})
    for n,op,a,b in p['source']:
        a=0 if isinstance(a,int) else ds[a];b=0 if isinstance(b,int) else ds[b]
        ds[n]=a+b if op=='*' else max(a,b)
    return ds

def symbolic_checks():
    # Deliberately small exact sparse-polynomial implementation over Z.
    # It is used only for the monic identities, not to expand final polynomials.
    dim=9;zero=(0,)*dim
    class Poly:
        def __init__(self,data):self.data={k:v for k,v in data.items() if v}
        @staticmethod
        def lift(x):return x if isinstance(x,Poly) else Poly({zero:x})
        def __add__(self,other):
            data=dict(self.data)
            for k,v in Poly.lift(other).data.items():data[k]=data.get(k,0)+v
            return Poly(data)
        __radd__=__add__
        def __neg__(self):return Poly({k:-v for k,v in self.data.items()})
        def __sub__(self,o):return self+-Poly.lift(o)
        def __rsub__(self,o):return Poly.lift(o)+-self
        def __mul__(self,other):
            data={}
            for k,v in self.data.items():
                for l,w in Poly.lift(other).data.items():
                    key=tuple(x+y for x,y in zip(k,l));data[key]=data.get(key,0)+v*w
            return Poly(data)
        __rmul__=__mul__
        def __pow__(self,n):
            out=Poly.lift(1)
            for _ in range(n):out=out*self
            return out
    def var(j):
        key=list(zero);key[j]=1;return Poly({tuple(key):1})
    d,N,e,a0,t,v,A=[var(j) for j in range(7)]
    C=d*t*t+N-e;U=C*C+4*(a0-d*t*t*N)
    R=U*U-16*C*C*a0
    def h8(v):return (v**4-2*d*(N+e)*v*v+d*d*((N-e)**2+4*a0))**2-16*a0*d*d*(v*v+d*(N-e))**2
    H=h8(v)
    assert not (h8(d*t)-d**4*R).data
    assert max(k[5] for k in H.data)==8
    assert {k:v for k,v in H.data.items() if k[5]==8}=={tuple(8 if j==5 else 0 for j in range(dim)):1}
    R4=(d*t*t+d*A-e)**2-4*d*d*A*t*t
    def h4(v):return (v*v+d*d*A-d*e)**2-4*d*d*A*v*v
    H4=h4(v)
    assert not (h4(d*t)-d*d*R4).data
    assert max(k[5] for k in H4.data)==4
    assert {k:v for k,v in H4.data.items() if k[5]==4}=={tuple(4 if j==5 else 0 for j in range(dim)):1}
    # Exact identity for arithmetic in Z[B][sqrt(B)].
    x0,x1,y0,y1,B,r=[var(j) for j in range(6)]
    raw=(x0+x1*r)*(y0+y1*r)-(x0*y0+B*x1*y1+(x0*y1+x1*y0)*r)
    reduced={}
    for k,v in raw.data.items():
        k=list(k);k[4]+=k[5]//2;k[5]%=2;k=tuple(k)
        reduced[k]=reduced.get(k,0)+v
    assert not Poly(reduced).data
    return {'monic_degree8_identity':'exact symbolic pass','monic_degree4_identity':'exact symbolic pass','quadratic_pair_ring_identity':'exact symbolic pass'}

def pair_mul(a,b,B,m):return ((a[0]*b[0]+B*a[1]*b[1])%m,(a[0]*b[1]+a[1]*b[0])%m)
def numeric_norm_checks(p,n=80):
    # Independent Horner evaluation of the monic polynomial at the quadratic
    # pair (W+sqrt(B))/p. Work in finite fields with p invertible.
    rng=random.Random(215);prime=1000000007;done=0
    while done<n:
        vals={x:rng.randrange(1,50) for x in p['witnesses']};vals.update(beta=31,K0=127,MC=10,MF=45)
        vs=evaluate(p,vals,prime)
        if vs['p']==0:continue
        inv=pow(vs['p'],-1,prime);z=(vs['W']*inv%prime,inv);z2=pair_mul(z,z,vs['B'],prime)
        d=vs['d'];A=vs['A'];e=vs['e']
        if len(p['witnesses'])==12:
            N=vs['N'];a0=vs['a0']
            c2=-2*d*(N+e);c0=d*d*((N-e)**2+4*a0)
            vz=pair_mul(z2,z2,vs['B'],prime)
            vz=((vz[0]+c2*z2[0]+c0)%prime,(vz[1]+c2*z2[1])%prime)
            uz=((z2[0]+d*(N-e))%prime,z2[1]);vv=pair_mul(vz,vz,vs['B'],prime);uu=pair_mul(uz,uz,vs['B'],prime)
            hz=((vv[0]-16*a0*d*d*uu[0])%prime,(vv[1]-16*a0*d*d*uu[1])%prime);deg=8
        else:
            uz=((z2[0]+d*d*A-d*e)%prime,z2[1]);uu=pair_mul(uz,uz,vs['B'],prime)
            hz=((uu[0]-4*d*d*A*z2[0])%prime,(uu[1]-4*d*d*A*z2[1])%prime);deg=4
        scale=pow(vs['p'],deg,prime);real=hz[0]*scale%prime;imag=hz[1]*scale%prime
        expected=(real*real-vs['B']*imag*imag)%prime
        actual=(vs['norm_real_square']-vs['B_norm_imag_square'])%prime
        assert expected==actual;done+=1
    return {'field_prime':prime,'independent_pair_horner_cases':done,'passed':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--symbolic',action='store_true');args=parser.parse_args()
    packets=[*construct12(),*construct13()];receipt={}
    for p in packets:
        degrees=degree_bounds(p)
        if 'output' in p:assert degrees[p['output']]==p['exact_degree'],(p['name'],degrees[p['output']],p['exact_degree'])
        else:
            actual=[max(degrees.get(x,0) if isinstance(x,str) else 0 for x in row) for row in p['comparisons']]
            assert actual==p['residual_exact_degrees'],(p['name'],actual,p['residual_exact_degrees'])
        p['degree_upper_by_register']=degrees
        (OUT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        receipt[p['name']]={'ledger':p['ledger'],'degree':p.get('exact_degree',p.get('residual_exact_degrees'))}
        if 'system' in p['name']:receipt[p['name']]['independent_evaluation']=numeric_norm_checks(p)
    if args.symbolic:receipt['symbolic_checks']=symbolic_checks()
    (OUT/'merger_checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
