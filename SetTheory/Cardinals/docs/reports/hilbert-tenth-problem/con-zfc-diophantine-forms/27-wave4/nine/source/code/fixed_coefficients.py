"""Modular fingerprints of the *actual fixed* T4 coefficient tuple.

No enormous integer is expanded. All exponents here are fixed natural
numbers. Horner evaluation works for arbitrary moduli, including even
ones, without assuming that the radix has an inverse.
"""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def pow_sum(base,n,mod):
    """Return (base**n, sum(base**j for j<n)), modulo mod, without division."""
    if mod<1 or n<0:
        raise ValueError('positive modulus and nonnegative exponent required')
    result_power,result_sum=1%mod,0
    block_power,block_sum=base%mod,1%mod
    while n:
        if n&1:
            result_sum=(result_sum+result_power*block_sum)%mod
            result_power=result_power*block_power%mod
        block_sum=block_sum*(1+block_power)%mod
        block_power=block_power*block_power%mod
        n//=2
    return result_power,result_sum

def t4_ports(mod,windows=None):
    if mod<1:
        raise ValueError('positive modulus required')
    if windows is None:
        windows=json.loads((ROOT/'coefficients/t4_windows.json').read_text())
    if len(windows)!=37075:
        raise ValueError('wrong T4 tile count')
    rho=pow(2,390625,mod)
    A=65536%mod
    B=pow(2,5**18,mod)
    ap=[1%mod]
    for _ in range(1760):
        ap.append(ap[-1]*A%mod)
    anchors=[43661,130983,392949,1178847]
    offsets=[40587,40148,39709,38831]
    emax=1178847
    common=sum(ap[1756+t] for t in range(1,5))+1
    horner=0
    for row in windows:
        val=common+sum(ap[1+439*j+symbol] for j,symbol in enumerate(row))
        horner=(horner*rho+val)%mod
    packed=horner*pow(rho,emax-len(windows)+1,mod)%mod
    for j,offset in enumerate(offsets):
        horner=0
        for u in range(439):
            horner=(horner*rho+ap[1+439*j+u])%mod
        packed=(packed+horner*pow(rho,emax-offset-438,mod))%mod
    for t,e in enumerate(anchors,1):
        packed=(packed+ap[1756+t]*pow(rho,emax-e,mod))%mod
    # The dummy's clause coefficient is zero.
    dc=(sum(pow(rho,e,mod) for e in (1317,2228468,349288,1047864))+
        packed*(pow(rho,4586163-emax,mod)+pow(rho,6943861-emax,mod)))%mod
    dr=pow(rho,2228029,mod)
    selector_sum=pow_sum(rho,37075,mod)[1]
    copy_geom=pow_sum(rho,439,mod)[1]
    copy_sum=copy_geom*sum(pow(rho,e,mod) for e in offsets)
    support_sum=(selector_sum+copy_sum+pow(rho,42343,mod)+
                 sum(pow(rho,e,mod) for e in anchors))%mod
    mc=(B-1-support_sum+rho-2*pow(rho,42343,mod))%mod
    mu=(A-2+A*pow_sum(A,18743,mod)[1])%mod
    mf0=(mu*(pow(rho,4586163,mod)+pow(rho,6943861,mod))+
         copy_geom*(pow(rho,40148,mod)+pow(rho,2228029+40587,mod)+
                    pow(rho,2228029+40148,mod))+
         pow(rho,392949,mod)+pow(rho,1178847,mod))%mod
    return {'beta':(B-1)%mod,'K0':(dc+B*dr)%mod,'MC':mc,'MF':(mf0+4+B-1)%mod}

def direct_t4_ports(mod,windows):
    """Slow independent transcription of the finite sums, for verification."""
    rho=pow(2,390625,mod); A=65536%mod; B=pow(2,5**18,mod)
    coeff={}
    for i,row in enumerate(windows):
        coeff[i]=(1+sum(pow(A,1+439*j+s,mod) for j,s in enumerate(row))+
                  sum(pow(A,1756+t,mod) for t in range(1,5)))%mod
    for j,offset in enumerate([40587,40148,39709,38831]):
        for u in range(439):
            coeff[offset+u]=pow(A,1+439*j+u,mod)
    for t,e in enumerate([43661,130983,392949,1178847],1):
        coeff[e]=pow(A,1756+t,mod)
    coeff[42343]=0
    dc=(sum(pow(rho,e,mod) for e in [1317,2228468,349288,1047864])+
        sum(v*(pow(rho,4586163-e,mod)+pow(rho,6943861-e,mod)) for e,v in coeff.items()))%mod
    dr=pow(rho,2228029,mod)
    mu=(A-2+sum(pow(A,j,mod) for j in range(1,18744)))%mod
    mf0=(mu*(pow(rho,4586163,mod)+pow(rho,6943861,mod))+
         sum(pow(rho,40148+u,mod) for u in range(439))+
         sum(pow(rho,2228029+40587+u,mod)+pow(rho,2228029+40148+u,mod) for u in range(439))+
         pow(rho,392949,mod)+pow(rho,1178847,mod))%mod
    mc=(B-1-sum(pow(rho,e,mod) for e in coeff if e!=1)-2*pow(rho,42343,mod))%mod
    return {'beta':(B-1)%mod,'K0':(dc+B*dr)%mod,'MC':mc,'MF':(mf0+4+B-1)%mod}

def main():
    path=ROOT/'coefficients/t4_windows.json'
    windows=json.loads(path.read_text())
    expected='9c2e473b5dbc5b3dc1468a31aefdbec6a901d6ba1e6b1ec9212698d41e1d84b1'
    require(hashlib.sha256(path.read_bytes()).hexdigest()==expected, 'Wrong ordered tile hash')
    results=[]
    for m in [16,100,101,1009,1000003]:
        fast=t4_ports(m,windows)
        slow=direct_t4_ports(m,windows)
        require(fast==slow, 'Fast and direct fixed coefficients differ')
        results.append({'modulus':m,'ports':fast})
    for b in range(-3,7):
        for n in range(30):
            require(pow_sum(b,n,97)==(pow(b,n,97),sum(b**j for j in range(n))%97),
                    'Geometric sum identity failed')
    receipt={'status':'PASS','fixed_port_fingerprints':results,
             'ordered_tile_sha256':expected,'geometric_sum_checks':300,
             'scope':'Exact residues of the actual fixed coefficients; no coefficient expansion and no solvability claim.'}
    (ROOT/'verification/fixed_coefficients.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
