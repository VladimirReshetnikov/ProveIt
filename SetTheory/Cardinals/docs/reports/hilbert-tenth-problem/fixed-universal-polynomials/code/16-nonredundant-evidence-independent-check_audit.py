#!/usr/bin/env python3
"""Portable exact audit; requires Python 3 and SymPy (tested with SymPy 1.14.0).

Default: canonical JSON on stdout; no writes. --expect compares frozen bytes.
--output creates a NEW file outside this packet. No upstream code is executed.
Importing this module performs no checks, imports no SymPy, and writes no files.
Finite fixtures are subsystem corroboration, never infinite-existence evidence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys


def require(condition, message='Independent audit check failed'):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_receipt():
    import sympy as sp
    HERE = Path(__file__).resolve().parent
    ROOT = HERE.parent
    # Added follow-on context is authenticated as inert bytes, never imported.
    context_pins={
     'Report37.snapshot.tex':'57d6598d60389b2fc283f89f47b29ef5905af259ebe0ea69433a8838f9749001',
     'compiler.snapshot.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
     'complete77.snapshot.py':'9222a13dc180bd2361877674c4bd957d18f2d9aef827852cf5d320a3d7ac7d7a',
     'projection.snapshot.json':'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
    }
    for name,digest in context_pins.items():
        require(sha(ROOT/'context'/name)==digest)
    materializer=(ROOT/'context/complete77.snapshot.py').read_text()
    require('return self.B-1-sum(1<<(self.radix_bits*e) for e in self.positions if e!=1)' in materializer)
    require('old_positions=tuple(range(k))+tuple(payload.values())+dummy' in materializer)
    require('assert k>=2' in materializer)

    # Algebraic identity for the analytic remainder; epsilon functions are represented
    # by arbitrary symbols. Divisibility by z in their actual values is proved in review.
    z,v,Y,a0,ea,eb,ek,delta = sp.symbols('z v Y a0 ea eb ek delta')
    d = 2*ea+eb
    l = (1/v-4*a0)/3
    f_exact = ((Y/z+1)*(l+2*a0+eb)+2*(delta-ek))/(3*l+4*a0+d)
    G = (2*a0/3 + sp.Rational(2,3)*(Y/z+1)*(eb-ea) + 2*(delta-ek)
         - sp.Rational(2,3)*Y*a0*v*d/z)/(1+v*d)
    f_split = Y/(3*z)+sp.Rational(2,3)*Y*a0*v/z+sp.Rational(1,3)+v*G
    require(sp.cancel(f_exact-f_split)==0)
    X=sp.symbols('X',positive=True)
    D0=3*sp.log(X)+4*a0
    explicit=sp.Rational(2,3)*Y*a0*X/D0
    require(sp.simplify(sp.diff(explicit,X,2) + 2*Y*a0/(X*D0**2)*(1-6/D0))==0)

    q,K,W,r,j,M=sp.symbols('q K W r j M')
    Q=q*q-1; L0=q*(q-1)*Q; C=W+1; Xr=q**3*(1+(q-1)*r)
    P0=Q*((1+q*(K+q**3))*C-q*q-W)-M
    p=P0+L0*j
    N=sp.cancel((p+M)/Q)
    F=sp.cancel((N-1+q*q)/q)
    zquot=sp.cancel(((K+Xr)*C-F)/(q-1))
    require(sp.expand(F-((K+q**3)*C+(q-1)*j))==0)
    require(sp.expand(zquot-(q**3*r*C-j))==0)
    require(sp.expand(-p-((q*q-1-q*F)*Q+M))==0)
    require(sp.expand(Q*((1+q*(K+Xr))*C-q*q-W)-M-P0-L0*q**3*C*r)==0)
    D,R=sp.symbols('D R')
    require(sp.expand((D-R)**2-D**2+R*(2*D-R))==0)

    # Static source inventories and SOS suffixes. We compare records as data; we do
    # not interpret/evaluate the source schedule or import any upstream module.
    scout=json.loads((ROOT/'context/projection.snapshot.json').read_text())
    source_checks={}
    for form in scout['forms']:
        packet=form['packet']; mode=packet['mode']
        if mode not in ('raw30','positive22'): continue
        source=packet['source']; poly=packet['polynomial_source']; comps=packet['comparisons']; n=len(comps)
        expected=[]
        for i,(left,right) in enumerate(comps):
            expected += [[f'residual_{i}','-',left,right], [f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
        expected += [['sum_1','+','square_0','square_1']]
        expected += [[f'sum_{i}','+',f'sum_{i-1}',f'square_{i}'] for i in range(2,n)]
        require(poly == source+expected)
        require(packet['output']==f'sum_{n-1}')
        require(len(packet['witnesses']) == (29 if mode=='raw30' else 21))
        # Dependency closure only, not mathematical evaluation of any register.
        depends={'ga'}
        for dest,op,left,right in source:
            if left in depends or right in depends: depends.add(dest)
        affected=[i for i,(left,right) in enumerate(comps) if left in depends or right in depends]
        require(affected==([9] if mode=='raw30' else [4]))
        source_checks[mode]={'witnesses':len(packet['witnesses']),'comparisons':n,
                            'ga_affected_comparisons':affected,'complete_sos_suffix':True}

    # Exact elementary compiler-bound and lattice fixtures. These are abstract
    # contract-compatible numeral fixtures, NOT actual compiled machines.
    fixtures=0
    for dcell,b in [(5,5),(25,5),(25,25),(125,5)]:
        B=1<<dcell
        for x in (1,2,3,5):
            u=2*dcell*x+b; Wn=1<<u; qn=B**(2*x+2)
            require(qn>=Wn+u-b+2 and qn%2==0 and qn%3!=0 and (qn-1)%(B-1)==0)
            J=(qn-1)//(B-1); Qn=qn*qn-1; Ln=qn*(qn-1)*Qn; Cn=Wn+1
            for MC in (2,6,B-2):
                MFsrc=4+B-1; Kn=B*B-1; Mn=(MC+qn*MFsrc)*J
                Pn=Qn*((1+qn*(Kn+qn**3))*Cn-qn*qn-Wn)-Mn
                pn0=Pn%Ln
                require(pn0%2==1 and pn0%4==1)
                for rn in (1,2,10):
                    Xn=qn**3*(1+(qn-1)*rn)
                    for kn in (0,1,11):
                        pn=pn0+Ln*kn
                        require((pn+Mn)%Qn==0)
                        Nn=(pn+Mn)//Qn
                        require(Nn%qn==1)
                        Fn=(Nn-1+qn*qn)//qn
                        require(((Kn+Xn)*Cn-Fn)%(qn-1)==0)
                        require(-pn==(qn*qn-1-qn*Fn)*Qn+Mn)
                        fixtures+=1

    # Own Pell arithmetic with pair multiplication/powering, no saved schedule.
    def pell(V,n,mod=None):
        def mul(a,b):
            c=(a[0]*b[0]+(V*V-1)*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
            return tuple(t%mod for t in c) if mod else c
        out=(1,0); base=(V,1)
        while n:
            if n&1: out=mul(out,base)
            base=mul(base,base); n//=2
        return out
    aux_cases=0
    # p>=13, p==1 mod4 fixtures: testing c² divisibility and the U congruence modulo c
    # is small with modular powering. The other congruence is proved symbolically.
    for A in (2,4,6,10,20):
        for pn in (13,17,21,25):
            Dn,cn=pell(A,pn); mn=2*cn*pn; ell=pn+2*mn
            require(cn%2==1 and ell%4==1 and mn%cn==0)
            require(pell(A,mn,cn*cn)[1]==0)
            # For T divisible by c, chi_T(ell)/T has constant coefficient +ell.
            # Validate its polynomial identity independently for modest odd ell below.
            aux_cases+=1
    T,A=sp.symbols('T A')
    polynomial_cases=0
    for ell in range(1,50,2):
        h=(ell-1)//2
        quotient=sp.cancel(sp.chebyshevt(ell,T)/T)
        require(sp.Poly(quotient,T).coeff_monomial(1)==(-1)**h*ell)
        polynomial=sp.Poly(quotient,T)
        substituted=sum(coeff*(1-A*A)**(mon[0]//2) for mon,coeff in polynomial.terms())
        require(sp.expand(substituted-(-1)**h*sp.chebyshevu(ell-1,A))==0)
        polynomial_cases+=1


    return {
     'schema':'unwrapped-family-independent-audit-v1',
     'status':'all exact checks passed',
     'dependencies':['Python 3','SymPy'],
     'candidate_sha256':sha(ROOT/'ALL-BUT-MAIN-PROJECTION.md'),
     'author_checker_sha256':sha(ROOT/'check_unwrapped_family.py'),
     'independent_review_sha256':sha(HERE/'INDEPENDENT-REVIEW.md'),
     'independent_checker_sha256':sha(Path(__file__)),
     'portable_context_pins_checked':context_pins,
     'historical_evidence':{
       'file':'historical_audit_receipt.json',
       'sha256':sha(HERE/'historical_audit_receipt.json'),
       'scope':'Original five-source authentication and 43-file sealed-tree unchanged check; historical only, not re-executed by this portable checker',
     },
     'symbolic_remainder_identity':True,
     'symbolic_curvature_identity':True,
     'symbolic_lattice_and_residual_identities':True,
     'source_static_inventory':source_checks,
     'abstract_bound_lattice_fixtures':fixtures,
     'p_1_mod_4_large_index_modular_auxiliary_fixtures':aux_cases,
     'odd_quotient_polynomial_identities':polynomial_cases,
     'finite_evidence_scope':'subsystem corroboration only; no actual-compiler candidate or full zero materialized',
     'execution_boundary':'own checker only; upstream modules and saved schedules neither imported nor executed',
    }


def canonical_bytes(receipt):
    return (json.dumps(receipt, sort_keys=True, indent=2, ensure_ascii=True)+'\n').encode('utf-8')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expect', type=Path, help='Require exact equality with frozen canonical JSON bytes')
    parser.add_argument('--output', type=Path, help='Create a new receipt file outside the packet; otherwise use stdout')
    args=parser.parse_args(argv)
    try:
        packet=Path(__file__).resolve().parent.parent
        output=args.output.resolve() if args.output is not None else None
        if output is not None:
            require(not output.is_relative_to(packet), 'Output must be outside the packet')
            require(not output.exists(), 'Output must be a new file')
            if args.expect is not None:
                require(output!=args.expect.resolve(), 'Output cannot replace the expected receipt')
        data=canonical_bytes(build_receipt())
        if args.expect is not None:
            require(args.expect.read_bytes()==data, 'Frozen receipt byte mismatch')
        if output is None:
            sys.stdout.buffer.write(data)
        else:
            with output.open('xb') as stream:
                stream.write(data)
        return 0
    except Exception as error:
        print(f'audit failed: {error}', file=sys.stderr)
        return 1


if __name__=='__main__':
    raise SystemExit(main())
