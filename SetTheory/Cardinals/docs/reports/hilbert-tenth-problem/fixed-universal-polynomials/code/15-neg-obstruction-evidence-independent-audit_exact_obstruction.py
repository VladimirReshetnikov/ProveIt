#!/usr/bin/env python3
"""Independent mathematical and static-data checks. Never imports/executes upstream code or schedules."""
from pathlib import Path
from hashlib import sha256, sha1
import argparse
import json
import sys
from math import comb
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parents[1]

class AuditFailure(RuntimeError):
    """A mathematical, provenance, or frozen-receipt check failed."""


def require(condition, message):
    """Checks remain active under python -O."""
    if not condition:
        raise AuditFailure(message)


def run_checks():
    counts={}

    def tick(name): counts[name]=counts.get(name,0)+1

    def pell(A,n,mod=None):
        # Independent multiplication in Z[sqrt(A^2-1)], binary powering.
        D=A*A-1
        def mul(a,b):
            x=a[0]*b[0]+D*a[1]*b[1]; y=a[0]*b[1]+a[1]*b[0]
            return (x%mod,y%mod) if mod else (x,y)
        z=(1,0); b=(A,1)
        while n:
            if n&1: z=mul(z,b)
            n//=2
            if n: b=mul(b,b)
        return z

    def matmul(a,b,mod):
        return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%mod for i in range(2) for j in range(2))

    def quotient_mod(T2,ell,mod):
        # chi_T(ell)/T is a polynomial in T^2 for odd ell.
        require(ell%2==1 and ell>=1, 'Check failed: ell%2==1 and ell>=1')
        h=(ell-1)//2
        if not h: return 1%mod
        n=h-1; out=(1,0,0,1); base=((4*T2-2)%mod,-1%mod,1,0)
        while n:
            if n&1: out=matmul(out,base,mod)
            n//=2
            if n: base=matmul(base,base,mod)
        return (out[0]*(4*T2-3)+out[1])%mod

    # Authenticate the corrected local snapshots and compare entire objects as data.
    manifest=json.loads((ROOT/'source_manifest.json').read_text())
    for entry in manifest['files']:
        data=(ROOT/'sources'/entry['file']).read_bytes()
        require(len(data)==entry['bytes'], "Check failed: len(data)==entry['bytes']")
        require(sha256(data).hexdigest()==entry['sha256'], "Check failed: sha256(data).hexdigest()==entry['sha256']")
        require(sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==entry['git_blob_sha1'], "Check failed: sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()==entry['git_blob_sha1']")
        tick('source_manifest_byte_and_git_blob_authentication')
    files={}
    for path in sorted((ROOT/'sources').iterdir()):
        b=path.read_bytes();files[path.name]={'sha256':sha256(b).hexdigest(),'bytes':len(b)}
    prior_context = (ROOT/'context/PRIOR-INDEPENDENT-REVIEW.md').read_text(encoding='utf-8')
    prior_hashes = {
        'complete74_nonlinear_index_projection_scout.json': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
        'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
        'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
    }
    # The original audit compared prior and current full JSON objects directly. For
    # portable replay, authenticate those same bytes using the prior audit's recorded
    # hashes, retained in the packet-relative context file.
    for name, digest in prior_hashes.items():
        require(digest in prior_context, 'Check failed: digest in prior_context')
        require(files[name]['sha256'] == digest, "Check failed: files[name]['sha256'] == digest")
        files[name]['prior_sha256'] = digest
        files[name]['matches_prior_sha256'] = True
    now=json.loads((ROOT/'sources/complete74_nonlinear_index_projection_scout.json').read_bytes())
    expected_witnesses={
     'raw30':'C F Jrep W Z a alpha c d delta eta f ga h i j k kappa mu o phi q rho s tau w y_aux zeta zquot'.split(),
     'positive22':'Jrep F alpha zquot f h i j o s w tau eta zeta ga y_aux Z W delta phi rho'.split(),
    }
    expected_comparisons={
     'raw30':[['repunit','qm1'],['raw_bound','q'],['innerC','local_rhs_sum'],['restored_r','r_lhs'],['C','marked_rhs'],['L9','R9'],['c','R10a'],['k','R10b'],['a','R12'],['d','R14'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs'],['kappa','index_rhs'],['c','pell_gap'],['mu2','norm_rhs'],['mu','exponent_rhs']],
     'positive22':[['raw_bound','q'],['innerC','local_rhs_sum'],['restored_r','r_lhs'],['L9','R9'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs'],['R10a','pell_gap'],['mu2','norm_rhs']],
    }
    for form in now['forms']:
        p=form['packet'];mode=p['mode']
        if mode not in expected_witnesses: continue
        require(p['witnesses']==expected_witnesses[mode], "Check failed: p['witnesses']==expected_witnesses[mode]")
        require(p['comparisons']==expected_comparisons[mode], "Check failed: p['comparisons']==expected_comparisons[mode]")
        require(p['polynomial_source'][:len(p['source'])]==p['source'], "Check failed: p['polynomial_source'][:len(p['source'])]==p['source']")
        # Static row comparison, not arithmetic evaluation.
        expected=[]
        for i,(a,b) in enumerate(p['comparisons']):
            expected += [[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
        for i in range(1,len(p['comparisons'])):
            expected.append([f'sum_{i}','+','square_0' if i==1 else f'sum_{i-1}',f'square_{i}'])
        require(p['polynomial_source'][len(p['source']):]==expected, "Check failed: p['polynomial_source'][len(p['source']):]==expected")
        require(p['output']==f"sum_{len(p['comparisons'])-1}", 'Check failed: p[\'output\']==f"sum_{len(p[\'comparisons\'])-1}"')
        tick('literal_witness_comparison_and_full_finalizer_lists')

    # Pure polynomial identity Q_h(1-z)=(-1)^h psi_{sqrt(z)}(2h+1).
    def add(a,b):
        c=[0]*max(len(a),len(b))
        for i,v in enumerate(a):c[i]+=v
        for i,v in enumerate(b):c[i]+=v
        while len(c)>1 and c[-1]==0:c.pop()
        return c

    def linear(a,constant,slope):return add([constant*v for v in a],[0]+[slope*v for v in a])

    def compose_one_minus(a):
        out=[0]*len(a)
        for i,v in enumerate(a):
            for j in range(i+1):out[j]+=v*comb(i,j)*(-1)**j
        return out

    Q0,Q1=[1],[-3,4]
    S0,S1=[1],[-1,4]
    for h in range(0,61):
        if h==0:Q,S=Q0,S0
        elif h==1:Q,S=Q1,S1
        else:
            Q=add(linear(Q1,-2,4),[-v for v in Q0]);Q0,Q1=Q1,Q
            S=add(linear(S1,-2,4),[-v for v in S0]);S0,S1=S1,S
        require(compose_one_minus(Q)==[(-1)**h*v for v in S], 'Check failed: compose_one_minus(Q)==[(-1)**h*v for v in S]')
        require(Q[0]==(-1)**h*(2*h+1), 'Check failed: Q[0]==(-1)**h*(2*h+1)')
        tick('exact_odd_quotient_polynomial_identities')

    # Main/input congruences and positivity of recovered ga and rho whenever a small marker matches.
    for A in range(4,44,2):
        a=A-2;Delta=A*A-1;H=4*a+3
        for r in range(1,82):
            chi,psi=pell(A,r)
            prev=pell(A,r-1)[1]
            require(chi-a*psi==2*psi-prev, 'Check failed: chi-a*psi==2*psi-prev')
            require(chi-a*psi>psi, 'Check failed: chi-a*psi>psi')
            require((chi-a*psi-pow(2,r,H))%H==0, 'Check failed: (chi-a*psi-pow(2,r,H))%H==0')
            require(psi%Delta==(r if r%2 else r*A)%Delta, 'Check failed: psi%Delta==(r if r%2 else r*A)%Delta')
            if r>=3:require(psi>=4*A*A-1, 'Check failed: psi>=4*A*A-1')
            tick('main_input_projection_discriminant_and_growth')
        for u in range(3,20,2):
            for e in (u,u*A):
                kappa=pell(A,e)[1]
                require(kappa>u and (kappa-u)%Delta==0, 'Check failed: kappa>u and (kappa-u)%Delta==0')
                tick('positive_integral_delta_both_input_branches')

    # Aux divisibility and sign for many p; no giant Pell number required here.
    for A in range(2,32,2):
        for p in range(3,34,2):
            c=pell(A,p)[1];m=c*p if p%4==3 else 2*c*p;ell=p+2*m
            require(c%2==1 and ell%4==1, 'Check failed: c%2==1 and ell%4==1')
            require(pell(A,m,c*c)[1]==0, 'Check failed: pell(A,m,c*c)[1]==0')
            require(quotient_mod(0,ell,c)==p%c, 'Check failed: quotient_mod(0,ell,c)==p%c')
            tick('auxiliary_divisibility_and_positive_sign')

    # Larger modular completions retain the full f but avoid astronomical U,y.
    for A,p in [(2,3),(3,3),(4,3),(2,5),(2,7),(4,5)]:
        Delta=A*A-1;c=pell(A,p)[1];m=c*p if p%4==3 else 2*c*p;ell=p+2*m
        f,psim=pell(A,m);T=Delta*psim
        require(T%(c*c)==0 and T>=c*c, 'Check failed: T%(c*c)==0 and T>=c*c')
        require(T*T==Delta*(f*f-1), 'Check failed: T*T==Delta*(f*f-1)')
        require(ell%4==1, 'Check failed: ell%4==1')
        require(quotient_mod(T*T%f,ell,f)==(-c)%f, 'Check failed: quotient_mod(T*T%f,ell,f)==(-c)%f')
        require(pell(A,ell,f)[1]==(-c)%f, 'Check failed: pell(A,ell,f)[1]==(-c)%f')
        require(quotient_mod(T*T%c,ell,c)==p%c, 'Check failed: quotient_mod(T*T%c,ell,c)==p%c')
        tick('auxiliary_full_f_modular_completion')

    # Materialize small auxiliary-only tuples and directly check the four equations.
    aux=[]
    for A,p in [(2,3),(3,3),(4,3)]:
        Delta=A*A-1;c=pell(A,p)[1];m=c*p;ell=p+2*m
        f,psim=pell(A,m);T=Delta*psim;i=T//(c*c)
        TU,y=pell(T,ell);require(TU%T==0, 'Check failed: TU%T==0');U=TU//T
        require((U-p)%c==0 and (U+c)%f==0, 'Check failed: (U-p)%c==0 and (U+c)%f==0')
        j=(U-p)//c;o=(U+c)//f
        require(min(f,T,i,U,y,j,o)>0, 'Check failed: min(f,T,i,U,y,j,o)>0')
        require(T==i*c*c, 'Check failed: T==i*c*c')
        require(T*T==Delta*(f*f-1), 'Check failed: T*T==Delta*(f*f-1)')
        require(T*T*(U*U-y*y)==1-y*y, 'Check failed: T*T*(U*U-y*y)==1-y*y')
        require(U==j*c+p==o*f-c, 'Check failed: U==j*c+p==o*f-c')
        aux.append({'A':A,'p':p,'c':c,'m':m,'ell':ell,'U_bits':U.bit_length()})
        tick('auxiliary_entire_positive_tuple')

    # Check ceil/floor and parity boundaries independently of huge scale values.
    for T in range(2,260,2):
        lo=(T+2)//3+1;hi=(T-6)//2
        for p in range(1,140,2):
            n=(T+1-p)//2
            require((lo<=p<=hi)==(2*p+6<=T<=3*p-3), 'Check failed: (lo<=p<=hi)==(2*p+6<=T<=3*p-3)')
            if lo<=p<=hi:require(n<p<2*n and 2*n-p>=7, 'Check failed: n<p<2*n and 2*n-p>=7')
            tick('representative_interval_boundary')

    # Deterministic outer reconstruction for synthetic arithmetic data, no compiler/full-zero claim.
    for B in (16,32):
        for J in range(1,14,2):
            q=(B-1)*J+1;Q=q*q-1
            for MC in (1,B-2):
                for MF0 in (1,B-2):
                    M=(MC+q*(MF0+B-1))*J
                    for Fval in (q-1,q,q+1,2*q):
                        for Z in (1,2,q-1):
                            R=(q*q-Z-q*Fval)*Q+M
                            if R>=0:continue
                            p=-R;N=(p+M)//Q;zz=N%q;ff=q+(N-zz)//q
                            require((p+M)%Q==0 and (zz,ff)==(Z,Fval), 'Check failed: (p+M)%Q==0 and (zz,ff)==(Z,Fval)')
                            require(Fval>=q, 'Check failed: Fval>=q')
                            if Fval==q:require(Z>=2, 'Check failed: Z>=2')
                            tick('negative_packing_recovery_and_boundary')

    # Exact rational Binet envelopes; these are not full-zero or representative fixtures.
    for q in (16,46,76):
        for w in (1,2,5):
            for s in (1,2,7):
                X=w*q**3;Y=s*q**3;A=Y*(X+1)+2;P=2*X*Y*Y+1
                amin=2*A-F(1,A);amax=2*A-F(1,2*A)
                bmin=2*P-F(1,P);bmax=2*P-F(1,2*P)
                rmin=F(P*P-1,2*A*P)*(1-F(1,(2*A-1)**26))
                rmax=F(P*A,2*(A*A-1))/(1-F(1,(2*P-1)**14))
                require(P>A, 'Check failed: P>A')
                for p in (13,15,21):
                    for n in ((p+7)//2,p-1):
                        ratio=F(pell(A,p)[1],2*pell(P,n)[1])
                        require(rmin*amin**p/bmax**n < ratio < rmax*amax**p/bmin**n, 'Check failed: rmin*amin**p/bmax**n < ratio < rmax*amax**p/bmin**n')
                        # Rigorous logarithmic error majorants using log(1+z)<z.
                        square_error=F(1,A*A-1)+F(1,P*P-1)
                        tails=2*F(1,(2*A-1)**26)+2*F(1,(2*P-1)**14)
                        require(square_error<F(3,A*A) and tails<F(1,A*A), 'Check failed: square_error<F(3,A*A) and tails<F(1,A*A)')
                        error_bound=F(p,4*A*A-2)+F(n,4*P*P-2)+square_error+tails
                        require(error_bound<F(p,A*A), 'Check failed: error_bound<F(p,A*A)')
                        tick('exact_rational_binet_and_log_error_bounds')
                E=X*Y
                for t in (1,2,3*q//s):
                    lo=max(13,(t*E+2)//3+1);hi=min(X*q**4-1,(t*E-6)//2)
                    if lo>hi:continue
                    for p in (lo,hi):
                        n=F(t*E+1-p,2)
                        require(7<=n<p, 'Check failed: 7<=n<p')
                        require(F(p+n,3)+4<p, 'Check failed: F(p+n,3)+4<p')
                        require(F(p,A*A)<F(1,X*q*q)<=F(1,q**5), 'Check failed: F(p,A*A)<F(1,X*q*q)<=F(1,q**5)')
                        tick('representative_uniform_subunit_error_bounds')

    # Wrapped/unwrapped thresholds, including both one-unit boundaries.
    for u in range(3,20,2):
        for q in range(2,25,2):
            for s in range(1,5):
                for w in range(1,5):
                    H=4*s*w*q**6+4*s*q**3+3
                    wrapped=H<=2**u
                    require(wrapped==(4*s*w*q**6+4*s*q**3+4<=2**u), 'Check failed: wrapped==(4*s*w*q**6+4*s*q**3+4<=2**u)')
                    bound=(2**u-4*s*q**3-4)//(4*s*q**6)
                    require(wrapped==(w<=bound), 'Check failed: wrapped==(w<=bound)')
                    if wrapped:require(4*q**6<2**u, 'Check failed: 4*q**6<2**u')
                    else:require(pow(2,u,H)==2**u, 'Check failed: pow(2,u,H)==2**u')
                    tick('wrapped_odd_thresholds')

    result={'scope':'Static upstream data inspection only; newly written exact mathematical checks, no upstream modules or arithmetic schedules executed; no full compiler zero search.', 'counts':counts,'files':files,'auxiliary_only_fixtures':aux,'prior_receipt_sha256_matches':True}
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Write the deterministic receipt outside the packet; default is stdout only")
    parser.add_argument("--expect", type=Path,
                        help="Require a byte-exact match with this frozen JSON receipt")
    args = parser.parse_args()
    if args.output is not None:
        target = args.output.resolve()
        require(not target.is_relative_to(ROOT), "--output must be outside the packet")
        require(args.expect is None or target != args.expect.resolve(),
                "--output must not overwrite the frozen --expect receipt")
    result = run_checks()
    rendered = (json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")
    if args.expect is not None:
        require(args.expect.read_bytes() == rendered,
                "Generated receipt differs from the frozen --expect receipt")
    if args.output is not None:
        args.output.write_bytes(rendered)
    sys.stdout.buffer.write(rendered)


if __name__ == "__main__":
    main()
