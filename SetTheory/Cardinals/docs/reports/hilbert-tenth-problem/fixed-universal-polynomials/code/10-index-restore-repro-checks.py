"""New stdlib-only, bounded checks. Load only after verify.py's identity gate.

Pinned source schedules are compared as JSON data, never evaluated or imported.
No assertions: every condition is checked in ordinary and optimized Python.
"""
import hashlib
import json
from math import gcd, lcm, prod

COMMIT = '2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff'
PROOF_SHA256 = 'b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd'

class CheckFailure(Exception):
    pass

def require(condition, message):
    if condition is not True:
        raise CheckFailure(message)

def exact(a, b):
    """Recursive JSON equality with no bool/int or int/float coercion."""
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CheckFailure('Duplicate JSON key: ' + key)
        result[key] = value
    return result

def reject_constant(value):
    raise CheckFailure('Non-finite JSON constant: ' + value)

def read_json(raw):
    return json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                      parse_constant=reject_constant)

def canonical(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True,
                       allow_nan=False) + '\n').encode('utf-8')

def sha256(raw):
    return hashlib.sha256(raw).hexdigest()

def source_checks(files):
    manifest = read_json(files['source_manifest.json'])
    require(type(manifest) is list and len(manifest) == 16, 'source manifest length')
    seen = set()
    for row in manifest:
        name = row['path']
        require(type(name) is str and name.startswith('sources/'), 'source name')
        require(name not in seen, 'duplicate source path')
        seen.add(name)
        raw = files[name]
        require(sha256(raw) == row['sha256'], 'source SHA256: ' + name)
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(blob == row['sha'] == row['git_blob_calculated'], 'Git blob: ' + name)
        url = row.get('url', row.get('display_url'))
        require(type(url) is str and url.startswith(
            'https://github.com/VladimirReshetnikov/ProveIt/blob/' + COMMIT + '/'),
            'commit-pinned source URL: ' + name)
    require(sha256(files['evidence/FULL-SIGNED-COUNTEREXAMPLE.md']) == PROOF_SHA256,
            'reviewed proof identity')
    audit = files['evidence/INDEPENDENT-AUDIT.md'].decode('utf-8')
    require(PROOF_SHA256 in audit and '**PASS.**' in audit, 'audit/proof binding')
    provenance = read_json(files['evidence/provenance.json'])
    for row in provenance['files']:
        require(sha256(files[row['packaged_path']]) == row['packaged_sha256'],
                'packaged evidence provenance')
        require(type(row['byte_identical']) is bool, 'byte-identical flag type')
        if row['byte_identical']:
            require(row['original_sha256'] == row['packaged_sha256'], 'original hash')
    return {'source_files': len(seen), 'sha256_matches': len(seen),
            'git_blob_sha1_matches': len(seen), 'commit': COMMIT,
            'reviewed_proof_sha256': PROOF_SHA256,
            'evidence_files': len(provenance['files']),
            'executable_upstream_sources_executed': False}

def data_schedule_checks(files):
    parent = read_json(files['sources/complete74_factored_first_norm.json'])
    child = read_json(files['sources/complete74_nonlinear_index_projection_scout.json'])
    parents = {f['packet']['mode']: f['packet'] for f in parent['forms']}
    children = {f['packet']['mode']: f['packet'] for f in child['forms']}
    require(set(parents) == set(children) == {'raw30', 'positive22', 'signed20'},
            'three source forms')
    rows = []
    for mode in ['raw30', 'positive22', 'signed20']:
        p, c = parents[mode], children[mode]
        require(exact(c['witnesses'], [w for w in p['witnesses'] if w != 'r']),
                'deleted witness only: ' + mode)
        actual_k = 'k' if mode == 'raw30' else 'R10b'
        expected = []
        for gate in p['source']:
            if gate[0] in ['r1', 'R11']:
                continue
            expected.append([gate[0], gate[1]] + [
                'restored_r' if type(arg) is str and arg == 'r' else arg
                for arg in gate[2:]])
        by_name = {gate[0]: gate for gate in c['source']}
        require(len(by_name) == len(c['source']), 'unique gate outputs')
        require(exact(by_name['index_partial'], ['index_partial', '-', actual_k, 'hpm1']),
                'index_partial data')
        require(exact(by_name['restored_r'], ['restored_r', '-', 'index_partial', 1]),
                'restored_r data')
        retained = [gate for gate in c['source'] if gate[0] not in ['index_partial','restored_r']]
        require(exact(retained, expected), 'literal 72-gate transfer: ' + mode)
        expected_comparisons = []
        for pair in p['comparisons']:
            if exact(pair, [actual_k, 'R11']):
                continue
            expected_comparisons.append(['restored_r' if item == 'r' else item for item in pair])
        require(exact(c['comparisons'], expected_comparisons), 'residual transfer')
        # Count operation labels, but never assign arithmetic values to source gates.
        for packet in [p, c]:
            for source_key, ledger_key in [('source','certificate_ledger'),
                                           ('polynomial_source','polynomial_ledger')]:
                gates, ledger = packet[source_key], packet[ledger_key]
                additions = sum(g[1] in ['+', '-'] for g in gates)
                multiplications = sum(g[1] == '*' for g in gates)
                require(exact([additions, multiplications, len(gates)],
                              [ledger['A'], ledger['M'], ledger['operations']]),
                        'literal operation-label count: ' + mode)
                require(additions + multiplications == len(gates), 'known gate labels')
        rows.append({'mode': mode, 'parent_witnesses': len(p['witnesses']),
                     'child_witnesses': len(c['witnesses']),
                     'parent_residuals': len(p['comparisons']),
                     'child_residuals': len(c['comparisons']),
                     'unchanged_or_substituted_gates': len(retained),
                     'parent_polynomial_operations': p['polynomial_ledger']['operations'],
                     'child_polynomial_operations': c['polynomial_ledger']['operations'],
                     'child_polynomial_additions_subtractions': c['polynomial_ledger']['A'],
                     'child_polynomial_multiplications': c['polynomial_ledger']['M']})
    signed = children['signed20']
    require(exact(signed['comparisons'], [
        ['innerC','local_rhs_sum'], ['restored_r','r_lhs'], ['L9','R9'], ['L15','R15'],
        ['ic22','R16'], ['L17','P17'], ['H17','aux_u_rhs'], ['mu2','norm_rhs']]),
        'signed19 eight-residual interface')
    require(exact(signed['witnesses'], ['Jrep','F','alpha','zquot','f','h','i','j','o',
        's','w','tau','eta','zeta','y_aux','Z','delta','rho','sigma']), 'signed19 coordinates')
    return {'scope': 'Literal data comparison and label counts only; no schedule execution',
            'forms': rows, 'signed19_residuals': signed['comparisons']}

def certify(node, seen, count):
    """Full Lucas n-1 criterion, recursively certifying every prime factor."""
    require(type(node) is dict and type(node.get('n')) is int, 'certificate node/n type')
    n = node['n']
    count[0] += 1
    seen.add(n)
    if n == 2:
        require(exact(node, {'n': 2}), 'base prime node')
        return n
    require(set(node) == {'n','a','factors','children'}, 'certificate exact keys')
    require(n > 2 and n % 2 == 1, 'candidate odd integer')
    a, factors, children = node['a'], node['factors'], node['children']
    require(type(a) is int and 1 < a < n, 'Lucas base')
    require(type(factors) is list and type(children) is list and
            len(factors) == len(children) and len(factors) > 0, 'factor children count')
    primes = []
    product = 1
    for pair, sub in zip(factors, children):
        require(type(pair) is list and len(pair) == 2 and
                all(type(v) is int for v in pair), 'factor pair exact integer types')
        p, e = pair
        require(2 <= p < n and 1 <= e <= n.bit_length(), 'factor/exponent range')
        require(p not in primes, 'distinct prime factors')
        require(certify(sub, seen, count) == p, 'child matches prime factor')
        primes.append(p)
        product *= p ** e
    require(product == n - 1, 'complete n-1 factorization')
    require(pow(a, n-1, n) == 1, 'Lucas full exponent')
    for p in primes:
        require(gcd(pow(a, (n-1)//p, n) - 1, n) == 1, 'Lucas factor gcd')
    return n

def pell(A, n, modulus=None):
    """Binary exponentiation of pairs in Z[sqrt(A^2-1)], exact or modular."""
    require(type(A) is int and type(n) is int and n >= 0, 'Pell input types/range')
    delta = A*A - 1
    def multiply(u, v):
        x = u[0]*v[0] + delta*u[1]*v[1]
        y = u[0]*v[1] + u[1]*v[0]
        return (x, y) if modulus is None else (x % modulus, y % modulus)
    value, base = (1, 0), (A, 1)
    while n:
        if n & 1:
            value = multiply(value, base)
        n >>= 1
        if n:
            base = multiply(base, base)
    return value

def crt(a, m, b, n):
    require(gcd(m,n) == 1, 'CRT coprimality')
    return (a + m * (((b-a)*pow(m,-1,n)) % n)) % (m*n)

def outer_checks(files):
    cert = read_json(files['evidence/prime-certificate.json'])
    seen, count = set(), [0]
    ell = certify(cert, seen, count)
    d=t=5
    q=B=2**t
    p0=12*t+7
    X=2**p0
    Q=q*q-1
    require((4*q**3*(X+1)) % 3 == 0, 'D0 divisibility')
    D0=4*q**3*(X+1)//3
    s0=2
    s=s0+27*Q
    require(ell == 1+D0*s, 'certificate/progression prime equality')
    require(gcd(D0,Q) == gcd(s0,Q) == gcd(1+D0*s0,Q) == 1, 'primitive prime progression')
    Y=s*q**3
    E=X*Y
    a=Y*(X+1)
    A=a+2
    H=4*a+3
    Delta=A*A-1
    P=2*X*Y*Y+1
    require(H == 3*ell and ell % 3 == 2, 'prime scale shape')
    require(gcd(Q*H,2*E) == gcd(Q*H,2*(ell-1)) == 1, 'order multiple coprimality')
    require(Delta % 2 == 1, 'odd main discriminant')
    v2=lambda v: (v & -v).bit_length()-1
    require(v2(P*P-1) == 2+p0+2*v2(Y) and v2(P*P-1) % 2 == 1,
            'distinct-field squarefree parity fixture')
    # Start from a proven exponent multiple; factorization comes from the certificate.
    order_factors={p:e for p,e in cert['factors']}
    order_factors[2] = order_factors.get(2,0)+1
    O=2*(ell-1)
    require(prod(p**e for p,e in order_factors.items()) == O, 'order-multiple factorization')
    require(pow(2,O,H) == 1, 'initial order multiple')
    for prime in sorted(order_factors):
        while O % prime == 0 and pow(2,O//prime,H) == 1:
            O//=prime
    require(pow(2,O,H) == 1, 'order exponent equality')
    remaining=[prime for prime in sorted(order_factors) if O % prime == 0]
    require(all(pow(2,O//prime,H) != 1 for prime in remaining), 'order minimality')
    T=lcm(4,2*E,O)
    L=E//2
    require(gcd(Q*H,T) == 1, 'decisive CRT coprimality')
    # These arbitrary illustrative numbers are NOT authenticated compiler exports.
    x,b,K0,MC,MF,J=1,1,0,2,4,1
    u=2*d*x+b
    C=z=1
    alpha=q-1-2*d*x
    w=X//q**3
    F=K0+X-q+1
    M=(MC+q*(MF+B-1))*J
    mu,kappa=pell(A,u)
    eu=mu-a*kappa
    delta,rem=divmod(kappa-u,Delta)
    require(rem == 0 and delta > 0, 'positive input slack')
    target=-M-Q*(q*q-q*F+eu-1)
    pstar=crt(p0,T,target,Q*H)
    step=T*Q*H
    threshold=max(1,Q*(q*F-q*q+2)-M,Q*(q*F-q*q-eu+H+2)-M)
    if pstar < threshold:
        pstar += ((threshold-pstar+step-1)//step)*step
    n0=((1-p0)//2)%L
    records=[]
    exact_records=[]
    for j in range(32):
        p=pstar+j*step
        n=n0+L*(j+1)
        require(p%4 == 3 and p%T == p0%T and (p-target)%(Q*H) == 0, 'p progression')
        require(pow(2,p,H) == X%H, 'projection power congruence')
        require((2*n+p-1)%E == 0, 'first-index congruence')
        require((p+M)%Q == 0, 'Z integrality')
        Z=q*q-q*F+(p+M)//Q
        require((Z+eu-1)%H == 0, 'rho integrality')
        rho=(Z+eu-1)//H
        W=1-Z
        require(min(J,alpha,w,s,F,Z,rho,delta,z) > 0 and W < 0, 'outer witness signs')
        require(q == (B-1)*J+1 and X == w*q**3 and Y == s*q**3, 'repunit/scales')
        require(C == q-alpha-2*d*x and (K0+X)*C == F+z*(q-1), 'transport residual')
        require((q*q-Z-q*F)*Q+M == -p, 'packing residual negative value')
        require(W+a*kappa+rho*H == mu and mu > 0, 'positive input root')
        require(kappa == u+delta*Delta and mu*mu-Delta*kappa*kappa == 1, 'input residual')
        records.append({'p_bits':p.bit_length(),'Z_bits':Z.bit_length(),'rho_bits':rho.bit_length()})
        exact_records.append({'p':p,'n_congruence_representative_only':n,'Z':Z,'rho':rho})
    legacy={'scope':'Bounded exact prime, CRT and outer identities only; no full numerical child zero',
            'toy_fixture':{'d':d,'q':q,'p0':p0,'s':s,'ell':ell,'ell_bits':ell.bit_length(),'O':O},
            'prime_certificate_verified':True,'coprimality_QH_T':gcd(Q*H,T),
            'outer_cases':len(records),'input_index':u,'input_kappa_bits':kappa.bit_length(),
            'records':records,'full_main_or_auxiliary_witness_materialized':False,
            'upstream_code_executed':False}
    require(exact(legacy,read_json(files['evidence/bounded-check-results.json'])),
            'exact-typed comparison with historical bounded result')
    return {'prime_certificate':{'n':ell,'bits':ell.bit_length(),'recursive_nodes':count[0],
                'distinct_primes':sorted(seen),'criterion':'Full Lucas n-1, recursively certified'},
            'order_mod_3ell':O,'order_proved_minimal':True,'coprimality_QH_T':gcd(Q*H,T),
            'toy_parameters':{'d':d,'N':1,'b':b,'x':x,'K0':K0,'MC':MC,'MF_native':MF},
            'authenticated_compiler_export_claimed':False,'outer_cases':32,
            'exact_fixture_digest_sha256':sha256(canonical(exact_records)),
            'historical_bounded_result_exacttyped_match':True,'records':records,
            'main_ratio_hits_searched':False,'full_child_zero_materialized':False}

def polynomial_add(a,b):
    out=[0]*max(len(a),len(b))
    for i,x in enumerate(a): out[i]+=x
    for i,x in enumerate(b): out[i]+=x
    while len(out)>1 and out[-1] == 0: out.pop()
    return out

def polynomial_scale(a,s):
    return [s*x for x in a]

def polynomial_mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out

def polynomial_eval(coeffs,x,modulus=None):
    total=0
    for c in reversed(coeffs):
        total=total*x+c
        if modulus is not None: total%=modulus
    return total

def polynomial_compose(a,b):
    out=[0]
    for c in reversed(a): out=polynomial_add(polynomial_mul(out,b),[c])
    return out

def odd_quotient(b,z,modulus=None):
    """Q_b(z) from Q_0=1, Q_1=4z-3; logarithmic matrix recurrence."""
    if b == 0: return 1 if modulus is None else 1%modulus
    def mul(u,v):
        w=[u[0]*v[0]+u[1]*v[2],u[0]*v[1]+u[1]*v[3],
           u[2]*v[0]+u[3]*v[2],u[2]*v[1]+u[3]*v[3]]
        return w if modulus is None else [x%modulus for x in w]
    v=[1,0,0,1]
    base=[4*z-2,-1,1,0]
    power=b-1
    while power:
        if power&1: v=mul(v,base)
        power>>=1
        if power: base=mul(base,base)
    value=v[0]*(4*z-3)+v[1]
    return value if modulus is None else value%modulus

def pell_checks():
    count=0
    for A in range(2,13):
        delta=A*A-1
        a=A-2
        H=4*a+3
        previous=0
        for n in range(41):
            chi,psi=pell(A,n)
            require(chi*chi-delta*psi*psi == 1, 'Pell norm fixture')
            require((chi-a*psi-pow(2,n,H))%H == 0, 'projection e_n congruence')
            if n:
                require(chi-a*psi == 2*psi-previous, 'projection e_n identity')
            if n%2:
                require((psi-n)%delta == 0, 'odd input index congruence')
                if n>=3: require(psi>n, 'positive input slack fixture')
            previous=psi
            count+=1
    first=0
    for X in [1,2,4,8]:
        for Y in range(1,6):
            E=X*Y
            P=2*X*Y*Y+1
            for n in range(1,9):
                tau,psi=pell(P,n)
                k=2*psi
                require(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k == 1, 'first norm fixture')
                require((E*k*Y)*(E*k*Y+k) == X*Y*Y*(X*Y*Y+1)*k*k, 'factored first norm')
                require(psi%E == n%E, 'first-index modular recurrence')
                first+=1
    qs=[[1],[-3,4]]
    ps=[[1],[-1,4]]
    for b in range(2,25):
        qs.append(polynomial_add(polynomial_mul([-2,4],qs[-1]),polynomial_scale(qs[-2],-1)))
        ps.append(polynomial_add(polynomial_mul([-2,4],ps[-1]),polynomial_scale(ps[-2],-1)))
    evaluation_count=0
    for b,coeffs in enumerate(qs):
        require(coeffs[0] == (-1)**b*(2*b+1), 'odd quotient constant polynomial')
        require(exact(polynomial_compose(coeffs,[1,-1]),polynomial_scale(ps[b],(-1)**b)),
                'coefficientwise Q_b(1-v)=(-1)^b psi polynomial')
        for A in range(2,10):
            chi,psi=pell(A,2*b+1)
            require(chi%A == 0 and chi//A == polynomial_eval(coeffs,A*A), 'odd quotient Pell identity')
            require(polynomial_eval(coeffs,1-A*A) == (-1)**b*psi, 'odd quotient negative argument')
            require(odd_quotient(b,A*A) == chi//A, 'binary odd quotient recurrence')
            evaluation_count+=1
    return {'main_pell_projection_cases':count,'first_pell_factoring_cases':first,
            'odd_quotient_coefficient_identities':len(qs),
            'odd_quotient_evaluation_cases':evaluation_count,
            'largest_odd_quotient_polynomial_degree':24,
            'scope':'Finite exact arithmetic and polynomial fixtures; not the density theorem'}

def auxiliary_checks():
    records=[]
    for A,p in [(2,3),(3,3),(4,3),(5,3),(6,3),(2,7)]:
        delta=A*A-1
        D,c=pell(A,p)
        m=c*p
        f,psi_m=pell(A,m)
        Q=delta*psi_m
        require(psi_m%(c*c) == 0, 'auxiliary c^2 divisibility')
        i=Q//(c*c)
        require(i>0 and Q==i*c*c and Q*Q==delta*(f*f-1), 'strong auxiliary square')
        s=p+2*m
        b=(s-1)//2
        require(c%2 == m%2 == 1 and p%4 == 3 and s%4 == 1 and b%2 == 0, 'auxiliary parity')
        require(odd_quotient(b,(Q*Q)%c,c) == p%c, 'U=p mod c')
        require((Q*Q-(1-A*A))%f == 0, 'auxiliary Q^2 negative-square congruence')
        require(pell(A,s,f)[1] == (-c)%f, 'psi_A(p+2m)=-c mod f')
        require(odd_quotient(b,(Q*Q)%f,f) == (-c)%f, 'U=-c mod f')
        require(4*Q*Q-3>c>p and s>=3, 'auxiliary strict growth bound')
        full=(A,p)==(2,3)
        if full:
            chi_Q,y=pell(Q,s)
            require(chi_Q%Q==0, 'materialized local U integer')
            U=chi_Q//Q
            require(U == odd_quotient(b,Q*Q), 'materialized local odd quotient')
            require((U-p)%c==0 and (U+c)%f==0, 'materialized local quotients')
            j,o=(U-p)//c,(U+c)//f
            require(min(i,j,o,y,f)>0, 'local auxiliary positivity')
            require(U==j*c+p==o*f-c, 'local auxiliary linear residuals')
            require(Q*Q*(U*U-y*y)==1-y*y, 'local strong auxiliary Pell residual')
        records.append({'A':A,'p':p,'c':c,'m':m,'saux':s,'f_bits':f.bit_length(),
                        'Qaux_bits':Q.bit_length(),'U_y_materialized':full})
    return {'strong_auxiliary_congruence_cases':len(records),
            'full_local_auxiliary_blocks':1,'records':records,
            'scope':'Small independent local fixtures; no full outer/main child witness tuple'}

def harness_semantics_checks():
    require(not exact(True,1) and not exact(False,0) and not exact(1,1.0), 'strict primitive types')
    require(not exact({'x':[True]},{'x':[1]}), 'strict nested bool/int distinction')
    require(exact({'x':[True,1,None]},{'x':[True,1,None]}), 'strict same-type equality')
    for data in [b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}']:
        rejected=False
        try: read_json(data)
        except (ValueError,CheckFailure): rejected=True
        require(rejected, 'malformed/nonfinite JSON rejected')
    return {'bool_int_distinguished':True,'int_float_distinguished':True,
            'duplicate_keys_rejected':True,'nonfinite_json_rejected':True,
            'assert_statements_used':False}

def run(files):
    return {'schema':'research-report33-repro-v1','status':'PASS',
            'semantics':harness_semantics_checks(),'provenance':source_checks(files),
            'source_data':data_schedule_checks(files),'outer':outer_checks(files),
            'pell_polynomials':pell_checks(),'auxiliary':auxiliary_checks(),
            'limitations':[
                'Finite replay does not prove Dirichlet or irrational-rotation density.',
                'The 32 outer cases use toy constants, not authenticated compiler exports.',
                'No main ratio hit or complete signed19 zero is numerically materialized.',
                'Only one small local auxiliary block is fully materialized.',
                'Source programs and JSON schedules are never executed or imported.',
                'Hash matches bind cached bytes to recorded receipts, not a fresh network retrieval.',
                'The mathematical existence proof and independent audit remain separate evidence.'
            ]}
