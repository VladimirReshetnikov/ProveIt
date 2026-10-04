#!/usr/bin/env python3
"""Bounded pinned-data evidence for the prime-index free83 collapse proof.

No predecessor code executes. Sparse rational arithmetic follows the explicit
coefficient-cut method used in earlier independent reviews; the specialization,
outer host, prime trial divisions and Pell/CRT checks here are fresh.
"""
import argparse
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path

PINS = {
 'complete83_free_coefficient_scout.py': 'a72a406021b96df8111c7f11d36e42241894f0834a660c9ed7c6a75cbfbe1485',
 'complete83_free_coefficient_scout.json': '682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md': '867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
 'complete75_weakened86_all_input_collapse.md': '46f3e0f25fc4efeb3f8129b77c3df988283c7a818ee2af330e8e8f460dc8d017',
 'complete75_weakened86_auxiliary_sign_lift.md': '491ac3c3755efed1c6c89f7e07a752c25fb040859cac8c07d7db25e803c62c53',
 'complete75_weakened86_infinite_outer_family.md': '74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2',
 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_weakened86_rejecting_compiler.md': '186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
FACTORS = ['norm_first', 'norm_main', 'norm_input', 'norm_aux',
           'norm_index', 'norm_transport', 'norm_strong']


def need(test, message):
    if not test:
        raise ValueError(message)


def sha(raw): return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def exact(a, b):
    if type(a) is not type(b): return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def unique_object(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, 'duplicate JSON key ' + k)
        out[k] = v
    return out


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


class Poly:
    """Integer coefficients; a sorted tuple of variable names is a monomial."""
    def __init__(self, value=0):
        if isinstance(value, Poly): self.c = value.c
        elif type(value) is int: self.c = {(): value} if value else {}
        else: self.c = {m: v for m, v in value.items() if v}
    def __add__(self, other):
        other = Poly(other); out = dict(self.c)
        for m, v in other.c.items(): out[m] = out.get(m, 0) + v
        return Poly(out)
    __radd__ = __add__
    def __neg__(self): return Poly({m: -v for m, v in self.c.items()})
    def __sub__(self, other): return self + -Poly(other)
    def __rsub__(self, other): return Poly(other) + -self
    def __mul__(self, other):
        other = Poly(other); out = {}
        for m, v in self.c.items():
            for n, w in other.c.items():
                key = tuple(sorted(m+n)); out[key] = out.get(key, 0) + v*w
        return Poly(out)
    __rmul__ = __mul__
    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'polynomial power')
        out = Poly(1); base = self
        while n:
            if n & 1: out = out*base
            n //= 2
            if n: base = base*base
        return out
    def __eq__(self, other): return self.c == Poly(other).c
    def saved(self): return [[list(m), v] for m, v in sorted(self.c.items())]


def variable(name): return Poly({(name,): 1})


class Rat:
    """Formal rational functions, normalized only after exact cross-products."""
    def __init__(self, numerator=0, denominator=1):
        if isinstance(numerator, Rat): self.n, self.d = numerator.n, numerator.d
        else: self.n, self.d = Poly(numerator), Poly(denominator)
        need(bool(self.d.c), 'zero formal denominator')
    def __add__(self, other):
        other = Rat(other)
        if self.d == other.d: return Rat(self.n+other.n, self.d)
        return Rat(self.n*other.d+other.n*self.d, self.d*other.d)
    __radd__ = __add__
    def __neg__(self): return Rat(-self.n, self.d)
    def __sub__(self, other): return self + -Rat(other)
    def __rsub__(self, other): return Rat(other) + -self
    def __mul__(self, other):
        other = Rat(other)
        return Rat(self.n*other.n, self.d*other.d)
    __rmul__ = __mul__
    def __eq__(self, other):
        other = Rat(other)
        return self.n*other.d == other.n*self.d


def source_proof(packet):
    names = 'beta J Y k c D tau x d b K MC MF W kap mu f S V y'.split()
    beta, J, Y, k, c, D, tau, x, d, b, K, MC, MF, W, kap, mu, f, S, V, y = map(variable, names)
    q = beta*J+1; X = q; E = q*Y; a = Y*(q+1)
    Delta = (a+1)*(a+3); H = 4*a+3; u = 2*d*x+b
    C = W+1; F = (K+1)*C
    R = (q*q-q*F-1)*(q*q-1)+(MC+q*MF)*J
    gamma = Rat(D-a*c-q, H)
    rho = Rat(mu-a*kap-W, H)
    env = {
      'Bm1': Rat(beta), 'Jrep': Rat(J), 'w': Rat(1), 's': Rat(Y, q**3),
      'tau_root': Rat(tau), 'eta': Rat(c-k*Y), 'zeta': Rat(k*(Y+1)-c),
      'rho': rho, 'sigma': Rat(D-a*c-q-mu+a*kap+W, H),
      'F': Rat(F), 'Z': Rat(1), 'x': Rat(x), 'Kconstant': Rat(K),
      'MC': Rat(MC), 'MF': Rat(MF), 'twice_cell_bits': Rat(2*d), 'inner_bits': Rat(b),
      'alpha': Rat(q-F-W-2*d*x-2), 'delta': Rat(kap-u, Delta),
      'h': Rat(k-R-1, E), 'transport_quotient': Rat(1),
      'f': Rat(f), 'aux_coefficient_root': Rat(S), 'y_aux': Rat(y),
      'auxiliary_quotient': Rat(V+c+R*f*f, c*f),
    }
    need(set(env) == set(packet['free']), 'exact full free interface')
    expected = [tau*tau-X*Y*Y*(X*Y*Y+1)*k*k,
                D*D-Delta*c*c, mu*mu-Delta*kap*kap,
                S*S*V*V-(S*S-1)*y*y, Poly(1), Poly(1), Delta*f*f-S*S]
    targets = {
      'q': Rat(q), 'wn2': Rat(q), 'sn2': Rat(Y), 'UM': Rat(E), 'R10b': Rat(k),
      'R10a': Rat(c), 'R12': Rat(a), 'gamma_sum': gamma, 'gam': Rat(D-a*c-q),
      'R14': Rat(D), 'A': Rat(Delta), 'marked_rhs': Rat(C), 'W': Rat(W),
      'odd_index': Rat(u), 'index_product': Rat(kap-u), 'index_rhs': Rat(kap),
      'modulus_multiple': Rat(mu-a*kap-W), 'exponent_rhs': Rat(mu),
      'hpm1': Rat(k-R-1), 'index_difference': Rat(R+1), 'r_lhs': Rat(R),
      'kinner': Rat(K+1), 'innerC': Rat(F), 'transport_partial': Rat(q),
      'local_rhs': Rat(q-1), 'auxiliary_Tf': Rat(V+c+R*f*f, c),
      'auxiliary_Tf_minus_one': Rat(V+R*f*f, c),
      'auxiliary_c_Tf': Rat(V+R*f*f), 'aux_u_rhs': Rat(V),
    }
    targets.update({name: Rat(value) for name, value in zip(FACTORS, expected)})
    product = Poly(1)
    for norm in expected: product = product*norm
    targets['polynomial'] = Rat(product-Delta)
    dependencies = {}; cuts = []; M = Acount = 0
    for name, op, left, right in packet['source']:
        need(name not in env and op in ('+', '-', '*'), 'fresh legal gate ' + name)
        for port in [left, right]:
            need(type(port) is int or type(port) is str and port in env, 'source closure')
        lhs = env[left] if type(left) is str else Rat(left)
        rhs = env[right] if type(right) is str else Rat(right)
        value = lhs+rhs if op == '+' else lhs-rhs if op == '-' else lhs*rhs
        if name in targets:
            need(value == targets[name], 'full coefficient cut ' + name)
            value = targets[name]; cuts.append(name)
        env[name] = value
        dependencies[name] = [p for p in [left, right] if type(p) is str]
        M += op == '*'; Acount += op != '*'
    need(set(cuts) == set(targets), 'every declared cut encountered')
    need(env[packet['output']] == Rat(product-Delta), 'complete rational output identity')
    live = set(); pending = [packet['output']]
    while pending:
        name = pending.pop()
        if name not in live:
            live.add(name); pending.extend(dependencies.get(name, []))
    need(live == set(env), 'all paid gates and supplied ports live')
    need((M, Acount, len(packet['witnesses'])) == (46, 37, 18), 'full count')
    # Independently trace every literal finalizer operation with cut norm ports.
    abstract = {name: variable(name) for name in FACTORS}; abstract['A'] = variable('Delta')
    tail = []
    for name, op, left, right in packet['source']:
        if name in FACTORS or name == 'A': continue
        if all(type(p) is int or p in abstract for p in [left, right]):
            l = abstract[left] if type(left) is str else Poly(left)
            r = abstract[right] if type(right) is str else Poly(right)
            abstract[name] = l+r if op == '+' else l-r if op == '-' else l*r
            tail.append([name, op, left, right])
    expected_tail = Poly(1)
    for name in FACTORS: expected_tail = expected_tail*variable(name)
    need(abstract['polynomial'] == expected_tail-variable('Delta'), 'complete factor finalizer')
    need(len(tail) == 7, 'six paid final products and final subtraction')
    # Substitution norm_first=...=norm_transport=1, norm_strong=Delta.
    specialization = {name: Poly(1) for name in FACTORS[:-1]}
    specialization[FACTORS[-1]] = variable('Delta'); specialization['A'] = variable('Delta')
    for name, op, left, right in tail:
        l = specialization[left] if type(left) is str else Poly(left)
        r = specialization[right] if type(right) is str else Poly(right)
        specialization[name] = l+r if op == '+' else l-r if op == '-' else l*r
    need(specialization['polynomial'] == 0, 'conditional entire source zero')
    return {
      'formal_variables': names, 'denominators': ['q^3', 'H', 'Delta', 'q*Y', 'c*f'],
      'paid_rows_checked': 83, 'M': M, 'A': Acount, 'witnesses': 18,
      'coefficient_cuts': cuts, 'factor_polynomials': [v.saved() for v in expected],
      'full_output_monomials': len((product-Delta).c),
      'full_output_coefficients_sha256': sha(canonical((product-Delta).saved())),
      'literal_finalizer': tail, 'conditional_factor_values': [1,1,1,1,1,1,'Delta'],
      'identity_scope': 'Exact rational full-source substitution; the note proves positive integral specialization.'}


def pell(A, n, modulus=None):
    """Binary multiplication in Z[t]/(t^2-(A^2-1)); exact or modular."""
    need(type(A) is int and A >= 2 and type(n) is int and n >= 0, 'Pell domain')
    D = A*A-1
    def mul(u, v):
        pair = (u[0]*v[0]+D*u[1]*v[1], u[0]*v[1]+u[1]*v[0])
        return pair if modulus is None else (pair[0]%modulus, pair[1]%modulus)
    out = (1, 0); base = (A, 1)
    while n:
        if n & 1: out = mul(out, base)
        n //= 2
        if n: base = mul(base, base)
    return out


def prime_trial(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    return all(n % d for d in range(3, isqrt(n)+1, 2))


def hosts():
    # Diagnostic numeral interface only: these are NOT valid compiler masks.
    d = b = x = K = 1; B = 2; N = 5; q = 32; J = 31
    MC, MF_native = 2, 4; MF_source = MF_native+B-1
    u = 2*d*x+b; W = 2**u; C = W+1; F = (K+1)*C
    alpha = q-F-W-2*d*x-2
    G = q*q-q*F-1; R = G*(q*q-1)+(MC+q*MF_source)*J
    need(q == B**N and q == (B-1)*J+1, 'diagnostic width and repunit')
    need(all(v > 0 for v in [J,F,alpha,W,C,x]), 'positive outer host')
    need(q-F-1-alpha-2*d*x == C and C-1 == W, 'actual C/W definitions')
    need((K+1)*C+q-F-(q-1) == 1, 'actual positive transport factor')
    need(0 < R+1 < q**4 and R % 2 == 1, 'host positive odd packed R')
    outer = {'d':d,'b':b,'x':x,'Kconstant':K,'B':B,'N':N,'q':q,'Jrep':J,
             'u':u,'W':W,'Z':1,'C':C,'F':F,'alpha':alpha,'w':1,'transport_quotient':1,
             'MC_diagnostic':MC,'MF_native_diagnostic':MF_native,'MF_source':MF_source,
             'gap':G,'R':R,'norm_transport':1,'valid_compiler_fixture':False,
             'compiler_exclusions':['B=2 < 16','MC and MF_native exceed the required strict B-1 mask bound'],
             'main_first_and_auxiliary_witnesses_materialized':False}
    Cprime = 4*q**3*(q+1)//3; s = 6; ell = Cprime*s+1
    Y = q**3*s; a = Y*(q+1); A = a+2; Delta = A*A-1
    H = 4*a+3; L = 2*(ell-1); progression = 4*L
    p = 42095320498181
    need(Cprime == 1441792 and Cprime%5 == 2 and s%5 == 1, 'modulus host recipe')
    need(prime_trial(ell) and ell>3 and ell%5 == 3, 'trial-certified modulus prime')
    need(H == 3*ell and pow(2,L,H) == 1, 'actual modulus and exponent period')
    need(gcd(Cprime+1,5*Cprime) == 1 and gcd(N,progression) == 1, 'both reduced progressions')
    need(prime_trial(p) and p>max(Delta,R) and p%progression == N, 'trial-certified main progression prime')
    need(p%4 == 1 and pow(2,p,H) == q, 'main exponent congruence')
    c_mod_p = pell(A,p,p)[1]
    need(c_mod_p == pow(Delta,(p-1)//2,p) and c_mod_p in (1,p-1), 'prime host Frobenius')
    c_mod_8p = pell(A,p,8*p)[1]
    need(gcd(c_mod_8p,8*p) == 1, 'main host auxiliary CRT coprimality')
    Dmod, cmod = pell(A,p,H)
    need((Dmod-a*cmod-q)%H == 0, 'main gamma integral congruence')
    mu, kap = pell(A,u)
    need((kap-u)%Delta == 0 and (mu-a*kap-W)%H == 0, 'input host integrality')
    delta = (kap-u)//Delta; rho = (mu-a*kap-W)//H
    need(delta>0 and rho>0 and mu*mu-Delta*kap*kap == 1, 'positive input host')
    P = 2*q*Y*Y+1; v2 = 0; t = P*P-1
    while t%2 == 0: v2 += 1; t //= 2
    need(A < P < 2*A*A-1 and Delta%2 == 1 and v2%2 == 1, 'ratio-field host premises')
    return outer, {
      's':s,'Cprime':Cprime,'ell':ell,'Y':Y,'a':a,'A':A,'Delta':Delta,'H':H,'L':L,
      'main_progression_modulus':progression,'main_progression_residue':N,
      'p':p,'main_progression_multiplier':(p-N)//progression,
      'p_gt_Delta':True,'p_gt_R':True,'c_mod_p':c_mod_p,'c_mod_8p':c_mod_8p,
      'gcd_c_8p':1,'input_kappa':kap,'input_mu':mu,'input_delta':delta,'input_rho':rho,
      'first_Pell_base':P,'main_discriminant_odd':True,'first_discriminant_v2':v2,
      'trial_division_bounds':{'ell':isqrt(ell),'p':isqrt(p)},
      'strict_first_main_ratio_checked':False,'main_Pell_pair_materialized':False,
      'scope':'Prime and congruence host only; no equidistribution simulation or complete zero.'}


def recurrence_checks():
    rows = []
    for A in [2,4,6,8,16,34]:
        Delta=A*A-1; a=A-2; H=4*a+3; gammas=[]
        for n in range(0,14):
            chi, psi = pell(A,n)
            num = chi-a*psi-2**n
            need(num%H == 0, 'input/main gamma congruence')
            g=num//H; gammas.append(g)
            need(chi*chi-Delta*psi*psi == 1, 'Pell norm')
            if n>=2: need(g>0 and (n==2 or g>gammas[-2]), 'gamma positive increasing tail')
            if n>=3: need(g==2*A*gammas[n-1]-gammas[n-2]+2**(n-2), 'gamma recurrence')
            if n%2 == 1: need((psi-n)%Delta == 0, 'odd-index input divisibility')
        need(gammas[:3] == [0,0,1], 'gamma seeds')
        rows.append({'A':A,'indices':list(range(14)),'gamma_values':gammas})
    frobenius=[]
    for A in [2,4,6,8,16,34]:
        for p in [5,13,17,29,37,41,53,61]:
            if (A*A-1)%p == 0: continue
            need(prime_trial(p) and p%4 == 1, 'small prime')
            residue=pell(A,p,p)[1]; target=pow(A*A-1,(p-1)//2,p)
            need(residue==target and residue in (1,p-1), 'bounded Frobenius formula')
            need(gcd(pell(A,p,8*p)[1],8*p)==1, 'bounded CRT coprimality')
            frobenius.append({'A':A,'p':p,'psi_mod_p':residue,'Legendre_value':target})
    return rows, frobenius


def auxiliary_checks():
    rows=[]
    for A,p,R in [(2,5,3),(2,13,7),(2,17,19),(4,13,3),(4,17,11),(4,29,21),
                  (6,13,5),(6,17,23),(6,41,31),(8,5,3),(8,17,9),(8,29,37)]:
        need(prime_trial(p) and p%4==1 and (A*A-1)%p, 'auxiliary case assumptions')
        Delta=A*A-1; D,c=pell(A,p); f,bstrong=pell(A,2*p); S=Delta*bstrong
        need(c%2==1 and gcd(c,8*p)==1 and gcd(c,f)==1, 'exact auxiliary coprimality')
        need(bstrong==2*D*c and Delta*f*f-S*S==Delta, 'exact scaled strong factor')
        v=R+c*((3*p-R)*pow(c,-1,8*p)%(8*p))
        need(v>0 and v%c==R%c and v%(8*p)==3*p and v%4==3, 'actual auxiliary CRT')
        modulus=S*c*f
        chi_mod,y_mod=pell(S,v,modulus)
        need(chi_mod%S==0, 'odd auxiliary quotient integral modulo exact multiple')
        Vmod=chi_mod//S
        need(Vmod%c==(-R)%c and Vmod%f==(-c)%f, 'both auxiliary quotient congruences')
        need((Vmod+c+R*f*f)%(c*f)==0, 'positive T numerator integral congruence')
        need((S*S*Vmod*Vmod-(S*S-1)*(y_mod%(c*f))**2-1)%(c*f)==0, 'auxiliary norm congruence')
        need(pell(A,8*p,f)==(1,0), 'coefficientwise 8p return modulo f')
        need(pell(A,3*p)[1]==(2*f+1)*c, 'exact main triplication')
        need((2*D)%c != 0, 'literal restored i nonintegral')
        rows.append({'A':A,'p':p,'R':R,'c':c,'D':D,'f':f,'S':S,'auxiliary_index':v,
                     'chi_mod_Scf':chi_mod,'V_mod_cf':Vmod,'cf':c*f,
                     'T_numerator_mod_cf':0,'restored_i_numerator':2*D,'restored_i_denominator':c,
                     'auxiliary_full_values_materialized':False,'complete_source_zero_materialized':False})
    return rows


def verify(root):
    for name,pin in PINS.items(): need(sha((root/name).read_bytes())==pin, 'dependency pin '+name)
    parent=read_json(root/'complete83_free_coefficient_scout.json'); packet=parent['packet']
    need(packet['factors']==FACTORS and packet['exact_degree']==111, 'inherited packet facts')
    need(packet['ledger']['total']==83 and len(packet['free'])==25, 'inherited packet interface')
    proof=source_proof(packet); outer,prime=hosts(); recurrence,frobenius=recurrence_checks(); aux=auxiliary_checks()
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'dependency_pins':PINS,
            'packet':packet,'packet_sha256':sha(canonical(packet)),
            'packet_scope':'Unchanged ancestor packet, including its historical open-soundness metadata; new theorem is in the companion note.',
            'formal_source':proof,'outer_host':outer,'prime_progression_host':prime,
            'gamma_recurrence_cases':recurrence,'Frobenius_cases':frobenius,'auxiliary_CRT_cases':aux,
            'evidence_counts':{'full_rows':83,'formal_cuts':len(proof['coefficient_cuts']),
              'gamma_states':sum(len(v['indices']) for v in recurrence),'Frobenius_cases':len(frobenius),
              'auxiliary_CRT_cases':len(aux),'trial_certified_host_primes':2},
            'external_existence_dependencies':['Dirichlet primes in a reduced progression',
              'Vinogradov prime equidistribution for irrational multiples',
              'prime number theorem in fixed reduced progressions','pinned strict Pell-ratio tail estimate'],
            'scope':'Finite exact evidence and full conditional source identity; no finite test proves the infinite-existence theorem.',
            'giant_full_zero_materialized':False,'prime_density_simulated':False,
            'valid_compiler_fixture_numerically_materialized':False,'predecessor_Python_executed':False,
            'new_universal_upper_bound_claim':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output',type=Path); mode.add_argument('--expect',type=Path)
    args=parser.parse_args(); result=verify(args.root.resolve())
    serialized=json.dumps(result,indent=2,sort_keys=True)+'\n'
    need(exact(result,json.loads(serialized)), 'type-exact JSON round trip')
    if args.expect:
        need(exact(result,read_json(args.expect)), 'exact saved receipt')
    else: args.output.write_text(serialized)
    print(json.dumps({'status':'PASS','evidence_counts':result['evidence_counts'],
                      'ledger':result['packet']['ledger'],'mode':'expect' if args.expect else 'output'},sort_keys=True))


if __name__=='__main__': main()
