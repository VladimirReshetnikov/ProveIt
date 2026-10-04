#!/usr/bin/env python3
"""Independent static algebra audit. Python standard library only.

This program never imports or executes packet code, Lean, a counter program, or
physical simulation. The input directory is read-only. Outputs go to --out.
Sparse monomials are tuples of (variable, exponent), unlike the packet checker.
"""
import argparse
import hashlib
import json
import math
import stat
from fractions import Fraction
from pathlib import Path


def must(test, message):
    if not test:
        raise AssertionError(message)


class Poly:
    def __init__(self, value=0):
        self.c = ({(): value} if value else {}) if isinstance(value, int) else {m:c for m,c in value.items() if c}

    @staticmethod
    def v(name):
        return Poly({((name,1),):1})

    @staticmethod
    def of(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, rhs):
        result = dict(self.c)
        for m,c in Poly.of(rhs).c.items():
            result[m] = result.get(m,0)+c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m:-c for m,c in self.c.items()})

    def __sub__(self, rhs):
        return self + (-Poly.of(rhs))

    def __rsub__(self, lhs):
        return Poly.of(lhs)+(-self)

    def __mul__(self, rhs):
        result = {}
        for lm,lc in self.c.items():
            for rm,rc in Poly.of(rhs).c.items():
                p = dict(lm)
                for n,e in rm:
                    p[n] = p.get(n,0)+e
                m = tuple(sorted(p.items()))
                result[m] = result.get(m,0)+lc*rc
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        must(isinstance(n,int) and n>=0, 'natural polynomial exponent')
        r = Poly(1)
        a = self
        while n:
            if n&1:
                r = r*a
            n >>= 1
            if n:
                a = a*a
        return r

    def degree(self):
        return max((sum(e for _,e in m) for m in self.c), default=-1)

    def names(self):
        return {n for m in self.c for n,e in m}

    def subst(self, values):
        result = Poly(0)
        for m,c in self.c.items():
            term = Poly(c)
            for n,e in m:
                term = term*Poly.of(values.get(n, Poly.v(n)))**e
            result += term
        return result

    def at(self, values):
        return sum(c*math.prod(values[n]**e for n,e in m) for m,c in self.c.items())

    def coefficient(self, **powers):
        return self.c.get(tuple(sorted(powers.items())),0)

    def data(self):
        return [{'powers':dict(m),'coefficient':c} for m,c in sorted(self.c.items())]

    def same(self, other):
        return self.c == Poly.of(other).c


NAT = 'd_wb d_wC d_yC q_alpha q_sigma q_tau q_r'.split()
DIRECT22 = 'o w M g x y u v s t q_b q_v J'.split()


def module(arity, base, index):
    names = DIRECT22 if arity==22 else ('o g u v t q_b q_v J'.split() if arity==16 else 'o g u q_b q_v J'.split())
    leaves = names + [n+'_plus' for n in NAT]
    if arity!=13:
        leaves += ['alpha_plus']
    if arity==22:
        leaves += ['beta_plus']
    a = {n:Poly.v(n) for n in names}
    a.update({n:Poly.v(n+'_plus')-1 for n in NAT})
    if arity!=13:
        a['alpha'] = Poly.v('alpha_plus')+1
    if arity==22:
        a['beta'] = Poly.v('beta_plus')+1
    else:
        a['w'] = base+a['d_wb']
        a['y'] = index+a['d_yC']
        a['beta'] = 1+4*a['y']*a['q_b']
        if arity!=16:
            a['v'] = a['y']**2*a['q_v']
            a['t'] = index+4*a['y']*a['q_tau']
        if arity!=13:
            a['M'] = 2*base*a['alpha']-base**2-1
            a['x'] = a['y']*(a['alpha']-base)+base*a['o']+a['M']*a['q_r']
            a['s'] = a['x']+a['u']*a['q_sigma']
    if arity==13:
        a['M'] = base*a['o']+a['J']
        d = 2*base
        A = a['M']+base**2+1
        X = a['y']*(A-d*base)+d*base*a['o']+d*a['M']*a['q_r']
        S = X+d*a['u']*a['q_sigma']
        a.update(d=d,A=A,X=X,S=S)
        r = [X**2-d**2-(A**2-d**2)*a['y']**2,
             d**2*(a['u']**2-1)-(A**2-d**2)*a['v']**2,
             S**2-d**2*(1+(a['beta']**2-1)*a['t']**2),
             d*(a['beta']-a['u']*a['q_alpha'])-A,
             a['w']-index-a['d_wC'],
             A**2-d**2*(1+((a['w']+1)**2-1)*(a['w']*a['g'])**2)]
    else:
        r = [a['x']**2-(a['alpha']**2-1)*a['y']**2-1,
             a['u']**2-(a['alpha']**2-1)*a['v']**2-1,
             a['s']**2-(a['beta']**2-1)*a['t']**2-1,
             a['beta']-1-4*a['y']*a['q_b'],
             a['beta']-a['alpha']-a['u']*a['q_alpha'],
             a['v']-a['y']**2*a['q_v'],
             a['s']-a['x']-a['u']*a['q_sigma'],
             a['t']-index-4*a['y']*a['q_tau'],
             a['y']-index-a['d_yC'],
             a['w']-base-a['d_wb'],
             a['w']-index-a['d_wC'],
             a['M']-base*a['o']-a['J'],
             a['alpha']**2-1-((a['w']+1)**2-1)*(a['w']*a['g'])**2,
             2*base*a['alpha']-a['M']-base**2-1,
             a['x']-a['y']*(a['alpha']-base)-base*a['o']-a['M']*a['q_r']]
        if arity==16:
            r = [r[i] for i in [0,1,2,4,5,7,10,11,12]]
        if arity==14:
            r = [r[i] for i in [0,1,2,4,10,11,12]]
    must(len(leaves)==arity and len(set(leaves))==arity, 'distinct positive leaf ledger')
    return r,leaves,a


def sos(residuals):
    return sum((r**2 for r in residuals),Poly(0))


def imported_polynomial(rows):
    result = {}
    for row in rows:
        powers = {}
        for n in row['monomial']:
            powers[n] = powers.get(n,0)+1
        m = tuple(sorted(powers.items()))
        must(m not in result, 'source JSON monomials unique')
        result[m] = row['coefficient']
    return Poly(result)


def quadratic_power(parameter, n):
    # Binary exponentiation in Z[sqrt(parameter^2-1)], newly authored.
    D = parameter*parameter-1
    def multiply(p,q):
        return (p[0]*q[0]+D*p[1]*q[1],p[0]*q[1]+p[1]*q[0])
    answer, factor = (1,0),(parameter,1)
    while n:
        if n&1:
            answer = multiply(answer,factor)
        n //= 2
        if n:
            factor = multiply(factor,factor)
    return answer


def quotient(n,d):
    must(d>0 and n>=0 and n%d==0, 'nonnegative integral quotient')
    return n//d


def fixture(b,C,parameter_multiple=1):
    w = max(b,C)
    alpha,wg = quadratic_power(w+1,w*parameter_multiple)
    g = quotient(wg,w)
    x,y = quadratic_power(alpha,C)
    u,v = quadratic_power(alpha,2*C*y)
    # Direct CRT residue, independent from any packet routine.
    must(math.gcd(u,4*y)==1, 'fixture CRT coprimality')
    shift = ((1-alpha)*pow(u,-1,4*y))%(4*y)
    beta = alpha+u*shift
    s,t = quadratic_power(beta,C)
    o = b**(C-1)
    M = 2*b*alpha-b*b-1
    f = dict(o=o,w=w,M=M,g=g,x=x,y=y,u=u,v=v,s=s,t=t,
             q_b=quotient(beta-1,4*y),q_v=quotient(v,y*y),J=M-b*o,
             alpha_plus=alpha-1,beta_plus=beta-1,
             d_wb_plus=w-b+1,d_wC_plus=w-C+1,d_yC_plus=y-C+1,
             q_alpha_plus=quotient(beta-alpha,u)+1,q_sigma_plus=quotient(s-x,u)+1,
             q_tau_plus=quotient(t-C,4*y)+1,q_r_plus=quotient(x-y*(alpha-b)-b*o,M)+1)
    must(all(z>0 for z in f.values()), 'all 22 adapter values positive')
    return f


def family(f,C,k):
    f = dict(f)
    f['beta_plus'] += 4*f['y']*f['u']*k
    beta = f['beta_plus']+1
    f['s'],f['t'] = quadratic_power(beta,C)
    f['q_b'] = quotient(beta-1,4*f['y'])
    f['q_alpha_plus'] = quotient(beta-f['alpha_plus']-1,f['u'])+1
    f['q_sigma_plus'] = quotient(f['s']-f['x'],f['u'])+1
    f['q_tau_plus'] = quotient(f['t']-C,4*f['y'])+1
    return f


def reconstruct(arity,f,b,C):
    result = dict(f)
    if arity==22:
        return result
    a = {n:f[n+'_plus']-1 for n in NAT}
    w,y = b+a['d_wb'],C+a['d_yC']
    if arity==13:
        M = b*f['o']+f['J']
        alpha = Fraction(M+b*b+1,2*b)
        must(alpha.denominator==1, 'recovered rational alpha integral')
        alpha = int(alpha)
    else:
        alpha = f['alpha_plus']+1
        M = 2*b*alpha-b*b-1
    x = y*(alpha-b)+b*f['o']+M*a['q_r']
    result.update(w=w,y=y,alpha_plus=alpha-1,M=M,x=x,
                  s=x+f['u']*a['q_sigma'],beta_plus=4*y*f['q_b'])
    if arity in [13,14]:
        result.update(v=y*y*f['q_v'],t=C+4*y*a['q_tau'])
    must(all(result[n]>0 for n in module(22,Poly(b),Poly.v('C'))[1]), 'restored positivity')
    return result


def compressed(T,accepted):
    A,B,j,r,s = [Poly.v(n) for n in ['counterA','counterB','selector','slackA','slackB']]
    K,N = T+1,(T+1)**2
    den = math.factorial(N-1)
    U,V = Poly(0),Poly(0)
    for node in range(1,N+1):
        L = Poly(1)
        denominator = 1
        for other in range(1,N+1):
            if node!=other:
                L *= j-other
                denominator *= node-other
        must(den%denominator==0, 'interpolation denominator clears')
        L *= den//denominator
        U += (1+(node-1)//K)*L
        V += (1+(node-1)%K)*L
    for node in range(1,N+1):
        must(U.at({'selector':node})==den*(1+(node-1)//K),'first table coordinate')
        must(V.at({'selector':node})==den*(1+(node-1)%K),'second table coordinate')
    R,H = Poly(1),Poly(1)
    for node in range(1,N+1):
        R *= j-node
        if node in accepted:
            H *= j-node
    return [R,(den*A-U)*(U-den*K),den*A-U-den*(r-1),
            (den*B-V)*(V-den*K),den*B-V-den*(s-1),H]


def source_snapshot(root):
    result = {}
    for p in sorted([root]+list(root.rglob('*'))):
        s = p.stat()
        row = {'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':'dir' if p.is_dir() else 'file'}
        if p.is_file():
            data = p.read_bytes()
            row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        result[str(p.relative_to(root))] = row
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args = parser.parse_args()
    root,out = args.source.resolve(),args.out.resolve()
    must(root!=out and root not in out.parents, 'outputs must be outside frozen source')
    out.mkdir(parents=True,exist_ok=True)
    before = source_snapshot(root)
    receipt = {'scope':'independent static exact algebra; no source code imported or executed','source_directory':str(root),'checks':{}}
    for filename in ['MANIFEST.json','SOURCE_PINS.json']:
        raw = json.loads((root/filename).read_text())
        entries = raw['files'] if isinstance(raw,dict) else raw
        for entry in entries:
            actual = before[entry['file']]
            must(actual['sha256']==entry['sha256'] and actual['bytes']==entry['bytes'], 'pin '+entry['file'])
        receipt['checks'][filename] = len(entries)
    must(before['dependencies/pell-source.lean']['sha256']=='993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a','exact Lean pin')
    expected = {
      (22,False):[4,4,4,2,2,3,2,2,1,1,1,1,6,1,2],(22,True):[4,4,4,2,2,3,2,2,1,1,1,2,6,2,2],
      (16,False):[4,4,6,2,3,2,1,1,6],(16,True):[6,4,6,2,3,2,1,2,6],
      (14,False):[4,8,8,2,1,1,6],(14,True):[6,8,8,2,1,2,6],
      (13,False):[4,8,8,2,1,6],(13,True):[8,10,10,3,1,8]}
    modules = []
    C,B = Poly.v('C'),Poly.v('B')
    for arity in [22,16,14,13]:
        for variable in [False,True]:
            b = B+1 if variable else Poly(2)
            rr,leaves,a = module(arity,b,C)
            whole = sos(rr)
            deg = 12 if arity in [22,16] else (20 if arity==13 and variable else 16)
            must([r.degree() for r in rr]==expected[arity,variable], 'all residual degrees')
            must(whole.degree()==deg,'exact SOS degree')
            must(whole.names()==set(leaves)|({'B','C'} if variable else {'C'}),'all and only declared variables live')
            top = ({'w':8,'g':4} if arity==22 else {'d_wb_plus':8,'g':4} if arity==16 else
                   {'alpha_plus':4,'d_yC_plus':8,'q_v':4} if arity==14 else
                   {'B':8,'d_yC_plus':8,'q_v':4} if variable else {'J':4,'d_yC_plus':8,'q_v':4})
            must(whole.coefficient(**top)==1,'degree witness coefficient one')
            label = ('variable_base_B_plus_one' if variable else 'fixed_base_two') if arity==22 else f'variant_{arity}_'+('variable_base' if variable else 'fixed_base_two')
            saved = json.loads((root/'evidence'/(label+'.polynomial.json')).read_text())
            must(set(saved['positive_leaves'])==set(leaves),'frozen expansion leaf ledger')
            must(len(saved['residuals'])==len(rr),'frozen expansion residual ledger')
            must(all(r.same(imported_polynomial(sr)) for r,sr in zip(rr,saved['residuals'])),'independent residual expansion equals frozen JSON')
            must(whole.same(imported_polynomial(saved['sum_of_squares'])),'independent full expansion equals frozen JSON')
            result = {'arity':arity,'variable_base':variable,'residuals':len(rr),'residual_degrees':[r.degree() for r in rr],
                      'degree':deg,'monomials':len(whole.c),'degree_witness':top,'degree_witness_coefficient':1,'leaves':leaves}
            modules.append(result)
            (out/(label+'.independent.json')).write_text(json.dumps({'summary':result,'residuals':[r.data() for r in rr],'sum_of_squares':whole.data()},separators=(',',':'))+'\n')
    receipt['checks']['modules'] = modules
    # Symbolic elimination identities in a free base, not only a base fixture.
    b = B+1
    r22,_,a22 = module(22,b,C)
    r16,_,a16 = module(16,b,C)
    sub16 = {n:a16[n] for n in ['w','y','M','x','s']}
    sub16['beta_plus'] = a16['beta']-1
    kept = [0,1,2,4,5,7,10,11,12]
    for i,r in enumerate(r22):
        want = r16[kept.index(i)] if i in kept else 0
        must(r.subst(sub16).same(want),'22 to 16 symbolic identity')
    r14,_,a14 = module(14,b,C)
    sub14 = {n:a14[n] for n in ['v','t']}
    kept = [0,1,2,3,6,7,8]
    for i,r in enumerate(r16):
        want = r14[kept.index(i)] if i in kept else 0
        must(r.subst(sub14).same(want),'16 to 14 symbolic identity')
    r13,_,a13 = module(13,b,C)
    modulus = {'J':a14['M']-b*Poly.v('o')}
    for j,(i,factor) in enumerate([(0,4*b*b),(1,4*b*b),(2,4*b*b),(3,2*b),(4,1),(6,4*b*b)]):
        must(r13[j].subst(modulus).same(r14[i].subst(modulus)*factor),'14 to 13 scaled symbolic identity')
    must(r14[5].subst(modulus).same(0),'eliminated modulus identity')
    receipt['checks']['elimination_identities'] = {'22_to_16':15,'16_to_14':9,'14_to_13':7}
    # Direct sign-lemma algebra, beyond the substitution identities.
    aa,bb,xx,yy = [Poly.v(n) for n in ['a','b','x0','y0']]
    must((xx**2-(yy*(aa-bb))**2 - (xx**2-1-(aa**2-1)*yy**2)).same((2*aa*bb-bb**2-1)*yy**2+1),'h positive square-difference identity')
    fixture_count,roundtrips,old_shifts,perturbations = 0,0,0,0
    fixture_rows = []
    for b,Cn,multiple in [(2,1,1),(2,1,2),(3,1,1),(4,1,1),(6,1,1),(2,2,1)]:
        original = fixture(b,Cn,multiple)
        qb = []
        for k in [0,1,3,17]:
            f = family(original,Cn,k)
            qb.append(f['q_b'])
            for arity in [22,16,14,13]:
                rr,leaves,_ = module(arity,Poly(b),Poly.v('C'))
                values = {n:f[n] for n in leaves}
                must(all(r.at(values|{'C':Cn})==0 for r in rr),'complete fixed-base fixture')
                rv,_,_ = module(arity,Poly.v('B')+1,Poly.v('C'))
                must(all(r.at(values|{'C':Cn,'B':b-1})==0 for r in rv),'complete variable-base fixture')
                restored = reconstruct(arity,values,b,Cn)
                must(all(restored[n]==f[n] for n in module(22,Poly(b),Poly.v('C'))[1]),'restriction-reconstruction exact inverse')
                fixture_count += 2
                roundtrips += 1
            # Old signed-pair quotient normalization with unequal common shifts.
            for shifts in [(0,0,0,0),(1,4,2,7),(9,3,11,5)]:
                for q,shift,scale,z,residue in zip(
                    ['q_alpha','q_sigma','q_tau','q_r'],shifts,[f['u'],f['u'],4*f['y'],f['M']],
                    [f['beta_plus']+1,f['s'],f['t'],f['x']-f['y']*(f['alpha_plus']+1-b)],
                    [f['alpha_plus']+1,f['x'],Cn,b*f['o']]):
                    first,second = shift,shift+f[q+'_plus']-1
                    must(first>=0 and second>=0 and z+scale*first-residue-scale*second==0,'old common-shift embedding')
                    must(second-first==f[q+'_plus']-1,'old normalization recovery')
                old_shifts += 1
        must(qb==[original['q_b']+original['u']*k for k in [0,1,3,17]],'retained qb infinite-family increment')
        # Mutation checks are diagnostics, not proof of isolation.
        rr,leaves,_ = module(22,Poly(b),Poly.v('C'))
        for leaf in leaves:
            changed = dict(original,C=Cn)
            changed[leaf] += 1
            must(any(r.at(changed)!=0 for r in rr),'single baseline leaf perturbation detected')
            perturbations += 1
        fixture_rows.append({'base':b,'index':Cn,'auxiliary_pell_index_multiple':multiple,'max_bit_length':max(z.bit_length() for z in original.values())})
    receipt['checks']['fixtures'] = {'complete_module_evaluations':fixture_count,'reconstruction_roundtrips':roundtrips,'old_shift_tuples':old_shifts,'perturbations':perturbations,'sources':fixture_rows}
    # An entire infinite family is checked as a polynomial in k for each module.
    k = Poly.v('k')
    symbolic = fixture(2,1)
    symbolic.update(beta_plus=16+2308*k,s=17+2308*k,q_b=4+577*k,q_alpha_plus=1+4*k,q_sigma_plus=1+4*k,C=1)
    family_identities = 0
    for arity in [22,16,14,13]:
        rr,_,_ = module(arity,Poly(2),Poly.v('C'))
        for r in rr:
            must(r.subst(symbolic).same(0),'explicit infinite family identity')
            family_identities += 1
    receipt['checks']['infinite_family_polynomial_identities'] = family_identities
    rational_cases = 0
    for d in range(1,49):
        for A in range(1,321):
            alpha = Fraction(A,d)
            if (alpha*alpha).denominator==1:
                must(alpha.denominator==1,'rational integer-square fixture')
            rational_cases += 1
    receipt['checks']['rational_integer_square_cases'] = rational_cases
    # One generic induction step proves the Pell invariant algebraically.
    x,y,z = [Poly.v(n) for n in ['px','py','z']]
    nx,ny = z*x+(z*z-1)*y,x+z*y
    must((nx*nx-(z*z-1)*ny*ny).same(x*x-(z*z-1)*y*y),'generic Pell induction invariant')
    receipt['checks']['pell_generic_induction_identity'] = True
    # Composition is algebra only; accepted classes are hand-specified, never simulated.
    compositions,clip_cases = [],0
    for T,accepted in [(0,set()),(0,{1}),(1,set()),(1,{1,3}),(1,{1,2,3,4}),(2,{1,2,3}),(2,set(range(1,10)))]:
        inner_r = compressed(T,accepted)
        inner = sos(inner_r)
        K = T+1
        for A in range(1,K+4):
            for Bc in range(1,K+4):
                u,v = min(A,K),min(Bc,K)
                j = (u-1)*K+v
                values = dict(counterA=A,counterB=Bc,selector=j,slackA=A-u+1,slackB=Bc-v+1)
                must((inner.at(values)==0)==(j in accepted),'finite clipped algebra table fixture')
                clip_cases += 1
        for arity,D in [(22,12),(16,12),(14,16),(13,16)]:
            lr,ll,_ = module(arity,Poly(2),Poly.v('counterA'))
            rr,rl,_ = module(arity,Poly(2),Poly.v('counterB'))
            lr = [r.subst({n:Poly.v('L_'+n) for n in ll}) for r in lr]
            rr = [r.subst({n:Poly.v('R_'+n) for n in rl}) for r in rr]
            gaps = [Poly.v(n) for n in ['gap1','gap2','gap3']]
            totalgap = sum(gaps,Poly(0))
            gap_r = [(20*gaps[0]-totalgap)*Poly.v('L_o')-2*totalgap,
                     (20*gaps[2]-totalgap)*Poly.v('R_o')-2*totalgap]
            all_r = lr+rr+gap_r+inner_r
            total = sos(all_r)
            witnesses = {'counterA','counterB','selector','slackA','slackB'}|{'L_'+n for n in ll}|{'R_'+n for n in rl}
            must(len(witnesses)==2*arity+5 and len(all_r)==2*len(lr)+8,'composition declared ledger')
            must(total.names()==witnesses|{'gap1','gap2','gap3'},'composition live ledger')
            must(total.degree()==max(D,inner.degree()),'composition exact joint degree')
            f = fixture(2,1)
            values = {'L_'+n:f[n] for n in ll}|{'R_'+n:f[n] for n in rl}
            values.update(counterA=1,counterB=1,selector=1,slackA=1,slackB=1,gap1=3,gap2=14,gap3=3)
            must((total.at(values)==0)==(1 in accepted),'complete composed gap fixture')
            compositions.append({'module_leaves':arity,'horizon':T,'accepted':sorted(accepted),'witnesses':len(witnesses),'residual_slots':len(all_r),'degree':total.degree(),'compressed_degree':inner.degree()})
    receipt['checks']['compositions'] = compositions
    receipt['checks']['compressed_finite_clipping_cases'] = clip_cases
    after = source_snapshot(root)
    must(before==after,'frozen source hashes, modes, sizes and mtimes preserved')
    receipt['preservation'] = {'entries':len(before),'identical_before_after':True,'atime_excluded':'read access may update atime; required modes, bytes and mtimes preserved'}
    receipt['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (out/'source_snapshot.json').write_text(json.dumps(before,indent=2)+'\n')
    receipt['status'] = 'PASS'
    (out/'results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','modules':len(modules),'complete_module_evaluations':fixture_count,'reconstruction_roundtrips':roundtrips,'compositions':len(compositions),'source_unchanged':True},indent=2))


if __name__=='__main__':
    main()
