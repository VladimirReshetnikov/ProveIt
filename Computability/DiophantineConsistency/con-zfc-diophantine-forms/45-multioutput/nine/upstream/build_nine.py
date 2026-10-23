#!/usr/bin/env python3
"""Wave5 nu31 Jones circuits with signed finalizer and completed-square bounds.
Derived from packages27,28,30, pinned in SOURCE_PINS.json. Standard library.
Fixed coefficients are recipes, not variables. No kernel-check or minimum claim.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
from itertools import product
from math import factorial,comb
import json,gzip,hashlib
ROOT=Path(__file__).resolve().parent
HORNER_PRIORITY=[1216820, -499253, 264672, 1450889, 2253367, -1266077, 895613, -1597971, 1681100, -2247850, 761134, 2665496, 1885814, 9149, -2722096, -2423428, 2247402, 1702726, 453763, -602406, 2758381, 3462067, 3015400, 1182051, -1158413, 695814, -422716, 625369, -1692869, 1951730, 674285, 1417079, 449393]
def add(p, q):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, 0) + c
        if not r[a]:
            del r[a]
    return r


def mul(p, q):
    r = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            r[tuple(x + y for x, y in zip(a, b))] += c * d
    return {a: c for a, c in r.items() if c}


def shift_term(a, c, n):
    """Substitute the first n coordinates by X+1; leave fixed ports alone."""
    active = [(i, e) for i, e in enumerate(a[:n]) if e]
    for chosen in product(*(range(e + 1) for _, e in active)):
        b = [0] * n + list(a[n:])
        d = c
        for (i, e), f in zip(active, chosen):
            b[i] = f
            d *= comb(e, f)
        yield tuple(b), d


def shift(p, n):
    r = defaultdict(int)
    for a, c in p.items():
        for b, d in shift_term(a, c, n):
            r[b] += d
    return {a: c for a, c in r.items() if c}


def build_parent(parent):
    n = len(parent['variables'])
    residuals = []
    shifted = []
    total = {}
    for eq in parent['equations']:
        r = {tuple(t['powers']): t['coefficient'] for t in eq['terms']}
        if any(sum(a[:n]) > 2 for a in r):
            raise ValueError('Parent contains a residual above degree two')
        rs = shift(r, n)
        residuals.append(r)
        shifted.append(rs)
        total = add(total, mul(rs, rs))
    grouped = defaultdict(dict)
    for a, c in total.items():
        grouped[(0,) + a[:n]][a[n:]] = c
    weighted = {}
    for a, poly in grouped.items():
        k0 = 4 - sum(a)
        if k0 < 0:
            raise ValueError('Parent sum of squares exceeds degree four')
        fac = factorial(k0)
        for e in a:
            fac *= factorial(e)
        weighted[a] = {p: fac * c for p, c in poly.items()}
    return residuals, shifted, total, dict(grouped), weighted


def sparse_records(poly):
    return [{'powers': list(a), 'coefficient': c}
            for a, c in sorted(poly.items())]


def polynomial_value(poly, values, modulus=None):
    out = 0
    for a, c in poly.items():
        term = c
        for v, e in zip(values, a):
            term *= pow(v, e, modulus) if modulus else v ** e
            if modulus:
                term %= modulus
        out += term
        if modulus:
            out %= modulus
    return out


def exponent_vector_compositions(length, total):
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in exponent_vector_compositions(length - 1, total - first):
            yield (first,) + tail


def all_alphas(nu):
    for degree in range(5):
        yield from exponent_vector_compositions(nu + 1, degree)


def expo(a):
    return sum(e * 5 ** j for j, e in enumerate(a))


class DAG:
    """Hash-consed binary arithmetic DAG; no division or variable powers."""
    def __init__(self):
        self.nodes = []
        self.cache = {}
        self.pow_cache = {}
        self.known = {}
        self.names = {}

    def node(self, obj):
        key = json.dumps(obj, sort_keys=True, separators=(',', ':'))
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(obj)
        return self.cache[key]

    def const(self, value):
        i = self.node({'kind': 'literal', 'value': value})
        self.known[i] = value
        return i

    def fixed(self, name):
        return self.node({'kind': 'fixed', 'name': name})

    def var(self, name):
        return self.node({'kind': 'variable', 'name': name})

    def op(self, op, a, b):
        ka, kb = self.known.get(a), self.known.get(b)
        if ka is not None and kb is not None:
            return self.const({'add': lambda: ka + kb,
                               'sub': lambda: ka - kb,
                               'mul': lambda: ka * kb}[op]())
        if op == 'add':
            if ka == 0: return b
            if kb == 0: return a
        if op == 'sub' and kb == 0: return a
        if op == 'mul':
            if ka == 0 or kb == 0: return self.const(0)
            if ka == 1: return b
            if kb == 1: return a
        if op in ('add', 'mul') and a > b:
            a, b = b, a
        return self.node({'kind': op, 'left': a, 'right': b})

    def plus(self, *args):
        out = self.const(0)
        for a in args: out = self.op('add', out, a)
        return out

    def times(self, *args):
        out = self.const(1)
        for a in args: out = self.op('mul', out, a)
        return out

    def minus(self, a, b):
        return self.op('sub', a, b)

    def power(self, a, e):
        if not isinstance(e, int) or e < 0:
            raise ValueError('Only fixed nonnegative integer exponents')
        key = (a, e)
        if key in self.pow_cache: return self.pow_cache[key]
        if e == 0: out = self.const(1)
        elif e == 1: out = a
        else:
            half = self.power(a, e // 2)
            out = self.times(half, half)
            if e % 2: out = self.times(out, a)
        self.pow_cache[key] = out
        return out

    def geometric(self, a, e):
        """1+a+...+a^(e-1), using a finite O(log e) addition circuit."""
        if e == 0: return self.const(0)
        if e == 1: return self.const(1)
        half = e // 2
        val = self.times(self.geometric(a, half),
                         self.plus(self.const(1), self.power(a, half)))
        if e % 2: val = self.plus(val, self.power(a, 2 * half))
        return val

    def save(self, name, value):
        self.names[name] = value
        return value

    def prune(self, root):
        live, todo = set(), [root]
        while todo:
            i = todo.pop()
            if i in live: continue
            live.add(i)
            n = self.nodes[i]
            if n['kind'] in ('add', 'sub', 'mul'):
                todo += [n['left'], n['right']]
        remap = {old: new for new, old in enumerate(sorted(live))}
        nodes = []
        for old in sorted(live):
            n = dict(self.nodes[old])
            if n['kind'] in ('add', 'sub', 'mul'):
                n['left'], n['right'] = remap[n['left']], remap[n['right']]
            nodes.append(n)
        return nodes, remap[root], {k: remap[v] for k, v in self.names.items() if v in live}


def coding_blocks(d, B, nu, keys, z):
    A,M,P,c=d.plus,d.times,d.power,d.const
    # t[j] = B^(5^j), by repeated fifth powers.
    t=[B]
    for _ in range(nu+1):
        t.append(M(P(t[-1],4),t[-1]))
    # v[j]=B^(5^nu-5^j). Reuse fourth powers from t construction.
    v=[None]*(nu+1);v[nu]=c(1)
    for j in range(nu-1,-1,-1):
        v[j]=M(P(t[j],4),v[j+1])
    variables=[t[nu]]+v
    hs=[c(1)]+[c(0)]*4
    for term in variables:
        for deg in range(1,5): hs[deg]=A(hs[deg],M(term,hs[deg-1]))
    baseline=hs[4]
    # Greedy recursive multivariate Horner. Coefficient leaves remain fixed.
    terms=[((4-sum(alpha),)+tuple(alpha),(d.const(name) if isinstance(name,int) else d.fixed(name))) for alpha,name in keys]
    @lru_cache(None)
    def horner(terms):
        if not terms:return c(0)
        positive=[sum(ex[j]>0 for ex,coef in terms) for j in range(len(variables))]
        m=max(positive)
        if m==0:return A(*(coef for ex,coef in terms))
        j=max((j for j in range(len(variables)) if positive[j]),key=lambda j:(positive[j]*1000000+HORNER_PRIORITY[j],sum(ex[j] for ex,coef in terms),j))
        yes=[];no=[]
        for ex,coef in terms:
            if ex[j]:
                ex=list(ex);ex[j]-=1;yes.append((tuple(ex),coef))
            else:no.append((ex,coef))
        return A(horner(tuple(no)),M(variables[j],horner(tuple(yes))))
    e=M(t[nu],A(M(z,baseline),horner(tuple(terms))))
    # S_(5^k)(B)=prod_j S_5(t_j), then S_(4L)=S_L(1+q)(1+q^2).
    factors=[]
    for j in range(nu+1):
        x=t[j]
        factors.append(A(c(1),M(A(P(x,2),x),A(c(1),P(x,2)))))
    q=t[nu+1]
    lam=M(*factors,A(c(1),q),A(c(1),P(q,2)))
    ell=A(*t[1:nu+1])
    return q,ell,lam,e,t[nu]

def make_body(nu, coefficient_keys, weights='sharp', positive=False, certificate=False):
    d = DAG()
    c = d.const
    A, M, S, P = d.plus, d.times, d.minus, d.power
    input_names=['epsilon','g0','h0','s0','w0','phi','i0','j0','n']
    positive_names=['epsilon_plus','g','h','s','w','phi_plus','i','j','n_plus']
    v={name:d.var(positive_names[k] if positive else name) for k,name in enumerate(input_names)}
    z, y = d.fixed('z_index'), d.fixed('y_index')
    b = d.save('b', A(y,v['epsilon']) if positive else A(y,c(1),v['epsilon']))
    g, h, s, w, ii, jj = ((v[key] if positive else A(v[key],c(1))) for key in
                         ['g0', 'h0', 's0', 'w0', 'i0', 'j0'])
    phi=S(v['phi'],c(1)) if positive else v['phi']
    nfinal=S(v['n'],c(1)) if positive else v['n']
    B = d.save('B', P(b,5))
    L = 5 ** (nu + 1)
    q,ell,lam,e,top=coding_blocks(d,B,nu,coefficient_keys,z)
    for name,value in [('q',q),('ell',ell),('lambda',lam),('e',e)]: d.save(name,value)
    theta = S(B, M(c(2), z))
    N = d.save('N', P(q, 16))
    Gcap = d.save('Gcap', M(c(32), b, top))
    Rleft=A(g,M(P(q,3),A(e,M(ell,P(q,2)),M(P(q,4),A(M(c(2),S(e,M(z,lam)),P(A(c(1),B,g),4)),M(lam,B),M(lam,B,P(q,4)))))))
    Rright=A(M(P(q,3),A(c(1),M(theta,lam))),M(ell,S(c(1),b)),M(S(B,c(2)),P(q,8)))
    R = d.save('R', A(M(Rleft, S(P(N, 2), N)),
                       M(Rright, S(P(N, 2), c(1)))))
    U = d.save('U', M(P(N, 2), w))
    Y = d.save('Y', M(P(N, 2), s))
    MM = d.save('M', M(R, Y))
    PP = d.save('P', M(c(2), P(MM, 2), U))
    K = d.save('K', A(R, c(1), M(h, S(PP, c(1)))))
    AA = d.save('A', M(MM, A(U, c(1))))
    Bprime = A(M(c(2), R), c(1))
    Wsmall = d.save('Wsmall', M(b, w))
    CC = d.save('C', A(Bprime, Wsmall, phi))
    JJ = d.save('J', S(M(c(4), AA), c(5)))
    QQ = d.save('Q', S(M(c(3), Wsmall, CC), M(c(2), S(P(Wsmall, 2), c(1)))))
    DD = d.save('D', A(M(S(P(AA, 2), c(1)), P(CC, 2)), c(1)))
    EE = d.save('E', M(ii, JJ, DD, P(CC, 2)))
    FF = d.save('F', A(M(S(P(AA, 2), c(1)), P(EE, 2)), c(1)))
    Gp = d.save('Gp', A(AA, M(FF, S(A(M(CC, DD), c(1)), AA))))
    HH = d.save('H', A(Bprime, M(jj, CC)))
    II = d.save('I', A(M(S(P(Gp, 2), c(1)), P(HH, 2)), c(1)))
    a0 = d.save('a0', A(S(P(M(PP,K),2),P(K,2)),c(1)))
    a1 = d.save('a1', M(DD, FF, II))
    if weights in ('structured','sharp'):
        divisor = d.save('divisor', M(JJ, FF))
        dividend = d.save('dividend', A(M(QQ, FF), M(JJ, S(HH, CC))))
        divbound = d.save('division_bound', A(P(QQ, 2), P(S(HH, CC), 2), c(1)))
    else:
        divisor = d.save('divisor', P(M(JJ, FF), 2))
        dividend = d.save('dividend', P(A(M(QQ, FF), M(JJ, S(HH, CC))), 2))
    margin = d.save('margin', S(S(M(P(K, 2), Gcap),
                               M(c(4), P(S(CC, M(K, Y)), 2), Gcap)),
                             M(c(8), g, P(K, 2))))
    if weights == 'literal':
        V0 = d.save('V0', A(P(a0, 2), c(2)))
        V1 = d.save('V1', A(P(a1, 2), c(2)))
    elif weights in ('structured','sharp'):
        # A=R*Y*(U+1), C=2R+1+bw+phi. All eight outer variables are nonnegative.
        # These bounds use the unconditional R!=0 and |A|>=2 lemmas.
        r = d.save('r_positive', A(Wsmall, phi))
        psmall = d.save('A_scale', M(Y, A(U, c(1))))
        MD = d.save('majorant_D', M(psmall, A(P(R, 2), P(CC, 2))))
        MF = d.save('majorant_F', A(M(AA, EE), c(1)))
        ch = d.save('majorant_CH', A(M(A(jj, c(2)), P(CC, 2)), P(r, 2)))
        MI = d.save('majorant_I', A(S(M(FF, A(M(DD, ch), M(c(2), P(HH, 2)),
                                                  P(AA, 2))), P(AA, 2)), c(1)))
        if weights=='sharp':
            MD=d.save('majorant_D',A(M(AA,CC),M(psmall,P(A(r,c(1)),2)),c(1)))
            ch=d.save('majorant_CH',A(M(CC,HH),P(r,2)))
            MI=d.save('majorant_I',A(S(M(FF,A(M(DD,ch),M(c(2),P(HH,2)),P(AA,2))),P(AA,2)),c(1)))
        V0 = d.save('V0', A(M(PP, K), c(1)))
        V1 = d.save('V1', A(M(MD, MF, MI), c(1)))
    elif weights == 'majorant':
        V0 = d.save('V0', A(P(PP, 2), P(K, 2), c(2)))
        V1 = d.save('V1', A(M(A(P(AA, 2), P(CC, 2), c(1)),
                              A(P(AA, 2), P(EE, 2), c(1)),
                              A(P(Gp, 2), P(HH, 2), c(1))), c(1)))
    else:
        raise ValueError('Unknown weight choice')
    WW = d.save('W', M(divisor, S(M(c(2), margin), c(1))))
    if weights in ('structured','sharp'):
        TT = d.save('T', S(A(M(divisor, A(nfinal, divbound)), dividend),
                           M(WW, A(M(c(2), divbound), M(V0, V1)))))
    else:
        TT = d.save('T', S(A(M(divisor,nfinal), dividend),
                           M(WW, A(dividend, M(V0, V1)))))
    if certificate and weights=='sharp':
        # Exact telescoping certificate for the only top-degree cancellation.
        t=M(psmall,P(A(r,c(1)),2))
        deltaD=d.save('deltaD',A(M(c(2),AA,CC,t),P(t,2),M(c(2),AA,CC),M(c(2),t),P(CC,2)))
        deltaF=d.save('deltaF',A(M(c(2),AA,EE),P(EE,2)))
        mi_minus_gh=d.save('mi_minus_gh',A(M(FF,DD,P(r,2)),M(c(2),FF,P(HH,2)),M(S(FF,c(1)),P(AA,2)),c(1),S(c(0),M(FF,HH)),M(AA,S(FF,c(1)),HH)))
        deltaI=d.save('deltaI',S(A(M(mi_minus_gh,A(MI,M(Gp,HH))),P(HH,2)),c(1)))
        deltaV=d.save('deltaV',A(M(deltaD,P(MF,2),P(MI,2)),M(DD,deltaF,P(MI,2)),M(DD,FF,deltaI),M(c(2),MD,MF,MI),c(1)))
        E0=d.save('E0',S(A(M(divisor,A(nfinal,divbound)),dividend),M(c(2),WW,divbound)))
        inner=d.save('inner',S(A(P(E0,2),S(c(0),M(c(2),E0,WW,V0,V1)),M(P(WW,2),P(V0,2),deltaV)),M(P(WW,2),a0)))
    else:
        inner=d.save('inner',S(P(TT,2),M(P(WW,2),A(a0,M(P(V0,2),a1)))))
    output=d.save('output',S(P(inner,2),M(c(4),P(M(P(WW,2),V0),2),a0,a1)))
    nodes, root, names = d.prune(output)
    return {'nu': nu, 'L': L, 'coefficient_binding':{'path_base':'package_root','manifest':'INSTANCE.json','tuple':'wang943-compact-5pow10','fixed_recipes':'nine/source/30-quartic31/nine/nu31/COMPACT_CONSTANTS.json'}, 'weights': weights,'degree_certificate':certificate,
            'variables': positive_names if positive else input_names, 'domain':'positive integers' if positive else 'nonnegative integers', 'nodes': nodes, 'output': root,
            'named_nodes': names,
            'operation_counts': {kind: sum(n['kind'] == kind for n in nodes)
                                 for kind in ['add', 'sub', 'mul']},
            'model': 'Binary +,-,*; squaring and fixed-coefficient multiplication charged; fixed integer recipes not evaluated.'}

def canonical_coefficients(constants):
    """Fold literal coefficient recipes and alias identical fixed-port polynomials."""
    canonical={};keys=[];aliases={}
    for row in constants['coefficient_records']:
        recipe=row['coefficient_polynomial_in_fixed_ports']
        signature=json.dumps(recipe,sort_keys=True,separators=(',',':'))
        if len(recipe)==1 and not any(recipe[0]['powers']):
            name=recipe[0]['coefficient']
            aliases[row['name']]={'literal':name}
        else:
            name=canonical.setdefault(signature,row['name'])
            aliases[row['name']]={'fixed':name}
        keys.append((tuple(row['alpha']),name))
    return keys,aliases
def evaluate_dag(body, fixed, variables, modulus):
    vals = []
    for node in body['nodes']:
        k = node['kind']
        if k == 'literal': value = node['value']
        elif k == 'fixed': value = fixed[node['name']]
        elif k == 'variable': value = variables[node['name']]
        elif k == 'add': value = vals[node['left']] + vals[node['right']]
        elif k == 'sub': value = vals[node['left']] - vals[node['right']]
        elif k == 'mul': value = vals[node['left']] * vals[node['right']]
        else: raise ValueError(k)
        vals.append(value % modulus)
    return vals[body['output']], {name: vals[i] for name, i in body['named_nodes'].items()}


def run():
    constants=json.loads((ROOT/'source/30-quartic31/nine/nu31/COMPACT_CONSTANTS.json').read_text())
    keys,aliases=canonical_coefficients(constants)
    out=ROOT/'generated';out.mkdir(exist_ok=True)
    (out/'COEFFICIENT_ALIASES.json').write_text(json.dumps(aliases,indent=2)+'\n')
    z=1<<constants['index_exponent'];raw=z.to_bytes((z.bit_length()+7)//8,'little')
    (out/'z_index.bin').write_bytes(raw);(out/'z_index.bin.gz').write_bytes(gzip.compress(raw,mtime=0))
    (out/'Z_MATERIALIZATION.json').write_text(json.dumps(dict(definition='2^45933757',encoding='unsigned little-endian, minimal bytes',bytes=len(raw),bit_length=z.bit_length(),sha256=hashlib.sha256(raw).hexdigest()),indent=2)+'\n')
    ledger={}
    for weight in ['structured','sharp']:
      for positive in [False,True]:
        body=make_body(31,keys,weight,positive)
        name=weight+('_positive' if positive else '_natural')
        (out/f'nine_{name}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
        ledger[name]={'operations':sum(body['operation_counts'].values()),'operation_counts':body['operation_counts'],'fixed_leaves':sum(n['kind']=='fixed' for n in body['nodes']),'degree':(92324*5**32+296 if weight=='sharp' else 93264*5**32+288)}
    cert=make_body(31,keys,'sharp',False,True)
    (out/'nine_sharp_degree_certificate.json').write_text(json.dumps(cert,separators=(',',':'))+'\n')
    (out/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print(json.dumps(ledger,indent=2))
if __name__=='__main__':run()

