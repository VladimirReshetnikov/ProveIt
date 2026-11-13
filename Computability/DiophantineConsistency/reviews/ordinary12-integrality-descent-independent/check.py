#!/usr/bin/env python3
"""Independent exact checks of the proposed ordinary-tail descent."""
from collections import Counter
from itertools import product
from math import gcd, isqrt
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
AUTHOR = BASE / 'research/ordinary12-ipra-bridge/integrality-descent-analysis'
GRAPH = BASE / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'


def need(ok, message):
    if not ok: raise ValueError(message)


# Sparse monomials are sorted tuples of variable names, rather than the
# exponent-vector implementation used in the author's check.
class Poly:
    def __init__(self, data): self.data = {m:c for m,c in data.items() if c}
    @staticmethod
    def var(name): return Poly({(name,):1})
    @staticmethod
    def lift(x): return x if isinstance(x, Poly) else Poly({():x})
    def __add__(self, other):
        d = Counter(self.data); d.update(self.lift(other).data); return Poly(d)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.data.items()})
    def __sub__(self, other): return self + -self.lift(other)
    def __rsub__(self, other): return self.lift(other) + -self
    def __mul__(self, other):
        d = Counter()
        for (m,c),(n,e) in product(self.data.items(), self.lift(other).data.items()):
            d[tuple(sorted(m+n))] += c*e
        return Poly(d)
    __rmul__ = __mul__
    def __pow__(self, n):
        p = self.lift(1)
        for _ in range(n): p = p*self
        return p
    def __eq__(self, other): return self.data == self.lift(other).data


def main():
    pins = {'README.md':'1d3eaf5b90570ab1441d0d8f5b9c7bef1f81e0f53bd58eb2a66cd4fd98e59334',
            'check_identities.py':'020f8b2b8314cd4860beb3a3bb456fb964c1a628d4ca6402b15b6339148c45e3'}
    original = {}
    for name,digest in pins.items():
        ref = 'e5e341f1e2:'+(AUTHOR/name).relative_to(ROOT).as_posix()
        data = subprocess.run(['git','show',ref],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(data).hexdigest()==digest, 'reviewed historical source pin '+name)
        original[name] = data
    need(hashlib.sha256(GRAPH.read_bytes()).hexdigest()=='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22', 'graph source pin')
    Q,d,V,n,v,a,b,s,x,y = map(Poly.var, ('Q','d','V','n','v','a','b','s','x','y'))
    w = V+n; p = 1-Q; h = p*w*w+Q*V*V-1
    bn = 2*p*w; A = d*h+Q*p; N = A*A-d*Q*bn*bn
    D = d*bn; Y = w*D-A
    identities = {
        'cleared_auxiliary': Q*V*V*D*D-(Q-1)*Y*Y-D*D+(Q-1)*N,
        'polarized_tail': (d*h-Q*p)**2+4*d*Q*p*(Q*V*V-1)-N,
        'bezout_square': (a*x+b*y)**3-(a*a*(a*x**3+3*b*x*x*y)+b*b*(3*a*x*y*y+b*y**3)),
    }
    q = 1+b*b*s
    vp = (2*q-1)*v-2*b*s*a
    ap = (2*q-1)*a-2*q*v*b
    t = 2*b*s*a-2*q*v
    norm = lambda u,z: q*u*u*b*b-(q-1)*z*z-b*b
    identities['transformed_norm'] = norm(vp,ap)-norm(v,a)
    identities['numerator_shift'] = ap-a-b*t
    identities['bezout_update'] = ap*x+b*(y-t*x)-(a*x+b*y)
    for name,p0 in identities.items(): need(p0 == 0, 'identity '+name)
    need(identities['transformed_norm']+1 != 0, 'identity mutation control')

    graph = json.loads(GRAPH.read_bytes())
    rows = {row[0]:row for row in graph['source']}
    expected = [
        ['E','*','X','Y'], ['a','+','E','Y'], ['k','+','eta','zeta'],
        ['kY','*','Y','k'], ['c','+','eta','kY'], ['g15','*',4,'a'],
        ['H','+',3,'g15'], ['g17','*','a','a'], ['Delta','+','H','g17'],
        ['f','+',1,'t'], ['f2','*','f','f'], ['rho','-','f2',1],
        ['Q','*','Delta','rho'], ['c2','*','c','c'], ['den','*','c2','c2'],
        ['g73','*','T','c'], ['g74','-','g73','R'], ['g75','*','f2','g74'],
        ['V','-','g75','c']]
    need(graph['domain']=='strictly positive integers' and
         all(rows.get(r[0])==r for r in expected), 'graph hypothesis bindings')
    env = {'Q':Q,'den':d,'V':V,'n':n}
    started = False
    for name,op,l,r in graph['source']:
        if name == 'oneQ': started = True
        if not started: continue
        if name in env: continue
        if any(type(z) is not int and z not in env for z in (l,r)): continue
        l = Poly.lift(l) if type(l) is int else env[l]
        r = Poly.lift(r) if type(r) is int else env[r]
        env[name] = l+r if op=='+' else l-r if op=='-' else l*r
        if name == 'N': break
    need(env['N'] == N, '95-gate polarized literal tail')
    need(env['N'] != N+1, 'graph mutation control')

    # Enumerate every possible square a in the stated finite ranges by exact
    # division and integer square root, including all reduced states.
    states = steps = 0; max_v = 0
    for qi,bi,vi in product(range(2,26),range(1,13),range(1,101)):
        numerator = qi*vi*vi*bi*bi-bi*bi
        ai2, rem = divmod(numerator,qi-1)
        if rem: continue
        ai = isqrt(ai2)
        if ai*ai != ai2 or gcd(ai,bi) != 1: continue
        states += 1; max_v = max(max_v,vi)
        need((qi-1)%(bi*bi)==0, 'b² divisibility')
        if vi == 1:
            need(ai==bi==1, 'base case'); continue
        need(ai>vi*bi and qi*vi*bi>(qi-1)*ai, 'strict inequalities')
        si=(qi-1)//(bi*bi)
        vx=(2*qi-1)*vi-2*bi*si*ai
        ax=(2*qi-1)*ai-2*qi*vi*bi
        need(0<abs(vx)<vi and ax!=0, 'strict signed descent')
        need(gcd(abs(ax),bi)==1, 'updated coprimality')
        need(qi*vx*vx*bi*bi==(qi-1)*ax*ax+bi*bi, 'updated norm')
        steps += 1

    # Exhaust the original cleared equation with signs independently of gcd
    # normalization. D=0 is intentionally excluded from the claim.
    signed_states = 0
    for qi,vi,yi,di in product(range(2,9),range(-7,8),range(-25,26),range(-8,9)):
        if di == 0 or qi*vi*vi*di*di != (qi-1)*yi*yi+di*di: continue
        signed_states += 1
        need(vi!=0 and yi!=0 and yi%di==0, 'signed cleared equation')
    need(1*1*1*2*2==(1-1)*1*1+2*2 and 1%2!=0, 'Q=1 counterexample')
    # The weaker generic assumptions Q>1, d=c^4>0, n>0, N=0 do not
    # suffice for bn!=0: this is not claimed to be a full graph valuation.
    qi,di,ci,ni,Vi = 16,16,2,1,-1
    wi=ni+Vi; bni=2*(1-qi)*wi
    Ai=di*((1-qi)*wi*wi+qi*Vi*Vi-1)+qi*(1-qi)
    need(di==ci**4 and qi>1 and ni>0 and Ai*Ai-di*qi*bni*bni==0 and bni==0,
         'missing nonzero premise control')

    # Demonstrate precisely why an optimized author-checker run is not a
    # verification: append a deliberately false assertion to a temporary copy.
    source=original['check_identities.py'].decode()
    with tempfile.TemporaryDirectory(prefix='ordinary12-audit-') as td:
        altered=Path(td)/'mutated.py'; altered.write_text(source+'\nassert False, "audit mutation"\n')
        authored=Path(td)/'original.py'; authored.write_text(source)
        author=subprocess.run([sys.executable,'-B',str(authored)],capture_output=True,text=True)
        normal=subprocess.run([sys.executable,'-B',str(altered)],capture_output=True,text=True)
        optimized=subprocess.run([sys.executable,'-B','-O',str(altered)],capture_output=True,text=True)
    need(author.returncode==0 and normal.returncode!=0 and optimized.returncode==0, 'assert mutation behavior')
    result = {'status':'PASS','optimized':bool(sys.flags.optimize),
      'author_plan_sha256':pins['README.md'],
      'author_file_sha256':pins['check_identities.py'],
      'author_normal_exit':author.returncode,'author_normal_stdout':author.stdout.strip(),
      'false_assertion_mutation':{'normal_exit':normal.returncode,'optimized_exit':optimized.returncode,
                                  'optimized_stdout':optimized.stdout.strip()},
      'independent_exact_identities':list(identities),'graph_sha256':hashlib.sha256(GRAPH.read_bytes()).hexdigest(),
      'literal_95_gate_tail_identity':True,'graph_hypothesis_bindings':len(expected),
      'reduced_survey':{'q':[2,25],'b':[1,12],'v':[1,100],
          'states':states,'transformed_states':steps,'max_v':max_v},
      'signed_survey':{'q':[2,8],'v':[-7,7],'Y':[-25,25],'D':[-8,8],'D_excludes_zero':True,'states':signed_states},
      'q_equals_one_counterexample':{'q':1,'v':1,'Y':1,'D':2},
      'missing_bn_nonzero_counterexample':{'Q':qi,'d':di,'c':ci,'n':ni,'V':Vi,'full_graph_valuation':False},
      'scope':'Finite checks and polynomial identities only; no model least-number, graph transport, or iPRA proof.'}
    print(json.dumps(result,indent=2))


if __name__ == '__main__': main()
