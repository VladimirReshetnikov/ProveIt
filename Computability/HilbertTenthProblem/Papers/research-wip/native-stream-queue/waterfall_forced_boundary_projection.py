"""Complete natural quadratic certificates with forced Waterfall boundaries.

The external horizon counts source-TM instructions. This compiler does not
compress an unbounded history into fixed arity or improve the universal bound.
Original archive and source bytes are authenticated before use.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import io
import json
from math import prod
from pathlib import Path
import random
import subprocess
from types import ModuleType
from zipfile import ZipFile

ARCHIVE = 'Waterfall_Diophantine_Certificates.zip'
ARCHIVE_SHA256 = 'b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc'
SOURCE = 'waterfall-diophantine/replay/grouped_quadratic.py'
SOURCE_SHA256 = '506c7d8505e2076628b351a016104a3ad851a4178fa664709ae87774a645dc7f'
ARRIVAL = '24a743255'
SCOPE = ('Natural coordinates, exact externally fixed source-TM first-halt horizon; '
         'the fixed 46-clock frontend is represented through its proved macrosteps. '
         'No unbounded fixed-arity equation, arbitrary-program tape loader cost, '
         'universal operation improvement, or arithmetic optimality is claimed.')


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list):
        return len(a) == len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a == b


def key(k, mode):
    if type(k) is not int or k < 1: raise ValueError('The external horizon must be a positive integer')
    if type(mode) is not str or mode not in ('parent','prefix','ends'): raise ValueError('Unknown mode')
    if mode == 'ends' and k < 4: raise ValueError('Disjoint forced boundaries require k >= 4')
    return k,mode


@lru_cache(None)
def _parent_module():
    root = Path(__file__).resolve().parents[5]
    path = root/'docs'/'incoming'/ARCHIVE
    raw = path.read_bytes() if path.exists() else subprocess.run(
        ['git','show',f'{ARRIVAL}:docs/incoming/{ARCHIVE}'],cwd=root,
        capture_output=True,check=True,timeout=60).stdout
    if hashlib.sha256(raw).hexdigest() != ARCHIVE_SHA256:
        raise ValueError('Waterfall archive hash mismatch')
    with ZipFile(io.BytesIO(raw)) as z: code = z.read(SOURCE)
    if hashlib.sha256(code).hexdigest() != SOURCE_SHA256:
        raise ValueError('Waterfall compiler source hash mismatch')
    module = ModuleType('_waterfall_boundary_parent'); module.__file__ = SOURCE
    exec(compile(code,SOURCE,'exec'),module.__dict__)
    return module


def add(a,b,scale=1):
    out = dict(a)
    for name,c in b.items():
        out[name] = out.get(name,0)+scale*c
        if not out[name]: del out[name]
    return out


def const(c): return {'':c} if c else {}
def var(n): return {n:1}
def times(a,c): return {n:v*c for n,v in a.items() if v*c}
def serial(a): return tuple(sorted(a.items()))
def value(a,env): return sum(c*(env[n] if n else 1) for n,c in a)


def affine(p):
    assert p.degree <= 1
    return {m[0] if m else '':c for m,c in p.t.items()}


def full_polynomial(squares,products):
    out = {}
    for a,b in [(p,p) for _,p in squares]+[(a,b) for _,a,b in products]:
        for n,c in a:
            for m,d in b:
                mon = tuple(sorted(x for x in (n,m) if x))
                out[mon] = out.get(mon,0)+c*d
    return tuple((m,c) for m,c in sorted(out.items()) if c)


def schedule(squares,products):
    """Literal exact affine evaluation with shared gates, followed by finalization.

    Every binary +, -, * costs one. Integer constants/copies are free; scalar
    multiplication costs one unless its scalar is 0 or 1. No division/power
    oracle is used. The schedule is an achieved bound, not a global optimum.
    """
    rows = []; cache = {}; forms = {}
    def gate(op,a,b):
        if type(a) is int and type(b) is int:
            return a*b if op == '*' else a+b if op == '+' else a-b
        if op == '*':
            if a == 0 or b == 0: return 0
            if a == 1: return b
            if b == 1: return a
        if op == '+' and a == 0: return b
        if op in ('+','-') and b == 0: return a
        if op == '-' and a == b: return 0
        if op in ('+','*') and repr(b) < repr(a): a,b = b,a
        signature = op,a,b
        if signature not in cache:
            n = f'_g{len(rows)}'; rows.append((n,op,a,b)); cache[signature] = n
        return cache[signature]
    def total(terms):
        x = 0
        for t in terms: x = gate('+',x,t)
        return x
    def form(p):
        if p not in forms:
            pos = []; neg = []
            for n,c in p:
                t = gate('*',abs(c),n) if n else abs(c)
                (pos if c > 0 else neg).append(t)
            forms[p] = gate('-',total(pos),total(neg))
        return forms[p]
    square_values = tuple((n,form(p)) for n,p in squares)
    product_values = tuple((n,form(a),form(b)) for n,a,b in products)
    certificate_rows = len(rows)
    terms = [gate('*',p,p) for _,p in square_values]
    terms += [gate('*',a,b) for _,a,b in product_values]
    output = total(terms)
    used = {output} if type(output) is str else set()
    for n,op,a,b in reversed(rows):
        if n in used: used.update(x for x in (a,b) if type(x) is str)
    assert all(n in used for n,op,a,b in rows), 'unpaid/dead schedule rows'
    M = sum(op == '*' for n,op,a,b in rows)
    return dict(source=tuple(rows),output=output,squared_values=square_values,
        product_values=product_values,certificate_gate_count=certificate_rows,
        operations=len(rows),M=M,A=len(rows)-M)


@lru_cache(None)
def _build(k,mode):
    key(k,mode); m = _parent_module(); parent = m.DirectionalQuadratic(k)
    parameters = tuple(parent.parameters); original = tuple(parent.witnesses)
    rules = tuple(tuple(t) for t in m.RULES)
    assert len(rules) == 29 and rules[0] == (0,0,1,1,0)
    replacements = {}
    def select(j,q,s):
        selected = [i for i,t in enumerate(rules) if t[:2] == (q,s)]
        assert len(selected) == 1
        for i in range(29): replacements[f'e{j}_{i}'] = const(int(i == selected[0]))
    def control(j,field,direction=None):
        out = {}
        for i,t in enumerate(rules):
            if direction is None or t[3] == direction:
                out = add(out,var(f'e{j}_{i}'),t[field])
        return out
    def outputR(j):
        return add(add(times(var(f'YL{j}'),2),control(j,4,0)),var(f'QR{j}'))
    if mode != 'parent':
        select(0,0,0)
        for n in ('QL0','rL0','YL0'): replacements[n] = {}
        replacements['YR0'] = var('L0')
        if k >= 2: replacements['rR0'] = control(1,1)
    if mode == 'ends':
        suffix = ((6,0,7,0,0),(7,0,8,0,1),(8,1,9,0,1))
        for target in (9,8,7):
            assert len([r for r in rules if r[2] == target]) == 1
        for j,t,r in zip(range(k-3,k),suffix,(0,1,1)):
            assert t in rules
            select(j,*t[:2]); replacements[f'rL{j}'] = const(r)
            for name in ('QR','rR','YR'): replacements[f'{name}{j}'] = {}
            replacements[f'YL{j}'] = outputR(j-1)
        replacements[f'QL{k-3}'] = add(times(var(f'QL{k-2}'),2),const(1))
        replacements[f'QL{k-2}'] = add(times(var(f'QL{k-1}'),2),const(1))
    active = set()
    @lru_cache(None)
    def resolve(n):
        if n not in replacements: return serial(var(n))
        assert n not in active, 'cyclic restoration'
        active.add(n); out = {}
        for x,c in replacements[n].items():
            out = add(out,dict(resolve(x)) if x else const(1),c)
        active.remove(n); return serial(out)
    def substitute(p):
        out = {}
        for n,c in affine(p).items(): out = add(out,dict(resolve(n)) if n else const(1),c)
        return serial(out)
    witnesses = tuple(n for n in original if n not in replacements)
    restores = tuple((n,resolve(n)) for n in original if n in replacements)
    coordinates = parameters+witnesses
    assert all(c >= 0 and (not x or x in coordinates) for n,p in restores for x,c in p)
    old_squares = tuple((n,serial(affine(p))) for n,p in parent.squares)
    old_products = tuple((n,serial(affine(a)),serial(affine(b))) for n,a,b in parent.products)
    all_squares = tuple((n,substitute(p)) for n,p in parent.squares)
    all_products = tuple((n,substitute(a),substitute(b)) for n,a,b in parent.products)
    squares = tuple((n,p) for n,p in all_squares if p)
    products = tuple((n,a,b) for n,a,b in all_products if a and b)
    assert all(c >= 0 for n,a,b in products for x,c in a+b)
    if mode == 'parent': expected = (35*k,5*k+4,2*k)
    elif mode == 'prefix': expected = (35*k-33-int(k>=2),5*k-int(k>=2),2*k-2)
    else: expected = (35*k-138,5*k-15,2*k-8)
    assert (len(witnesses),len(squares),len(products)) == expected
    expanded = full_polynomial(squares,products)
    assert dict(expanded)[('tau','tau')] == 1
    slp = schedule(squares,products)
    return dict(horizon=k,mode=mode,parameters=parameters,witnesses=witnesses,
        parent_witnesses=original,restoration=restores,squares=squares,products=products,
        deleted_square_names=tuple(n for n,p in all_squares if not p),
        deleted_product_names=tuple(n for n,a,b in all_products if not a or not b),
        parent_squares=old_squares,parent_products=old_products,
        expanded_polynomial=expanded,**slp,
        ledger=dict(witnesses=len(witnesses),squares=len(squares),products=len(products),
                    degree=2,expanded_monomials=len(expanded),operations=slp['operations'],
                    M=slp['M'],A=slp['A']),
        domain='natural integers including zero',archive_sha256=ARCHIVE_SHA256,
        parent_source_sha256=SOURCE_SHA256,scope=SCOPE)


def build(k=7,mode='ends'):
    key(k,mode); return deepcopy(_build(k,mode))


def checked(compiled):
    if type(compiled) is not dict: raise ValueError('Expected complete canonical compiler output')
    k,mode = key(compiled.get('horizon'),compiled.get('mode'))
    if not exact(compiled,_build(k,mode)): raise ValueError('Noncanonical compiler output')
    return compiled


def assignment(names,env,natural=True):
    if type(env) is not dict or set(env) != set(names): raise ValueError('Wrong coordinate set')
    if any(type(n) is not str or type(v) is not int or natural and v < 0 for n,v in env.items()):
        raise ValueError('Coordinates must be exact integers in the declared domain')
    return dict(env)


def restore_assignment(compiled,env,*,signed=False):
    c = checked(compiled)
    if type(signed) is not bool: raise ValueError('signed must be Boolean')
    env = assignment(c['parameters']+c['witnesses'],env,not signed)
    env.update((n,value(p,env)) for n,p in c['restoration'])
    assert set(env) == set(c['parameters']+c['parent_witnesses'])
    return env


def energy(squares,products,env):
    return sum(value(p,env)**2 for n,p in squares)+sum(value(a,env)*value(b,env) for n,a,b in products)


def evaluate(compiled,env,*,signed=False):
    c = checked(compiled)
    if type(signed) is not bool: raise ValueError('signed must be Boolean')
    env = assignment(c['parameters']+c['witnesses'],env,not signed)
    for n,op,a,b in c['source']:
        x = env[a] if type(a) is str else a; y = env[b] if type(b) is str else b
        env[n] = x*y if op == '*' else x+y if op == '+' else x-y
    return env[c['output']] if type(c['output']) is str else c['output']


def project_assignment(compiled,env):
    c = checked(compiled)
    env = assignment(c['parameters']+c['parent_witnesses'],env)
    if energy(c['parent_squares'],c['parent_products'],env) != 0:
        raise ValueError('Projection requires a complete parent natural zero')
    out = {n:env[n] for n in c['parameters']+c['witnesses']}
    assert restore_assignment(c,out) == env and evaluate(c,out) == 0
    return out


def canonical_assignment(compiled,L,R):
    c = checked(compiled)
    if type(L) is not int or L < 0 or type(R) is not int or R < 0: raise ValueError('Natural half tapes required')
    m = _parent_module(); history,halt,end = m.tm_history(L,R,c['horizon'])
    if len(history) != c['horizon'] or not halt: return None
    old,halt,end = m.DirectionalQuadratic(c['horizon']).lift(L,R)
    assert halt
    return project_assignment(c,old)


def graph_identity(compiled,env):
    c = checked(compiled); old = restore_assignment(c,env,signed=True)
    lhs = energy(c['parent_squares'],c['parent_products'],old)
    rhs = evaluate(c,env,signed=True)
    return lhs,rhs


def verify():
    if not __debug__: raise RuntimeError('Assertions must be enabled')
    rng = random.Random(24646); counts = Counter(); records = []
    for k in (1,2,3,4,5,7,8,10):
        for mode in ('parent','prefix','ends'):
            if mode == 'ends' and k < 4: continue
            c = build(k,mode); records.append(dict(k=k,mode=mode,**c['ledger']))
            for _ in range(12):
                env = {n:rng.randrange(-3,5) for n in c['parameters']+c['witnesses']}
                a,b = graph_identity(c,env); assert a == b
                expanded = sum(coef*prod(env[n] for n in mon) for mon,coef in c['expanded_polynomial'])
                assert expanded == b; counts['signed_graph_and_expanded_identities'] += 1
            for _ in range(8):
                env = {n:rng.randrange(4) for n in c['parameters']+c['witnesses']}
                old = restore_assignment(c,env)
                assert all(v >= 0 for v in old.values())
                assert evaluate(c,env) >= 0; counts['global_natural_lifts'] += 1
    cases = []
    for L in range(16):
        for R in range(12):
            history,halt,end = _parent_module().tm_history(L,R,36)
            if halt and len(history) >= 4:
                k = len(history); c = build(k,'ends'); env = canonical_assignment(c,L,R)
                assert env is not None and evaluate(c,env) == 0
                assert project_assignment(c,restore_assignment(c,env)) == env
                counts['actual_first_halt_zero_bijections'] += 1
                if len(cases) < 8: cases.append(dict(L=L,R=R,k=k,C=env['C'],tau=env['tau']))
    c = build(); env = canonical_assignment(c,6,0)
    assert env['C'] == 189 and env['tau'] == 428
    for n in c['parameters']+c['witnesses']:
        changed = dict(env); changed[n] += 1
        # Input parameters can change the represented instance. Keep the
        # singleton-witness claim scoped to fixed source parameters.
        if n in c['witnesses'] or n in ('C','tau'):
            assert evaluate(c,changed) > 0; counts['single_coordinate_corruptions'] += 1
    rejected = 0
    def reject(fn):
        nonlocal rejected
        try: fn()
        except (ValueError,TypeError): rejected += 1
        else: raise AssertionError('Malformed public call accepted')
    for bad in (True,False,0,-1,1.0,'7',None): reject(lambda: build(bad,'prefix'))
    for bad in (True,None,'bad'): reject(lambda: build(7,bad))
    for k in (1,2,3): reject(lambda: build(k,'ends'))
    for n in c['parameters']+c['witnesses']:
        for bad in (True,1.0,-1):
            malformed = dict(env); malformed[n] = bad
            reject(lambda: evaluate(c,malformed))
    bad = deepcopy(c); bad['ledger']['degree'] = 2.0; reject(lambda: evaluate(bad,env))
    bad = deepcopy(c); bad['source'] = bad['source'][:-1]; reject(lambda: evaluate(bad,env))
    bad = deepcopy(c); bad['restoration'] = (); reject(lambda: restore_assignment(bad,env))
    bad = dict(env); bad['unused'] = 0; reject(lambda: evaluate(c,bad))
    reject(lambda: restore_assignment(c,env,signed=1))
    bad = restore_assignment(c,env); bad['e0_0'] = 0; reject(lambda: project_assignment(c,bad))
    counts['malformed_public_calls_rejected'] = rejected
    changed = build(); changed['ledger'].clear(); assert build() == c
    counts['owned_public_exports'] = 1
    return dict(status='PASS',archive_sha256=ARCHIVE_SHA256,parent_source_sha256=SOURCE_SHA256,
        counts=dict(counts),ledgers=records,first_halt_examples=cases,
        complete_seven_step_compiler=c,seven_step_zero=env,scope=SCOPE)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true'); args = parser.parse_args()
    result = verify(); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(path.read_text()) == json.loads(json.dumps(result))
    print(json.dumps({k:v for k,v in result.items() if k not in ('complete_seven_step_compiler','seven_step_zero')},indent=2))
