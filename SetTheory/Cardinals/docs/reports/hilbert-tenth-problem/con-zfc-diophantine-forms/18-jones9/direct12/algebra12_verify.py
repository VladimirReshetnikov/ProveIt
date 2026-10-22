"""Independent finite audits for the twelve-positive-variable circuit.

The exact degree proof and infinite-domain correctness theorem are in the
accompanying mathematical note.  These checks verify the emitted arithmetic
against a separately implemented three-radical norm and line restrictions.
Only the Python standard library is required.
"""
import json
import random
import sys
from pathlib import Path
sys.dont_write_bytecode = True
from algebra12_build import build, build_system, evaluate


def independent_norm(data, supplied):
    q = supplied['beta']*supplied['J']+1
    X = supplied['w']*q
    Y = supplied['s']*q**3
    E = X*Y
    k = supplied['eta']+supplied['zeta']
    c = k*Y+supplied['eta']
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    R = (((q-1)*(q-supplied['F'])+supplied['alpha'])*(q*q-1)
         +(supplied['MC']+q*supplied['MF'])*supplied['J'])
    Lfirst = E*k*Y
    A = 1+Lfirst*(Lfirst+k)
    I = H*supplied['i']*c*c
    D = 1+Delta*I*I
    Q = Delta*Delta*I*I
    d = Q-1
    v = c*supplied['T']
    z0 = c+R*D
    e = Q*(D*v*v+z0*z0)-1
    B = 2*Q*v*z0
    M = 2*(D+v*v)
    G = 1+Delta*c*c
    Ubound = M*(Lfirst+k+1)+2*(v*((a+2)*I+1)+z0)
    ell = 1+H*Ubound
    S = H*supplied['t']+ell*(a*c+X)
    W = H*M
    # Independent representation: index bits mean powers of r,f,tau.
    def multiply(x, y):
        out = [0]*8
        for ii, xx in enumerate(x):
            for jj, yy in enumerate(y):
                if xx == 0 or yy == 0:
                    continue
                coeff = xx*yy
                duplicate = ii & jj
                for bit, square in [(1,G),(2,D),(4,A)]:
                    if duplicate & bit:
                        coeff *= square
                out[ii ^ jj] += coeff
        return out
    term = [S, -ell, 0, 0, -W, 0, 0, 0]
    original = [d*x for x in multiply(term, term)]
    original[0] -= H*H*e
    original[2] += H*H*B
    result = original
    for flipped in [2, 4, 1]:
        conjugate = [-x if index & flipped else x
                     for index, x in enumerate(result)]
        result = multiply(result, conjugate)
    if any(result[1:]):
        raise RuntimeError('Norm retained a radical coefficient')
    return result[0]


def line_degree(artifact, prime):
    def trim(xs):
        while len(xs)>1 and xs[-1] == 0:
            xs.pop()
        return xs
    def plus(xs, ys, sign=1):
        out = [0]*max(len(xs), len(ys))
        for i, x in enumerate(xs): out[i] += x
        for i, y in enumerate(ys): out[i] += sign*y
        return trim([x % prime for x in out])
    def times(xs, ys):
        out = [0]*(len(xs)+len(ys)-1)
        for i,x in enumerate(xs):
            if x:
                for j,y in enumerate(ys):
                    out[i+j] += x*y
        return trim([x % prime for x in out])
    env = {v:[0,1] for v in artifact['unknowns']}
    env.update(beta=[3], Kconstant=[5], MC=[2], MF=[4])
    def val(x): return [x % prime] if isinstance(x,int) else env[x]
    for out, op, x, y in artifact['source']:
        xx, yy = val(x), val(y)
        env[out] = times(xx,yy) if op == '*' else plus(xx,yy, 1 if op=='+' else -1)
    return {'prime':prime, 'product_degree':len(env[artifact['output']])-1,
            'norm_degree':len(env[artifact['labels']['R12']])-1,
            'leading_coefficient':env[artifact['output']][-1]}


def main():
    artifact = build()
    system = build_system(artifact)
    rng = random.Random(20261022)
    result = {'identity_cases':0, 'degree_diagnostics':[],
              'semantic_scope':'Finite arithmetic audits; not an infinite-domain proof.'}
    bound = set(artifact['unknowns']+artifact['fixed_ports'])
    for out, op, x, y in artifact['source']:
        if op not in ('+', '-', '*') or out in bound:
            raise RuntimeError('Invalid gate')
        if any(isinstance(z,str) and z not in bound for z in [x,y]):
            raise RuntimeError('Unbound operand')
        bound.add(out)
    system_bound = set(system['unknowns']+system['fixed_ports'])
    if system['targets'] != [1, 1, 0] or system['outputs'] != artifact['system_outputs']:
        raise RuntimeError('Incorrect system equations')
    if len(system['source']) != 147 or system['operations'] != 147:
        raise RuntimeError('Incorrect system gate count')
    for out, op, x, y in system['source']:
        if op not in ('+', '-', '*') or out in system_bound:
            raise RuntimeError('Invalid system gate')
        if any(isinstance(z,str) and z not in system_bound for z in [x,y]):
            raise RuntimeError('Unbound system operand')
        system_bound.add(out)
    needed = set(system['outputs'])
    for out, op, x, y in reversed(system['source']):
        if out not in needed:
            raise RuntimeError('Dead gate in system circuit')
        needed.update(z for z in [x,y] if isinstance(z,str))
    for case in range(48):
        supplied = {v:rng.randint(-3,3) for v in artifact['unknowns']}
        supplied.update(beta=rng.randint(2,5),Kconstant=5,MC=2,MF=4)
        env = evaluate(artifact, supplied)
        system_env = evaluate(system, supplied)
        if any(system_env[output] != env[output] for output in system['outputs']):
            raise RuntimeError('System projection discrepancy in case '+str(case))
        if env[artifact['labels']['R12']] != independent_norm(artifact,supplied):
            raise RuntimeError('Norm identity discrepancy in case '+str(case))
        result['identity_cases'] += 1
    for prime in [101,103]:
        check = line_degree(artifact, prime)
        if check['product_degree'] != 1609 or check['norm_degree'] != 1600:
            raise RuntimeError('Degree diagnostic discrepancy')
        result['degree_diagnostics'].append(check)
    result.update(gate_count=len(artifact['source']),
                  system_gate_count=len(system['source']),
                  structural_audit='passed')
    destination = Path(__file__).resolve().with_name('radical12_checks.json')
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
