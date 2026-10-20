#!/usr/bin/env python3
"""Independent, endpoint-bound replay of K223's merged-G certificate.

Imports no code from the supplied certificate generator or either bundled
checker. TAUT is an abbreviation for the retained rho8/rho6 propositional
bridge, audited separately in the accompanying mathematical review.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path

F = ('rel', 0, 0)
I = lambda x, y: ('imp', x, y)
Q = lambda z, x: ('all', z, x)
E = lambda x, y: ('eq', x, y)
N = lambda x: I(x, F)
EX = lambda z, x: N(Q(z, N(x)))
AND = lambda x, y: N(I(x, N(y)))
KAPPA = lambda a, b: 4 * ((a+b)*(a+b+1)//2+b) + 1
H = lambda a, b: I(E(a,b), Q(KAPPA(a,b), E(a,b)))
R7 = lambda a,b,c: I(E(c,a), I(E(c,b), E(a,b)))
G = lambda a,b,c: I(E(c,a), I(E(c,b), Q(KAPPA(a,b), E(a,b))))
CASES = [(0,0,0), (0,1,2), (1,0,0), (1,1,0), (3,999,1001)]


def require(p, why):
    if not p:
        raise ValueError(why)


def freeze(x):
    return tuple(map(freeze, x)) if isinstance(x, list) else x


def is_nat(x):
    return type(x) is int and x >= 0


def check_formula(f):
    require(isinstance(f, tuple) and f, 'formula must be a constructor tuple')
    if f[0] in ('eq', 'rel'):
        require(len(f) == 3 and is_nat(f[1]) and is_nat(f[2]), 'atomic labels')
    elif f[0] == 'all':
        require(len(f) == 3 and is_nat(f[1]), 'quantifier label')
        check_formula(f[2])
    elif f[0] == 'imp':
        require(len(f) == 3, 'implication arity')
        check_formula(f[1]); check_formula(f[2])
    elif f[0] == 'opaque':
        require(len(f) == 2 and f[1] in ('K', 'RV', 'H'), 'schematic atom')
    else:
        raise ValueError('unknown formula constructor')


def atoms(f):
    if f == F:
        return set()
    if f[0] == 'imp':
        return atoms(f[1]) | atoms(f[2])
    return {f}


def truth(f, valuation):
    if f == F:
        return False
    if f[0] == 'imp':
        return not truth(f[1], valuation) or truth(f[2], valuation)
    return valuation[f]


def expected_roots():
    roots = {}
    for a,b,c in CASES:
        e = E(a,b); z = KAPPA(a,b)
        fs = {
            'reflexivity': E(a,a),
            'ordinary_helper': H(a,b),
            'equality_box_elim': I(Q(z,e),e),
            'original_rho7': R7(a,b,c),
            'symmetry': I(e,E(b,a)),
            'merged_from_old': G(a,b,c),
        }
        roots.update({f'{name}_{a}_{b}_{c}': f for name,f in fs.items()})
    k,rv,h = ('opaque','K'), ('opaque','RV'), ('opaque','H')
    old, new = N(I(k,I(rv,N(h)))), AND(k,rv)
    roots.update({
        'old_bundle_to_new_bundle': I(old,new),
        'old_bundle_projects_helper': I(old,h),
        'new_bundle_and_helper_to_old_bundle': I(new,I(h,old)),
    })
    return roots


def replay(data):
    fs = [freeze(f) for f in data['formulas']]
    for f in fs:
        check_formula(f)
    ns = data['proof_nodes']
    dependencies, counts = [], {}
    for j,node in enumerate(ns):
        fi = node['formula']
        require(is_nat(fi) and fi < len(fs), 'formula index')
        f,r,a = fs[fi], node['rule'], node['args']
        counts[r] = counts.get(r,0)+1
        deps = []
        if r == 'MP':
            require(len(a) == 2 and all(is_nat(x) and x < j for x in a), 'MP edge order')
            require(fs[ns[a[0]]['formula']] == I(fs[ns[a[1]]['formula']],f), 'MP endpoint')
            deps = a
        elif r == 'GEN':
            require(len(a) == 2 and is_nat(a[0]) and is_nat(a[1]) and a[1] < j, 'GEN edge order')
            require(f == Q(a[0],fs[ns[a[1]]['formula']]), 'GEN endpoint')
            deps = [a[1]]
        elif r == 'TAUT':
            av = sorted(atoms(f), key=repr)
            require(all(truth(f,dict(zip(av,bits)))
                        for bits in itertools.product((False,True),repeat=len(av))), 'TAUT validity')
        elif r == 'rho1':
            require(f[0] == 'imp' and f[1][0] == 'all', 'rho1 shape')
            z = f[1][1]
            require(f[1][2][0] == 'imp' and f[1][2][1][0] == 'eq', 'rho1 equality')
            e = f[1][2][1]
            require(e[1] == z and f == EX(z,e), 'rho1 endpoint')
        elif r == 'rho2':
            require(f[0] == 'imp' and f[1][0] == 'all' and f[1][2][0] == 'imp', 'rho2 shape')
            z,aa,bb = f[1][1],f[1][2][1],f[1][2][2]
            require(f == I(Q(z,I(aa,bb)),I(Q(z,aa),Q(z,bb))), 'rho2 endpoint')
        elif r == 'rho6':
            require(f[0] == 'imp' and f[1][0] == 'imp' and f[1][1][0] == 'all', 'rho6 shape')
            z,aa = f[1][1][1],f[2]
            require(f == I(EX(z,Q(z,aa)),aa), 'rho6 endpoint')
        elif r in ('G','OLD_H','OLD_RHO7'):
            require(len(a) == (2 if r == 'OLD_H' else 3) and all(map(is_nat,a)), 'axiom parameters')
            expected = H(*a) if r == 'OLD_H' else R7(*a) if r == 'OLD_RHO7' else G(*a)
            require(f == expected, 'exact '+r+' endpoint')
        else:
            raise ValueError('unpermitted rule '+r)
        dependencies.append(deps)
    expected = expected_roots()
    require(set(data['roots']) == set(expected), 'exact root inventory')
    rr = {}
    for name,idx in data['roots'].items():
        require(is_nat(idx) and idx < len(ns), 'root index')
        require(fs[ns[idx]['formula']] == expected[name], 'claimed root endpoint: '+name)
        visited, todo = set(), [idx]
        while todo:
            x = todo.pop()
            if x in visited:
                continue
            visited.add(x);todo.extend(dependencies[x])
        used = {ns[x]['rule'] for x in visited}
        if name.startswith(('reflexivity_', 'ordinary_helper_', 'equality_box_elim_', 'original_rho7_', 'symmetry_')):
            require(not used.intersection({'OLD_H','OLD_RHO7'}), 'circular old-theory premise')
        if name.startswith('merged_from_old_'):
            require('G' not in used, 'circular G premise')
        rr[name] = {'nodes':len(visited),'rules':sorted(used)}
    return {'nodes':len(ns),'formulas':len(fs),'root_count':len(rr),'rules':counts,'roots':rr}


def controls(data):
    results = {}
    wrong = copy.deepcopy(data)
    name = 'original_rho7_0_1_2'
    idx = wrong['roots'][name]
    good_form = wrong['proof_nodes'][idx]['formula']
    wrong['roots'][name] = next(i for i,n in enumerate(wrong['proof_nodes']) if n['formula'] != good_form)
    trials = {'wrong_claimed_root':wrong}
    hidden = copy.deepcopy(data)
    name = 'ordinary_helper_0_1_2'
    fi = hidden['proof_nodes'][hidden['roots'][name]]['formula']
    hidden['proof_nodes'].append({'rule':'OLD_H','formula':fi,'args':[0,1]})
    hidden['roots'][name] = len(hidden['proof_nodes'])-1
    trials['correct_endpoint_with_forbidden_old_helper'] = hidden
    wrong_binder = copy.deepcopy(data)
    row = next(n for n in wrong_binder['proof_nodes'] if n['rule'] == 'G')
    row['args'][0] += 1
    trials['wrong_G_native_parameters'] = wrong_binder
    for name,d in trials.items():
        try:
            replay(d)
        except (ValueError, IndexError, KeyError, TypeError) as e:
            results[name] = {'rejected':True,'reason':str(e)}
        else:
            raise ValueError('negative control accepted: '+name)
    return results


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('proof',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    raw = args.proof.read_bytes(); data = json.loads(raw)
    result = replay(data)
    result.update(status='PASS_INDEPENDENT_ENDPOINT_BOUND_K223_LOGICAL_REPLAY',
                  proof_sha256=hashlib.sha256(raw).hexdigest(),
                  negative_controls=controls(data),
                  scope='Exact finite endpoints, well-formed natural-labelled formulas, topological MP/GEN, exact row schemas, Boolean TAUT, and cross-theory premise separation. Uniformity and the rho8/rho6 TAUT compilation are supplied by the separately audited mathematical argument; this is not a TM or proof-assistant endpoint.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'roots'},indent=2))
