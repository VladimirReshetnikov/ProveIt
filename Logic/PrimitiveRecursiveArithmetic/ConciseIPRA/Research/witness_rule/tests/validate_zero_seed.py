"""Untrusted symbolic certificate construction and independent ZCC restriction guard.

No size record is claimed for this supporting validator. The upstream checker
is used unchanged, with an interception guard that only RESTRICTS its CC rule.
The separate ZCC+ branch implements the explicitly stated wrapped rule.
"""
from pathlib import Path
import copy
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'reference'


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


p = module('upstream_producer', SOURCE / 'counter_producer.py')
kernel = module('upstream_counter_checker', SOURCE / 'counter_checker.py')
original_check = kernel.check


def state_free(tree, depth=0):
    """Check the old outer state slot, including under nested R binders."""
    tag = tree[0]
    if tag == 'b':
        return tree[1] != depth
    if tag in ('0', 'f'):
        return True
    if tag == 'R':
        return (state_free(tree[1], depth)
                and state_free(tree[2], depth)
                and state_free(tree[3], depth + 2))
    if tag == 'S':
        return state_free(tree[1], depth)
    raise ValueError('Not a canonical numerical term')


def check(goal, proof, context, free):
    rule = proof.get('rule')
    if rule in ('CC', 'ZCC+'):
        kernel.require(goal[0] == '=' and goal[1][0] == goal[2][0] == 'R', 'R roots')
        left, right = goal[1:]
        kernel.require(left[2:] == right[2:], 'Unchanged seed/body')
        kernel.require(left[2] == kernel.ZERO, 'ZCC requires literal-zero seed')
        kernel.require(state_free(left[3]), 'ZCC update must ignore outer state')
        if rule == 'ZCC+':
            kernel.require(left[1][0] == right[1][0] == 'S', 'Displayed successor counters')
            check(('=', left[1][1], right[1][1]), proof['major'], context, free)
            return
    return original_check(goal, proof, context, free)


kernel.check = check


def nodes(value):
    if isinstance(value, dict):
        return int('rule' in value) + sum(nodes(v) for v in value.values())
    if isinstance(value, list):
        return sum(nodes(v) for v in value)
    return 0


def U(t):
    return p.R(t, p.Z(), 'u_ctr', 'u_state', p.S(p.S(p.V('u_ctr'))))


def u_representation(t, context_size=0, suffix='0'):
    x, y, z, a = ['zcc_' + name + suffix for name in ('x', 'y', 'z', 'a')]
    body = p.S(p.S(p.V('u_ctr')))
    matrix = p.E(U(p.V(y)), p.S(p.V(y)))
    base = p.rzero(p.Z(), body, 'u_ctr', 'u_state')
    step = p.rstep(p.V(z), p.Z(), body, 'u_ctr', 'u_state')
    proof = {'rule': 'DE', 'paired': p.D(x, y, matrix), 'eigen': a,
             'major': {'rule': 'DI', 'mode': 'case', 'witness': p.Z(),
                       'eigen': z, 'body': step[2]},
             'body': {'rule': 'QE', 'closure': p.Q(y, matrix), 'target': t,
                      'major': {'rule': 'hyp', 'index': context_size},
                      'base': base[2]}}
    return U(t), p.S(t), proof


def join(major, left_endpoint, right_endpoint):
    """L=R, L=F, R=G -> R=F -> F=G by exactly two RL nodes."""
    return p.rl(p.rl(major, left_endpoint), right_endpoint)


def successor_congruence(equality, context_size=0, suffix='0'):
    s, t, _ = equality
    body = p.S(p.S(p.V('u_ctr')))
    lifted = p.cc(equality, p.Z(), body, 'u_ctr', 'u_state')
    return join(lifted, u_representation(s, context_size, 's' + suffix),
                u_representation(t, context_size, 't' + suffix))


def congruence(F, equality, context_size=0, suffix='0', wrapped=False):
    s, t, source_proof = equality
    body = F(p.V('f_ctr'))
    if wrapped:
        lifted = (p.R(p.S(s), p.Z(), 'f_ctr', 'f_state', body),
                  p.R(p.S(t), p.Z(), 'f_ctr', 'f_state', body),
                  {'rule': 'ZCC+', 'major': source_proof})
    else:
        lifted = p.cc(successor_congruence(equality, context_size, suffix),
                      p.Z(), body, 'f_ctr', 'f_state')
    return join(lifted, p.rstep(s, p.Z(), body, 'f_ctr', 'f_state'),
                p.rstep(t, p.Z(), body, 'f_ctr', 'f_state'))


def run():
    output = ROOT / 'zero_seed_certificates'
    output.mkdir(exist_ok=True)
    source = p.rstep(p.V('a'), p.Z(), p.V('source_u'), 'source_u', 'source_v')
    contexts = [
        ('successor', p.S, ['a']),
        ('initializer', lambda x: p.R(p.V('q'), x, 'nu', 'nv', p.S(p.V('nv'))), ['a', 'q']),
        ('nested_update', lambda x: p.R(p.V('q'), p.V('b'), 'nu', 'nv',
                    p.R(x, p.V('nv'), 'ku', 'kv', p.S(p.V('ku')))), ['a', 'q', 'b'])
    ]
    rows = []
    for wrapped in (False, True):
        for name, F, parameters in contexts:
            proof = congruence(F, source, suffix=name, wrapped=wrapped)
            packet = p.packet(proof, parameters)
            kernel.verify(packet)
            expected_nodes = 6 if wrapped else 21
            if nodes(packet) != expected_nodes:
                raise ValueError('Wrong proof size')
            key = ('wrapped_' if wrapped else 'zero_seed_') + name
            (output / (key + '.json')).write_text(json.dumps(packet, indent=2) + '\n')
            rows.append({'name': key, 'accepted': True, 'nodes': nodes(packet),
                         'source_nodes': 1, 'overhead': nodes(packet) - 1})
    controls = []
    for bad_seed, bad_body in [(p.S(p.Z()), p.V('c_u')), (p.Z(), p.V('c_v')),
                             (p.Z(), p.R(p.Z(), p.Z(), 'inner_u', 'inner_v', p.V('c_v')))]:
        bad = p.packet(p.cc(source, bad_seed, bad_body, 'c_u', 'c_v'), ['a'])
        try:
            kernel.verify(bad)
        except Exception as error:
            controls.append({'rejected': True, 'reason': str(error)})
        else:
            raise ValueError('ZCC side-condition control unexpectedly accepted')
    # Independently expose the quotient relation used in the universal countermodel proof.
    equivalent = lambda a, b: a == b or (a in (0, 1) and b in (0, 1))
    for a in range(10):
        for b in range(10):
            if equivalent(a + 1, b + 1) and a != b:
                raise ValueError('Successor-domain separation failed')
            for c in range(10):
                if equivalent(a, b) and equivalent(a, c) and not equivalent(b, c):
                    raise ValueError('Root replacement relation failed')
    if not equivalent(0, 1) or equivalent(1, 2):
        raise ValueError('Countermodel witness failed')
    result = {'status': 'PASS', 'positive_certificates': rows, 'negative_controls': controls,
              'countermodel_relation_finite_sanity': {'range': '0..9', 'passed': True},
              'scope': 'Concrete certificate and side-condition checks, not a universal formalization; the complete metatheorems are written proofs.'}
    (ROOT / 'zero_seed_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    run()
