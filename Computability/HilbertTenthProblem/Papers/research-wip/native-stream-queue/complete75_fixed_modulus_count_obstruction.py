"""A fixed-modulus count replacing the input bridge forces periodic slices.

This audits a guarded hypothetical replacement, not a new universal bound.
The original75/87 sources and their full input bridges are unchanged.
"""
import argparse
from collections import Counter
from hashlib import sha256
from math import gcd
import json
from pathlib import Path
import random

import sympy as sp
import complete75_normalized_strong87 as parent

PRIVATE = {'x', 'alpha', 'count_hat', 'count_scaled_input', 'count_gap',
           'count_multiple', 'raw_scaled_input'}
PORTS = ('raw_input_port', 'count_input_port')


def prefix(a, m, weight):
    assert all(type(v) is int and v > 0 for v in (a, m, weight))
    rows = [('raw_scaled_input', '*', a, 'x'),
            ('raw_input_port', '+', 'alpha', 'raw_scaled_input'),
            ('count_gap', '-', 'count_hat', 1),
            ('count_multiple', '*', m, 'count_gap')]
    if weight != 1:
        rows.append(('count_scaled_input', '*', weight, 'x'))
    rows.append(('count_input_port', '+', 'count_multiple',
                 'x' if weight == 1 else 'count_scaled_input'))
    return rows


def guard(packet):
    """Only the two complete invariant ports can escape their fixed prefix."""
    a, m, weight = (packet[k] for k in ('a', 'modulus', 'weight'))
    paid = prefix(a, m, weight)
    assert type(packet['period']) is int and packet['period'] == m//gcd(m, weight)
    rows = packet['source']
    assert rows[:len(paid)] == paid
    available = set(packet['free'])
    assert {'x', 'alpha', 'count_hat'} <= available
    assert not (set(PORTS) & available)
    assert len(available) == len(packet['free'])
    for at, (name, op, left, right) in enumerate(rows):
        assert name not in available and op in ('+', '-', '*')
        assert all(type(v) is int or v in available for v in (left, right))
        if at >= len(paid):
            assert not ({left, right} & PRIVATE), (name, left, right)
        available.add(name)
    roots = [packet['output']] + [v for pair in packet['comparisons'] for v in pair]
    assert all(type(v) is int or v in available for v in roots)
    assert not (set(roots) & PRIVATE)
    # No private prefix value is silently exported through another interface.
    assert packet.get('public_registers', {}) == dict(zip(PORTS, PORTS))
    nodes = {row[0]: row[2:] for row in rows}
    seen = set()
    def visit(v):
        if type(v) is int or v not in nodes or v in seen:
            return
        seen.add(v)
        for child in nodes[v]:
            visit(child)
    for v in roots:
        visit(v)
    assert seen == set(nodes)
    return True


def build(host='polynomial87', modulus=15, weight=1, word='count_word',
          finalizer='sos', B=16):
    """Keep actual parent constraints except its input bridge, attach a count.

    The word port can stand for any x-independent history extraction. These
    fixtures do not claim that the chosen word is already a typed selector.
    """
    assert host in ('certificate75', 'polynomial87')
    assert finalizer in ('sos', 'anchor')
    assert type(B) is int and B >= 16 and B & (B-1) == 0
    assert word in ('count_word', 'C', 'F', 'Jrep')
    d = B.bit_length()-1
    fixed = parent.eliminated.fixed_inputs(dict(B=B, DC=3, DR=5, MC=B-2,
                                               MF=4, cell_bits=d, inner_bits=3))
    if host == 'certificate75':
        baseline = parent.eliminated.baseline
        old = [tuple(row) for row in baseline.source_audit()['schedule']]
        nodes = {n:(op,l,r) for n,op,l,r in old}
        assert nodes['bounded'] == ('+', 'C', 'alpha')
        assert nodes['scaled_t'] == ('*', 'twice_cell_bits', 'x')
        assert nodes['raw_bound'] == ('+', 'bounded', 'scaled_t')
        comparisons = list(baseline.prior.EQUALITIES[:15])
        assert len(baseline.prior.EQUALITIES) == 19
        nodes['raw_bound'] = ('+', 'C', 'raw_input_port')
        variables = list(baseline.prior.NAMES)
        first = None
        if finalizer == 'anchor':
            # An alternative arithmetic output with the same zero set: an
            # integer product times a positive SOS cannot change translation.
            first = 'count_anchor'
            nodes[first] = ('+', 'F', 1)
    else:
        old = parent.sources()[1]
        nodes = {n:(op,l,r) for n,op,l,r in old}
        assert nodes['C_after_alpha'] == ('-', 'q_minus_FZ', 'alpha')
        assert nodes['scaled_t'] == ('*', 'twice_cell_bits', 'x')
        assert nodes['marked_rhs'] == ('-', 'C_after_alpha', 'scaled_t')
        nodes['marked_rhs'] = ('-', 'q_minus_FZ', 'raw_input_port')
        comparisons = [(n,1) for n in parent.FACTOR_NAMES if n != 'norm_input']
        variables = list(parent.RETAINED)
        if word == 'C':
            word = 'marked_rhs'
        first = None
        if finalizer == 'anchor':
            first, comparisons = comparisons[0][0], comparisons[1:]
    paid = prefix(2*d, modulus, weight)
    nodes['count_residual'] = ('-', word, 'count_input_port')
    comparisons.append(('count_residual',0))
    squares = []
    for k,(left,right) in enumerate(comparisons):
        residual, square = f'count_test_{k}', f'count_square_{k}'
        nodes[residual] = ('-', left, right)
        nodes[square] = ('*', residual, residual)
        squares.append(square)
    total = squares[0]
    for k,square in enumerate(squares[1:],1):
        result = f'count_sum_{k}'
        nodes[result] = ('+', total, square)
        total = result
    if first is None:
        output = total
    elif host == 'polynomial87':
        nodes['count_positive_sum'] = ('+', total, 1)
        nodes['count_anchored_product'] = ('*', first, 'count_positive_sum')
        nodes['count_output'] = ('-', 'count_anchored_product', 1)
        output = 'count_output'
    else:
        nodes['count_output'] = ('*', first, total)
        output = 'count_output'
    # Inline only actual fixed numerical inputs, never witnesses or x.
    nodes = {n:(op,fixed.get(l,l),fixed.get(r,r)) for n,(op,l,r) in nodes.items()}
    supplied = set(variables + ['x', 'count_hat', 'count_word'])
    done = supplied | set(PORTS)
    active = set()
    body = []
    used = set()
    def visit(v):
        if type(v) is int:
            return
        if v in supplied:
            used.add(v)
            return
        if v in done:
            return
        assert v not in active, v
        active.add(v)
        op,l,r = nodes[v]
        visit(l); visit(r)
        body.append((v,op,l,r))
        done.add(v); active.remove(v)
    visit(output)
    # Root comparisons are included for explicit residual inspection.
    for l,r in comparisons:
        visit(l); visit(r)
    free = sorted(used | {'x','alpha','count_hat'})
    result = dict(host=host, modulus=modulus, weight=weight, a=2*d, B=B,
                  period=modulus//gcd(modulus,weight), free=free,
                  source=paid+body, comparisons=comparisons, output=output,
                  public_registers=dict(zip(PORTS,PORTS)), finalizer=finalizer,
                  source_word=word)
    guard(result)
    return result


def run(packet, values):
    env = dict(values)
    def get(v):
        return v if type(v) is int else env[v]
    for name,op,left,right in packet['source']:
        a,b = get(left),get(right)
        env[name] = a+b if op=='+' else a-b if op=='-' else a*b
    return env


def translate(packet, values, steps=1):
    P = packet['period']
    assert type(P) is int and P > 0
    assert type(steps) is int and steps > 0
    shifted = dict(values)
    shifted['x'] -= P*steps
    shifted['alpha'] += packet['a']*P*steps
    shifted['count_hat'] += packet['weight']*P*steps//packet['modulus']
    assert packet['weight']*P % packet['modulus'] == 0
    return shifted


def verify():
    x,alpha,t,a,m,c,k,P = sp.symbols('x alpha t a m c k P')
    assert sp.expand((alpha+a*P*k)+a*(x-P*k)-(alpha+a*x)) == 0
    assert sp.expand(m*(t+c*P*k/m-1)+c*(x-P*k)-(m*(t-1)+c*x)) == 0
    rng = random.Random(750031)
    counts = Counter()
    selected = []
    for host in ('certificate75','polynomial87'):
      for form in ('sos','anchor'):
       for B in (16,32,64):
        for modulus,weight in ((B-1,1),(B-1,2),(B-1,3),(12,8)):
         for word in ('count_word','C','F','Jrep'):
            packet = build(host,modulus,weight,word,form,B)
            counts['guarded_complete_host_sources'] += 1
            for case in range(8):
                signed = case >= 4
                values = {n:rng.randrange(-6,7) if signed else rng.randrange(1,7)
                          for n in packet['free']}
                steps = rng.randrange(1,5)
                values['x'] = packet['period']*steps+rng.randrange(1,16)
                shifted = translate(packet,values,steps)
                before,after = run(packet,values),run(packet,shifted)
                if not signed:
                    assert min(shifted[n] for n in packet['free']) > 0
                    counts['positive_witness_translations'] += 1
                else:
                    counts['signed_identity_assignments'] += 1
                unchanged = set(before)-PRIVATE
                assert all(before[n] == after[n] for n in unchanged)
                for l,r in packet['comparisons']:
                    lv = lambda env,v: v if type(v) is int else env[v]
                    assert lv(before,l)-lv(before,r) == lv(after,l)-lv(after,r)
                assert before[packet['output']] == after[packet['output']]
                counts['complete_output_residual_and_body_identities'] += 1
            if B==16 and modulus==15 and weight==1 and word=='count_word':
                selected.append(packet)
    # The argument requires the complete port guard, including metadata.
    rejects = 0
    good = build()
    for leaked in ('x','alpha','count_hat','raw_scaled_input','count_gap','count_multiple'):
        bad = dict(good, source=list(good['source']))
        bad['source'].append(('leak','+',good['output'],leaked)); bad['output']='leak'
        try: guard(bad)
        except AssertionError: rejects += 1
        else: raise AssertionError(('accepted forbidden direct dependency',leaked))
    bad = dict(good, public_registers={'private':'count_multiple'})
    try: guard(bad)
    except AssertionError: rejects += 1
    else: raise AssertionError('accepted private export')
    for m0 in (0,-1,'count_word'):
        try: build(modulus=m0)
        except AssertionError: rejects += 1
        else: raise AssertionError('accepted nonfixed/nonpositive modulus')
    for packet, period in ((good, float(good['period'])), (build(modulus=1), True)):
        bad = dict(packet, period=period)
        try: guard(bad)
        except AssertionError: rejects += 1
        else: raise AssertionError('accepted noninteger period metadata')
    for steps in (1.0, True, 0, -1, '1'):
        try: translate(good, dict(x=30, alpha=1, count_hat=1), steps)
        except AssertionError: rejects += 1
        else: raise AssertionError('accepted nonpositive/noninteger translation step')
    # Direct fixed-radix selector aliases: these are count components only.
    aliases=[]
    for B in (2,3,4,8,16):
      for length in range(B+1,B+13):
        L=(B**length-1)//(B-1)
        x1=length; x0=x1-(B-1)
        t1=1+(L-x1)//(B-1)
        t0=t1+1
        assert min(x0,t0,t1)>0
        assert L==(B-1)*(t1-1)+x1==(B-1)*(t0-1)+x0
        aliases.append(dict(B=B,length=length,wrong_input=x0))
    # Every fixed positive period fails the powers-of-two language.
    power_cases=[]
    for period in range(1,257):
        high=1 << (2*period).bit_length()
        low=high-period
        assert high>2*period and high//2<low<high and low&(low-1)
        power_cases.append(dict(period=period,accepted_power=high,forced_nonpower=low))
    hashes={}
    for name,rows in (('certificate75',parent.eliminated.baseline.source_audit()['schedule']),
                      ('normalized87',parent.sources()[3])):
        hashes[name]=sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()
    return dict(status='PASS_COMPLETE75_FIXED_MODULUS_COUNT_OBSTRUCTION',
                theorem='Only x-ports alpha+a*x and m*(t-1)+weight*x imply downward closure modulo m/gcd(m,weight), hence each fixed-program input slice is ultimately periodic.',
                symbolic_port_identities=2, counts=dict(counts),
                rejected_contracts=rejects, selector_component_aliases=aliases,
                powers_of_two_obstructions=power_cases, parent_source_sha256=hashes,
                selected_hypothetical_sources=selected,
                scope='Guarded hypothetical input-bridge replacement only. Source/value and count fixtures are not full positive Pell zeros. No uniform threshold-extraction algorithm, universal bound, or obstruction to variable-radix counting is asserted.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=json.loads(json.dumps(verify()))
    path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result
    print(result['status']);print(result['counts'])


if __name__=='__main__':main()
