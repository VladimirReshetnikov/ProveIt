"""One native AND types chronological Wang tape and nearest-neighbor heads.

Four row choices are mark/stay, read/stay, left and right. Finite program
control and an ordinary-TM input bridge are not supplied by this packet.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import wang_b_packed_tape as parent

native = parent.native
PARAMETERS = ['initial_tape_hat', 'final_tape_hat', 'initial_head', 'final_head']
WORDS = ('T', 'G', 'C', 'I', 'W', 'V', 'L', 'R', 'MH', 'LH')
OUTER_AUX = ['height_slack', 'global_bound']+[w+'_hat' for w in WORDS]+['Stay_hat']


def build():
    g = parent.Gates()
    o = g.emit
    D = g.sum(PARAMETERS+['height_slack'], 'height')
    Bhalf = o('*', 4, D, 'half_radix')
    B = o('+', Bhalf, Bhalf, 'radix')
    Bm1 = o('-', B, 1, 'radix_minus_one')
    v = {key: o('-', key+'_hat', 1, 'unhat_'+key) for key in WORDS}
    total = g.sum(['I_hat', 'L_hat', 'R_hat', 'Stay_hat'], 'action_total')
    J = o('-', total, 4, 'repunit')
    Move = o('+', v['L'], v['R'], 'moving_rows')
    Pm1 = o('*', Bm1, J, 'scale_minus_one')
    P = o('+', Pm1, 1, 'scale')
    H = o('+', v['G'], J, 'heads')
    masks = {name: o('*', Bm1, word, name+'_mask')
             for name, word in (('mark', v['I']), ('move', Move), ('left', v['L']))}
    Dm1 = o('-', D, 1, 'height_minus_one')
    rm = o('*', Dm1, J, 'range_mask')
    bound = g.sum([J]+[w+'_hat' for w in WORDS]+['global_bound'], 'bound_sum')
    following = o('-', o('+', v['T'], v['W'], 'marked_tapes'), v['V'], 'next_tapes')
    tape_left = o('+', o('*', B, following, 'shift_next'), 'initial_tape_hat', 'tape_left')
    terminal = o('*', P, 'final_tape_hat', 'terminal_tape')
    tape_right = o('-', o('+', v['T'], terminal, 'tape_sum'), Pm1, 'tape_right')
    # Multiplying this comparison by two gives the doubled-head transport.
    # Charging B/2 explicitly saves two gates relative to doubling endpoints.
    before_double = o('-', o('+', H, v['MH'], 'head_move_sum'), v['LH'], 'head_right_sum')
    head_left = o('+', o('*', B, before_double, 'shift_next_head'), 'initial_head', 'head_left')
    head_sum = o('+', H, o('*', P, 'final_head', 'terminal_head'), 'head_sum')
    left_correction = o('*', Bhalf, v['LH'], 'left_head_correction')
    head_right = o('+', head_sum, left_correction, 'head_right')
    # Twelve canonical P-lanes; B is typed by the positive product scale.
    ah = g.pack([H, v['T'], H, v['C'], v['I'], v['T'], v['G'],
                 Move, v['L'], H, H, v['I']], P, 'input_H')
    am = g.pack([v['G'], H, masks['mark'], masks['mark'], J, rm, rm,
                 J, Move, masks['move'], masks['left'], Move], P, 'input_M')
    az = g.pack([0, v['C'], v['W'], v['V'], v['I'], v['T'], v['G'],
                 Move, v['L'], v['MH'], v['LH'], 0], P, 'output_Z')
    P2 = o('*', P, P, 'P2')
    P4 = o('*', P2, P2, 'P4')
    P8 = o('*', P4, P4, 'P8')
    P12 = o('*', P8, P4, 'P12')
    scale = o('*', B, P12, 'native_scale')
    ns, np, _ = native.source('and64_prescribed')
    assert ns[:7] == [('q','*',16,'P'), ('scaled_A','*',16,'Hhat'),
        ('padded_A','-','scaled_A',4), ('scaled_B','*',16,'Mhat'),
        ('padded_B','-','scaled_B',6), ('scaled_Z','*',16,'Zhat'), ('F3','-','scaled_Z',8)]
    pre = 'native__'
    name = lambda x: pre+x if isinstance(x, str) else x
    source = g.source+[(pre+'q','*',16,scale), (pre+'scaled_A','*',16,ah),
        (pre+'padded_A','+',pre+'scaled_A',12), (pre+'scaled_B','*',16,am),
        (pre+'padded_B','+',pre+'scaled_B',10), (pre+'scaled_Z','*',16,az),
        (pre+'F3','+',pre+'scaled_Z',8)]
    source += [(name(n), op, name(a), name(b)) for n, op, a, b in ns[7:]]
    pairs = [(bound, P), (tape_left, tape_right), (head_left, head_right)]
    pairs += [(name(a), name(b)) for a, b in np]
    aux = OUTER_AUX+[name(n) for n in native.domains('and64_prescribed')[1]]
    packet = dict(source=source, comparisons=pairs, parameters=PARAMETERS, auxiliaries=aux,
        interfaces=dict(D=D, B=B, Bhalf=Bhalf, Bm1=Bm1, J=J, P=P, H=H, Move=Move,
            mark_mask=masks['mark'], move_mask=masks['move'], left_mask=masks['left'],
            range_mask=rm, joined_H=ah, joined_M=am, joined_Z=az,
            native_scale=scale, global_bound=bound, next_tapes=following,
            head_right_sum=before_double, tape_left=tape_left, tape_right=tape_right,
            head_left=head_left, head_right=head_right, **v))
    cc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    packet.update(operations=len(source), multiplications=cc['M'], additions_subtractions=cc['A'],
                  equations=len(pairs), witnesses=len(aux))
    known = set(PARAMETERS+aux)
    for n, op, a, b in source:
        assert n not in known and op in ('+', '-', '*')
        assert all(not isinstance(x, str) or x in known for x in (a, b))
        known.add(n)
    assert all(not isinstance(x, str) or x in known for pair in pairs for x in pair)
    return packet


polynomial_source = parent.polynomial_source
degree_bound = parent.degree_bound
ledger = parent.ledger
execute = parent.execute


def independent(values):
    v = {w: values[w+'_hat']-1 for w in WORDS}
    D = sum(values[n] for n in PARAMETERS)+values['height_slack']
    B = 8*D
    J = sum(values[n+'_hat'] for n in ('I', 'L', 'R', 'Stay'))-4
    P = (B-1)*J+1
    H = v['G']+J
    Move = v['L']+v['R']
    mark, move, left = ((B-1)*a for a in (v['I'], Move, v['L']))
    rm = (D-1)*J
    pack = lambda xs: sum(a*P**j for j, a in enumerate(xs))
    ah = pack([H, v['T'], H, v['C'], v['I'], v['T'], v['G'],
               Move, v['L'], H, H, v['I']])
    am = pack([v['G'], H, mark, mark, J, rm, rm,
               J, Move, move, left, Move])
    az = pack([0, v['C'], v['W'], v['V'], v['I'], v['T'], v['G'],
               Move, v['L'], v['MH'], v['LH'], 0])
    rr = [J+sum(values[w+'_hat'] for w in WORDS)+values['global_bound']-P,
          B*(v['T']+v['W']-v['V'])+values['initial_tape_hat']-
              (v['T']+P*values['final_tape_hat']-(P-1)),
          B*(H+v['MH']-v['LH'])+values['initial_head']-
              (H+P*values['final_head']+4*D*v['LH'])]
    native_values = dict(P=B*P**12, Hhat=ah+1, Mhat=am+1, Zhat=az+1,
        **{n: values['native__'+n] for n in native.domains('and64_prescribed')[1]})
    ns, np, _ = native.source('and64_prescribed')
    e = native.parent.execute(ns, native_values)
    return rr+[e[a]-e[b] for a, b in np], (ah, am, az), native_values


def positive_path(initial, initial_head, actions):
    assert initial >= 0 and initial_head > 0 and initial_head & (initial_head-1) == 0
    assert actions and all(a in ('mark', 'stay', 'left', 'right') for a in actions)
    tapes, heads = [initial], [initial_head]
    rows = {w: [] for w in WORDS}
    stays = []
    for action in actions:
        T, H = tapes[-1], heads[-1]
        C = T & H
        I, L, R = (int(action == a) for a in ('mark', 'left', 'right'))
        assert not (L and H == 1)
        row = dict(T=T, G=H-1, C=C, I=I, W=I*H, V=I*C,
                   L=L, R=R, MH=(L+R)*H, LH=L*H)
        for w in WORDS:
            rows[w].append(row[w])
        stays.append(int(action == 'stay'))
        tapes.append(T+I*(H-C))
        heads.append(H//2 if L else 2*H if R else H)
    params = dict(initial_tape_hat=tapes[0]+1, final_tape_hat=tapes[-1]+1,
                  initial_head=heads[0], final_head=heads[-1])
    D = 16
    while D <= max(tapes+heads+[sum(params.values())]):
        D *= 2
    B, n = 8*D, len(actions)
    P = B**n
    J = (P-1)//(B-1)
    pack = lambda xs: sum(x*B**j for j, x in enumerate(xs))
    values = {w+'_hat': pack(row)+1 for w, row in rows.items()}
    values.update(params, height_slack=D-sum(params.values()), Stay_hat=pack(stays)+1)
    values['global_bound'] = P-J-sum(values[w+'_hat'] for w in WORDS)
    assert values['global_bound'] >= D*J-9 > 0
    assert all(x > 0 for x in values.values())
    values.update({'native__'+n: 1 for n in native.domains('and64_prescribed')[1]})
    return values, dict(tapes=tapes, heads=heads, actions=list(actions), duration=n, radix=B)


def rejected_local_shapes():
    # A left step at the lowest cell has odd doubled output, whereas every
    # supplied next head is integral. All other outer rows and bit lanes hold.
    values, _ = positive_path(0, 1, ['stay'])
    values.update(L_hat=2, MH_hat=2, LH_hat=2, Stay_hat=1)
    D = sum(values[n] for n in PARAMETERS)+values['height_slack']
    B = 8*D
    values['global_bound'] = B-1-sum(values[w+'_hat'] for w in WORDS)
    rr, words, _ = independent(values)
    assert min(values.values()) > 0 and rr[:2] == [0, 0]
    assert rr[2] == -B//2 and words[0] & words[1] == words[2]
    lowest = dict(B=B, head_residual=rr[2], scope='All other outer equations and joined bit lanes hold.')

    # A forged long jump changes only the supplied final head and compensates
    # its contribution to D; the bit graph does not secretly supply motion.
    values, _ = positive_path(0, 2, ['stay'])
    values['final_head'] = 8
    values['height_slack'] -= 6
    rr, words, _ = independent(values)
    assert min(values.values()) > 0 and rr[:2] == [0, 0] and rr[2] != 0
    assert words[0] & words[1] == words[2]
    jump = dict(initial_head=2, final_head=8, head_residual=rr[2])

    # Omitting the top I AND Move=0 lane would accept this simultaneous
    # mark-and-left first row. The unused Stay word contains a borrow.
    D = 16
    B = 8*D
    P = B*B
    J = B+1
    raw = dict(T=2*B, G=1, C=0, I=1, W=2, V=0, L=1, R=0, MH=2, LH=2)
    values = {w+'_hat': raw[w]+1 for w in WORDS}
    values.update(initial_tape_hat=1, final_tape_hat=3, initial_head=2, final_head=1,
                  height_slack=9, Stay_hat=B)
    values['global_bound'] = P-J-sum(values[w+'_hat'] for w in WORDS)
    values.update({'native__'+n: 1 for n in native.domains('and64_prescribed')[1]})
    rr, words, _ = independent(values)
    assert min(values.values()) > 0 and rr[:3] == [0, 0, 0]
    assert (words[0] & words[1])-words[2] == P**11
    assert (words[0] % (P**11)) & (words[1] % (P**11)) == words[2]
    simultaneous = dict(B=B, P=P, I=1, L=1, Move=1, Stay=B-1,
                        first_row='simultaneous mark and left',
                        scope='Violates exactly the top exclusivity bit lane; not a claimed false endpoint.')
    carries = []
    for exponent in range(2, 10):
        B = 1 << exponent
        P = B
        free_move = B-1
        assert (B-1)*free_move == 1+(B-2)*P >= P
        carries.append(dict(B=B, P=P, J=1, free_move=free_move,
                            mask_digits=[1, B-2]))
    return dict(left_from_lowest_cell=lowest, forged_head_jump=jump,
                simultaneous_mark_move=simultaneous,
                unbounded_selector_mask_carries=carries)


def verify():
    packet = build()
    rng = random.Random(2026100301)
    source, out = polynomial_source(packet)
    identities = signed = 0
    for case in range(384):
        positive = case < 192
        values = {n: rng.randrange(1, 6) if positive else rng.randrange(-4, 5)
                  for n in PARAMETERS+packet['auxiliaries']}
        env = execute(source, values)
        rr, words, nv = independent(values)
        at = lambda x: env[x] if isinstance(x, str) else x
        assert rr == [at(a)-at(b) for a, b in packet['comparisons']]
        assert env[out] == sum(r*r for r in rr)
        if positive:
            assert min(words) >= 0 and nv['P'] >= 1
            assert env['native__q'] >= 16 and env['native__F3'] >= 8
            at_interface = lambda name: env[packet['interfaces'][name]]
            assert 0 <= at_interface('I') <= at_interface('J')
            assert 0 <= at_interface('L') <= at_interface('Move') <= at_interface('J')
            assert all(at_interface(k) < at_interface('P')
                       for k in ('mark_mask', 'move_mask', 'left_mask'))
        identities += 1
        signed += not positive
    paths = 0
    by_action = Counter()
    for length in range(1, 13):
        for case in range(24):
            h = 1 << rng.randrange(1, 7)
            start = h
            actions = []
            for _ in range(length):
                choices = ['mark', 'stay', 'right']+(['left'] if h > 1 else [])
                a = rng.choice(choices)
                actions.append(a)
                h = h//2 if a == 'left' else 2*h if a == 'right' else h
            values, trace = positive_path(0 if case < 3 else rng.randrange(256), start, actions)
            rr, words, nv = independent(values)
            assert rr[:3] == [0, 0, 0]
            assert words[0] & words[1] == words[2]
            assert max(words) < nv['P']
            env = execute(packet['source'], values)
            assert env[packet['interfaces']['B']] == trace['radix']
            by_action.update(actions)
            paths += 1
    # Canonical doubled-head transport is equivalent to each local update,
    # including the initial/final positions. Arbitrary head jumps fail it.
    transports = 0
    for D in (8, 16, 32):
        B = 8*D
        for n in range(1, 7):
            for _ in range(32):
                H = [1 << rng.randrange(D.bit_length()) for _ in range(n)]
                actions = [rng.randrange(3) for _ in range(n)]
                next2 = [h*(1, 2, 4)[a] for h, a in zip(H, actions)]
                initial = 1 << rng.randrange(D.bit_length()-1)
                final = 1 << rng.randrange(D.bit_length()-1)
                hp = sum(h*B**j for j, h in enumerate(H))
                nxt = sum(h*B**j for j, h in enumerate(next2))
                eq = B*nxt+2*initial == 2*hp+2*B**n*final
                rows = initial == H[0] and next2[:-1] == [2*h for h in H[1:]] and next2[-1] == 2*final
                assert eq == rows
                transports += 1
    local_rows = 0
    for H in (1, 2, 4, 8, 16):
        for I in (0, 1):
            for L in (0, 1):
                for R in (0, 1):
                    valid = L+R <= 1 and I*(L+R) == 0
                    if valid:
                        v = 2*H+2*(L+R)*H-3*L*H
                        assert v == (H if L else 4*H if R else 2*H)
                        if L and H == 1:
                            assert v % 2 == 1
                        local_rows += 1
    record = ledger(packet)
    assert record['certificate'] == dict(operations=188, multiplications=81,
        additions_subtractions=107, equations=19, witnesses=35)
    assert record['polynomial']['operations'] == 244
    assert record['polynomial']['degree_upper_bound'] == 316
    return dict(status='PASS_WANG_B_PACKED_MOTION', ledger=ledger(packet),
        complete_residual_sos_identities=identities, signed_cases=signed,
        genuine_chronological_outer_paths=paths, action_occurrences=dict(by_action),
        independent_head_transport_cases=transports, local_primitive_cases=local_rows,
        rejected_shapes=rejected_local_shapes(),
        source_sha256=hashlib.sha256(json.dumps(source, sort_keys=True).encode()).hexdigest(),
        example=dict(source=source, comparisons=packet['comparisons'], parameters=PARAMETERS,
            auxiliaries=packet['auxiliaries'], interfaces=packet['interfaces'], output=out),
        scope='Complete uniform nonempty chronological batch of mark/stay, read/stay, left '
              'and right primitives, with positive dyadic initial/final head parameters. '
              'No finite instruction control, ordinary-TM input coding or universal polynomial '
              'bound is supplied. Finite outer paths are not expanded full Pell zeros.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledger'])
