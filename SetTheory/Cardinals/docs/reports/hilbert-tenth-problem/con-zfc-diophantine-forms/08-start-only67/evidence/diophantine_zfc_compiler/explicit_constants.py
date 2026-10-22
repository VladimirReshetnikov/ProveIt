#!/usr/bin/env python3
"""Explicit bounded coefficient definition for the blank-input K215 instance.

This is newly written standalone code, not an imported upstream checker.
Default runs finite audits only. Full alphabet enumeration is finite but
astronomical; --enumerate-windows is deliberately an explicit opt-in.
All choices and loop bounds are independent of whether K215 halts.
"""
from pathlib import Path
from itertools import product
from hashlib import sha256
import argparse
import json

HERE = Path(__file__).resolve().parent
MACHINE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
COMMIT = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'


def read_machine():
    data = (HERE / 'k215.tm').read_bytes()
    assert sha256(data).hexdigest() == MACHINE_SHA256
    transitions = {}
    for line in data.decode().splitlines():
        if line.startswith('#') or not line.strip():
            continue
        q, s, w, direction, target = line.split()
        key = int(q), int(s)
        assert key not in transitions
        transitions[key] = int(w), (1 if direction == 'R' else -1), int(target)
        assert direction in ('L', 'R')
    assert set(transitions) == set(product(range(215), range(2)))
    assert all(w in (0, 1) and 0 <= q <= 215 for w, _, q in transitions.values())
    return transitions


TM = read_machine()
Q0, Q1, ERASE, RETURN = range(4)
HALT = 434
STATE_COUNT = 435
SYMBOL_COUNT = 10
# ordinary two-track pairs 00,01,10,11; then their endpoint-flagged versions.
PAIR_TO_SYMBOL = {(0, 0): 0, (0, 1): 3, (1, 0): 4, (1, 1): 5}
SYMBOL_TO_PAIR = {v: (k, False) for k, v in PAIR_TO_SYMBOL.items()}
SYMBOL_TO_PAIR.update({6 + 2*p + n: ((p, n), True) for p, n in product(range(2), repeat=2)})


def delta(q, symbol):
    """(written symbol, signed physical displacement, new state)."""
    assert 0 <= q < STATE_COUNT and 0 <= symbol < SYMBOL_COUNT
    if q == Q0 and symbol == 1:
        return 2, 0, Q1
    if q == Q1 and symbol == 2:
        return 2, -1, ERASE
    if q == ERASE and symbol == 1:
        return 0, -1, ERASE
    if q == ERASE and symbol == 0:
        return 0, 1, RETURN
    if q == RETURN and symbol == 0:
        return 0, 1, RETURN
    if q == RETURN and symbol == 2:
        return 6, 0, 4  # logical state0, positive track, blank endpoint.
    if q == HALT:
        return symbol, 0, HALT
    if 4 <= q < HALT and symbol in SYMBOL_TO_PAIR:
        original_q, track = divmod(q - 4, 2)
        bits, endpoint = SYMBOL_TO_PAIR[symbol]
        bits = list(bits)
        written, logical_move, target = TM[original_q, bits[track]]
        bits[track] = written
        crossing = endpoint and ((track == 0 and logical_move == -1) or
                                  (track == 1 and logical_move == 1))
        new_track = 1-track if crossing else track
        physical_move = 0 if crossing else (-logical_move if track == 0 else logical_move)
        new_symbol = 6 + 2*bits[0] + bits[1] if endpoint else PAIR_TO_SYMBOL[tuple(bits)]
        new_q = HALT if target == 215 else 4 + 2*target + new_track
        return new_symbol, physical_move, new_q
    # Unreachable malformed configurations have an explicit nonhalting loop.
    return symbol, 0, q


V, H, LEFT, INPUT, START_HEAD, RIGHT = range(6)
ALPHABET_SIZE = 6 + SYMBOL_COUNT*(STATE_COUNT+1)  # 4366
PHASE_EDGE = {(LEFT, LEFT), (LEFT, INPUT), (INPUT, INPUT),
              (INPUT, START_HEAD), (START_HEAD, RIGHT), (RIGHT, RIGHT)}


def tile(symbol, head=None):
    assert 0 <= symbol < SYMBOL_COUNT
    assert head is None or 0 <= head < STATE_COUNT
    return 6 + symbol*(STATE_COUNT+1) + (0 if head is None else head+1)


def payload(t):
    if t == LEFT or t == RIGHT:
        return 0, None
    if t == INPUT:
        return 1, None
    if t == START_HEAD:
        return 1, Q0
    if t >= 6:
        symbol, head_code = divmod(t-6, STATE_COUNT+1)
        return symbol, (head_code-1 if head_code else None)
    return 0, None  # a V neighbor is read as blank/headless.


def allowed_window(w):
    """The exact radius-one clause centered in a row-major 3x3 window.

    Unused corners remain legitimate tile coordinates. Overlap enforces
    the same center predicate at every point of the reconstructed plane.
    """
    if len(w) != 9 or any(not 0 <= t < ALPHABET_SIZE for t in w):
        return False
    above, left, center, right, below = w[1], w[3], w[4], w[5], w[7]
    if not ((above == V) == (center == V) == (below == V)):
        return False
    if center == V and (left == V or right == V):
        return False
    for neighbor in (left, right):
        if center != V and neighbor != V and ((center == H) != (neighbor == H)):
            return False
    if center == H and (above == H or below == H):
        return False
    if center in (V, H):
        return True
    phase = 2 <= center < 6
    if phase != (above == H):
        return False
    if phase:
        if left == V and center != LEFT:
            return False
        if right == V and center != RIGHT:
            return False
        if left != V and (left, center) not in PHASE_EDGE:
            return False
        if right != V and (center, right) not in PHASE_EDGE:
            return False
    symbol, head = payload(center)
    if below == H:
        return head is None or head == HALT
    # Vertical propagation already excluded below=V for an interior center.
    written, movement, target = (symbol, 0, None) if head is None else delta(head, symbol)
    if head is not None and ((movement == -1 and left == V) or
                             (movement == 1 and right == V)):
        return False
    incoming = []
    for source, needed_direction in ((left, 1), (center, 0), (right, -1)):
        source_symbol, source_head = payload(source)
        if source_head is not None:
            _, source_movement, source_target = delta(source_head, source_symbol)
            if source_movement == needed_direction:
                incoming.append(source_target)
    if len(incoming) > 1:
        return False
    return payload(below) == (written, incoming[0] if incoming else None)


START_WINDOW = (H,H,H, INPUT,INPUT,START_HEAD,
                tile(1),tile(1),tile(2,Q1))
END_WINDOW = (H,H,H, LEFT,INPUT,INPUT,
              tile(0),tile(1),tile(1))


def enumerate_windows():
    """Unique, fully specified finite alphabet. Never invokes TM simulation."""
    yield START_WINDOW
    yield END_WINDOW
    for w in product(range(ALPHABET_SIZE), repeat=9):
        if w != START_WINDOW and w != END_WINDOW and allowed_window(w):
            yield w


def next_power_of_five(n):
    value = 1
    while value < n:
        value *= 5
    return value


def compiler_layout(windows, alphabet_size):
    """Independent implementation of explicit complete75 compiler numerals.

    Accepts a finite list; on the K215 window alphabet its termination is
    bounded a priori, but actually listing that alphabet is not attempted.
    The returned sparse integer expression is the coefficient definition.
    """
    windows = tuple(tuple(w) for w in windows)
    a, k = alphabet_size, len(windows)
    assert k >= 2 and len(set(windows)) == k
    assert all(len(w)==9 and all(0<=s<a for s in w) for w in windows)
    A = 1 << max(2, (k+1).bit_length())
    T0 = k+3*a
    pos = {(r,c,s): T0+(2-r)*3*a+(2-c)*a+s
           for r,c,s in product(range(3),range(3),range(a))}
    coefficients = {i:1 for i in range(k)}
    mu = A-2
    for r,c,s in product(range(3),range(3),range(a)):
        j = 1+(3*r+c)*a+s
        weight = A**j
        coefficients[pos[r,c,s]] = weight
        mu += weight
        for i,w in enumerate(windows):
            if w[3*r+c] == s:
                coefficients[i] += weight
    anchor_weights = [A**j for j in range(1+9*a,5+9*a)]
    for weight in anchor_weights:
        mu += weight
        for i in range(k):
            coefficients[i] += weight
    m = 2*mu.bit_count()+12*a+2
    assert m == 2*(A.bit_length()-1)+30*a+8
    padding = 0
    while m+1 < k+9*a+5:
        mu += A**(5+9*a+padding)
        padding += 1
        m += 2
    dummy_count = m+1-k-9*a-4
    dummy = tuple(range(k+12*a,k+12*a+dummy_count))
    native0 = tuple(range(k))+tuple(pos.values())+dummy
    M0 = max(native0)+3*a+1
    anchors = tuple(i*M0 for i in (1,3,9,27))
    native = native0+anchors
    for e,c in zip(anchors,anchor_weights):
        coefficients[e] = c
    K,Emax = len(native),max(native)
    H0 = Emax+24*M0+3*a+1
    T1 = H0+2*Emax+a+1
    T2 = T1+2*Emax+1
    g = T2+Emax+1
    L = next_power_of_five(g+Emax+1)
    mass = (K+2)*(2*sum(coefficients.values())+6)
    target = max(4*mass+8,2*mu+4,16)
    b = next_power_of_five((target-1).bit_length())
    d = b*L
    DC = {}
    def add(poly,e,c=1): poly[e] = poly.get(e,0)+c
    for e in (3*a,H0+a,8*M0,24*M0): add(DC,e)
    for e,c in coefficients.items():
        add(DC,T1-e,c)
        add(DC,T2-e,c)
    old_unit = (2*sum(c*pow(2,e,5) for e,c in DC.items())-pow(2,H0,5))%5
    epsilon = int(old_unit == 0)
    if epsilon: add(DC,g)
    MF = {0:4,T1:mu,T2:mu}
    for r,c,s in product(range(2),range(3),range(a)): add(MF,pos[r,c,s])
    for r,c,s in product(range(3),range(2),range(a)): add(MF,H0+pos[r,c,s])
    for e in anchors[2:]: add(MF,e)
    assert K == m+1 and dummy and dummy[0]+1<Emax
    assert len(set(native))==K
    assert max(DC)+Emax<L and all(e>0 for e in DC)
    assert (2*sum(c*pow(2,e,5) for e,c in DC.items())-pow(2,H0,5))%5
    return dict(a=a,k=k,A=A,coefficients=coefficients,mu=mu,m=m,padding=padding,
                native=native,payload=pos,dummy=dummy,anchors=anchors,M0=M0,H=H0,T1=T1,T2=T2,
                g=g,L=L,b=b,d=d,DC=DC,MF=MF,epsilon=epsilon,mass=mass)


def materialize_constants(layout):
    """Optional, exact, finite; output size is enormous even for toy layouts."""
    b,d = layout['b'],layout['d']
    B = 1 << d
    DC = sum(c << (b*e) for e,c in layout['DC'].items())
    DR = 1 << (b*layout['H'])
    MF = sum(c << (b*e) for e,c in layout['MF'].items())
    MC = B-1-sum(1 << (b*e) for e in layout['native'] if e != 1)
    MC -= 2 << (b*layout['dummy'][0])
    return dict(Bm1=B-1,Kconstant=DC+B*DR,twice_cell_bits=2*d,inner_bits=b,
                MC=MC,MF=MF,MF_source=MF+B-1,W0=1 << (b+2*d))



def emitted_fixed_ports(layout):
    """Actual fixed_input_polynomial74.json ports, NOT the native mask API.

    The polynomial port named MF is MF_source=MF_native+B-1. This wrapper
    intentionally omits inner_bits and binds the fixed loader W0 instead.
    """
    c = materialize_constants(layout)
    return {name:c[source] for name,source in (
        ('Bm1','Bm1'), ('Kconstant','Kconstant'),
        ('twice_cell_bits','twice_cell_bits'), ('MC','MC'),
        ('MF','MF_source'), ('W0','W0'))}


def symbolic_constant_spec():
    """Print a finite expression DAG without expanding its enormous bound sums."""
    return {
      'format':'bounded-integer-expression-dag-v1',
      'coefficient_semantics':'All symbols denote fixed integers, never existential variables.',
      'commit':COMMIT,'machine_sha256':MACHINE_SHA256,
      'a':ALPHABET_SIZE,'window_bound':ALPHABET_SIZE**9,
      'start_window':START_WINDOW,'end_window':END_WINDOW,
      'predicate':'allowed_window in explicit_constants.py (total finite function)',
      'target':'fixed_input_polynomial74.json',
      'target_ports':{'Bm1':'Bm1','Kconstant':'Kconstant','twice_cell_bits':'twice_cell_bits',
                      'MC':'MC','MF':'MF_source','W0':'W0'},
      'native_mask_warning':'The target port MF is NOT the native field mask; it is MF_source=MF_native+B-1.',
      'nodes':[
        ['U','a^9'],
        ['P(n)','indicator(allowed_window(base_a_9_digits(n))), 0<=n<U'],
        ['k','sum(n=0..U-1,P(n))'],
        ['windows','START_WINDOW, END_WINDOW, then other passing tuples in lexicographic order'],
        ['ell','max(2,bitlength(k+1))'],['A','2^ell'],
        ['pos(r,c,s)','k+3*a+(2-r)*3*a+(2-c)*a+s'],
        ['j(r,c,s)','1+(3*r+c)*a+s'],
        ['selector_coeff(i)','1+sum(r,c=0..2,A^j(r,c,windows[i][3*r+c]))+sum(j=9*a+1..9*a+4,A^j)'],
        ['copy_coeff(r,c,s)','A^j(r,c,s)'],
        ['m0','2*ell+30*a+8'],['padding','max(0,ceil((k+9*a+4-m0)/2))'],
        ['m','m0+2*padding'],['mu','A-2+sum(j=1..9*a+4+padding,A^j)'],
        ['D','m-k-9*a-3'],['dummies','k+12*a..k+12*a+D-1'],
        ['M0','k+15*a+D'],['anchors','[M0,3*M0,9*M0,27*M0]'],
        ['E','selectors union copy positions union dummies union anchors'],
        ['anchor_coeff(t)','A^(9*a+t), t=1..4'],['dummy_coeff','0'],
        ['K','m+1'],['Emax','27*M0'],['H0','Emax+24*M0+3*a+1'],
        ['T1','H0+2*Emax+a+1'],['T2','T1+2*Emax+1'],['g','T2+Emax+1'],
        ['L','least power of 5 greater than g+Emax'],
        ['mass','(K+2)*(2*sum(e in E,coeff(e))+6)'],
        ['target','max(4*mass+8,2*mu+4,16)'],
        ['b','least power of 5 at least bitlength(target-1)'],
        ['d','b*L'],['R','2^b'],['B','2^d'],
        ['DC0(T)','T^(3*a)+T^(H0+a)+T^(8*M0)+T^(24*M0)+sum(e in E,coeff(e)*(T^(T1-e)+T^(T2-e)))'],
        ['epsilon','indicator((2*DC0(2)-2^H0) mod 5 = 0)'],
        ['DC','DC0(R)+epsilon*R^g'],['DR','R^H0'],
        ['MF0','mu*(R^T1+R^T2)+sum(r<2,c<3,s<a,R^pos(r,c,s))+sum(r<3,c<2,s<a,R^(H0+pos(r,c,s)))+R^(9*M0)+R^(27*M0)'],
        ['MC','B-1-sum(e in E,e!=1,R^e)-2*R^(k+12*a)'],
        ['MF','MF0+4'],['Bm1','B-1'],['Kconstant','DC+B*DR'],
        ['twice_cell_bits','2*d'],['inner_bits','b'],['MF_source','MF+B-1'],
        ['W0','2^(b+2*d)']],
      'warning':'The bounded sums specify exact integers. They have not been numerically expanded.'}


def audit_helical_toy():
    """Full local/seam test with an explicitly substituted immediate-halting TM.

    This is a test of the normalization/tableau construction, not a claim that
    the actual K215 halts. The real transition dictionary is restored in finally.
    """
    original = TM[0,0]
    TM[0,0] = (1,1,215)
    try:
        margin,u,height = 3,3,25
        width = margin+u+4
        xq = width-3
        xs,xe = xq-1,xq-u
        tape={x:1 for x in range(-u,1)}
        head,q=0,Q0
        G=[]
        G.append([V]+[H]*(width-1))
        G.append([V]+[LEFT]*margin+[INPUT]*u+[START_HEAD]+[RIGHT]*2)
        for y in range(2,height):
            written,move,q=delta(q,tape.get(head,0))
            tape[head]=written;head+=move
            assert 0 < head+xq < width
            G.append([V]+[tile(tape.get(x-xq,0),q if x-xq==head else None)
                           for x in range(1,width)])
        assert q==HALT
        def cell(x,y): return G[(y+x//width)%height][x%width]
        def window(x,y): return tuple(cell(x+dx,y+dy) for dy in (-1,0,1) for dx in (-1,0,1))
        checked=0
        for x,y in product(range(-width,2*width),range(height)):
            assert allowed_window(window(x,y)),(x,y,window(x,y))
            checked+=1
        N=width*height
        cyclic={(-(x-xs)-width*(y-1))%N:window(x,y)
                for x,y in product(range(width),range(height))}
        assert len(cyclic)==N and cyclic[0]==START_WINDOW and cyclic[2]==END_WINDOW
        assert sum(w==START_WINDOW for w in cyclic.values())==1
        assert sum(w==END_WINDOW for w in cyclic.values())==1
        for i in range(N):
            center,right,nxt=cyclic[i],cyclic[(i-1)%N],cyclic[(i-width)%N]
            assert all(center[3*r+c+1]==right[3*r+c] for r in range(3) for c in range(2))
            assert all(center[3*(r+1)+c]==nxt[3*r+c] for r in range(2) for c in range(3))
        # A nonhalting head immediately before H is forbidden.
        bad=list(window(xq,1));bad[7]=H
        assert not allowed_window(tuple(bad))
        return dict(width=width,height=height,period=N,all_plane_windows=checked,
                    all_cyclic_overlaps=N,unique_start=0,unique_end=2,
                    substituted_transition='K215 state0/read0 -> write1,R,halt (test only)')
    finally:
        TM[0,0]=original


def bounded_audits():
    records = {}
    stub={'b':1,'d':9,'H':3,'DC':{0:17},'MF':{0:52},'native':[0,1,6],'dummy':[6]}
    ports=emitted_fixed_ports(stub)
    assert ports==dict(Bm1=511,Kconstant=4113,twice_cell_bits=18,MC=318,MF=563,W0=524288)
    records['fixed_polynomial_port_binding_checked']=ports
    assert STATE_COUNT == 435 and ALPHABET_SIZE == 4366
    assert allowed_window(START_WINDOW) and allowed_window(END_WINDOW)
    assert START_WINDOW != END_WINDOW
    transitions = [delta(q,s) for q,s in product(range(STATE_COUNT),range(SYMBOL_COUNT))]
    assert all(0<=s<SYMBOL_COUNT and v in (-1,0,1) and 0<=q<STATE_COUNT
               for s,v,q in transitions)
    assert all(delta(HALT,s)==(s,0,HALT) for s in range(SYMBOL_COUNT))
    records['normalized_transition_count'] = len(transitions)
    records['helical_toy_audit'] = audit_helical_toy()
    # Sweep erases any input and arrives at precisely the blank folded machine.
    for length in range(2,31):
        tape = {x:1 for x in range(1-length,1)}
        head,q,steps = 0,Q0,0
        while q != 4:
            s,move,q = delta(q,tape.get(head,0))
            tape[head]=s
            head+=move
            steps+=1
            assert head<=0 and steps <= 2*length+6
        assert head==0 and tape.get(0)==6 and all(v==0 for x,v in tape.items() if x!=0)
    records['erasure_lengths_checked'] = [2,30]
    # Every one-step simulated transition, every pair value, both origins and tracks.
    fold_cases=0
    for q,p,n,endpoint,track in product(range(215),range(2),range(2),range(2),range(2)):
        s = 6+2*p+n if endpoint else PAIR_TO_SYMBOL[p,n]
        ws,move,nq = delta(4+2*q+track,s)
        old_pos = 0 if endpoint else 3
        logical = old_pos if track==0 else -old_pos-1
        write,logical_move,target = TM[q,(p,n)[track]]
        expected = logical+logical_move
        if nq==HALT:
            assert target==215
        else:
            recovered_q,new_track=divmod(nq-4,2)
            assert recovered_q==target
            physical=old_pos-move
            actual=physical if new_track==0 else -physical-1
            assert actual==expected and physical>=0
        pair,origin=SYMBOL_TO_PAIR[ws]
        expect_pair=list((p,n));expect_pair[track]=write
        assert pair==tuple(expect_pair) and origin==bool(endpoint)
        fold_cases+=1
    records['fold_transition_cases_checked']=fold_cases
    # Compiler geometry uses synthetic alphabets, not misleading machine approximations.
    summaries=[]
    for windows,a in [([(0,)*9,(1,)*9],2),([(0,)*9,(1,)*9,(2,)*9],3),
                      (list(product(range(2),repeat=9))[:100],2),
                      (list(product(range(2),repeat=9))[:3],2)]:
        layout=compiler_layout(windows,a)
        E=set(layout['native']);extra=layout['dummy'][0]
        v1,v2=layout['anchors'][2:]
        assert layout['T2']-layout['T1']>2*max(E)
        assert layout['L']-(layout['T2']-layout['T1'])>max(E)
        assert [(x,y) for x in E for y in E if y-x==v2-v1]==[(v1,v2)]
        old_tests=set(layout['MF'])-{0}
        for target in old_tests:
            assert layout['DC'].get(target-extra,0)==0
            assert target-extra!=layout['H'] and target!=extra
        assert layout['mass'] <= (1 << layout['b'])//4-2
        # Every native basis bit against every old field-test coefficient.
        basis_checks=0
        pos=layout['payload']
        tests=[]
        for target in (layout['T1'],layout['T2']):
            tests.append((target,lambda site,e:layout['coefficients'].get(e,0) if site==0 else 0))
        for r,c,ss in product(range(2),range(3),range(a)):
            source,target=pos[r+1,c,ss],pos[r,c,ss]
            tests.append((target,lambda site,e,source=source,target=target:
                          int(site==0 and e==source or site==2 and e==target)))
        for r,c,ss in product(range(3),range(2),range(a)):
            cs,rs=pos[r,c+1,ss],pos[r,c,ss]
            tests.append((layout['H']+rs,lambda site,e,cs=cs,rs=rs:
                          int(site==0 and e==cs or site==1 and e==rs)))
        for source,target in zip(layout['anchors'][:2],layout['anchors'][2:]):
            tests.append((target,lambda site,e,source=source,target=target:
                          int(site==0 and e==source or site==2 and e==target)))
        for target,expected in tests:
            for site,e in product(range(3),E):
                actual=(layout['DC'].get(target-e,0) if site==0 else
                        int(target-e==layout['H']) if site==1 else int(target==e))
                assert actual==expected(site,e),(target,site,e)
                basis_checks+=1
        summary={k:layout[k] for k in ('a','k','m','b','L','d','epsilon')}
        summary['all_native_field_basis_checks']=basis_checks
        summaries.append(summary)
    records['compiler_toy_audits']=summaries
    records['full_window_alphabet_enumerated']=False
    records['full_numerals_materialized']=False
    records['coefficient_definition_is_bounded']=True
    records['window_enumeration_upper_bound']=str(ALPHABET_SIZE**9)
    records['source_sha256']=MACHINE_SHA256
    return records


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--enumerate-windows',action='store_true')
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--symbolic-spec',type=Path)
    args=parser.parse_args()
    if args.enumerate_windows:
        for w in enumerate_windows(): print(','.join(map(str,w)))
        return
    if args.symbolic_spec:
        args.symbolic_spec.write_text(json.dumps(symbolic_constant_spec(),indent=2,sort_keys=True)+'\n')
    receipt=bounded_audits()
    output=json.dumps(receipt,indent=2,sort_keys=True)+'\n'
    if args.receipt: args.receipt.write_text(output)
    print(output,end='')

if __name__=='__main__': main()
