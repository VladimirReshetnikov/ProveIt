"""Exact carry synthesis checks and scoped native-controller obstructions."""
from collections import deque
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
VERIFICATION = HERE.parents[1] / "verification"
sys.path.insert(0, str(VERIFICATION))
import sympy as sp
import explore_delayed_blank_raw_queue as delayed


def digits(n, length):
    return tuple(n // 3**j % 3 for j in range(length))


def word(ds):
    return sum(d * 3**j for j, d in enumerate(ds))


def source_check():
    # Coefficient symbols are fixed compiler numerals, not input witnesses.
    names = 'Z0 Z1 Z2 Z3 H q a0 a1 a2 a3 h c_start c_final'.split()
    symbols = dict(zip(names, sp.symbols(' '.join(names))))
    dag = [(f'p{i}', '*', f'a{i}', f'Z{i}') for i in range(4)]
    dag += [('s1', '+', 'p0', 'p1'), ('s2', '+', 's1', 'p2'),
            ('s3', '+', 's2', 'p3'), ('clock', '*', 'h', 'H'),
            ('total1', '+', 's3', 'clock'), ('total2', '+', 'total1', 'c_start'),
            ('endpoint', '*', 'q', 'c_final'), ('twiceH', '*', 2, 'H'),
            ('repunit', '+', 'twiceH', 1)]
    env = dict(symbols)
    for name, op, a, b in dag:
        left = env[a] if isinstance(a, str) else sp.Integer(a)
        right = env[b] if isinstance(b, str) else sp.Integer(b)
        assert name not in env
        env[name] = left*right if op == '*' else left+right
    source = sum(symbols[f'a{i}']*symbols[f'Z{i}'] for i in range(4))
    source += symbols['h']*symbols['H']+symbols['c_start']-symbols['q']*symbols['c_final']
    assert sp.expand(env['total2']-env['endpoint']-source) == 0
    assert sp.expand(env['repunit']-symbols['q']-(2*symbols['H']+1-symbols['q'])) == 0
    assert len(dag) == 13 and sum(row[1] == '*' for row in dag) == 7
    return dict(operations=13, multiplications=7, additions=6, comparisons=2,
                fixed_coefficients='a0 a1 a2 a3 h c_start c_final'.split(),
                unpaid='q=3^t and stream bounds; no universal machine claimed',
                instructions=[list(row) for row in dag])


def carry_check():
    count = 0
    integral_false = 0
    # Signed coefficients, signed endpoints, nonzero clock offset, and t=0.
    for coeffs, h in (((1, 1, -1), 0), ((2, -3, 1), 1), ((-1, 2, -2), -2)):
        bound = max(2, (abs(h) + 2*sum(map(abs, coeffs)) + 1)//2)
        for t in range(4):
            q = 3**t
            H = (q-1)//2
            for streams in product(range(q), repeat=3):
                for start in (-2, 0, 1):
                    c = start
                    integral = True
                    for j in range(t):
                        numerator = c+h+sum(a*(z//3**j % 3) for a, z in zip(coeffs, streams))
                        if numerator % 3:
                            integral = False
                            break
                        c = numerator//3
                        assert abs(c) <= bound
                    for final in (-2, 0, 1):
                        equality = sum(a*z for a, z in zip(coeffs, streams))+h*H+start == q*final
                        assert equality == (integral and c == final)
                        count += 1
                        integral_false += not integral
    return dict(tuples=count, nonintegral_rejections=integral_false)


def productive(machine):
    initial, table, states = machine.compile()
    reverse = {s: [] for s in states}
    for (s, _), (n, _, _) in table.items():
        reverse[n].append(s)
    live = {s for s in states if s.kind == 'accept'}
    todo = list(live)
    while todo:
        for s in reverse[todo.pop()]:
            if s not in live:
                live.add(s)
                todo.append(s)
    return initial, table, states, live


def prefix_to_erase(initial, table, live):
    todo = deque([(initial, [])])
    seen = {initial}
    while todo:
        state, path = todo.popleft()
        if state.kind == 'erase':
            return state, path
        for read in delayed.old.ALPHABET:
            nxt, output, _ = table[state, read]
            if nxt in live and nxt not in seen:
                seen.add(nxt)
                todo.append((nxt, path+[(read, output)]))
    raise AssertionError('no productive eraser')


def table_check():
    # Columns are a0,a1,b0,b1,h,c(E),c(F).
    rows = [[0,0,0,0,1,-2,0], [1,0,0,0,1,-2,0], [0,2,0,0,1,-2,0],
            [0,0,0,0,1,0,-2], [1,0,1,0,1,0,-2], [0,2,0,2,1,0,-2]]
    matrix = sp.Matrix(rows)
    assert matrix.rank() == 6
    assert matrix.nullspace() == [sp.Matrix([0,0,0,0,2,1,1])]
    samples = []
    for old in delayed.old.fixtures():
        machine = delayed.wrap(old)
        initial, table, states, live = productive(machine)
        if initial not in live:
            samples.append(dict(name=machine.name, states=len(states), productive_states=0))
            continue
        erase, prefix = prefix_to_erase(initial, table, live)
        final, output, _ = table[erase, delayed.old.DELIM]
        assert final.kind == 'accept' and output == (0, 0)
        for read in ((0,0), (1,0), (0,2)):
            nxt, output, _ = table[erase, read]
            assert nxt == erase and output == (0,0)
            nxt, output, _ = table[final, read]
            assert nxt == final and output == read
        samples.append(dict(name=machine.name, states=len(states), productive_states=len(live),
                            prefix_length=len(prefix)))
    return dict(local_rank=6, local_nullspace=[[0,0,0,0,2,1,1]], fixtures=samples)


def scalar_queue_check():
    # Independently specified local and global sources, without using runs.
    u, v, W, N, Nnext, c, cnext, cf, d, e = sp.symbols('u v W N Nnext c cnext cf d e')
    fifo = 3*Nnext-N+d-W*e
    carry = 3*cnext-c-2*cf-u*d-v*e
    Y = v*N+W*(cf-c)
    Ynext = v*Nnext+W*(cf-cnext)
    conservation = 3*Ynext-Y+(u*W+v)*d
    assert sp.expand(conservation-v*fifo+W*carry) == 0
    x, A, D, cs, q, H = sp.symbols('x A D cs q H')
    flux = u*x+(u*W+v)*A-(cf-cs)
    global_carry = u*D+v*A+2*cf*H+cs-q*cf
    global_fifo = D-x-W*A
    assert sp.expand(global_carry-u*global_fifo-cf*(2*H-q+1)-flux) == 0
    local_count = 0
    for ui, vi, cfi in product(range(-2,3), range(-2,3), range(-1,2)):
        for Wi in (3,9):
            for Ni, ci, ei in product(range(Wi), range(-3,4), range(3)):
                di = Ni % 3
                numerator = ci+2*cfi+ui*di+vi*ei
                if numerator % 3:
                    continue
                cni = numerator//3
                Nni = Ni//3+(Wi//3)*ei
                Yi = vi*Ni+Wi*(cfi-ci)
                Yni = vi*Nni+Wi*(cfi-cni)
                assert 3*Yni == Yi-(ui*Wi+vi)*di
                local_count += 1
    bound_count = admitted = 0
    for ui, vi, K in product((-2,-1,1,2), range(-3,4), range(-3,4)):
        bound = max(abs(vi),abs(K))//abs(ui)
        for Wi in (3,9,27):
            for xi, Ai in product(range(Wi), range(41)):
                if ui*xi+(ui*Wi+vi)*Ai == K:
                    assert xi <= bound
                    admitted += 1
                bound_count += 1
    return dict(symbolic_residuals=2, local_transitions=local_count,
                arbitrary_flux_tuples=bound_count, admitted_flux_tuples=admitted,
                input_bound='floor(max(abs(v),abs(c_final-c_start))/abs(u)) for u!=0')


def monomials(variables, max_degree):
    return [powers for powers in product(range(max_degree+1), repeat=variables)
            if sum(powers) <= max_degree]


def add_modular_row(basis, row, prime):
    row = [v % prime for v in row]
    for pivot, prior in sorted(basis.items()):
        factor = row[pivot]
        if factor:
            row = [(v-factor*w) % prime for v, w in zip(row, prior)]
    pivot = next((i for i, v in enumerate(row) if v), None)
    if pivot is not None:
        inverse = pow(row[pivot], -1, prime)
        basis[pivot] = [(inverse*v) % prime for v in row]


def grid_check():
    machine = delayed.wrap(delayed.old.fixtures()[0])
    initial, table, _, live = productive(machine)
    erase, prefix = prefix_to_erase(initial, table, live)
    r = len(prefix)
    pd = [word(row[0][i] for row in prefix) for i in range(2)]
    pa = [word(row[1][i] for row in prefix) for i in range(2)]
    prime = 1000003
    powers = monomials(5, 3)
    basis = {}
    count = 0
    for k in range(1, 5):
        values = sorted(word(ds) for ds in product((0,1), repeat=k))
        H = (3**k-1)//2
        # All k<=2 grids; a complete 4-by-4-by-4-by-4 subgrid at k>=3.
        erasing = values[:4]
        copying = [v for v in values if v][:4]
        for e0, e1, c0, c1 in product(erasing, erasing, copying, copying):
            E, C = (H+e0, e1), (c0, c1)
            path = list(prefix)
            path += [(tuple(digits(E[i],k)[j] for i in range(2)), (0,0)) for j in range(k)]
            path += [(delayed.old.DELIM, (0,0))]
            path += [(tuple(digits(C[i],k)[j] for i in range(2)),
                      tuple(digits(C[i],k)[j] for i in range(2))) for j in range(k)]
            state = initial
            for read, append in path:
                state, output, _ = table[state, read]
                assert output == append
            assert state.kind == 'accept'
            D = [word(row[0][i] for row in path) for i in range(2)]
            A = [word(row[1][i] for row in path) for i in range(2)]
            q = 3**len(path)
            assert len(path) == r+2*k+1
            assert D == [pd[i]+3**r*E[i]+3**(r+k)*(i==1)+3**(r+k+1)*C[i] for i in range(2)]
            assert A == [pa[i]+3**(r+k+1)*C[i] for i in range(2)]
            assert min(D+A) > 0 and D[0]+D[1] < q and max(A) < q
            point = D+A+[q]
            if len(basis) < len(powers):
                row = []
                for exponents in powers:
                    entry = 1
                    for coordinate, exponent in zip(point, exponents):
                        entry = entry*pow(coordinate, exponent, prime) % prime
                    row.append(entry)
                add_modular_row(basis, row, prime)
            count += 1
    assert len(basis) == len(powers) == 56
    # The stream-affine map has block triangular diagonal (3^r,3^r,s,s).
    u, s = sp.symbols('u s', nonzero=True)
    affine = sp.Matrix([[u,0,s,0], [0,u,0,s], [0,0,s,0], [0,0,0,s]])
    assert affine.det() == u*u*s*s
    return dict(paths=count, prefix_length=r, tested_k=[1,2,3,4],
                polynomial_degree=3, polynomial_columns=56, modular_rank=56, prime=prime,
                affine_determinant='u^2*s^2', positive_streams=True, joint_bound=True)


def sha(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def verify():
    return dict(scope='Conditional carry compiler and witness-free controller obstruction; complete bound unchanged at 76',
                source=source_check(), carry=carry_check(), table=table_check(),
                scalar_queue=scalar_queue_check(), grids=grid_check(),
                dependencies={name: sha(VERIFICATION/name) for name in
                              ('explore_delayed_blank_raw_queue.py', 'explore_constant_length_raw_queue.py')})


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'saved receipt mismatch'
    print(json.dumps(result, indent=2))
