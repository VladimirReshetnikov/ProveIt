#!/usr/bin/env python3
"""Independent read-only audit of two incoming integer equation families.

No package module is imported.  Polynomial strings use a restricted arithmetic
AST, and the replay receipt concerns scratch copies only.  The mathematical
integrality argument is reviewed in the companion note, not inferred from tests.
"""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys
import sympy as S

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = HERE.parent / 'PROPOSAL_REVIEW_RADICAL_RESIDUE_SHEARS_INTEGER.json'


def need(ok, label):
    if not ok:
        raise RuntimeError(label)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_expr(text, env, integer):
    def rec(node):
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return integer(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -rec(node.operand)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Add):
                return rec(node.left) + rec(node.right)
            if isinstance(node.op, ast.Sub):
                return rec(node.left) - rec(node.right)
            if isinstance(node.op, ast.Mult):
                return rec(node.left) * rec(node.right)
            if (isinstance(node.op, ast.Pow) and
                    isinstance(node.right, ast.Constant) and
                    type(node.right.value) is int and node.right.value >= 0):
                return rec(node.left) ** node.right.value
        raise RuntimeError('not polynomial arithmetic')
    return rec(ast.parse(text, mode='eval').body)


def names(text):
    return {n.id for n in ast.walk(ast.parse(text, mode='eval'))
            if isinstance(n, ast.Name)}


def degree(text, env):
    def rec(node):
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, ast.Constant):
            return 0
        if isinstance(node, ast.UnaryOp):
            return rec(node.operand)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, (ast.Add, ast.Sub)):
                return max(rec(node.left), rec(node.right))
            if isinstance(node.op, ast.Mult):
                return rec(node.left) + rec(node.right)
            if isinstance(node.op, ast.Pow):
                return rec(node.left) * node.right.value
        raise RuntimeError('degree syntax')
    return rec(ast.parse(text, mode='eval').body)


def identity(left, right, label):
    need(S.expand(left - right) == 0, label)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--arrival-root', type=Path,
                    default=Path('/tmp/dioph-wave11-arrivals-440dd03ab8'))
    ap.add_argument('--replay', type=Path,
                    default=Path('/tmp/proofs62ff-radical-shears-integer-replay/REPLAY.json'))
    args = ap.parse_args()
    intake = args.arrival_root
    arrivals = json.loads((intake / 'ARRIVALS.json').read_text())[:2]
    for item in arrivals:
        need(sha(REPO / item['archive']) == item['sha256'], 'intake ZIP digest')
    shears = intake / 'ConZFC_Polynomial_Shears_2026-10-23/con_zfc_polynomial_shears/integer'
    radical = intake / 'con-zfc-radical-residue-2026-10-23/con-zfc-radical-residue-2026-10-23/integer'
    roots = [shears, radical]
    inherited = []
    for root in roots:
        pins = json.loads((root / 'SOURCE_PINS.json').read_text())
        for item in pins['files']:
            path = item.get('local_path', item.get('stored_path'))
            need(sha(root / path) == item['sha256'], 'inherited source digest')
        inherited.append(len(pins['files']))

    ports, raw_hashes = {}, {}
    for name in ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']:
        a = gzip.decompress((shears / 'coefficients' / (name + '.bin.gz')).read_bytes())
        b = gzip.decompress((radical / 'coefficients' / (name + '.bin.gz')).read_bytes())
        need(a == b, 'same entire six-numeral tuple')
        ports[name] = int.from_bytes(a, 'little')
        raw_hashes[name] = hashlib.sha256(a).hexdigest()
    binding = json.loads((radical / 'coefficients/BINDING.json').read_text())
    for name, item in binding['payloads'].items():
        need(raw_hashes[name] == item['raw_sha256'], 'whole tuple binding raw digest')
        need(sha(radical / 'coefficients' / item['path']) == item['gzip_sha256'], 'whole tuple gzip digest')
        need(ports[name].bit_length() == item['bits'], 'whole tuple bit lengths')
    need(ports['beta'] == (1 << 1064921) - 1 and
         ports['cone_A'] == 1 << 1113 and ports['cone_B'] == 1 << 666104,
         'exact source34 scales')
    prior = json.loads((HERE.parent / 'PROPOSAL_REVIEW_PELL_CONGRUENCES_INTEGER.json').read_text())
    need(prior['whole_tuple_raw_hashes'] == raw_hashes, 'same tuple as Pell-congruence review')

    # Independent actual-port diagonal substitution gives an exact lower-degree
    # certificate over a finite field.  Structural AST bounds supply the upper.
    prime, t = 1000000007, S.Symbol('t')
    zero = S.Poly(0, t, modulus=prime)
    integer = lambda n: S.Poly(n, t, modulus=prime)
    results = []
    for root in roots:
        paths = sorted((root / 'forms').glob('*.json'))
        for path in paths:
            if path.stem.endswith('_dag'):
                continue
            packet = json.loads(path.read_text())
            env = {n: S.Poly((2 * i + 1) * t, t, modulus=prime)
                   for i, n in enumerate(packet['variables'])}
            env.update({n: integer(v % prime) for n, v in ports.items()})
            dd = {n: 1 for n in packet['variables']}
            dd.update({n: 0 for n in ports})
            known = set(env)
            for n, text in packet.get('definitions', {}).items():
                need(n not in known and names(text) <= known, 'definition topology')
                env[n] = run_expr(text, env, integer)
                dd[n] = degree(text, dd)
                known.add(n)
            rows = packet.get('compact_residuals', packet['residuals'])
            rr = [run_expr(text, env, integer) for text in rows]
            bounds = [degree(text, dd) for text in rows]
            if path.stem == 'center18_degree80':
                value = (integer(1) + rr[-1]) * (integer(1) + sum((x*x for x in rr[:-1]), zero)) - integer(1)
                upper = bounds[-1] + 2 * max(bounds[:-1])
            else:
                value = sum((x*x for x in rr), zero)
                upper = 2 * max(bounds)
            need(value.degree() == packet['exact_degree'] == upper,
                 'exact actual-port polynomial degree')
            need(packet['variable_count'] == len(packet['variables']) and
                 packet['residual_count'] == len(rows), 'literal dimensions')
            results.append(dict(package=root.parent.name, name=path.stem,
                                variables=len(packet['variables']), residuals=len(rows),
                                degree=upper, actual_diagonal_leader_mod_prime=int(value.LC()) % prime,
                                literal_sha256=sha(path)))

    # Check topology/liveness/counts directly; compare literal DAG and formula
    # along the same exact finite-field polynomial substitution (not samples).
    dags = []
    for path in sorted((radical / 'forms').glob('*_dag.json')):
        dag = json.loads(path.read_text())
        packet = json.loads(path.with_name(path.name.replace('_dag', '')).read_text())
        env = {'v:' + n: S.Poly((2*i+1)*t, t, modulus=prime)
               for i, n in enumerate(dag['variables'])}
        env.update({'c:' + n: integer(v % prime) for n, v in ports.items()})
        deps, hist = {}, Counter()
        def get(n):
            if n.startswith('n:'):
                return integer(int(n[2:]))
            return env[n]
        for node in dag['nodes']:
            n, left, right, op = (node[k] for k in ['id', 'left', 'right', 'op'])
            need(n not in env and op in ['add', 'sub', 'mul'], 'DAG identifier/operator')
            a, b = get(left), get(right)
            env[n] = a+b if op == 'add' else a-b if op == 'sub' else a*b
            deps[n] = [left, right]
            hist[op] += 1
        live, todo = set(), [dag['output']]
        while todo:
            n = todo.pop()
            if n in live:
                continue
            live.add(n)
            todo.extend(deps.get(n, []))
        need(set(deps) <= live, 'all arithmetic gates live')
        need({'v:' + n for n in dag['variables']} <= live, 'all variables live')
        need({'c:' + n for n in dag['fixed_ports']} <= live, 'all six fixed ports live')
        need(len(deps) == dag['operation_count'] and dict(hist) == dag['operation_histogram'], 'live binary count')
        formenv = {n: env['v:' + n] for n in dag['variables']}
        formenv.update({n: env['c:' + n] for n in ports})
        for n, text in packet['definitions'].items():
            formenv[n] = run_expr(text, formenv, integer)
        rr = [run_expr(text, formenv, integer) for text in packet['compact_residuals']]
        need([get(n) for n in dag['residual_outputs']] == rr, 'DAG residual diagonal equality')
        if path.stem.startswith('center18'):
            wanted = (integer(1)+rr[-1])*(integer(1)+sum((x*x for x in rr[:-1]),zero))-integer(1)
        else:
            wanted = sum((x*x for x in rr), zero)
        need(get(dag['output']) == wanted, 'DAG finalizer diagonal equality')
        dags.append(dict(name=dag['name'], operations=len(deps), histogram=dict(hist),
                         all_gates_inputs_ports_live=True, literal_sha256=sha(path)))

    # Small symbolic cuts check the actual coordinate identities without
    # expanding the large tuple-dependent polynomials.
    a, H, c, T, k, tau, V, I, nu, u, xi = S.symbols('a H c T k tau V I nu u xi')
    Z = S.Symbol('Z')
    identity((a*c+Z)**2-(a*a+H)*c*c-1, 2*a*c*Z+Z*Z-H*c*c-1, 'main norm cancellation')
    identity((tau+T)**2-T*(k+T)-1, tau*tau+(2*tau-k)*T-1, 'first norm translation')
    identity(I*I*V*V-(I*I-1)*(V+nu)**2-1,
             (V+nu)**2-I*I*nu*(2*V+nu)-1, 'auxiliary norm translation')
    A, Q, delta, Bnum = u*(u+k)+1, I*I, I*I-1, I*I*V*V-1
    L = xi*xi+2*I*(2*u+k)*xi+Q*(k*k-4)
    N = (delta*L-4*Bnum)**2-64*delta*Q*A*Bnum
    Jt = delta*(L+4*V*xi)-4*(V*V-1)
    Ht = 4*delta*I*(2*u+k)*V
    N110 = Jt*Jt+2*Jt*Ht+64*delta*Q*A*(1-V*V)+16*delta*delta*Q*(k*k-4)*V*V
    identity(N.subs(xi, xi+2*V), N110, 'exact degree110 integer shear')
    identity((2*tau-2*u-k)**2+2*(2*u+k)*(2*tau-2*u-k)+k*k-4,
             4*(tau*tau-A), 'midpoint first norm identity')
    B = S.Symbol('B')
    ss = (I*(2*u+k)+xi)/2
    # Substitution Bnum=delta*B after using Q=I².
    identity(N.subs(V*V, (delta*B+1)/Q),
             16*delta*delta*((ss*ss-Q*A-B)**2-4*Q*A*B), 'scaled radical resultant identity')
    parity_cases = 0
    for tt in range(-20,21):
        for uu in range(-20,21):
            for kk in range(-10,11):
                m = tt*tt+2*(2*uu+kk)*tt+kk*kk-4
                if m == 0:
                    need((tt+kk)%2 == 0 and
                         ((tt+2*uu+kk)//2)**2 == uu*(uu+kk)+1, 'integral midpoint inverse')
                parity_cases += 1
    replay = json.loads(args.replay.read_text())
    need(replay['status'] == 'PASS' and
         [r['byte_identical_forms'] for r in replay['results']] == [5,10], 'selected scoped replays')
    need(sum(len(r['stages']) for r in replay['results']) == 12 and
         all(x['returncode'] == 0 for r in replay['results'] for x in r['stages']), 'all twelve Python stages passed')
    out = dict(status='PASS', sympy=S.__version__, python_optimization=sys.flags.optimize,
               arrivals=arrivals, inherited_file_counts=inherited,
               whole_tuple_raw_hashes=raw_hashes, tuple_raw_bytes=binding['total_raw_bytes'],
               literal_results=results, literal_dags=dags, exact_local_identities=True,
               midpoint_parity_control_cases=parity_cases, scoped_replay=replay,
               scope='Ordinary integer coordinate/guard/radical proof review in companion note; no Lean, object-ZFC derivation, new native calibration, or positive/nine/full release replay.')
    target = OUT if not sys.flags.optimize else OUT.with_name(OUT.stem+'_OPTIMIZED.json')
    target.write_text(json.dumps(out, indent=2)+'\n')
    print('PASS shears/radical integer literals, full tuple, local identities, live DAGs and scratch replays')


if __name__ == '__main__':
    main()
