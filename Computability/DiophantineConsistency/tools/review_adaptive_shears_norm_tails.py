#!/usr/bin/env python3
"""Independent local audit: adaptive positive11 and shared two-root tails.

Imports no candidate or builder module.  This checks exact graph transforms,
short ring identities, full fixed-byte bindings, and selected diagnostics.
Ordinary unbounded existence arguments remain in the companion review note.
"""
import collections
import gzip
import hashlib
import json
from pathlib import Path
import sys
import zipfile
import sympy as S

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
OPS = {'add', 'sub', 'mul'}


def need(ok, text):
    if not ok:
        raise RuntimeError(text)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(path.read_text())


def identity(a, b, text):
    need(S.expand(a-b) == 0, text)


def adaptive():
    home = ROOT / 'candidates/positive11-adaptive-shears'
    pins = read(home / 'SOURCE_PINS.json')
    need(sha((REPO / 'docs/incoming/ConZFC_Polynomial_Shears_2026-10-23.zip').read_bytes()) == pins['archive_sha256'], 'positive11 intake archive')
    for item in pins['retained'].values():
        need(sha((home / item['stored']).read_bytes()) == item['sha256'], 'positive11 retained source')
    archive = REPO / 'docs/incoming/ConZFC_Polynomial_Shears_2026-10-23.zip'
    with zipfile.ZipFile(archive) as zf:
        for name,item in pins['retained'].items():
            suffix = '/positive11/'+name
            members = [n for n in zf.namelist() if n.endswith(suffix)]
            need(len(members) == 1 and zf.read(members[0]) == (home/item['stored']).read_bytes(), 'positive11 exact actual ZIP member')
    parent, child = read(home / 'upstream/parent112.json'), read(home / 'positive11.json')
    old, new = parent['source'], child['source']
    need(['g67','*','Y','q'] in old and ['S','*',4,'g67'] in old, 'actual parent carrier')
    wanted = [['S' if n == 'g67' else n,op,a,b] for n,op,a,b in old if n != 'S']
    need(wanted == new, 'exact one-gate deletion and full ordered prefix')
    available = set(child['witnesses'] + child['fixed_numerals'])
    deps, counts = {}, collections.Counter()
    for n,op,a,b in new:
        need(n not in available and op in ['+','-','*'], 'fresh binary positive11 gate')
        need(all(type(x) is int or x in available for x in [a,b]), 'positive11 topology')
        available.add(n)
        deps[n] = [x for x in [a,b] if isinstance(x,str)]
        counts[op] += 1
    live, todo = set(), [child['output']]
    while todo:
        n = todo.pop()
        if n in live:
            continue
        live.add(n)
        todo.extend(deps.get(n, []))
    need(live == available and dict(counts) == {'*':63,'+':31,'-':17}, '111 live operations')
    for key in ['witnesses','fixed_numerals','output','exact_degree','residual_degrees']:
        need(parent[key] == child[key], 'same ordered polynomial interface')
    binding_path = ROOT / 'con-zfc-diophantine-forms/44-b4-sparse/native/COEFFICIENT_BINDING.json'
    binding = read(binding_path)
    ports, hashes = {}, {}
    for item in binding['materialization']['files']:
        packed = (binding_path.parent / item['file']).read_bytes()
        raw = gzip.decompress(packed)
        need(sha(raw) == item['sha256'] and sha(packed) == item['gzip_sha256'], 'whole compact44 payloads')
        ports[item['port']] = int.from_bytes(raw, 'little')
        hashes[item['port']] = sha(raw)
    need(ports['beta'] == (1 << 590069)-1 and ports['beta'] % 3 == 1 and
         ports['K'] > 0 and 0 < ports['MC'] < ports['beta'] and
         0 < ports['MF_source'] < 2*ports['beta'], 'actual carrier/mask bounds')
    # Exact local cancellation and leading gamma term in the changed main row.
    U,X,a,c,H,v,ss,gamma,q,Y = S.symbols('U X a c H v ss gamma q Y')
    shift = U*gamma+ss*X-v
    main = (U*(X+a*c)+H*shift)**2-U*U*(1+(a*a+H)*c*c)
    reduced = 2*U*a*c*(U*X+H*shift)+(U*X+H*shift)**2-U*U*H*c*c-U*U
    identity(main, reduced, 'main norm exact cancellation')
    # After U=q²Y, a~XY,c~kY,H~4XY,shift~q²Y gamma+R0.
    k,R0 = S.symbols('k R0')
    leader = 2*(q*q*Y)*(X*Y)*(k*Y)*(4*X*Y)*(q*q*Y*gamma+R0)
    identity(leader, 8*q*q*k*X*X*Y**4*(q*q*Y*gamma+R0), 'reduced main leader')
    # N8 = square -64*integer, so N8 cannot be -2 mod4 even
    # though A1 no longer has a factor4 in its subtracted term.
    need(all((z*z-64*m) % 4 != 2 for z in range(4) for m in range(4)), 'finalizer negative-unit exclusion')
    replay = read(Path('/tmp/proofs62ff-positive11-adaptive-review/REPLAY.json'))
    need(replay['status'] == 'PASS' and all(x['returncode'] == 0 for x in replay['results']), 'positive11 normal/optimized scratch algebra')
    return dict(literal_sha256=sha((home/'positive11.json').read_bytes()), variables=11,
                operations=111, operation_histogram=dict(counts), exact_degree=211,
                proof_review='Adaptive cofactor, early dependencies, positivity of inverse shear, and canonical transport offset checked in companion note.',
                selected_uniform_degree_coefficient='2^9*(3*beta)^48',
                entire_graph_is_parent_with_one_carrier_gate_removed=True,
                whole_compact44_raw_hashes=hashes, scoped_replay=replay)


def normalize(nodes, root, cuts):
    cache, visited = {}, set()
    def visit(i):
        if i in cache:
            return cache[i]
        visited.add(i)
        if i in cuts:
            result = cuts[i]
        else:
            n = nodes[i]
            if n['kind'] == 'literal':
                result = S.Integer(n['value'])
            else:
                need(n['kind'] in OPS, 'tail has no undeclared atom')
                a,b = visit(n['left']),visit(n['right'])
                result = a+b if n['kind']=='add' else a-b if n['kind']=='sub' else a*b
        cache[i] = S.expand(result)
        return cache[i]
    return visit(root), visited


def norm_case(case, home):
    parent_path, child_path = ROOT / case['parent'], home / (case['name']+'.json')
    parent, child = read(parent_path), read(child_path)
    cert = read(home / (case['name']+'_identity.json'))
    need(sha(parent_path.read_bytes()) == case['parent_sha256'] == cert['parent_sha256'], 'tail parent SHA')
    need(sha(child_path.read_bytes()) == cert['child_sha256'], 'tail child SHA')
    remap = {int(i):j for i,j in cert['retained_remap'].items()}
    cuts = cert['cutset']
    need(len(cuts) == 4 and len(set(cuts)) == 4 and len({remap[i] for i in cuts}) == 4, 'four distinct mapped atoms')
    sy = S.symbols('t s a b')
    old, _ = normalize(parent['nodes'], parent['output'], dict(zip(cuts,sy)))
    new, covered = normalize(child['nodes'], child['output'], {remap[i]:x for i,x in zip(cuts,sy)})
    t,s,a,b = sy
    wanted = (t*t-s*(a+b))**2-4*s*s*a*b
    identity(old, wanted, 'actual parent norm shape')
    identity(new, wanted, 'actual child exact norm identity')
    for i,j in remap.items():
        node = dict(parent['nodes'][i])
        if node['kind'] in OPS:
            need(node['left'] in remap and node['right'] in remap, 'prefix closed under operands')
            node['left'],node['right'] = remap[node['left']],remap[node['right']]
            if node['kind'] in ['add','mul']:
                node['left'],node['right'] = sorted([node['left'],node['right']])
        need(child['nodes'][j] == node, 'complete retained local-node proof')
        covered.add(j)
    need(covered == set(range(len(child['nodes']))), 'all child nodes justified')
    live,todo = set(),[child['output']]
    counts = collections.Counter()
    for i,node in enumerate(child['nodes']):
        if node['kind'] in OPS:
            need(0 <= node['left'] < i and 0 <= node['right'] < i, 'tail topology')
            counts[node['kind']] += 1
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        n = child['nodes'][i]
        if n['kind'] in OPS:
            todo.extend([n['left'],n['right']])
    need(live == set(range(len(child['nodes']))), 'tail full liveness')
    need(sum(counts.values()) == case['operations']-1 == child['total_operations'], 'one live operation saved')
    for key in ['variables','domain','coefficient_recipes','fixed_recipes']:
        need(parent.get(key) == child.get(key), 'unchanged domain/whole coefficient recipes')
    binding_path = home / case['fixed_binding']
    binding = read(binding_path)
    fixed = {}
    if case['fixed_kind'] == 'shared54':
        for item in binding['records']:
            packed = (binding_path.parent.parent/item['path']).read_bytes()
            raw = gzip.decompress(packed)
            need(sha(packed) == item['gzip_sha256'] and sha(raw) == item['raw_sha256'], 'all compact54 fixed leaf bytes')
            fixed[item['name']] = item['sign']*int.from_bytes(raw,'little')
    else:
        for n,item in binding.items():
            packed = (binding_path.parent/item['file']).read_bytes()
            raw = gzip.decompress(packed)
            need(sha(packed) == item['gzip_sha256'] and sha(raw) == item['raw_sha256'] and raw[0] in [0,1], 'all signed norm10 fixed leaf bytes')
            fixed[n] = (-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
    need({n['name'] for n in child['nodes'] if n['kind']=='fixed'} <= set(fixed), 'all actual fixed leaves supplied')
    def evaluate(body, inputs, modulus):
        values = []
        for node in body['nodes']:
            kind = node['kind']
            if kind == 'literal':
                v = node['value']
            elif kind == 'fixed':
                v = fixed[node['name']]
            elif kind == 'variable':
                v = inputs[node['name']]
            else:
                a,b = values[node['left']],values[node['right']]
                v = a+b if kind=='add' else a-b if kind=='sub' else a*b
            values.append(v%modulus)
        return values
    for prime in [65537,1000000007,2147483647]:
        for seed in range(20):
            inputs = {n:(j+2)*seed-19 for j,n in enumerate(child['variables'])}
            before,after = evaluate(parent,inputs,prime),evaluate(child,inputs,prime)
            need(before[parent['output']] == after[child['output']], 'actual-port scalar output diagnostic')
    return dict(name=case['name'], variables=len(child['variables']), domain=child['domain'],
                operations=child['total_operations'], exact_degree_inherited=case['degree'],
                parent_sha256=sha(parent_path.read_bytes()), child_sha256=sha(child_path.read_bytes()),
                full_prefix_and_exact_tail_verified=True, whole_fixed_leaves=len(fixed),
                extra_actual_port_diagnostics=60)


def main():
    t,s,a,b = S.symbols('t s a b')
    identity((t*t-s*(a+b))**2-4*s*s*a*b,
             (t*t+s*(a-b))**2-4*s*a*t*t, 'generic shared-tail identity')
    home = ROOT / 'candidates/norm-tail-sharing'
    pins = read(home/'source10/SOURCE_PINS.json')
    actual_archive_hash = sha((REPO/pins['archive']).read_bytes())
    need(actual_archive_hash == pins['archive_sha256'], 'norm10 archive digest corrected to actual intake ZIP')
    with zipfile.ZipFile(REPO/pins['archive']) as zf:
        for key,item in pins['parents'].items():
            members = [n for n in zf.namelist() if n.endswith('/'+item['arrival_member'])]
            need(len(members) == 1, 'one norm10 actual ZIP parent member')
            raw = zf.read(members[0])
            need(sha(raw) == item['sha256'] and raw == (home/'source10'/('parent_'+key+'.json')).read_bytes(), 'norm10 parent exact actual ZIP member')
        for path in (home/'source10/fixed').glob('*.gz'):
            members = [n for n in zf.namelist() if n.endswith('/norm10/fixed/'+path.name)]
            need(len(members) == 1 and zf.read(members[0]) == path.read_bytes(), 'norm10 fixed payload exact actual ZIP member')
    cases = read(home/'PARENTS.json')
    selected = [case for case in cases if case['name'] in ['saturated_positive','integer10_cubic']]
    need(len(selected) == 2, 'one Sat and one 10Z case selected')
    result = dict(status='PASS', python_optimization=sys.flags.optimize, sympy=S.__version__,
                  adaptive_positive11=adaptive(), generic_shared_norm_identity=True,
                  norm10_archive_sha256=actual_archive_hash,
                  selected_shared_norm_cases=[norm_case(case,home) for case in selected],
                  scope='Exact local/prefix ring identities and ordinary-proof review; inherited native calibration/exact parent degrees not re-proved; no Lean or internal-ZFC derivation.')
    out = ROOT/'PROPOSAL_REVIEW_ADAPTIVE_SHEARS_NORM_TAILS.json'
    if sys.flags.optimize:
        out = out.with_name(out.stem+'_OPTIMIZED.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS adaptive positive11 and selected Sat/10Z shared-tail exact-prefix audits')


if __name__ == '__main__':
    main()
