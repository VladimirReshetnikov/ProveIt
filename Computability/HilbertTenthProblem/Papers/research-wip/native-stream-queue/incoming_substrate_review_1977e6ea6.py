"""Source-pinned replay and independent checks of six incoming substrate reports.

Archives stay unchanged. Retired files are recovered from their arrival commit.
The companion note states mathematical scope and separates original defects
from repaired implementations; finite replay is not a universality proof.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import io
import itertools
import json
from math import prod
from pathlib import Path, PurePosixPath
import random
import subprocess
import sys
import tempfile
import types
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[5]
ARRIVAL = '1977e6ea6'
ARCHIVES = {
    'Exact_Wiring_Diophantine_Report.zip': '5115e76cf01577b7348cc7b987260d4ec166ba61b746dc7601625adad00fcf08',
    'ProveIt_Exact_Erasure_Research.zip': '6e44cd4ef319dc51ae1974481a51be6fb046e151f82af5a968e3318b114e77af',
    'Thermal_Arithmetic_Diophantine_Hamiltonians.zip': '205a46f9798a0dcf5219e80f989182168705bc2c790d1ac39effa22f6b200309',
    'Topology_Is_Not_Free_Interaction_Nets.zip': 'd0d7405ec4e572f1542b8a618815f5de99498cc385ccd9cdcdbd5d8080ebd5b8',
    'no_ghost_wires.zip': '5df354ceed72357e5b61233535052e424e56a5646f8afafcdc26c981a902419a',
    'sandpile_diophantine_research.zip': '2022a5d4986621045e2d9e25ac7edb79d90d8a13c3112e24fa6ee3f4ddffb14e',
}
RUNS = {
    'Exact_Wiring_Diophantine_Report.zip': ('Exact_Wiring_Diophantine', [
        ['code/verify.py']]),
    'Topology_Is_Not_Free_Interaction_Nets.zip': ('Interaction_Net_Diophantine', [
        ['code/verify.py'], ['code/verify_exports.py']]),
    'no_ghost_wires.zip': ('no_ghost_wires', [
        ['code/verify.py'], ['code/check_export.py']]),
    'ProveIt_Exact_Erasure_Research.zip': ('exact_erasure_research', [
        ['code/run_checks.py'],
        ['code/check_certificate.py', 'examples/pcp_nine_state_certificate.json'],
        ['code/check_certificate.py', 'examples/seven_state_erasure_certificate.json'],
        ['code/check_certificate.py', 'examples/seven_state_information_certificate.json'],
        ['code/check_certificate.py', 'examples/pcp_nine_state_information_certificate.json'],
        ['code/check_certificate.py', 'examples/seven_state_uniform_certificate.json'],
        ['code/check_certificate.py', 'examples/three_state_information_certificate.json'],
        ['code/check_certificate.py', 'examples/three_state_nonuniform_erasure_certificate.json'],
        ['code/check_certificate.py', 'examples/three_state_wrong_uniform_target.json']]),
    'Thermal_Arithmetic_Diophantine_Hamiltonians.zip': ('thermal_arithmetic', [
        ['verify.py']]),
    'sandpile_diophantine_research.zip': ('sandpile_diophantine_certificates', [
        ['verify.py', '--output', 'verification.json', '--export-dir', 'example'],
        ['verify_compact.py'], ['verify_spatial.py']]),
}


def archive(name, *, from_git=False):
    assert type(name) is str and name in ARCHIVES and type(from_git) is bool
    path = ROOT/'docs'/'incoming'/name
    raw = (path.read_bytes() if path.exists() and not from_git else subprocess.run(
        ['git', 'show', f'{ARRIVAL}:docs/incoming/{name}'], cwd=ROOT,
        check=True, capture_output=True).stdout)
    assert hashlib.sha256(raw).hexdigest() == ARCHIVES[name]
    with ZipFile(io.BytesIO(raw)) as z:
        assert len(z.namelist()) == len(set(z.namelist()))
        out = {}
        for n in z.namelist():
            p = PurePosixPath(n)
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in n
            if not n.endswith('/'): out[n] = z.read(n)
        return out


def original_replays(all_files):
    results = {}
    for name, files in all_files.items():
        prefix, runs = RUNS[name]
        with tempfile.TemporaryDirectory(prefix='substrate-1977-') as tmp:
            root = Path(tmp)
            for member, raw in files.items():
                path = root/member
                assert path.resolve().is_relative_to(root.resolve())
                path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)
            records = []
            for args in runs:
                done = subprocess.run([sys.executable]+args, cwd=root/prefix,
                    check=False, capture_output=True, text=True, timeout=240)
                expected = int(args[-1] == 'examples/three_state_wrong_uniform_target.json')
                assert done.returncode == expected, (name, args, done.stdout, done.stderr)
                stdout = done.stdout.replace(tmp, '<archive>')
                stderr = done.stderr.replace(tmp, '<archive>')
                ignored = []
                try:
                    summary = json.loads(stdout)
                except json.JSONDecodeError:
                    summary = None
                if type(summary) is dict:
                    for field in ('runtime_seconds', 'elapsed_seconds', 'python', 'python_version'):
                        if field in summary: ignored.append(field); del summary[field]
                    stdout = json.dumps(summary, sort_keys=True, separators=(',', ':'))
                records.append(dict(argv=args, expected_exit_code=expected, exit_code=done.returncode,
                    ignored_runtime_metadata=ignored, json_summary=summary,
                    stdout_sha256=hashlib.sha256(stdout.encode()).hexdigest(),
                    stderr_sha256=hashlib.sha256(stderr.encode()).hexdigest()))
            results[name] = records
    return results


@contextmanager
def modules(files, paths):
    """Load only named exact archive bytes and restore the import namespace."""
    before = {n: sys.modules.get(n) for n, member in paths}
    made = {}
    try:
        for name, member in paths:
            module = types.ModuleType(name); module.__file__ = member
            sys.modules[name] = module
            exec(compile(files[member], member, 'exec'), module.__dict__)
            made[name] = module
        yield made
    finally:
        for name, previous in before.items():
            if previous is None: sys.modules.pop(name, None)
            else: sys.modules[name] = previous


def sandpile_checks(files):
    import sympy as sp
    prefix = 'sandpile_diophantine_certificates/'
    paths = [(n, prefix+n+'.py') for n in ('sandpile_cubic', 'sandpile_compact', 'sandpile_spatial')]
    with modules(files, paths) as loaded:
        base, compact, spatial = (loaded[n] for n, _ in paths)
        counts = Counter(); rng = random.Random(1977)
        def burnable(g, u, z):
            support = [i for i in range(g.n) if u[i]]
            return all(any(z[v] >= sum(g.a[v][w] for w in X) for v in X)
                for k in range(1, len(support)+1) for X in itertools.combinations(support, k))
        for n in (1, 2, 3):
            pairs = list(itertools.combinations(range(n), 2))
            for bits in itertools.product((0, 1), repeat=len(pairs)):
                a = [[0]*n for _ in range(n)]
                for (i, j), value in zip(pairs, bits): a[i][j] = a[j][i] = value
                for sink in itertools.product((0, 1), repeat=n):
                    try: g = base.Graph(tuple(map(tuple, a)), tuple(sum(a[i])+sink[i] for i in range(n)))
                    except ValueError: continue
                    counts['simple_dissipative_graphs'] += 1
                    for eta in itertools.product(range(3), repeat=n):
                        actual, _ = base.stabilize(g, eta, bulk=False)
                        new = compact.certificate(g, eta); old = base.certificate(g, eta)
                        assert compact.from_baseline(g, eta, old) == new
                        assert compact.to_baseline(g, eta, new) == old
                        assert tuple(new[f'u_{i}'] for i in range(n)) == actual
                        counts['complete_zero_roundtrips'] += 1
                        for u in itertools.product(range(4), repeat=n):
                            z = tuple(eta[i]-sum((g.d[i] if i == j else -g.a[i][j])*u[j]
                                for j in range(n)) for i in range(n))
                            good = all(0 <= z[i] < g.d[i] for i in range(n)) and burnable(g, u, z)
                            assert good == (u == actual)
                            counts['subset_burning_candidate_checks'] += 1
        for case in range(24):
            n = 1+case % 4; a = [[0]*n for _ in range(n)]
            for i, j in itertools.combinations(range(n), 2): a[i][j] = a[j][i] = rng.randrange(3)
            g = base.Graph(tuple(map(tuple, a)), tuple(sum(row)+1+rng.randrange(2) for row in a))
            L = sp.Matrix([[g.d[i] if i == j else -a[i][j] for j in range(n)] for i in range(n)])
            ray = sp.Matrix([rng.randrange(1, 4) for _ in range(n)])
            offset = tuple(rng.randrange(5) for _ in range(n))
            c = L.inv()*ray; b = L.inv()*sp.Matrix([v-1 for v in g.d])
            T = 1+max(int(sp.floor(b[i]/c[i])) for i in range(n))
            q = int(sp.ilcm(*([int(v.q) for v in c]+[1])))
            nu = tuple(int(q*v) for v in c)
            for t in range(T, T+min(q, 8)):
                eta = tuple(offset[i]+t*int(ray[i]) for i in range(n))
                eta2 = tuple(eta[i]+q*int(ray[i]) for i in range(n))
                u, z = base.stabilize(g, eta); u2, z2 = base.stabilize(g, eta2)
                assert z == z2 and u2 == tuple(u[i]+nu[i] for i in range(n)) and min(u) > 0
                assert base.burning_ranks(g, u, z) == base.burning_ranks(g, u2, z2)
                counts['weighted_eventual_period_pairs'] += 1
            counts['weighted_period_graphs'] += 1
        a = [[0, 1], [1, 0]]; d = [2, 3]; g = base.Graph(a, d)
        a[0][1] = 2; d[0] = 1
        bad = base.certificate(g, (0, 2), (2, 1)); actual = base.stabilize(g, (0, 2))[0]
        assert actual == (0, 0) and base.evaluate(g, (0, 2), bad) == 0
        bg = [0, 0, 0, 0]; src = spatial.PeriodicInput((4,), bg)
        inst = spatial.SpatialInstance.build(src, 0); witness = inst.certificate(); bg[2] = 2
        assert inst.evaluate(witness) == 0 and all(src.height((2+4*k,)) == 2 for k in range(-5, 6))
        source = spatial.PeriodicInput((1,), (1,), (((2,), 2),))
        graph, sites = base.box_graph(1, 0)
        forged = spatial.SpatialInstance(source, 0, 0, graph, sites, ((-1,), (1,)))
        fw = forged.certificate(); assert forged.evaluate(fw) == 0
        try: spatial.SpatialInstance.build(source, 0)
        except ValueError: pass
        else: raise AssertionError('validated builder accepted omitted finite defect')
        return dict(counts=dict(counts), original_defects=dict(
            mutable_graph=dict(a=a, d=d, eta=[0, 2], claimed_u=[2, 1], actual_u=list(actual), witness=bad),
            mutable_periodic_background=dict(periods=[4], before=[0, 0, 0, 0], after=bg,
                radius=0, witness=witness, infinitely_many_unstable_sites='2+4k, k in Z'),
            unchecked_spatial_constructor=dict(background=[1], override=[[2, 2]], radius=0,
                minimum_radius=0, witness=fw, scope='The finite defect outside the collar is omitted; the infinite one-dimensional input is explosive.')))


@contextmanager
def applied_patch(files, prefix, patch_name, patch_sha256):
    patch = Path(__file__).with_name(patch_name)
    assert hashlib.sha256(patch.read_bytes()).hexdigest() == patch_sha256
    with tempfile.TemporaryDirectory(prefix='substrate-repair-') as tmp:
        root = Path(tmp)
        for member, raw in files.items():
            path = root/member
            assert path.resolve().is_relative_to(root.resolve())
            path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)
        done = subprocess.run(['patch', '--batch', '--fuzz=0', '-p1', '-i', str(patch)],
            cwd=root/prefix, capture_output=True, text=True)
        assert done.returncode == 0, (done.stdout, done.stderr)
        yield root/prefix, {member: (root/member).read_bytes() for member in files}


def sandpile_repair_checks(files):
    prefix = 'sandpile_diophantine_certificates'
    patch_name = 'sandpile_immutable_input_guards.patch'
    patch_sha = 'db3861fe54973fa0688623001ecbeb9e15883127ae8246c6937c60d1ed7859bd'
    paths = [(n, prefix+'/'+n+'.py') for n in ('sandpile_cubic', 'sandpile_compact', 'sandpile_spatial')]
    counts = Counter()
    def reject(fn):
        try: fn()
        except (ValueError, TypeError): counts['rejected_bad_inputs'] += 1
        else: raise AssertionError('malformed constructor accepted by repair')
    with applied_patch(files, prefix, patch_name, patch_sha) as (root, changed):
        with modules(changed, paths) as loaded:
            base, compact, spatial = (loaded[n] for n, _ in paths)
            a = [[0, 1], [1, 0]]; d = [2, 3]; g = base.Graph(a, d)
            a[0][1] = 2; d[0] = 1
            assert g.a == ((0, 1), (1, 0)) and g.d == (2, 3)
            reject(lambda: base.certificate(g, (0, 2), (2, 1)))
            reject(lambda: base.Graph(a, d))
            for eta in itertools.product(range(4), repeat=2):
                old = base.certificate(g, eta); new = compact.certificate(g, eta)
                assert compact.from_baseline(g, eta, old) == new
                assert compact.to_baseline(g, eta, new) == old
                counts['repaired_graph_zero_roundtrips'] += 1
            bg = [0, 0, 0, 0]; periods = [4]
            source = spatial.PeriodicInput(periods, bg)
            inst = spatial.SpatialInstance.build(source, 0); witness = inst.certificate()
            bg[2] = 2; periods[0] = 1
            assert inst.evaluate(witness) == 0 and source.height((2,)) == 0
            assert source.periods == (4,); counts['periodic_snapshot_regressions'] += 1
            reject(lambda: spatial.PeriodicInput((4,), bg))
            coordinates = [0]; record = [coordinates, 2]; overrides = [record]
            source = spatial.PeriodicInput([1], [0], overrides)
            coordinates[0] = 100; record[1] = 500; overrides.clear()
            assert source.overrides == (((0,), 2),)
            inst = spatial.SpatialInstance.build(source, 0)
            assert inst.evaluate(inst.certificate()) == 0
            counts['nested_override_snapshot_regressions'] += 1
            source = spatial.PeriodicInput((1,), (1,), (((2,), 2),))
            graph, sites = base.box_graph(1, 0)
            reject(lambda: spatial.SpatialInstance(source, 0, 0, graph, sites, ((-1,), (1,))))
            reject(lambda: spatial.SpatialInstance.build(source, 0))
            source = spatial.PeriodicInput((1,), (0,))
            for field, value in [('radius', True), ('radius', 0.0), ('minimum_radius', -1),
                                 ('graph', base.Graph(((0,),), (3,))), ('sites', ((False,),)),
                                 ('collar', ()), ('collar', ((1,), (-1,)))]:
                args = dict(source=source, radius=0, minimum_radius=0,
                    graph=graph, sites=sites, collar=((-1,), (1,)))
                args[field] = value
                reject(lambda args=args: spatial.SpatialInstance(**args))
            mutable_sites = [[0]]; mutable_collar = [[-1], [1]]
            inst = spatial.SpatialInstance(source, 0, 0, graph, mutable_sites, mutable_collar)
            mutable_sites[0][0] = 99; mutable_collar.clear()
            assert inst.sites == ((0,),) and inst.collar == ((-1,), (1,))
            assert inst.evaluate(inst.certificate()) == 0
            counts['spatial_snapshot_regressions'] += 1
        for args in RUNS['sandpile_diophantine_research.zip'][1]:
            done = subprocess.run([sys.executable]+args, cwd=root, capture_output=True, text=True, timeout=240)
            assert done.returncode == 0, (args, done.stdout, done.stderr)
            counts['repaired_original_author_suites'] += 1
        outputs = [n for n in files if n.startswith(prefix+'/example/')]
        outputs += [prefix+'/'+n for n in ('verification.json', 'verification_compact.json', 'verification_spatial.json')]
        assert len(outputs) == 9
        for member in outputs:
            assert (root/member.removeprefix(prefix+'/')).read_bytes() == files[member], member
            counts['byte_identical_original_receipts_and_exports'] += 1
        return dict(patch=patch_name, patch_sha256=patch_sha, counts=dict(counts),
            patched_source_sha256={n: hashlib.sha256(changed[n]).hexdigest()
                for n in (prefix+'/sandpile_cubic.py', prefix+'/sandpile_spatial.py')},
            scope='Private application to exact original archive bytes; original archive is unchanged.')


def thermal_checks(files):
    import sympy as sp
    counts = Counter(); rng = random.Random(19771002)
    with modules(files, [('_incoming_thermal', 'thermal_arithmetic/compiler.py')]) as loaded:
        c = loaded['_incoming_thermal']
        builder = c.Compiler(1); z = builder.add(builder.variable(0), c.Atom('const', 0.5))
        malformed = builder.finish(z, z)
        assert malformed.canonical((0,)) == (0, 0.5, 1)
        assert malformed.energy((0, 0, 1)) == 0.5
        float_export = malformed.export()
        builder = c.Compiler(1); z = builder.add(builder.variable(0), c.Atom('mode', 1))
        cyclic = builder.finish(z, z)
        assert cyclic.energy((0, 7, 1)) == cyclic.energy((0, 8, 1)) == 0
        cyclic_export = cyclic.export()
        for model in json.loads(files['thermal_arithmetic/examples.json']):
            k, p, m = model['inputs'], model['parameters'], model['modes']
            zs = sp.symbols(f'z0:{m}'); ps = sp.symbols(f'p0:{p}')
            def atom(a, ns, params):
                return a['value'] if a['kind'] == 'const' else ns[a['value']] if a['kind'] == 'mode' else params[a['value']]
            residuals = []
            for j, gate in enumerate(model['gates']):
                assert gate['output'] == k+j and gate['operation'] in ('add', 'mul')
                for a in (gate['left'], gate['right']):
                    assert type(a['value']) is int and a['value'] >= 0
                    assert (a['kind'] == 'const' or a['kind'] == 'mode' and a['value'] < k+j
                            or a['kind'] == 'param' and a['value'] < p)
                a, b = atom(gate['left'], zs, ps), atom(gate['right'], zs, ps)
                residuals.append(zs[gate['output']]-(a+b if gate['operation'] == 'add' else a*b))
            residuals += [atom(model['left'], zs, ps)-atom(model['right'], zs, ps), zs[-1]-1]
            energy = sp.expand((1+sum(zs))*sum(r*r for r in residuals))
            assert sp.expand(energy-sp.sympify(model['expanded_H'])) == 0
            assert sp.Poly(energy, *(zs+ps)).total_degree() <= 5
            assert len(residuals) == model['equations']
            assert model['local_terms'] == (m+1)*len(residuals)
            assert all(len(sp.sympify(r).free_symbols & set(zs)) <= 3 for r in residuals)
            counts['complete_export_symbolic_checks'] += 1
            source = {tuple(term['exponents']): term['coefficient'] for term in model['sparse_source']}
            built = c.compile_polynomial(source, k, p)
            for _ in range(40):
                params = tuple(rng.randrange(4) for _ in range(p)); xs = tuple(rng.randrange(4) for _ in range(k))
                values = list(xs)
                for gate in model['gates']:
                    a, b = atom(gate['left'], values, params), atom(gate['right'], values, params)
                    values.append(a+b if gate['operation'] == 'add' else a*b)
                values = tuple(values+[1])
                expected = sum(v*prod(x**e for x, e in zip(params+xs, powers)) for powers, v in source.items())
                assert values == built.canonical(xs, params) and built.penalty(values, params) == expected**2
                counts['independent_canonical_checks'] += 1
            for _ in range(30):
                params = tuple(rng.randrange(3) for _ in range(p)); values = tuple(rng.randrange(3) for _ in range(m))
                expected = int(energy.subs(dict(zip(zs+ps, values+params))))
                assert expected == built.energy(values, params)
                assert expected == 0 or expected >= 1+sum(values)
                counts['independent_full_tuple_checks'] += 1
        for d in (1, 2, 3):
            for t in (Fraction(0), Fraction(1, 4), Fraction(2, 3)):
                q = Fraction(1, 16); expected = q/(1-q*t)**d
                for excited in (False, True):
                    interval = c.partition_interval(lambda ns: 1+sum(ns), d, q, t,
                        Fraction(1, 1024), excited_only=excited)
                    assert interval.lower <= expected <= interval.upper and interval.width <= Fraction(1, 1024)
                    counts['geometric_partition_enclosures'] += 1
            interval = c.partition_interval(lambda ns: 1+sum(ns), d, Fraction(1, 16), Fraction(1),
                Fraction(1, 1024), excited_only=True)
            assert interval.lower <= Fraction(1, 16)/(1-Fraction(1, 16))**d <= interval.upper
            counts['excited_boundary_enclosures'] += 1
        return dict(counts=dict(counts), original_defects=dict(float_atom=dict(export=float_export,
            canonical=[0, 0.5, 1], natural_tuple=[0, 0, 1], fractional_energy=0.5),
            cyclic_gate=dict(export=cyclic_export, same_source_input=0, distinct_zero_completions=[[0, 7, 1], [0, 8, 1]])))


def erasure_checks(files):
    import sympy as sp
    paths = [('_incoming_erasure', 'exact_erasure_research/code/erasure.py'),
             ('_incoming_erasure_checker', 'exact_erasure_research/code/check_certificate.py')]
    counts = Counter(); rng = random.Random(1977)
    with modules(files, paths) as loaded:
        compiler, checker = (loaded[n] for n, _ in paths)
        for d, r in ((1, 2), (2, 2), (1, 3), (1, 4)):
            source = [[[rng.randrange(-3, 4) for _ in range(d)] for _ in range(d)] for _ in range(2)]
            source[0] = [[0]*d for _ in range(d)]
            compiled = compiler.compile_mortality(source, tensor_degree=r, eta=Fraction(2, 7))
            for word in itertools.product(range(compiled['k']), repeat=3):
                target = sp.eye(compiled['n']); original = sp.eye(d)
                for label in word:
                    target = sp.Matrix(compiled['matrices'][label])*target
                    if label < len(source): original = sp.Matrix(source[label])*original
                assert target.rank() == 1+r*original.rank()
                assert checker.evaluate(compiler.certificate(compiled, word))['accepted'] == (original.rank() == 0)
                assert checker.evaluate(compiler.information_certificate(compiled, word))['accepted'] == (original.rank() == 0)
                counts['independent_tensor_rank_cases'] += 1
        for matrices in ([[[2, 2], [2, 2]], [[1, 3], [3, 1]]], [[[2, 2], [2, 2]], [[2, 2], [2, 2]]]):
            accepted = []
            for selectors in itertools.product(range(3), repeat=2):
                for y in range(9):
                    data = dict(format='exact-erasure-information-quartic-v1', n=2, k=2, T=1, D=4,
                        matrices=matrices, selectors=[list(selectors)], information_prefixes=[[[y]]])
                    expected = selectors in ((1, 0), (0, 1)) and y == 4 and (selectors == (1, 0) or matrices[1] == matrices[0])
                    actual = checker.evaluate(data)['accepted']; assert actual == expected
                    counts['small_natural_zero_census'] += 1
                    if actual: accepted.append((selectors, y))
            assert len(accepted) == (1 if matrices[0] != matrices[1] else 2)
        signed = dict(format='exact-erasure-information-quartic-v1', n=2, k=2, T=1, D=6,
            matrices=[[[3, 2], [3, 4]], [[3, 1], [3, 5]]], selectors=[[2, -1]], information_prefixes=[[[6]]])
        assert 2*(3-2)-(3-1) == 0 and sum(signed['selectors'][0]) == 1
        try: checker.evaluate(signed)
        except ValueError: counts['signed_false_erasure_rejected'] += 1
        else: raise AssertionError('negative selector accepted')
        return dict(counts=dict(counts), natural_domain_obstruction=signed,
            scope='Rank identities and complete numerical certificates, including a full small selector census. Natural-domain restriction is retained; no fixed universal alphabet is instantiated.')


def thermal_repair_checks(files):
    prefix = 'thermal_arithmetic'; patch_name = 'thermal_exact_dag_guards.patch'
    patch_sha = '525bbeb76e5e82a0a13cc44a2b25ad71aa46c6affdf4c406485a6bc0a372c907'
    counts = Counter()
    def reject(fn):
        try: fn()
        except (ValueError, TypeError): counts['rejected_bad_descriptors'] += 1
        else: raise AssertionError('invalid arithmetic DAG accepted by repair')
    with applied_patch(files, prefix, patch_name, patch_sha) as (root, changed):
        with modules(changed, [('_incoming_thermal_fixed', prefix+'/compiler.py')]) as loaded:
            c = loaded['_incoming_thermal_fixed']
            for kind in ('const', 'mode', 'param'):
                for value in (True, False, 0.5, 1.0, -1):
                    reject(lambda kind=kind, value=value: c.Atom(kind, value))
            for kind in ('invalid', True, 0): reject(lambda kind=kind: c.Atom(kind, 0))
            builder = c.Compiler(1); x = builder.variable(0)
            for invalid in (c.Atom('mode', 1), c.Atom('mode', 10), c.Atom('param', 0)):
                reject(lambda invalid=invalid: builder.add(x, invalid))
                reject(lambda invalid=invalid: builder.multiply(builder.constant(0), invalid))
                reject(lambda invalid=invalid: builder.power(invalid, 0))
                reject(lambda invalid=invalid: builder.finish(invalid, invalid))
            self_gate = c.Gate('add', x, c.Atom('mode', 1), 1)
            reject(lambda: c.Compiled(1, 0, (self_gate,), x, x))
            for output in (0, 2, 100):
                reject(lambda output=output: c.Compiled(1, 0, (c.Gate('add', x, x, output),), x, x))
            for value in (True, 1.0, -1):
                reject(lambda value=value: c.Compiled(value, 0, (), x, x))
                reject(lambda value=value: c.Gate('add', x, x, value))
            gate = c.Gate('add', x, c.Atom('const', 2), 1); gates = [gate]
            good = c.Compiled(1, 0, gates, c.Atom('mode', 1), c.Atom('mode', 1)); gates.clear()
            assert good.gates == (gate,)
            for value, intermediate, marker in itertools.product(range(4), range(8), range(3)):
                assert (good.energy((value, intermediate, marker)) == 0) == (intermediate == value+2 and marker == 1)
                counts['complete_natural_fiber_tuples'] += 1
            assert good.canonical((10**400,)) == (10**400, 10**400+2, 1)
            counts['immutable_direct_descriptor_checks'] += 1
            builder = c.Compiler(1); x = builder.variable(0)
            builder.add(x, builder.constant(2)); builder.gates.clear()
            result = builder.add(x, builder.constant(2)); model = builder.finish(result, result)
            assert model.canonical((0,)) == (0, 2, 1) and len(model.gates) == 1
            counts['edited_public_gate_list_cache_checks'] += 1
        done = subprocess.run([sys.executable, 'verify.py'], cwd=root, capture_output=True, text=True, timeout=240)
        assert done.returncode == 0, (done.stdout, done.stderr)
        for member in ('examples.json', 'verification.json'):
            assert (root/member).read_bytes() == files[prefix+'/'+member], member
            counts['byte_identical_original_receipts_and_exports'] += 1
        counts['repaired_original_author_suites'] += 1
        return dict(patch=patch_name, patch_sha256=patch_sha, counts=dict(counts),
            patched_compiler_sha256=hashlib.sha256(changed[prefix+'/compiler.py']).hexdigest(),
            scope='Private application to exact original archive bytes; valid high-level exports are byte-identical and invalid low-level descriptors are rejected.')


def wiring_checks(all_files):
    name = 'incoming_wiring_checks_1977e6ea6.py'
    raw = Path(__file__).with_name(name).read_bytes()
    sha = hashlib.sha256(raw).hexdigest()
    assert sha == '08d660dbbf0442c1dc13539d2254a16627de5fdf10565a7210975858e1b1211e'
    with modules({name: raw}, [('_incoming_wiring_review', name)]) as loaded:
        result = loaded['_incoming_wiring_review'].verify(all_files)
    return dict(helper=name, helper_sha256=sha, evidence=result)


def verify():
    files = {name: archive(name) for name in ARCHIVES}
    # Exercise retirement fallback now, even while the incoming ZIPs exist.
    for name in ARCHIVES: assert archive(name, from_git=True) == files[name]
    return dict(status='PASS_INCOMING_SUBSTRATE_REVIEW_1977e6ea6', arrival=ARRIVAL,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        archives={name: dict(sha256=ARCHIVES[name], members={member: hashlib.sha256(raw).hexdigest()
            for member, raw in data.items()}) for name, data in files.items()},
        original_author_replays=original_replays(files),
        wiring=wiring_checks(files),
        sandpile=sandpile_checks(files['sandpile_diophantine_research.zip']),
        sandpile_repair=sandpile_repair_checks(files['sandpile_diophantine_research.zip']),
        thermal=thermal_checks(files['Thermal_Arithmetic_Diophantine_Hamiltonians.zip']),
        thermal_repair=thermal_repair_checks(files['Thermal_Arithmetic_Diophantine_Hamiltonians.zip']),
        erasure=erasure_checks(files['ProveIt_Exact_Erasure_Research.zip']),
        git_archive_fallback_checks=len(ARCHIVES),
        scope='Exact source-pinned original replays and focused independent finite checks; see the review for proof scope, constructor defects and repair status. No universal arithmetic bound follows from these tests.')


if __name__ == '__main__':
    if not __debug__: raise RuntimeError('checks require assertions; do not use Python -O')
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true'); args = parser.parse_args()
    result = json.loads(json.dumps(verify())); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status']); print(result['sandpile']['counts'])
