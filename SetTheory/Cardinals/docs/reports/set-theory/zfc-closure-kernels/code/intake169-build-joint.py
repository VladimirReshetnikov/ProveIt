#!/usr/bin/env python3
"""Build and finitely validate two joint equational packets. Root execution only.

No theorem search, Turing-machine simulation, compiler, network or subprocess.
The ordinary model-equivalence argument is in proof.md; the emitted checks
certify exact syntax, finite Boolean/Horn steps and the complete bit codec.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
DEFAULT_REFERENCE = Path('/tmp/zfc-compare-d584512002/zfc242-contextual-reuse-20261018/zfc242-contextual-reuse-20261018/research/formalism_dispatch/reference')
PINS = {
    'equational_search.py': 'c82f277d3c1b4c654ed61e6df8f920cb5e908a9b845dda860351d34cf7bb7a23',
    'build_equations.py': 'ed3cefc8ede645ceebf3f2e9bde59fd40fe480e6c8451d1c170a4f636bfbdc62',
    'FC13B_complete.json': '3e3c1e272ba99c19dfafdffbd21368041d411a5ac87b0abc3540e659bdf6cc1a',
    'baseline_grouped.json': '34a3de2a4bb585c5df1966a1e741c4faebc5819501b46cc5cb70686b9ae7d49a',
}
HORN_SHA = '9d27d1f20854992161fd49f2176333914574f754a9084c21be32bf503c59f441'
PACKED = ('V', 'A', 'U', 'F')
D, TOP, ONE, O = ('d',), ('top',), ('I', ('d',), ('d',)), ('o',)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value

def membership(x, y):
    return ('p_Inc', ('C', ('C', D, D, x), ONE, y), ('A', D, ONE))

def eliminate_membership(t):
    if isinstance(t, str):
        return t
    args = tuple(eliminate_membership(x) for x in t[1:])
    return membership(*args) if t[0] == 'p_E' else (t[0], *args)

def dispatch(t):
    if isinstance(t, str):
        return t
    args = tuple(dispatch(x) for x in t[1:])
    return ('H', ('tag_' + t[0],), *args) if t[0] in PACKED else (t[0], *args)

def transform(t):
    return dispatch(eliminate_membership(t))

def transformed_literal(lit):
    atom = transform(('p_' + lit[1], lit[2], lit[3]))
    return (lit[0], atom[0][2:], *atom[1:])

def fuse(t):
    if t == TOP:
        return D
    return t if isinstance(t, str) else (t[0], *(fuse(x) for x in t[1:]))

def alias(t):
    if t == ONE:
        return O
    return t if isinstance(t, str) else (t[0], *(alias(x) for x in t[1:]))

def congruence(symbol, arity, groups, fixed_selector=False):
    clauses = []
    for group in groups:
        xs = tuple('x' + str(i) for i in range(arity))
        ys = tuple('y' + str(i) if i in group else xs[i] for i in range(arity))
        prefix = ('t',) if fixed_selector else ()
        premises = tuple((False, 'Eq', xs[i], ys[i]) for i in group)
        clauses.append(premises + ((True, 'Eq', (symbol, *prefix, *xs), (symbol, *prefix, *ys)),))
    return clauses

def horn_equation(B, clause):
    require(all(not l[0] for l in clause[:-1]) and clause[-1][0], 'Expected Horn clause.')
    atoms = [B.atom(l) for l in clause]
    antecedent = atoms[0]
    for atom in atoms[1:-1]:
        antecedent = B.N(B.TOP, B.N(antecedent, atom))
    equation = (B.TOP, B.N(antecedent, B.N(B.TOP, atoms[-1])))
    require(B.check_equation([clause], equation), 'New Horn-to-NAND translation failed.')
    return equation

def strict_codec_checks(B, K, signature, equations, start, target, bits):
    expected = (signature, [B.canonical_equation(e) for e in equations], start, target)
    require(B.decode_packet(bits, list(signature)) == expected, 'Roundtrip failed.')
    rejected = 0
    for end in range(len(bits)):
        try:
            B.decode_packet(bits[:end], list(signature))
        except (ValueError, IndexError):
            rejected += 1
        else:
            raise RuntimeError('Strict truncation accepted at ' + str(end))
    for bad in (bits + '0', bits + '1', 'x' + bits[1:]):
        try:
            B.decode_packet(bad, list(signature))
        except (ValueError, IndexError):
            rejected += 1
        else:
            raise RuntimeError('Malformed or trailing packet accepted.')
    kernel = K.Kernel(signature, equations, start, target)
    orientations = 0
    for i, equation in enumerate(equations):
        values = [D] * len(kernel.rule_variables[i])
        environment = dict(zip(kernel.rule_variables[i], values))
        for reverse in (False, True):
            a, b = equation[::-1] if reverse else equation
            a, b = K.substitute(a, environment), K.substitute(b, environment)
            step = dict(rule=i, reverse=reverse, address=[0], values=values)
            require(kernel.step(('N', a, D), step) == ('N', b, D), 'Contextual orientation check failed.')
            orientations += 1
    return dict(strict_truncations_rejected=len(bits), malformed_or_trailing_rejected=rejected-len(bits), contextual_orientations=orientations)

def build_variant(name, use_alias, B, K, source, baseline, horn):
    signature = {s: a for s, a in baseline['signature'].items() if s not in (*PACKED, 'p_E', 'top')}
    signature.update({('tag_' + s): 0 for s in PACKED})
    signature['H'] = 3
    if use_alias:
        signature['o'] = 0
    cgroups = ((0,), (1,), (2,)) if use_alias else ((0, 1), (2,))
    hgroups = ((0,), (1,)) if use_alias else ((0, 1),)
    equations = [B.SHEFFER, B.TOP_DEFINITION]
    provenance = []
    dropped = []
    for group in baseline['source_groups']:
        indices = tuple(group['source_indices'])
        # Native V/A/U/F congruences are replaced by fixed-selector H laws;
        # C congruence is partitioned; E congruence follows its definition.
        if indices in ((15,), (16,), (18,), (19,), (20,), (21,)):
            dropped.append(indices[0])
            continue
        clauses = [tuple(transformed_literal(l) for l in source[i]) for i in indices]
        equation = tuple(transform(t) for t in group['equation'])
        require(B.check_equation(clauses, equation), 'Retained group Boolean check failed: ' + str(indices))
        equations.append(equation)
        atoms = {B.atom(l) for clause in clauses for l in clause}
        provenance.append(dict(kind='transformed_baseline_group', source_indices=indices, clauses=clauses, equation_before_fusion=equation, boolean_assignments=1 << len(atoms)))
    require(dropped == [15, 16, 18, 19, 20, 21], 'Dropped source clauses changed.')
    cclauses = congruence('C', 3, cgroups)
    hclauses = congruence('H', 2, hgroups, True)
    def schema_clause(name, renaming):
        premises, goal = horn['schemas'][name]
        def rename(t):
            return renaming.get(t, t) if isinstance(t, str) else (t[0], *(rename(x) for x in t[1:]))
        return tuple((False, *rename(t)) for t in premises) + ((True, *rename(goal)),)
    cnames = ('C_0', 'C_1', 'C_2') if use_alias else ('C_pair', 'C_2')
    hnames = ('H_1', 'H_2') if use_alias else ('H_objects',)
    require(source[13] == schema_clause('refl', {}) and source[14] == schema_clause('euclid', {}), 'Equality laws differ from the Horn premises.')
    require(source[16] == schema_clause('C_full', {}), 'Original C congruence differs from the Horn premise.')
    require(source[22] == schema_clause('Inc_congr', {'x': 'x0', 'u': 'y0', 'y': 'x1', 'v': 'y1'}), 'Retained Inc congruence differs from the Horn premise.')
    require(cclauses == [schema_clause(n, {}) for n in cnames], 'C helper schemas do not bind emitted clauses.')
    hrename = {'x0': 't', 'x1': 'x0', 'x2': 'x1', 'y1': 'y0', 'y2': 'y1'}
    require(hclauses == [schema_clause(n, hrename) for n in hnames], 'H helper schemas do not bind emitted clauses.')
    certificate_name = 'derived_membership_congruence_' + ('alias' if use_alias else 'noalias')
    certificate = next(c for c in horn['certificates'] if c['name'] == certificate_name)
    # The helper uses fresh constant names to prove a universally substitutable
    # Horn schema. Bind those names to the exact packet term and variable slots.
    certificate_renaming = {('a',): 'x', ('b',): 'y', ('u',): 'u', ('v',): 'v', ('tA',): ('tag_A',)}
    def bind_certificate_term(t):
        if t in certificate_renaming:
            return certificate_renaming[t]
        return t if isinstance(t, str) else (t[0], *(bind_certificate_term(x) for x in t[1:]))
    def derived_inc(x, y):
        atom = transform(('p_E', x, y))
        if use_alias:
            atom = alias(atom)
        return ('Inc', *atom[1:])
    expected_assumptions = [('Eq', 'x', 'u'), ('Eq', 'y', 'v'), derived_inc('x', 'y')]
    require([bind_certificate_term(t) for t in certificate['assumptions']] == expected_assumptions, 'Membership certificate assumptions do not bind the emitted definition.')
    require(bind_certificate_term(certificate['goal']) == derived_inc('u', 'v'), 'Membership certificate goal does not bind the emitted definition.')
    for symbol, clauses in [('C', cclauses), ('H', hclauses)]:
        for clause in clauses:
            equation = horn_equation(B, clause)
            equations.append(equation)
            provenance.append(dict(kind='partition_congruence', symbol=symbol, clauses=[clause], equation_before_fusion=equation, boolean_assignments=1 << len({B.atom(l) for l in clause})))
    equations = [tuple(fuse(t) for t in equation) for equation in equations]
    if use_alias:
        equations = [tuple(alias(t) for t in equation) for equation in equations] + [(O, ONE)]
    start, target = ('N', D, D), D
    K.Kernel(signature, equations, start, target)
    bits, metrics = B.encode_packet(equations, signature, start, target)
    # Structural ceilings, not assumed bit totals. All bits are measured below.
    require((metrics['signature_symbols'], metrics['local_variable_capacity'], metrics['opcode_width'], metrics['equations']) == ((12, 4, 4, 21) if use_alias else (11, 5, 4, 18)), 'Unexpected signature/capacity/equation census.')
    checks = strict_codec_checks(B, K, signature, equations, start, target, bits)
    require(metrics['both_side_tree_nodes'] == sum(K.nodes(t) for e in equations for t in e), 'Term census mismatch.')
    require(metrics['complete_packet_bits'] == len(bits) == metrics['signature_and_capacity_bits'] + metrics['equation_payload_bits'] + metrics['ground_endpoint_bits'], 'Complete bit accounting failed.')
    payload = dict(name=name, signature=signature, equations=equations, start=start, target=target, transformations=['membership definition', 'fixed-selector dispatch V/A/U/F', 'C and H object-coordinate congruence partitions', 'Boolean truth fused with d'] + (['o = I(d,d) explicit alias'] if use_alias else []), c_partition=cgroups, h_object_partition=hgroups, selector_congruence=False, original_groups=provenance, dropped_original_congruence_clause_indices=dropped, horn_binding=dict(c_schema_names=cnames, h_schema_names=hnames, membership_certificate=certificate_name, membership_assumptions=expected_assumptions, membership_conclusion=derived_inc('u', 'v'), source_equality_clause_indices=[13, 14], source_C_congruence_clause_index=16, source_Inc_congruence_clause_index=22), scope='Finite equational packet with ordinary equisatisfiability proof; no Turing-machine state bound, new consistency proof or internal PA result.')
    return payload, bits, dict(metrics, **checks, checked_boolean_assignments=sum(x['boolean_assignments'] for x in provenance))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reference', type=Path, default=DEFAULT_REFERENCE)
    p.add_argument('--horn-helper', type=Path, default=Path('/tmp/zfc-joint-equational-proof-review/horn_certificates.py'))
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    require(__debug__, 'Run with assertions enabled.')
    require(HORN_SHA is not None, 'Independent Horn helper pin is still pending.')
    output = args.output.resolve()
    require(not output.exists(), 'Fresh output required.')
    require(not output.is_relative_to(args.reference.resolve()) and not output.is_relative_to(HERE), 'Output must be separate from inputs.')
    inputs = {str((args.reference/name).resolve()): expected for name, expected in PINS.items()}
    inputs[str(args.horn_helper.resolve())] = HORN_SHA
    inputs[str(Path(__file__).resolve())] = sha(__file__)
    for path, expected in inputs.items():
        require(sha(path) == expected, 'Input identity changed: ' + path)
    K = load_module('equational_search', args.reference/'equational_search.py')
    B = load_module('joint_packet_build_equations', args.reference/'build_equations.py')
    H = load_module('joint_packet_horn_certificates', args.horn_helper)
    source = K.freeze(json.loads((args.reference/'FC13B_complete.json').read_text()))
    baseline_raw = json.loads((args.reference/'baseline_grouped.json').read_text())
    baseline = dict(baseline_raw, equations=K.freeze(baseline_raw['equations']), source_groups=[dict(g, equation=K.freeze(g['equation'])) for g in baseline_raw['source_groups']])
    require(len(source) == 23 and len(baseline['source_groups']) == 19, 'Baseline clause/group census changed.')
    for group in baseline['source_groups']:
        require(B.check_equation([source[i] for i in group['source_indices']], group['equation']), 'Original Boolean group failed.')
    basebits, basemetrics = B.encode_packet(baseline['equations'], baseline['signature'], K.freeze(baseline['start']), K.freeze(baseline['target']))
    require(basemetrics['complete_packet_bits'] == 2324, 'Wrong inherited baseline.')
    require(B.decode_packet(basebits, list(baseline['signature'])) == (baseline['signature'], [B.canonical_equation(e) for e in baseline['equations']], K.freeze(baseline['start']), K.freeze(baseline['target'])), 'Baseline roundtrip failed.')
    horn = H.verify_certificates()
    require(horn['status'] == 'FINITE_SYNTACTIC_HORN_CERTIFICATES_PASS' and horn['certificate_count'] == 12 and horn['inference_count'] == 49 and horn['findings'] == [], 'Horn certificate replay failed.')
    output.mkdir(parents=True)
    result = dict(status='RUNNING', before=inputs, baseline=basemetrics, horn_certificates=horn, variants={}, supplied_search_executed=False, simulator_executed=False, compiler_executed=False)
    def save():
        (output/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
    save()
    try:
        for name, use_alias in [('dispatch_no_alias', False), ('dispatch_split_alias', True)]:
            payload, bits, metrics = build_variant(name, use_alias, B, K, source, baseline, horn)
            (output/(name+'.json')).write_text(json.dumps(payload, indent=2)+'\n')
            (output/(name+'.bits')).write_text(bits+'\n')
            (output/(name+'.equations')).write_text('\n'.join(f'{i}: {B.pretty(a)} = {B.pretty(b)}' for i, (a, b) in enumerate(payload['equations']))+'\n')
            result['variants'][name] = dict(metrics, files={suffix: dict(path=str(output/(name+suffix)), sha256=sha(output/(name+suffix))) for suffix in ('.json', '.bits', '.equations')})
            save()
        result['after'] = {path: sha(path) for path in inputs}
        require(result['after'] == result['before'], 'Inputs changed during execution.')
        result['status'] = 'PASS_FINITE_PACKET_CHECKS'
    except BaseException as exc:
        result.update(status='FAIL', error=repr(exc), after={path: sha(path) for path in inputs})
        save()
        raise
    save()
    print(json.dumps(result['variants'], indent=2))

if __name__ == '__main__':
    main()
