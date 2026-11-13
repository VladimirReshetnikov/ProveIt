"""Emit or check the Lean let-chains of package 54's fifteen-positive gate lists,
instantiated at the 121x8801 ports.

Usage: py -I -X utf8 -S -B generate_short15_p54.py TARGET       (print one block)
       py -I -X utf8 -S -B generate_short15_p54.py --check      (check all modules)
       py -I -X utf8 -S -B generate_short15_p54.py --mutations  (self-test: mutants must fail)

Targets (each JSON pinned by SHA-256):

  p70  54-calibrated-carry/positive/p70_degree80.json  -> Mixed121/P54p70Graph.lean
  p71  54-calibrated-carry/positive/p71_degree78.json  -> Mixed121/P54p71Graph.lean
  p72  54-calibrated-carry/positive/p72_degree64.json  -> Mixed121/P54p72Graph.lean

PORT BINDING. Package 54's JSONs bind their four fixed numerals beta, K0, MC, MF
to its own tuple `complemented-factorized-receiver-89x4831` (native base
2^429959, `native/COEFFICIENT_BINDING.json`). That tuple is NOT calibrated in
the Lean tree. The Lean modules use only 54's gate lists: the fixed numerals are
the `let`-bound leaves `.constant (p 0..3)`, and each endpoint instantiates `p`
at `Short15ConvData.intPorts`, i.e. `Mixed121Ports.ports`, the
wang943-mixed-121x8801 tuple whose payload hashes are package 55's
(`55-congruence-norms/fourteen/coefficients/ports.json`). This script checks
that 54's own port hashes are four different payloads (so the Lean equations are
NOT 54's literal c54-port equations), that both tuples use the same shifted
`MF_source` convention for the port named MF, and that each endpoint module
instantiates the graph at `intPorts`.

The inputs are `.var 0 .. .var 14` in the JSON order; gates keep their JSON
names. With --check, every block between the markers of each Lean module must
equal the emitted block exactly.
"""
import copy, hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
FORMS = os.path.join(ROOT, 'con-zfc-diophantine-forms')
LEAN = os.path.join(ROOT, 'Lean', 'DiophantineConsistency', 'Mixed121')
PORTS55 = os.path.join(FORMS, '55-congruence-norms', 'fourteen', 'coefficients', 'ports.json')
P54 = os.path.join(FORMS, '54-calibrated-carry')
BIND54 = os.path.join(P54, 'native', 'COEFFICIENT_BINDING.json')

FIXED = ['beta', 'K0', 'MC', 'MF']
BASE = ['J', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 's', 'w', None, 'eta', 'zeta', None, 'gamma']


def wit(a, b):
    return BASE[:10] + [a] + BASE[11:13] + [b] + BASE[14:]


TARGETS = {
    'p70': ('p70_degree80.json', 'dc5dd19d068b5886a7efc2311f32018506a6ff52e211ecfc58b9a6cc08373603',
            'P54p70Graph.lean', 'IPRAPositive54p70.lean', wit('tau', 'y'), 70, 80, (39, 17, 14)),
    'p71': ('p71_degree78.json', '684988711ad2bcb6794b48e02b148aae82398ca4b74e1768e4f2c100e1b16c73',
            'P54p71Graph.lean', 'IPRAPositive54p71.lean', wit('r', 'y'), 71, 78, (40, 17, 14)),
    'p72': ('p72_degree64.json', 'a3c80bd9bc91d32ef8e0b1be7ee14fd2952f86a6aba3169868d373494b820946',
            'P54p72Graph.lean', 'IPRAPositive54p72.lean', wit('r', 'u'), 72, 64, (40, 18, 14)),
}


def hashes(path, n=4):
    return re.findall(r'"(?:raw_)?sha256": *"([0-9a-f]{64})"', open(path, encoding='utf-8').read())[:n]


def check_ports():
    """54's ports are its own c54 tuple, disjoint from 55's 121x8801 payloads."""
    pins55 = hashes(PORTS55)
    p55 = json.load(open(PORTS55, encoding='utf-8'))
    b54 = json.load(open(BIND54, encoding='utf-8'))
    assert p55['instance'] == 'wang943-mixed-121x8801', p55['instance']
    assert b54['coefficient_instance'] == 'complemented-factorized-receiver-89x4831'
    assert b54['native_base_exponent'] == 429959
    pins54 = [p['sha256'] for p in b54['ports']]
    assert [p['name'] for p in b54['ports']] == ['beta', 'K', 'MC', 'MF_source']
    assert [p['file'] for p in p55['ports']] == ['beta.bin.gz', 'K.bin.gz', 'MC.bin.gz', 'MF_source.bin.gz']
    assert b54['binding'] == {'beta': 'beta.bin.gz', 'K0': 'K.bin.gz', 'MC': 'MC.bin.gz',
                              'MF': 'MF_source.bin.gz'}, b54['binding']
    assert 'shift' in p55['warning'].lower() or 'shifted' in p55['warning'].lower()
    assert 'already equals MF_native+B-1' in b54['MF_convention']
    assert len(pins55) == 4 and len(pins54) == 4
    assert not set(pins54) & set(pins55), 'package 54 shares a port payload with package 55'
    return pins54, pins55


def block(target, data=None):
    source, pin, _, _, inputs, nops, degree, counts = TARGETS[target]
    if data is None:
        raw = open(os.path.join(P54, 'positive', source), 'rb').read()
        digest = hashlib.sha256(raw).hexdigest()
        if digest != pin:
            raise SystemExit(f'{target}: source hash {digest} differs from pin {pin}')
        d = json.loads(raw.decode('utf-8'))
    else:
        d, digest = data, 'mutant'
    assert d['witnesses'] == inputs, (target, d['witnesses'])
    assert d['fixed_numerals'] == FIXED, (target, d['fixed_numerals'])
    assert d['witness_domain'] == 'strictly positive integers'
    assert d['coefficient_binding']['aliases'] == {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}
    assert d['output'] == 'polynomial' and len(d['source']) == nops == d['operations'], (target, len(d['source']))
    assert d['exact_degree'] == degree
    tally = [sum(1 for g in d['source'] if g[1] == o) for o in '*+-']
    assert tuple(tally) == counts and d['operation_counts'] == dict(zip('*+-', counts)), (target, tally)
    known = set(inputs) | set(FIXED)
    lines = []
    for name, op, a, b in d['source']:
        assert op in '+-*' and name not in known, (name, op)
        ops = []
        for x in (a, b):
            if isinstance(x, int):
                assert x >= 0
                ops.append(str(x))
            else:
                assert x in known, x
                ops.append(x)
        lines.append(f'  let {name} := {ops[0]} {op} {ops[1]}')
        known.add(name)
    assert d['source'][-1][0] == 'polynomial'
    return '\n'.join(lines), digest, nops


def lean_block(target):
    text = open(os.path.join(LEAN, TARGETS[target][2]), encoding='utf-8').read()
    start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
    end = text.index('  -- END LITERAL GRAPH')
    head = text[:start]
    for j, x in enumerate(TARGETS[target][4]):
        assert f'  let {x} : Expr (Fin 15) := .var {j}\n' in head, (target, x)
    for j, x in enumerate(FIXED):
        assert f'  let {x} : Expr (Fin 15) := .constant (p {j})\n' in head, (target, x)
    return text[start:end].rstrip('\n')


def check_endpoint(target):
    graph = TARGETS[target][2][:-5]
    text = open(os.path.join(LEAN, TARGETS[target][3]), encoding='utf-8').read()
    assert f'def expression : Expr (Fin 15) := ({graph}.graph intPorts).output' in text, target
    assert 'open Short15ConvData (intPorts)' in text, target


def mutants(d):
    """A few corruptions of a gate list; each must be rejected by --check."""
    out = []
    m = copy.deepcopy(d); m['source'][5][1] = '+'; out.append(('operator', m))
    m = copy.deepcopy(d); g = m['source'][4]; g[2], g[3] = g[3], g[2]; out.append(('operand order', m))
    m = copy.deepcopy(d)
    g = next(g for g in m['source'] if g[0] == 'H'); g[3] = 4; out.append(('numeral', m))
    m = copy.deepcopy(d)
    g = next(g for g in m['source'] if g[0] == 'aux_minus_two'); g[3] = 1; out.append(('finalizer constant', m))
    m = copy.deepcopy(d)
    g = next(g for g in m['source'] if g[0] == 'Nt'); g[2] = 'transport'; out.append(('wiring', m))
    m = copy.deepcopy(d); m['witnesses'][3], m['witnesses'][7] = m['witnesses'][7], m['witnesses'][3]
    out.append(('witness order', m))
    m = copy.deepcopy(d); del m['source'][20]; out.append(('dropped gate', m))
    return out


if len(sys.argv) == 2 and sys.argv[1] == '--check':
    pins54, pins55 = check_ports()
    for t, spec in TARGETS.items():
        b, digest, nops = block(t)
        if lean_block(t) != b:
            raise SystemExit(f'{t}: Lean graph block of {spec[2]} differs from the JSON circuit')
        check_endpoint(t)
        print(f'ok {t}: {nops} gates (degree {spec[6]}) match {spec[2]}; source sha256 {digest}; '
              f'{spec[3]} instantiates at intPorts')
    print('ports: Lean endpoints use package 55\'s 121x8801 payloads ' + ', '.join(h[:12] for h in pins55))
    print('ports: NOT the JSONs\' own c54 payloads ' + ', '.join(h[:12] for h in pins54)
          + ' (complemented-factorized-receiver-89x4831, base 2^429959: uncalibrated)')
elif len(sys.argv) == 2 and sys.argv[1] == '--mutations':
    for t, spec in TARGETS.items():
        d = json.load(open(os.path.join(P54, 'positive', spec[0]), encoding='utf-8'))
        lean = lean_block(t)
        assert block(t, d)[0] == lean
        for name, m in mutants(d):
            try:
                rejected = block(t, m)[0] != lean
            except (AssertionError, KeyError, IndexError):
                rejected = True
            if not rejected:
                raise SystemExit(f'{t}: mutation "{name}" was NOT rejected')
            print(f'ok {t}: mutation "{name}" rejected')
elif len(sys.argv) == 2 and sys.argv[1] in TARGETS:
    print(block(sys.argv[1])[0])
else:
    raise SystemExit(__doc__)
