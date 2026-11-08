"""Emit or check the Lean let-chains of the fifteen-positive 121x8801 circuits.

Usage: py -I -X utf8 -S -B generate_short15.py TARGET      (print one block)
       py -I -X utf8 -S -B generate_short15.py --check     (check all modules)

Targets (each JSON pinned by SHA-256; its four fixed numerals must be bound to
package 55's four payload hashes, i.e. the wang943-mixed-121x8801 tuple):

  p69  59-degree-separated/short/circuits/p69_d91.json    -> Mixed121/P59p69Graph.lean
  p68  59-degree-separated/short/circuits/p68_d101.json   -> Mixed121/P59p68Graph.lean
  p67  59-degree-separated/short/circuits/p67_d125.json   -> Mixed121/P59p67Graph.lean
  q54  56-free-coordinate/.../ordinary_gap_minima73_squared_modulus_degree54.json
                                                          -> Mixed121/P56q54Graph.lean
  q46  56-free-coordinate/.../gap_minima74_squared_modulus_degree46.json
                                                          -> Mixed121/P56q46Graph.lean
  p75  47-sparse-support/minima/gap_minima75.json         -> Mixed121/P47p75Graph.lean

The inputs are `.var 0 .. .var 14` in the JSON order and the four fixed numerals
are the `let`-bound `.constant (p 0..3)` leaves; gates keep their JSON names.
With --check, every block between the markers of each Lean module must equal
the emitted block exactly.
"""
import hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
FORMS = os.path.join(ROOT, 'con-zfc-diophantine-forms')
LEAN = os.path.join(ROOT, 'Lean', 'DiophantineConsistency', 'Mixed121')
PORTS55 = os.path.join(FORMS, '55-congruence-norms', 'fourteen', 'coefficients', 'ports.json')

P59 = os.path.join(FORMS, '59-degree-separated', 'short')
P56 = os.path.join(FORMS, '56-free-coordinate', 'short', 'generated')
P47 = os.path.join(FORMS, '47-sparse-support', 'minima')

W59 = ['J', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 's', 'w', None, 'eta', 'zeta', 'y', 'gamma']
W56 = ['Jrep', 'F', 'alpha', 'transport_quotient', 'f', 'h', 'i', 'auxiliary_quotient', 's', 'w',
       'tau_root', 'eta', 'zeta', 'auxiliary_gap', 'gamma']

TARGETS = {
    'p69': (os.path.join(P59, 'circuits', 'p69_d91.json'),
            '6ff5c3483b968a732fe1ec8a66bdad8c409b26b26c85403f5c9ba1f00344299b',
            'P59p69Graph.lean', W59[:10] + ['r'] + W59[11:], ['beta', 'K0', 'MC', 'MF'], 69, 'p59'),
    'p68': (os.path.join(P59, 'circuits', 'p68_d101.json'),
            '7f49ee83172f406cbd36e87602abc61bc7be80e29b054489e0a6824705a2e1fb',
            'P59p68Graph.lean', W59[:10] + ['tau'] + W59[11:], ['beta', 'K0', 'MC', 'MF'], 68, 'p59'),
    'p67': (os.path.join(P59, 'circuits', 'p67_d125.json'),
            '3fedfef91a401be393ace0fd36476dc3d26e77a1e123f2ca13bdfca8ee9bae74',
            'P59p67Graph.lean', W59[:10] + ['tau'] + W59[11:], ['beta', 'K0', 'MC', 'MF'], 67, 'p59'),
    'q54': (os.path.join(P56, 'ordinary_gap_minima73_squared_modulus_degree54.json'),
            '20924fade8733da84904e75700a65d9480205254305b697b5bb9a9df1b397aac',
            'P56q54Graph.lean', W56, ['Bm1', 'Kconstant', 'MC', 'MF'], 73, 'p56'),
    'q46': (os.path.join(P56, 'gap_minima74_squared_modulus_degree46.json'),
            'e40786771047909c5b70051e926394127437049cd79c2a058e911225b9b52021',
            'P56q46Graph.lean', W56, ['Bm1', 'Kconstant', 'MC', 'MF'], 74, 'p56'),
    'p75': (os.path.join(P47, 'gap_minima75.json'),
            '00e2d7f8a199f77f40139d83a896b91fc69b877082128511b31c0ab66df1bdba',
            'P47p75Graph.lean', W56, ['Bm1', 'Kconstant', 'MC', 'MF'], 75, 'p47'),
}


def hashes(path, n=4):
    return re.findall(r'"(?:raw_)?sha256": *"([0-9a-f]{64})"', open(path, encoding='utf-8').read())[:n]


PINS55 = hashes(PORTS55)
assert len(PINS55) == 4


def check_binding(kind):
    """The four ports of the package are package 55's payloads (beta, K, MC, MF), in order."""
    if kind == 'p59':
        pins = hashes(os.path.join(P59, 'COEFFICIENT_BINDING.json'))
    elif kind == 'p56':
        sums = json.load(open(os.path.join(FORMS, '56-free-coordinate', 'SHA256SUMS.json'),
                              encoding='utf-8'))
        base = 'short/coefficients31/payloads/'
        pins = [sums[base + n + '.bin'] for n in ('beta', 'K', 'MC', 'MF_source')]
    else:
        pins = hashes(os.path.join(P47, 'fixed_coefficients.json'))
    assert pins == PINS55, (kind, pins, PINS55)


def block(target):
    source, pin, _, inputs, fixed, nops, kind = TARGETS[target]
    raw = open(source, 'rb').read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != pin:
        sys.exit(f'{target}: source hash {digest} differs from pin {pin}')
    d = json.loads(raw.decode('utf-8'))
    assert d['witnesses'] == inputs, (target, d['witnesses'])
    assert d['fixed_numerals'] == fixed, (target, d['fixed_numerals'])
    assert d['output'] == 'polynomial' and len(d['source']) == nops, (target, len(d['source']))
    check_binding(kind)
    known = set(inputs) | set(fixed)
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


if len(sys.argv) == 2 and sys.argv[1] == '--check':
    for t, spec in TARGETS.items():
        text = open(os.path.join(LEAN, spec[2]), encoding='utf-8').read()
        start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
        end = text.index('  -- END LITERAL GRAPH')
        b, digest, nops = block(t)
        if text[start:end].rstrip('\n') != b:
            sys.exit(f'{t}: Lean graph block of {spec[2]} differs from the JSON circuit')
        print(f'ok {t}: {nops} gates match {spec[2]}; source sha256 {digest}; ports = package 55 ports')
elif len(sys.argv) == 2 and sys.argv[1] in TARGETS:
    print(block(sys.argv[1])[0])
else:
    sys.exit(__doc__)
