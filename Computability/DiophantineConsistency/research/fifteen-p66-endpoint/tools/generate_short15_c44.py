"""Emit or check the Lean let-chains of package 66's fifteen-positive circuits,
and check that their fixed numerals are the compact44 original-order tuple.

Usage: py -I -X utf8 -S -B generate_short15_c44.py TARGET   (print one block)
       py -I -X utf8 -S -B generate_short15_c44.py --check  (check everything)

Targets (each JSON pinned by SHA-256):

  p78  66-gap-congruence/algebra/p15_78_degree30.json  -> Compact44/P66p78Graph.lean
  p87  66-gap-congruence/algebra/p15_87_degree26.json  -> Compact44/P66p87Graph.lean
  p88  66-gap-congruence/algebra/p15_88_degree24.json  -> Compact44/P66p88Graph.lean

The inputs are `.var 0 .. .var 14` in the JSON `witnesses` order and the four
fixed numerals `beta K0 MC MF` are the `let`-bound `.constant (p 0..3)` leaves;
gates keep their JSON names. With --check, the block between the markers of
each Lean module must equal the emitted block exactly.

Coefficient binding. The JSONs name `coefficients/COEFFICIENT_BINDING.json`
with aliases `beta K0 MC MF -> beta K MC MF_source`; package 66 does not carry
that directory, but its two hash lists pin the binding file and the four gzip
payloads. The checker verifies that

* package 66's `SHA256SUMS.json` and `algebra/SHA256SUMS.json`, and package
  58's `MANIFEST.sha256` (the cited source of the circuits), pin the same
  binding-file and payload hashes;
* the tree's retained compact44 copies
  (`candidates/free-j-polarized-positive/source/positive/coefficients/`) have
  exactly those bytes: the binding file `recipe/COEFFICIENT_BINDING.json` and
  `payloads/{beta,K,MC,MF_source}.bin.gz`;
* the decoded raw payloads match `BINDING.json` there, in particular K raw
  SHA-256 `c6d523bd...`, the original-order K payload that the external
  transcription of `paramKernel rho` reproduces
  (`reviews/compact44-k-four-port-source-review`);
* each circuit's `transformation.source_sha256` is package 58's circuit.

This is an external byte comparison, as for packages 64 and 65; it is not a
Lean theorem about the payload bytes.
"""
import gzip, hashlib, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
FORMS = os.path.join(ROOT, 'con-zfc-diophantine-forms')
P66 = os.path.join(FORMS, '66-gap-congruence')
P58 = os.path.join(FORMS, '58-integral-root')
RETAINED = os.path.join(ROOT, 'candidates', 'free-j-polarized-positive', 'source', 'positive',
                        'coefficients')
LEAN = os.path.join(ROOT, 'Lean', 'DiophantineConsistency', 'Compact44')

BINDING_SHA = '0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783'
GZ = {'beta': '466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
      'K': 'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a',
      'MC': '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
      'MF_source': '935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b'}
RAW = {'beta': '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d',
       'K': 'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e',
       'MC': '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
       'MF_source': '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737'}
BITS = {'beta': 590069, 'K': 592884, 'MC': 590069, 'MF_source': 590070}
ALIASES = {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}

W78 = ['J', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'w', 'Y', 'r', 'eta', 'zeta', 'u', 'gamma']
W87 = ['j', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'X', 'Y', 'r', 'eta', 'zeta', 'u', 'gamma']

TARGETS = {
    'p78': ('p15_78_degree30.json', 'df49ad7c9b3c538c5f5f340e7ee6e380e1b0dbe1c3ed174977fa4852210d073f',
            'P66p78Graph.lean', W78, 78, 30, ['A', 'paired', 'auxiliary', 'strong'], 'sum_3',
            'p15_degree30.json', '2623733d4d53b78eab892e0b5b579ae41e2b78624ae6890c6914c71cbfdc30c0'),
    'p87': ('p15_87_degree26.json', 'e6b90695eedd69d1458609368f2c5dde191548229de5e4b84280365a5491789e',
            'P66p87Graph.lean', W87, 87, 26, ['A', 'B', 'coupled', 'auxiliary', 'strong'], 'sum_4',
            'p15_degree26.json', 'b4104f1b9d2a88ac255b5489da754feb54ecd6fbfc4de95ae8ea46d56d8f3fb1'),
    'p88': ('p15_88_degree24.json', '90e6281e5e315f3ad283775c785ac2f784244d9e8f48c88d2a0814486de06c46',
            'P66p88Graph.lean', W87, 88, 24,
            ['A', 'B', 'index_res', 'transport_res', 'auxiliary', 'strong'], 'sum_5',
            'p15_degree24.json', '39d785143cef12766127398ced6e2680b85ed182a636248737764892746c20ae'),
}


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def manifest(path):
    out = {}
    for line in open(path, encoding='utf-8'):
        m = re.match(r'([0-9a-f]{64})\s+\*?(.+?)\s*$', line)
        if m:
            out[m.group(2)] = m.group(1)
    return out


def check_tuple():
    """The four fixed numerals are the compact44 original-order tuple."""
    sums66 = json.load(open(os.path.join(P66, 'SHA256SUMS.json'), encoding='utf-8'))
    alg = json.load(open(os.path.join(P66, 'algebra', 'SHA256SUMS.json'), encoding='utf-8'))
    assert sums66['algebra/SHA256SUMS.json'] == sha(os.path.join(P66, 'algebra', 'SHA256SUMS.json'))
    assert sums66['algebra/coefficients/COEFFICIENT_BINDING.json'] == BINDING_SHA
    assert alg['coefficients/COEFFICIENT_BINDING.json'] == BINDING_SHA
    m58 = manifest(os.path.join(P58, 'MANIFEST.sha256'))
    assert m58['coefficients/COEFFICIENT_BINDING.json'] == BINDING_SHA
    for port, h in GZ.items():
        assert sums66[f'algebra/coefficients/coefficients/{port}.bin.gz'] == h, port
        assert alg[f'coefficients/coefficients/{port}.bin.gz'] == h, port
        assert m58[f'coefficients/coefficients/{port}.bin.gz'] == h, port
    # the retained compact44 copies
    assert sha(os.path.join(RETAINED, 'recipe', 'COEFFICIENT_BINDING.json')) == BINDING_SHA
    rb = json.load(open(os.path.join(RETAINED, 'recipe', 'COEFFICIENT_BINDING.json'), encoding='utf-8'))
    assert rb['instance'] == 'wang943-complement67-shared-anchor-length8807-prime581197'
    assert rb['d'] == 590069 and rb['b'] == 67 and rb['L'] == 8807
    bd = json.load(open(os.path.join(RETAINED, 'BINDING.json'), encoding='utf-8'))
    for lean_port, up in ALIASES.items():
        e = bd['ports'][lean_port]
        assert e['upstream_port'] == up, lean_port
        assert e['sha256_gzip'] == GZ[up] and e['sha256_raw'] == RAW[up], lean_port
        gzb = open(os.path.join(RETAINED, 'payloads', up + '.bin.gz'), 'rb').read()
        assert hashlib.sha256(gzb).hexdigest() == GZ[up], up
        raw = gzip.decompress(gzb)
        assert hashlib.sha256(raw).hexdigest() == RAW[up], up
        assert int.from_bytes(raw, 'little').bit_length() == BITS[up], up
    return sums66, alg, m58


def block(target, sums):
    fname, pin, _, inputs, nops, degree, residuals, output, src58, pin58 = TARGETS[target]
    sums66, alg, m58 = sums
    path = os.path.join(P66, 'algebra', fname)
    raw = open(path, 'rb').read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != pin:
        sys.exit(f'{target}: source hash {digest} differs from pin {pin}')
    assert sums66['algebra/' + fname] == pin and alg[fname] == pin, target
    d = json.loads(raw.decode('utf-8'))
    assert d['witnesses'] == inputs, (target, d['witnesses'])
    assert d['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'], target
    assert d['port_aliases'] == ALIASES, target
    assert d['coefficient_binding_file'] == 'coefficients/COEFFICIENT_BINDING.json', target
    assert d['domain'] == 'strictly positive integers', target
    assert d['residuals'] == residuals and d['output'] == output, target
    assert d['operations'] == nops == len(d['source']) and d['exact_degree'] == degree, target
    assert d['transformation']['source_sha256'] == pin58 == m58['circuits/' + src58], target
    assert sha(os.path.join(P58, 'circuits', src58)) == pin58, target
    known = set(inputs) | {'beta', 'K0', 'MC', 'MF'}
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
    assert d['source'][-1][0] == output
    return '\n'.join(lines), digest, nops


if len(sys.argv) == 2 and sys.argv[1] == '--check':
    sums = check_tuple()
    print('ok tuple: package 66 and 58 pin binding '
          f'{BINDING_SHA[:16]}... and the four gzip payloads; retained compact44 copies match; '
          f'K raw {RAW["K"][:16]}... (original order), beta/MC/MF raw match BINDING.json')
    for t, spec in TARGETS.items():
        text = open(os.path.join(LEAN, spec[2]), encoding='utf-8').read()
        start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
        end = text.index('  -- END LITERAL GRAPH')
        b, digest, nops = block(t, sums)
        if text[start:end].rstrip('\n') != b:
            sys.exit(f'{t}: Lean graph block of {spec[2]} differs from the JSON circuit')
        print(f'ok {t}: {nops} gates match {spec[2]}; source sha256 {digest}; '
              f'package 58 source {spec[9][:16]}...')
elif len(sys.argv) == 2 and sys.argv[1] in TARGETS:
    print(block(sys.argv[1], check_tuple())[0])
else:
    sys.exit(__doc__)
