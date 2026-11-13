"""Port a Compact44 converse module to 121x8801 by exact constant substitution.

Usage: py -I -X utf8 -S -B const_port.py SOURCE_MODULE TARGET_MODULE [--rename OLD=NEW ...]

SOURCE_MODULE and TARGET_MODULE are module names relative to
`Lean/DiophantineConsistency`, e.g. `Compact44.ArithmeticControllerDataCompact44`
and `Mixed121.Mixed121ControllerData`. Every numeral in CONSTANTS is replaced at
word boundaries. `--rename` maps further identifiers (namespaces, module names);
each OLD is replaced at identifier boundaries, longest first. Imports of modules
named in a rename are retargeted too.

The script refuses to write if any Compact44-only numeral survives
(see FORBIDDEN). It is a transcription aid: the Lean build is the check.
Every replacement value is derived in `controller_constants()` below and
asserted against its defining property.
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'Lean', 'DiophantineConsistency'))


def controller_constants():
    d44, p44 = 67 * 8807, 581197
    d, p = 121 * 8801, 2341
    assert d == 11**2 * 13 * 677
    g44 = pow(2, d44 * (p44 - 1), d44 * p44 * p44)
    g = pow(2, d * (p - 1), d * p * p)
    C0 = d * p
    assert g % C0 == 1
    v = (g - 1) // C0 % p
    assert v == 1556 and (d * v) % p == 1092      # recipe §4: B^2340 = 1 + 1092*2341 mod 2341^2
    vinv = pow(v, -1, p)
    assert (v * vinv) % p == 1 and v * C0 + 1 == g
    return {
        590069: d,                       # block width d = b*L
        581197: p,                       # auxiliary prime
        581196: p - 1,
        290598: (p - 1) // 2,
        295034: (d - 1) // 2,
        502425: v,
        134409: vinv,
        172304811153038026: g,           # g mod d*p^2
        199319379664053821: d * p * p,
        342945742524: d * (p - 1),
        342946332593: C0,
        8807: 8801,
        8806: 8800,
    }


CONSTANTS = controller_constants()
FORBIDDEN = [str(k) for k in CONSTANTS]


def main(argv):
    if len(argv) < 3:
        sys.exit(__doc__)
    src, dst = argv[1], argv[2]
    renames, extra = {}, {}
    rest = argv[3:]
    while rest:
        if rest[0] not in ('--rename', '--extra') or len(rest) < 2 or '=' not in rest[1]:
            sys.exit('bad arguments: ' + ' '.join(rest))
        old, new = rest[1].split('=', 1)
        (renames if rest[0] == '--rename' else extra)[old] = new
        rest = rest[2:]
    path = lambda m: os.path.join(LEAN, *m.split('.')) + '.lean'
    text = open(path(src), encoding='utf-8').read()
    for old in sorted(renames, key=len, reverse=True):
        text = re.sub(r'(?<![\w])' + re.escape(old) + r'(?![\w])', renames[old], text)
        text = re.sub(r'(?<=import DiophantineConsistency\.)' + re.escape(old) + r'\b',
                      renames[old], text)
    # module-specific numerals first (they take precedence over CONSTANTS)
    for old in sorted(extra, key=len, reverse=True):
        pat = r'(?<![\d.])' + re.escape(old) + r'(?![\d])'
        if not re.search(pat, text):
            sys.exit(f'--extra {old} does not occur')
        text = re.sub(pat, extra[old], text)
    for k in sorted(CONSTANTS, key=lambda k: -len(str(k))):
        text = re.sub(r'(?<![\d.])' + str(k) + r'(?![\d])', str(CONSTANTS[k]), text)
    left = [f for f in FORBIDDEN if re.search(r'(?<![\d.])' + f + r'(?![\d])', text)]
    if left:
        sys.exit(f'refusing: Compact44 numerals survive: {left}')
    out = path(dst)
    if os.path.exists(out):
        sys.exit(f'refusing to overwrite {out}')
    with open(out, 'w', encoding='utf-8', newline='\n') as f:
        f.write(text)
    print(f'wrote {out}')


if __name__ == '__main__':
    main(sys.argv)
