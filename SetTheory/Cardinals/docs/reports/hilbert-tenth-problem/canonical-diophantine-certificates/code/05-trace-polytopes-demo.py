#!/usr/bin/env python3
"""Small end-to-end examples. Run from any working directory."""
from pathlib import Path
import json
from trace_polytope import Net, compile_certificate


def main() -> None:
    out = Path(__file__).resolve().parents[1] / 'results'
    out.mkdir(exist_ok=True)
    net = Net(pre=((0,), (0,), (1,)), post=((1,), (0,), (0,)),
              names=('a', 'b', 'c'))
    cert = compile_certificate(net, (1,), (1,), 3)
    word = (1, 2, 0)  # b,c,a is the normal form of c,a,b.
    z = cert.witness(word)
    if not cert.zero(z) or cert.decode(z) != word:
        raise RuntimeError('Unexpected witness failure.')
    print(f'Ordinary example: {len(cert.variables)} variables, '
          f'{len(cert.residuals)} residuals; energy {cert.energy(z)}')
    guarded = compile_certificate(net, (0,), (0,), 3,
                                  upper=((None,), (0,), (None,)))
    z2 = guarded.witness((0, 2, 1))  # increment, decrement, zero-test.
    guarded.export(str(out / 'example_guarded.json'))
    (out / 'witness_guarded.json').write_text(json.dumps(z2, indent=2) + '\n')
    print(f'Guarded example: {len(guarded.variables)} variables, '
          f'{len(guarded.residuals)} residuals; energy {guarded.energy(z2)}')


if __name__ == '__main__':
    main()
