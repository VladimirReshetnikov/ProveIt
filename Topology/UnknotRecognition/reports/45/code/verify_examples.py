"""Replay the two shipped examples. Neither file supplies arbitrary knot provenance."""
from pathlib import Path
import json
from types import SimpleNamespace
from checker import verify_power
from braid_bridge import verify_braid_certificate


def main() -> None:
    data = Path(__file__).resolve().parents[1] / 'data'
    word = json.loads((data / 'example_word_certificate.json').read_text())
    fields = word['certificate']
    certificate = SimpleNamespace(root=fields['root'], **{
        name: int(fields[name], 16) for name in ('u', 'v', 'exponent', 'width')
    })
    if not verify_power(word['rules'], certificate):
        raise ValueError('Invalid algebraic example certificate')
    braid = json.loads((data / 'example_braid_certificate.json').read_text())
    # Bind to the specified source, rather than accepting a source from the file.
    if not verify_braid_certificate(3, [1, 2], braid['certificate']):
        raise ValueError('Invalid source-bound braid example certificate')
    print('Both shipped examples replay successfully; the word example is algebraic only.')


if __name__ == '__main__':
    main()
