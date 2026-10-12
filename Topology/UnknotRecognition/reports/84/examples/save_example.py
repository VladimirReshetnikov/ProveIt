"""Create the saved algebraic example; this is not a knot or geometric proof."""
from dataclasses import asdict
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from interface_homology import Core, Loop, Surface, Model, condense, wire
from interface_homology.smith import smith


def main() -> None:
    model = Model(Core(vertices=1, edges=((0, 0),)), (
        Surface(orientable=False, complexity=1, boundary=1,
                circles=(Loop(anchor=0, word=(1, 1)),)),))
    packet = condense(model)
    normal = smith(packet.matrix, cols=packet.relation_count)
    bundle = {
        'schema': 'saved-algebraic-interface-example-v1',
        'trust': 'Abstract algebraic model only; no certified source cut or S3 embedding.',
        'model': asdict(model),
        'condensation': packet.payload(),
        'smith': asdict(normal),
    }
    destination = ROOT / 'examples' / 'mobius_certificate.json'
    destination.write_text(json.dumps(wire(bundle), indent=2, sort_keys=True) + '\n')
    print(destination.name)


if __name__ == '__main__':
    main()
