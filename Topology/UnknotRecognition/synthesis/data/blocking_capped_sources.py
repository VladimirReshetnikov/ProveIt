"""Independent topology controls for the two newly completed span queries.

Run from fast with PYTHONPATH=. and the optional Regina environment.
This is a correctness audit, not a performance benchmark.
"""
from hashlib import sha256
import json
from pathlib import Path

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from normal_orbit_research import blocking, seeds
from normal_orbit_research.fixtures import regina_triangulation, regina_surface

before = blocking.pins()
records = []
for entry in json.loads(blocking.SOURCE.read_text())['cases']:
    source = entry['source']
    if source['name'] not in ('gordian', 'circle-33'): continue
    diagram = Diagram.from_pd(source['pd'])
    raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
    result = minimize_cocycle_span(seed['vertices'], seed['heights'], max_work=2000000)
    proof = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                 triangulation=raw, heights=seed['heights'], coordinates=result['coordinates'],
                 span_certificate=result['certificate'])
    summary = inspect_cocycle_certificate(diagram, proof)
    surface = regina_surface(regina_triangulation(raw), result['coordinates'])
    components = surface.components()
    discs = sum(int(str(s.eulerChar())) == 1 and s.isCompressingDisc(True) for s in components)
    assert summary['components'] == len(components) == 1
    assert surface.isOrientable()
    assert summary['euler_characteristic'] == int(str(surface.eulerChar()))
    assert summary['compressing_discs'] == discs
    record = dict(name=source['name'], crossings=len(source['pd']), stats=result['stats'],
                  summary=summary, certificate_sha256=seeds.digest(proof))
    records.append(record)
    print(record, flush=True)
assert blocking.pins() == before
output = dict(source_sha256=before, controls=records,
              driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
Path(__file__).with_name('cocycle-blocking-large-controls.json').write_text(json.dumps(output, indent=2)+'\n')
