import json
from pathlib import Path
from envelope_kernel import Candidate, Envelope, reduce_family
from checker import check_reduction, check_run
from fixtures import restricted_grammar, wide_envelope
from grammar import solve, to_data
from surface_replay import replay_witness

root=Path(__file__).resolve().parents[1]
g=restricted_grammar(5,2,3)
a=solve(g)
assert check_run(g,a)[0]
mesh=replay_witness(g,a['witness'])
assert mesh['disk']
(root/'examples/grammar.json').write_text(json.dumps(to_data(g),indent=2)+'\n')
(root/'examples/run_certificate.json').write_text(json.dumps(a,indent=2)+'\n')
(root/'examples/surface_replay.json').write_text(json.dumps(mesh,indent=2)+'\n')
e=Envelope(*wide_envelope(256,3))
items=[Candidate(e.coordinate_partition(mask),mask-5,0,(mask,)) for mask in range(8)]
red=reduce_family(items,e)
assert check_reduction(items,e.sigma,e.rho,red.certificate)[0]
payload={'sigma':e.sigma,'rho':e.rho,'items':[{'partition':c.partition,'cost_hex':hex(c.cost),'sector':c.sector,'witness':c.witness} for c in items], 'certificate':red.certificate}
(root/'examples/wide_reduction.json').write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'grammar_status':a['status'],'cost_hex':a['cost_hex'],'mesh':mesh,
                  'wide':{'arcs':e.r,'cycle_rank':e.lam,'retained':len(red.retained)}},indent=2))
