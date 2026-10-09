"""Verify the retained examples from independent source files."""
import json
from pathlib import Path
from envelope_kernel import Candidate
from grammar import from_data
from checker import check_run, check_reduction
from surface_replay import replay_witness


def main():
    root=Path(__file__).resolve().parents[1]
    g=from_data(json.loads((root/'examples/grammar.json').read_text()))
    answer=json.loads((root/'examples/run_certificate.json').read_text())
    ok,reason=check_run(g,answer)
    if not ok:raise SystemExit('Run certificate not verified: '+reason)
    mesh=replay_witness(g,answer['witness'])
    if not mesh['disk']:raise SystemExit('Recovered surface is not a disk')
    expected=json.loads((root/'examples/surface_replay.json').read_text())
    if mesh!=expected:raise SystemExit('Stored mesh statistics disagree')
    wide=json.loads((root/'examples/wide_reduction.json').read_text())
    items=[Candidate(tuple(c['partition']),int(c['cost_hex'],16),c['sector'],tuple(c['witness']))
           for c in wide['items']]
    ok,reason=check_reduction(items,wide['sigma'],wide['rho'],wide['certificate'])
    if not ok:raise SystemExit('Wide certificate not verified: '+reason)
    print('Full source-bound run certificate verified.')
    print('Recovered abstract disk verified by literal triangulated-surface replay.')
    print('256-arc, cycle-rank-three reduction certificate independently verified.')
    print('No ambient embedding, geometric completeness, or knot verdict is asserted.')

if __name__=='__main__':main()
