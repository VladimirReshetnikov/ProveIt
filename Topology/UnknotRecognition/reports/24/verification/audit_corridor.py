"""Independent degreewise equality audit against the inherited full transfer."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FAST = next(path for path in (ROOT/'fast', ROOT/'implementation/fast', ROOT/'work/fast')
            if (path/'fastunknot/corridor.py').is_file())
sys.path.insert(0, str(FAST))
from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.graded import GradedScan
from fastunknot.corridor import corridor_transfer, CorridorScan
from fastunknot.ordering import best_scan_order

REFERENCE = next(path for path in (ROOT/'reference/graded_transfer_v1.py',
                                  ROOT/'work/reference/graded_transfer_v1.py')
                 if path.is_file())
spec = importlib.util.spec_from_file_location('inherited_transfer_audit', REFERENCE)
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)


def key(result):
    return tuple(result[k] for k in ('mid', 'deg', 'q', 'out'))


def scalar_key(scalar):
    result = {name: scalar[name] for name in ('mid', 'deg', 'q')}
    for name in ('i', 'p', 'h'):
        result[name] = [col if isinstance(col, int) else sum(1 << a for a in col)
                        for col in scalar[name]]
    return result


def main():
    rng = random.Random(202610081827)
    started = time.monotonic()
    diagrams = stages = comparisons = certificates = partials = 0
    nonzero_minimal = forward_components = reverse_components = 0
    while diagrams < 80:
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 13))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        order = best_scan_order(diagram.pd)
        if diagrams % 2:
            rng.shuffle(order)
        scan = GradedScan(shape_cache=False, max_objects=20000)
        changed = CorridorScan(shape_cache=False, max_objects=20000,
                               scalar_engine='components', direction_policy='ports')
        for crossing in order:
            scan.add_crossing(diagram.pd[crossing], reduce_now=False)
            scan.check_grading()
            if diagrams % 3 == 0:
                scan.eliminate(update_budget=rng.randrange(0, 5))
                partials += 1
            old = reference.transfer(scan, certificates=True)
            reference.check_certificate(scan, old)
            certificates += 1
            nonzero_minimal += bool(any(old['out']))
            configurations = [dict(mode=mode, prune=prune) for mode, prune in
                              [('forward', True), ('reverse', True),
                               ('auto', True), ('forward', False)]]
            configurations += [dict(mode=mode, prune=True, scalar_engine='components',
                                    direction_policy='ports')
                               for mode in ('forward', 'reverse', 'auto')]
            for configuration in configurations:
                new = corridor_transfer(scan, **configuration)
                assert key(new) == key(old), (word, order, crossing, configuration)
                assert scalar_key(new['scalar']) == scalar_key(old['scalar'])
                assert new['stats']['propagations'] <= new['stats']['chosen_bound']
                comparisons += 1
                if configuration['mode'] == 'auto':
                    forward_components += new['stats']['forward_components']
                    reverse_components += new['stats']['reverse_components']
            scan.eliminate()
            changed.add_crossing(diagram.pd[crossing])
            changed.check_grading()
            changed.check_d_squared()
            stages += 1
        assert scan.ranks_by_bidegree() == changed.ranks_by_bidegree(), (word, order)
        diagrams += 1
    result = dict(status='passed', seed=202610081827, diagrams=diagrams, stages=stages,
                  comparisons=comparisons, complete_special_contractions=certificates,
                  partial_sparse_stages=partials, nonzero_minimal_stages=nonzero_minimal,
                  automatic_forward_components=forward_components,
                  automatic_reverse_components=reverse_components,
                  reference_sha256=hashlib.sha256(REFERENCE.read_bytes()).hexdigest(),
                  corridor_sha256=hashlib.sha256(
                      (FAST/'fastunknot/corridor.py').read_bytes()).hexdigest(),
                  dependency_sha256={name: hashlib.sha256(
                      (FAST/'fastunknot'/name).read_bytes()).hexdigest()
                      for name in ('binary_contraction.py', 'scalar_components.py',
                                   'graded.py', 'scan_fast.py')},
                  seconds=time.monotonic()-started)
    Path(__file__).with_name('corridor_independent_audit.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
