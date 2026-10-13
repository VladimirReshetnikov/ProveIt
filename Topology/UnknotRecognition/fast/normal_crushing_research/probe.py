"""Retain the first larger diagram search, including incomplete outcomes."""
import json
from pathlib import Path
import sys
import time

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from .benchmark import source_hashes


def main():
    diagram = Diagram.from_braid(2, [1, 1, 1])
    output = dict(source_sha256=source_hashes(), input_pd=diagram.pd,
        scope='bounded trefoil exploration; incomplete results are not knot verdicts or timings for complete recognition',
        passed=False, records=[])
    for order, sectors, bases in (('canonical', 1000, 10000),
                                  ('diversified', 1, 1),
                                  ('diversified', 1000, 10000)):
        start = time.monotonic()
        def check():
            if time.monotonic()-start > 30:
                raise TimeoutError('30-second cooperative exploration ceiling')
        record = dict(sector_order=order, max_sectors=sectors, max_bases=bases,
                      cancellation_seconds=30)
        try:
            result = recognize_by_crushing(diagram, sector_order=order,
                max_sectors=sectors, max_bases=bases, check=check)
        except TimeoutError as exc:
            result = dict(status='CANCELLED', reason=str(exc))
        record.update(result=result, elapsed_seconds=time.monotonic()-start)
        if result['status'] == 'INCONCLUSIVE':
            assert verify_crushing_chain(diagram, result['partial_chain'])
            record['independent_partial_chain_replay'] = True
        output['records'].append(record)
        Path(sys.argv[1]).write_text(json.dumps(output, indent=2)+'\n')
        print(order, sectors, result['status'], result.get('stats'), flush=True)
    assert output['source_sha256'] == source_hashes(), 'probed source changed during the run'
    output['passed'] = True
    Path(sys.argv[1]).write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
