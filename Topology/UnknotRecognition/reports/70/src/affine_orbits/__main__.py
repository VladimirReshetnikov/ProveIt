"""JSON command line. Results are orbit data, never a knot verdict."""
from __future__ import annotations
import argparse
import json
import sys
import time
from pathlib import Path
from .core import BulkIndex, Model, SparseOverlay, wire, histogram_records
from .certificate import make_certificate
from .checker import verify


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path, help='JSON containing model and optional defects')
    p.add_argument('--output', type=Path)
    p.add_argument('--verify', type=Path, help='check a certificate against the input')
    p.add_argument('--seconds', type=float, help='cooperative producer deadline')
    p.add_argument('--max-bytes', type=int, default=64 * 1024 * 1024)
    p.add_argument('--max-vertices', type=int, default=1000000)
    a = p.parse_args()
    try:
        if a.input.stat().st_size > a.max_bytes:
            raise ValueError('input exceeds byte limit')
        data = json.loads(a.input.read_text())
        model = Model.parse(data['model'])
        if model.vertices > a.max_vertices:
            raise ValueError('explicit base-vertex limit exceeded')
        defects = data.get('defects', [])
        if a.verify:
            if a.verify.stat().st_size > a.max_bytes:
                raise ValueError('certificate exceeds byte limit')
            cert = json.loads(a.verify.read_text())
            cert = cert.get('certificate', cert)
            verify(model, defects, cert)
            out = {'status': 'verified-orbit-certificate', 'knot_verdict': None}
        else:
            deadline = None if a.seconds is None else time.monotonic() + a.seconds
            def check() -> None:
                if deadline is not None and time.monotonic() >= deadline:
                    raise TimeoutError('cooperative deadline exceeded')
            index = BulkIndex(model, check=check)
            overlay = SparseOverlay(index)
            for d in defects:
                overlay.add(d)
            cert = make_certificate(index, overlay)
            check()
            # Separate checker is deliberately included in a completed CLI result.
            verify(model, defects, cert)
            check()
            out = dict(status='verified-orbit-profile', knot_verdict=None,
                       histogram=histogram_records(overlay.histogram),
                       component_count=overlay.component_count, certificate=cert)
        text = json.dumps(wire(out), indent=2, sort_keys=True) + '\n'
        if a.output:
            a.output.write_text(text)
        else:
            sys.stdout.write(text)
        return 0
    except (ValueError, KeyError, TypeError, OSError, TimeoutError, ArithmeticError) as e:
        print(json.dumps({'status': 'error-or-inconclusive', 'error': str(e),
                          'knot_verdict': None}), file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
