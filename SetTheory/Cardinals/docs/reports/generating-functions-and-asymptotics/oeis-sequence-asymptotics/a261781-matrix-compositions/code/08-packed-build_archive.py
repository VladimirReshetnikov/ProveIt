#!/usr/bin/env python3
"""Create a deterministic report-and-code ZIP, refusing existing output paths."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import sys
import zipfile
from release_tools import fresh_file, regular_bytes

ROOT = Path(__file__).absolute().parent
FILES = [
    'README.md', 'build_archive.py', 'build_pdf.py', 'release_tools.py',
    'source/report169.tex', 'report169.pdf', 'sources.json',
    'companion/README.md', 'companion/coefficient_formulas.txt',
    'companion/packed_matrix.py', 'companion/run_companion.py',
    'companion/test_companion.py', 'companion/verify_symbolic.py',
    'companion/provenance.json', 'companion/requirements-optional.txt',
    'companion/frozen/coefficients_C0_C3.json', 'companion/frozen/oeis_A261784.json',
    'companion/examples/coefficients_exact_checks.json',
    'companion/examples/counts_exact.json', 'companion/examples/diagnostics_uncertified.json',
    'companion/examples/manifest.json', 'companion/examples/marked_exact.json',
    'companion/symbolic_checks/manifest.json', 'companion/symbolic_checks/symbolic_checks.json',
    'companion/optional_large_run/manifest.json',
    'companion/optional_large_run/diagnostics_uncertified.json',
]


def archive(destination):
    # Validate/read every source before creating the output; reject symbolic links.
    files = {name: regular_bytes(ROOT / name) for name in sorted(FILES)}
    lines = [hashlib.sha256(content).hexdigest() + '  ' + name
             for name, content in sorted(files.items())]
    files['SHA256SUMS'] = ('\n'.join(lines) + '\n').encode('ascii')
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, 'w', compression=zipfile.ZIP_STORED) as result:
        for name, content in sorted(files.items()):
            info = zipfile.ZipInfo('report169/' + name, date_time=(2026, 10, 3, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            result.writestr(info, content)
    with fresh_file(destination) as stream:
        stream.write(buffer.getvalue())
    print('Created report-and-code ZIP with %d files' % len(files))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        archive(args.output)
    except (OSError, ValueError, RuntimeError, zipfile.BadZipFile) as error:
        print('Archive failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
