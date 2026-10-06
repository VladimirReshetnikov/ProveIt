#!/usr/bin/env python3
"""Create a deterministic, stored ZIP at one NEW external file destination."""
import sys
sys.dont_write_bytecode = True
import argparse
from hashlib import sha256
import io
import json
from pathlib import Path
import subprocess
import zipfile
from output_guard import external_output, write_external_bytes

ROOT = Path(__file__).resolve().parent

def archive_bytes(blobs):
    buffer = io.BytesIO()
    # ZIP_STORED deliberately avoids zlib-version dependence.
    with zipfile.ZipFile(buffer, mode='w', compression=zipfile.ZIP_STORED,
                         allowZip64=False) as archive:
        for name in sorted(blobs):
            info = zipfile.ZipInfo('report133/' + name, date_time=(2026, 10, 2, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            info.flag_bits = 0
            info.extra = b''
            info.comment = b''
            archive.writestr(info, blobs[name])
    return buffer.getvalue()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='NEW external ZIP file')
    args = parser.parse_args()
    try:
        destination = external_output(args.output, ROOT)  # Before inventory reads or mathematical work.
        from verify import verify, check_inventory, require
        verify(ROOT)
        before = check_inventory(ROOT)
        data = archive_bytes(before)
        require(check_inventory(ROOT) == before, 'BUNDLE_CHANGED_DURING_PACK')
        write_external_bytes(destination, data, ROOT)
        print(json.dumps({'status': 'PASS', 'members': len(before),
                          'zip_sha256': sha256(data).hexdigest()}, sort_keys=True))
    except (ValueError, OSError, subprocess.SubprocessError, zipfile.BadZipFile) as exc:
        print('PACK_FAIL: ' + str(exc), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
