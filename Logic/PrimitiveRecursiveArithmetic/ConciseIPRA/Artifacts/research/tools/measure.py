"""Whole-source metrics, with maximum-compression gzip reported only as FYI."""
from pathlib import Path
import ast
import gzip
import importlib.util
import io
import json
import platform
import sys
import zlib

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'inherited_source_measure', ROOT / 'reference/audit/source_measure.py')
inherited = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inherited)


def compressed_size(data):
    output = io.BytesIO()
    with gzip.GzipFile(fileobj=output, filename='', mode='wb',
                       compresslevel=9, mtime=0) as stream:
        stream.write(data)
    return len(output.getvalue())


def measure(path):
    path = Path(path)
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(inherited.StripDocstrings().visit(
        ast.parse(raw.decode('utf-8'))))
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    result = inherited.metrics(path)
    result.pop('core', None)  # Never use a fragment-only count as the result.
    result['gzip9_raw_bytes'] = compressed_size(raw)
    result['gzip9_normalized_bytes'] = compressed_size(normalized)
    result['file'] = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    return result


def main():
    paths = [Path(p).resolve() for p in sys.argv[1:]] or sorted((ROOT / 'code').glob('*.py'))
    print(json.dumps({'python': platform.python_version(),
                      'zlib': zlib.ZLIB_RUNTIME_VERSION,
                      'gzip': {'compresslevel': 9, 'mtime': 0, 'filename': ''},
                      'programs': [measure(p) for p in paths]}, indent=2))


if __name__ == '__main__':
    main()
