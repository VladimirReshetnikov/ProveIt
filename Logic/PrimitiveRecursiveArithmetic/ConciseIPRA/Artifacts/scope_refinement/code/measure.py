"""Measure complete modules using the pinned ConciseIPRA convention."""
import argparse
import json
from pathlib import Path
import platform
from census import measure


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='+', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = {'python': platform.python_version(), 'files': []}
    for path in args.files:
        result['files'].append({'path': str(path), **measure(path.read_bytes())})
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
