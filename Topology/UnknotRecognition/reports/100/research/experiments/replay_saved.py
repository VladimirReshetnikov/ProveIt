"""Independently replay every archived native census packet."""

from pathlib import Path
import argparse
import json

from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    count = 0
    for path in sorted(args.directory.glob('*.json')):
        packet = json.loads(path.read_text())
        source, result = packet['case'], packet['result']
        if result['status'] != 'COMPLETE':
            raise AssertionError(f'Nonpositive packet: {path.name}')
        if not verify_normal_cut_handlebodies(source['triangulation'],
                source['coordinates'], result['certificate']):
            raise AssertionError(f'Replay failed: {path.name}')
        count += 1
    if not count:
        raise AssertionError('No saved packets found')
    print(f'Independently replayed {count} saved source census certificates.')


if __name__ == '__main__':
    main()
