#!/usr/bin/env python3
"""Audit the historical random-area record; optionally make a separate new draw.

Default mode performs no RNG call. A new draw requires --draw --output NEW_PATH
and exclusive file creation, so an existing record cannot be overwritten.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import secrets

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--draw', action='store_true', help='make a separate new draw')
    parser.add_argument('--output', type=Path, help='new nonexisting output path')
    args = parser.parse_args()
    try:
        original = json.loads((ROOT / 'data/selection.json').read_text(encoding='utf-8'))
        areas = original['ordered_areas']
        digest = hashlib.sha256('\n'.join(areas).encode('utf-8')).hexdigest()
        index = original['zero_based_index']
        if not (len(areas) == original['count'] == 120 and digest == original['list_sha256']
                and 0 <= index < len(areas) and original['one_based_index'] == index + 1
                and areas[index] == original['area']):
            raise ValueError('Historical selection record is inconsistent')
        if args.draw:
            if args.output is None:
                parser.error('--draw requires --output NEW_PATH')
            # Reserve the destination before drawing; never replace an existing record.
            with args.output.open('x', encoding='utf-8') as stream:
                index = secrets.randbelow(len(areas))
                new = dict(original)
                new.update(zero_based_index=index, one_based_index=index+1, area=areas[index],
                           method='Python secrets.randbelow; separate new draw, not the historical selection')
                stream.write(json.dumps(new, indent=2) + '\n')
            print(json.dumps({'new_record': str(args.output), 'area': areas[index],
                              'one_based_index': index+1}, indent=2))
        else:
            if args.output is not None:
                parser.error('--output is only used together with --draw')
            print(json.dumps({'status': 'PASS', 'rng_called': False, 'count': len(areas),
                              'one_based_index': original['one_based_index'],
                              'area': original['area'], 'list_sha256': digest}, indent=2))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, f'SELECTION CHECK FAILED: {error}\n')


if __name__ == '__main__':
    main()
