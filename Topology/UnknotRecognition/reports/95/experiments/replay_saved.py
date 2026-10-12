"""Replay every preserved source certificate, with no discovery or oracle."""

import json
from pathlib import Path

from normal_cut_saturation_verify import verify_normal_cut_saturation


ROOT = Path(__file__).resolve().parents[1]


def main():
    files = sorted((ROOT / 'data/certificates').glob('*.json'))
    for path in files:
        item = json.loads(path.read_text())
        assert verify_normal_cut_saturation(item['triangulation'], item['coordinates'],
                                            item['certificate']), path.name
        print(item['id'], item['certificate']['conclusion']['status'])
    print(f'{len(files)} saved certificates independently verified')


if __name__ == '__main__':
    main()
