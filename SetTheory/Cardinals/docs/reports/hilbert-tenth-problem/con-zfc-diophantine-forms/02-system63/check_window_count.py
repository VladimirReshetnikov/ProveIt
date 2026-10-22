#!/usr/bin/env python3
"""Reproduce the small exhaustive controls for the exact window-count formula."""
import json
from pathlib import Path
from normalized_k215 import count_allowed_windows, verify_count_fixtures


def main():
    actual = count_allowed_windows()
    fixtures = verify_count_fixtures()
    recorded = json.loads(Path(__file__).with_name('window_count_checks.json').read_text())
    if fixtures != recorded:
        raise ValueError('Small exhaustive cross-count controls changed.')
    if actual['allowed_windows'] != 20522746353535702537070419760:
        raise ValueError('Actual K215 window-count formula changed.')
    print(json.dumps({'status':'PASS', 'actual_window_count':actual,
                      'small_exhaustive_fixtures':fixtures,
                      'actual_K215_window_list_enumerated':False}, indent=2))


if __name__ == '__main__':
    main()
