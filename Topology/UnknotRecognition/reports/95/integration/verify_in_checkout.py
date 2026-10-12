"""Verify the added namespaced modules in a checkout after applying the patch.

Usage: python3 -B integration/verify_in_checkout.py /path/to/repo/Topology/UnknotRecognition/fast
Only the supplied checkout is imported; the bundled runtime is not put on sys.path.
"""

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    fast = Path(sys.argv[1]).resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.normal_cut_saturation import normal_cut_saturation
    from fastunknot.normal_cut_saturation_verify import verify_normal_cut_saturation
    proofs = sorted((ROOT / 'data/certificates').glob('*.json'))
    for path in proofs:
        item = json.loads(path.read_text())
        assert verify_normal_cut_saturation(item['triangulation'], item['coordinates'],
                                            item['certificate']), path.name
    cases = json.loads((ROOT / 'data/native_corpus.json').read_text())['cases']
    for index, precheck in ((0, False), (4, False), (3, True)):
        case = cases[index]
        answer = normal_cut_saturation(case['triangulation'], case['coordinates'],
                                       record_certificate=True, precheck_core=precheck)
        assert verify_normal_cut_saturation(case['triangulation'], case['coordinates'],
                                            answer['certificate'])
    print(json.dumps(dict(saved_proofs=len(proofs), fresh_queries=3, status='PASS',
                          imported_checkout=str(fast)), indent=2))


if __name__ == '__main__':
    main()
