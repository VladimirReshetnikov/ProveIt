"""Finite integration evidence for the standalone checker and proof compilers.

This is not a proof-assistant verification or a proof of consistency.
Run with Python 3.12 or newer from any working directory.
"""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests/support'))
import translate as trans
from packets import encode, decode
from control_translations import fusion_to_control


def run(data, script, optimized):
    proc = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(ROOT/'code'/script)],
                          input=json.dumps(data), text=True, capture_output=True, timeout=60)
    return proc.returncode == 0 and proc.stdout.strip() == 'ACCEPT'


def main():
    result = {'positive_cases': [], 'negative_cases': [], 'source_translations': [], 'failures': []}
    for path in sorted((ROOT/'tests/source_proofs').glob('*.json')):
        data = json.loads(path.read_text())
        trans.reference_old.check(data)
        separate = fusion_to_control(data['proof'])
        assert trans.reference_old.derive(separate, [], 0, True) == data['goal']
        new = trans.control_to_new(separate)
        trans.new_reference.check({'goal': data['goal'], 'proof': new})
        packet = {'goal': data['goal'], 'proof': encode(trans.annotated_to_forward(new))}
        assert packet == json.loads((ROOT/'tests/positive'/path.name).read_text())
        result['source_translations'].append(path.stem)
    for path in sorted((ROOT/'tests/positive').glob('*.json')):
        data = json.loads(path.read_text())
        tagged = decode(data['proof'])
        assert encode(tagged) == data['proof']
        trans.new_forward.check({'goal': data['goal'], 'proof': tagged})
        independently_replayed = trans.forward_to_annotated(tagged)
        trans.new_reference.check({'goal': data['goal'], 'proof': independently_replayed})
        old_tagged = trans.new_forward_to_old(tagged)
        trans.old_forward.check({'goal': data['goal'], 'proof': old_tagged})
        old = {'goal': data['goal'], 'proof': encode(old_tagged, old=True)}
        checks = []
        for script, value in [('checker.py', data), ('control_old.py', old)]:
            for optimized in [False, True]:
                accepted = run(value, script, optimized)
                checks.append({'script': script, 'optimized': optimized, 'accepted': accepted})
                if not accepted:
                    result['failures'].append({'name': path.stem, 'script': script, 'optimized': optimized})
        result['positive_cases'].append({'name': path.stem, 'checks': checks})
    for path in sorted((ROOT/'tests/negative').glob('*.json')):
        data = json.loads(path.read_text())
        accepted = [run(data, 'checker.py', optimized) for optimized in [False, True]]
        if any(accepted):
            result['failures'].append({'name': path.stem, 'accepted': accepted})
        result['negative_cases'].append({'name': path.stem, 'accepted': accepted})
    result['summary'] = {'positive_cases': len(result['positive_cases']),
                         'negative_cases': len(result['negative_cases']),
                         'source_proof_translations': len(result['source_translations']),
                         'standalone_process_checks': 4*len(result['positive_cases']) + 2*len(result['negative_cases']),
                         'failures': len(result['failures'])}
    (ROOT/'evidence').mkdir(exist_ok=True)
    (ROOT/'evidence/verification.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['summary'], indent=2))
    if result['failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
