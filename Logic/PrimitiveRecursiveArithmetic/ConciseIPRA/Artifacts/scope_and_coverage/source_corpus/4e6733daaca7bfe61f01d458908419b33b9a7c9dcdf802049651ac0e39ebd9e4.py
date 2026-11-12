"""Independent named producer and full-process validation of selected profiles."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(path, packet, optimized=False, raw=False):
    result = subprocess.run([sys.executable]+(['-O'] if optimized else [])+[str(path)],
                            input=packet if raw else json.dumps(packet),
                            text=True, capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n', result.returncode


def main():
    spec = importlib.util.spec_from_file_location('named_producer', ROOT/'reference/named_producer.py')
    producer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(producer)
    old = producer.Emitter
    class LocalEmitter(old):
        def emit(self, proof, context):
            previous = self.floor
            self.floor = -len(context)
            try:
                return super().emit(proof, context)
            finally:
                self.floor = previous
    producer.Emitter = LocalEmitter
    cases = producer.build_cases()
    frozen = json.loads((ROOT/'evidence/local_composition_cases.json').read_text())
    if json.loads(json.dumps(cases)) != frozen:
        raise AssertionError('Named producer differs from frozen lexical certificates')
    profiles = ['local_argument.py','local_argument_bytes.py',
                'local_loop_joint.py','local_loop_joint_separate.py']
    rows = []
    for profile in profiles:
        for case in cases:
            for optimized in (False, True):
                accepted, status = run(ROOT/'code'/profile, case['packet'], optimized)
                rows.append({'profile': profile, 'case':case['name'], 'optimized':optimized,
                             'expected':case['accept'], 'accepted':accepted,
                             'ok':accepted==case['accept'], 'exit':status})
    malformed = ['', '{}', 'null', 'true', '42', '"x"', '["x"]', '[[]]',
                 '[[0,[0]]]', '[[true,0,0,0],[0,[0]]]']
    # Empty-array goal [ [] ] is truth, but has no proof command; it must
    # reject as a certificate. Other cases are malformed or claim falsity.
    for profile in profiles:
        for index, packet in enumerate(malformed):
            for optimized in (False, True):
                accepted, status = run(ROOT/'code'/profile, packet, optimized, raw=True)
                rows.append({'profile':profile, 'case':'malformed_'+str(index),
                             'optimized':optimized,'expected':False,'accepted':accepted,
                             'ok':not accepted,'exit':status})
    false_proof = json.loads((ROOT/'tests/failed_opaque/false_float_capture.json').read_text())
    for profile in profiles:
        accepted, status = run(ROOT/'code'/profile, false_proof)
        rows.append({'profile':profile,'case':'opaque_float_false_proof','expected':False,
                     'accepted':accepted,'ok':not accepted,'exit':status})
    bad, bad_status = run(ROOT/'tests/failed_opaque/UNSOUND_experiment.py', false_proof)
    if not bad:
        raise AssertionError('The deliberately unsound control did not reproduce the counterexample')
    result = {'status':'passed' if all(row['ok'] for row in rows) else 'FAILED',
              'total':len(rows),'accepted':sum(row['accepted'] for row in rows),
              'rejected':sum(not row['accepted'] for row in rows),
              'counterexample_control':{'unsound_prototype_accepts_false':bad,'exit':bad_status},
              'rows':rows, 'scope':'Finite tests; mathematical metatheory is written, not proof-assistant verified.'}
    (ROOT/'evidence/kernel_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    examples=ROOT/'tests/examples'; examples.mkdir(exist_ok=True)
    for case in cases:
        name=''.join(c if c.isalnum() or c in '_-' else '_' for c in case['name'])
        (examples/(name+'.json')).write_text(json.dumps(case['packet'],indent=2)+'\n')
    print(json.dumps({key:val for key,val in result.items() if key!='rows'},indent=2))
    if result['status'] != 'passed':
        raise AssertionError([r for r in rows if not r['ok']])


if __name__=='__main__':
    main()
