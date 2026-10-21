"""Reproduce all producer modes from frozen text inputs; does not invoke Lean."""
import argparse, json, subprocess, sys, time
from pathlib import Path
from review_saved import load, review, sha

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    p.add_argument('--out', type=Path, required=True, help='New output directory')
    args = p.parse_args()
    review(args.packet)
    summary, files, paths = load(args.packet)
    old = json.loads(files['generation/reproduction2/result.json'])
    args.out.mkdir(parents=True, exist_ok=False)
    # Recreate the repository-relative layout used by default template lookup.
    formal = args.out / 'workspace/Computability/BusyBeaver/Research/ZFC/k225-formal'
    template = args.out / 'workspace/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/149-dom-theory-ev-CD230.v'
    formal.mkdir(parents=True)
    template.parent.mkdir(parents=True)
    (formal / 'rho8plan').mkdir()
    destinations = {}
    for oldpath in old['inputs_before']:
        basename = Path(oldpath).name
        if basename == 'generate_domrho8_lean.py':
            dest = formal / basename
        elif basename == '149-dom-theory-ev-CD230.v':
            dest = template
        elif basename in ('plan.json', 'replay.py'):
            dest = formal / 'rho8plan' / basename
        else:
            dest = args.out / basename
        dest.write_bytes(files[paths[oldpath]])
        destinations[oldpath] = dest.resolve()
    before = {str(q): sha(q.read_bytes()) for q in destinations.values()}
    cases = []
    for original in old['cases']:
        name = original['name']
        output = (args.out / (name + '.lean')).resolve()
        command = [sys.executable, '-B'] + [str(destinations.get(a, a)) for a in original['command'][2:]]
        command[4] = str(output)
        started = time.monotonic()
        result = subprocess.run(command, capture_output=True, timeout=30)
        (args.out / (name + '.stdout')).write_bytes(result.stdout)
        (args.out / (name + '.stderr')).write_bytes(result.stderr)
        row = {'name': name, 'command': command, 'exit_code': result.returncode,
               'seconds': time.monotonic() - started}
        if 'expected' in original:
            row['output_sha256'] = sha(output.read_bytes()) if output.exists() else None
            assert result.returncode == 0 and row['output_sha256'] == original['expected'], row
        else:
            row['output_absent'] = not output.exists()
            assert result.returncode != 0 and row['output_absent'], row
        cases.append(row)
    after = {str(q): sha(q.read_bytes()) for q in destinations.values()}
    assert before == after
    assert (args.out / 'default.lean').read_bytes() + files['candidate/APIAudit.lean.inc'] == files['kernel/SharedWithAudit.lean']
    record = {'status': 'PASS_RENDERER_ONLY', 'source_sha256': summary['source_sha256'],
              'producer_sha256': summary['producer_sha256'], 'inputs_before': before,
              'inputs_after': after, 'cases': cases, 'kernel_invoked': False,
              'generated_plus_clients_matches_saved_kernel_source': True}
    (args.out / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'result': str(args.out / 'result.json')}, indent=2))

if __name__ == '__main__':
    main()
