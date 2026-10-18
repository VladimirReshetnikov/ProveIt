#!/usr/bin/env python3
"""Replay source67's eight reviewed substantive checks on a new external copy.

No manifest checks, solver calls, discovery searches or proof compilers. The
large incoming-action partition is coverage-only; the three-row synthesis
certificate also replays each recorded affine rejection, not semantic TM
failure. Both families retain their original proof-search bounds.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must be enabled; do not use -O or -OO.')
    source = args.package.resolve()
    output = args.output.resolve()
    if output.exists() or output == source or source in output.parents:
        ap.error('--output must be a new directory outside the source package')
    output.mkdir(parents=True)
    package = output / 'package'
    shutil.copytree(source, package)
    ledger = package / 'research/agent_state/incoming_extended_compensating_search.json'
    ledger.write_bytes(gzip.decompress(Path(str(ledger) + '.gz').read_bytes()))
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['ZFC246_SOURCE'] = str(package / 'research/sources/context246/zfc-context246')
    env.pop('ZFC246_TABLE', None)
    jobs = [
        ('201-node source bisimulation', ['research/agent_logic/verify_reassociation.py']),
        ('alternate246 complete certificate', ['research/agent_logic/verify_rotated246.py']),
        ('incoming-action partition coverage only', ['research/agent_state/check_compensating_partition.py']),
        ('dirty-root abstract post-fixpoint', ['research/agent_logic/abstract_cfg.py', '--K', '8']),
        ('propositional axiom-specialization countermodel', ['research/agent_logic/specialized_axiom_countermodel.py']),
        ('opaque-macro graph and tape counterexample', ['research/agent_state/check_oracle_counterexample.py']),
        ('bad245 first-complete-frame counterexample', ['research/root_search/literal_rebracket_counterexample.py']),
        ('three-row partition and all affine rejection leaves', ['research/agent_state/rebracket/check_synthesis201_certificate.py', '--replay']),
    ]
    records = []
    result = dict(
        status='RUNNING', source=67, source_package=str(source),
        working_package=str(package), checksum_manifests_checked=False,
        line_endings_checked=False, compiler_invoked=False,
        new_search_run=False, reference_full_suite_replayed=False,
        incoming_partition_rejection_premises_replayed=False,
        three_row_affine_rejections_replay_planned=True,
        three_row_affine_rejections_replayed=False,
        decompressed_ledger_sha256=sha(ledger),
        input_scripts=[dict(path=job[0], sha256=sha(package / job[0])) for _, job in jobs],
        commands=records,
    )
    record_path = output / 'replay.json'

    def save():
        record_path.write_text(json.dumps(result, indent=2) + '\n')

    save()
    for index, (label, job) in enumerate(jobs, 1):
        command = [sys.executable, '-B', *job]
        print(f'[{index}/{len(jobs)}] {label}', flush=True)
        began = time.monotonic()
        try:
            process = subprocess.run(command, cwd=package, env=env, text=True,
                                     capture_output=True, timeout=120)
            stdout, stderr, code = process.stdout, process.stderr, process.returncode
        except subprocess.TimeoutExpired as error:
            stdout, stderr, code = error.stdout or '', error.stderr or '', 124
            if isinstance(stdout, bytes):
                stdout = stdout.decode(errors='replace')
            if isinstance(stderr, bytes):
                stderr = stderr.decode(errors='replace')
        out = output / f'{index:02d}.stdout.txt'
        err = output / f'{index:02d}.stderr.txt'
        out.write_text(stdout)
        err.write_text(stderr)
        records.append(dict(label=label, command=command, cwd=str(package),
                            timeout_seconds=120, returncode=code,
                            seconds=time.monotonic() - began,
                            stdout=str(out), stderr=str(err),
                            stdout_sha256=sha(out), stderr_sha256=sha(err)))
        result['status'] = 'FAIL' if code else 'RUNNING'
        save()
        if code:
            raise SystemExit(code)
    try:
        machine = package / 'machines/zfc_rotated246.tm'
        regenerated = package / 'research/agent_logic/rotated246/zfc_rotated246.tm'
        assert machine.read_bytes() == regenerated.read_bytes()
        assert sha(machine) == '15254535ae4bed3755944a3d11666df60b8e3b36c3b101ef8869ece28db38cc2'
        certificate = json.loads((package / 'research/agent_logic/rotated246/verification.json').read_text())
        assert certificate['status'] == 'PASS' and certificate['working_states'] == 246
        assert certificate['source']['decoder_nodes'] == 202
        assert certificate['instructions']['guarded_cases'] == 8391
        assert certificate['instructions']['minimum_literal_steps'] == 13
        partition = json.loads((package / 'research/agent_state/incoming_partition_audit.json').read_text())
        assert partition['status'] == 'PASS' and partition['covered_complete_assignments'] == 42486984
        replay = json.loads((package / 'research/agent_state/rebracket/synthesis201_partition_audit.json').read_text())
        assert replay['status'] == 'PASS' and replay['covered'] == 952763904
        assert replay['affine_rejections_replayed'] == 19661
    except Exception as error:
        result['status'] = 'FAIL'
        result['postcheck_error'] = repr(error)
        save()
        raise
    result.update(status='PASS', canonical_machine_sha256=sha(machine),
                  three_row_affine_rejections_replayed=True,
                  regenerated_primary_bytes_equal=True,
                  scope='Source DAG equivalence and alternate246 executable certificate; no complete sub246 machine or new Lean/PA endpoint. Incoming-action partition is coverage-only; three-row rejection replay is bounded affine-proof-system rejection, not a general TM lower bound.')
    save()
    print('PASS', len(records), 'reviewed jobs', flush=True)


if __name__ == '__main__':
    main()
