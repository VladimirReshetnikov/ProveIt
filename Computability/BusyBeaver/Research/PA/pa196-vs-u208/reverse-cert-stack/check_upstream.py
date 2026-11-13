#!/usr/bin/env python3
"""Kernel-check the standalone extractor against pinned PA196 command sources.

Requires Lean 4.32.0. All .olean outputs are in a private temporary directory.
The checked theorem remains conditional on the native checker interfaces and
is not a proof of an iPRA or literal machine theorem.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parents[1] / 'jamesyc-upstream/pa196'
PINS = {
    'M6/Source/Cantor.lean': '490ba3fa497a633fe12ff76803a865f7b0ba192707d2dec44b2f92455df5655f',
    'PA196/Commands/Code.lean': '261d6536ae909f8c83fe792ed7640b465021698bc792bad1049de25bccc5410b',
    'PA196/Commands/Store.lean': 'eb29647751302d4449302254842942792e115f834ffecdf51023c30ed00615e3',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for rel, expected in PINS.items():
        need(sha(UPSTREAM / rel) == expected, 'upstream source hash mismatch: ' + rel)
    version = subprocess.run(['lean', '--version'], check=True, text=True,
                             capture_output=True).stdout.strip()
    need(version.startswith('Lean (version 4.32.0,'), 'requires Lean 4.32.0: ' + version)
    with tempfile.TemporaryDirectory(prefix='pa196-command-audit-') as directory:
        temp = Path(directory)
        (temp / 'M6/Source').mkdir(parents=True)
        (temp / 'PA196/Commands').mkdir(parents=True)
        env = os.environ.copy()
        env['LEAN_PATH'] = str(temp)
        def check(source, output=None):
            command = ['lean']
            if output is not None:
                command += ['-o', str(temp / output)]
            command += [str(source)]
            return subprocess.run(command, check=True, text=True, capture_output=True,
                                  env=env).stdout
        check(UPSTREAM / 'M6/Source/Cantor.lean', 'M6/Source/Cantor.olean')
        check(UPSTREAM / 'PA196/Commands/Code.lean', 'PA196/Commands/Code.olean')
        check(UPSTREAM / 'PA196/Commands/Store.lean', 'PA196/Commands/Store.olean')
        stack_log = check(HERE / 'CertificateStack.lean', 'CertificateStack.olean')
        audit_log = check(HERE / 'UpstreamCommandAudit.lean')
        required = {
            'PA196CertificateStack.Native.native_halt_extractor': stack_log,
            'PA196UpstreamCommandAudit.upstream_halt_has_checker_certificate': audit_log,
            'PA196UpstreamCommandAudit.old_order_wrong': audit_log,
        }
        for theorem, log in required.items():
            expected = f"'{theorem}' depends on axioms: [propext, Quot.sound]"
            need(expected in log, 'unexpected theorem assumptions: ' + theorem)
            need('sorryAx' not in log, 'unchecked proof in Lean output')
    receipt = {
        'lean_version': '4.32.0',
        'pinned_upstream_sha256': PINS,
        'certificate_stack_sha256': sha(HERE / 'CertificateStack.lean'),
        'upstream_audit_sha256': sha(HERE / 'UpstreamCommandAudit.lean'),
        'kernel_checked_theorems': sorted(required),
        'axioms': ['propext', 'Quot.sound'],
        'upstream_head4_counterexample': {'D': 1, 'H': 0, 'A': 0,
                                           'correct': 144136, 'old_order': 119544},
        'scope': 'Conditional standard-natural command theorem; not iPRA, checker instantiation, or tape binding.',
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
