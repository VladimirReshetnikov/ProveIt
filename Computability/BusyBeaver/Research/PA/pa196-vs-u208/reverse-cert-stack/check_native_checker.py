#!/usr/bin/env python3
"""Check the direct Nat checker against pinned upstream rule expressions.

Requires Lean 4.32.0; all .olean files are built in a private temp directory.
The Foundation model-valued checker and the direct Nat recurrence have not yet
been proved equal; neither an iPRA nor a literal-machine theorem is asserted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
UPSTREAM = HERE.parents[1] / 'jamesyc-upstream/pa196'
PINS = {
    'M6/Source/Cantor.lean': '490ba3fa497a633fe12ff76803a865f7b0ba192707d2dec44b2f92455df5655f',
    'PA196/Commands/Code.lean': '261d6536ae909f8c83fe792ed7640b465021698bc792bad1049de25bccc5410b',
    'PA196/Commands/Store.lean': 'eb29647751302d4449302254842942792e115f834ffecdf51023c30ed00615e3',
    'M6PA/Scheduler/ActualArithmeticGraph.lean': '1df240f2689bf23a26e1c3c54d761120e213ea8aa3fbe8e54184e5abcfcc7ea6',
    'PA196/Arithmetic/HeadGraphs.lean': '95998688eb29f0cdc900f194e220637b0b645351c3cbc1972532533a355aacbd',
    'PA196/Arithmetic/Scalar.lean': '310114fb36f3efaeba8c59bd2b869452b2691a5736a697ecf65a417258643b67',
    'PA196/Arithmetic/CheckerRule.lean': 'ec870e1bc5456af958e4638c60116bc07d7f69638ee3e9c3195aadb63d31fcf1',
    'PA196/Arithmetic/CheckerRows.lean': 'cf46506a40263feeacb5ce2028e3ad48e9a6fe75aed8aa4c3dca4a455e44c929',
    'PA196/Arithmetic/Checker.lean': '7313a9be8557d2aa5b89421f3ce9e3ac01ce4155ea57f775536d10eb382fecbc',
}
FRAGMENTS = {
    'M6PA/Scheduler/ActualArithmeticGraph.lean': ('inductive Expr where', 'noncomputable def graph :'),
    'PA196/Arithmetic/HeadGraphs.lean': ('def im (x y : Expr)', 'theorem implication_exact'),
    'PA196/Arithmetic/Scalar.lean': ('inductive Expr where', 'noncomputable def graph :'),
    'PA196/Arithmetic/CheckerRule.lean': ('def zero : Scalar.Expr', 'noncomputable def ruleGraph'),
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    for rel, digest in PINS.items():
        need(sha(UPSTREAM / rel) == digest, 'upstream source hash mismatch: ' + rel)
    syntax = (HERE / 'CheckerRuleSyntax.lean').read_text()
    for rel, (start, end) in FRAGMENTS.items():
        source = (UPSTREAM / rel).read_text()
        need(source.count(start) == 1 and source.count(end) == 1, 'fragment markers differ: ' + rel)
        fragment = source[source.index(start):source.index(end)].rstrip() + '\n'
        need(syntax.count(fragment) == 1, 'extracted fragment differs: ' + rel)
        if rel.endswith('CheckerRule.lean'):
            need(fragment.count('.previous') == 2 and fragment.count('.nth .previous') == 2,
                 'prior table is used outside the two nth operations')
    version = subprocess.run(['lean', '--version'], check=True, text=True,
                             capture_output=True).stdout.strip()
    need(version.startswith('Lean (version 4.32.0,'), 'requires Lean 4.32.0: ' + version)
    with tempfile.TemporaryDirectory(prefix='pa196-native-checker-') as directory:
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
        check(HERE / 'CertificateStack.lean', 'CertificateStack.olean')
        check(HERE / 'UpstreamCommandAudit.lean', 'UpstreamCommandAudit.olean')
        checker_log = check(HERE / 'NativeChecker.lean', 'NativeChecker.olean')
        check(HERE / 'CheckerRuleSyntax.lean', 'CheckerRuleSyntax.olean')
        rule_log = check(HERE / 'CheckerRuleAudit.lean')
        binding_log = check(HERE / 'NativeCheckerBinding.lean')
        required = {
            'PA196CertificateStack.NativeChecker.checker_interfaces': checker_log,
            'PA196CertificateStack.NativeChecker.entry_eq_listTable': checker_log,
            'PA196CertificateStack.NativeChecker.rule_matches_extracted_source': rule_log,
            'PA196CertificateStack.NativeChecker.upstream_command_halt_yields_numeric_certificate': binding_log,
        }
        for theorem, log in required.items():
            normalized = re.sub(r'\s+', ' ', log)
            expected = f"'{theorem}' depends on axioms: [propext, Quot.sound]"
            need(expected in normalized, 'unexpected theorem dependencies: ' + theorem)
            need('sorryAx' not in log and 'Classical.choice' not in log,
                 'unchecked or classical dependency in Lean output')
    files = ['NativeChecker.lean', 'CheckerRuleSyntax.lean', 'CheckerRuleAudit.lean',
             'NativeCheckerBinding.lean', 'CertificateStack.lean', 'UpstreamCommandAudit.lean']
    receipt = {'lean_version': '4.32.0', 'pinned_upstream_sha256': PINS,
               'local_sources_sha256': {name: sha(HERE / name) for name in files},
               'source_fragments_match_byte_for_byte': sorted(FRAGMENTS),
               'prior_table_used_only_by_two_nth_nodes': True,
               'kernel_checked_theorems': sorted(required),
               'axioms': ['propext', 'Quot.sound'],
               'scope': 'Nat checker and extracted source rule; Foundation-model checker equality, iPRA and literal-TM bindings remain open.'}
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
