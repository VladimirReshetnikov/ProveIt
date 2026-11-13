#!/usr/bin/env python3
"""Point-in-time evidence inspection; no Lean replay or ancestry audit."""
from hashlib import sha256
from pathlib import Path
import json
import os

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
EXP = BASE / 'research/ordinary12-ipra-bridge'
STD = EXP / 'positive-model-ipra-standard-adapter-prototype'
NATIVE = EXP / 'positive-model-ipra-adapter-prototype'
LEAN = BASE / 'Lean/DiophantineConsistency'
SNAPSHOT = Path('/tmp/positive-model-ipra-standard-adapter-author-jf_d4eoc')
PINS = {
    STD/'PositiveModelIPRAStandardAdapter.lean': '7046c2d8fde9411d517641829e3158733bfec14e778fdce6cb7d86cc9f3ccb78',
    STD/'run.py': '9b586a0f5bb7bc5d55d57d7de1a39dcfd8ef7c74f7deb59456b0fd2d73ee86e7',
    STD/'observations/attempt01/terminal.json': '8f1f5cd6bb92885dbab9bb9d8eb29fa350be78da3a848abedcd95e212b38720e',
    STD/'observations/attempt01/compile.log': 'ae0d009dc87c65dd21028b34e4422970def8b12aa92f6ac8ae7102bcd7847b37',
    NATIVE/'PositiveModelIPRAAdapter.lean': '4faabe0a42f1adabe102e58c4355ddbdf03f9c0ccb29498c48c99241066356ea',
    NATIVE/'observations/attempt03/terminal.json': '9b401cd44c874ad80fe2d4415195b7e2adb228f0f2a291af7afdb66bbbf1944b',
    LEAN/'IPRAStandardTheory.lean': 'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
    LEAN/'IPRAReferenceInductionConversion.lean': 'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9',
    LEAN/'IPRAOrderErasure.lean': 'd14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6',
    LEAN/'IPRAEqualityOnlyReference.lean': 'b398a7930de5c96d92c5d2a29b1c627c4e5f96bb8394b55e20a39948968a078f',
    LEAN/'IPRABoundedRhoZFC.lean': '11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c',
    LEAN/'IPRAFoundationZFCMappedNegation.lean': '9186acc49f486e0fbed0aa52ada450e253f028e64b18c5ee637e926edd4ad95c',
    LEAN/'FoundationZFCConsistencyNat.lean': 'c9e90e5861848ece065a410ad2b0012617e481b9d4fbfccd37436b2ebf40b613',
    LEAN/'FoundationHAConsistencyNormalization.lean': '1a69a875738db6ebbd7c5e466022d0d169ee747e50184fc838077d42f0ad8e09',
    LEAN/'IPRAExpressionNative.lean': 'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
    LEAN/'AdaptiveEquationSyntax2011.lean': 'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
    SNAPSHOT/'PositiveModelIPRAStandardAdapter.lean': '7046c2d8fde9411d517641829e3158733bfec14e778fdce6cb7d86cc9f3ccb78',
    SNAPSHOT/'PositiveModelIPRAStandardAdapter.olean': '1fb7efa7fe6adce191c37dd9fc457ca4af4dd02210b3a19e6ae110d46fea9ce5',
    Path('/tmp/positive-model-ipra-adapter-author-gzcg51tr/PositiveModelIPRAAdapter.olean'): '8955395f621d3b4445bbe56ad3660be21b4f2d3b15f15cb384340a163cd81c12',
}

def sha(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    if not path.is_file():
        raise RuntimeError(f'dangling path: {path}')
    return {'sha256': sha(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

for path, pin in PINS.items():
    if sha(path) != pin:
        raise RuntimeError(f'pin mismatch: {path}')
receipt = json.loads((STD/'observations/attempt01/terminal.json').read_text())
native = json.loads((NATIVE/'observations/attempt03/terminal.json').read_text())
log = (STD/'observations/attempt01/compile.log').read_text()
guards = receipt['guards_before']
guard_check = all(record(p) == r for p, r in guards.items())
provider = Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
current = {str(p): record(p) for p in provider.rglob('*') if p.is_file()}
provider_check = current == receipt['provider_before']
checks = {
    'pinned_files': len(PINS),
    'source_equal_to_run_copy': sha(STD/'PositiveModelIPRAStandardAdapter.lean') == sha(SNAPSHOT/'PositiveModelIPRAStandardAdapter.lean'),
    'output_matches_receipt': sha(SNAPSHOT/'PositiveModelIPRAStandardAdapter.olean') == receipt['object_sha256'],
    'standard_author_exit_zero': receipt['exit_code'] == 0,
    'standard_recorded_guards_unchanged': receipt['guards_unchanged'],
    'standard_recorded_provider_unchanged': receipt['provider_unchanged'],
    'current_direct_guards_match_receipt': guard_check,
    'current_provider_matches_receipt': provider_check,
    'current_provider_files': len(current),
    'native_author_exit_zero': native['exit_code'] == 0,
    'native_recorded_guards_unchanged': native['guards_unchanged'],
    'native_recorded_provider_unchanged': native['provider_unchanged'],
    'native_source_matches_receipt': native['source_sha256'] == sha(NATIVE/'PositiveModelIPRAAdapter.lean'),
    'native_object_matches_pin': native['object_sha256'] == PINS[Path('/tmp/positive-model-ipra-adapter-author-gzcg51tr/PositiveModelIPRAAdapter.olean')],
    'three_reported_axiom_lines': log.count('depends on axioms: [propext,') == 3 and log.count(' Classical.choice,\n Quot.sound]') == 3,
    'log_clean': all(x not in log for x in ('error:', 'warning:', 'sorryAx')),
}
checks['pinned_files_unchanged'] = all(sha(path) == pin for path, pin in PINS.items())
print(json.dumps(checks, indent=2, sort_keys=True))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)
