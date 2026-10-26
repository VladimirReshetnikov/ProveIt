#!/usr/bin/env python3
"""Exercise the locally authored auditor in an isolated temporary copy.

Unlike check_integrated.py, this test harness writes temporary files, removes
them on exit, and invokes only that copied auditor with the current Python.
No Lean/compiler, network, git, incoming scripts, or source-tree writes occur.
"""
from __future__ import annotations
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'


def require(ok, message):
    if not ok: raise RuntimeError(message)


def inventory(root):
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in root.rglob('*') if path.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', type=Path, default=ROOT/'baseline')
    args = parser.parse_args()
    config = json.loads((ROOT/'audit/variants.json').read_text())
    with tempfile.TemporaryDirectory(prefix='round5-auditor-') as directory:
        base = Path(directory); package = base/'portable-package'; elsewhere = base/'elsewhere'
        elsewhere.mkdir()
        artifacts = ['audit/check_integrated.py', 'audit/variants.json', 'catalog/fresh_source_inventory.json',
                     'catalog/late91dce/candidate_binding.json']
        late_binding = json.loads((ROOT/'catalog/late91dce/candidate_binding.json').read_text())
        for record in late_binding['records']:
            target = package/'baseline'/record['path']
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(args.baseline_tree/record['path'], target)
        for variant in config['variants']:
            artifacts.append(variant['patch'])
            artifacts.extend(spec['candidate'] for spec in variant['files'].values())
            for name in variant['files']:
                target = package/'baseline'/PREFIX/name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(args.baseline_tree/PREFIX/name, target)
        for relative in artifacts:
            target = package/relative; target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/relative, target)

        def run(optimized=False):
            command = [sys.executable, '-B']+(['-O'] if optimized else [])
            result = subprocess.run(command+[str(package/'audit/check_integrated.py')],
                                    cwd=elsewhere, capture_output=True, text=True)
            require(not result.stderr, 'Unexpected auditor stderr: '+result.stderr)
            return result.returncode, json.loads(result.stdout)

        before = inventory(package)
        normal_code, normal = run(); optimized_code, optimized = run(True)
        require(normal_code == optimized_code == 0, 'Portable default-baseline replay failed')
        require(normal == optimized, 'Normal/optimized audit outputs differ')
        require(before == inventory(package), 'Auditor wrote to the copied package')
        require(not list(elsewhere.iterdir()), 'Auditor wrote to its cwd')

        by_name = {v['name']: v for v in config['variants']}
        controls = []
        mutations = [
            ('lost_subtraction_guard', 'guarded_power_cast_fusion', 'PrimePowerOrder.lean',
             'theorem pow_cast_eq_one_iff {g m : ℕ} (hg : 1 ≤ g)',
             'theorem pow_cast_eq_one_iff {g m : ℕ} (hg : 0 ≤ g)'),
            ('added_nonzero_modulus', 'guarded_power_cast_fusion', 'PrimePowerOrder.lean',
             '{g m : ℕ} (hg', '{g m : ℕ} [NeZero m] (hg'),
            ('changed_definition', 'gamma_pos_from_coprime', 'CurrentControllerUnits2011.lean',
             'def dimension (n : ℕ) : ℕ := auxiliary^n', 'def dimension (n : ℕ) : ℕ := auxiliary^(n+1)'),
            ('lost_omit_scope', 'bit3_clear_of_residue', 'CurrentWordPadding2011.lean',
             'omit [NeZero (N*2011)] in', ''),
            ('added_trust_hole', 'bit3_clear_of_residue', 'CurrentWordPadding2011.lean',
             '  simpa only [PaddingStaircase.bit3_mask_iff,',
             '  sorry\n  simpa only [PaddingStaircase.bit3_mask_iff,'),
            ('changed_coordinate_witness', 'exact_order_clients', 'CurrentPowerCoordinates2011.lean',
             'exact ⟨e,fun z => by rw [pow_mul]; exact he z⟩',
             'exact ⟨e,fun z => by rw [pow_mul]; exact he z⟩\n  skip'),
        ]
        for label, variant_name, name, old, new in mutations:
            variant = by_name[variant_name]
            candidate_path = package/variant['files'][name]['candidate']
            patch_path = package/variant['patch']
            candidate = candidate_path.read_text(); patch = patch_path.read_text()
            require(candidate.count(old) == 1, 'Mutation has no unique target: '+label)
            mutated = candidate.replace(old, new)
            baseline = (package/'baseline'/PREFIX/name).read_text()
            candidate_path.write_text(mutated)
            patch_path.write_text(''.join(difflib.unified_diff(
                baseline.splitlines(keepends=True), mutated.splitlines(keepends=True),
                fromfile='a/'+PREFIX+name, tofile='b/'+PREFIX+name)))
            for optimized_mode in (False, True):
                code, result = run(optimized_mode)
                require(code != 0 and result['status'] == 'FAIL', 'Mutation escaped: '+label)
                controls.append({'mutation': label, 'optimized': optimized_mode,
                                 'rejected': True, 'reason': result['error']})
            candidate_path.write_text(candidate); patch_path.write_text(patch)
        require(before == inventory(package), 'Mutation test failed to restore isolated copy')
    print(json.dumps({'status': 'PASS_PORTABILITY_AND_NEGATIVE_CONTROLS',
                      'arbitrary_cwd_and_default_sibling_baseline': True,
                      'normal_and_optimized_json_identical': True,
                      'auditor_writes_observed': 0, 'negative_controls': controls,
                      'lean_status': 'UNCOMPILED'}, indent=2))


if __name__ == '__main__': main()
