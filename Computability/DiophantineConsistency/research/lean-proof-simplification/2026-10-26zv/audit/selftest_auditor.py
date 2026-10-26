#!/usr/bin/env python3
"""Isolated portability and adversarial self-test of the locally authored auditor.

Unlike check_integrated.py this harness writes a temporary package, invokes its
copied auditor with Python only, and removes the temporary copy on exit. No
Lean, compiler, network, Git, incoming script, or source-tree modification.
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
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', type=Path, default=ROOT/'baseline')
    args = parser.parse_args()
    config = json.loads((ROOT/'audit/variants.json').read_text())
    binding = json.loads((ROOT/'evidence/git_source_bindings.json').read_text())
    with tempfile.TemporaryDirectory(prefix='round6-auditor-') as directory:
        base = Path(directory); package = base/'portable-package'; elsewhere = base/'elsewhere'
        elsewhere.mkdir()
        artifacts = ['audit/check_integrated.py','audit/variants.json','evidence/git_source_bindings.json',
                     'catalog/novelty_decisions.json','catalog/late60fcb/source_binding.json']
        documentary = json.loads((ROOT/'catalog/novelty_decisions.json').read_text())
        artifacts.extend(item['files']['source']['path'] for item in documentary['decisions'])
        late_binding = json.loads((ROOT/'catalog/late60fcb/source_binding.json').read_text())
        for item in binding['files']+late_binding['bindings']:
            target = package/'baseline'/item['path']; target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(args.baseline_tree/item['path'], target)
        for variant in config['variants']:
            artifacts.append(variant['patch'])
            artifacts.extend(spec['candidate'] for spec in variant['files'].values())
        artifacts.extend(alt['patch'] for alt in config['isolated_alternatives'])
        for relative in artifacts:
            target = package/relative; target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/relative, target)

        def run(optimized=False, override=False):
            command = [sys.executable, '-B']+(['-O'] if optimized else [])
            command.append(str(package/'audit/check_integrated.py'))
            if override: command += ['--baseline-tree',str(package/'baseline')]
            result = subprocess.run(command,cwd=elsewhere,capture_output=True,text=True)
            require(not result.stderr, 'Auditor emitted stderr: '+result.stderr)
            return result.returncode,json.loads(result.stdout)

        before = inventory(package)
        code, normal = run(); ocode, optimized = run(True); bcode, overridden = run(override=True)
        require(code == ocode == bcode == 0, 'Portable audit failed')
        require(normal == optimized == overridden, 'Mode/baseline override outputs differ')
        require(before == inventory(package) and not list(elsewhere.iterdir()), 'Auditor wrote files')
        by_name = {v['name']:v for v in config['variants']}
        mutations = [
          ('unlisted_retired_optional_edit','literal_affine_positions','CurrentControllerPositions2011.lean',
           '  have h : auxiliary ≤ auxiliary^(k+1) := by',
           '  skip\n  have h : auxiliary ≤ auxiliary^(k+1) := by'),
          ('changed_position_definition','literal_affine_positions','CurrentControllerPositions2011.lean',
           '  2+(auxiliary-1)*j.val','  3+(auxiliary-1)*j.val'),
          ('changed_option','literal_affine_positions','CurrentControllerPositions2011.lean',
           'set_option maxHeartbeats 4000000','set_option maxHeartbeats 8000000'),
          ('lost_rephase_zero_omission','exact_rephase_fields','CurrentWordRephase2011.lean',
           'omit [NeZero N] in',''),
          ('changed_modular_transport','exact_rephase_fields','CurrentWordRephase2011.lean',
           '(CurrentKernel2011.K+2^W)*word radix c [MOD radix^n-1]',
           '(CurrentKernel2011.K+2^W)*word radix c [MOD radix^n]'),
          ('changed_same_packing_witness','exact_rephase_fields','CurrentWordRephase2011.lean',
           '  have hf\' := normalization_rephase a dummy hd s t hst carry digits hf',
           '  skip\n  have hf\' := normalization_rephase a dummy hd s t hst carry digits hf'),
          ('changed_rank_cast_bridge','direct_rank_growth','CurrentPackingRank2011.lean',
           '  have hn := hc.trans_le (fourBlocks_ge_cube C F hC hCF)',
           '  have hn := hc.trans_le (fourBlocks_ge_cube C F hC hCF)\n  skip'),
          ('lost_cube_zero_omission','direct_rank_growth','CurrentPackingRank2011.lean',
           'omit [NeZero N] in',''),
          ('lost_mask_strict_bound','disjoint_add_housekeeping','NativePackingPopulation.lean',
           'theorem disjoint_add_lt {u A M : ℕ} (hA : A < 2^u)',
           'theorem disjoint_add_lt {u A M : ℕ} (hA : A ≤ 2^u)'),
          ('inserted_trust_hole','disjoint_add_housekeeping','NativePackingPopulation.lean',
           '  rw [JM1984.add_eq_land_add_lor, hm, zero_add]',
           '  sorry\n  rw [JM1984.add_eq_land_add_lor, hm, zero_add]'),
          ('unlisted_new_helper','disjoint_add_housekeeping','NativePackingPopulation.lean',
           'end DiophantineConsistency.NativePackingPopulation',
           'private theorem helper : True := by trivial\n\nend DiophantineConsistency.NativePackingPopulation')]
        controls = []
        for label,variant_name,filename,old,new in mutations:
            variant = by_name[variant_name]; cp = package/variant['files'][filename]['candidate']; pp = package/variant['patch']
            candidate = cp.read_text(); patch = pp.read_text()
            require(candidate.count(old) == 1, 'Nonunique negative-control target: '+label)
            mutated = candidate.replace(old,new); baseline = (package/'baseline'/PREFIX/filename).read_text()
            cp.write_text(mutated); pp.write_text(''.join(difflib.unified_diff(
                baseline.splitlines(keepends=True),mutated.splitlines(keepends=True),
                fromfile='a/'+PREFIX+filename,tofile='b/'+PREFIX+filename)))
            for mode in (False,True):
                status,result = run(mode)
                require(status != 0 and result['status'] == 'FAIL', 'Mutation escaped: '+label)
                controls.append({'mutation':label,'optimized':mode,'rejected':True,'reason':result['error']})
            cp.write_text(candidate); pp.write_text(patch)
        for name in ('optional_next_lt', 'optional_stride_lt', 'position_ne_three'):
            obsolete = package/'safety/patches'/(name+'.patch')
            obsolete.write_text((package/'safety/patches/position_budget.patch').read_text())
            for mode in (False,True):
                status,result = run(mode)
                require(status != 0 and result['status'] == 'FAIL', 'Obsolete patch escaped: '+name)
                controls.append({'mutation':'obsolete_patch_'+name,'optimized':mode,
                                 'rejected':True,'reason':result['error']})
            obsolete.unlink()
        target = package/'baseline'/PREFIX/'CurrentDummySafety2011.lean'
        source = target.read_text(); target.write_text(source+'\n')
        for mode in (False,True):
            status,result = run(mode)
            require(status != 0 and result['status'] == 'FAIL', 'Tampered bound baseline escaped')
            controls.append({'mutation':'changed_bound_physical_safety_baseline','optimized':mode,
                             'rejected':True,'reason':result['error']})
        target.write_text(source)
        require(before == inventory(package), 'Self-test did not restore isolated copy')
    print(json.dumps({'status':'PASS_PORTABILITY_AND_NEGATIVE_CONTROLS',
        'arbitrary_cwd_and_default_sibling_baseline':True, 'optional_baseline_tree_verified':True,
        'normal_and_optimized_json_identical':True, 'auditor_writes_observed':0,
        'negative_control_count':len(controls), 'negative_controls':controls,
        'scope':'These test enforcement of source controls, not Lean validity.',
        'lean_status':'UNCOMPILED'},indent=2))


if __name__ == '__main__': main()
