#!/usr/bin/env python3
"""Run the portable certificate checks. No PA/Lean theorem is claimed by this wrapper."""
from pathlib import Path
import subprocess,sys,json,hashlib
ROOT=Path(__file__).resolve().parent

def run(script,*args):
 print('\nChecking '+script,flush=True)
 subprocess.run([sys.executable,str(ROOT/script),*args],cwd=ROOT,check=True)

def main():
 if not __debug__:raise RuntimeError('Run without -O: assertion checks are required')
 run('comparison/compare_designs.py','--output',str(ROOT/'comparison/comparison_receipt.json'))
 run('rotated196/verify_layout.py')
 run('rotated196/verify_macro62.py')
 run('repair_obstructions/repair_obstruction.py')
 run('source_rotations/retarget_rotations.py','--second')
 run('axiom_rewrite/distributed_gate.py',str(ROOT/'axiom_rewrite/inputs/BusyBeaver'),
     '--output',str(ROOT/'axiom_rewrite/words'))
 run('axiom_rewrite/verify_selected_word.py','--receipt',str(ROOT/'axiom_rewrite/selected_word_audit.json'))
 run('axiom_rewrite/core_countermodel.py','--receipt',str(ROOT/'axiom_rewrite/core_countermodel_receipt.json'))
 run('grammar67/verify_grammar.py','--receipt',str(ROOT/'grammar67/receipt.json'))
 run('distributed198/verify_distributed.py')
 run('axiom_rewrite/audit_physical_binding.py',str(ROOT/'distributed198'),
     '--receipt',str(ROOT/'axiom_rewrite/physical_binding_audit.json'))
 run('shared_helper/replay.py','--output',str(ROOT/'shared_helper/receipt.json'))
 run('shared_helper/replay.py','--general','--output',str(ROOT/'shared_helper/general_receipt.json'))
 output={'all_portable_checks_passed':True,'working_state_record_improved':False,
   'pa_internal_biconditional_exported':False,
   'scope':'Thirty reference tables, two new 196-state layouts, a new 198-state distributed-gate compiler with independent source/startup audit, local obstruction certificates, shared-helper searches, source rotations, equivalent axiom emitter, common-core countermodel, and three grammar witnesses.'}
 (ROOT/'verification_summary.json').write_text(json.dumps(output,indent=2)+'\n')
 print(json.dumps(output,indent=2))

if __name__=='__main__':main()
