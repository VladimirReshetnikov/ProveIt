#!/usr/bin/env python3
"""Offline replay of the218-target research packet, with explicit result status.

Default freshly proves every primitive case for both the valid alternative219
machine and the initialized218 core. --quick audits their stored certificates.
Both modes reproduce the218 core's blank-start failure. A PASS is not a claim
that the218-state blank-tape target has been achieved.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parent

def need(x,s):
 if not x:raise ValueError(s)
def dump(p,o):Path(p).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path,required=True);p.add_argument('--quick',action='store_true');p.add_argument('--full-baseline',action='store_true');a=p.parse_args()
 need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Assertions must be enabled')
 out=a.output_dir.resolve();need(out!=ROOT and ROOT not in out.parents,'Output must be outside portable');need(not out.exists()or not any(out.iterdir()),'Output must initially be empty');out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
 start=time.monotonic();rec=dict(status='RUNNING',target_states=218,target_achieved=False,mode='stored_runtime_integrity'if a.quick else'fresh_unbounded_runtime',phases=[])
 def save():rec['seconds']=time.monotonic()-start;dump(out/'replay.json',rec)
 def phase(name,args):
  t=time.monotonic();log=out/'logs'/f'{name}.log';print(name,flush=True)
  with log.open('w')as f:r=subprocess.run([sys.executable,'-B',*map(str,args)],stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
  rec['phases'].append(dict(name=name,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log.relative_to(out))));save();need(r.returncode==0,f'Failed{name}; see{log}')
 try:
  flags=(['--quick']if a.quick else[])+(['--full-baseline']if a.full_baseline else[])
  phase('01_valid_alternative219',[ROOT/'reproduce_alternative219.py',*flags,'--output-dir',out/'alternative219'])
  base=out/'alternative219/baseline/K219_Construction_2026-10-20'
  p221=out/'alternative219/parent_replay/parent_replay/baseline/K221_Construction_2026-10-20'
  machine=ROOT.parent/'machine/core218'
  phase('02_core218_literal_and_blank_failure',[ROOT/'core218_literal.py','--baseline',base,'--core',machine/'core218.native.tm','--sites',machine/'sites219.json','--output',out/'core218'])
  if a.quick:shutil.copytree(ROOT/'core218_reference_results',out/'core218/runtime')
  else:phase('03_core218_fresh_unbounded_runtime',[ROOT/'check_runtime218.py','--baseline',p221,'--table',out/'core218/core218.native.tm','--sites',out/'core218/sites219.json','--output',out/'core218/runtime'])
  phase('04_core218_independent_runtime_audit',[ROOT/'audit_runtime218.py','--baseline',p221,'--table',out/'core218/core218.native.tm','--sites',out/'core218/sites219.json','--runtime',out/'core218/runtime','--driver',ROOT/'check_runtime218.py','--construction',out/'core218/construction.json','--output',out/'core218/runtime_audit.json'])
  phase('05_fused_D_implication_certificate',[ROOT.parent/'research/theory218/certify_fused_d.py','--verify-only'])
  phase('06_GH_implication_certificate',[ROOT.parent/'research/theory_notes/certify_gh.py','--verify-only'])
  phase('07_uniform_obstruction_finite_premises',[ROOT/'check_obstruction.py','--output',out/'uniform_obstruction.json'])
  phase('08_power_of_two_padding_certificate',[ROOT.parent/'research/theory218_bootstrap/certify_residue_schedule.py','--output',out/'residue_lemma.json'])
  con=json.loads((out/'core218/construction.json').read_text());rt=json.loads((out/'core218/runtime/runtime.json').read_text())
  need(con['working_states']==218 and rt['cases']==6167,'Core certificate count')
  rec.update(status='QUICK_RESEARCH_REPLAY_PASS_TARGET_NOT_MET'if a.quick else'FULL_RESEARCH_REPLAY_PASS_TARGET_NOT_MET',target_achieved=False,
    accepted_blank_machine_states=219,initialized_core_states=218,initialized_core_cases=6167,initialized_core_symbolic_rules=1515192,
    initialized_core_table_sha256=con['table_sha256'],blank_core_status='UNCONDITIONAL_NONHALTING_RAY_FROM_STEP85',
    mathematical_scope='The alternative219 blank machine retains the inherited Con(ZFC) calibration. The218 initialized core has a complete arbitrary-natural primitive proof but fails blank initialization. No218-state blank Con(ZFC) construction is supplied.',
    verification_boundary='Executable ordinary mathematical certificates and inherited written calibration; no newly compiled proof-assistant endpoint. Finite search receipts are not unrestricted lower bounds.')
  save();print(rec['status'],flush=True)
 except Exception as e:rec.update(status='FAILED',error=repr(e));save();raise
if __name__=='__main__':main()
