"""Check fixed252 action/configuration/run arithmetic after five fresh prerequisites.

This separate arithmetic checker reuses an explicitly supplied, source/object-
matched Std core and pinned built Foundation/Mathlib. All new modules/audits are
freshly compiled serially in external scratch. No download/dependency rebuild,
shared-cache mutation, main-runner edit or internal PA machine/proof equivalence is asserted.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

RESEARCH=Path('Computability/BusyBeaver/Research/ZFC')
LEAN=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
PREFIX='SetTheory.BusyBeaver.ZFC.'
# Explicit reviewed audit contracts; do not infer trusted contracts from input.
SPECS={
 'graph':dict(module='ArithmeticMachineGraphPerm252',audit='arithmetic_machine_graph_perm252_audit.lean',imports=['BusyBeaver.ZFC.ArithmeticMachinePerm252','BusyBeaver.ZFC.ArithmeticHistory254'],
  probes=('lookup_defined','lookup_nat','numeral_mono','lookupValue_bound','actionLookup_defined','literalRows_length','literalRows_positive_bounded','actionLookup_bound','literal_lookup_actual','actionLookup_nat','halt_action_number','first_action_number'),callers=17),
 'step':dict(module='ArithmeticMachineStepPerm252',audit='arithmetic_machine_step_perm252_audit.lean',imports=['BusyBeaver.ZFC.ArithmeticMachineGraphPerm252'],
  probes=('bounded_output_pair','apply_defined','generic_step_defined','step_defined','step_total','decode_encode','encode_decode','lookupNat_absent','lookupNat_zero','lookupNat_invalid','actionNumber_decode','actionNumber_positive','foundation_sub_projection_nat','applyValue_nat_formula','applyValue_nat','native_read_bit','stepValue_nat_encoded','stepValue_nat','stepDef_nat'),callers=31),
 'run':dict(module='ArithmeticMachineRunPerm252',audit='arithmetic_machine_run_perm252_audit.lean',imports=['BusyBeaver.ZFC.ArithmeticMachineStepPerm252'],
  probes=('run_defined','run_defined_delta','run_definable','run_zero','run_succ','run_total','run_nat','runDef_nat','run_state_nat','run_halt_iff','haltingSentence_nat','totalitySentence_true','isigma1_proves_totality','peano_proves_totality'),callers=25),
}


def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path);p.add_argument('--dependency-root',type=Path,required=True)
 p.add_argument('--core-evidence',type=Path,required=True);p.add_argument('--core-cache',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[]);p.add_argument('--lean',type=Path)
 p.add_argument('--through',choices=tuple(SPECS),default='run');p.add_argument('--prepare-only',action='store_true')
 for stage in SPECS:
  p.add_argument('--'+stage+'-source',type=Path);p.add_argument('--'+stage+'-audit',type=Path)
 p.add_argument('--output',type=Path);a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 script=Path(__file__).resolve();repo=a.repo.resolve() if a.repo else next((q for q in script.parents if(q/'.git').exists()),None)
 if repo is None:p.error('Pass --repo outside checkout.')
 helper_path=repo/RESEARCH/'check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('machine_arithmetic_helpers',helper_path)
 if spec is None or spec.loader is None:p.error('Maintained Cantor checker helper missing.')
 base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
 root=a.dependency_root.resolve();history_runner=repo/RESEARCH/'check_arithmetic_history254.py'
 stages=list(SPECS)[:list(SPECS).index(a.through)+1];sources={};audits={}
 for stage in stages:
  contract=SPECS[stage]
  base.fail(bool(contract['probes']) and contract['callers']>0,'Final reviewed audit contract is not installed for '+stage)
  sources[stage]=(getattr(a,stage+'_source') or repo/LEAN/(contract['module']+'.lean')).resolve()
  audits[stage]=(getattr(a,stage+'_audit') or repo/RESEARCH/contract['audit']).resolve()
  base.fail(sources[stage].is_file() and audits[stage].is_file(),'Missing machine source/audit for '+stage)
  text=audits[stage].read_text();qualified=[PREFIX+contract['module']+'.'+n for n in contract['probes']]
  base.fail(re.findall(r'^#print axioms (.+)$',text,re.M)==qualified and len(re.findall(r'^example\b',text,re.M))==contract['callers'],'Unexpected stored audit contract: '+stage)
  base.fail(base.lean_imports(sources[stage].read_text())==contract['imports'],'Review changed imports before checking: '+stage)
 work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-arithmetic-machine252-check-'))
 if any(work.is_relative_to(q) for q in(repo,root)) or(work.exists() and any(work.iterdir())):p.error('Use new/empty external scratch.')
 work.mkdir(parents=True,exist_ok=True)
 inputs=[script,helper_path,history_runner,a.core_evidence.resolve(),*sources.values(),*audits.values()]
 for stem,module in [('cantor','Cantor'),('code254','Code254'),('templates254','Templates254'),('row254','Row254'),('history254','History254')]:
  inputs += [repo/LEAN/('Arithmetic'+module+'.lean'),repo/RESEARCH/('arithmetic_'+stem+'_audit.lean'),repo/RESEARCH/('check_arithmetic_'+stem+'.py')]
 inputs=list(dict.fromkeys(inputs));hashes={str(q):base.digest(q) for q in inputs}
 record=dict(status='PREPARED' if a.prepare_only else 'RUNNING',scope='Fresh five-arithmetic prerequisite chain plus fixed252 machine arithmetic through '+a.through+'. No machine/proof internal PA equivalence.',repo=str(repo),scratch=str(work),inputs=hashes,selected_stages=stages,commands=[],dependency_rebuild=False,downloads=False,main_runner_or_umbrella_modified=False)
 def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
 save()
 if a.prepare_only:return
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
 def run(label,command):
  t=time.monotonic();r=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True);text=r.stdout+r.stderr;log=work/(label+'.log');log.write_text(text)
  record['commands'].append(dict(label=label,command=command,cwd=str(work),exit_code=r.returncode,seconds=round(time.monotonic()-t,6),log=str(log),output=text));save()
  base.fail(r.returncode==0 and 'sorryAx' not in text and "declaration uses 'sorry'" not in text,label+' failed; inspect '+str(log));print(label,'PASS',record['commands'][-1]['seconds'],flush=True);return text
 try:
  # Rebuild all five arithmetic sources/audits, never reuse prior proof objects.
  command=[sys.executable,'-B',str(history_runner),'--repo',str(repo),'--dependency-root',str(root),'--core-evidence',str(a.core_evidence.resolve()),'--output',str(work/'history')]
  for flag,value in(('--core-cache',a.core_cache),('--lean',a.lean)):
   if value is not None:command += [flag,str(value.resolve())]
  for value in a.library_path:command += ['--library-path',str(value.resolve())]
  run('history-prerequisite',command);prior=json.loads((work/'history/verification.json').read_text())
  base.fail(prior.get('status')=='PASS' and prior['total_named_axiom_probes']==151 and prior['total_callers']==164 and prior['only_standard_axioms'],'Incomplete five-arithmetic checks.')
  base.fail(len(prior['fresh_modules'])==5 and prior['fresh_stored_audits']==5,'Prerequisite did not rebuild all five modules/audits.')
  env.update(LEAN_PATH=prior['LEAN_PATH'],LEAN_NUM_THREADS='1');cache=Path(env['LEAN_PATH'].split(os.pathsep)[0]);compiler=Path(prior['compiler']['path']);compiler_hash=base.digest(compiler)
  base.fail(compiler.is_absolute() and 'version 4.32.0' in prior['compiler']['version'],'Expected absolute pinned4.32.0 compiler.')
  evidence=json.loads(a.core_evidence.read_text());base.fail(str(evidence.get('status','')).startswith('PASS') and evidence.get('all_source_identities_unchanged_after_check') is True and evidence.get('units',0)>=168,'Need successful168+ core source closure.')
  core_cache=a.core_cache.resolve() if a.core_cache else Path(evidence['cache']).resolve();rows={}
  for row in evidence['source_closure']:
   rel=Path(row['path']);base.fail(not rel.is_absolute() and '..' not in rel.parts and rel.suffix=='.lean','Unsafe core source path.')
   base.fail('/Lean/' in rel.as_posix(),'Unexpected core source layout.');module=rel.as_posix().split('/Lean/',1)[1].removesuffix('.lean').replace('/','.')
   base.fail(module not in rows,'Duplicate core module.');rows[module]=row
  reused={q['module']:dict(q) for q in prior['reused_core']};visiting=set()
  def visit(module):
   base.fail(module in rows and module not in visiting,'Missing/cyclic recorded core: '+module);row=rows[module];source=repo/row['path'];obj=core_cache/Path(module.replace('.','/')).with_suffix('.olean')
   base.fail(source.is_file() and obj.is_file() and base.digest(source)==row['sha256'] and base.digest(obj)==row['olean_sha256'],'Core source/object does not match successful evidence: '+module)
   if module in reused:
    q=reused[module];base.fail(q['source_sha256']==row['sha256'] and q['olean_sha256']==row['olean_sha256'] and base.digest(Path(q['olean']))==row['olean_sha256'],'Prior arithmetic used different core object: '+module);return
   visiting.add(module)
   for imported in base.lean_imports(source.read_text()):
    if imported in rows:visit(imported)
    else:base.fail(imported in{'Init','Std','Lean'} or imported.startswith(('Init.','Std.','Lean.')),'Unexpected non-Std core import: '+imported)
   target=cache/Path(module.replace('.','/')).with_suffix('.olean');base.fail(not target.exists() and not target.is_symlink(),'Unexpected preexisting core object: '+module);target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(obj.resolve())
   reused[module]=dict(module=module,path=row['path'],source_sha256=row['sha256'],olean=str(target),olean_sha256=row['olean_sha256']);visiting.remove(module)
  for module in list(reused):visit(module)
  visit('BusyBeaver.ZFC.ArithmeticMachinePerm252')
  # Capture the five freshly emitted objects before the new graph/step/run.
  fresh=[]
  for module in prior['fresh_modules']:
   obj=cache/Path(module.replace('.','/')).with_suffix('.olean');base.fail(obj.is_file() and not obj.is_symlink(),'Missing fresh arithmetic object: '+module)
   fresh.append(dict(module=module,path=str(obj),sha256=base.digest(obj)))
  record.update(compiler=prior['compiler'],compiler_binary_sha256=compiler_hash,dependencies=prior['dependencies'],core_evidence=dict(path=str(a.core_evidence.resolve()),sha256=base.digest(a.core_evidence),units=evidence['units'],cache=str(core_cache)),reused_core=list(reused.values()),reused_core_count=len(reused),fresh_prerequisite=prior,fresh_arithmetic_prerequisite_objects=fresh,LEAN_PATH=env['LEAN_PATH'],new_modules=[]);save()
  all_reports=[];total_callers=0;new_objects=[]
  for stage in stages:
   contract=SPECS[stage];module='BusyBeaver.ZFC.'+contract['module'];snapshot=work/'sources'/Path(module.replace('.','/')).with_suffix('.lean');snapshot.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(sources[stage],snapshot);audit_copy=work/contract['audit'];shutil.copyfile(audits[stage],audit_copy)
   obj=cache/Path(module.replace('.','/')).with_suffix('.olean');base.fail(not obj.exists() and not obj.is_symlink(),'New arithmetic object already present: '+module);obj.parent.mkdir(parents=True,exist_ok=True)
   run(stage+'-source',[str(compiler),'--root='+str(work/'sources'),'-o',str(obj),str(snapshot)]);objhash=base.digest(obj);output=run(stage+'-audit',[str(compiler),str(audit_copy)])
   parsed=[]
   for name,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output,re.S):
    axioms=[q.strip() for q in block.split(',') if q.strip()];base.fail(set(axioms)<=base.STANDARD_AXIOMS,'Unexpected axioms: '+name);parsed.append(dict(theorem=name,axioms=axioms))
   qualified={PREFIX+contract['module']+'.'+n for n in contract['probes']};base.fail(len(parsed)==len(qualified) and {q['theorem'] for q in parsed}==qualified,'Missing/duplicate/unexpected audit report: '+stage)
   base.fail(base.digest(obj)==objhash,'New object changed during its audit.');entry=dict(stage=stage,module=module,source=dict(path=str(sources[stage]),sha256=hashes[str(sources[stage])],snapshot=str(snapshot)),audit_source=dict(path=str(audits[stage]),sha256=hashes[str(audits[stage])],snapshot=str(audit_copy)),module_object=dict(path=str(obj),sha256=objhash),axiom_reports=parsed,named_axiom_probes=len(parsed),callers=contract['callers']);record['new_modules'].append(entry);all_reports+=parsed;total_callers+=contract['callers'];new_objects.append(entry['module_object']);save()
  base.fail(all(base.digest(Path(q))==h for q,h in hashes.items()),'An input source/audit/helper changed.')
  base.fail(all(base.digest(repo/q['path'])==q['source_sha256'] and base.digest(Path(q['olean']))==q['olean_sha256'] for q in reused.values()),'A reused actual core source/object changed.')
  base.fail(all(base.digest(Path(q['path']))==q['sha256'] for q in fresh+new_objects),'A fresh arithmetic object changed.')
  base.fail(all(base.digest(Path(q['source']))==q['source_sha256'] and base.digest(Path(q['object']))==q['object_sha256'] for q in prior['iteration_providers']),'A PRF/Seq provider changed.')
  base.fail(all(base.digest(Path(q['path']))==q['sha256'] for q in prior['dependencies']['providers'].values()),'A cached arithmetic dependency provider changed.')
  base.fail(base.digest(compiler)==compiler_hash,'Compiler changed.')
  record.update(status='PASS',named_axiom_probes=len(all_reports),callers=total_callers,total_named_axiom_probes=151+len(all_reports),total_callers=164+total_callers,only_standard_axioms=True,fresh_modules=prior['fresh_modules']+[x['module'] for x in record['new_modules']],fresh_stored_audits=5+len(stages),all_source_and_reused_object_identities_unchanged_after_check=True,PRF_Seq_and_dependency_provider_identities_unchanged_after_check=True,warning_count=sum(c['output'].count('warning:') for c in record['commands'][1:]));save();print('Evidence:',work,flush=True)
 except Exception as e:record.update(status='FAIL',error=str(e));save();raise

if __name__=='__main__':main()
