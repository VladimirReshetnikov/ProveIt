#!/usr/bin/env python3
"""Exact rotation240 whole-tape frame composition from three actual parents.
Only selected actual-import providers are reused from pinned successful records.
Fresh source/audit share120s, -j1/-M4096, default proof limits. Prepare-only has
no compiler/version call, dependency build or download. This is external Lean,
not an object-theory PA proof. Historical caches are required.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
CFG = {'module': 'BusyBeaver.ZFC.BootstrapFrameRotation240', 'source': '/tmp/zfc-rotation240-frame/BootstrapFrameRotation240.lean', 'source_sha256': '1a86e2d1434193fabb2b878e071017fcef74dfb858f8833dfbc61c47701151e4', 'audit': '/tmp/zfc-rotation240-frame/Audit.lean', 'audit_sha256': '7960ce5d3dbdd4fa9e707fc32639550eb9cea3ae8f27300806d31b0c7c90334f', 'imports': ['BusyBeaver.ZFC.BootRotation240Chunk009', 'BusyBeaver.ZFC.Rotation240Simulation', 'BusyBeaver.ZFC.LogicalSeed246'], 'probes': ['spares_nonempty', 'physical_seed', 'seed_tail', 'target_zip', 'frame_of_target', 'frame_of_checkpoint', 'target_checkpoint', 'bootstrap_frame'], 'callers': 9, 'parents': {'bootstrap': {'path': '/tmp/zfc-rotation240-bootstrap/chunk009/run1/verification.json', 'sha256': '68a2b1c456d52039496842f2ed89051eaffee93059edd7e77ceccbeff293d239', 'module': 'BusyBeaver.ZFC.BootRotation240Chunk009', 'probes': 10, 'callers': 13, 'probe_names': ['SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409680', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409680', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409688', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409688', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409690', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409690', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.block409691', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.reached409691', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.bootstrap409691', 'SetTheory.BusyBeaver.ZFC.BootRotation240Chunk009.bootstrap_active_through'], 'logs': {'source': '/tmp/zfc-rotation240-bootstrap/chunk009/run1/source.log', 'audit': '/tmp/zfc-rotation240-bootstrap/chunk009/run1/audit.log'}, 'actual_provider_includes_tools': True}, 'frame': {'path': '/tmp/zfc-rotation240-runtime-seven-v1/frame/run1/verification.json', 'sha256': 'ac209f0b190a7224ae71187105684cc1abacc0ec4618a5b694e51fb31aa3b391', 'module': 'BusyBeaver.ZFC.Rotation240Simulation', 'probes': 14, 'callers': 15, 'probe_names': ['SetTheory.BusyBeaver.ZFC.Rotation240Simulation.registerBits_eq', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.flat_map_bit', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.start_concrete', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.source_represents', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.target_concrete', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.target_frame', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.incr_eq_write', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.decr_eq_write', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.unchanged_rebase', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.nth_vregs_append_getD', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.increment_rebase', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.decrement_rebase', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.valid_none', 'SetTheory.BusyBeaver.ZFC.Rotation240Simulation.valid_branch'], 'logs': {'source': '/tmp/zfc-rotation240-runtime-seven-v1/frame/run1/source.log', 'audit': '/tmp/zfc-rotation240-runtime-seven-v1/frame/run1/audit.log'}, 'actual_provider_includes_tools': True}, 'seed': {'path': '/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/results/prefix246-binary-verification.json', 'sha256': '6f23d1ff40845704cc58fbd59e98388b1c2e5b9b42aeb519ef03e62796cdf6f2', 'module': 'BusyBeaver.ZFC.BinaryPrefix246', 'probes': 9, 'callers': 9, 'probe_names': ['SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_initial_config', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.actual_coverage', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.boot_related', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_after_prefix_iff', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_register', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_zf_refutation', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.blank_halts_iff_zfc_refutation', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.nonhalting_iff_zf_consistency', 'SetTheory.BusyBeaver.ZFC.BinaryPrefix246.nonhalting_iff_zfc_consistency'], 'logs': {'source': '/tmp/zfc-prefix246-lean/endpoint/run1/source.log', 'audit': '/tmp/zfc-prefix246-lean/endpoint/run1/audit.log'}, 'actual_provider_includes_tools': False}}, 'expected_modules': ['BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.Choice', 'BoundedZFCConsistency.CodePredicate', 'BoundedZFCConsistency.Coding', 'BoundedZFCConsistency.FormulaClosedSet', 'BoundedZFCConsistency.InternalSat', 'BoundedZFCConsistency.InternalSatTotality', 'BoundedZFCConsistency.OmegaRecursion', 'BusyBeaver.Core', 'BusyBeaver.ZFC.ActualTree254', 'BusyBeaver.ZFC.Bisim254', 'BusyBeaver.ZFC.BootRotation240Chunk001', 'BusyBeaver.ZFC.BootRotation240Chunk002', 'BusyBeaver.ZFC.BootRotation240Chunk003', 'BusyBeaver.ZFC.BootRotation240Chunk004', 'BusyBeaver.ZFC.BootRotation240Chunk005', 'BusyBeaver.ZFC.BootRotation240Chunk006', 'BusyBeaver.ZFC.BootRotation240Chunk007', 'BusyBeaver.ZFC.BootRotation240Chunk008', 'BusyBeaver.ZFC.BootRotation240Chunk009', 'BusyBeaver.ZFC.BootRotation240First', 'BusyBeaver.ZFC.Bootstrap', 'BusyBeaver.ZFC.Code254', 'BusyBeaver.ZFC.Code254Containers', 'BusyBeaver.ZFC.Code254GIC', 'BusyBeaver.ZFC.Code254Models', 'BusyBeaver.ZFC.CodeOrder', 'BusyBeaver.ZFC.CompositionModel', 'BusyBeaver.ZFC.Constructible', 'BusyBeaver.ZFC.ConstructibleAbs', 'BusyBeaver.ZFC.ConstructibleChoice', 'BusyBeaver.ZFC.ConstructibleDef', 'BusyBeaver.ZFC.ConstructibleOrder', 'BusyBeaver.ZFC.ConstructibleReflect', 'BusyBeaver.ZFC.ConstructibleZF', 'BusyBeaver.ZFC.Dag254', 'BusyBeaver.ZFC.DecodeFresh254', 'BusyBeaver.ZFC.DeepPositiveClosure', 'BusyBeaver.ZFC.DefinableClosure', 'BusyBeaver.ZFC.DirtyProgram254', 'BusyBeaver.ZFC.DirtyRoot254', 'BusyBeaver.ZFC.Enum254', 'BusyBeaver.ZFC.EnumSafeStart254', 'BusyBeaver.ZFC.FastTableRotation240', 'BusyBeaver.ZFC.FiniteSets', 'BusyBeaver.ZFC.FiniteZipper', 'BusyBeaver.ZFC.InductiveAttempts', 'BusyBeaver.ZFC.InternalOrd', 'BusyBeaver.ZFC.InternalRank', 'BusyBeaver.ZFC.InternalWO', 'BusyBeaver.ZFC.Kalmar', 'BusyBeaver.ZFC.L2Axioms254', 'BusyBeaver.ZFC.L2AxiomsEval254', 'BusyBeaver.ZFC.L2Control254', 'BusyBeaver.ZFC.L2Lib254', 'BusyBeaver.ZFC.L2Macros254', 'BusyBeaver.ZFC.L2Root254', 'BusyBeaver.ZFC.LogicalSeed246', 'BusyBeaver.ZFC.Lukasiewicz', 'BusyBeaver.ZFC.NamedForm254', 'BusyBeaver.ZFC.NamedZF', 'BusyBeaver.ZFC.NativeDecoded254', 'BusyBeaver.ZFC.NativeTheory254', 'BusyBeaver.ZFC.OrderRec', 'BusyBeaver.ZFC.PSCCalibration', 'BusyBeaver.ZFC.Permutation252Frame', 'BusyBeaver.ZFC.PositiveClosure', 'BusyBeaver.ZFC.PowerSyntax', 'BusyBeaver.ZFC.ProfileAxioms', 'BusyBeaver.ZFC.ProfileCollection', 'BusyBeaver.ZFC.ProfileComposition', 'BusyBeaver.ZFC.ProfileCongruence', 'BusyBeaver.ZFC.ProfileModel', 'BusyBeaver.ZFC.ProfilePairs', 'BusyBeaver.ZFC.ProfileSyntax', 'BusyBeaver.ZFC.Prog254', 'BusyBeaver.ZFC.QuotientBasic', 'BusyBeaver.ZFC.QuotientCPGIC', 'BusyBeaver.ZFC.QuotientModel', 'BusyBeaver.ZFC.QuotientPower', 'BusyBeaver.ZFC.QuotientReplacement', 'BusyBeaver.ZFC.QuotientSeparation', 'BusyBeaver.ZFC.QuotientZF0', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RMEquiv254', 'BusyBeaver.ZFC.RegisterBoxes253', 'BusyBeaver.ZFC.RegisterBoxesPerm252', 'BusyBeaver.ZFC.RegisterMarkPerm252', 'BusyBeaver.ZFC.RegisterMarkRotation240', 'BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.RegisterPathClean', 'BusyBeaver.ZFC.Rotation240Boxes', 'BusyBeaver.ZFC.Rotation240KernelRows', 'BusyBeaver.ZFC.Rotation240Pulse', 'BusyBeaver.ZFC.Rotation240Simulation', 'BusyBeaver.ZFC.SatSupport', 'BusyBeaver.ZFC.SingletonInfinity', 'BusyBeaver.ZFC.SiteRotation240', 'BusyBeaver.ZFC.SymbolicRotation240', 'BusyBeaver.ZFC.Table253', 'BusyBeaver.ZFC.TablePerm252', 'BusyBeaver.ZFC.TableRotation240', 'BusyBeaver.ZFC.TarskiCalculus', 'BusyBeaver.ZFC.TarskiClean', 'BusyBeaver.ZFC.TarskiComplete', 'BusyBeaver.ZFC.TarskiDerived', 'BusyBeaver.ZFC.TarskiFalsity', 'BusyBeaver.ZFC.TarskiLeibniz', 'BusyBeaver.ZFC.TransRec', 'BusyBeaver.ZFC.TupleOrder', 'BusyBeaver.ZFC.WFModel', 'BusyBeaver.ZFC.WFRelativization', 'BusyBeaver.ZFC.WFTheory', 'BusyBeaver.ZFC.WellFoundedPart', 'BusyBeaver.ZFC.WritingRuns', 'BusyBeaver.ZFC.ZFNative', 'BusyBeaver.ZFC.ZFRank', 'BusyBeaver.ZFC.ZipperRuns', 'FirstOrder.Calculus', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf'], 'scope': 'Exact 409691-step whole-tape startup frame at distance 64, LogicalSeed246 and 167 nonempty value-one spares. No decoder coverage, complete binary calibration, or internal PA endpoint.'}
TOOLS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',
       'Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
TIMEOUT=120

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def need(ok,message):
 if not ok:raise RuntimeError(message)
def imports(path):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(path).read_text(),re.M)
def first_path(row):return Path(row['actual_first'] if 'actual_first' in row else row['path']).resolve()

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--source',type=Path,default=Path(CFG['source']))
 ap.add_argument('--audit',type=Path,default=Path(CFG['audit']))
 for label,cfg in CFG['parents'].items():
  ap.add_argument('--'+label+'-evidence',type=Path,required=cfg['path'] is None,
                  default=Path(cfg['path']) if cfg['path'] is not None else None)
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--prepare-only',action='store_true')
 args=ap.parse_args()
 if not __debug__:ap.error('Assertions must remain enabled.')
 need(all(not row['sha256'].startswith('PENDING_') for row in CFG['parents'].values()),
      'Freeze every required successful parent record before preparation or compilation.')
 repo=args.repo.resolve();work=args.output.resolve();source=args.source.resolve();audit=args.audit.resolve()
 need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())),'Use a new/empty external output.')
 need(sha(source)==CFG['source_sha256'] and sha(audit)==CFG['audit_sha256'],'Changed source/audit.')
 need(imports(source)==CFG['imports'] and imports(audit)==[CFG['module']],'Exact direct imports differ.')
 st=source.read_text();at=audit.read_text();prefix='SetTheory.BusyBeaver.ZFC.'+CFG['module'].rsplit('.',1)[1]+'.'
 need(re.findall(r'^theorem (\w+)',st,re.M)==CFG['probes'],'Source theorem census differs.')
 need(re.findall(r'^#print axioms (\S+)$',at,re.M)==[prefix+n for n in CFG['probes']] and
      len(re.findall(r'^example\b',at,re.M))==CFG['callers'],'Audit census differs.')
 for text in (st,at):
  need(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',text,re.M),'Forbidden proof shortcut.')
  need(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',text),'Keep default proof limits.')
 inputs=[Path(__file__).resolve(),source,audit];pool={};parents={};summaries=[];compiler=None;tool_pool={}
 for label,cfg in CFG['parents'].items():
  evidence=getattr(args,label+'_evidence');evidence=(evidence if evidence.is_absolute() else repo/evidence).resolve()
  need(sha(evidence)==cfg['sha256'],'Changed '+label+' parent record.')
  d=json.loads(evidence.read_text());parents[label]=(d,evidence);inputs.append(evidence)
  need(d['status']=='PASS' and d['prepare_only'] is False and d['only_standard_axioms'] is True and
       d['all_input_provider_postchecks'] is True and d['all_fresh_objects_unchanged_after_audit'] is True and
       d['before']==d['after'] and d['source_object_recorded_before_audit'] is True,'Incomplete '+label+' parent.')
  need((d['named_axiom_probes'],d['callers'])==(cfg['probes'],cfg['callers']),'Parent audit census differs.')
  need([q['label'] for q in d['commands']]==['source','audit'] and
       all(q['exit_code']==0 and not q.get('timed_out',False) for q in d['commands']),'Parent command failed.')
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
  need([n for n,_ in reports]==cfg['probe_names'] and len(set(cfg['probe_names']))==cfg['probes'] and
       all({x.strip() for x in block.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'} for _,block in reports),
       'Raw parent named axiom reports differ.')
  parent_audit=Path(d['audit']['snapshot']).resolve()
  need(sha(parent_audit)==d['audit']['sha256'] and
       re.findall(r'^#print axioms (\S+)$',parent_audit.read_text(),re.M)==cfg['probe_names'] and
       len(re.findall(r'^example\b',parent_audit.read_text(),re.M))==cfg['callers'],'Parent typed audit changed.')
  inputs.append(parent_audit)
  for command in d['commands']:
   raw=Path(cfg['logs'][command['label']]).resolve()
   need(sha(raw)==hashlib.sha256(command['output'].encode()).hexdigest(),'Parent raw log changed.')
   inputs.append(raw)
  need(all('sorryAx' not in q['output'] and "declaration uses 'sorry'" not in q['output'] for q in d['commands']),
       'Parent shortcut diagnostic.')
  fresh=d['fresh_modules'];need(len(fresh)==1 and fresh[0]['module']==cfg['module'],'Wrong fresh parent module.')
  f=fresh[0];saved=d['source_pass_object']
  need(all(saved[k]==f[k] for k in ('module','path','sha256','source_sha256')) and
       f['source_sha256']==d['source']['sha256'],'Parent pre-audit source binding differs.')
  first=d['fresh_first_provider_before_audit']
  need(first['module']==f['module'] and first_path(first)==Path(f['path']).resolve() and first['sha256']==f['sha256'],
       'Parent fresh first-provider identity differs.')
  c=d['compiler'];identity=(str(Path(c['path']).resolve()),c['sha256'],c['version'])
  need(identity[1]==COMPILER_SHA,'Unexpected compiler identity.')
  if compiler is None:compiler=dict(path=identity[0],sha256=identity[1],version=identity[2],compiler_version_query_performed=False)
  else:need(identity==(compiler['path'],compiler['sha256'],compiler['version']),'Parent compiler differs.')
  actuals={q['module']:q for q in d['actual_first_providers']}
  expected_actuals={q['module'] for q in d['reused_modules']}
  if cfg['actual_provider_includes_tools']:expected_actuals|={q['module'] for q in d['toolchain_providers']}
  need(len(actuals)==len(d['actual_first_providers']) and set(actuals)==expected_actuals,
       'Duplicate/missing parent provider or unexpected tool-schema variant.')
  rows=[(q,False) for q in d['reused_modules']]+[(dict(module=f['module'],source=d['source']['path'],
      source_sha256=d['source']['sha256'],object=f['path'],object_sha256=f['sha256']),True)]
  for q,is_fresh in rows:
   name=q['module']
   row=dict(module=name,source=str(Path(q['source']).resolve()),source_sha256=q['source_sha256'],
            object=str(Path(q['object']).resolve()),object_sha256=q['object_sha256'],evidence=str(evidence))
   if is_fresh:
    need(d['before'][str(Path(q['source']).resolve())]==d['after'][str(Path(q['source']).resolve())]==q['source_sha256'],'Parent fresh source pre/post binding differs.')
   else:
    for key in ('source','object'):
     need(d['before'][str(Path(q[key]).resolve())]==d['after'][str(Path(q[key]).resolve())]==q[key+'_sha256'],'Parent reused pre/post binding differs.')
    actual=actuals[name]
    need(first_path(actual)==Path(q['object']).resolve() and actual['sha256']==q['object_sha256'],'Parent actual provider differs.')
   if name in pool:
    need((pool[name]['source_sha256'],pool[name]['object_sha256'])==(row['source_sha256'],row['object_sha256']),
         'Conflicting same-named source/object '+name)
   else:pool[name]=dict(row,parent_label=label,parent_fresh=is_fresh)
  for t in d['toolchain_providers']:
   need(t['module'] in TOOLS and t['object_sha256']==TOOLS[t['module']],'Parent tool identity differs.')
   tp=str(Path(t['object']).resolve())
   need(d['before'][tp]==d['after'][tp]==t['object_sha256'],'Parent tool pre/post identity differs.')
   if cfg['actual_provider_includes_tools']:
    need(first_path(actuals[t['module']])==Path(tp) and actuals[t['module']]['sha256']==t['object_sha256'],
         'Parent tool first-provider identity differs.')
   if t['module'] in tool_pool:need(tool_pool[t['module']]['object_sha256']==t['object_sha256'],'Conflicting tool provider.')
   else:tool_pool[t['module']]=t
  summaries.append(dict(label=label,path=str(evidence),sha256=sha(evidence),fresh_module=cfg['module'],
                        source_object_recorded_before_audit=True))
 closure=[];visiting=set();tool_names={'Init'}
 def visit(name):
  if name in closure:return
  need(name in pool and name not in visiting,'Missing/cyclic actual provider '+name);visiting.add(name)
  q=pool[name]
  need(sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256'],'Current selected provider changed '+name)
  for child in imports(q['source']):
   if child=='Init' or child.startswith(('Lean.','Std.')):tool_names.add(child)
   else:visit(child)
  visiting.remove(name);closure.append(name)
 for name in CFG['imports']:visit(name)
 need(set(closure)==set(CFG['expected_modules']) and len(closure)==len(CFG['expected_modules']),
      'Exact project import closure differs.')
 need(tool_names==set(TOOLS) and tool_names<=set(tool_pool),'Exact Init/Omega boundary differs.')
 selected={name:pool[name] for name in closure}
 # Rehash only snapshots of fresh parents actually imported; evidence-only seed
 # reuse selects LogicalSeed246 and its dependencies, never BinaryPrefix246.
 for row in summaries:
  d,e=parents[row['label']];used=row['fresh_module'] in selected;row['fresh_module_selected']=used
  if used:
   for role in ('source','audit'):
    p=Path(d[role]['path']).resolve();snap=Path(d[role]['snapshot']).resolve()
    need(sha(p)==sha(snap)==d[role]['sha256']==d['before'][str(p)]==d['after'][str(p)],'Selected parent snapshot changed.')
    inputs.extend([p,snap])
 C=Path(compiler['path']);need(sha(C)==COMPILER_SHA,'Compiler bytes changed.');toolroot=C.parent.parent/'lib/lean'
 inputs.append(C)
 for q in selected.values():inputs.extend([Path(q['source']),Path(q['object'])])
 for name in sorted(tool_names):
  p=toolroot/Path(name.replace('.','/')).with_suffix('.olean')
  need(Path(tool_pool[name]['object']).resolve()==p.resolve() and sha(p)==TOOLS[name],'Selected tool bytes changed.');inputs.append(p)
 for p in inputs:need(not p.resolve().is_relative_to(work),'Input lies in output directory.')
 work.mkdir(parents=True,exist_ok=True);cache=work/'cache';cache.mkdir();snap=work/'sources'
 ss=snap/Path(CFG['module'].replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True)
 aa=snap/'Audit.lean';shutil.copyfile(source,ss);shutil.copyfile(audit,aa)
 for name,q in selected.items():
  dest=cache/Path(name.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 def first(name):
  rel=Path(name.replace('.','/')).with_suffix('.olean')
  return next(root/rel for root in (cache,toolroot) if (root/rel).is_file())
 actual=[]
 for name,q in selected.items():
  p=first(name);need(p.resolve()==Path(q['object']).resolve() and sha(p)==q['object_sha256'],'Actual first provider differs.')
  actual.append(dict(module=name,actual_first=str(p),resolved=str(p.resolve()),sha256=sha(p)))
 tools=[]
 for name in sorted(tool_names):
  p=first(name);need(p.resolve()==(toolroot/Path(name.replace('.','/')).with_suffix('.olean')).resolve() and
                   sha(p)==TOOLS[name],'Actual tool provider differs.')
  tools.append(dict(module=name,object=str(p.resolve()),object_sha256=sha(p),actual_first=str(p)))
 inputs.extend([ss,aa]);inputs=list(dict.fromkeys(p.resolve() for p in inputs));before={str(p):sha(p) for p in inputs}
 env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(C.parent.parent),PYTHONDONTWRITEBYTECODE='1')
 record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,scope=CFG['scope'],
  compiler=compiler,compiler_version_query_performed=False,source_overridden=source!=Path(CFG['source']).resolve(),
  audit_overridden=audit!=Path(CFG['audit']).resolve(),source=dict(path=str(source),sha256=sha(source),snapshot=str(ss)),
  audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aa)),provider_evidence=[dict(path=row['path'],sha256=row['sha256']) for row in summaries],
  parent_summaries=summaries,reused_modules=[{k:v for k,v in selected[name].items() if k not in ('parent_label','parent_fresh')} for name in closure],
  candidate_provider_count=len(pool),excluded_candidate_modules=sorted(set(pool)-set(closure)),exact_project_import_closure=True,
  project_module_count=len(closure),external_project_boundaries=[],toolchain_providers=tools,actual_first_providers=actual,
  actual_direct_tool_imports=sorted(tool_names),before=before,commands=[],fresh_modules=[],LEAN_PATH=str(cache),dependency_build=False,
  downloads=False,shared_wall_seconds=120,limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),
  expected_named_axiom_probes=len(CFG['probes']),expected_callers=CFG['callers'])
 def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
 def post():
  record['after']={str(p):sha(p) for p in inputs};need(record['after']==before,'Input/provider changed.')
  for name,q in selected.items():need(first(name).resolve()==Path(q['object']).resolve() and sha(first(name))==q['object_sha256'],'First provider changed.')
  for t in tools:need(first(t['module']).resolve()==Path(t['object']).resolve() and sha(first(t['module']))==t['object_sha256'],'Tool provider changed.')
  record['all_input_provider_postchecks']=True
 save()
 try:
  if args.prepare_only:post();save();print(work/'verification.json');return
  deadline=time.monotonic()+TIMEOUT
  def run(label,path,obj=None):
   cmd=[str(C),'-j1','-M4096','--root='+str(snap)]
   if obj is not None:cmd+=['-o',str(obj)]
   cmd+=[str(path)];started=time.monotonic();remaining=deadline-started;need(remaining>0,'Shared proof wall budget exhausted.')
   timed_out=False;interrupted=None
   proc=subprocess.Popen(cmd,cwd=snap,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
   try:data,_=proc.communicate(timeout=remaining)
   except BaseException as ex:
    timed_out=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timed_out else type(ex).__name__
    try:os.killpg(proc.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    data,_=proc.communicate()
   output,code=data.decode(errors='replace'),proc.returncode
   log=work/(label+'.log');log.write_text(output)
   record['commands'].append(dict(label=label,command=cmd,cwd=str(snap),seconds=time.monotonic()-started,exit_code=code,
                                  timed_out=timed_out,interrupted=interrupted,log=str(log),output=output));save()
   need(not timed_out and interrupted is None and code==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,label+' failed; inspect '+str(log))
   return output
  obj=cache/Path(CFG['module'].replace('.','/')).with_suffix('.olean');run('source',ss,obj)
  need(obj.is_file() and not obj.is_symlink(),'Fresh source object missing.')
  fresh=dict(module=CFG['module'],path=str(obj),sha256=sha(obj),source_sha256=sha(source))
  need(first(CFG['module']).resolve()==obj.resolve(),'Fresh source object is not first.')
  record.update(source_object_recorded_before_audit=True,source_pass_object=dict(fresh,source_command_index=0),fresh_modules=[fresh],
    fresh_first_provider_before_audit=dict(module=CFG['module'],actual_first=str(first(CFG['module'])),resolved=str(obj.resolve()),sha256=sha(obj)));save()
  output=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output,re.S)
  need([n for n,_ in reports]==[prefix+n for n in CFG['probes']],'Missing/reordered axiom reports.')
  axioms=[dict(name=n,axioms=[x.strip() for x in block.split(',') if x.strip()]) for n,block in reports]
  record['actual_axiom_sets']=axioms;save()
  need(all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in axioms),'Unexpected axioms.')
  post();need(sha(obj)==fresh['sha256'] and first(CFG['module']).resolve()==obj.resolve(),'Fresh source object changed during audit.')
  record.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=len(CFG['probes']),callers=CFG['callers'],
                only_standard_axioms=True,warnings={q['label']:q['output'].count('warning:') for q in record['commands']})
 except Exception as ex:
  record.update(status='FAIL',error=str(ex))
  try:post()
  except Exception as pe:record['postcheck_error']=str(pe)
  save();raise
 save();print(work/'verification.json')

if __name__=='__main__':main()
