from pathlib import Path
import ast,difflib,hashlib,json
B=Path('/tmp/zfc-routing245-lean/coverage-subtree-pilots')
old=Path('/tmp/zfc-routing245-lean/coverage-pilots/check-pilots.py').read_text()
s=old
s=s.replace('Serial routing245 leaf measurements, each with a shared120-second source/audit budget.','Serial routing245 subtree measurements, each with a shared120-second source/audit budget.')
s=s.replace('Uses exact successful SiteRouting245 and ProgramRouting245 providers. Each leaf\nproves actual-tree linkage and acceptance at fuel4000; CD includes both guards.','Uses exact successful SiteRouting245 and ProgramRouting245 providers plus the\nchecked generic SiteCoverage provider. Each actual-tree subtree retains its full\nreverse prefix and checks fuel4000, including both CD guards.')
s=s.replace("MANIFEST_SHA='032d42a2d8d8de138482b025d7759d725139a3ed056ed25213b3af61a2e2e5f1'", "MANIFEST_SHA='c861f4b83dd94980edaece32b92c74f5a7e876d3c920ece6a616e7fd8d6cf60b'")
s=s.replace("GENERATOR_SHA='178c3e081ce28d4c684da47c84cb40407d148aeeeb3031a416c565d262468cc4'", "GENERATOR_SHA='146176f7f6cc8c53d673e8d3a544e3af865b5cfbe2442e7dd871a293a751fca1'\nBOUNDARY_SHA='b4a29c4fcc41e07cfb8c8117e5efd3e6754d6148ba3c37f53a86481369bb0e4d'\nCOVERAGE_EVIDENCE=('Computability/BusyBeaver/Research/ZFC/results/prefix246-runtime-verification.json',\n '1965fff0430079cec4e3bb067a22ca05ef2d526fe97fae1e7c74fab1e7fa506f')")
a=s.index('ORDER=');z=s.index('TIMEOUT=120',a)
s=s[:a]+'''ORDER=[70,174,0]
EXPECTED_CUTS={70:('1110100100101011010101000110111010111001',1684,1717,33,43,11),
 174:('111010010010101101010101111111',4684,4731,47,61,11),0:('0',0,10,10,13,5)}
DIRECT=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245']
PROBES=['checked']
'''+s[z:]
s=s.replace(" i=unit['site_index'];depth,opcode,operand,guards,callers=EXPECTED_CASES[i]", " i=unit['index'];path,lo,hi,leaves,guards,height=EXPECTED_CUTS[i];callers=2")
a=s.index(' need(module==');z=s.index(' source=Path(',a)
s=s[:a]+''' need(module==f'BusyBeaver.ZFC.SitesRouting245CutPilot{i:03d}' and
      tuple(unit[k] for k in ('path','lo','hi','leaves','guards','height'))==(path,lo,hi,leaves,guards,height) and
      unit['probes']==1 and unit['callers']==callers and unit['imports']==DIRECT,'Unit descriptor differs.')
'''+s[z:]
s=s.replace(' inputs=[Path(__file__).resolve(),manifest,generator]'," boundary=HERE/'boundary-plan.json';need(sha(boundary)==BOUNDARY_SHA,'Changed boundary inventory.')\n inputs=[Path(__file__).resolve(),manifest,generator,boundary]")
s=s.replace('# Revalidate every frozen pilot source/audit, even when selecting one leaf.','# Revalidate every frozen source/audit, even when selecting one subtree.')
s=s.replace("plan['pilots']","plan['selected_units']")
a=s.index(" expected_path='");z=s.index(' selected={}',a)
s=s[:a]+''' literal=lambda bits:'['+', '.join('true' if b=='1' else 'false' for b in bits)+']'
 expected_path=literal(path);reverse_path=literal(path[::-1])
 goal=f'allSites SiteRouting245.checkSite {reverse_path}\\n      (descend TreeRouting245.tree {expected_path}) = true'
 need(f'theorem checked :\\n    {goal} := by\\n  decide +kernel\\n' in st,'Exact subtree proposition/proof differs.')
 need(f'example : {goal} := checked' in at and
      f'(hl : LeafAt (descend TreeRouting245.tree {expected_path}) Q e)' in at and
      f'SiteRouting245.checkSite ({reverse_path}.reverse ++ Q) e = true :=' in at and
      f'allSites_sound SiteRouting245.checkSite hl {reverse_path} checked' in at,'Typed subtree audit clients differ.')
'''+s[z:]
a=s.index(" need(tool_pins==TOOLS")
s=s[:a]+''' # Select only the checked generic SiteCoverage pair from this older record.
 # Its unrelated Prefix246 runtime providers are neither imported nor promoted.
 e=args.coverage_evidence.resolve();need(sha(e)==COVERAGE_EVIDENCE[1],'Changed generic coverage evidence.')
 parent=json.loads(e.read_text());evidence[str(e)]=COVERAGE_EVIDENCE[1];inputs.append(e)
 need(parent['status']=='PASS' and parent['prepare_only'] is False and parent['only_standard_axioms'] is True and
      parent['all_input_provider_postchecks'] is True and parent['all_fresh_objects_unchanged_after_audit'] is True and
      parent['source_object_recorded_before_audit'] is True and parent['before']==parent['after'] and
      (parent['named_axiom_probes'],parent['callers'])==(11,12),'Incomplete generic coverage provider evidence.')
 need([q['label'] for q in parent['commands']]==['source','audit'] and
      all(q['exit_code']==0 and not q.get('timed_out',False) for q in parent['commands']),'Generic evidence command failure.')
 need(Path(parent['compiler']['path']).resolve()==compiler and parent['compiler']['sha256']==COMPILER_SHA and
      parent['compiler']['version']==version,'Generic provider compiler differs.')
 rows=[q for q in parent['reused_modules'] if q['module']=='BusyBeaver.ZFC.SiteCoverage']
 actuals=[q for q in parent['actual_first_providers'] if q['module']=='BusyBeaver.ZFC.SiteCoverage']
 need(len(rows)==len(actuals)==1,'Generic coverage provider missing or duplicated.')
 q=rows[0];actual=actuals[0]
 for k in ('source','object'):
  need(parent['before'][q[k]]==parent['after'][q[k]]==q[k+'_sha256'],'Generic provider pre/post binding differs.')
 need(actual['sha256']==q['object_sha256'] and first_path(actual)==Path(q['object']).resolve(),'Generic actual provider differs.')
 add(q,e);summaries.append(dict(label='generic_coverage',evidence=str(e),module=q['module'],reused_provider_only=True,
                               source_sha256=q['source_sha256'],object_sha256=q['object_sha256']))
 expected={q['module']:q for q in json.loads(boundary.read_text())['providers']}
 need(set(expected)==set(selected),'Provider set differs from frozen boundary inventory.')
 for m,q in selected.items():
  need(all(q[k]==expected[m][k] for k in ('source','source_sha256','object','object_sha256')),'Provider inventory differs '+m)
'''+s[a:]
s=s.replace("len(closure)==22,'Exact22-project", "len(closure)==23,'Exact23-project")
s=s.replace("leaf_index=i,path_bits=unit['path'],depth=depth,opcode=opcode,operand=operand,guard_cases=guards,site_fuel=4000,margin=64,", "cut_index=i,path_bits=path,leaf_interval=[lo,hi],leaf_count=leaves,subtree_height=height,guard_cases=guards,site_fuel=4000,margin=64,")
s=s.replace('manifest=descriptor(manifest),generator=descriptor(generator),provider_evidence=', 'manifest=descriptor(manifest),generator=descriptor(generator),boundary_inventory=descriptor(boundary),provider_evidence=')
s=s.replace('project_module_count=22','project_module_count=23').replace('expected_named_axiom_probes=2','expected_named_axiom_probes=1').replace('named_axiom_probes=2,callers=callers','named_axiom_probes=1,callers=callers')
s=s.replace("HERE/'pilot-plan.json'", "HERE/'subtree-plan.json'").replace("HERE/'prepare_pilots.py'", "HERE/'prepare_subtrees.py'")
s=s.replace(" ap.add_argument('--program-evidence',type=Path)", " ap.add_argument('--program-evidence',type=Path)\n ap.add_argument('--coverage-evidence',type=Path)")
s=s.replace("'--leaf'", "'--cut'").replace('args.leaf','args.cut')
s=s.replace(" if args.program_evidence is None:args.program_evidence=args.repo/PARENTS['program'][0]", " if args.program_evidence is None:args.program_evidence=args.repo/PARENTS['program'][0]\n if args.coverage_evidence is None:args.coverage_evidence=args.repo/COVERAGE_EVIDENCE[0]")
s=s.replace("units={u['site_index']:u for u in plan['selected_units']}","units={u['index']:u for u in plan['selected_units']}")
a=s.index(" need(len(units)==");z=s.index(' keys=ORDER',a)
s=s[:a]+''' need(len(units)==len(plan['selected_units'])==3 and set(units)==set(ORDER) and plan['preferred_order']==ORDER and
      plan['total_selected_leaves']==90 and plan['total_selected_guards']==117 and plan['probes']==3 and plan['callers']==6,
      'Exact subtree set differs.')
 need(plan['proof_policy']==dict(each_source_audit_shared_seconds=120,threads=1,memory_mib=4096,proof_limits='defaults') and
      plan['site_fuel']==4000 and plan['header_margin']==64,'Measurement policy differs.')
'''+s[z:]
s=s.replace('Duplicate leaf selection.','Duplicate subtree selection.').replace('selected_leaf_indices','selected_cut_indices').replace('failed_leaf','failed_cut')
s=s.replace('Only selected measured leaves; no all-sites or endpoint claim.', 'Only selected actual-tree subtrees; no complete all-sites or endpoint claim.')
s=s.replace("work/f'case{i:04d}'", "work/f'cut{i:03d}'").replace('dict(leaf_index=i,','dict(cut_index=i,').replace("'PASS_SELECTED_PILOTS'","'PASS_SELECTED_SUBTREES'")
ast.parse(s)
(B/'check-subtrees.py').write_text(s)
(B/'guard-from-leaf.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='checked-leaf/check-pilots.py',tofile='subtrees/check-subtrees.py')))
print(hashlib.sha256(s.encode()).hexdigest(),len(s.splitlines()))
