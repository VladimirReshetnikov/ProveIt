from pathlib import Path
import hashlib,json,re,subprocess
R=Path.cwd();P=Path('/tmp/k215-intake215/K215_Proof_Simplification (2)/k215-proof-simplification');O=Path('/tmp/k215-intake215')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
arrival=read(O/'arrival.json');a=next(x for x in arrival['archives']if x['number']==1)
assert arrival['arrival_commit']=='1b16269c48e54b0e5aff35caa645f392f9c019af'
assert sha(P/'report.tex')==next(x['sha256']for x in a['members']if x['member'].endswith('/report.tex'))
D=P/'decoder-residual';pins=read(D/'source-pins.json');ledger=read(D/'evidence/validation-receipt.json');assert len(pins['order'])==len(pins['modules'])==len(ledger['modules'])==51
rows=[]
for row in ledger['modules']:
 m=row['module'];v=pins['modules'][m];q=D/'lean'/Path(*m.split('.')).with_suffix('.lean')if v['origin']=='new'else R/v['origin'];log=D/'evidence/accepted-logs'/f'{m}.log'
 assert sha(q)==v['sha256']==row['source_sha256'];assert sha(log)==row['log_sha256'];assert row['exit_code']==0 and not row['unexpected_axioms']
 rows.append({'module':m,'source':str(q),'source_sha256':sha(q),'origin':v['origin'],'accepted_log_sha256':sha(log)})
assert sum(v['origin']=='new' for v in pins['modules'].values())==24
pat=re.compile(r'theorem block_(\d+)\s*:\s*allSites \((?:KSim.checkEdge|KResidualRouting215.checkLeafSuffix) tm215\) (\[[^\]]*\])\s*\(descend KSource215.t215 (\[[^\]]*\])\) = true := by\s*exact (?:KFastSites215|KResidualFast215).allSites_of_fast \(by decide \+kernel\)')
blocks={};oldblocks={}
for f in (D/'lean/BusyBeaver/ZFC').glob('KResidualSites215Batch*.lean'):
 for i,rev,p in pat.findall(f.read_text()):
  assert int(i)not in blocks;blocks[int(i)]=(rev,p)
for f in (R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC').glob('KSites215Batch*.lean'):
 for i,rev,p in pat.findall(f.read_text()):
  assert int(i)not in oldblocks;oldblocks[int(i)]=(rev,p)
assert blocks==oldblocks and set(blocks)==set(range(105))
for rev,p in blocks.values():assert rev[1:-1].split(', ')==p[1:-1].split(', ')[::-1]
# Independently reconstruct the optional transparent abbreviation in memory only.
ab=P/'subtree-abbreviation';measure=read(ab/'measurement.json');helper='/-- Check a source subtree while writing its complete prefix only once. -/\nabbrev checkedSubtree (test : List Bool → Edge → Bool) (t : Tree)\n    (prefix : List Bool) : Prop :=\n  allSites test prefix.reverse (descend t prefix) = true\n\n'
regex=re.compile(r'allSites \(KSim.checkEdge tm215\) \[([^\]]*)\]\s*\(descend KSource215.t215 \[([^\]]*)\]\) = true');number=0
for row in measure['files']:
 f=R/row['path'];s=f.read_text();assert sha(f)==row['before_sha256'];assert len(f.read_bytes())==row['before_bytes']
 if f.name=='SiteCoverage.lean':
  assert s.count('def leafCount : Tree → Nat\n')==1;t=s.replace('def leafCount : Tree → Nat\n',helper+'def leafCount : Tree → Nat\n')
 else:
  def sub(m):
   global number
   rev,word=m.groups();assert rev.split(', ')==word.split(', ')[::-1];number+=1
   return 'checkedSubtree (KSim.checkEdge tm215) KSource215.t215 ['+word+']'
  t=regex.sub(sub,s)
 assert hashlib.sha256(t.encode()).hexdigest()==row['after_sha256'] and len(t.encode())==row['after_bytes']
assert number==105 and sum(x['before_bytes']-x['after_bytes']for x in measure['files'])==18565
for n in ['DominatedImplication','Lukasiewicz']:
 assert (P/'shared-basis/src/BusyBeaver/ZFC'/f'{n}.lean').read_bytes()==(R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/f'{n}.lean').read_bytes()
key=['report.tex','artifact-guide.tex','validation-summary.tex','README.md','NOTICE.md','decoder-residual/README.md','decoder-residual/source-pins.json','decoder-residual/evidence/validation-receipt.json','decoder-residual/lean/BusyBeaver/ZFC/KResidualRouting215.lean','decoder-residual/lean/BusyBeaver/ZFC/KResidualFast215.lean','decoder-residual/lean/BusyBeaver/ZFC/KResidualSites215.lean','decoder-residual/build.py','lean-bridge/README.md','lean-bridge/minimal/BusyBeaver/ZFC/KDenseBridge.lean','lean-bridge/terminal-drain/BusyBeaver/ZFC/TerminalDrain.lean','lean-bridge/terminal-drain/BusyBeaver/ZFC/KPartial.lean','lean-bridge/terminal-drain/BusyBeaver/ZFC/RegisterPartial.lean','lean-bridge/terminal-drain/BusyBeaver/ZFC/TerminalDrainExamples.lean','rocq-components/README.md','rocq-components/ADOPTION.md','rocq-components/TerminalDrain.v','rocq-components/relabel/K215F/StateRelabel.v','subtree-abbreviation/README.md','subtree-abbreviation/rewrite.py','subtree-abbreviation/measurement.json','subtree-abbreviation/generator-wiring.patch']
result={'status':'ORDINARY_REVIEW_WITH_OWN_READ_ONLY_STATIC_COMPARISONS','source':193,'arrival_commit':arrival['arrival_commit'],'archive_path':a['archive_path'],'archive_git_blob':a['archive_blob'],'archive_sha256':sha(a['scratch_archive']),'authored_base':'57541fe0cfe3af62b4cb58747d8d1d7c16b338d5','current_head_at_review':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'main_manuscript_lines':len((P/'report.tex').read_text().splitlines()),'manuscript_includes':['validation-summary.tex','artifact-guide.tex'],'key_member_pins':{n:{'sha256':sha(P/n),'bytes':len((P/n).read_bytes())}for n in key},'checks':{'all_51_component_source_pins_accessible_and_exact':True,'all_51_delivered_log_hashes_and_success_metadata_consistent':True,'objects_not_distributed_or_independently_checked':True,'residual_blocks_exact_same_105_paths_and_guards_by_retained_checker':True,'105_block_proof_bodies_exact_fast_transfer_kernel_decide':True,'optional_abbreviation_105_inert_reconstructions_match_delivered_after_hashes':True,'optional_abbreviation_net_source_bytes_saved':18565,'phase13_shared_basis_pair_literal_current':True},'residual_source_bindings':rows,'dense_successor_peer':{'path':'/tmp/k215-source193-dense-peer/review.json','sha256':sha('/tmp/k215-source193-dense-peer/review.json')},'scope':'Read full main report and both TeX includes, component documentation and selected mathematical sources. Own inert hash/string/graph-data checks only. No supplied script, generator, proof compiler, manifest validator or archive code executed. No current endpoint adoption or new formal status conferred.','checker_sha256':sha(__file__)}
(O/'ordinary-01-data.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['key_member_pins','residual_source_bindings']},indent=2))
