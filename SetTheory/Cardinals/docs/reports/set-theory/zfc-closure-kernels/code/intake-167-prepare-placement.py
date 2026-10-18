"""Own scratch-only source71 placement proposal preserving all inherited members."""
from pathlib import Path
import json,hashlib,collections,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc244-d91a27b462-inspection');O=W/'intake';I=json.loads((O/'inventory.json').read_text());P=W/'zfc244-loop-rotation-20261018/zfc244-loop-rotation-20261018';H='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
sha=lambda b:hashlib.sha256(b).hexdigest()
code={'.py','.v','.lean','.sh','.ps1','.cpp','.cc','.c','.h','.wl','.wls','.hs','.ml','.smt2'};aux={'.aux','.fdb_latexmk','.fls','.out','.toc'};readmes={'README.md','reference/baseline245/README.md','reference/baseline245/reference/context246/README.md'};files=[];targets=set()
for x in I['members']:
 p=Path(x['relative']);s=str(p);e=p.suffix.lower();x=dict(x)
 if e in {'.pdf','.tex'} or e in aux or s in readmes:
  x.update(disposition='archive_only',reason='Addition manuscript/PDF/TeX or delivery README, or delivered LaTeX auxiliary; original archive retains exact bytes.')
 else:
  folder='code/' if e in code or p.name in {'Makefile','makefile'} else '' if e in {'.md','.rst'} or p.name.lower().startswith(('readme','notice','license','copying')) else 'data/'
  slug='71-qt-'+s.replace('/','-');slug += '.txt' if slug.endswith('.log') else '';target=H+'/'+folder+slug
  if len('C:\\ProveIt\\'+target)>199:
   slug='71-qt-'+p.stem[:65]+'-'+sha(s.encode())[:10]+''.join(p.suffixes);slug+='.txt' if slug.endswith('.log') else '';target=H+'/'+folder+slug
  assert target not in targets and not (R/target).exists();targets.add(target);x.update(disposition='place_unchanged',target=target,windows_path_length=len('C:\\ProveIt\\'+target))
 files.append(x)
c=collections.Counter(x['disposition'] for x in files)
record={'status':'SOURCE_ONLY_PROPOSAL_NO_PLACEMENT','batch':167,'host_source':71,'host':H,'prefix':'71-qt-','archive':{k:I[k] for k in ['arrival','archive','archive_blob','archive_sha256','archive_bytes']},'counts':{'total':1044,'placed':c['place_unchanged'],'archive_only':c['archive_only'],'history_hit_members':I['counts']['member_history_hits'],'new_member_blobs':1044-I['counts']['member_history_hits'],'max_windows_path_length':max(x.get('windows_path_length',0) for x in files)},'files':files,'role':'Addition to existing closure-kernel/machine-minimization report; separately maintained candidate inputs may be promoted by root after review. Delivered request for a project folder is source content, not an override of intake section2.','retire_only_after_exact_placement':[I['archive']],'pending_queue':'Only the selected d91a27b462 loop-rotation archive belongs to this batch; eighteen earlier pending archives remain outside it. Other arrivals, if any, are not retired.','no_duplicate':'All1044 members were matched against reachable Git blobs and45 original placement trees:975 unique blobs,246 historically present unique blobs,297 member history hits,747 new member occurrences. New exact table/source rewrite, proof sections and drivers establish an addition rather than a repeated delivery; inherited files are preserved too.','original_data_untouched':True,'root_only_next_steps':['Review ordinary proof and supplied verification before execution on copy.','Place from fresh committed archive, compare all targetGitblobs, retire only thisZIP in one placement commit.','Write source71 reconciliation with new source rotation, retained row-coverage qualification, full optional source/formalism research and PA distinctions; preserve exactbytes/attribution.','Complete separate catalogue with reportcount290 and sourcecount71; no basearticle rewrite.']}
(O/'placement-proposal.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'counts':record['counts'],'map_sha256':sha((O/'placement-proposal.json').read_bytes())},indent=2))
