"""Own scratch-only source70 placement proposal and literal table identity inventory."""
from pathlib import Path
import json,hashlib,collections,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc244-248bc05936-inspection');O=W/'intake';I=json.loads((O/'inventory.json').read_text());P=W/'zfc244-compensated-routing-20261018';H='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
sha=lambda b:hashlib.sha256(b).hexdigest()
code={'.py','.v','.lean','.sh','.ps1','.cpp','.cc','.c','.h','.wl','.wls','.hs','.ml','.smt2'};aux={'.aux','.fdb_latexmk','.fls','.out','.toc'};readmes={'README.md','runtime/reference/context246/README.md'};files=[];targets=set()
for x in I['members']:
 p=Path(x['relative']);s=str(p);e=p.suffix.lower();x=dict(x)
 if e in {'.pdf','.tex'} or e in aux or s in readmes:
  x.update(disposition='archive_only',reason='Addition manuscript/PDF/TeX or delivery README, or delivered LaTeX auxiliary; original archive retains exact bytes.')
 else:
  folder='code/' if e in code or p.name in {'Makefile','makefile'} else '' if e in {'.md','.rst'} or p.name.lower().startswith(('readme','notice','license','copying')) else 'data/'
  slug='70-c244-'+s.replace('/','-');slug += '.txt' if slug.endswith('.log') else '';target=H+'/'+folder+slug
  if len('C:\\ProveIt\\'+target)>199:
   slug='70-c244-'+p.stem[:65]+'-'+sha(s.encode())[:10]+''.join(p.suffixes);slug+='.txt' if slug.endswith('.log') else '';target=H+'/'+folder+slug
  assert target not in targets and not (R/target).exists();targets.add(target);x.update(disposition='place_unchanged',target=target,windows_path_length=len('C:\\ProveIt\\'+target))
 files.append(x)
c=collections.Counter(x['disposition'] for x in files)
record={'status':'SOURCE_ONLY_PROPOSAL_NO_PLACEMENT','batch':166,'host_source':70,'host':H,'prefix':'70-c244-','archive':{k:I[k] for k in ['arrival','archive','archive_blob','archive_sha256','archive_bytes']},'counts':{'total':191,'placed':c['place_unchanged'],'archive_only':c['archive_only'],'history_hit_members':I['counts']['member_history_hits'],'new_member_blobs':191-I['counts']['member_history_hits'],'max_windows_path_length':max(x.get('windows_path_length',0) for x in files)},'files':files,'role':'Addition to existing closure-kernel/machine-minimization report; separately maintained candidate inputs may be promoted by root after review. Delivered request for a project folder is source content, not an override of intake section2.','retire_only_after_exact_placement':[I['archive']],'pending_queue':'Latest supplement increases18 to19; selecting this archive leaves18. No earlier archive receives a new local number here.','no_duplicate':'Exact191-member payload includes84 member occurrences not previously in reachable Git blobs and newly authored proof/driver;44 original placement trees checked for inherited members. New main-file hashes alone are not the novelty criterion.','original_data_untouched':True,'root_only_next_steps':['Review ordinary proof and supplied verification before execution on copy.','Place from fresh committed archive, compare all targetGitblobs, retire only thisZIP in one placement commit.','Write source70 reconciliation with finite local/all-values/PA distinctions and fullequational branch; preserve exactbytes/attribution.','Complete separate catalogue with reportcount290 and sourcecount70; no basearticle rewrite.']}
(O/'placement-proposal.json').write_text(json.dumps(record,indent=2)+'\n')
def parse(p):
 d={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  if not line or line.startswith('#'):continue
  q,b,w,m,t=line.split();q,b,w,t=map(int,[q,b,w,t]);assert b in [0,1] and w in [0,1] and m in ['L','R'] and (q,b) not in d;d[q,b]=(w,m,t)
 return start,d
oldp=P/'runtime/reference/zfc245_old.tm';maint=R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc245_old.tm'
if not maint.exists():
 candidates=list((R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245').glob('*old*.tm'));assert len(candidates)==1;maint=candidates[0]
assert maint.read_bytes()==oldp.read_bytes();os,old=parse(oldp);ns,new=parse(P/'machine/zfc_compensated244_old.tm');ds,dense=parse(P/'machine/zfc_compensated244.tm');ren=json.loads((P/'machine/renumbering.json').read_text());mp={int(k):v for k,v in ren['old_to_canonical'].items()}
assert os==ns==95 and ds==0 and len(old)==490 and len(new)==len(dense)==488
states={q for q,b in new};assert states=={q for q,b in old}-{122} and {t for w,d,t in new.values()}-states=={254}
assert sorted(states-{95})==ren['canonical_to_old'][1:] and ren['canonical_to_old'][0]==95
assert dense=={(mp[q],b):(w,d,mp[t]) for (q,b),(w,d,t) in new.items()};assert set(dense)=={(q,b) for q in range(244) for b in [0,1]}
changes=[{'state':q,'read':b,'old':list(old[q,b]),'new':list(new[q,b])} for q,b in sorted(new) if old[q,b]!=new[q,b]]
assert [(x['state'],x['read']) for x in changes]==[(92,1),(104,1),(106,1),(167,1)]
literal={'status':'STATIC_LITERAL_IDENTITY_REVIEW','baseline':{'path':str(maint),'sha256':sha(maint.read_bytes())},'new_old':{'path':str(P/'machine/zfc_compensated244_old.tm'),'sha256':sha((P/'machine/zfc_compensated244_old.tm').read_bytes())},'new_canonical':{'path':str(P/'machine/zfc_compensated244.tm'),'sha256':sha((P/'machine/zfc_compensated244.tm').read_bytes())},'canonical_rows':488,'working_states':244,'start':0,'halt_target':244,'dispatcher':mp[96],'removed_old':122,'changed_retained_rows':changes,'all_other_retained_rows_equal':True,'bijection_exact':True,'simulation_performed':False,'theorem_or_fresh_runtime_pass_claimed':False}
(O/'literal-identity.json').write_text(json.dumps(literal,indent=2)+'\n')
print(json.dumps({'placement':record['counts'],'map_sha256':sha((O/'placement-proposal.json').read_bytes()),'literal_sha256':sha((O/'literal-identity.json').read_bytes())},indent=2))
