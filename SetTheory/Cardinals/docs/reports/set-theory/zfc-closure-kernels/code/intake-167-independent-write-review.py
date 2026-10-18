from pathlib import Path, PurePosixPath
import hashlib,json,re,posixpath,ast
B=Path('/tmp/zfc244-d91a27b462-inspection/intake'); R=Path('/home/codex/.codex/worktrees/ec20/Proofs'); O=B/'independent-write-review'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
checks=0
def ck(v,msg):
 global checks
 checks+=1
 assert v,msg
p=json.loads((B/'write-inputs.json').read_text()); files=p['files']; target={r['target']:r for r in files}
ck(len(files)==len(target)==139,'exact selected census')
ck(sha(B/'write_167.py')=='191a3ba93315f7d4c80e90fe7b5794f8105acf2af5e6155bfa2b75c01abcb6e8','builder')
ck(sha(B/'write-inputs.json')=='4025253dc7f970c0602d83ad5181284220e3765661c618fed7e83edb003b34d5','manifest')
for row in files:
 q=Path(row['source']);ck(sha(q)==row['sha256'] and q.stat().st_size==row['bytes'],str(q))
 t=PurePosixPath(row['target']);ck(not t.is_absolute() and '..' not in t.parts and str(t).startswith('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/'),'target scope')
 if 'replace_before_sha256' in row:ck(t.name=='README.md','sole replacement')
ck(sum('replace_before_sha256'in r for r in files)==1,'one replacement')
ck(sha(R/p['base_article']['path'])==p['base_article']['sha256'],'base')
ck(sha(p['placement_map']['path'])==p['placement_map']['sha256'],'placement')
placement=json.loads(Path(p['placement_map']['path']).read_text()); placed=[r for r in placement['files'] if r['disposition']=='place_unchanged']
ck(len(placement['files'])==1044 and len(placed)==1007,'placement census')
for row in placed:ck(sha(R/row['target'])==row['sha256'],row['target'])
records={}
for k,d in p['records'].items():
 ck(sha(d['path'])==d['sha256'],k);records[k]=json.loads(Path(d['path']).read_text())
ck(records['primary']['cases']==8390 and records['primary']['symbolic_rules']==2312438,'primary counts')
ck(len(records['primary']['jobs'])==7 and all(j['returncode']==0 and not j['timeout'] for j in records['primary']['jobs']),'7 jobs')
ck(len(records['auxiliary']['jobs'])==15 and all(j['exit_code']==0 and not j['timed_out'] for j in records['auxiliary']['jobs']),'15 aux')
ck(records['logical']['returncode']==0 and not records['logical']['timeout'],'separate logical')
ck(records['combined']['counts']==dict(cases=8390,symbolic_rules=2314868),'combined counts')
for k in ['primary_review','auxiliary_review','combined_review']:ck(records[k]['findings']==[],k)
for a,b,f in [('primary_review','primary','verification'),('auxiliary_review','auxiliary','execution'),('combined_review','combined','verification')]:ck(records[a][f]['sha256']==p['records'][b]['sha256'],'review binding')
links=[]
prose=[]
for row in files:
 if Path(row['source']).parent!=B/'write-v3' or Path(row['source']).suffix!='.md':continue
 text=Path(row['source']).read_text();prose.append(desc(row['source']))
 if Path(row['source']).name=='host-README.md':text=text[text.index('Batch 167 adds '):text.index('## Sources, overlap and base')]
 for match in re.finditer(r'\[[^\]]*\]\(([^)]+)\)',text):
  link=match.group(1).split('#',1)[0]
  if not link or '://' in link:continue
  t=posixpath.normpath(posixpath.join(posixpath.dirname(row['target']),link))
  ck(t in target or (R/t).is_file(),f'link {link} -> {t}')
  links.append(dict(from_target=row['target'],link=link,resolves=t))
# Source parsing only: no imports or invocation of the reviewed helper.
a=ast.parse((B/'write_167.py').read_text());imports=[n for n in ast.walk(a) if isinstance(n,(ast.Import,ast.ImportFrom))]
ck(all((isinstance(n,ast.ImportFrom) and n.module=='pathlib') or (isinstance(n,ast.Import) and all(x.name in ['argparse','hashlib','json'] for x in n.names)) for n in imports),'inert imports')
result=dict(status='SOURCE_FIDELITY_AND_WRITE_HELPER_REVIEW_PASS',findings=[],reviewer_role='Independent of intake prose, placement and write helper; author of separately referenced ordinary/combined evidence reviews and three relative ports. Existing evidence was read, not rerun.',scope='Full current three new prose files, host source71 section, complete 108-line helper and explicit 139-file input mapping; not a reread of all inherited host prose or 1044 supplied sources.',builder=desc(B/'write_167.py'),inputs=desc(B/'write-inputs.json'),prose=prose,reviewer_source=desc(Path(__file__)),checks=checks,local_links=links,census=dict(selected_files=139,plus_input_manifest=1,placed_ancillary=1007,archive_only=37,recoverable=1044,primary_jobs=7,auxiliary_jobs=16,host_sources=71,collection_reports=290),accepted_scope=['QT244 ordinary source/runtime/blank/calibration; independent of compensated244 exact machine','Combined243 is subsequent, with distinct complete expanded replay and five-unit relative 83/39 Lean result; no absolute243 or PA endpoint','Broken unused auxiliary retained; valid primary expanded path unaffected','Failed historical row-usage condition, optional unrun seeds and bounded discovery searches remain explicit','Current ordinary review corrected SHA and 18-then-19 queue chronology preserved'],execution=dict(supplied_code=False,compiler=False,write_helper=False,maintained_edits=False),installation_review=False)
(O/'review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(review=desc(O/'review.json'),checks=checks,links=len(links))))
