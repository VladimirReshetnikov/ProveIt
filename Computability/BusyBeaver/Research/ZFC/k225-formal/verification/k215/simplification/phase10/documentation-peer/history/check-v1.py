from pathlib import Path
import hashlib,json,re,subprocess,urllib.parse
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
OUT=Path('/tmp/k215-phase10-docs-peer')
F=ROOT/'Computability/BusyBeaver/Research/ZFC/k225-formal'
P=F/'verification/k215/simplification/phase10'
RUN=Path('/tmp/k215-phase10-main/full-run1')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
js=lambda p:json.loads(p.read_text())
docs=[ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md',F/'README.md',F/'rho8cd/PROVEIT_STATUS.md',F/'verification/k215/README.md',F/'verification/k215/lean/README.md',F/'verification/k215/simplification/phase9/README.md',ROOT/'docs/incoming/README.md',P/'README.md']
link_docs=docs+[P/'source-proposal/README.md',P/'source-peer/review.md',P/'source-peer/producer-review.md']
links=[]
for p in link_docs:
 s=re.sub(r'```.*?```','',p.read_text(),flags=re.S)
 destinations=re.findall(r'\[[^\]\n]*\]\(([^\s)]+)(?:\s+"[^"\n]*")?\)',s)
 destinations+=re.findall(r'(?m)^\[[^\]\n]+\]:\s*(\S+)',s)
 for url in destinations:
  if re.match(r'[a-zA-Z][\w+.-]*:',url) or url.startswith('//'):continue
  raw=urllib.parse.unquote(url.strip('<>')).split('#',1)[0]
  target=(p.parent/raw).resolve() if raw else p
  links.append({'from':str(p.relative_to(ROOT)),'target':url,'resolved':str(target.relative_to(ROOT)) if target.is_relative_to(ROOT) else str(target),'exists':target.exists()})
missing=[x for x in links if not x['exists']]
expected=P/'lean/README.md'
assert all(ROOT/x['resolved']==expected for x in missing),missing
copy_map=js(P/'copy-map.json')
copy_records=[]
for row in copy_map['files']:
 source=Path(row['source']);target=ROOT/row['destination']
 assert h(source)==h(target)==row['sha256']
 assert target.stat().st_size==row['bytes']
 copy_records.append({'target':row['destination'],'sha256':h(target)})
assert len(copy_records)==61
adopt=js(P/'integration/adoption.json')
for row in adopt['files']:
 assert h(ROOT/row['target'])==h(Path(row['source']))==row['sha256']
old=P/'source-proposal/inputs/DominatedImplication.baseline.lean'
core=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DominatedImplication.lean'
adapter=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean'
assert h(adapter)==h(P/'source-proposal/inputs/DomRho8.adapter.lean')=='8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378'
oldtext,newtext=old.read_text(),core.read_text()
assert oldtext[oldtext.index('universe v'):oldtext.index('private theorem b1')]==newtext[newtext.index('universe v'):newtext.index('private theorem d1')]
for name in ['rho8_all','composition','lift_right']:
 pat=rf'(?m)^theorem {name}\b.*?:='
 assert re.search(pat,oldtext,re.S).group()==re.search(pat,newtext,re.S).group()
assert core.stat().st_size==14739 and old.stat().st_size==19378
assert len(newtext.splitlines())==330 and len(oldtext.splitlines())==381
assert adapter.stat().st_size==2680 and len(adapter.read_text().splitlines())==73
result=js(RUN/'result.json'); completed=js(RUN/'completed.json'); inv=js(RUN/'inventory.json')
assert result['status']=='PASS' and result['selected_project_modules']==197 and len(completed)==197
assert len(result['fresh_modules'])==8 and len(result['isolated_reused_modules'])==189 and not result['phase8_reused_modules']
assert h(RUN/'result.json')==adopt['compiled_full_result_sha256']
assert h(RUN/'inventory.json')==result['inventory_sha256'] and h(RUN/'completed.json')==result['completed_sha256']
ledger=js(P/'integration/canonical-review.json')['ledger']
assert set(ledger)==set(completed)
imports={r['module']:r['imports'] for r in inv['modules']}
def closure(m):
 seen=set()
 def rec(n):
  if n in seen or n=='Init':return
  seen.add(n)
  for c in imports[n]:rec(c)
 rec(m);return seen
assert len(closure('BusyBeaver.ZFC.KEndpoint215'))==192
assert len(set(completed)-closure('BusyBeaver.ZFC.KEndpoint215'))==5
source_records=[]
for name,row in ledger.items():
 assert h(ROOT/row['canonical'])==row['source']==completed[name]['source_sha256']
 assert h(Path(completed[name]['log']))==row['log']==completed[name]['log_sha256']
 assert completed[name]['status']=='PASS' and completed[name]['exit_code']==0 and not completed[name]['timed_out']
 source_records.append({'module':name,'source_sha256':row['source'],'log_sha256':row['log']})
site=[f'BusyBeaver.ZFC.KSites215Batch{i:03}' for i in range(9)]
for name in site:
 assert name in result['isolated_reused_modules'] and 'DominatedImplication' not in ' '.join(closure(name))
 assert '/k215-phase9-main/full-run2/' in completed[name]['log']
fresh_warnings=sum(completed[x]['warnings'] for x in result['fresh_modules'])
assert fresh_warnings==0
inherited_warnings=sum(completed[x]['warnings'] for x in result['isolated_reused_modules'])
assert inherited_warnings==21
assert len(result['audits'])==2 and sum(len(x['named_reports']) for x in result['audits'])==10
for a in result['audits']:
 assert a['status']=='PASS' and a['exit_code']==0 and not a['timed_out']
 assert h(Path(a['source']))==a['source_sha256']
 assert h(Path(a['log']))==a['log_sha256']
 log=Path(a['log']).read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for _,axioms in a['named_reports']:
  assert set(re.findall(r'[\w.]+',axioms))<= {'propext','Classical.choice','Quot.sound'}
core_reports=completed['BusyBeaver.ZFC.DominatedImplication']['reports']
assert len(core_reports)==3 and all(not axioms for _,axioms in core_reports)
for n in ['producer-execution.json','maintained-producer-check.json']:
 assert js(P/'integration'/n)['status'].startswith('PASS')
notes={'status':'PASS_READ_ONLY_DOCS_AND_COPY_BINDINGS_WITH_EXPECTED_PENDING_PACKET_LINK','docs':{str(p.relative_to(ROOT)):h(p) for p in docs},'local_link_occurrences':len(links),'local_link_missing_expected':missing,'links':links,'copy_map_files':len(copy_records),'copy_map_sha256':h(P/'copy-map.json'),'copied_files':copy_records,'adopted_paths':len(adopt['files']),'six_generic_public_declarations_unchanged':True,'adapter_exact':True,'old_core_bytes':19378,'new_core_bytes':14739,'saved_core_bytes':4639,'saved_core_percent_rounded':round(100*4639/19378,2),'saved_lines':51,'core_plus_adapter_bytes':17419,'core_plus_adapter_lines':403,'selected_modules':197,'endpoint_modules':192,'extra_decoder_modules':5,'fresh_modules':result['fresh_modules'],'reused_count':189,'inherited_site_batches':site,'fresh_warnings':fresh_warnings,'inherited_warnings':inherited_warnings,'audit_reports':10,'audit_warnings':0,'all_current_source_and_selected_log_pins_rehashed':source_records,'actual_full_result':h(RUN/'result.json'),'scope_exclusions':['No compiler or producer execution','No new independent rehash of compiled objects/toolchain','Pending execution archive and saved-reader publication are not accepted here','No PA theorem or new Rocq claim'],'authorship_disclosure':'Reviewer authored the generic core successor and producer; this review independently checks root-authored prose/copies/actual saved bindings, not another independent mathematical review.'}
(OUT/'checks.json').write_text(json.dumps(notes,indent=2)+'\n')
print(json.dumps({k:v for k,v in notes.items() if k not in ['links','copied_files','all_current_source_and_selected_log_pins_rehashed','docs']},indent=2))
