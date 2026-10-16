"""Static preparation only: write new /tmp archive-helper text and source metadata."""
import ast,datetime,difflib,functools,hashlib,json,pathlib,subprocess
P=pathlib.Path(__file__).parent
ROOT=pathlib.Path('/home/codex/.codex/worktrees/9c9b/Proofs')
OLD=pathlib.Path('/tmp/gowers-merge68ad-post-native-tools')
NATIVE=pathlib.Path('/tmp/gowers-merge04fd-native-tools')
SOURCE='aca2a610c9b3722e66e8cf415bca374e9f28cb1a'
PARENT='cb7319ce84f72719fa92797c689591a29e547d40'
INCOMING='04fd0fb36e46ff05373664236758eff99665bded'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(pathlib.Path(p).read_text())
def pin(p,expected=None):
    p=pathlib.Path(p).resolve();h=sha(p)
    if expected:assert h==expected,(str(p),h)
    return {'path':str(p),'sha256':h}
def save(name,value):
    target=P/name;assert not target.exists()
    target.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def git(*a):return subprocess.check_output(['git','-C',str(ROOT),*a])
assert git('rev-parse','HEAD').decode().strip()==SOURCE
assert git('show','-s','--format=%P',SOURCE).decode().strip().split()==[PARENT,INCOMING]
old_pin=pin(OLD/'archive.py','71c60153a33e2677fc15dd81c675866b51eb0d37271f66346af1eaaae574573b')
old=(OLD/'archive.py').read_text()
replacements=[('/tmp/gowers-merge68ad-native-tools',str(NATIVE)),('a87906dc3960604bc3a0b423868d392b43ba85c0',SOURCE)]
new=old
for a,b in replacements:assert new.count(a)==1;new=new.replace(a,b)
assert len(old.splitlines())==len(new.splitlines())
ast.parse(new) # No module execution, imports, or native helper invocation.
(P/'archive.py').write_text(new)
(P/'changes.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(OLD/'archive.py'),tofile=str(P/'archive.py'))))
toolpins={}
for n,h in {'common.py':'4c71aedd3ec630046fd5dd5d205e250893c93bb0b1f1d2b0faf69bfe89e07328','capture.py':'8463cc8e288255e12fd9ad777f8a2fe7f0a75aa6cbf888f423129a112f6cecd2','run.py':'bf1aa169ed14fc098fd20c57a93a8c9904718bfc2b2648997384a3effd61e83a'}.items():
    pin(NATIVE/n,h);assert (NATIVE/n).read_bytes()==(pathlib.Path('/tmp/gowers-merge68ad-native-tools')/n).read_bytes();toolpins[str(NATIVE/n)]=h
snapshot_pin=pin('/tmp/gowers-merge04fd-aca2-source-snapshot.json','d33fe17ef5f2f59c3825878f370fbb10b72500e0da1b893b2666bf937480c730')
snapshot=load(snapshot_pin['path']);assert snapshot['source_commit']==SOURCE and snapshot['tools']==toolpins
assert len(snapshot['source_hashes'])==1971
measurement_pin=pin(NATIVE/'measurement.json','6853f91e7577e100676651eee73d251d1e76796a4b0f73650c7f6b120464dd2d')
native_freeze_pin=pin(NATIVE/'freeze.json','adfb93ef7c4874af5bda29f92ab64c30488156b2bd2babb06be8a4e104cdd886')
for n,h in load(native_freeze_pin['path']).items():pin(NATIVE/n,h)
m=load(measurement_pin['path']);rows=load(NATIVE/'source-rows.json');changed=load(NATIVE/'changed-owners.json');modes=load(NATIVE/'mode-closures.json');graph=load(NATIVE/'fullgraph-imports.json')
assert len(changed)==70 and sum(r['source_lines_delta'] for r in changed)==-1386
assert all(r['imports_before']==r['imports_current'] for r in changed)
for r in changed:
    live=(ROOT/r['path']).read_bytes();assert hashlib.sha256(live).hexdigest()==r['current_sha256']==snapshot['source_hashes'][r['path']]
    assert live==git('show',SOURCE+':'+r['path'])
    assert hashlib.sha256(git('show',PARENT+':'+r['path'])).hexdigest()==r['baseline_sha256']
review_pin=pin('/tmp/gowers-merge04fd-actual-source-independent-review/report.json','528a9b51b5d3e5fc47e62044992a02355b8ed3a53e4b8e3f68a102f0eb48b67d')
review=load(review_pin['path']);assert review['published_parent']==PARENT and review['incoming']==INCOMING
resolution_pin=pin('/tmp/gowers-merge04fd-actual-resolution/resolution.json','fee223e6feb427bef423171fb823fa932ddebd1c0ea560d7e21060afe153358c')
resolution=load(resolution_pin['path'])
for r in load('/tmp/gowers-merge04fd-actual-source-independent-review/source-rows.json'):
    assert sha(ROOT/r['file'])==r['merged_sha256']
inv_pin=pin('/tmp/gowers-merge04fd-inventory-actual/comparison.json','42d4e89374878db9728bdf4f43e1ba98195a5fa98250106d82ff4cd40636d432')
inv=load(inv_pin['path']);ip='Combinatorics/Ramsey/gowers-proof-status.json';ih='d705215fb1fe2edb737ff21e464913e0823d6c5b682de168eddbc6146d0ffadd'
assert sha(ROOT/ip)==snapshot['source_hashes'][ip]==inv['normalized_sha256']==ih
assert (ROOT/ip).read_bytes()==git('show',SOURCE+':'+ip)
@functools.lru_cache(None)
def closure(n):return frozenset([n]).union(*(closure(x) for x in graph[n] if x in graph))
routes={}
for mode,spec in modes.items():
    mods=set(spec['modules']);recomputed=set().union(*(closure(n) for n in spec['roots']));assert mods==recomputed
    routes[mode]={'root_count':len(spec['roots']),'modules':len(mods),'source_lines':sum(rows[n]['source_lines'] for n in mods)}
    assert routes[mode]['modules']==m['mode_counts'][mode]['module_count']
    assert routes[mode]['source_lines']==m['mode_counts'][mode]['source_lines']
for name,root in [('original_final','GowersSzemeredi.Final'),('stronger_final','GowersSzemeredi.Proofs18CoverFejerAllDegrees')]:
    mods=closure(root);routes[name]={'root':root,'modules':len(mods),'source_lines':sum(rows[n]['source_lines'] for n in mods)}
union=set().union(*(set(s['modules']) for s in modes.values()));routes['union']={'modules':len(union),'source_lines':sum(rows[n]['source_lines'] for n in union)}
assert len(union)==1964
prior_index_path=ROOT/'Combinatorics/Ramsey/Research/GowersSzemeredi/verification/2026-10-16-merge68ad-evidence/index.json'
priorpin=pin(prior_index_path,'8578f6772c9d6054b677c271112e3c4a0fc220e17284cf8fe38583bd88427926');prior=load(prior_index_path)
assert prior['source_commit']=='a87906dc3960604bc3a0b423868d392b43ba85c0' and [r['terminal_exit'] for r in prior['actual_invocations']]==[0,0,0]
assert prior_index_path.read_bytes()==git('show',PARENT+':'+str(prior_index_path.relative_to(ROOT)))
interfaces=review['interfaces']
ledger={'status':'Committed merged source ledger; actual native outcomes must be supplied separately','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':SOURCE,'parents':[PARENT,INCOMING],'comparison_commit':PARENT,'previous_verified_source':'a87906dc3960604bc3a0b423868d392b43ba85c0','previous_published_checkpoint':PARENT,'previous_archive_index_historical_only':priorpin,'snapshot':snapshot_pin,'changed_production_owners':changed,'global_source_line_delta':-1386,'declaration_preservation':{**interfaces,'inspection_scope':'71 owners inspected, including the unchanged resolved conflict owner; 70 owners actually changed from the published parent.'},'incoming_count_qualification':'Incoming 68ad→04fd removes 130 names (87 dead +43 inlined); actual cb→aca2 removes129 because context_zero_notMem_right was already absent. 76 public intermediate names are intentionally removed; no current repository code references remain, but external users may need updates.','imports_and_retained_headers_unchanged':True,'merge_conflicts':[resolution],'actual_source_review':review_pin,'incoming_source_review':pin('/tmp/gowers-incoming04fd-source-api-independent-review/report.json','971f86251e8610d01c24dbc8d1f11945e3a805b47d093312846b1b11a9068b44'),'final_statement_protection':load('/tmp/gowers-merge04fd-actual-source-independent-review/final-facing-inputs.json'),'routes':routes,'inventory':{'path':ip,'sha256':ih,'ordered_rows':inv['row_count'],'companion_occurrences':inv['companion_occurrences'],'whole_object_permutations':inv['whole_object_permutations'],'line_leaf_changes':len(inv['location_leaf_changes']),'comparison':inv_pin},'validation_scope':{'root_counts':[1,65,18],'module_counts':[572,1915,351],'actual_commands_required':3,'per_root_metadata_rows':84,'union_modules':1964,'protected_inputs':1971,'full_graph_modules':6021,'dependent_consumers':m['dependent_consumers_union'],'covered_consumers':m['covered_consumers'],'excluded_facades':m['excluded_facades']},'native_measurement':measurement_pin,'native_tools_freeze':native_freeze_pin,'historical_retention_planned':False,'full_native_success_claimed':False,'actual_native_receipts':{'core':None,'shared':None,'supplemental':None},'actual_archive':None,'proposed_repository_archive':'Combinatorics/Ramsey/Research/GowersSzemeredi/verification/2026-10-16-merge04fd-evidence','limitations':['Source-only preparation while merged-source core is running; this ledger asserts no completed aca2 native command.','The passed a879 archive and publication cb7319 are historical and do not validate aca2.','84 own-root rows describe three commands, not 84 independent command outcomes.','Inventory has120 ordered rows and544 companion occurrences; coverage is not a certificate of fidelity to every original paper statement.','Prospective NEXT2111, further source simplifications and progression-route drafts remain separate, unapplied and excluded from this checkpoint.','Artifact freshness/stability follows existing checker input mtimes and artifact mtime/size, not artifact-content hashes.']}
save('source-ledger.json',ledger)
preparation={'status':'SOURCE-ONLY PREPARATION; ARCHIVE HELPER NOT EXECUTED','source_commit':SOURCE,'previous_archive_helper':old_pin,'archive_changes':[{'old':a,'new':b,'occurrences':1} for a,b in replacements],'algorithms_otherwise_byte_exact':True,'archive_sha256':sha(P/'archive.py'),'source_ledger_sha256':sha(P/'source-ledger.json'),'snapshot':snapshot_pin,'native_helper_toolpins':toolpins,'native_helpers_byte_exact_to_prior':True,'native_measurement':measurement_pin,'native_tools_freeze':native_freeze_pin,'root_routes':routes,'all_changed_source_hashes_match_commit_and_snapshot':True,'actual_source_review':review_pin,'actual_inventory_comparison':inv_pin,'native_validation_completed':False,'archiving_executed':False}
save('preparation.json',preparation)
print(json.dumps({'archive_sha256':preparation['archive_sha256'],'source_ledger_sha256':preparation['source_ledger_sha256'],'routes':routes},indent=2))
