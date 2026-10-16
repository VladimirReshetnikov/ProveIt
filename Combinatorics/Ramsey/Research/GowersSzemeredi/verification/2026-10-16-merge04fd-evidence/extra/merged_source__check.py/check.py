import collections,difflib,hashlib,json,pathlib,re,subprocess
P=pathlib.Path(__file__).parent
BASE='68ad8d3';PARENT='cb7319ce84f72719fa92797c689591a29e547d40';INCOMING='04fd0fb36e46ff05373664236758eff99665bded'
ROOT=pathlib.Path('/home/codex/.codex/worktrees/9c9b/Proofs')
def git(*a):return subprocess.check_output(['git','-C',str(ROOT),*a])
def blob(c,p):return git('show',c+':'+p)
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(P/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def pin(p):return {'path':str(p),'sha256':sha(pathlib.Path(p).read_bytes())}
ns={};exec(pathlib.Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py').read_text(),ns)
ns['COMMAND']=re.compile(ns['COMMAND'].pattern.replace('|export|run_cmd','|export|alias|run_cmd'),re.M)
parse=ns['parse_declarations'];mask=ns['mask_comments']
assert git('rev-parse','HEAD').decode().strip()==PARENT
assert git('rev-parse','MERGE_HEAD').decode().strip()==INCOMING
resolution_path=pathlib.Path('/tmp/gowers-merge04fd-actual-resolution/resolution.json')
assert sha(resolution_path.read_bytes())=='fee223e6feb427bef423171fb823fa932ddebd1c0ea560d7e21060afe153358c'
resolution=json.loads(resolution_path.read_text());docs={x['path']:x for x in resolution['documentation_corrections']};conflict=resolution['conflict_file']
paths=git('diff','--name-only',BASE,INCOMING,'--','*.lean').decode().splitlines()
parent_changes=set(git('diff','--name-only',BASE,PARENT,'--','*.lean').decode().splitlines())
overlap=sorted(set(paths)&parent_changes)
assert len(paths)==70 and len(overlap)==4
rows=[];retained=[];removed=[];added=[];evidence=[]
ed=P/'evidence';ed.mkdir()
def apply_incoming_hunks_to_parent(path,parent):
    # Standard unified hunks are matched byte-exact with their context in the
    # already-published parent. No fuzzy matching or mutation of any source.
    diff=git('diff','--no-ext-diff','--unified=3',BASE,INCOMING,'--',path).decode().splitlines(True)
    chunks=[];cur=None
    for l in diff:
        if l.startswith('@@'):
            if cur is not None:chunks.append(cur)
            cur=[]
        elif cur is not None:
            if l[0:1] in [' ','-','+']:cur.append(l)
            elif l.startswith('\\'):raise AssertionError('Unexpected no-newline marker')
    if cur is not None:chunks.append(cur)
    out=parent
    for h in chunks:
        before=''.join(l[1:] for l in h if l[0] in ' -')
        after=''.join(l[1:] for l in h if l[0] in ' +')
        assert out.count(before)==1,(path,'nonunique or missing exact hunk',before[:100])
        out=out.replace(before,after,1)
    return out
for path in sorted(set(paths)|set(docs)):
    b=blob(BASE,path);q=blob(PARENT,path);i=blob(INCOMING,path);a=(ROOT/path).read_bytes()
    if path==conflict:
        assert a==q
        bd=parse(b.decode());qd=parse(q.decode());id=parse(i.decode())
        incoming_removed=sorted(set(bd)-set(id));incoming_changed=[n for n in set(bd)&set(id) if bd[n]['block']!=id[n]['block']]
        assert incoming_removed==['LeanProofs.GowersSzemeredi.context_zero_notMem_right']
        assert incoming_changed==['LeanProofs.GowersSzemeredi.context_additive_ext']
        assert all(n not in qd for n in incoming_removed+incoming_changed)
        expected=q
        method='Exact published parent retained; both incoming-edited declarations already absent there.'
    elif path in overlap:
        expected=apply_incoming_hunks_to_parent(path,q.decode()).encode()
        method='All exact incoming unified hunks applied in memory to the published parent, with unique full context.'
    else:
        assert q==b,(path,'unexpected additional local source difference')
        expected=i;method='Exact incoming whole-file bytes.'
    pre_comment=expected
    if path in docs:
        x=docs[path];old=x['old_text'].encode();new=x['replacement'].encode()
        assert expected.count(old)==1
        expected=expected.replace(old,new,1)
        assert sha(pre_comment)==x['before_sha256'] and sha(expected)==x['after_sha256']
        assert re.sub(r'\s+',' ',mask(pre_comment.decode())).strip()==re.sub(r'\s+',' ',mask(expected.decode())).strip()
        method+=' Then exact reviewed comment replacement only.'
    assert a==expected,(path,'merged bytes differ from independently reconstructed result')
    assert ns['imports'](q.decode())==ns['imports'](a.decode())
    before=parse(q.decode());after=parse(a.decode())
    for n,d in before.items():
        if n not in after:removed.append({'file':path,'name':n,'kind':d['kind'],'private':'private ' in d['header']})
        else:
            e=after[n];assert d['header']==e['header'] and d['context']==e['context'],(path,n)
            retained.append({'file':path,'name':n,'header_sha256':sha(d['header'].encode()),'context':d['context'],'whole_block_exact':d['block']==e['block'],'before_block_sha256':sha(d['block'].encode()),'after_block_sha256':sha(e['block'].encode())})
    added.extend({'file':path,'name':n} for n in after if n not in before)
    rows.append({'file':path,'baseline_sha256':sha(b),'published_parent_sha256':sha(q),'incoming_sha256':sha(i),'merged_sha256':sha(a),'parent_lines':len(q.splitlines()),'merged_lines':len(a.splitlines()),'line_delta':len(a.splitlines())-len(q.splitlines()),'changed_from_parent':a!=q,'reconstruction':method})
    if path in overlap or path in docs:
        f=ed/(pathlib.Path(path).name+'.parent-to-merged.diff');f.write_text(''.join(difflib.unified_diff(q.decode().splitlines(True),a.decode().splitlines(True),fromfile='published/'+path,tofile='merged/'+path)));evidence.append(pin(f))
assert not added
actual_changed=set(git('diff','--name-only',PARENT,'--','Combinatorics/Ramsey/Lean').decode().splitlines())
expected_changed={r['file'] for r in rows if r['changed_from_parent']}
assert actual_changed==expected_changed
assert len(actual_changed)==70
assert sum(r['line_delta'] for r in rows)==-1386
save('source-rows.json',rows);save('retained-declarations.json',retained);save('removed-declarations.json',removed)
finals=[]
for n in ['Final.lean','Proofs18Final.lean','Proofs18CoverFejerAllDegrees.lean','Proofs18GenericSzemeredi.lean','Definitions.lean','Sections17_18.lean','Proofs18CoverVanDerWaerden.lean','FinalProofSimplificationAudit.lean']:
    path='Combinatorics/Ramsey/Lean/GowersSzemeredi/'+n
    q=blob(PARENT,path);i=blob(INCOMING,path);a=(ROOT/path).read_bytes();assert q==i==a
    finals.append({'file':path,'sha256':sha(a),'published_parent_incoming_and_merged_exact':True})
save('final-facing-inputs.json',finals)
# Re-read every inspected source after all comparisons; inventory generation
# is explicitly outside this report and may proceed independently.
for r in rows:assert sha((ROOT/r['file']).read_bytes())==r['merged_sha256']
assert git('rev-parse','HEAD').decode().strip()==PARENT
assert git('rev-parse','MERGE_HEAD').decode().strip()==INCOMING
report={'status':'PASS_SOURCE_ONLY','published_parent':PARENT,'incoming':INCOMING,'merge_commit':None,'scope':'Actual uncommitted merged production Lean source only; inventory generation, docs archive and native checks outside scope.','independent_source_reconstruction':{'incoming_Lean_owners':70,'current_parent_overlaps':overlap,'examined_owners_including_documentation_and_unchanged_conflict':len(rows),'actually_changed_Lean_owners':len(actual_changed),'actual_source_line_delta':sum(r['line_delta'] for r in rows),'arithmetic':'Incoming −1390; obsolete incoming −3-line edit already absent in published parent, giving +3; QuantitativeSzemeredi comment adds 1 line. Total −1386.','all_incoming_hunks_preserved_except_obsolete_block':True,'all_other_parent_edits_preserved':True,'imports_unchanged':True},'conflict':{'file':conflict,'merged_equals_published_parent':True,'obsolete_incoming_removed_name':'context_zero_notMem_right','obsolete_incoming_changed_name':'context_additive_ext','these_two_names_already_absent_in_parent':True,'canonical_shared_caller_retained':'lemma134_additive_ext'},'comment_only_adjustments':resolution['documentation_corrections'],'interfaces':{'retained_normal_declarations':len(retained),'retained_complete_headers_and_contexts_exact':True,'unchanged_complete_blocks':sum(x['whole_block_exact'] for x in retained),'changed_blocks':sum(not x['whole_block_exact'] for x in retained),'removed_names':len(removed),'removed_private':sum(x['private'] for x in removed),'removed_public':sum(not x['private'] for x in removed),'new_names':0,'qualification':'Intentional reviewed intermediate-name removals. This is not a claim that all old intermediate exports remain available.'},'final_theorem_threshold_AP_and_axiom_audit_source':'All eight listed files exactly match both parents and merged bytes.','byte_stability':'All inspected live Lean source hashes and HEAD/MERGE_HEAD were reread at completion.','native_status':'Not run for the merge. Prior a879 passed 572/1915/351 and publication cb7319 are historical; new merged-source validation remains required.','inputs':[pin(resolution_path),pin(pathlib.Path('/tmp/gowers-incoming04fd-source-api-independent-review/report.json')),pin(pathlib.Path('/tmp/gowers-incoming04fd-source-api-independent-review/freeze.json')),pin(pathlib.Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py'))],'no_mutations':'Only this new /tmp review directory written. No source/index/HEAD/refs/cache/native operation or generator invocation.'}
save('report.json',report)
print(json.dumps(report,ensure_ascii=False,indent=2))
