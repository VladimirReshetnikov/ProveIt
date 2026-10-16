import collections, hashlib, json, pathlib, re, subprocess

P=pathlib.Path(__file__).parent
G='/tmp/gowers-origin04fd-source-review.git'
BASE='68ad8d391';TIP='04fd0fb36e46ff05373664236758eff99665bded'
def git(*a):return subprocess.check_output(['git','--git-dir='+G,*a])
BASE=git('rev-parse','68ad8d3').decode().strip()
def sha(x):return hashlib.sha256(x).hexdigest()
def save(n,j):(P/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def blob(c,p):return git('show',c+':'+p)
ns={};exec(pathlib.Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py').read_text(),ns)
mask=ns['mask_comments'];rows=json.loads((P/'source-rows.json').read_text());removed=json.loads((P/'removed-declarations.json').read_text());ret=json.loads((P/'retained-declarations.json').read_text())
prefix='Combinatorics/Ramsey/Lean/GowersSzemeredi/'
finals=[]
for name in ['Final.lean','Proofs18Final.lean','Proofs18CoverFejerAllDegrees.lean','Proofs18GenericSzemeredi.lean','Definitions.lean','Sections17_18.lean','Proofs18CoverVanDerWaerden.lean','FinalProofSimplificationAudit.lean']:
    path=prefix+name;b=blob(BASE,path);a=blob(TIP,path);live=pathlib.Path(path).read_bytes();assert a==b==live
    finals.append({'file':path,'sha256':sha(a),'incoming_equals_baseline_equals_current_a879':True})
save('final-facing-inputs.json',finals)
leaves={d['name'].rsplit('.',1)[1] for d in removed}
paths=git('ls-tree','-r','--name-only',TIP).decode().splitlines()
lean=[p for p in paths if p.endswith('.lean')]
hits=(P/'remaining-raw-Lean-name-hits.txt').read_text().splitlines()
codehits=[]
for hit in hits:
    _,path,line,text=hit.split(':',3);src=blob(TIP,path).decode();code=mask(src).splitlines()[int(line)-1]
    if any(re.search(r'(?<![\w\'])'+re.escape(n)+r'(?![\w\'])',code) for n in leaves):codehits.append(hit)
assert not codehits
removed_attrs=[d['name'] for d in removed if '@[' in d['header'] or d['kind']=='instance']
assert not removed_attrs
aliases=[]
for p in rows:
    a=mask(blob(BASE,p).decode());b=mask(blob(TIP,p).decode())
    pat=r'^\s*(?:@\[[^\n]+\]\s*)?(?:private\s+|protected\s+)?alias\s+[^\n]+'
    aa=re.findall(pat,a,re.M);bb=re.findall(pat,b,re.M);assert aa==bb
    if aa:aliases.append({'file':p,'aliases':aa})
save('remaining-references.json',{'tracked_Lean_files_scanned':len(lean),'configured_Ramsey_Lean_files':sum(p.startswith('Combinatorics/Ramsey/Lean/') for p in lean),'configured_library_Lean_files':sum(p.startswith('lib/openai-math/') for p in lean),'search':'All 130 removed full-name leaf tokens, whole-word fixed string git grep over every tracked *.lean at exact incoming commit, then nested-comment/string masking and manual examination of both hits. Includes qualified/method suffix forms and audit quoted names.','raw_hits':hits,'code_or_audit_hits':codehits,'removed_instances_or_attached_attributes':removed_attrs,'unchanged_alias_commands':aliases})
catpath='Combinatorics/Ramsey/gowers-proof-status.json';cb=blob(BASE,catpath);ca=blob(TIP,catpath);assert cb==ca;cat=json.loads(ca)
loc=[];entries=[];missing=[]
def walk(x,path):
    if isinstance(x,dict):
        if 'name' in x and 'file' in x and 'line' in x:entries.append((path,x))
        for k,v in x.items():walk(v,path+[k])
    elif isinstance(x,list):
        for i,v in enumerate(x):walk(v,path+[i])
walk(cat,[])
for path,x in entries:
    assert x['name'] not in leaves
    if x['file'] not in rows:continue
    def find(c):
        s=mask(blob(c,x['file']).decode());pat=r'^(?:@\[[^\n]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|alias)\s+'+re.escape(x['name'])+r'(?![\w\'])'
        ms=list(re.finditer(pat,s,re.M));assert len(ms)==1,(x,ms)
        return s[:ms[0].start()].count('\n')+1
    b=find(BASE);a=find(TIP)
    if b!=a:loc.append({'catalogue_path':path+['line'],'name':x['name'],'file':x['file'],'stored_line':x['line'],'actual_baseline_line':b,'actual_incoming_line':a})
save('catalogue-impact.json',{'inventory_sha256':sha(ca),'inventory_unchanged_between_commits':True,'rows':len(cat['statements']),'companion_occurrences':len(entries),'removed_catalogue_names':[],'source_location_changes':loc,'qualification':'Source-based before/after line comparison only; incoming JSON was not regenerated. This is not an actual generator or normalized inventory result. Earlier baseline metadata may itself have stale locations.'})
E=P/'evidence';E.mkdir(exist_ok=True)
for n in ['Proofs16FaceLifts.lean','Proofs18QuantitativeSzemeredi.lean','Proofs18AffineTransfer.lean']:(E/n).write_bytes(blob(TIP,prefix+n))
for n in ['dead_decls.py','delete_decls.py','inline_short.py','inline_have.py','prune_haves.py']:
    (E/(n+'.txt')).write_bytes(blob(TIP,'Combinatorics/Ramsey/Research/GowersSzemeredi/fejer-generators/'+n))
(E/'commit-messages.txt').write_bytes(git('log','--format=fuller',BASE+'..'+TIP))
(E/'research-notes.diff').write_bytes(git('diff',BASE+'..'+TIP,'--','Combinatorics/Ramsey/Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md'))
docs=[{'file':prefix+'Proofs16FaceLifts.lean','incoming_line':18,'old_text':'* `vertexFace` and `translatedVertex_eq_face`: when `e i = false`, the vertex\n  map is a function of `dropAt (castSucc i) z`.','suggested_text':'* `exists_false_of_ne_one`: every vertex other than the all-ones vertex\n  has a coordinate `i` with `e i = false`.','reason':'The named face definition/theorem are deleted; the replacement describes the surviving final theorem of this owner. Deleting this obsolete bullet is an even smaller alternative.'},{'file':prefix+'Proofs18QuantitativeSzemeredi.lean','incoming_line':30,'old_text':'density increment: `ModAP.density_cyclic_pullback` records the ambient-density\nloss when the progression indices are embedded in a larger cyclic group.','suggested_text':'density increment: `ModAP.card_cyclic_pullback` preserves cardinality when\nthe progression indices are embedded in a larger cyclic group; ambient\ndensity still uses the new modulus.','reason':'The density wrapper is deleted; the surviving cardinality theorem in Proofs18AffineTransfer (line 71) does not itself assert a normalized-density identity.'}]
save('documentation-followups.json',docs)
s=json.loads((P/'summary.provisional.json').read_text())
report={'status':'PASS_WITH_NONBLOCKING_DOCUMENTATION_FINDINGS','review_kind':'Independent incoming source/API review only; no native execution or merged-source acceptance','baseline':BASE,'incoming':TIP,'bare_repository':G,'current_worktree_anchor':'a87906dc3960604bc3a0b423868d392b43ba85c0','summary':s,'retained_statement_checks':{'retained_normal_declarations':len(ret),'unchanged_complete_blocks':sum(x['block_exact'] for x in ret),'rewritten_existing_blocks':dict(collections.Counter(x['kind'] for x in ret if not x['block_exact'])),'header_and_binder_context_changes':[],'new_declarations':[],'aliases_unchanged':aliases,'parser_scope':'Known multiline Lean command scanner; retained byte-identical complete blocks establish preservation even for nontrivial header syntax. All 37 changed blocks were read directly, with complete header/body boundaries and inline substitution checked. No generic Lean-parser claim.'},'imports_and_registration':{'all_70_import_lists_exact':True,'no_Lean_modules_added_or_removed':True,'import_graph_unchanged':True,'removed_instances':0,'removed_attached_attributes':0,'surviving_attribute_and_alias_commands_exact':True,'only_removed_nondeclaration_command':'set_option exponentiation.threshold 512 in, attached solely to the removed final theorem fejerCubicTwistedThreshold_le_double_exp; no subsequent declaration inherits it.'},'mathematical_review':{'finding':None,'scope':'All 43 single-use substitutions inspected through the 37 changed retained declaration bodies. They preserve original statements and instantiate the same proof terms/tactics; no new hypotheses, numerical constants, axioms, sorry or native_decide introduced. Both modified definitions change only embedded proof fields. Finite/empty cases and positivity/NeZero/prime hypotheses remain as in retained headers.','limits':'Larger ambient tactic contexts, typeclass elaboration and declaration heartbeat behavior still require actual merged-source native checking. No concrete source-level mismatch was found.'},'public_API':{'removed_total':130,'removed_private':54,'removed_public':76,'dead_phase_public_removals':65,'inlined_phase_public_removals':11,'qualification':'This is intentionally not export-preserving for all intermediate names. Current tracked repo code and named axiom audits have no remaining references, but external callers of the 76 public names will need changes.'},'references':'remaining-references.json','final_facing_inputs':'final-facing-inputs.json','catalogue':'catalogue-impact.json','catalogue_summary':{'rows':120,'companion_occurrences':len(entries),'removed_names':0,'occurrences_with_source_line_shift':len(loc),'needs_actual_postmerge_regeneration':True},'documentation_findings':docs,'author_build_claim':{'claimed':'Each modified module rebuilt with heal_build SUCCESS, no stale olean, zero duplicate names, and a Proofs18Final-route stub axiom check. Per-candidate scripts require a successful scratch Lean elaboration against existing built dependencies.','verified_here':'Exact commit prose and script source only. The four generator scripts and inherited prune_haves.py were read as data, never imported or executed.','limits':'No independently bound command receipt/log or source/artifact manifest for that author run was provided by these four commits. Windows-specific paths, cache-dependent scratch checks, and a final-route stub are not substitutes for the actual merged-source core/shared/supplemental chain, full selected roots, artifact freshness and named audits. Current a879 native result cannot validate future 04fd merged sources.'},'merge_context':{'root_preview_path':'/tmp/gowers-origin04fd-merge-tree-preview.txt','root_preview_sha256':'b47693f2626eef91211d1094eb8dcccfea469e302a19441f6426f9a6cbffbd24','attribution':'Root-authored preview only; no merge or composition performed by this review.','known_conflict':'PreparedFrequencyGraph: preserve local deletion of obsolete contextRestrictionLeft/Right and context_additive_ext; incoming merely inlines a helper within that already removed block. Other current-source overlaps are disjoint body edits per root preview and direct comparison.'},'actions':'Read-only Git object and source inspection; wrote only this new /tmp evidence package. No repository/Git refs/cache/native or generator changes.'}
save('report.json',report)
print(json.dumps({'status':report['status'],'summary':s,'catalogue_shift_occurrences':len(loc),'alias_commands':len(aliases),'report_sha256':sha((P/'report.json').read_bytes())},indent=2))
