#!/usr/bin/env python3
"""Offline Git tree/blob/SHA256/coverage/delta replay; never invokes Lean or network."""
import hashlib,json,pathlib,sys
BASE=pathlib.Path(__file__).resolve().parents[1];P=BASE/'provenance';bad=[];counts={};WITH_ARCHIVES='--with-archives' in sys.argv;archive_status=[]
def read(n): return json.loads((P/n).read_text())
def check(ok,why):
    if not ok:bad.append(why)
def gitsha(kind,data):return hashlib.sha1(kind.encode()+b' '+str(len(data)).encode()+b'\0'+data).hexdigest()
def tree_hash(rows):
    rows=sorted(rows,key=lambda e:(e['path']+('/' if e['type']=='tree' else '')).encode())
    data=b''.join((e['mode'].lstrip('0')+' '+e['path']).encode()+b'\0'+bytes.fromhex(e['sha']) for e in rows)
    return gitsha('tree',data)
names=['root_tree','computability_tree','dc_root_tree','Lean_tree','research_tree','reviews_tree','docs_tree','incoming_tree','Logic_tree','FirstOrder_tree','FirstOrder_Lean_root_tree','FirstOrder_modules_tree','SetTheory_tree','BoundedConsistency_tree','BoundedConsistency_Lean_root_tree','BoundedZFC_tree','HilbertTenthProblem_tree','H10_Lean_tree','BusyBeaver_tree','BusyBeaver_Lean_root_tree','BusyBeaver_modules_tree','BusyBeaver_ZFC_tree']
names += [prefix+n for prefix in ['previous_','closing_'] for n in ['root_tree','computability_tree','dc_root_tree','Lean_tree']]
trees={n:read(n+'.json') for n in names}
for name,d in trees.items():
    check(d.get('truncated') is False,[name,'missing complete-tree assertion'])
    dirs={'':[]};entries={e['path']:e for e in d['tree']}
    for e in d['tree']:
        parent,_,leaf=e['path'].rpartition('/');dirs.setdefault(parent,[]).append(dict(e,path=leaf))
    expected=d['sha']
    if name in ['root_tree','previous_root_tree','closing_root_tree']:
        head=read({'root_tree':'HEAD_binding.json','previous_root_tree':'previous_HEAD_binding.json','closing_root_tree':'closing_HEAD_binding.json'}[name]);expected=head['commit']['tree']['sha']
    check(tree_hash(dirs[''])==expected,[name,'root tree mismatch'])
    for path,rows in dirs.items():
        if path:check(entries.get(path,{}).get('sha')==tree_hash(rows),[name,path,'nested tree mismatch'])
def edge(parent,path,child):
    e=next((x for x in trees[parent]['tree'] if x['path']==path),{});check(e.get('sha')==trees[child]['sha'],[parent,path,child,'ancestor edge mismatch'])
for prefix in ['','previous_','closing_']:
    for a,b,c in [('root_tree','Computability','computability_tree'),('computability_tree','DiophantineConsistency','dc_root_tree'),('dc_root_tree','Lean','Lean_tree')]:edge(prefix+a,b,prefix+c)
for args in [('dc_root_tree','research','research_tree'),('dc_root_tree','reviews','reviews_tree'),('root_tree','docs','docs_tree'),('docs_tree','incoming','incoming_tree'),('root_tree','Logic','Logic_tree'),('Logic_tree','FirstOrder','FirstOrder_tree'),('FirstOrder_tree','Lean','FirstOrder_Lean_root_tree'),('FirstOrder_Lean_root_tree','FirstOrder','FirstOrder_modules_tree'),('root_tree','SetTheory','SetTheory_tree'),('SetTheory_tree','BoundedConsistency','BoundedConsistency_tree'),('BoundedConsistency_tree','Lean','BoundedConsistency_Lean_root_tree'),('BoundedConsistency_Lean_root_tree','BoundedZFCConsistency','BoundedZFC_tree'),('computability_tree','HilbertTenthProblem','HilbertTenthProblem_tree'),('HilbertTenthProblem_tree','Lean','H10_Lean_tree'),('computability_tree','BusyBeaver','BusyBeaver_tree'),('BusyBeaver_tree','Lean','BusyBeaver_Lean_root_tree'),('BusyBeaver_Lean_root_tree','BusyBeaver','BusyBeaver_modules_tree'),('BusyBeaver_modules_tree','ZFC','BusyBeaver_ZFC_tree')]:edge(*args)
def prefixed(name,prefix):return {prefix+e['path']:e['sha'] for e in trees[name]['tree'] if e['type']=='blob'}
pre='Computability/DiophantineConsistency/Lean/'
maps=[('root_tree',''),('dc_root_tree','Computability/DiophantineConsistency/'),('Lean_tree',pre),('research_tree','Computability/DiophantineConsistency/research/'),('reviews_tree','Computability/DiophantineConsistency/reviews/'),('H10_Lean_tree','Computability/HilbertTenthProblem/Lean/'),('BusyBeaver_modules_tree','Computability/BusyBeaver/Lean/BusyBeaver/'),('BusyBeaver_ZFC_tree','Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'),('BoundedZFC_tree','SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/'),('FirstOrder_modules_tree','Logic/FirstOrder/Lean/FirstOrder/'),('incoming_tree','docs/incoming/')]
bindings={}
for name,prefix in maps:bindings.update(prefixed(name,prefix))
for filename,folder,key in [('source_manifest.json','sources','sources'),('dependency_manifest.json','dependencies','sources'),('comparison_manifest.json','comparison_sources','sources'),('review_manifest.json','provenance/review_sources','sources'),('incoming_manifest.json','provenance/incoming_artifacts','files')]:
    m=read(filename);counts[folder]=len(m[key])
    for e in m[key]:
        local=e.get('local_path',folder+'/'+e['path']);f=BASE/local
        if filename=='incoming_manifest.json' and e['path'].endswith('.zip'):
            check(bindings.get(e['path'])==e['sha'],[local,'archive Git blob/tree binding mismatch'])
            check(len(e.get('sha256',''))==64,[local,'missing saved archive SHA256'])
            archive_status.append({'path':local,'git_blob':e['sha'],'saved_sha256':e['sha256'],'bytes_replayed':WITH_ARCHIVES,'status':'byte replay requested' if WITH_ARCHIVES else 'archive bytes not bundled in curated delivery; not replayed; saved Git blob bound to tree, SHA256 recorded only'})
            if not WITH_ARCHIVES:counts[folder]-=1;continue
        if not f.is_file():bad.append([local,'missing']);continue
        d=f.read_bytes();check(gitsha('blob',d)==e['sha'],[local,'blob SHA mismatch']);check(hashlib.sha256(d).hexdigest()==e['sha256'],[local,'SHA256 mismatch'])
        if 'line_count' in e:check(len(d.splitlines())==e['line_count'],[local,'line count mismatch'])
        if filename=='comparison_manifest.json':
            old=prefixed('previous_Lean_tree' if e['snapshot']=='round5_source' else 'closing_Lean_tree',pre);check(old.get(e['path'])==e['sha'],[local,'old tree binding mismatch'])
        else:check(bindings.get(e['path'])==e['sha'],[local,'pinned tree binding mismatch'])
active=prefixed('Lean_tree',pre);materialized={e['path']:e['sha'] for e in read('source_manifest.json')['sources'] if e['path'].startswith(pre)}
check(active==materialized,'active Lean subtree coverage mismatch')
for filename,treename,label in [('active_tree_delta.json','previous_Lean_tree','round5_source'),('since_closing_delta.json','closing_Lean_tree','round5_closing')]:
    old={e['path']:e['sha'] for e in trees[treename]['tree'] if e['type']=='blob'};new={e['path']:e['sha'] for e in trees['Lean_tree']['tree'] if e['type']=='blob'}
    actual={k:(old.get(k),new.get(k)) for k in old.keys()|new.keys() if old.get(k)!=new.get(k)};saved=read(filename)
    check(actual=={e['path']:(e['old_sha'],e['new_sha']) for e in saved['files']},[filename,'delta mismatch'])
    for e in saved['files']:
        for folder,key in [('comparison_sources/'+label,'old_lines'),('sources','new_lines')]:
            f=BASE/folder/pre/e['path'];n=len(f.read_bytes().splitlines()) if f.exists() else 0;check(n==e[key],[filename,e['path'],key,'line count mismatch'])
history={e['sha']:e for e in read('history_compact.json')}
def ancestors(start):
    seen=set();todo=[start]
    while todo:
        x=todo.pop()
        if x in seen:continue
        seen.add(x)
        if x in history:todo.extend(e['sha'] for e in history[x]['parents'])
    return seen
for filename in ['commit_timeline.json','since_closing_commit_timeline.json']:
    t=read(filename);actual=ancestors(t['head'])-ancestors(t['base'])
    check(actual=={e['sha'] for e in t['commits']},[filename,'parent graph membership mismatch']);check(len(actual)==t['commit_count']==t['ahead_by'],[filename,'commit count mismatch'])
research={e['path']:e['sha'] for e in trees['research_tree']['tree']}
for e in read('research.json'):check(research.get('lean-proof-simplification/'+e['name'])==e['sha'],[e['name'],'research inventory binding mismatch'])
incoming={e['path']:e['sha'] for e in trees['incoming_tree']['tree']};check(incoming=={e['name']:e['sha'] for e in read('incoming.json')},'incoming inventory binding mismatch')
# One bounded closing screen; does not move the source pin.
closing_names=['root','computability','dc','research','proposals','Lean_root','modules','docs','incoming']
closing={n:read('closing_screen_'+n+'_tree.json') for n in closing_names}
for e in read('CLOSING_research.json'):
    if e['name'] in ['2026-10-26zk','2026-10-26zl','2026-10-26zm','2026-10-26zn','2026-10-26zo']:
        closing[e['name']]=read('closing_trees/'+e['name']+'.json')
for name,d in closing.items():
    check(d.get('truncated') is False,[name,'closing tree not complete'])
    dirs={'':[]};entries={e['path']:e for e in d['tree']}
    for e in d['tree']:
        parent,_,leaf=e['path'].rpartition('/');dirs.setdefault(parent,[]).append(dict(e,path=leaf))
    check(tree_hash(dirs[''])==d['sha'],[name,'closing tree mismatch'])
    for path,rows in dirs.items():
        if path:check(entries.get(path,{}).get('sha')==tree_hash(rows),[name,path,'closing nested tree mismatch'])
check(closing['root']['sha']==read('CLOSING_HEAD.json')['tree']['sha'],'closing commit/root mismatch')
check(read('CLOSING_HEAD.json')['sha']==read('CLOSING_MAIN_REF.json')['object']['sha'],'closing main/commit mismatch')
for parent,path,child in [('root','Computability','computability'),('computability','DiophantineConsistency','dc'),('dc','research','research'),('research','lean-proof-simplification','proposals'),('dc','Lean','Lean_root'),('Lean_root','DiophantineConsistency','modules'),('root','docs','docs'),('docs','incoming','incoming')]:
    check(next((e['sha'] for e in closing[parent]['tree'] if e['path']==path),None)==closing[child]['sha'],[parent,path,child,'closing ancestor mismatch'])
for name in closing:
    if name.startswith('2026-'):
        check(next((e['sha'] for e in closing['proposals']['tree'] if e['path']==name),None)==closing[name]['sha'],[name,'closing packet binding mismatch'])
for filename,name in [('CLOSING_research.json','proposals'),('CLOSING_incoming.json','incoming')]:
    check({e['name']:e['sha'] for e in read(filename)}=={e['path']:e['sha'] for e in closing[name]['tree']},[filename,'closing inventory mismatch'])
for filename,tree in [('CLOSING_proposal_manifest.json','proposals'),('CLOSING_incoming_manifest.json','incoming')]:
    rows=read(filename)['files'];counts[filename]=len(rows)
    for e in rows:
        if e['name'].endswith('.zip'):
            check(next((x['sha'] for x in closing[tree]['tree'] if x['path']==e['name']),None)==e['sha'],[e['name'],'closing archive Git blob/tree mismatch'])
            check(len(e.get('sha256',''))==64,[e['name'],'missing closing archive SHA256'])
            archive_status.append({'path':e['local_path'],'git_blob':e['sha'],'saved_sha256':e['sha256'],'bytes_replayed':WITH_ARCHIVES,'status':'byte replay requested' if WITH_ARCHIVES else 'archive bytes not bundled in curated delivery; not replayed; saved Git blob bound to tree, SHA256 recorded only'})
            if not WITH_ARCHIVES:counts[filename]-=1;continue
        if not (BASE/e['local_path']).is_file():bad.append([e['local_path'],'missing']);continue
        d=(BASE/e['local_path']).read_bytes();check(gitsha('blob',d)==e['sha'],[e['local_path'],'closing blob mismatch']);check(hashlib.sha256(d).hexdigest()==e['sha256'],[e['local_path'],'closing SHA256 mismatch']);check(next((x['sha'] for x in closing[tree]['tree'] if x['path']==e['name']),None)==e['sha'],[e['name'],'closing content/tree mismatch'])
for e in read('CLOSING_placement_manifest.json')['files']:
    d=(BASE/e['local_path']).read_bytes();check(gitsha('blob',d)==e['sha'],[e['local_path'],'placement blob mismatch']);check(hashlib.sha256(d).hexdigest()==e['sha256'],[e['local_path'],'placement SHA256 mismatch']);check(next((x['sha'] for x in closing[e['packet']]['tree'] if x['path']==e['path']),None)==e['sha'],[e['local_path'],'placement tree mismatch'])
counts['closing_placement_documents']=len(read('CLOSING_placement_manifest.json')['files'])
binding=read('CLOSING_target_binding.json');target='Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean'
check(binding['source_blob']==materialized[target]==binding['closing_blob'],'candidate whole-file equality mismatch')
check(next(e['sha'] for e in closing['modules']['tree'] if e['path']=='CurrentPackingRank2011.lean')==binding['closing_blob'],'closing target tree mismatch')
summary={'commit':read('HEAD_binding.json')['sha'],'commit_root_tree':read('HEAD_binding.json')['commit']['tree']['sha'],'active_Lean_tree':trees['Lean_tree']['sha'],'checked_files':counts,'archive_mode':'full byte replay' if WITH_ARCHIVES else 'manifest/tree references only; archive bytes omitted','archives':archive_status,'checked_tree_snapshots':len(trees)+len(closing),'active_Lean_files':len(active),'delta_vs_round5_source':read('active_tree_delta.json')['counts'],'delta_vs_round5_closing':read('since_closing_delta.json')['counts'],'failures':bad,'closing_screen_commit':read('CLOSING_HEAD.json')['sha'],'closing_candidate_byte_identical':binding['byte_identical'],'Lean_elaboration':'not run','scope':'focused exact source snapshot, direct repository dependencies only, not full Lake checkout or proof validation'}
print(json.dumps(summary,indent=2));sys.exit(bool(bad))
