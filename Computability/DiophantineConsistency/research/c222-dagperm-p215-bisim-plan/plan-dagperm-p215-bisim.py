from pathlib import Path
import json, hashlib, re, copy
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
REV=D/'reviews'; OUT=D/'research/c222-dagperm-p215-bisim-cache-plan-20261026.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pin(p): return {'path':str(p),'sha256':sha(p)}
base=Path('/tmp/dag-controlperm222-controller-author-_s3qdbgq/inputs.json')
j=json.loads(base.read_text())
packet=REV/'arithmetic-dag-controlperm222-replay.json'
fresh=json.loads(packet.read_text())
rows=copy.deepcopy(j['modules'])
for rec in fresh['records']:
    if rec['module'].endswith('Checks'): continue
    src=Path(rec['source']['path'])
    old=next((r for r in rows if r['module']==rec['module']),None)
    new={'module':rec['module'],'source':rec['source'],
         'imports':['Init']+re.findall(r'^import\s+(\S+)',src.read_text(),re.M),
         'objects':[rec['object']],'provider':pin(packet),
         'action':'AUTHOR_FRESH_FROZEN_PENDING_ROOT_INDEPENDENT_ACCEPTANCE'}
    if old is None: rows.append(new)
    else:
        new['historical_selected_record']=copy.deepcopy(old)
        rows[rows.index(old)]=new
native=REV/'native-ordinary-source-construction-replay.json'
def collect(x):
    if isinstance(x,dict):
        if x.get('module')=='BusyBeaver.ZFC.KSource215Program': yield x
        for v in x.values(): yield from collect(v)
    elif isinstance(x,list):
        for v in x: yield from collect(v)
candidates=list(collect(json.loads(native.read_text())))
assert candidates
k=candidates[0]
assert all(r['source']==k['source'] and r['object']==k['object'] for r in candidates)
rows.append({'module':k['module'],'source':k['source'],
 'imports':k['actual_imports'],'objects':[k['object']],
 'provider':pin(native),'action':'ACCEPTED_CURRENT_SOURCE_OBJECT_REUSE'})
mods={r['module']:r for r in rows}; assert len(mods)==len(rows)
ext={r['module']:r for r in j['external']}
def imports(text):
    # Strip nested block comments, retaining newlines and quoted source strings.
    out=[];i=0;depth=0
    while i<len(text):
        if text.startswith('/-',i): depth+=1;i+=2;continue
        if depth and text.startswith('-/',i):depth-=1;i+=2;continue
        c=text[i];i+=1
        if not depth or c=='\n':out.append(c)
    result=[]
    for line in ''.join(out).splitlines():
        m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*(?:--.*)?$',line)
        if m:result.extend(m[1].split())
    if not re.search(r'^\s*prelude\s*$',text,re.M):result.insert(0,'Init')
    return list(dict.fromkeys(result))
observations=0
for r in rows:
    assert sha(r['source']['path'])==r['source']['sha256'],r['module']
    actual=imports(Path(r['source']['path']).read_text())
    assert actual==list(dict.fromkeys(['Init']+r['imports'])),(r['module'],actual,r['imports'])
    r['actual_imports']=actual;observations+=1
    for o in r['objects']:
        assert sha(o['path'])==o['sha256'],o['path'];observations+=1
    for name in actual:assert name in mods or name in ext,(r['module'],name)
for e in ext.values():assert sha(e['path'])==e['sha256'];observations+=1
pins=[]
for p in j['pins']:
    assert sha(p['path'])==p['sha256'],p['path'];pins.append(p)
for p in [base,packet,REV/'arithmetic-dag-controlperm222-author.md',
          REV/'arithmetic-dag-controlperm222-author-replay/FILES.json',native,
          REV/'machine215-current-closure-completed.json',
          REV/'arithmetic-dag-loops-root.md',
          REV/'arithmetic-dag-loops-root-authentication/arithmetic-dag-loops-root-authentication.json',
          D/'research/c222-dagperm-p215-control-comparison-20261026.md',
          D/'research/c222-dagperm-control-plan/p215-control-compare.json',
          D/'research/c222-dagperm-control-plan/p215-control-compare.py',Path(__file__)]:pins.append(pin(p))
seen=set();order=[]
def visit(n):
    if n in seen:return
    seen.add(n)
    for m in mods[n]['actual_imports']:
        if m in mods:visit(m)
    order.append(n)
direct=['BusyBeaver.ZFC.ArithmeticDagControlPerm222','BusyBeaver.ZFC.KSource215Program']
for n in direct:visit(n)
assert seen==set(mods),(set(mods)-seen)
result={'status':'READ_ONLY_PLAN_REAUTHENTICATED_NO_COMPILER',
 'direct_imports':direct,'counts':{'custom':len(rows),'Foundation':sum(n.startswith('Foundation.')for n in mods),
 'artifacts':sum(len(r['objects'])for r in rows),'external':len(ext),'fresh_prerequisites':0},
 'modules':[mods[n]for n in order],'external':j['external'],'pins':pins,
 'selected_source_object_boundary_observations':observations,
 'inherited_pin_observations':len(j['pins']), 'compiler':j['compiler'],
 'acceptance_boundary':'DagControl and its PackedTables object are author-frozen, root independent replay pending; select accepted byte-identical root providers by a later supplement. DagLoops accepted at b5459f3024. KSource215Program uses a current source-identical accepted native provider, not arbitrary cache discovery.',
 'proposed_new_leaves':['ArithmeticControl215Table','ArithmeticControlBisimPerm215'],
 'scope':'Actual complete p215 catalogue then 2850-entry/fuel6 segment certificate and all-internal IΣ1 control-run halting equivalence only. No Turing-machine or source-ZFC/HA endpoint.'}
assert not OUT.exists();OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['counts']), 'observations',observations,sha(OUT),OUT)
