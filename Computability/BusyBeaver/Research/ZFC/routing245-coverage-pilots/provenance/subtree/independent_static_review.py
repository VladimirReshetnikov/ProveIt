"""Independent source/prepared-metadata review only; never imports/runs supplied code."""
from pathlib import Path
import ast, collections, hashlib, json, re
B=Path('/tmp/zfc-routing245-lean/coverage-subtree-pilots')
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
checks=[]
def check(c,s):
    if not c: raise AssertionError(s)
    checks.append(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return {'path':str(p),'sha256':sha(p)}
def pinned(d):check(sha(d['path'])==d['sha256'],'hash '+d['path'])
def imports(p):return re.findall(r'^import\s+(\S+)\s*$',Path(p).read_text(),re.M)
M=json.loads((B/'subtree-plan.json').read_text())
G=(B/'check-subtrees.py').read_text(); tree=ast.parse(G)
constants={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ['MANIFEST_SHA','GENERATOR_SHA','BOUNDARY_SHA','COVERAGE_EVIDENCE','PARENTS','COMPILER_SHA','TOOLS','ORDER','EXPECTED_CUTS','DIRECT','PROBES','TIMEOUT']}
for file,key in [('subtree-plan.json','MANIFEST_SHA'),('prepare_subtrees.py','GENERATOR_SHA'),('boundary-plan.json','BOUNDARY_SHA')]:check(sha(B/file)==constants[key],key)
for d in M['inputs']:pinned(d)
P=Path(M['inputs'][1]['path']);pt=P.read_text()
rows={}
for line in pt.splitlines():
    m=re.fullmatch(r'private def row(\d+) : Row := (.*)',line)
    if m:
        tokens=re.findall(r'\.(\w+)(?: (\d+))?',m[2]);check(len(tokens)==2,'two edges row '+m[1])
        rows[int(m[1])]=tuple((op,int(n) if n else None) for op,n in tokens)
check(set(rows)==set(range(203)),'203 literal rows')
# Parse the actual TreeRouting245 definitions separately from the row declarations.
def edge(s):
    m=re.fullmatch(r't(\d{3})',s)
    if m:return ('node',int(m[1]))
    m=re.fullmatch(r'\(\.leaf \(\.(\w+) (\d+)\)\)',s)
    if m:return (m[1],int(m[2]))
    check(s=='(.leaf .halt)','literal halt tree edge');return ('halt',None)
trees={}
edgepat=r'(t\d{3}|\(\.leaf \(\.\w+ \d+\)\)|\(\.leaf \.halt\))'
for line in pt.splitlines():
    m=re.fullmatch(r'private def t(\d{3}) : Tree := \.node '+edgepat+' '+edgepat,line)
    if m:
        i=int(m[1]);trees[i]=(edge(m[2]),edge(m[3]));check(trees[i]==rows[i],'actual tree agrees row '+str(i))
check(set(trees)==set(rows),'all203 actual tree definitions parsed')
check('def tree : Tree := t202' in pt and 'theorem tree_eq : ptree program = tree := tree_eq_fuel 204 (by decide)' in pt,'actual root and proved ptree linkage')
expanded=[];stack=[('',('node',202))]
while stack:
    path,e=stack.pop()
    if e[0]=='node':
        a,b=trees[e[1]]
        for x in (a,b):check(x[0]!='node' or x[1]<e[1],'acyclic row '+str(e[1]))
        stack.extend([(path+'1',b),(path+'0',a)])
    else:expanded.append((path,e))
logical=json.loads(Path(M['inputs'][0]['path']).read_text());codes={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
check(expanded==[(p,(codes[k],v)) for p,k,v in logical],'all6460 actual-tree leaves equal delivered logical certificate')
check(len(expanded)==6460 and sum(1+(e[0]=='decnz') for _,e in expanded)==8391 and max(len(p) for p,_ in expanded)==51,'whole-tree counts')
unitreports=[]
for u in M['selected_units']:
    i=u['index'];prefix=u['path'];members=[(n,p,e) for n,(p,e) in enumerate(expanded) if p.startswith(prefix)]
    check([n for n,p,e in members]==list(range(u['lo'],u['hi'])),'exact contiguous subtree '+str(i))
    check(len(members)==u['leaves'] and sum(1+(e[0]=='decnz') for _,_,e in members)==u['guards'],'case counts '+str(i))
    check(max(len(p)-len(prefix) for _,p,e in members)==u['height'],'subtree height '+str(i))
    check(len(prefix)==u['prefix_length'] and max(len(p) for _,p,e in members)==u['maximum_absolute_depth'],'prefix/depth '+str(i))
    expectedmembers=[dict(index=n,path=p,opcode=next(k for k,v in codes.items() if v==e[0]),operand=e[1],guards=1+(e[0]=='decnz')) for n,p,e in members]
    check(expectedmembers==u['members'],'all member metadata '+str(i))
    for role in ['source','audit']:pinned(u[role])
    st=Path(u['source']['path']).read_text();au=Path(u['audit']['path']).read_text()
    ns='SetTheory.BusyBeaver.ZFC.'+u['module'].split('.')[-1]
    bools=lambda text: ''.join('1' if x=='true' else '0' for x in re.findall(r'true|false',text))
    m=re.search(r'theorem checked :\s+allSites SiteRouting245.checkSite (\[[^\]]*\])\s+\(descend TreeRouting245.tree (\[[^\]]*\])\) = true := by\s+decide \+kernel',st)
    check(m is not None and bools(m[1])==prefix[::-1] and bools(m[2])==prefix,'full-prefix actual-tree goal '+str(i))
    check(imports(u['source']['path'])==constants['DIRECT'] and imports(u['audit']['path'])==[u['module']],'imports '+str(i))
    check(re.findall(r'^#print axioms (\S+)$',au,re.M)==[ns+'.checked'] and len(re.findall(r'^example\b',au,re.M))==2,'1/2 audit '+str(i))
    check('allSites_sound SiteRouting245.checkSite hl' in au and 'Q : List Bool' in au and '.reverse ++ Q' in au,'arbitrary local leaf client '+str(i))
    check(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',st+'\n'+au,re.M),'default source proof policy '+str(i))
    q=B/'prepared1'/f'cut{i:03d}'/'verification.json';d=json.loads(q.read_text())
    check(d['status']=='PREPARED_NOT_BUILT' and d['prepare_only'] and d['commands']==[] and d['fresh_modules']==[],'preparation only '+str(i))
    check(len(d['before'])==85 and d['before']==d['after'] and d['all_input_provider_postchecks'],'85 unchanged preparation inputs '+str(i))
    for p,h in d['before'].items():check(sha(p)==h,'current preparation input '+str(i)+' '+p)
    check(not d['compiler_version_query_performed'] and not d['dependency_build'] and not d['downloads'],'no build/version/download '+str(i))
    check(d['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),'limits '+str(i))
    for role in ['source','audit']:
        check(d[role]['sha256']==u[role]['sha256']==sha(d[role]['snapshot']),'snapshot '+str(i)+' '+role)
    providers={p['module']:p for p in d['reused_modules']}
    actual={p['module']:p for p in d['actual_first_providers']}
    check(len(providers)==len(actual)==23,'23 unique providers '+str(i))
    for name,p in providers.items():
        check(all(sha(p[k])==p[k+'_sha256'] for k in ('source','object')),'current provider '+str(i)+' '+name)
        check(Path(actual[name]['actual_first']).resolve()==Path(p['object']).resolve() and actual[name]['sha256']==p['object_sha256'],'actual-first '+str(i)+' '+name)
    seen=set();external={'Init'}
    def dfs(name):
        if name in seen:return
        if name not in providers:external.add(name);return
        seen.add(name)
        for child in imports(providers[name]['source']):dfs(child)
    for name in constants['DIRECT']:dfs(name)
    check(seen==set(providers) and external==set(constants['TOOLS']),'exact actual DFS23 plusInitOmega '+str(i))
    for t in d['toolchain_providers']:check(sha(t['object'])==t['object_sha256']==constants['TOOLS'][t['module']],'tool provider '+str(i)+' '+t['module'])
    check(sha(d['compiler']['path'])==d['compiler']['sha256']==constants['COMPILER_SHA'],'compiler identity '+str(i))
    for e in d['provider_evidence']:pinned(e)
    unitreports.append(dict(index=i,path=prefix,leaves=u['leaves'],guards=u['guards'],height=u['height'],source=u['source'],audit=u['audit'],prepared_record=desc(q),prepared_inputs=85,project_providers=23,tools=sorted(external)))
check(sum(x['leaves'] for x in unitreports)==90 and sum(x['guards'] for x in unitreports)==117,'three-subtree90/117 scope')
# Source-only CFG safeguards: parser binding survives all certificate/provider loops.
for n in ast.walk(tree):
    if isinstance(n,ast.Name) and n.id=='args' and isinstance(n.ctx,ast.Store):
        check(any(isinstance(a,ast.Assign) and any(t is n for t in a.targets) and isinstance(a.value,ast.Call) and isinstance(a.value.func,ast.Attribute) and a.value.func.attr=='parse_args' for a in ast.walk(tree)),'args only assigned parser result')
check("cmd=[str(compiler),'-j1','-M4096','--root='+str(snap)]" in G and 'deadline=time.monotonic()+TIMEOUT' in G and 'timeout=remaining' in G,'serial default resource policy')
check(G.index('if args.prepare_only:post();save();return record')<G.index("run('source',ss,obj)"),'prepare returns before compiler')
check(G.index('source_object_recorded_before_audit=True')<G.index("output=run('audit',aa)"),'pre-audit source object persisted')
check("record.update(status='PASS',all_fresh_objects_unchanged_after_audit=True" in G and "need(result['status']==('PREPARED_NOT_BUILT' if args.prepare_only else 'PASS')" in G,'fail-closed per-unit acceptance')
report=dict(status='SOURCE_PATTERN_AND_EXISTING_PREPARATION_REVIEW_CLEAN',reviewer='drop_contract',findings=[],checks=len(checks),
 scope='Independent full source/audit/emitter/guard read, own static literal-tree parser and existing preparation/provider rehash; no supplied generator/guard, simulation, compiler or version execution. Actual subtree compiler runs intentionally not included.',
 files=[desc(B/x) for x in ['check-subtrees.py','prepare_subtrees.py','prepare_guard.py','subtree-plan.json','boundary-plan.json','guard-from-leaf.diff']],
 reviewed_helpers=[desc(P),desc(Path(M['inputs'][2]['path'])),desc(Path(M['inputs'][3]['path']))],units=unitreports,
 mathematical_findings=['Every source proposition descends the imported actual TreeRouting245.tree with the full forward path and carries its exact reverse prefix.','allSites_sound restores that full prefix before the arbitrary local path Q; no decoder context is reset.','SiteRouting245.checkSite includes the path-length test and both zero/positive decrement guards at unchanged fuel4000/margin64.','The existing ProgramRouting245 tree_eq binds the literal tree to the actual register decoder; all203 literal tree nodes independently match row definitions, all6460 expanded leaves match the pinned logical certificate.','These three subtrees cover90 leaves/117 guards only. Complete coverage still requires a disjoint complete frontier and structural joins to the root.'],
 guard_findings=['Exact23 current project provider pairs and Init/Omega selected from actual Site/Program plus generic SiteCoverage evidence; old runtime module is not imported.','Three existing preparations have85 unchanged current inputs each, zero commands/fresh modules and no compiler/version/build/download.','Selected source/audit hashes, actual-first providers and postchecks are enforced; source object is bound before typed audit; only successful units accepted.','Per-unit source and audit share120seconds with-j1/-M4096 and unchanged default proof limits. Legacy imported helper options are historical provider scope, not raised limits in the new sources.'],
 limitations=['No complete all-sites theorem or binary/PA endpoint claimed.','No conclusion from ongoing or later actual compiler results is included.','The236-cut cap64 metadata frontier is a planning artifact, not a frozen production schedule.'],
 reviewer_script=desc(Path(__file__)))
out=B/'independent-subtree-pattern-review.json';check(not out.exists(),'immutable report output is new');out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'report':desc(out),'checks':len(checks)}))
