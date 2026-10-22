from pathlib import Path
import ast, difflib, hashlib, json, re, subprocess

R = Path('/home/codex/.codex/worktrees/ec20/Proofs')
O = Path('/tmp/k215-phase16-coordination')
REMOTE = '140d832128fd43873f16e385766cd3cee08df8a9'
BASE = '8f2da699af96acc9c039436cac92093c02d26117'
PREFIX = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
ROOTS = ['Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean', 'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean']
def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)
def sha(b):
    return hashlib.sha256(b).hexdigest()

# Reuse the independently reviewed lexical readers, without executing their main code.
ns = {'re': re}
for node in ast.parse(Path('/tmp/k215-phase16-independent/inspect.py').read_text()).body:
    if isinstance(node, ast.FunctionDef) and node.name in ['clean', 'norm', 'decls']:
        exec(compile(ast.Module(body=[node], type_ignores=[]), '<lexical-reader>', 'exec'), ns)
clean, decls = ns['clean'], ns['decls']

names = ['KQ1Basic', 'KQ1Collect', 'KQ1Model', 'KQ1Power', 'KQ1Replacement', 'KQ1Separation', 'KQHyp', 'QuotientBasic', 'QuotientCPGIC', 'QuotientModel', 'QuotientPower', 'QuotientReplacement', 'QuotientSeparation']
reasons = {
 'KQ1Collect': 'One rw-then-exact compressed to rwa (dabeca4dc5).',
 'KQ1Model': 'Two rw-then-exact pairs compressed to rwa (dabeca4dc5).',
 'KQ1Replacement': 'One rw-then-exact compressed to rwa (dabeca4dc5).',
 'KQ1Power': 'Remote retains the original proposal trace_instance and PowerSyntax import/prose; checked branch inlines its only use and moves the import to the adapter.',
 'QuotientCPGIC': 'Remote retains two original proposal forwarders, and later compresses strong_trace/literal_subset_representative/quotient_containers proofs (a7b8f1ae67).',
 'QuotientModel': 'Remote retains original proposal mk_scons forwarder, uses KQ1Power.trace_instance and gets PowerSyntax transitively; checked branch removes/expands these.',
 'QuotientReplacement': 'Remote retains six original proposal forwarders and their QuotientSeparation import/open context; checked branch removes them.',
 'QuotientSeparation': 'Remote retains three original proposal forwarders; checked branch removes them.'
}
rows = []; diff = []
for n in names:
    p = PREFIX + n + '.lean'
    current = (R/p).read_bytes(); remote = git('show', REMOTE+':'+p)
    landing = git('show', '8e46744a76:'+p)
    rows.append({'module': n, 'path': p, 'checked_sha256': sha(current), 'remote_sha256': sha(remote), 'same': current == remote, 'same_at_claude_landing': current == landing, 'reason': reasons.get(n, 'Byte-identical.')})
    if current != remote:
        diff.extend(difflib.unified_diff(current.decode().splitlines(True), remote.decode().splitlines(True), fromfile='checked-phase16/'+p, tofile=REMOTE[:10]+'/'+p))
(O/'quotient-eight-files.diff').write_text(''.join(diff))

comparison = json.loads(Path('/tmp/k215-phase16-independent/comparison.json').read_text())
targets = [x['name'] for x in comparison['optional_retirement']['rows']] + ['KQ1Power.trace_instance']
assert len(targets) == 13
tokens = sorted({x.rsplit('.',1)[1] for x in targets})
rx = r'\b('+'|'.join(map(re.escape,tokens))+r')\b'
cmd = ['git','grep','-l','-E',rx,REMOTE,'--',*ROOTS]
r = subprocess.run(cmd,cwd=R,capture_output=True,text=True)
assert r.returncode in [0,1]
paths = [x.split(':',1)[1] for x in r.stdout.splitlines() if x.endswith('.lean')]
texts = {p: clean(git('show',REMOTE+':'+p).decode()) for p in paths}
pins = {p: sha(git('show',REMOTE+':'+p)) for p in paths}
target_set = set(targets)
census = []
for q in targets:
    mod,name = q.rsplit('.',1); hits = []
    for p,t in texts.items():
        local = p == PREFIX+mod+'.lean'
        opens = any(re.search(r'(?<![A-Za-z0-9_])'+re.escape(mod)+r'(?![A-Za-z0-9_])',line) for line in t.splitlines() if line.lstrip().startswith('open '))
        ds = decls(t); own = ds.get(name) if local else None
        for m in re.finditer(r'(?<![A-Za-z0-9_\'])'+re.escape(name)+r'(?![A-Za-z0-9_\'])',t):
            if own and own['start']<=m.start()<own['end']:
                continue
            pre = t[max(0,m.start()-120):m.start()]
            qualified = bool(re.search(r'\b'+mod+r'\.$',pre))
            bare = not pre.endswith('.') and (local or opens)
            if not (qualified or bare):
                continue
            owner = Path(p).stem
            declaration = next((n for n,d in ds.items() if d['start']<=m.start()<d['end']),None)
            line = t[:m.start()].count('\n')+1
            hits.append({'path':p,'line':line,'containing_declaration':owner+'.'+declaration if declaration else None,'text':t.splitlines()[line-1].strip()})
    outside = [h for h in hits if h['containing_declaration'] not in target_set]
    census.append({'name':q,'callers':hits,'outside_original_optional_forwarders':outside})
outside = [(row['name'],h) for row in census for h in row['outside_original_optional_forwarders']]
assert len(outside) == 1 and outside[0][0] == 'KQ1Power.trace_instance' and outside[0][1]['containing_declaration'] == 'QuotientModel.ofCPGIC',outside

review_path = R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase16/integration/current-review.json'
selected = json.loads(review_path.read_text())
effects = []
for mod,rec in selected['sources'].items():
    p = Path(rec['current']).relative_to(R).as_posix()
    actual = (R/p).read_bytes()
    assert sha(actual) == rec['sha256'], (p,'current receipt drift')
    r = subprocess.run(['git','show',REMOTE+':'+p],cwd=R,capture_output=True)
    if r.returncode:
        effects.append({'module':mod,'path':p,'remote':'absent'})
    elif r.stdout != actual:
        effects.append({'module':mod,'path':p,'remote':'different','checked_sha256':sha(actual),'remote_sha256':sha(r.stdout)})

scope = git('log','--reverse','--date=iso-strict','--format=%h | %ad | %s', 'b019487d0c..'+REMOTE,'--',*ROOTS).decode()
(O/'newer-lean-commits.txt').write_text(scope)
result = {
 'status':'READ_ONLY_COORDINATION_REVIEW',
 'base_head':BASE, 'remote_main_snapshot':REMOTE, 'cached_origin_main':git('rev-parse','origin/main').decode().strip(),
 'remote_observation':'git ls-remote observed main at this snapshot; fetched exact object using --no-write-fetch-head, without changing tracking refs.',
 'claude_named_ref':'0ec9a2191a161497f584725c0a0aa4b86a8c958b (2026-10-19); stale as a current-scope indicator',
 'claude_evidence':'Main commits co-authored by Claude Opus 5.5 and merge messages naming claude/busy-beaver-zfc-formalization-e75dc8.',
 'quotient_paths':rows,
 'generator':{'path':'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_kq1.py','checked':'absent','remote':'absent'},
 'caller_census':{'commit':REMOTE,'roots':ROOTS,'targets':census,'shortlisted_paths':pins,'strong_optional_forwarders':12,'new_outside_callers_of_twelve':0,'weak_trace_outside_callers':1,'weak_trace_only_owner':'QuotientModel.ofCPGIC','interpretation':'Remote retains original proposal helpers. These are not newly restored APIs in response to the unpublished phase16 cleanup. No new remote callers prevent the same optional trimming.'},
 'checked199_receipt_sha256':sha(review_path.read_bytes()),
 'checked199_effects':{'changed_or_absent':len(effects),'absent':sum(x['remote']=='absent' for x in effects),'rows':effects},
 'scope_limits':'No checkout, merge, staging, compilation, producer execution, canonical writes, other-worktree changes, or external messages. Source-level census only; upstream build claims are attributed Git data.'
}
(O/'mapping.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'quotient_matches':sum(x['same'] for x in rows),'quotient_differences':sum(not x['same'] for x in rows),'new_callers_of_twelve':0,'trace_only_caller':'QuotientModel.ofCPGIC','selected199_effects':len(effects),'output':str(O/'mapping.json')},indent=2))
