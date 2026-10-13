"""Bind native lex-prefix sources, tests, historical controls and final article.

This helper never runs tests, discovery, certificate replay, historical
publication mains or PDF builds. The reusable test_source_files() records
an exact pre-run byte closure. Final evidence checks follow separately.
"""
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

from strict_pachner32_publication import included_tex, python_dependencies

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
PREFIX = 'native-lex-prefix'
COMMAND = DATA/f'{PREFIX}-test-command.txt'
HISTORICAL_REVISION = 'c93b433f6fb18aec4cf939ba0037d7f63e5fff7d'
HISTORICAL_MANIFEST = DATA/'prefix-factor-evidence-publication.json'
HISTORICAL_MANIFEST_SHA256 = 'ca85277142409def82d181662460e4bcf4f16a94aedf588a5b6ce0da65b631f9'
GIT_PREFIX = 'Topology/UnknotRecognition/'
NATIVE_CHANGED = 'fast/fastunknot/exact_lp.py'
NEW_TEST = 'fast/tests/test_native_lex_prefix.py'
NEW_FIXTURE = 'fast/tests/fixtures/lex_bland_controls.json'
DOCUMENT_EXCEPTIONS = frozenset(('fast/README.md', 'synthesis/README.md',
    'synthesis/report.tex', 'synthesis/marked_cut_handlebodies.tex', 'synthesis/report.pdf',
    'synthesis/capped_pivot_pilot.tex', 'synthesis/whole_call_prefix.tex',
    'synthesis/exact_polynomial_lp.tex', 'synthesis/prepared_euler_matrix.tex'))


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(same(x,y) for x,y in zip(a,b))
    return a == b


def equal(a, b, message):
    require(same(a,b), message)


def load(path):
    return json.loads(path.read_bytes())


def test_source_files():
    """Exact 45-module native/static-import/dynamic-fixture/command closure."""
    old_command = DATA/'prepared-euler-matrix-test-command.txt'
    prior = re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', old_command.read_text())
    names = re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b', COMMAND.read_text())
    require(len(prior) == len(set(prior)) == 44, 'exact predecessor broad suite')
    equal(names, prior+['test_native_lex_prefix'], 'old44 plus new focused module in declared order')
    require(len(names) == len(set(names)) == 45, 'exact broad45 coverage')
    tests = {ROOT/'fast/tests'/(name+'.py') for name in names}
    initializer = ROOT/'fast/tests/__init__.py'
    if initializer.is_file():
        tests.add(initializer)
    fixtures = {DATA/'boundary-unlayer-audit.json',
        DATA/'coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/commitment_research/coherent-obstruction-certificate.json',
        ROOT/'reports/79/repro/fast/shared_cover_research/results/exhaustion.json',
        ROOT/'fast/tests/fixtures/causal_noncanonical.json',
        ROOT/'fast/conflict_composition_research/data/generation/tt-state.json.gz',
        ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz',
        ROOT/NEW_FIXTURE}
    files = set((ROOT/'fast/fastunknot').rglob('*.py'))
    files.update(python_dependencies(tests | fixtures))
    files.add(COMMAND)
    require(all(p.is_file() and p.is_relative_to(ROOT) for p in files), 'complete existing test closure')
    return {str(p.relative_to(ROOT)):digest(p) for p in sorted(files)}


def git_show(revision, relative):
    # Resolve git's root explicitly; paths below are repository-relative.
    repository = subprocess.check_output(['git','rev-parse','--show-toplevel'],
        cwd=ROOT, text=True).strip()
    return subprocess.check_output(['git','show',revision+':'+GIT_PREFIX+relative],
        cwd=repository)


def historical_checkpoint():
    require(digest(HISTORICAL_MANIFEST) == HISTORICAL_MANIFEST_SHA256, 'historical 961-file manifest')
    relative = str(HISTORICAL_MANIFEST.relative_to(ROOT))
    require(sha256(git_show(HISTORICAL_REVISION, relative)).hexdigest() == HISTORICAL_MANIFEST_SHA256,
        'manifest belongs to published predecessor revision')
    manifest = load(HISTORICAL_MANIFEST)
    equal({k:manifest[k] for k in ('schema','passed','tests','test_modules','skipped_tests',
        'tested_files','native_modules','maintained_native_sources_changed',
        'general_quasipolynomial','new_timing_claims')},
        dict(schema='prefix-factor-evidence-publication-v1',passed=True,tests=394,
            test_modules=44,skipped_tests=0,tested_files=361,native_modules=299,
            maintained_native_sources_changed=False,general_quasipolynomial=False,
            new_timing_claims=False), 'historical checkpoint coverage and scope')
    stdout = DATA/'prefix-factor-evidence-publication.txt'
    equal(load(stdout),{k:v for k,v in manifest.items() if k!='files_sha256'},
        'historical publication stdout binding')
    pins = manifest['files_sha256']
    require(type(pins) is dict and len(pins)==961, 'complete historical file inventory')
    exceptions = DOCUMENT_EXCEPTIONS | {NATIVE_CHANGED}
    require(exceptions <= pins.keys(), 'exceptions refer to existing historical files')
    paths, changed = set(), []
    for name, expected in pins.items():
        require(type(name) is str and type(expected) is str and re.fullmatch('[0-9a-f]{64}',expected),
            'literal historical hash entry')
        path=(ROOT/name).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(), 'historical file exists within project')
        paths.add(path)
        if digest(path)!=expected:
            require(name in exceptions, 'unexpected historical file change: '+name)
            changed.append(name)
    current_native={str(p.relative_to(ROOT)):digest(p)
        for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
    old_native={name:value for name,value in pins.items()
        if name.startswith('fast/fastunknot/') and name.endswith('.py')}
    require(len(current_native)==len(old_native)==299 and current_native.keys()==old_native.keys(),
        'native file set unchanged')
    equal(sorted(name for name in current_native if current_native[name]!=old_native[name]),
        [NATIVE_CHANGED], 'only exact LP implementation changed')
    return manifest,dict(revision=HISTORICAL_REVISION,manifest_sha256=HISTORICAL_MANIFEST_SHA256,
        historical_files=961,unchanged_files=961-len(changed),
        actual_changes=sorted(changed),allowed_document_changes=sorted(DOCUMENT_EXCEPTIONS),
        changed_native_files=[NATIVE_CHANGED],unchanged_native_modules=298), \
        paths|{HISTORICAL_MANIFEST,stdout}


def native_ast_check(manifest):
    """Reconstruct the entire predecessor AST, including Bland poll order."""
    old_bytes=git_show(HISTORICAL_REVISION,NATIVE_CHANGED)
    require(sha256(old_bytes).hexdigest()==manifest['files_sha256'][NATIVE_CHANGED],
        'git predecessor LP source matches historical manifest')
    old=ast.parse(old_bytes)
    new=ast.parse((ROOT/NATIVE_CHANGED).read_bytes())
    require(digest(ROOT/NATIVE_CHANGED)=='d338e71cd931d284c7bc0e6fa0404548e9c394fc51e19fd67ca950e3e331d43c',
        'native implementation equals independently reviewed candidate')
    functions=lambda tree:{node.name:node for node in tree.body if isinstance(node,ast.FunctionDef)}
    before,after=functions(old),functions(new)
    equal(set(after)-set(before),{'_dantzig_entering','_lexicographic_leaving'},
        'exactly two new selector helpers')
    require(not set(before)-set(after),'no removed functions')
    restored=deepcopy(new)
    restored.body=[node for node in restored.body if not (
        isinstance(node,ast.FunctionDef) and node.name in ('_dantzig_entering','_lexicographic_leaving'))]
    now=functions(restored)
    helper=now['_solve_prepared_kernel']
    require(helper.args.kwonlyargs[-1].arg=='pivot_rule' and
        isinstance(helper.args.kw_defaults[-1],ast.Constant) and
        helper.args.kw_defaults[-1].value=='bland','private default remains Bland')
    helper.args.kwonlyargs.pop();helper.args.kw_defaults.pop()
    guard=helper.body[1]
    expected_guard=ast.parse("if type(pivot_rule) is not str or pivot_rule not in ('bland', 'dantzig_lex'):\n    raise ValueError('unsupported private pivot rule')").body[0]
    equal(ast.dump(guard),ast.dump(expected_guard),'strict private-rule guard has no callbacks')
    helper.body.pop(1)
    class RestoreBland(ast.NodeTransformer):
        count=0
        def visit_If(self,node):
            if ast.unparse(node.test)=="pivot_rule == 'bland'":
                self.count+=1
                return node.body
            return self.generic_visit(node)
    transformer=RestoreBland();transformer.visit(helper)
    equal(transformer.count,2,'only entering/leaving branch restoration')
    added=[]
    for node in ast.walk(now['_run_kernel_policy']):
        if isinstance(node,ast.Call):
            for keyword in list(node.keywords):
                if keyword.arg=='pivot_rule':
                    require(isinstance(node.func,ast.Name) and node.func.id=='_solve_prepared_kernel' and
                        isinstance(keyword.value,ast.Constant) and keyword.value.value=='dantzig_lex',
                        'only polynomial tableau call receives the new rule')
                    added.append(keyword)
                    node.keywords.remove(keyword)
    equal(len(added),1,'sole controller keyword insertion')
    # Only these three explanatory docstrings changed with the implementation.
    require(isinstance(restored.body[0],ast.Expr),'module docstring')
    restored.body[0]=deepcopy(old.body[0])
    for name in ('_solve_prepared_kernel','solve_nonnegative_kernel'):
        now[name].body[0]=deepcopy(before[name].body[0])
    equal(ast.dump(restored),ast.dump(old),'entire restored predecessor AST')
    return dict(predecessor_exact_lp_sha256=sha256(old_bytes).hexdigest(),
        current_exact_lp_sha256=digest(ROOT/NATIVE_CHANGED),
        full_predecessor_ast_restored=True,explicit_bland_control_flow_and_polls_preserved=True,
        controller_only_polynomial_call_local_keyword=True,new_helpers=2,
        public_signatures_and_fallback_unchanged=True)


def legacy_fixture_check():
    import whole_call_prefix_replay as pilot
    archive=DATA/pilot.ARCHIVE_NAME
    payloads=pilot.checked_members(archive)  # Byte/inventory validation only; no child process.
    controls_bytes=payloads[pilot.PREFIX+'controls.json']
    controls=json.loads(controls_bytes)
    fixture=load(ROOT/NEW_FIXTURE)
    equal(set(fixture),{'schema','historical_revision','historical_controls_sha256',
        'baseline_exact_lp_sha256','records'},'exact retained legacy fixture schema')
    equal(fixture['schema'],'native-lex-legacy-controls-v1','legacy fixture schema')
    equal(fixture['historical_revision'],pilot.REVISION,'fixture historical source revision')
    equal(fixture['historical_controls_sha256'],sha256(controls_bytes).hexdigest(),
        'fixture authenticated control bytes')
    snapshot=json.loads(payloads[pilot.PREFIX+'snapshot/manifest.json'])
    native_paths={ROOT/'fast'/name[len('native/'):] for name in snapshot['files']}
    current_paths={p for p in (ROOT/'fast/fastunknot').rglob('*') if p.is_file() and
        '__pycache__' not in p.parts and p.suffix!='.pyc'}
    equal(native_paths,current_paths,'complete301-file native package inventory')
    for name,expected in snapshot['files'].items():
        path=ROOT/'fast'/name[len('native/'):]
        if str(path.relative_to(ROOT))!=NATIVE_CHANGED:
            equal(digest(path),expected,'unchanged native package member')
    original_lp=payloads[pilot.PREFIX+'snapshot/native/fastunknot/exact_lp.py']
    equal(fixture['baseline_exact_lp_sha256'],sha256(original_lp).hexdigest(),'fixture prechange LP source')
    inputs=(('positive_degenerate',[[1,1,-1]],[1,1,0],{}),
        ('dependent_dual',[[1,-1],[2,-2],[0,0]],[1,-2],{}),
        ('zero_width',[[],[]],[],{}),('zero_user',[[1,-1]],[1,0],{'max_pivots':0}),
        ('one_user',[[1,-1]],[1,0],{'max_pivots':1}))
    historical=[r for r in controls['legacy'] if r['arm']=='prepared_bland']
    require(len(historical)==len(fixture['records'])==5,'exact five unchanged Bland controls')
    for record,old,(name,matrix,cost,options) in zip(fixture['records'],historical,inputs):
        equal(old['case'],name,'historical legacy order')
        equal(old['pristine'],old['result'],'historical pristine/installed Bland equality')
        equal(record,dict(id=name,matrix=matrix,objective=cost,options=options,result=old['pristine']),
            'fixture is exact prior executed result with unchanged input')
    return dict(records=5,controls_sha256=sha256(controls_bytes).hexdigest(),
        archive_sha256=digest(archive),fixture_sha256=digest(ROOT/NEW_FIXTURE),
        historical_results_regenerated=False),native_paths|{archive,DATA/'whole_call_prefix_replay.py',ROOT/NEW_FIXTURE}


def check_tests():
    snapshot_path=DATA/f'{PREFIX}-test-source.json'
    snapshot=load(snapshot_path)
    tested=test_source_files()
    equal(snapshot['files_sha256'],tested,'pre-run source map still equals tested closure')
    equal(snapshot['schema'],'native-lex-prefix-test-source-v1','pre-run manifest schema')
    equal(snapshot['expected_tests'],408,'394 predecessor plus14 new test methods')
    require(len(tested)==363,'complete363-file test closure')
    expected_modules=re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b',COMMAND.read_text())
    equal(snapshot['modules'],['tests.'+name for name in expected_modules],'pre-run ordered module list')
    log_path=DATA/f'{PREFIX}-tests.txt'
    log=log_path.read_text()
    equal(re.findall(r'^Ran (\d+) tests in [\d.]+s$',log,re.M),['408'],'one complete408-test run')
    require(log.rstrip().endswith('\nOK'),'successful broad test completion')
    require(not re.search(r'skipped|expected failure|unexpected success|^FAIL|^ERROR',log,re.I|re.M),
        'no skipped or failed tests')
    cases=re.findall(r'^test_\w+ \((tests\.[^\n)]+)\) \.\.\. ok$',log,re.M)
    require(len(cases)==len(set(cases))==408,'exact distinct test coverage')
    modules=set(re.findall(r'\btests\.(test_[A-Za-z0-9_]+)\b',COMMAND.read_text()))
    equal({case.split('.')[1] for case in cases},modules,'all45 declared modules executed')
    require(len(modules)==45,'broad module count')
    parsed=ast.parse((ROOT/NEW_TEST).read_bytes())
    methods=[node.name for node in ast.walk(parsed)
        if isinstance(node,ast.FunctionDef) and node.name.startswith('test_')]
    require(len(methods)==len(set(methods))==14,'fourteen focused test methods')
    observed=[case for case in cases if case.startswith('tests.test_native_lex_prefix.')]
    require(len(observed)==14,'all focused methods in broad run')
    focused_path=DATA/f'{PREFIX}-focused-tests.txt'
    require(digest(focused_path)=='519385fe8d26d45fbfb6c90857dd44afab10a0b7e9c25bdcae5dff5ef760bd95','retained focused-run log bytes')
    focused=focused_path.read_text()
    equal(re.findall(r'^Ran (\d+) tests in [\d.]+s$',focused,re.M),['32'],'focused32 completion')
    require(focused.rstrip().endswith('\nOK') and not re.search(
        r'skipped|expected failure|unexpected success|^FAIL|^ERROR',focused,re.I|re.M),
        'focused run passed without skips')
    focused_cases=re.findall(r'^test_\w+ \((tests\.[^\n)]+)\) \.\.\. ok$',focused,re.M)
    require(len(focused_cases)==len(set(focused_cases))==32,'focused distinct coverage')
    equal({case.split('.')[1] for case in focused_cases},
        {'test_native_lex_prefix','test_prepared_exact_lp','test_polynomial_exact_lp'},
        'focused suite module coverage')
    require(set(focused_cases)<=set(cases),'every focused method repeated in source-bound broad run')
    return tested,dict(tests=408,test_modules=45,focused_methods=14,focused_regression_tests=32,
        skipped_tests=0,tested_files=len(tested),native_modules=299,pre_run_test_closure_exact=True), \
        {snapshot_path,log_path,COMMAND,focused_path}


def check_native_whole_call():
    """Bind one separately executed/replayed native call; perform no replay."""
    import native_lex_prefix_whole_call as runner
    helper=DATA/'native_lex_prefix_whole_call.py'
    require(digest(helper)=='4359f5d22a6d0d638ca1d7206dd37c8440d551e5479b88f61e35e96cd89f755f',
        'exact independently reviewed native evidence runner')
    run_path=DATA/'native-lex-prefix-whole-call.json'
    replay_path=DATA/'native-lex-prefix-whole-call-replay.json'
    run_stdout=DATA/'native-lex-prefix-whole-call.txt'
    replay_stdout=DATA/'native-lex-prefix-whole-call-replay.txt'
    retained={run_path:'030290ef9f30beb8299dfbc424a1e77aa133cbdce5b5553237bec1088ab422a7',
        replay_path:'41441d75e23c5422ce3927025ff82dd28b2bcd1095b27ce075de67c286c016e1',
        run_stdout:'931af83ad2a517b8a2a3b08929a3f1497896f6b398bcc901c59927b3e6f898cd',
        replay_stdout:'470ba8c04d5a03a426bf0073ea7c6c3997f4bf36926133996229451ed281155a'}
    for path,expected in retained.items():
        equal(digest(path),expected,'retained native run/replay bytes')
    record,replayed=load(run_path),load(replay_path)
    equal(record['schema'],'native-lex-prefix-whole-call-v1','native run schema')
    equal(replayed['schema'],'native-lex-prefix-whole-call-replay-v1','native replay schema')
    flags=dict(passed=True,phase='complete',case_id='W34',failures=[],timings_claimed=False,
        wall_limit_seconds=None,historical_native_equality_asserted=False,
        archived_native_imported=False,selector_monkeypatch_used=False,injected_source_used=False,
        historical_lp_queries_replayed=0,other_historical_calls_replayed=0,
        source_pins_unchanged=True)
    current=runner.source_hashes()  # Pure hash map, not native import/discovery.
    require(len(current)==302,'all299 native modules plus runner/accessor/archive')
    for evidence in (record,replayed):
        equal({key:evidence[key] for key in flags},flags,'exact fresh/replay scope flags')
        equal(evidence['source_sha256'],current,'current executed source pins')
        equal(evidence['source_sha256_after'],current,'source pins remained stable')
    equal((record['recognition_calls_started'],record['recognition_calls_returned']),(1,1),
        'exactly one fresh returned native call')
    equal((replayed['recognition_calls_started'],replayed['recognition_calls_returned']),(0,0),
        'separate check ran no recognition discovery')
    equal(replayed['discovery_disabled'],True,'separate proof replay disabled discovery')
    equal(replayed['input_sha256'],digest(run_path),'separate replay input-byte binding')
    require(type(replayed['input_path']) is str and Path(replayed['input_path']).name==run_path.name,
        'retained replay input filename; full bytes bound independently of historical absolute path')
    reference=runner.load_reference()  # Pure authenticated archive/metadata reads.
    equal(record['reference'],{key:reference[key] for key in ('archive_sha256','archive_audit_sha256',
        'historical_revision','archived_arm','config_sha256','result_sha256')},
        'historical candidate used only as bound comparison')
    equal(record['config'],reference['config'],'same original PD and all shared-cap options')
    value_hash=lambda value:sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    equal(record['config_sha256'],value_hash(record['config']),'literal config digest')
    equal(record['config_sha256'],reference['config_sha256'],'same historical config digest')
    equal(record['result_sha256'],value_hash(record['result']),'full native result digest')
    equal(record['result'],reference['result'],'observed full native/candidate result equality')
    equal(record['source_ledger'],reference['source_ledger'],'observed exact labelled path equality')
    comparison=dict(typed_result_equal=same(record['result'],reference['result']),
        typed_stats_equal=same(record['result']['stats'],reference['result']['stats']),
        typed_source_ledger_equal=same(record['source_ledger'],reference['source_ledger']),
        actual_status=record['result']['status'],archived_status=reference['result']['status'],
        actual_result_sha256=record['result_sha256'],archived_result_sha256=reference['result_sha256'])
    equal(record['comparison'],comparison,'equality flags are actual typed comparisons')
    equal(record['matches_archived_candidate'],True,'observed candidate match')
    expected_replay=dict(status='KNOTTED',proof_verified=True,partial_chain_verified=False,
        accepted_counts=dict(crushing_steps=32,boundary_unlayerings=0,pachner32_moves=3,pachner_descent_macros=3),
        elementary_macro_upward_moves=3,elementary_macro_downward_moves=6,
        endpoint=dict(terminal=False,source_sha256='5f53366b61f16027b896868a66cee02dce1c7a21b0cbb513e4ef583d2fd44345',
            tetrahedra=31,vertices=1,boundary_faces=2),
        recorded_work_counters_checked=True,lp_operation_trace_reconstructed=False)
    equal(record['replay'],expected_replay,'fresh native independent proof/ledger summary')
    equal(record['archived_candidate_replay'],expected_replay,'separately checked one historical comparison proof')
    hooks=record['disabled_discovery_hooks']
    require(type(hooks) is list and all(type(hook) is str for hook in hooks) and
        hooks==sorted(set(hooks)),'literal unique discovery guards retained')
    require({'fastunknot.exact_lp._run_kernel_policy','fastunknot.normal_crushing_search.recognize_by_crushing',
        'fastunknot.normal_euler_tree._EulerMaskOracle.attempt',
        'fastunknot.normal_geometric_descent.reduce_geometric_descent_once'}<=set(hooks),
        'LP, original recognizer, mask and geometric discovery disabled during proof replay')
    stats=record['result']['stats']
    require(type(stats) is dict and all(type(value) is int and value>=0 for value in stats.values()),
        'literal nonnegative native counters')
    equal({key:stats[key] for key in ('lp_calls','lp_pivots','lp_tableau_updates','lp_fallbacks',
        'lp_ellipsoid_iterations','lp_feasibility_calls')},dict(lp_calls=62,lp_pivots=6606,
        lp_tableau_updates=33094980,lp_fallbacks=0,lp_ellipsoid_iterations=0,lp_feasibility_calls=0),
        'observed finite native work counts')
    for option,fields in runner.CAP_STATS.items():
        require(all(field in stats for field in fields),'all shared-budget counters retained')
        cap=record['config']['options'][option]
        require(cap is None or (type(cap) is int and cap>=sum(stats[field] for field in fields)),
            'same finite native caller budget')
    summary=runner.summary(record)  # Pure stored-field projection.
    equal(load(run_stdout),summary,'native run stdout binding')
    equal(replayed['run_summary'],summary,'separate replay returned exact native summary')
    equal(load(replay_stdout),replayed,'separate replay stdout binding')
    files={helper,*retained}
    for name,expected in current.items():
        path=(ROOT/name).resolve()
        require(path.is_relative_to(ROOT) and path.is_file() and digest(path)==expected,
            'existing current native evidence dependency')
        files.add(path)
    return dict(case_id='W34',fresh_recognition_calls=1,separate_replay_recognition_calls=0,
        status='KNOTTED',result_sha256=record['result_sha256'],
        run_sha256=digest(run_path),replay_sha256=digest(replay_path),source_files=302,
        lp_calls=62,lp_pivots=6606,lp_tableau_updates=33094980,lp_fallbacks=0,
        accepted_counts=expected_replay['accepted_counts'],endpoint=expected_replay['endpoint'],
        typed_result_equal=True,typed_stats_equal=True,typed_source_ledger_equal=True,
        recorded_work_counters_checked=True,lp_operation_trace_reconstructed=False,
        historical_other_thirteen_calls_claimed_current=False,
        replay_executed_by_this_helper=False,timings_claimed=False),files


def diagnostics(contents):
    found=Counter()
    for line in contents.splitlines():
        if 'Warning:' in line or re.match(r'^(?:Over|Under)full \\[hv]box\b',line):
            line=re.sub(r'\bat lines \d+--\d+\b','at lines <range>',line.strip())
            line=re.sub(r'\bat line \d+\b','at line <number>',line)
            found[line]+=1
    return found


def check_build(manifest):
    baseline=DATA/'prefix-factor-evidence-latex-3.txt'
    equal(digest(baseline),manifest['files_sha256'][str(baseline.relative_to(ROOT))],
        'historical final diagnostic reference')
    builds=[DATA/f'{PREFIX}-latex-{i}.txt' for i in (1,2,3)]
    for path in builds:
        text=path.read_text()
        require('Output written on report.pdf' in text,'completed PDF pass')
        require(not re.search(r'^!|Emergency stop|Fatal error occurred',text,re.M),'no PDF build error')
    final=builds[-1].read_text()
    require(not re.search(r'undefined references|undefined on input|Rerun to get|Label\(s\) may have changed|multiply.defined labels',final),
        'final references settled')
    require(not (diagnostics(final)-diagnostics(baseline.read_text())),'no additional build diagnostics')
    match=re.search(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)',final)
    require(match is not None,'final page/byte report')
    pdf=ROOT/'synthesis/report.pdf'
    require(pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size==int(match[2]),
        'current PDF agrees with final build')
    tex=included_tex(ROOT/'synthesis/report.tex')
    require({ROOT/'synthesis/native_lex_prefix.tex',ROOT/'synthesis/coordinate_separator_obstruction.tex'}<=tex,
        'new selector and abstract separator-obstruction theory included')
    return dict(report_pages=int(match[1]),report_bytes=int(match[2]),included_tex_files=len(tex)), \
        tex|set(builds)|{pdf,baseline}


def main():
    if not __debug__:
        raise RuntimeError('publication checks require assertions enabled')
    output=DATA/f'{PREFIX}-publication.json'
    if output.exists():
        raise FileExistsError('Refuse to overwrite retained publication: '+str(output))
    manifest,history,files=historical_checkpoint()
    structure=native_ast_check(manifest)
    fixture,fixture_files=legacy_fixture_check()
    tested,tests,test_files=check_tests()
    native_call,native_call_files=check_native_whole_call()
    build,build_files=check_build(manifest)
    files |= fixture_files|test_files|native_call_files|build_files|{ROOT/name for name in tested}|{
        Path(__file__).resolve(),DATA/'strict_pachner32_publication.py',
        ROOT/'fast/strict_pachner32_research/common.py',
        ROOT/'fast/strict_pachner32_research/check_evidence.py'}
    files=python_dependencies(files)
    require(all(p.is_file() and p.is_relative_to(ROOT) for p in files),'complete final pin closure')
    equal(test_source_files(),tested,'tested files stable throughout publication check')
    result=dict(schema='native-lex-prefix-publication-v1',passed=True,**tests,**build,
        historical_checkpoint=history,native_structure=structure,legacy_fixture=fixture,
        native_whole_call=native_call,
        general_quasipolynomial=False,new_timing_claims=False,
        tests_or_build_run_by_this_helper=False,solver_discovery_run_by_this_helper=False,
        certificate_replay_run_by_this_helper=False,replay_subprocess_run_by_this_helper=False,
        historical_publication_mains_executed=False,
        files_sha256={str(p.relative_to(ROOT)):digest(p) for p in sorted(files)})
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='files_sha256'},sort_keys=True))


if __name__=='__main__':
    main()
