"""Independent frozen-source pins and small pure metadata controls; no collector."""
from pathlib import Path, PurePosixPath
import argparse, ast, hashlib, json, re
S = Path('/tmp/k215-phase15-publication')
O = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
a = argparse.ArgumentParser()
a.add_argument('--freeze-sha256', required=True)
args = a.parse_args()
assert sha(S/'freeze.json') == args.freeze_sha256
freeze = json.loads((S/'freeze.json').read_text())
assert freeze['status'] == 'FROZEN_PUBLICATION_HELPERS_NOT_EXECUTED'
for n, pin in freeze['files'].items():
    assert sha(S/n) == pin, n
cfg = json.loads((S/'config.json').read_text())
for p, row in cfg['files'].items():
    assert sha(p) == row['sha256'] and Path(p).stat().st_size == row['bytes'], p
assert len(cfg['project_source_paths']) == 199
assert len(cfg['adoption']['raw']['files']) == 10 and len(cfg['historical_inputs']) == 9
assert cfg['adoption']['raw']['status'] == 'ADOPTED_EXACT_CHECKED_PHASE15'
assert sum(len(x) for x in cfg['new_api_profiles'].values()) == 28
# Load only the already read pure definitions. No import or top-level validator,
# collector, saved reader, source producer or compiler is executed.
tree = ast.parse((S/'packet.py').read_text())
names = {'safe','same_source_closure','exact_reuse','exact_resume','reports','profiles','named_reports','explicit_externals'}
nodes = [n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names]
assert {n.name for n in nodes} == names
ns = {'PurePosixPath':PurePosixPath,'re':re,'STANDARD':{'propext','Classical.choice','Quot.sound'},
      'BINARY':{'.olean','.ilean','.o','.so','.a','.vo','.vos','.vok','.glob','.pyc','.pyo'}}
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(S/'packet.py'),'exec'),ns)
checks = []
def check(name, accepted, call):
    try:
        call()
        actual = True
    except (AssertionError,KeyError):
        actual = False
    assert actual == accepted, name
    checks.append({'name':name,'expected_accept':accepted,'matched':True})
check('safe source path',True,lambda:ns['safe']('execution/Source.lean'))
for p in ['/absolute','a/../b','x.olean.server','ancestor.tar.gz']:
    check('reject '+p,False,lambda p=p:ns['safe'](p))
r = {'status':'PASS','source_sha256':'s','object_sha256':'o','log_sha256':'l'}
check('exact successful resume',True,lambda:ns['exact_resume'](r,dict(r)))
check('reject failed resume',False,lambda:ns['exact_resume']({**r,'status':'FAIL'}, {**r,'status':'FAIL'}))
check('reject changed resumed object',False,lambda:ns['exact_resume']({**r,'object_sha256':'changed'},r))
old = {'A':{'source_sha256':'a','imports':['B'],'object_sha256':'same'},'B':{'source_sha256':'b','imports':['Init'],'object_sha256':'same'}}
check('exact transitive source closure',True,lambda:ns['same_source_closure'](old,old,{'A','B'}))
changed = {**old,'B':{**old['B'],'source_sha256':'new'}}
check('reject source change masked by identical object',False,lambda:ns['same_source_closure'](changed,old,{'A','B'}))
changed = {**old,'B':{**old['B'],'imports':[]}}
check('reject changed import closure',False,lambda:ns['same_source_closure'](changed,old,{'A','B'}))
pq = b"'exact' depends on axioms: [propext, Quot.sound]\n"
check('exact PQ report',True,lambda:ns['named_reports'](pq,['exact'],[['propext','Quot.sound']]))
check('reject added choice in exact PQ profile',False,lambda:ns['named_reports'](pq.replace(b'propext,',b'Classical.choice, propext,'),['exact'],[['propext','Quot.sound']]))
check('reject sorryAx report',False,lambda:ns['named_reports'](pq.replace(b'propext',b'sorryAx'),['exact']))
check('reject changed report name',False,lambda:ns['named_reports'](pq,['other']))
check('Init-only external import',True,lambda:ns['explicit_externals']([{'module':'A','imports':['Init']}]))
check('reject unknown provider',False,lambda:ns['explicit_externals']([{'module':'A','imports':['Unknown']}]))
out = {'status':'PASS_INDEPENDENT_PURE_METADATA_CONTROLS','freeze_sha256':args.freeze_sha256,
       'helper_pins':freeze['files'],'context_files':len(cfg['files']),'checks':checks,
       'positive':sum(x['expected_accept'] for x in checks),'negative':sum(not x['expected_accept'] for x in checks),
       'scope':'Frozen source/config rehash and extracted pure metadata functions only; no collector/saved reader/compiler/producer.'}
p = O/'controls.json'
assert not p.exists()
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'positive':out['positive'],'negative':out['negative'],'sha256':sha(p)},indent=2))
