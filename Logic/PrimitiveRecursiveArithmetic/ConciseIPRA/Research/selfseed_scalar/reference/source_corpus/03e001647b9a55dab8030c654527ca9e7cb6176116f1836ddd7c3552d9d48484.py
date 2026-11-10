"""Self-contained finite verification of selected composed checkers.

The inherited universal metatheorems remain written mathematical proofs.
This script checks executable examples, scoped failures and provenance.
"""
import gzip,hashlib,importlib.util,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
PROGRAMS=['code/checker.py','code/readable_checker.py','ancillary/checker_bytes.py','ancillary/checker_ast.py','ancillary/checker_ast_loop.py']

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def accepted(path,data,opt=False,raw=False):
    run=subprocess.run([sys.executable]+(['-O'] if opt else [])+[str(path)],input=data if raw else json.dumps(data),text=True,capture_output=True,timeout=20)
    return run.returncode==0 and run.stdout=='ACCEPT\n'

def verify():
    producer=load('composed_producer',ROOT/'tests/producer.py')
    cases=json.loads(json.dumps(producer.build_cases()))
    if cases!=json.loads((ROOT/'tests/cases.json').read_text()):raise AssertionError('Changed producer cases')
    rebuilt=load('producer_rebuild',ROOT/'tools/rebuild_producer.py').generated()
    if rebuilt!=(ROOT/'tests/producer.py').read_text():raise AssertionError('Changed producer adaptation')
    for c in cases:
        if c['packet']!=json.loads((ROOT/'tests/fixtures'/(c['name']+'.json')).read_text()):raise AssertionError(c['name'])
    rows=[]
    for name in PROGRAMS:
        source=ROOT/name
        if gzip.decompress(Path(str(source)+'.gz').read_bytes())!=source.read_bytes():raise AssertionError('gzip mismatch: '+name)
        for opt in [False,True]:
            for c in cases:
                actual=accepted(source,c['packet'],opt)
                rows.append(dict(program=name,case=c['name'],optimized=opt,expected=c['accept'],actual=actual,ok=actual==c['accept']))
    malformed=[]
    for name in PROGRAMS:
        for raw in ['{','null','[]','{}','"text"','[null]','["a"]','[[["a",0]], [0,[0]]]']:
            ok=not accepted(ROOT/name,raw,raw=True)
            malformed.append(dict(program=name,input=raw,ok=ok))
    original=(ROOT/'code/checker.py').read_text()
    zero=[0,0,0];eq=[zero,0];comp=[None,0,0,0]
    reflex=[eq,zero,0,[3,0]];false_transport=[eq,0,[0],[0,3]]
    byname={c['name']:c for c in cases}
    controls=[
      ('paired_arity','i(*a, t, 2)','i(a[0], t, 2)',[[0,0,0,[0,0]],[[0,0],[0]]],'False 0=1.'),
      ('major_endpoint','m in ([s, u], not s and [t] * 3) and ','',[comp,comp,reflex,comp,false_transport,[0,[0]]],'False 0=1.'),
      ('recursive_state','i(t, [s, u, t], 3) if s else u','t if s else u',[[None,[0,0],[0],3],[[[[0,0]],[0],3],0]],'False I(1,1;v.v)=0.'),
      ('successor_construction','s and [s]','s',[[None,[0,0],[0],0],[[[0,0],[0],0],0]],'False I(0,1;v.0)=0.'),
      ('literal_equation_progress','len(a) % 2 == m','not m',byname['forbidden_compound_progress']['packet'],'Forbidden compound-formula induction.'),
      ('scope_floor','k <= a < d','a < d',[[None,0,-1,0],[[0,-1,0],-1]],'Unallocated negative parameter in a closed goal.'),
    ]
    guards=[]
    with tempfile.TemporaryDirectory(prefix='ipra-composed-control-') as d:
        for name,before,after,packet,meaning in controls:
            if original.count(before)!=1:raise AssertionError(name)
            mutant=Path(d)/(name+'.py');mutant.write_text(original.replace(before,after))
            for opt in [False,True]:
                real=accepted(ROOT/'code/checker.py',packet,opt);unsafe=accepted(mutant,packet,opt)
                guards.append(dict(name=name,optimized=opt,meaning=meaning,real_accepts=real,mutant_accepts=unsafe,ok=not real and unsafe))
    measure=load('composed_measure',ROOT/'measure.py').collect()
    saved=json.loads((ROOT/'evidence/measurements.json').read_text())
    if measure!=saved:raise AssertionError('Metrics/runtime differ; rerun measure.py to inspect.')
    result=dict(scope='Finite verification, not a formal proof of universal metatheorems.',cases=len(cases),programs=len(PROGRAMS),complete_runs=len(rows),malformed_runs=len(malformed),guard_process_runs=2*len(guards),all_pass=all(r['ok'] for r in rows+malformed+guards),rows=rows,malformed=malformed,guards=guards,source_hashes={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in PROGRAMS})
    (ROOT/'evidence/validation.json').write_text(json.dumps(result,indent=2)+'\n')
    if not result['all_pass']:raise AssertionError('Failed checks: '+repr([r for r in rows+malformed+guards if not r['ok']]))
    return {k:v for k,v in result.items() if k not in ('rows','malformed','guards')}

if __name__=='__main__':print(json.dumps(verify(),indent=2))
