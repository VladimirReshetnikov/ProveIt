"""Independent focused audit of retained typing and lazy ignored fields.
This is an executable regression check, not a formal soundness proof.
"""
from pathlib import Path
import ast, hashlib, json, subprocess, sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CONTROL=ROOT/'reference/control_intrinsic.py'
FILES={'control':CONTROL,'retained_lazy':ROOT/'code/checker.py'}

def kernel(path):
    tree=ast.parse(path.read_text())
    nodes=[node for node in tree.body if isinstance(node,ast.FunctionDef) or isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ('k','i') for t in node.targets)]
    ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path),'exec'),ns)
    return ns

def typed(value):
    return type(value) in (int,bool) or type(value) is list and all(map(typed,value))

def opening(ns,a,image=None,depth=3,floor=-5,missing=False):
    ns['k']=floor
    try:
        value=ns['i'](a,d=depth) if missing else ns['i'](a,image,depth)
        return {'accepted':True,'typed_output':typed(value),'value':value}
    except Exception as exc:return {'accepted':False,'exception':type(exc).__name__}

results={'sources':{name:{'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()} for name,path in FILES.items()},'opener':[],'missing_image':{},'processes':[],'failures':[]}
spaces={name:kernel(path) for name,path in FILES.items()}
float_holes=[100.5,-100.5,float('nan'),float('inf'),float('-inf')]
for value in float_holes:
    row={'source':repr(value),'image':1,'depth':3,'floor':-5,'outcomes':{name:opening(ns,value,1) for name,ns in spaces.items()}}
    results['opener'].append(row)
    if row['outcomes']['control']['accepted'] or any(not row['outcomes'][name]['accepted'] or row['outcomes'][name].get('value')!=1 for name in ('retained_lazy',)):results['failures'].append(row)
# A retained integral float must not become an eigenvariable or numeral.
for value in (-1.0,0.0,1.0,2.0):
    row={'source':repr(value),'image':1,'depth':3,'floor':-5,'outcomes':{name:opening(ns,value,1) for name,ns in spaces.items()}}
    results['opener'].append(row)
    if any(x['accepted'] for x in row['outcomes'].values()):results['failures'].append(row)
for name,ns in spaces.items():
    checks=0;accepted=[]
    for floor in (0,-1,-5,-100):
        for depth in (-3,-1,0,1,2,3,5,7):
            for value in float_holes+[-1.0,0.0,1.0,2.0,3.0]:
                for source in (value,[value],[value,1],[1,1,value],[[value]]):
                    checks+=1
                    got=opening(ns,source,depth=depth,floor=floor,missing=True)
                    if got['accepted']:accepted.append({'source':repr(source),'floor':floor,'depth':depth,'result':got})
    results['missing_image'][name]={'checks':checks,'unexpected_acceptance':accepted}
    results['failures'].extend(accepted)

# Constant D matrix: the witness and unmatched source never affect its meaning.
goal=[[[1,1,1],1]]
def theorem(source=0,witness=1):return [[0,1,1,[]],[0,1,1,[]],[source,0,witness,[]],goal]
capture=json.loads((ROOT/'tests/fixtures/capture_four.json').read_text())
cases=[('canonical_constant_D',theorem(),{'control':True,'retained_lazy':True,'retained_split':True}),
       ('ignored_null_source',theorem(source=None),{'control':False,'retained_lazy':True,'retained_split':True}),
       ('ignored_float_source',theorem(source=0.0),{'control':False,'retained_lazy':True,'retained_split':True}),
       ('unused_float_witness',theorem(witness=100.5),{'control':False,'retained_lazy':True,'retained_split':True}),
       ('unused_nan_witness',theorem(witness=float('nan')),{'control':False,'retained_lazy':True,'retained_split':True}),
       ('future_capture',capture,{name:False for name in FILES})]
false_doc=theorem(source=None);false_doc[-1]=[1,[1]]
cases.append(('ignored_data_cannot_prove_zero_one',false_doc,{name:False for name in FILES}))
for title,doc,expected in cases:
    for name,path in FILES.items():
        for optimized in (False,True):
            command=[sys.executable]+(['-O'] if optimized else [])+[str(path)]
            run=subprocess.run(command,input=json.dumps(doc,allow_nan=True)+'\n',capture_output=True,text=True,timeout=5)
            accepted=run.returncode==0 and run.stdout=='ACCEPT\n'
            row={'case':title,'checker':name,'optimized':optimized,'expected':expected[name],'accepted':accepted,'exit_code':run.returncode}
            results['processes'].append(row)
            if accepted!=expected[name]:results['failures'].append(row)
results['summary']={'opener_cases':len(results['opener']),'missing_image_checks':sum(x['checks'] for x in results['missing_image'].values()),'complete_process_runs':len(results['processes']),'unexpected_outcomes':len(results['failures'])}
(ROOT/'evidence/retained_validation_receipt.json').write_text(json.dumps(results,indent=2)+'\n')
(ROOT/'examples/lazy_ignored_source.json').write_text(json.dumps(theorem(source=None))+'\n')
(ROOT/'examples/float_hole_unused_witness.json').write_text(json.dumps(theorem(witness=100.5))+'\n')
print(json.dumps(results['summary'],indent=2))
assert not results['failures']
