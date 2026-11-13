"""Independent state-trace review of the continuation loop transformation."""
import ast
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

root=Path(__file__).resolve().parent.parent
control=root/'benchmarks/strict_tokens306.py'
candidate=root/'code/checker304.py'
cases=json.loads((root/'fixtures/three_field_cases.json').read_text())['cases']
selected=[case for case in cases if case['expected'] or case['name'].startswith('raw_attack_')]
omit={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.INDENT,tokenize.DEDENT,tokenize.NEWLINE,tokenize.NL,tokenize.COMMENT}

def metrics(path):
    tree=ast.parse(path.read_text())
    source=ast.unparse(tree)+'\n'
    return dict(tokens=sum(t.type not in omit for t in tokenize.generate_tokens(io.StringIO(source).readline)),ast_nodes=sum(1 for _ in ast.walk(tree)),normalized_bytes=len(source.encode()),sha256=hashlib.sha256(source.encode()).hexdigest())

def run(path,data):
    tree=ast.parse(path.read_text())
    function=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='c')
    condition=function.body[1]
    if isinstance(condition,ast.If):
        membership=condition.test
    else:
        assert isinstance(condition,ast.While)
        assert isinstance(condition.test,ast.Compare)
        membership=ast.Compare(left=condition.test.left,ops=[ast.In()],comparators=condition.test.comparators)
    logged=ast.Call(func=ast.Name(id='log',ctx=ast.Load()),args=[ast.Name(id=name,ctx=ast.Load()) for name in ('g','a','k')]+[membership],keywords=[])
    condition.test=logged if isinstance(condition,ast.If) else ast.UnaryOp(op=ast.Not(),operand=logged)
    module=ast.fix_missing_locations(ast.Module(body=[function],type_ignores=[]))
    stack=json.loads(json.dumps(data))
    trace=[]
    def log(g,a,k,contained):
        state=json.dumps([g,a,k,contained,len(stack)],separators=(',',':'))
        trace.append(hashlib.sha256(state.encode()).hexdigest())
        return contained
    namespace={'q':stack.pop,'log':log}
    exec(compile(module,str(path),'exec'),namespace)
    error=None
    try:
        namespace['c']([],stack.pop())
        accepted=True
    except Exception as exc:
        accepted=False
        error=type(exc).__name__
    return {'accepted':accepted,'error_type':error,'remaining_packets':len(stack),'trace':trace}

records=[]
for case in selected:
    old=run(control,case['certificate'])
    new=run(candidate,case['certificate'])
    records.append({'case':case['name'],'matches':old==new,'nodes':len(old['trace']),'accepted':new['accepted']})
result={'status':'PASS' if all(r['matches'] for r in records) else 'FAIL','python':platform.python_version(),'control':metrics(control),'candidate':metrics(candidate),'cases':len(records),'nodes':sum(r['nodes'] for r in records),'records':records,'scope':'Instrumented procedure-entry versus loop-iteration contexts, goals, floors, membership results, remaining packet counts, and exception classes. Finite evidence only.'}
(root/'evidence/loop_trace_review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if result['status']!='PASS':raise SystemExit(1)
