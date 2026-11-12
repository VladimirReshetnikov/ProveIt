"""Independent event-trace review of the disclosed implementation refinements."""
from pathlib import Path
import ast, copy, hashlib, io, json, sys, tokenize
ROOT = Path(__file__).resolve().parents[1] / 'checkers'
NATIVE = ['native_control.py', 'native_append_function.py', 'native_append_lambda.py']
STRICT = ['strict646_control.py', 'strict645_lambda.py']

def definition(name):
    tree = ast.parse((ROOT/name).read_text())
    tree.body = tree.body[:2]  # import json; c definition or c=lambda
    ns = {}
    exec(compile(tree,name,'exec'),ns)
    return ns

def trace(name, fixture, strict):
    payload = json.loads((ROOT/fixture).read_text())
    events=[]
    ns=definition(name)
    def pop():
        events.append(['pop',len(payload)-1,copy.deepcopy(payload[-1])])
        return payload.pop()
    ns['q']=pop
    code=ns['c'].__code__
    def profiler(frame,event,arg):
        if frame.f_code is code and event in ('call','return'):
            e=[event,copy.deepcopy(frame.f_locals['g']),copy.deepcopy(frame.f_locals['a']),frame.f_locals['k']]
            if strict:e.append(frame.f_locals['v'])
            events.append(e)
    goal=pop()
    sys.setprofile(profiler)
    try:
        value=ns['c']([0],goal,v=1) if strict else ns['c']([],goal)
    finally:
        sys.setprofile(None)
    return events, None if value is None else bool(value), len(payload)

reports=[]
for names,folder,strict in [(NATIVE,'fixtures/native/fixtures',False),(STRICT,'fixtures/strict/proofs',True)]:
    for case in ['computation_zero_local.json','transport_reflexivity_local.json','guarded_literal_equation_introduction_local.json']:
        runs=[trace(name,folder+'/'+case,strict) for name in names]
        assert all(r[0]==runs[0][0] and r[2]==runs[0][2] for r in runs),case
        assert all(r[1] is True for r in runs[1:])
        reports.append({'profile':'strict' if strict else 'native','fixture':folder+'/'+case,'programs':names,'events_per_program':len(runs[0][0]),'remaining_packets':runs[0][2],'matched':True})

skip={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.INDENT,tokenize.DEDENT,tokenize.NEWLINE,tokenize.NL,tokenize.COMMENT}
metrics=[]
for name in NATIVE+STRICT:
    raw=(ROOT/name).read_bytes();tree=ast.parse(raw);source=ast.unparse(tree)+'\n'
    metrics.append({'file':name,'tokens':sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(source).readline)),'ast_nodes':len(list(ast.walk(tree))),'normalized_bytes':len(source.encode()),'sha256':hashlib.sha256(raw).hexdigest()})
result={'python':sys.version,'scope':'Independent finite semantic-event comparison; supplements written all-traces induction','runs':sum(len(r['programs']) for r in reports),'cases':reports,'metrics':metrics}
out=Path(__file__).with_name('independent_trace_review.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'runs':result['runs'],'all_semantic_events_match':True,'metrics':metrics},indent=2))
