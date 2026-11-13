"""Offline validation of the input-derived clock against the frozen control.

The measured checker imports no part of this test/producer implementation.
Finite regression tests supplement the exact simulation argument in PROOF.txt.
"""
from pathlib import Path
import ast, copy, hashlib, io, json, random, subprocess, sys, tokenize
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parent
FILES={'control':HERE/'reference/retained_control.py','candidate':HERE/'code/checker.py','readable':HERE/'code/checker_readable.py'}

def compile_kernel(name):
    tree=ast.parse(FILES[name].read_text());nodes=[]
    for node in tree.body:
        if name=='readable':
            if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='packets' for t in node.targets):break
        elif isinstance(node,(ast.Import,ast.ImportFrom)):break
        nodes.append(node)
    return compile(ast.Module(body=nodes,type_ignores=[]),str(FILES[name]),'exec')
KERNELS={name:compile_kernel(name) for name in FILES}

def namespace(name):
    ns={};exec(KERNELS[name],ns);return ns

def run(name,document):
    ns=namespace(name)
    try:
        stack=json.loads(json.dumps(document,allow_nan=True))
        initial=len(stack)-1
        if name=='control':
            ns['q']=stack.pop;goal=ns['q']();ns['c']([[]],goal);floor=ns['k']
        elif name=='candidate':
            ns['p']=stack;goal=stack.pop();ns['n']=len(stack);ns['c']([[]],goal);floor=ns['k']()
        else:
            ns['packets']=stack;goal=stack.pop();ns['initial_count']=len(stack);ns['check']([[]],goal);floor=len(stack)-ns['initial_count']
        return {'accepted':True,'consumed':initial-len(stack),'floor':floor,'remaining':len(stack)}
    except Exception as exc:return {'accepted':False,'exception':type(exc).__name__}

def open_run(name,tree,floor=0,image=None,depth=0,has_image=False):
    ns=namespace(name)
    if name=='control':ns['k']=floor;op=ns['i']
    elif name=='candidate':ns.update(p=[None,None],n=2-floor);op=ns['i']
    else:ns.update(packets=[None,None],initial_count=2-floor);op=ns['opening']
    try:
        value=op(tree,image,depth) if has_image else op(tree,d=depth) if name!='readable' else op(tree,depth=depth)
        return True,value
    except Exception:return False,None

def term(a,n=0):
    if type(a)is bool:return a is True
    if type(a)is int:return a==1 or 3<=a<3+2*n and a%2==1
    return type(a)is list and (len(a)==1 and term(a[0],n) or len(a)==3 and term(a[0],n) and term(a[1],n) and term(a[2],n+1))
def formula(a,n=0):
    return type(a)is list and (len(a)==1 and formula(a[0],n+2) or len(a)==2 and term(a[0],n) and term(a[1],n))

def paths(value,p=()):
    yield p
    if type(value)is list:
        for j,x in enumerate(value):yield from paths(x,p+(j,))
def replace(value,path,new):
    if not path:return copy.deepcopy(new)
    result=copy.deepcopy(value);obj=result
    for j in path[:-1]:obj=obj[j]
    obj[path[-1]]=copy.deepcopy(new);return result

def measurements(path):
    raw=path.read_bytes();tree=ast.parse(raw);normalized=ast.unparse(tree)+'\n'
    skip={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
    return {'source_sha256':hashlib.sha256(raw).hexdigest(),'tokens':sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),'ast_nodes':len(list(ast.walk(tree))),'normalized_bytes':len(normalized.encode())}

def main():
    positives=json.loads((HERE/'fixtures/native_positives.json').read_text())['cases']
    capture=json.loads((HERE/'fixtures/capture_four.json').read_text())
    failures=[];counts={'exact_comparisons':0,'grammar_comparisons':0,'opener_comparisons':0,'false_export_mutations':0};baseline=[];cli=[]
    def compare(title,doc,expected=None):
        outcomes={name:run(name,doc) for name in FILES};counts['exact_comparisons']+=1
        accepted={x['accepted'] for x in outcomes.values()}
        good=len(accepted)==1 and (not next(iter(accepted)) or len({(x['consumed'],x['floor'],x['remaining']) for x in outcomes.values()})==1)
        if expected is not None:good=good and all(x['accepted']==expected for x in outcomes.values())
        if not good:failures.append({'kind':'run','name':title,'outcomes':outcomes,'expected':expected})
        return outcomes
    false_goals=[[1,[1]],[[1],1],[[[1]],1]]
    invalid_goals=[[3,1],[[3],[1]],[[5],[1]],[[1,3,1],1],[[1,1,5],1],[True,False],[1.0,1],None,{},'bad']
    values=[None,False,True,'','x',{},-100,-5,-2,-1,0,1,2,3,4,5,7,100,0.0,1.0,2.0,3.0,-1.0,-.5,.5,1.5,100.5,float('inf'),float('-inf'),float('nan')]
    for item in positives:
        name=item['name'];doc=item['certificate'];out=compare(name,doc,True);baseline.append({'name':name,'outcomes':out});cli.append((name,doc,True))
        for j,goal in enumerate(false_goals+invalid_goals):
            bad=doc[:-1]+[goal];compare(name+'_invalid_'+str(j),bad,False)
        for j,value in enumerate(values):compare(name+'_unused_'+str(j),[copy.deepcopy(value)]+doc,True)
        def true_alias(value):
            return [true_alias(x)for x in value]if type(value)is list else True if type(value)is int and value==1 else value
        compare(name+'_true_alias',true_alias(doc),True)
    compare('future_capture',capture,False);cli.append(('future_capture',capture,False))
    # Confirm this capture fixture exercises the scope guard, rather than merely
    # malformed packet arity. Never use this deliberately altered code as a checker.
    bad_source=FILES['candidate'].read_text().replace('k() <= a < d','a < d')
    bad_tree=ast.parse(bad_source);bad_nodes=[]
    for node in bad_tree.body:
        if isinstance(node,(ast.Import,ast.ImportFrom)):break
        bad_nodes.append(node)
    bad_ns={};exec(compile(ast.Module(body=bad_nodes,type_ignores=[]),'<deliberately_unguarded>','exec'),bad_ns)
    bad_data=copy.deepcopy(capture);bad_goal=bad_data.pop();bad_ns.update(p=bad_data,n=len(bad_data))
    try:bad_ns['c']([[]],bad_goal);unguarded_capture_accepts=True
    except Exception:unguarded_capture_accepts=False
    if not unguarded_capture_accepts:failures.append({'kind':'negative_control_did_not_trigger'})
    base=positives[0]['certificate']
    for j,record in enumerate([[],[0],[0,1],[0,1,2],[0,1,2,3,4],0,None,{},'bad']):
        bad=base[:-2]+[record]+base[-1:];compare('bad_record_'+str(j),bad,False);cli.append(('bad_record_'+str(j),bad,False))
    compare('missing_record',[base[-1]],False);cli.append(('missing_record',[base[-1]],False))
    # Public grammar remains exact despite moving its first scan before pop.
    rng=random.Random(20261113)
    def raw(depth):
        if depth<=0 or rng.random()<.55:return copy.deepcopy(rng.choice(values))
        return [raw(depth-1)for _ in range(rng.randrange(5))]
    samples=[raw(5)for _ in range(6000)]
    for n in range(6):
        for value in values:
            for pat in ([value,1],[[value],[1]],[[1,1,value],1]):
                obj=copy.deepcopy(pat)
                for _ in range(n):obj=[obj]
                samples.append(obj)
    samples += [x['certificate'][-1]for x in positives]
    for tree in samples:
        expected=bool(formula(tree));out={name:open_run(name,tree) for name in FILES};counts['grammar_comparisons']+=1
        if any(got[0]!=expected for got in out.values()):failures.append({'kind':'grammar','tree':tree,'expected':expected,'outcomes':repr(out)})
    # Floor snapshots agree at arbitrary depths, including malformed annotations.
    for floor in (0,-1,-5):
      for depth in (-3,-1,0,1,2,3,5,7):
       for value in values:
        for tree in (value,[value],[value,1],[1,1,value]):
         for image in (1,[1],-1,[-1],100.5,None):
            out={name:open_run(name,tree,floor,image,depth,True) for name in FILES};counts['opener_comparisons']+=1
            control=out['control']
            if any(other[0]!=control[0] or other[0] and other[1]!=control[1] for other in out.values()):failures.append({'kind':'opener','floor':floor,'depth':depth,'outcomes':repr(out)})
    # Mutate used fields and deep annotations; independently fix false public exports.
    for item in positives:
        doc=item['certificate'];ps=[(-2,j)for j in range(4)]
        choices=[p for p in paths(doc[:-1])if p];rng.shuffle(choices);ps += choices[:4]
        for pth in ps:
            for value in [None,False,True,{},'bad',0.0,1.0,-1.0,.5,100.5,0,1,-2,float('nan')]:
                mutant=replace(doc,pth,value);compare(item['name']+'_mutation',mutant)
                for goal in false_goals:
                    compare(item['name']+'_false_mutation',mutant[:-1]+[goal],False);counts['false_export_mutations']+=1
    # Complete standard-input and verdict checks, normal and optimized.
    for goal in false_goals+invalid_goals:cli.append(('false_or_invalid_public',base[:-1]+[goal],False))
    for j,value in enumerate(values):cli.append(('unused_json_'+str(j),[copy.deepcopy(value)]+positives[2]['certificate'],True))
    def process(job):
        name,title,doc,expected,opt=job
        done=subprocess.run([sys.executable,*(['-O']if opt else[]),str(FILES[name])],input=json.dumps(doc,allow_nan=True)+'\n',text=True,capture_output=True,timeout=10)
        accepted=done.returncode==0 and done.stdout=='ACCEPT\n'
        return {'checker':name,'name':title,'optimized':opt,'expected':expected,'accepted':accepted,'exit_code':done.returncode}
    jobs=[(name,title,doc,expected,opt)for title,doc,expected in cli for name in FILES for opt in (False,True)]
    with ThreadPoolExecutor(max_workers=8)as pool:processes=list(pool.map(process,jobs))
    failures.extend({'kind':'process',**x}for x in processes if x['accepted']!=x['expected'])
    receipt={'python':sys.version,'metrics':{name:measurements(path)for name,path in FILES.items()},'counts':counts,'baseline':baseline,'process_runs':len(processes),'processes':processes,'scope_guard_negative_control_accepts_false_capture':unguarded_capture_accepts,'failures':failures,'proof_status':'Finite tests supplement PROOF.txt; no new formal verification.'}
    (HERE/'evidence/verification.json').write_text(json.dumps(receipt,indent=2,allow_nan=True)+'\n')
    print(json.dumps({'metrics':receipt['metrics'],'counts':counts,'process_runs':len(processes),'failure_count':len(failures)},indent=2))
    if failures:raise SystemExit(1)
if __name__=='__main__':main()
