"""Independent, deterministic validation of intrinsic-JSON proper binder checker.
The in-process harness removes only fixed I/O statements and supplies q=list.pop.
Full process checks separately cover the actual submitted JSON reader and -O.
No theorem search or checker implementation is imported into the measured module.
"""
from pathlib import Path
import ast, copy, hashlib, io, json, math, random, subprocess, sys, tokenize
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parent
FIX=HERE/'fixtures/native_positives.json'
CHECK=HERE.parent/'code/checker.py'
SOURCE=CHECK.read_text(); TREE=ast.parse(SOURCE)
PREFIX=[]
for n in TREE.body:
    if isinstance(n,(ast.Import,ast.ImportFrom)):break
    PREFIX.append(n)
KERNEL=compile(ast.Module(body=PREFIX,type_ignores=[]),str(CHECK),'exec')
# Independent grammar: exact integers, with True explicitly decoded as zero code 1.
def term(a,n=0):
    if type(a) is bool:return a is True
    if type(a) is int:return a==1 or 3<=a<3+2*n and a%2==1
    return type(a) is list and (len(a)==1 and term(a[0],n) or len(a)==3 and term(a[0],n) and term(a[1],n) and term(a[2],n+1))
def formula(a,n=0):
    return type(a) is list and (len(a)==1 and formula(a[0],n+2) or len(a)==2 and term(a[0],n) and term(a[1],n))
def typed(a):
    return type(a) in (int,bool) or type(a) is list and all(map(typed,a))
def kernel_run(doc):
    ns={};exec(KERNEL,ns)
    try:
        # Preserve parsing identity (notably JSON NaN); same receiver as real reader.
        data=json.loads(json.dumps(doc,allow_nan=True));ns['q']=data.pop
        ns['c']([[]],ns['q']())
        return True
    except Exception:return False
def open_run(a,k=0,t=None,d=0,has_image=False):
    ns={};exec(KERNEL,ns);ns['k']=k
    try:
        y=ns['i'](a,t,d) if has_image else ns['i'](a,d=d)
        return True,y
    except Exception:return False,None

def paths(v,p=()):
    yield p
    if type(v) is list:
        for j,x in enumerate(v):yield from paths(x,p+(j,))
def replaced(v,p,x):
    if not p:return copy.deepcopy(x)
    r=copy.deepcopy(v);w=r
    for j in p[:-1]:w=w[j]
    w[p[-1]]=copy.deepcopy(x);return r

def main():
    positive=json.loads(FIX.read_text())['cases']
    cases=[]
    for c in positive:
        cases.append(c)
        cases.append({'name':c['name']+'_false_zero_one','certificate':c['certificate'][:-1]+[[1,[1]]],'expected':False})
        cases.append({'name':c['name']+'_false_one_zero','certificate':c['certificate'][:-1]+[[[1],1]],'expected':False})
    base=positive[0]['certificate']
    for j,a in enumerate([0,1,[],[0,1],[2,1],[3,1],[-1,1],[[3],[1]],[[5],[1]],[[1,3,1],1],[[1,1,5],1],[1,1,1],[[],1],True,1.5,None,'x',{}]):
        cases.append({'name':'invalid_public_'+str(j),'certificate':base[:-1]+[a],'expected':False})
    for j,a in enumerate([None,True,False,1.5,'',{},'unused']):
        cases.append({'name':'invalid_unused_'+str(j),'certificate':[a]+base,'expected':False})
    for j,a in enumerate([[],[0],[0,1],[0,1,2,3,4],0,None]):
        cases.append({'name':'malformed_root_packet_'+str(j),'certificate':base[:-2]+[a]+base[-1:],'expected':False})
    cases.append({'name':'missing_root_packet','certificate':[base[-1]],'expected':False})
    cases.append({'name':'future_witness_capture','certificate':json.loads((FIX.parent/'capture_four.json').read_text()),'expected':False})
    failures=[];baseline=[];proc=[]
    for c in cases:
        expected=True if c['name'].startswith('invalid_unused_') else c['expected']
        got=kernel_run(c['certificate'])
        baseline.append({'name':c['name'],'expected':expected,'accepted':got})
        if got!=expected:failures.append({'kind':'baseline','name':c['name'],'expected':expected,'accepted':got})
        proc.append({'name':c['name'],'certificate':c['certificate'],'expected':expected})
    print('Baseline completed',len(baseline),flush=True)
    # Exact public grammar is independently checked against sorted/binding recursion.
    rng=random.Random(20261113)
    scalars=[None,False,True,'','a','ab',{}, {'x':0},-100,-4,-3,-2,-1,0,1,2,3,4,5,6,7,9,1.0,2.0,3.0,-1.0,-.5,.5,1.5,2.5,3.5,float('inf'),float('-inf'),float('nan')]
    def raw(depth):
        if depth<=0 or rng.random()<.52:return copy.deepcopy(rng.choice(scalars))
        return [raw(depth-1) for _ in range(rng.randrange(5))]
    samples=[raw(5) for _ in range(12000)]
    for n in range(7):
        for a in scalars:
            for pattern in ([a,1],[[a],[1]],[[1,1,a],1]):
                x=copy.deepcopy(pattern)
                for _ in range(n):x=[x]
                samples.append(x)
    for c in positive:
        samples.append(c['certificate'][-1])
        def b1(x):return True if type(x)is int and x==1 else [b1(t)for t in x]if type(x)is list else x
        samples.append(b1(c['certificate'][-1]))
    grammar=0
    for x in samples:
        expected=bool(formula(x));got,y=open_run(x)
        grammar+=1
        if got!=expected or got and not typed(y):failures.append({'kind':'grammar','goal':x,'expected':expected,'accepted':got})
    print('Grammar completed',grammar,flush=True)
    # Opener can only visit int/bool leaves, including explicit holes.
    opener_runs=0;opener_failures=0
    for k in (0,-1,-2,-6):
      for d in (0,1,2,3,4,5,7,9):
       for a in scalars+[[],[1],[3], [1,1,3], [1,2,3,4], [1.0], [float('nan')]]:
        for image in (1,3,-1,[],[1],.5,1.0,'',None,{}):
            got,y=open_run(a,k,image,d,True);opener_runs+=1
            if got and (not typed(a) or not typed(y)):
                opener_failures+=1;failures.append({'kind':'opener_active_type','a':a,'image':image,'k':k,'d':d})
    print('Opener completed',opener_runs,flush=True)
    # Positive true aliases and arbitrary unused JSON payload are intentionally admitted.
    extra_positive=[]
    for c in positive:
        def b1(x):return True if type(x)is int and x==1 else [b1(t)for t in x]if type(x)is list else x
        variants=[('true_alias',b1(c['certificate']))]
        for j,x in enumerate(scalars):variants.append(('unused_'+str(j),[copy.deepcopy(x)]+c['certificate']))
        for tag,doc in variants:
            got=kernel_run(doc)
            extra_positive.append({'name':c['name']+'_'+tag,'accepted':got})
            if not got:failures.append({'kind':'intended_positive','name':c['name']+'_'+tag})
        if c['name'] in ('computation_zero_local','guarded_induction_with_used_hypothesis_local'):
            proc.append({'name':c['name']+'_true_alias','certificate':b1(c['certificate']),'expected':True})
    print('Positive aliases completed',len(extra_positive),flush=True)
    # Focused mutation campaign: used root fields, deeper scalar fields, scope attacks,
    # and fixed false/invalid export goals. Only these semantic rejections are asserted.
    false_goals=[[1,[1]],[[1],1],[[[1]],1]]
    invalid_goals=[[1.0,1],[True,False],[3,1],[[3],[1]],[[5],[1]],[[1,3,1],1],None,{},'a']
    adversaries=0;acc_false=0;positive_after_mutation=0;accepted_examples=[]
    mutations=[None,False,True,'','a',{}, {'x':0},0.0,1.0,2.0,3.0,-1.0,-.25,-1.5,.5,1.5,2.5,float('inf'),float('-inf'),float('nan')]
    for c in positive:
        base=c['certificate']
        packet=base[-2]
        rootpaths=[(-2,j)for j in range(len(packet))]+[(-2,)]
        # Check actual fields and up to 8 randomly selected deep leaves from all proof packets.
        ps=[p for p in paths(base[:-1]) if p]
        rng.shuffle(ps);rootpaths += ps[:8]
        for p in rootpaths:
            for v in mutations:
                mutant=replaced(base,p,v)
                # Distinct positive outcomes are evidence for broader input acceptance, not errors.
                accepted_original=kernel_run(mutant)
                positive_after_mutation+=accepted_original
                if accepted_original and len(accepted_examples)<20:
                    accepted_examples.append({'name':c['name'],'path':list(p),'value':v})
                for target in false_goals:
                    bad=mutant[:-1]+[target];got=kernel_run(bad);adversaries+=1
                    if got:
                        acc_false+=1;failures.append({'kind':'false_export','case':c['name'],'path':list(p),'value':v,'target':target})
        for target in invalid_goals:
            got=kernel_run(base[:-1]+[target]);adversaries+=1
            if got:failures.append({'kind':'invalid_export','case':c['name'],'target':target})
    print('Mutation campaign completed',adversaries,flush=True)
    # Future eigenvariable capture fixture plus nonintegral parameter alterations.
    cap=json.loads((FIX.parent/'capture_four.json').read_text())
    capture_results=[]
    for j,delta in enumerate((0,.25,-.25,.5,-.5)):
        def alter(v):return v+delta if type(v)is int and v<0 else [alter(x)for x in v]if type(v)is list else v
        doc=alter(cap);got=kernel_run(doc);capture_results.append({'delta':delta,'accepted':got})
        if got:failures.append({'kind':'scope_capture','delta':delta})
        proc.append({'name':'capture_delta_'+str(j),'certificate':doc,'expected':False})
    # Full parser/CLI comparison normal and optimized, including arbitrary junk and NaN prefix.
    for j,v in enumerate(scalars):
        proc.append({'name':'full_reader_unused_'+str(j),'certificate':[copy.deepcopy(v)]+positive[3]['certificate'],'expected':True})
    def run(job):
        c,optimized=job
        r=subprocess.run([sys.executable,*(['-O']if optimized else[]),str(CHECK)],input=json.dumps(c['certificate'],allow_nan=True),text=True,capture_output=True,timeout=10)
        got=r.returncode==0 and r.stdout=='ACCEPT\n'
        return {'name':c['name'],'optimized':optimized,'expected':c['expected'],'accepted':got,'exit_code':r.returncode}
    with ThreadPoolExecutor(max_workers=8)as ex:processes=list(ex.map(run,((c,o)for c in proc for o in(False,True))))
    failures.extend({'kind':'process',**x}for x in processes if x['expected']!=x['accepted'])
    ns=ast.unparse(TREE)+'\n';skip={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
    metrics={'tokens':sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(ns).readline)),'ast_nodes':len(list(ast.walk(TREE))),'normalized_bytes':len(ns.encode())}
    receipt={'candidate_sha256':hashlib.sha256(CHECK.read_bytes()).hexdigest(),'python':sys.version,'metrics':metrics,'baseline_cases':baseline,'public_grammar_comparisons':grammar,'intrinsic_opener_checks':opener_runs,'intrinsic_opener_type_failures':opener_failures,'intended_positive_variants':len(extra_positive),'positive_variants_failed':sum(not x['accepted']for x in extra_positive),'false_or_invalid_export_mutations':adversaries,'false_exports_accepted':acc_false,'mutated_original_goal_acceptances':positive_after_mutation,'accepted_mutation_examples':accepted_examples,'capture_results':capture_results,'process_runs':len(processes),'process_results':processes,'failures':failures,'claim_boundary':'Finite tests supplement the written all-input soundness proof. Deliberately malformed certificates may still prove true conclusions; only semantic false exports and invalid public goals are universally expected to reject.'}
    (HERE/'verification.json').write_text(json.dumps(receipt,indent=2,allow_nan=True)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('baseline_cases','process_results','accepted_mutation_examples')},indent=2,allow_nan=True))
    if failures:raise SystemExit(1)
if __name__=='__main__':main()
