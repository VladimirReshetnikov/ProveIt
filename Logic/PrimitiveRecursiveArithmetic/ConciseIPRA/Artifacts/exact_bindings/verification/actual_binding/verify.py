"""Recompile typed source derivations into the proper-binder protocol."""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import random
import subprocess
import sys
import tokenize
from compile_three import translate as three
from compile_four import translate as four

HERE=Path(__file__).resolve().parent
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,
      tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}

def term(a,n=0):
    if type(a) is int:
        return a==1 or 3<=a<3+2*n and a%2==1
    return type(a) is list and (len(a)==1 and term(a[0],n) or
            len(a)==3 and term(a[0],n) and term(a[1],n) and term(a[2],n+1))

def formula(a,n=0):
    return type(a) is list and (len(a)==1 and formula(a[0],n+2) or
            len(a)==2 and all(term(b,n) for b in a))

def measure(path):
    raw=path.read_bytes();n=ast.unparse(ast.parse(raw))+'\n'
    return {'tokens':sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(n).readline)),
            'ast_nodes':len(list(ast.walk(ast.parse(n)))),'normalized_bytes':len(n.encode()),
            'sha256':hashlib.sha256(raw).hexdigest()}

def main():
    source=json.loads((HERE/'fixtures/source_cases.json').read_text())['cases']
    positives=[c for c in source if c['expected']]
    jobs=[];compiled={};grammars={}
    configs=[('proper_tokens.py',three),('proper_bytes.py',four),('proper_nodes.py',lambda doc:three(doc,'entry'))]
    for profile,compiler in configs:
        cases=[];comp=[]
        for c in positives:
            doc,stats=compiler(c['certificate'])
            if not formula(doc[-1]):
                raise ValueError(('noncanonical compiled goal',c['name']))
            comp.append({'name':c['name'],'certificate':doc,'stats':stats})
            cases.append({'name':c['name'],'certificate':doc,'expected':True})
            cases.append({'name':c['name']+'_false_zero_one','certificate':doc[:-1]+[[1,[1]]],'expected':False})
            cases.append({'name':c['name']+'_false_one_zero','certificate':doc[:-1]+[[[1],1]],'expected':False})
        base=comp[0]['certificate']
        for j,a in enumerate([0,1,[],[0,1],[2,1],[3,1],[-1,1],[[3],[1]],[[5],[1]],
                              [[1,3,1],1],[[1,1,5],1],[1,1,1],[[],1],True,1.5,None,'x',{}]):
            if formula(a):
                raise ValueError(('negative syntax fixture became canonical',a))
            cases.append({'name':'invalid_public_'+str(j),'certificate':base[:-1]+[a],'expected':False})
        for j,bad in enumerate([None,True,False,1.5,'',{},'unused']):
            cases.append({'name':'invalid_unused_'+str(j),'certificate':[bad]+base,'expected':False})
        for j,bad in enumerate([[],[0],[0,1],[0,1,2,3,4],0,None]):
            cases.append({'name':'malformed_root_packet_'+str(j),'certificate':base[:-2]+[bad]+base[-1:],'expected':False})
        cases.append({'name':'missing_root_packet','certificate':[base[-1]],'expected':False})
        capture={'proper_tokens.py':'three','proper_bytes.py':'four','proper_nodes.py':'three_entry'}[profile]
        cases.append({'name':'future_witness_capture','certificate':json.loads((HERE/'fixtures'/('capture_'+capture+'.json')).read_text()),'expected':False})
        (HERE/'fixtures'/(profile[:-3]+'.json')).write_text(json.dumps({'cases':cases},indent=1)+'\n')
        compiled[profile]=[{'name':c['name'],'goal':c['certificate'][-1],'stats':c['stats']} for c in comp]
        for c in cases:
            for optimized in [False,True]:jobs.append((profile,c,optimized))
        tree=ast.parse((HERE/profile).read_text())
        node=next(x for x in tree.body if isinstance(x,ast.Assign) and any(isinstance(t,ast.Name)and t.id=='i' for t in x.targets))
        n={'k':0,'v':1,'c':lambda *args:None}
        exec(compile(ast.Module(body=[node],type_ignores=[]),'<public-opener>','exec'),n)
        grammars[profile]=n['i']
    rng=random.Random(132026)
    def raw(depth):
        if not depth or rng.random()<.45:return rng.randrange(-4,17)
        return [raw(depth-1) for _ in range(rng.randrange(5))]
    samples=[raw(5)for _ in range(10000)]
    for depth in range(8):
        for a in range(-2,2*depth+10):
            x=[[a],[1]]
            for _ in range(depth):x=[x]
            samples.append(x)
    gm=[]
    for x in samples:
        expected=bool(formula(x))
        for profile,op in grammars.items():
            try:
                y=op(x);got=True
            except Exception:got=False;y=None
            if got!=expected or got and y!=x:gm.append({'profile':profile,'goal':x,'expected':expected,'returned':y})
    def run(job):
        profile,c,optimized=job
        p=subprocess.run([sys.executable,*(['-O']if optimized else[]),str(HERE/profile)],input=json.dumps(c['certificate']),text=True,capture_output=True,timeout=20)
        accepted=p.returncode==0 and p.stdout=='ACCEPT\n'
        return {'profile':profile,'case':c['name'],'optimized':optimized,'expected':c['expected'],'accepted':accepted,'exit_code':p.returncode}
    with concurrent.futures.ThreadPoolExecutor(max_workers=8)as pool:runs=list(pool.map(run,jobs))
    failures=[r for r in runs if r['expected']!=r['accepted']]
    receipt={'python':sys.version,'metrics':{p:measure(HERE/p)for p,_ in configs},
             'source_positive_derivations':len(positives),'compiled':compiled,
             'grammar_comparisons':len(samples)*len(grammars),'grammar_mismatches':gm,
             'process_runs':len(runs),'failures':failures,'results':runs,
             'claim_boundary':'Typed source derivations are decoded and recompiled. Arbitrary flat raw bytecode is not translated. Finite evidence supplements the written proper-binder simulation.'}
    (HERE/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in ('results','compiled')},indent=2))
    if failures or gm:raise SystemExit(1)

if __name__=='__main__':main()
