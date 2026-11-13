import ast, concurrent.futures, copy, hashlib, io, json, pathlib, subprocess, sys, tokenize
ROOT = pathlib.Path(__file__).resolve().parents[1]
UP = ROOT
SKIP={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}
def metrics(path):
    src=path.read_text(); tree=ast.parse(src); norm=ast.unparse(tree)+'\n'
    return {'tokens':sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(norm).readline)), 'ast_nodes':len(list(ast.walk(tree))), 'bytes':len(norm.encode()),'sha256':hashlib.sha256(norm.encode()).hexdigest()}
def translate(cert, fields):
    cert=copy.deepcopy(cert)
    if type(cert) is not list: return cert
    for r in cert[:-1]:
        if type(r) is list and len(r)==fields and type(r[0]) is int and r[0]==0:
            if fields==4 or not r[1]: r[0]=[]
    return cert
def run(job):
    path,case,opt,fields=job
    cert=translate(case['certificate'],fields)
    proc=subprocess.run([sys.executable,'-I','-S','-B',*(['-O'] if opt else []),str(path)],input=json.dumps(cert),text=True,capture_output=True,timeout=15)
    ok=proc.returncode==0 and proc.stdout=='ACCEPT\n'
    return {'file':path.name,'case':case['name'],'optimized':opt,'accepted':ok,'expected':case['expected'],'error':proc.stderr.splitlines()[-1] if proc.stderr else ''}
def main():
    three=json.loads((UP/'fixtures/three_field_cases.json').read_text())['cases']
    four=json.loads((UP/'fixtures/four_field_cases.json').read_text())['cases']
    fs=[('code/checker_tokens304.py',three,3),('code/checker_joint311.py',three,3),('code/checker_ast345.py',four,4)]
    jobs=[(ROOT/name,c,o,f) for name,cs,f in fs for c in cs for o in [False,True]]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: results=list(ex.map(run,jobs))
    failures=[r for r in results if r['accepted']!=r['expected']]
    receipt={'python':sys.version,'executions':len(results),'fixture_counts':{'three_field':len(three),'four_field':len(four)},'metrics':{n:metrics(ROOT/n) for n,_,_ in fs},'failures':failures,'results':results}
    (ROOT/'evidence/validation334.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
    if failures: raise SystemExit(1)
if __name__=='__main__': main()
