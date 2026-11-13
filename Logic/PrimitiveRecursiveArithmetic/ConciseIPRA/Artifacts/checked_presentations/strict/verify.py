"""Recompute complete-source sizes and execute fixed positive/negative fixtures."""
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
from translate_terminal import convert

ROOT=Path(__file__).resolve().parent

def metrics(path):
    raw=path.read_bytes();source=raw.decode();tree=ast.parse(source);normalized=(ast.unparse(tree)+'\n').encode()
    excluded={tokenize.ENCODING,tokenize.COMMENT,tokenize.NL,tokenize.NEWLINE,tokenize.INDENT,tokenize.DEDENT,tokenize.ENDMARKER}
    return {'file':str(path.relative_to(ROOT)),'tokens':sum(t.type not in excluded for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)), 'ast_nodes':sum(1 for _ in ast.walk(tree)), 'normalized_bytes':len(normalized),'gzip9_bytes':len(gzip.compress(normalized,compresslevel=9,mtime=0)),'sha256':hashlib.sha256(raw).hexdigest()}

def check(task):
    c,checker,optimized=task
    command=[sys.executable]+(['-O'] if optimized else [])+[str(ROOT/checker)]
    r=subprocess.run(command,input=(ROOT/c['file']).read_bytes(),capture_output=True,timeout=12)
    accepted=r.returncode==0 and r.stdout==b'ACCEPT\n'
    return {'file':c['file'],'checker':checker,'optimized':optimized,'expected':c['expected'],'accepted':accepted,'passed':accepted==c['expected'],'exit':r.returncode,**({'stderr_tail':r.stderr.decode(errors='replace')[-500:]} if accepted!=c['expected'] else {})}

def main():
    sizes=[metrics(p) for d in ['code','controls'] for p in sorted((ROOT/d).glob('*.py'))]
    cases=json.loads((ROOT/'fixtures/cases.json').read_text())
    tasks=[(c,p,opt) for c in cases for p in c['checkers'] for opt in (False,True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        runs=list(pool.map(check,tasks))
    translations=[]
    for item in json.loads((ROOT/'evidence/translations.json').read_text()):
        regenerated,stats=convert(json.loads((ROOT/item['source']).read_text()))
        ok=regenerated==json.loads((ROOT/item['target']).read_text())
        translations.append({'source':item['source'],'target':item['target'],'passed':ok,'statistics':stats})
    # This table is the regression for the real compound-progress dispatch bug
    # caught while deriving the terminal profile. No compound root may select
    # progress when m=0, for any supplied marker in this finite boundary set.
    markers=[0,1,2,3,-1,[],[0],[1],[1,2]]
    candidate_ast=ast.parse((ROOT/'code/strict_bytes.py').read_text())
    selectors=[n for n in ast.walk(candidate_ast)
               if isinstance(n,ast.Call) and isinstance(n.func,ast.Name)
               and n.func.id=='any' and len(n.args)==1
               and isinstance(n.args[0],ast.Tuple) and len(n.args[0].elts)==2
               and isinstance(n.args[0].elts[0],ast.Name)
               and n.args[0].elts[0].id=='m']
    if len(selectors)!=1:
        raise ValueError('Could not identify the actual candidate mode selector')
    selector=compile(ast.Expression(body=selectors[0]),'<actual candidate selector>','eval')
    modes=[]
    for arity in (1,2,3):
        for u in markers:
            for m in (0,[],[1]):
                actual=eval(selector,{'__builtins__':{},'any':any,'len':len},
                            {'a':[0]*arity,'u':u,'m':m})
                expected=bool(m) or (arity==u==2)
                modes.append({'arity':arity,'marker':u,'major':m,'progress':actual,
                              'expected':expected,'passed':actual==expected})
    mode_ok=all(r['passed'] for r in modes)
    result={'python':sys.version,'metrics':sizes,'process_runs':len(runs),'fixture_files':len({r['file'] for r in runs}),'failed_runs':sum(not r['passed'] for r in runs),'translated':len(translations),'translation_failures':sum(not r['passed'] for r in translations),'mode_boundary_ok':mode_ok,'mode_boundary':modes,'runs':runs,'translations':translations}
    (ROOT/'evidence/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'evidence/metrics.json').write_text(json.dumps({'python':sys.version,'metrics':sizes},indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('runs','translations','mode_boundary')},indent=2))
    if result['failed_runs'] or result['translation_failures'] or not mode_ok:
        for r in runs:
            if not r['passed']:print(json.dumps(r))
        raise SystemExit(1)

if __name__=='__main__':main()
