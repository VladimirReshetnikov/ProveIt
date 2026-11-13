"""Reproducible finite checks for the new native strict profiles.

Finite process tests supplement the written scope/translation arguments.
No conclusion about all accepted certificates is inferred by testing alone.
"""
from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import subprocess
import sys
import tokenize
from compile_direct_three import translate as translate_three
from compile_four_entry import translate as translate_four

ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'reference/fixtures'
OUT=ROOT/'code'
IGNORED={tokenize.ENCODING,tokenize.ENDMARKER,tokenize.NEWLINE,tokenize.NL,
         tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT}

def metrics(p):
    src=p.read_text();s=ast.unparse(ast.parse(src))+'\n'
    return {'tokens':sum(t.type not in IGNORED for t in tokenize.generate_tokens(io.StringIO(s).readline)),
            'ast_nodes':len(list(ast.walk(ast.parse(s)))),
            'normalized_bytes':len(s.encode()),
            'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}

def run(job):
    profile,name,doc,expected,optimized=job
    p=OUT/profile
    r=subprocess.run([sys.executable,*(['-O'] if optimized else []),str(p)],
                     input=json.dumps(doc),text=True,capture_output=True,timeout=20)
    accepted=r.returncode==0 and r.stdout=='ACCEPT\n'
    return {'profile':profile,'case':name,'optimized':optimized,'expected':expected,
            'accepted':accepted,'exit_code':r.returncode}

def main():
    configs=[('checker_tokens302.py','return','three_field'),
             ('checker_ast340.py','entry','three_field'),
             ('checker_bytes584.py','entry','four_field'),
             ('checker_entry_tokens304.py','entry','three_field')]
    source=json.loads((SOURCE/'terminal_cases.json').read_text())['cases']
    negatives=json.loads((SOURCE/'three_field_cases.json').read_text())['cases']
    positives=[c for c in source if c['expected']]
    jobs=[];family_counts={};compilation={}
    fixtures=ROOT/'certificates';fixtures.mkdir(exist_ok=True)
    for profile,schedule,kind in configs:
        cases=[];compiled=[]
        for c in positives:
            doc,stats=(translate_four(c['certificate']) if kind=='four_field'
                       else translate_three(c['certificate'],schedule))
            compiled.append({'name':c['name'],'certificate':doc,'stats':stats})
            cases.append((c['name'],doc,True))
            cases.append((c['name']+'_false_zero_one',doc[:-1]+[[1,[1]]],False))
        base=compiled[0]['certificate']
        for j,goal in enumerate([0,1,[],[0,1],[2,1],[3,1],[-1,1],[[0]],[[1]],
                                [1,1,1],[[],1],True,1.5,None,'x',{}]):
            cases.append(('invalid_public_'+str(j),base[:-1]+[goal],False))
        for j,bad in enumerate([None,True,False,1.5,'',{},'unused']):
            cases.append(('invalid_unused_'+str(j),[bad]+base,False))
        for j,bad in enumerate([[],[0],[0,1],[0,1,2,3,4],0,None]):
            cases.append(('bad_root_record_'+str(j),base[:-2]+[bad]+base[-1:],False))
        cases.append(('no_record',[base[-1]],False))
        if kind=='three_field':
            for n in negatives:
                if not n['expected']:
                    cases.append(('upstream_negative_'+n['name'],n['certificate'],False))
        capture=json.loads((ROOT/'diagnostics'/f'{kind}_witness_capture.json').read_text())
        cases.append(('new_witness_capture',capture,False))
        # Earlier entry allocation permits -1 as an arbitrary parameter, but
        # changing the attempted captured name cannot prove this false goal.
        def rebind(t,n):
            if type(t)is list:return [rebind(x,n) for x in t]
            return n if t==-2 else t
        for n in [-1,-3,-4,-5]:
            cases.append(('witness_capture_name_'+str(n),rebind(capture,n),False))
        family_counts[profile]=len(cases)
        compilation[profile]=[{'name':c['name'],'stats':c['stats']} for c in compiled]
        (fixtures/(profile[:-3]+'.json')).write_text(json.dumps({'cases':[
            {'name':n,'certificate':d,'expected':e} for n,d,e in cases]},indent=1)+'\n')
        jobs.extend((profile,n,d,e,o) for n,d,e in cases for o in (False,True))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(run,jobs))
    failures=[r for r in results if r['accepted']!=r['expected']]
    diagnostics=[]
    for kind in ['three_field','four_field']:
        p=ROOT/'diagnostics'/f'UNSOUND_{kind}.py'
        doc=json.loads((ROOT/'diagnostics'/f'{kind}_witness_capture.json').read_text())
        for optimized in [False,True]:
            r=subprocess.run([sys.executable,*(['-O'] if optimized else []),str(p)],input=json.dumps(doc),text=True,capture_output=True,timeout=20)
            accepted=r.returncode==0 and r.stdout=='ACCEPT\n'
            diagnostics.append({'kind':kind,'optimized':optimized,'deliberately_unsound':True,'accepted_false_goal':accepted})
            if not accepted:failures.append({'diagnostic':kind,'optimized':optimized,'error':'expected diagnostic attack acceptance missing'})
    receipt={'python':sys.version,'metrics':{p:metrics(OUT/p) for p,_,_ in configs},
             'cases_per_profile':family_counts,'process_runs':len(results)+len(diagnostics),
             'failures':failures,'compilation':compilation,'diagnostics':diagnostics,'results':results}
    (ROOT/'evidence/verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('results','compilation')},indent=2))
    if failures:raise SystemExit(1)

if __name__=='__main__':main()
