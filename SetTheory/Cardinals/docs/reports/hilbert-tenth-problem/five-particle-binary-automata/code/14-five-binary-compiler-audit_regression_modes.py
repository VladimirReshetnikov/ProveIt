"""Run independent regressions against normal and optimized compiler imports.

In -O mode, compile the audit entry point with optimize=0 so its assertions
remain active, while its imported compiler/frontend run under actual -O.
"""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).parent
SCRIPTS=('audit_independent.py','audit_literal_boundaries.py','audit_frontend_independent.py')
BOOTSTRAP="""import pathlib,sys
p=pathlib.Path(sys.argv[1]).resolve()
sys.path.insert(0,str(p.parent))
exec(compile(p.read_text(),str(p),'exec',optimize=0),{'__name__':'__main__','__file__':str(p)})
"""

def run():
    results=[]
    hashes={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ('five_binary.py','frontend.py')}
    for optimized in (False,True):
        for script in SCRIPTS:
            command=[sys.executable]+(['-O'] if optimized else [])+['-c',BOOTSTRAP,str(ROOT/script)]
            result=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,check=True)
            receipt=json.loads(result.stdout)
            if receipt['status']!='passed':raise AssertionError((script,optimized,receipt))
            results.append({'script':script,'compiler_optimized':optimized,'audit_assertions_enabled':True,'counts':receipt['counts']})
            print(f'PASS {script}, compiler optimized={optimized}',flush=True)
    for name,digest in hashes.items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:raise AssertionError('code changed during audit')
    report={'status':'passed','code_sha256':hashes,'runs':results,
            'method':'Each independent audit entry point is compiled with optimize=0 to retain audit assertions; compiler/frontend imports use the actual process normal/-O mode.'}
    (ROOT/'audit_regression_modes.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':run()
