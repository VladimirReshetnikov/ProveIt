#!/usr/bin/env python3
"""Parse, but never execute, the historical AQ22/AQ26 launch runbooks."""
import ast,hashlib,json,re,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('audit requires assertions enabled')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
H=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for n in (22,26):
    path=ROOT/f'Computability/DiophantineConsistency/research/ipra-standard-aq{n}/historical/REAL-RUN.md'
    raw=path.read_bytes(); commit=subprocess.check_output(['git','-C',str(ROOT),'show','e4926948e0:'+str(path.relative_to(ROOT))]);assert raw==commit
    text=raw.decode(); blocks=re.findall(r'```bash\n(.*?)\n```',text,re.S);assert len(blocks)==1
    q=subprocess.run(['bash','-n'],input=blocks[0],capture_output=True,text=True);assert q.returncode==0,q.stderr
    scripts=re.findall(r"<<'(PY(?:_PREPARE)?)'\n(.*?)\n\1(?:\n|$)",blocks[0],re.S);assert len(scripts)>=5
    for _,script in scripts:ast.parse(script)
    prep=next(script for label,script in scripts if label=='PY_PREPARE')
    for token in ('subprocess.run(cmd,capture_output=True,text=True)','p.returncode','p.stdout','p.stderr',"(r/'preparer-process.json').open('x')",'sys.exit(p.returncode)'):
        assert token in prep,(n,token)
    rows.append({'aq':n,'path':str(path.relative_to(ROOT)),'sha256':H(raw),'bash_syntax_exit':q.returncode,'python_heredocs_parsed':len(scripts),'preparer_wrapper_inspected':True})
    print('PASS: AQ'+str(n)+' runbook static syntax and preparation wrapper',flush=True)
out=HERE/'runbook-validation.json';assert not out.exists();out.write_text(json.dumps({'status':'PASS_STATIC_RUNBOOK_AUDIT','workflow_commit':'e4926948e0','runbooks':rows,'scope':'Static parsing and wrapper inspection only; no runbook commands executed.'},indent=2,sort_keys=True)+'\n')
print('PASS_STATIC_RUNBOOK_AUDIT',H(out.read_bytes()),flush=True)
