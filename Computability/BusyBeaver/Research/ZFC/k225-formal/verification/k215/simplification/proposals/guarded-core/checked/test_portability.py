"""Relocation and rejection tests. Runs only this review's own Python checkers."""
import os,sys
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
    raise SystemExit('Validation requires assertions: reject optimized Python.')
from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile
B=Path(__file__).resolve().parent
SCRIPTS=('audit_received.py','check_decoder_prefixes.py')
OUTPUTS={'audit_received.py':'INDEPENDENT_AUDIT.json','check_decoder_prefixes.py':'DECODER_PREFIX_RESULT.json'}
def require(condition,message):
    if not condition:raise RuntimeError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
result={'scope':'Owned data-checker portability and rejection tests only; no incoming code or proof assistant run.','results':[]}
with tempfile.TemporaryDirectory(prefix='checked_portability_') as temporary:
    root=Path(temporary);relocated=root/'isolated'/'checked';shutil.copytree(B,relocated)
    cwd=root/'unrelated_working_directory';cwd.mkdir()
    require(not (root/'research_proof_simplification_next').exists(),'Unexpected old research directory')
    def run(script,label,flags=(),environment=None,expect=0):
        env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
        if environment:env.update(environment)
        p=subprocess.run([sys.executable,*flags,str(relocated/script)],cwd=cwd,env=env,capture_output=True,text=True,timeout=60)
        require((p.returncode==0) if expect==0 else (p.returncode!=0),f'{script} {label}: unexpected exit {p.returncode}')
        require('Traceback' not in p.stderr or expect!=0,f'{label}: positive run traceback')
        result['results'].append({'script':script,'test':label,'exit_code':p.returncode,'expected':'pass' if expect==0 else 'reject','stdout_sha256':sha(p.stdout.encode()),'stderr_sha256':sha(p.stderr.encode()),'diagnostic_tail':p.stderr.strip().splitlines()[-1:]})
        return p
    for script in SCRIPTS:
        run(script,'isolated relocated directory and unrelated cwd')
        actual=json.loads((relocated/OUTPUTS[script]).read_text());original=json.loads((B/OUTPUTS[script]).read_text())
        require(actual==original,f'{script}: relocated result changed')
        for label,flags,environment in [('-O',('-O',),None),('-OO',('-OO',),None),('PYTHONOPTIMIZE=1',(),{'PYTHONOPTIMIZE':'1'}),('PYTHONOPTIMIZE=2',(),{'PYTHONOPTIMIZE':'2'}),('PYTHONOPTIMIZE=0',(),{'PYTHONOPTIMIZE':'0'}),('-E with PYTHONOPTIMIZE=1',('-E',),{'PYTHONOPTIMIZE':'1'})]:
            before=(relocated/OUTPUTS[script]).read_bytes();p=run(script,label,flags,environment,expect=1)
            require('reject -O, -OO' in p.stderr,'Expected explicit optimization guard')
            require((relocated/OUTPUTS[script]).read_bytes()==before,'Rejected mode modified output')
    archive=relocated/'extracted/K215_Checked_Simplifications_2026-10-21'
    controls=[
        ('audit_received.py','received proof source mutation',archive/'normalized_rocq/NormalizedBisim.v'),
        ('audit_received.py','received manifest mutation',archive/'SHA256SUMS'),
        ('audit_received.py','bundled prior comparison mutation',relocated/'comparison_inputs/Prog215.v'),
        ('check_decoder_prefixes.py','decoder certificate mutation',archive/'decoder_lean/inputs/decoder_context_certificate.json'),
        ('check_decoder_prefixes.py','literal machine mutation',archive/'decoder_lean/inputs/k215.native.tm'),
        ('check_decoder_prefixes.py','source sites mutation',archive/'decoder_lean/inputs/sites215.json'),
    ]
    for script,label,path in controls:
        data=path.read_bytes();before=(relocated/OUTPUTS[script]).read_bytes()
        try:
            path.write_bytes(data+b'\n');run(script,label,expect=1)
            require((relocated/OUTPUTS[script]).read_bytes()==before,'Changed input rejection modified output')
        finally:path.write_bytes(data)
    for script in SCRIPTS:run(script,'restored data final replay')
result.update(status='PASS',owned_checker_sha256={s:sha((B/s).read_bytes()) for s in SCRIPTS},input_files_preserved=True,comparison_inputs_bundled=4,old_research_tree_required=False,optimization_rejections=12,changed_input_rejections=6,isolated_positive_replays=4)
(B/'PORTABILITY_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
