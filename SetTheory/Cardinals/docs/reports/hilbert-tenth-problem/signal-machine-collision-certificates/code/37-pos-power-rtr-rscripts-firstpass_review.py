"""Independent synthetic first-pass/no-shell-escape tests; no scientific execution."""
from pathlib import Path
import json,os,runpy,shutil,subprocess,sys
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
I=runpy.run_path(str(BASE/'auth_snapshot.py'));inv,sha,enc=I['inventory'],I['sha'],I['encoded']
H=runpy.run_path(str(BASE/'candidate/tools/release67.py'),run_name='firstpass_helpers')
out=BASE/'independent-firstpass';out.mkdir()
fixture=out/'fixture';fixture.mkdir()
for name in ('science','audits','tools'):
    shutil.copytree(BASE/'candidate'/name,fixture/name,copy_function=shutil.copy2)
shutil.copy2(BASE/'candidate/INPUT_PINS.json',fixture/'INPUT_PINS.json')
(folder:=fixture/'manuscript').mkdir()
for name in H['MODULES'][1:]: (folder/name).write_text('% Independent synthetic module '+name+'\n')
(folder/'Report67.tex').write_text('\\documentclass{article}\n\\IfFileExists{Report67.aux}{}{\\usepackage{ifthen}}\n\\ifnum\\pdfshellescape=0\\else\\errmessage{Shell escape enabled}\\fi\n\\pdftrailerid{}\n\\begin{document}\nIndependent first-pass recorder challenge.\n'+''.join('\\input{manuscript/'+n+'}\n' for n in H['MODULES'][1:])+'\\end{document}\n')
results=[]
def run(name,tool,args,success=True,needle=None):
    before=inv(fixture)
    c=subprocess.run([sys.executable,'-I','-S','-B',str(fixture/'tools'/tool),*args],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (out/(name+'.stdout')).write_bytes(c.stdout)
    assert (c.returncode==0)==success,(name,c.stdout[-2000:])
    if needle:assert needle.encode() in c.stdout
    assert inv(fixture)==before
    results.append({'name':name,'status':'PASS','exit_status':c.returncode,'source_preserved':True})
run('prepare','release67.py',['prepare','--output-dir',str(out/'prepared')])
shutil.copy2(out/'prepared/Report67.tex',fixture/'Report67.tex');shutil.copy2(out/'prepared/MANUSCRIPT_PINS.json',folder/'MANUSCRIPT_PINS.json')
pin=sha((folder/'MANUSCRIPT_PINS.json').read_bytes())
run('bootstrap-no-shell-escape','build_report67.py',['--pins-sha',pin,'--bootstrap','--output-dir',str(out/'bootstrap')])
union=json.loads((out/'bootstrap/RECORDER_INPUT_UNION.json').read_bytes())
assert [r['pass'] for r in union['passes']]==['format','compile-1','compile-2','compile-3']
early=set(union['passes'][1]['system_inputs'])-set(union['passes'][2]['system_inputs'])-set(union['passes'][3]['system_inputs'])
p=next(p for p in early if p.endswith('/ifthen.sty'));assert p in union['union']
for label in ('compile-1','compile-2','compile-3'):
    raw=(out/'bootstrap'/(label+'.fls')).read_text();assert (p in raw)==(label=='compile-1')
lockraw=(out/'bootstrap/BUILD_DEPENDENCIES.json').read_bytes();lock=json.loads(lockraw)
shutil.copy2(out/'bootstrap/BUILD_DEPENDENCIES.json',fixture/'tools/BUILD_DEPENDENCIES_LOCK.json');shutil.copy2(out/'bootstrap/Report67.pdf',fixture/'Report67.pdf')
run('locked-no-shell-escape','build_report67.py',['--pins-sha',pin,'--dependency-lock-sha',sha(lockraw),'--require-packaged-match','--output-dir',str(out/'locked')])
lock['system_inputs'].pop(p);changed=enc(lock);(fixture/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(changed)
run('reject-omitted-first-pass-input','build_report67.py',['--pins-sha',pin,'--dependency-lock-sha',sha(changed),'--output-dir',str(out/'omitted')],False,'Unpinned or changed executed TeX input: '+p)
receipt={'status':'PASS','scope':'Independent synthetic presentation test; no scientific execution','tests':results,'first_pass_only_dependency':p,'retained_in_union':True,'no_shell_escape_probed_in_tex':True,'review_script_sha256':sha(Path(__file__).read_bytes())}
(out/'FIRSTPASS_RECEIPT.json').write_bytes(enc(receipt));print(enc(receipt).decode())
