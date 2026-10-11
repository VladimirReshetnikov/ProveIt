"""Compile the four linked volumes and verify global reference convergence."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess

B=Path(__file__).resolve().parents[1]
V=B/'verification'
plan=json.loads((V/'volume-plan.json').read_text(encoding='utf-8'))
output=V/'.scratch-volumes'
output.mkdir(exist_ok=True)
env=dict(os.environ)
env['TEXINPUTS']=str(output.resolve())+os.pathsep+env.get('TEXINPUTS','')
rounds=[];previous=None
for round_number in range(1,6):
    runs=[]
    for volume in plan:
        stem=volume['stem']
        proc=subprocess.run(['lualatex','-interaction=nonstopmode','-halt-on-error',
            '-output-directory='+output.resolve().as_posix(),
            'volumes/'+stem+'.tex'],cwd=B,env=env,stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
        (output/(stem+f'-round-{round_number}.txt')).write_text(proc.stdout,encoding='utf-8')
        print('Round',round_number,'volume',volume['number'],'exit',proc.returncode,flush=True)
        if proc.returncode:raise SystemExit(proc.returncode)
        runs.append(dict(volume=volume['number'],exit_code=proc.returncode))
    state=hashlib.sha256(b''.join((output/(x['stem']+'.'+suffix)).read_bytes()
        for x in plan for suffix in ['aux','toc'])).hexdigest()
    rounds.append(dict(round_number=round_number,reference_state_sha256=state,runs=runs))
    if round_number>=3 and state==previous:break
    previous=state
else:raise SystemExit('Volume references did not converge in five complete rounds.')

results=[]
for volume in plan:
    stem=volume['stem']
    log=(output/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
    issues=[line for line in log.splitlines() if any(s in line for s in
        ['undefined','multiply defined','Overfull','Missing character',
         'Rerun to get','Label(s) may have changed','LABELS NOT IMPORTED'])]
    if issues:raise SystemExit(stem+': '+json.dumps(issues))
    pdf=B/'volumes'/(stem+'.pdf')
    shutil.copyfile(output/(stem+'.pdf'),pdf)
    results.append(dict(number=volume['number'],title=volume['title'],
        source='volumes/'+stem+'.tex',pdf='volumes/'+stem+'.pdf',
        pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),
        pdf_bytes=pdf.stat().st_size,issues=issues))

def group(text,start):
    """Read one balanced TeX group, ignoring escaped literal braces."""
    assert text[start]=='{'
    depth=1;i=start+1
    while depth:
        if text[i]=='\\':i+=2;continue
        if text[i]=='{':depth+=1
        elif text[i]=='}':depth-=1
        i+=1
    return text[start+1:i-1],i

labels={}
for volume in plan:
    rows=[]
    for line in (output/(volume['stem']+'.aux')).read_text(encoding='utf-8').splitlines():
        if not line.startswith('\\newlabel{'):continue
        name,end=group(line,len('\\newlabel'))
        value,end=group(line,end)
        fields=[];pos=0
        while pos<len(value):
            field,pos=group(value,pos);fields.append(field)
        assert len(fields)==5,(name,fields)
        fields[4]=volume['stem']+'.pdf'
        rows.append('\\expandafter\\gdef\\csname r@'+name+'\\endcsname{'+
                    ''.join('{'+field+'}' for field in fields)+'}')
    labels[volume['number']]=rows
reference_dir=B/'volumes/references'
reference_dir.mkdir(exist_ok=True)
for volume in plan:
    text='% Generated companion labels; rebuild with verification/build_volumes.py.\n\\makeatletter\n'
    text+='\n'.join(line for other in plan if other!=volume for line in labels[other['number']])
    text+='\n\\makeatother\n'
    (reference_dir/(volume['stem']+'.tex')).write_text(text,encoding='utf-8')
record=dict(passed=True,converged=True,rounds=rounds,volumes=results,
    scope='Separate LuaLaTeX PDFs; all four aux/toc states converge together. Mathematical replay, PDF inspection and visual review are separate.')
(V/'volume-build-results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
