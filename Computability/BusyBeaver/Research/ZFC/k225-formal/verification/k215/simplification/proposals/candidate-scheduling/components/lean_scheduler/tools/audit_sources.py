#!/usr/bin/env python3
"""Check unchanged executable declarations, theorem types, and producer replay."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess

p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--packet',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args();a.repo=a.repo.resolve();a.packet=a.packet.resolve();a.out=a.out.resolve();a.out.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
    out=[];i=0;depth=0;quoted=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-':depth+=1;i+=2
            elif s[i:i+2]=='-/':depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            out.append(s[i])
            if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
            elif s[i]=='"':quoted=False
            i+=1
        elif s[i:i+2]=='/-':depth=1;i+=2
        elif s[i:i+2]=='--':
            i=s.find('\n',i)
            if i==-1:break
        else:
            if s[i]=='"':quoted=True
            out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)
def declarations(s):
    s=strip_comments(s)
    rx=re.compile(r'^(?:(?:private|protected|noncomputable) )?(def|abbrev|structure|inductive|macro|theorem)\s+([^\s({:\n]+)',re.M)
    starts=list(rx.finditer(s));result={}
    for i,m in enumerate(starts):
        body=s[m.start():starts[i+1].start() if i+1<len(starts) else len(s)]
        body=re.split(r'\n(?:#print|end |namespace |attribute |open )',body,1)[0]
        result[(m[1],m[2])]=body
    return result
norm=lambda s:re.sub(r'\s+',' ',s).strip()
rows=[];all_old=all_new=0;old_lines=new_lines=0
prefix=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
for name in ['EnumPerm','Enum254','Enum222','EnumDom']:
    original=a.repo/prefix/(name+'.lean'); overlay=a.packet/'proof/BusyBeaver/ZFC'/(name+'.lean')
    old=original.read_text();new=overlay.read_text();od=declarations(old);nd=declarations(new)
    definitions=[];theorems=[]
    for key,body in od.items():
        assert key in nd,(name,key)
        if key[0]!='theorem':
            assert norm(body)==norm(nd[key]),(name,key,'executable declaration changed')
            definitions.append(key[1])
        else:
            header=lambda s:re.split(r'\s:=|\n  \|',s,1)[0]
            assert norm(header(body))==norm(header(nd[key])),(name,key,'theorem statement changed',header(body),header(nd[key]))
            theorems.append(key[1])
    rows.append({'module':name,'original_sha256':sha(original),'overlay_sha256':sha(overlay),
      'unchanged_executable_declarations':definitions,'preserved_theorem_statements':theorems,
      'before_bytes':len(old.encode()),'after_bytes':len(new.encode()),'before_lines':len(old.splitlines()),'after_lines':len(new.splitlines())})
    all_old+=len(old.encode());all_new+=len(new.encode());old_lines+=len(old.splitlines());new_lines+=len(new.splitlines())
core=a.packet/'proof/BusyBeaver/ZFC/CofinalScheduler.lean'
reg=a.out/'regenerated';d=reg/'BusyBeaver/ZFC';d.mkdir(parents=True,exist_ok=True)
(d/'Enum254.lean').write_bytes((a.packet/'proof/BusyBeaver/ZFC/Enum254.lean').read_bytes())
generators=[]
for filename,name in [('generate_enum222.py','Enum222'),('generate_enumdom.py','EnumDom')]:
    source=a.repo/'Computability/BusyBeaver/Research/ZFC/k225-formal'/filename
    rr=subprocess.run(['python3',str(source)],cwd=reg,text=True,capture_output=True)
    assert rr.returncode==0,rr.stderr
    assert (d/(name+'.lean')).read_bytes()==(a.packet/'proof/BusyBeaver/ZFC'/(name+'.lean')).read_bytes()
    generators.append({'script':filename,'source_sha256':sha(source),'exit_code':rr.returncode,'exact_output_match':True})
summary={'modules':rows,'core':{'sha256':sha(core),'bytes':core.stat().st_size,'lines':len(core.read_text().splitlines())},
 'aggregate_production':{'before_bytes':all_old,'after_bytes':all_new+core.stat().st_size,'before_lines':old_lines,'after_lines':new_lines+len(core.read_text().splitlines())},
 'generators':generators,'new_induction_proofs':3,'replaced_induction_proofs':16}
(a.out/'source-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'aggregate_production':summary['aggregate_production'],'core':summary['core'],'generators':generators},indent=2))
