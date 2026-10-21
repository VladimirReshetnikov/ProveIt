#!/usr/bin/env python3
"""Read-only static Lean source/import/assumption census; no Lean invocation."""
from pathlib import Path
import re,json,hashlib,argparse
if not __debug__:raise RuntimeError('Run without Python -O')
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();REPO=a.repo.resolve();OUTPUT=a.output.resolve()
assert REPO.is_dir() and not OUTPUT.exists() and REPO not in OUTPUT.parents and OUTPUT!=REPO
ROOTS=[REPO/'Computability/BusyBeaver/Lean',REPO/'Logic/FirstOrder/Lean',REPO/'SetTheory/ZF/Lean',REPO/'SetTheory/BoundedConsistency/Lean']

def strip(s):
    out=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\' and i+1<len(s):out.extend('  ');i+=2
            elif s[i]=='"':string=False;out.append(' ');i+=1
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    assert depth==0 and not string
    return ''.join(out)

def locate(m):
    candidates=[r/Path(*m.split('.')).with_suffix('.lean') for r in ROOTS]
    candidates=[p for p in candidates if p.is_file()]
    assert len(candidates)<=1,(m,candidates)
    return candidates[0] if candidates else None

seen={};external=set();hits=[]
def walk(m):
    if m in seen or m in external:return
    p=locate(m)
    if p is None:external.add(m);return
    data=p.read_bytes();s=data.decode();clean=strip(s)
    imports=[]
    for line in clean.splitlines():
        z=re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$',line)
        if z:imports.extend(z.group(1).split())
    item={'module':m,'path':str(p),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'imports':imports}
    seen[m]=item
    for n,line in enumerate(clean.splitlines(),1):
        if re.search(r'\b(?:axiom|sorry|admit|unsafe|native_decide|implemented_by|addDecl|mkAxiom|opaque|constant)\b',line):
            hits.append({'module':m,'line':n,'text':s.splitlines()[n-1]})
    for im in imports:walk(im)
walk('BusyBeaver.ZFC.KEndpoint215')
result={'status':'STATIC_SOURCE_CENSUS','roots':[str(r) for r in ROOTS],'endpoint':'BusyBeaver.ZFC.KEndpoint215','project_modules':list(seen.values()),'project_count':len(seen),'external_imports':sorted(external),'lexical_findings':hits,'boundary':'Imports explicitly named in project files only; implicit Init/toolchain closure is external. Compiler Print axioms must establish the actual theorem dependency set.'}
assert len(seen)==204 and external=={'Init'} and not hits, 'Unexpected post-partition static closure'
OUTPUT.parent.mkdir(parents=True,exist_ok=True)
with OUTPUT.open('x')as f:f.write(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'project_count':len(seen),'external_imports':sorted(external),'lexical_findings':hits},indent=2))
