#!/usr/bin/env python3
"""Check the complete native TeX input closure and bind every used source byte."""
import argparse,collections,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent;seen=set();edges=[]
def visit(name):
 if name in seen:return
 if Path(name).is_absolute()or'..'in Path(name).parts:raise ValueError('Nonlocal TeX input '+name)
 path=root/name
 if not path.is_file():raise ValueError('Missing native input '+name)
 seen.add(name);s=path.read_text()
 for c in s:
  if ord(c)<32 and c not in'\n\r\t':raise ValueError('Control character in '+name)
 for inp in re.findall(r'\\input\{([^}]+)\}',s):
  if not inp.endswith('.tex'):inp+='.tex'
  edges.append([name,inp]);visit(inp)
visit('main.tex');labels=collections.defaultdict(list);refs=[]
for name in sorted(seen):
 s=(root/name).read_text()
 for x in re.findall(r'\\label\{([^}]+)\}',s):labels[x].append(name)
 for x in re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',s):refs.append((x,name))
 if re.search(r'\b(?:TODO|FIXME|PLACEHOLDER)\b',s):raise ValueError('Unresolved drafting marker in '+name)
if any(len(v)>1 for v in labels.values()):raise ValueError('Duplicate labels')
if any(x not in labels for x,n in refs):raise ValueError('Unresolved source references')
result={'status':'PASS','entry':'main.tex','native_input_count':len(seen),'labels':len(labels),'references':len(refs),'inputs':[{'path':n,'bytes':(root/n).stat().st_size,'sha256':hashlib.sha256((root/n).read_bytes()).hexdigest()}for n in sorted(seen)],'input_edges':edges}
if a.write:(root/'TEX_SOURCE_CLOSURE.json').write_text(json.dumps(result,indent=2)+'\n')
else:
 old=json.loads((root/'TEX_SOURCE_CLOSURE.json').read_text())
 if old!=result:raise ValueError('Native source closure changed')
print(json.dumps({'status':'PASS','native_input_count':len(seen),'labels':len(labels),'references':len(refs)},sort_keys=True))
