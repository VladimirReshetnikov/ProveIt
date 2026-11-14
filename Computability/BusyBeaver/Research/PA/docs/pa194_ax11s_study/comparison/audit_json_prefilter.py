#!/usr/bin/env python3
from pathlib import Path
import importlib.util,json,re,zipfile,io,hashlib,collections
import argparse
ap=argparse.ArgumentParser(description='Replay the numeric-only JSON prefilter coverage audit.');ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--receipt',type=Path);args=ap.parse_args()
base=Path(__file__).resolve().parent;repo=args.repo
spec=importlib.util.spec_from_file_location('census',base/'rescan_corpus.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
known={x['normalized_sha256'] for x in json.loads((base/'census/occurrences.json').read_text())};seen=set();counts=collections.Counter();found=[]
def examine(data,path):
 ext=Path(path.split('!')[-1]).suffix.lower()
 if ext=='.zip':
  h=hashlib.sha256(data).hexdigest()
  if h in seen:return
  seen.add(h)
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   for info in z.infolist():
    if not info.is_dir() and Path(info.filename).suffix.lower() in ('.json','.zip'):examine(z.read(info),path+'!'+info.filename)
 elif ext=='.json':
  if any(tok in data for tok in (b'"L"',b'"R"',b' L ',b' R ',b'"table"',b'"transitions"')) or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',data):return
  counts['lexically_skipped_json']+=1
  if not re.search(rb'\[\s*[01]\s*,\s*-?1\s*,\s*\d+\s*\]|"(?:direction|move|dir|d)"\s*:\s*-?1',data):return
  counts['numeric_direction_candidates']+=1
  try:obj=json.loads(data)
  except (ValueError,UnicodeDecodeError):counts['non_json']+=1;return
  stack=[('$',obj)]
  while stack:
   ptr,node=stack.pop();p=m.decode(node)
   if p and len(p[1])>=2:
    digest=hashlib.sha256(m.normalized(p[0])).hexdigest();found.append({'path':path+'::json:'+ptr,'states':len(p[1]),'normalized_sha256':digest,'known':digest in known});continue
   if isinstance(node,dict):stack.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(list,dict,str)))
   elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(list,dict,str)))
for row in json.loads((base/'census/tracked_inputs.json').read_text()):
 path=row['path']
 if Path(path).suffix.lower() in ('.json','.zip'):examine((repo/path).read_bytes(),path)
result={'counts':dict(counts),'recognized_tables':found,'novel_labeled_tables':sum(not x['known'] for x in found)}
if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
