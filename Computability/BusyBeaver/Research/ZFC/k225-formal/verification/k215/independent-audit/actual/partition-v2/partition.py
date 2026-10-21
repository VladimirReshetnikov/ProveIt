#!/usr/bin/env python3
"""Copy-only partition of the exact monolithic source; no compiler or supplied code invoked."""
from pathlib import Path
import re,json,hashlib,argparse
ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
original=a.source.read_bytes();s=original.decode();out=a.output;out.mkdir(parents=True,exist_ok=False)
namespace='SetTheory.BusyBeaver.ZFC.KSource215'
header=f'namespace {namespace}\n\nopen RegisterPath RMBisim RMOffsetBisim\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
end=f'\nend {namespace}\n'
assert s.count('namespace '+namespace)==1 and s.rstrip().endswith('end '+namespace)
fw=s.index('theorem fwd_start :');mirror=s.index('/-! ## Mirrored certificate');bw=s.index('theorem bwd_start :')
common=s[:fw]+s[mirror:bw]+end
files={'KSource215Data.lean':common};mapping=[];order=['KSource215Data']
for direction in ['fwd','bwd']:
 for i in range(16):
  name=f'{direction}_ok{i}';pat=rf'(?m)^theorem {name} : [^\n]+\n';matches=list(re.finditer(pat,s));assert len(matches)==1
  decl=matches[0][0];assert decl.endswith(' := by decide +kernel\n')
  module=f'KSource215{direction.title()}Check{i:02d}'
  files[module+'.lean']='import BusyBeaver.ZFC.KSource215Data\n\n'+header+decl+end
  order.append(module);mapping.append({'declaration':name,'module':module,'original_line':s[:matches[0].start()].count('\n')+1,'declaration_sha256':hashlib.sha256(decl.encode()).hexdigest()})
facade=s[fw:mirror]+s[bw:]
for direction in ['fwd','bwd']:
 facade,n=re.subn(rf'(?m)^theorem {direction}_ok\d+ : [^\n]+\n\n?', '',facade);assert n==16
files['KSource215.lean']='\n'.join('import BusyBeaver.ZFC.'+n for n in order)+'\n\n'+header+facade
order.append('KSource215')
# Independent declaration-body comparison: remove only comments, module wrappers and whitespace.
def clean(t):
 z=[];i=0;depth=0
 while i<len(t):
  if t[i:i+2]=='/-':depth+=1;i+=2
  elif depth and t[i:i+2]=='-/':depth-=1;i+=2
  elif depth:i+=1
  elif t[i:i+2]=='--':
   j=t.find('\n',i);i=len(t)if j<0 else j
  else:z.append(t[i]);i+=1
 assert depth==0;return ''.join(z)
def declarations(t):
 t=clean(t);ms=list(re.finditer(r'(?m)^(def|abbrev|theorem) ([\w\']+)',t));d={}
 for j,m in enumerate(ms):
  body=t[m.start():ms[j+1].start() if j+1<len(ms)else len(t)]
  body=re.split(r'(?m)^#print|^end ',body)[0]
  d[m[2]]=re.sub(r'\s+','',body)
 return d
before=declarations(s);after={}
for name,text in files.items():
 for decl,body in declarations(text).items():assert decl not in after,(name,decl);after[decl]=body
assert before==after,(set(before)^set(after),[k for k in before.keys()&after.keys()if before[k]!=after[k]])
assert len(mapping)==32 and len(order)==34
for name,text in files.items():(out/name).write_text(text)
(out/'original-KSource215.lean').write_bytes(original)
rows=[]
for name in order:
 p=out/(name+'.lean');b=p.read_bytes();rows.append({'module':'BusyBeaver.ZFC.'+name,'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
result={'status':'SOURCE_ONLY_PARTITION_NOT_COMPILED','original_source':str(a.source),'original_sha256':hashlib.sha256(original).hexdigest(),'files':rows,'proof_mapping':mapping,'all_original_declaration_bodies_equal_ignoring_comments_whitespace':True,'declaration_count':len(before),'inherited_options':{'maxRecDepth':65536,'maxHeartbeats':8000000},'changes':'Module boundaries/imports only; namespace and every declaration statement/body retained. Original source copied unchanged.','claims_not_made':['No actual compiler pass','No guarantee each unit fits existing runtime/memory cap'],'original_single_module_plus_33_new_modules':True}
(out/'partition.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'modules':len(rows),'declarations':len(before),'proof_chunks':len(mapping),'bytes':sum(x['bytes']for x in rows)}))
