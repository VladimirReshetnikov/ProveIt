"""Partition KSource215 into data, individual kernel checks, and its facade.

Only module boundaries change. The transformer checks that every original declaration
statement and proof body is preserved. Generated data is still checked by Lean's kernel.
"""
from pathlib import Path
import re
import hashlib


def partition_source(source: str) -> dict[str, str]:
    s = source
    namespace='SetTheory.BusyBeaver.ZFC.KSource215'
    header=f'namespace {namespace}\n\nopen RegisterPath RMBisim RMOffsetBisim\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    end=f'\nend {namespace}\n'
    assert s.count('namespace '+namespace)==1 and s.rstrip().endswith('end '+namespace)
    fw=s.index('theorem fwd_start :')
    common=s[:fw]+end
    files={'KSource215Data.lean':common};mapping=[];order=['KSource215Data']
    for direction in ['fwd']:
     for i in range(16):
      name=f'{direction}_ok{i}';pat=rf'(?m)^theorem {name} : [^\n]+\n';matches=list(re.finditer(pat,s));assert len(matches)==1
      decl=matches[0][0];assert decl.endswith(' := by decide +kernel\n')
      module=f'KSource215{direction.title()}Check{i:02d}'
      files[module+'.lean']='import BusyBeaver.ZFC.KSource215Data\n\n'+header+decl+end
      order.append(module);mapping.append({'declaration':name,'module':module,'original_line':s[:matches[0].start()].count('\n')+1,'declaration_sha256':hashlib.sha256(decl.encode()).hexdigest()})
    facade=s[fw:]
    for direction in ['fwd']:
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
    assert len(mapping)==16 and len(order)==18
    return files


def write_partition(target: Path, source: str) -> None:
    assert target.name == "KSource215.lean"
    for name, text in partition_source(source).items():
        (target.parent / name).write_text(text, encoding="utf-8", newline="\n")
