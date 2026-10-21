"""Partition KSource215 into data, individual kernel checks, and its facade.

The partitioner checks that every original declaration statement and proof body
is preserved. The writer then explicitly quarter-batches proof bodies 12--15.
Their public statements and all generated data remain checked by Lean's kernel.
"""
from pathlib import Path
import re
import hashlib


def partition_source(source: str) -> dict[str, str]:
    s = source
    namespace='SetTheory.BusyBeaver.ZFC.KSource215'
    header=f'namespace {namespace}\n\nopen RegisterPath RMBisim\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
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


# The same quarter-block technique is used by the normalized and automatic
# certificate proposals. Keep the original partition-preservation check above.
_QUARTER_BODY = """/- Split this expensive kernel reduction into four independently checked lemmas.
   The CTree, checker, import and public theorem are unchanged. This follows
   the quarter-block method already used by the incoming normalized and
   automatic-certificates proposals. -/
private def left : CTree → CTree
  | .branch _ l _ => l
  | _ => .empty

private def right : CTree → CTree
  | .branch _ _ r => r
  | _ => .empty

private theorem part0_ok : allC fwdF (left (left fwd{index})) = true := by decide +kernel

private theorem part1_ok : allC fwdF (right (left fwd{index})) = true := by decide +kernel

private theorem part2_ok : allC fwdF (left (right fwd{index})) = true := by decide +kernel

private theorem part3_ok : allC fwdF (right (right fwd{index})) = true := by decide +kernel

theorem fwd_ok{index} : allC fwdF fwd{index} = true := by
  have h : allC fwdF fwd{index} =
      ((allC fwdF (left (left fwd{index})) && allC fwdF (right (left fwd{index}))) &&
      (allC fwdF (left (right fwd{index})) && allC fwdF (right (right fwd{index})))) := rfl
  rw [h, part0_ok, part1_ok, part2_ok, part3_ok]
  rfl
"""


def with_quarter_batches(files: dict[str, str]) -> dict[str, str]:
    """Batch four expensive proof bodies after exact declaration partitioning."""
    result = dict(files)
    for index in range(12, 16):
        filename = f"KSource215FwdCheck{index:02d}.lean"
        original = (f"theorem fwd_ok{index} : allC fwdF fwd{index} = true "
                    ":= by decide +kernel\n")
        assert result[filename].count(original) == 1
        result[filename] = result[filename].replace(
            original, _QUARTER_BODY.format(index=index))
    return result


def write_partition(target: Path, source: str) -> None:
    assert target.name == "KSource215.lean"
    for name, text in with_quarter_batches(partition_source(source)).items():
        (target.parent / name).write_text(text, encoding="utf-8", newline="\n")
