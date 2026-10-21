from pathlib import Path
import re,json,hashlib,difflib
b=Path('/tmp/k215-offset-symmetry');repo=Path('/home/codex/.codex/worktrees/ec20/Proofs')
formal=repo/'Computability/BusyBeaver/Research/ZFC/k225-formal';lean=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
cand=b/'candidate';py=cand/'Computability/BusyBeaver/Research/ZFC/k225-formal';out=cand/'lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;i+=2
  elif depth and s.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 assert depth==0
 return ''.join(out)
def decls(s):
 s=clean(s);ms=list(re.finditer(r'(?m)^(def|abbrev|theorem) ([\w\']+)',s));out={}
 for i,m in enumerate(ms):
  body=s[m.start():ms[i+1].start() if i+1<len(ms) else len(s)]
  body=re.split(r'(?m)^#print|^end ',body)[0]
  out[m[2]]=re.sub(r'\s+','',body)
 return out
old=decls((lean/'KSource215Data.lean').read_text());new=decls((out/'KSource215Data.lean').read_text())
assert set(new)=={n for n in old if not n.startswith('bwd')}
assert all(old[n]==v for n,v in new.items())
fwd=[]
for i in range(16):
 name=f'KSource215FwdCheck{i:02d}.lean';assert (out/name).read_bytes()==(lean/name).read_bytes();fwd.append(name)
a=decls((lean/'KSource215.lean').read_text());c=decls((out/'KSource215.lean').read_text())
assert set(c)=={n for n in a if not n.startswith('bwd')}
assert all(a[n]==v for n,v in c.items() if n!='p215_halts_iff')
assert a['p215_halts_iff'].split(':=')[0]==c['p215_halts_iff'].split(':=')[0]
# The checked facade differs from the emitted one only by the extra import of the isolated generic theorem.
isolated=clean((b/'KSource215Compact.lean').read_text().replace('import OffsetSymmetry\n',''))
assert re.sub(r'\s+','',isolated)==re.sub(r'\s+','',clean((out/'KSource215.lean').read_text()))
changes=[];diff=[]
for oldp,newp in [(lean/'RMOffsetBisim.lean',out/'RMOffsetBisim.lean'),(lean/'KSource215.lean',out/'KSource215.lean')]+[(formal/n,py/n) for n in ['generate_source215_lean.py','partition_source215_lean.py','prepare_k215.py']]:
 changes.append({'canonical':str(oldp.relative_to(repo)),'candidate':str(newp),'before_sha256':sha(oldp),'after_sha256':sha(newp)})
 diff.extend(difflib.unified_diff(oldp.read_text().splitlines(True),newp.read_text().splitlines(True),fromfile=str(oldp.relative_to(repo)),tofile=str(newp)))
(b/'candidate.diff').write_text(''.join(diff))
changes.append({'canonical':str((lean/'KSource215Data.lean').relative_to(repo)),'candidate':str(out/'KSource215Data.lean'),'before_sha256':sha(lean/'KSource215Data.lean'),'after_sha256':sha(out/'KSource215Data.lean')})
removes=[str((lean/f'KSource215BwdCheck{i:02d}.lean').relative_to(repo)) for i in range(16)]
record={'status':'PASS_STATIC_PRESERVATION_AND_ISOLATED_KERNEL_PROOF',
 'changes':changes,'remove_files':removes,'forward_check_files_byte_identical':fwd,
 'data_declarations_before':len(old),'data_declarations_after':len(new),'preserved_data_declarations':list(new),
 'removed_data_declarations':[n for n in old if n.startswith('bwd')],
 'old_data_bytes':(lean/'KSource215Data.lean').stat().st_size,'new_data_bytes':(out/'KSource215Data.lean').stat().st_size,
 'generic_kernel_record_sha256':sha(b/'run2/record.json'),'exact_facade_kernel_record_sha256':sha(b/'run3/record.json'),
 'pending':'Canonical adoption and final regenerated data/forward chunk/dependent kernel rebuild are not yet performed.'}
(b/'candidate-review.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ('changes','remove_files','forward_check_files_byte_identical','preserved_data_declarations','removed_data_declarations')},indent=2))
