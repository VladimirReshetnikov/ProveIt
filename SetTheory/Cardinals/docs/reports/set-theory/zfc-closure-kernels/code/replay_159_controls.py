from pathlib import Path
import importlib.util,json,re
ROOT=Path(__file__).resolve().parent.parent

def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
v=load(ROOT/'verify.py','recovered_verify')
a=load(ROOT/'work/state_reduction/audit_modified_source.py','recovered_machine')
p=ROOT/'source/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
body=p.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
rows=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body);assert len(rows)==6459
leaves=[]
def visit(q,path):
 for bit,e in enumerate(rows[q]):
  op,*arg=e.split();p=path+str(bit)
  if op=='CN':visit(int(arg[0]),p)
  else:leaves.append((p,op[1:],int(arg[0])if arg else None))
visit(0,'')
_,_,optimized,_,_=a.reconstruct((ROOT/'work/compiler_reduction/source27/decoder_entries.json').read_bytes())
assert leaves==optimized and len(leaves)==6460
best=ROOT/'experiments/direct-negation255';recipe=json.loads((best/'fold_sequence.json').read_text());t=v.table((best/'fresh_261_oldlabels.tm').read_bytes());assert len(t)==522
for step in recipe['recipes']:
 dead,keep,mask=step['deleted'],step['target'],step['copied_row_mask'];old=t
 t={(q,b):(w,m,keep if n==dead else n)for(q,b),(w,m,n)in old.items()if q!=dead}
 for b in(0,1):
  if mask>>b&1:
   w,m,n=old[dead,b];t[keep,b]=w,m,keep if n==dead else n
assert len(recipe['recipes'])==6 and t==v.table((best/'machine_255_oldlabels.tm').read_bytes())
ren=json.loads((best/'renumbering.json').read_text());m={int(k):n for k,n in ren['old_to_new'].items()}
nt={(m[q],b):(w,d,m[n])for(q,b),(w,d,n)in t.items()}
assert nt==v.table((best/'zfc_direct_negation255.tm').read_bytes()) and set(nt)=={(q,b)for q in range(255)for b in(0,1)} and m[64]==0 and m[254]==255
pair=lambda a,b:(a+b)*(a+b+1)//2+b
for x in range(10001):assert pair(x,1)==pair(0,x)+2 and 4*pair(x,1)==2*x*x+6*x+8
out=dict(status='PASS',literal_leaves=len(leaves),accepted_folds=6,working_states=255,rows=510,normalized_start=0,normalized_halt=255,identity_samples=10001,scope='Finite source correspondence, exact accepted table edits and renumbering, sampled identity only. Not a source semantic proof or full invariant certificate.')
(ROOT/'review-logs/recovered-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
