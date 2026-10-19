"""Check the exact row premises of increment_orientation_lemma.tex.

The accompanying paper supplies the word/list induction. This executable
checks literal table premises and reports no proof-kernel certification.
"""
from pathlib import Path
import json,sys,os
base=Path(os.environ.get('ZFC245_BASELINE',str(Path(__file__).resolve().parents[2]/'baseline/zfc245-proof-20261018')))
path=Path(sys.argv[1]) if len(sys.argv)>1 else base/'machine/zfc245_old.tm'
t={}
for line in path.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();t[int(q),int(b)]=(int(w),d,int(n))
families=[(39,6,8,69),(70,1,2,31),(72,5,7,64),(93,7,5,40),(169,4,3,56),(201,3,4,38)]
for q,logical,physical,skip in families:
 assert t[q,0]==(0,'R',57)
 assert t[q,1]==(0,'R',skip)
 assert t[skip,1]==(1,'R',skip)
fixed={
 (57,0):(0,'L',42),(57,1):(0,'R',73),
 (42,0):(1,'R',42),(42,1):(1,'L',2),
 (2,0):(0,'L',2),(2,1):(1,'L',4),(6,1):(1,'L',4),
 (4,1):(1,'L',4),(48,0):(0,'L',7),(48,1):(1,'L',63),
 (63,0):(0,'L',48),(63,1):(1,'L',63),
 (7,0):(1,'R',10),(7,1):(0,'L',7),
 (10,0):(0,'R',10),(10,1):(0,'R',14),
 (14,0):(0,'L',20),(14,1):(0,'R',14),
 (20,0):(1,'L',2),(84,0):(0,'R',84),(84,1):(1,'R',96),
}
scan=[4,6,9,13,19,29,41,58]
for i,q in enumerate(scan):
 fixed[q,0]=(0,'L',scan[i+1] if i+1<len(scan) else 84)
 fixed[q,1]=(1,'L',4)
for k,v in fixed.items():assert t[k]==v,(k,t[k],v)
out={'status':'PASS_LITERAL_PREMISES','families':[dict(state=q,logical_register=l,physical_register=r,selector=s)for q,l,r,s in families],'new_original_symbols':['h','m','r'],'new_fine_tokens':['A','T','F'],'new_masks':3,'scanner_threshold':len(scan),'distinct_control_rows_checked':len(fixed),'macro_scope':'Inherited arbitrary-register mark and increment contracts remain mathematical premises; the exact table is unchanged.','proof':'increment_orientation_lemma.tex','kernel_status':'No Lean/Rocq endpoint claimed'}
Path(__file__).with_name('increment-orientation-row-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
