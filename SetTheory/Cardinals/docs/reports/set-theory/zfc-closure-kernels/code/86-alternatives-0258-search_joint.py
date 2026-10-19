from pathlib import Path
import sys,os,importlib.util
R=Path(__file__).resolve().parents[1]
P=R/'context_folds/recovered/67/research'
B=P/'sources/context246/zfc-context246'
os.environ['ZFC246_BASE']=str(B)
os.environ['ZFC246_TABLE']=str(Path(__file__).parent/'joint246_old.tm')
sys.path.insert(0,str(P/'agent_logic'))
import verify_rotated246 as v
spec=importlib.util.spec_from_file_location('f',R/'context_folds/recovered/64/experiments/decoder/fold_search246.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
nodes,root,_=v.read_json(P/'root_search/rebracket202_minimal.json');source=v.Decoder(nodes,root)
f.CASES=[]
for word,e in source.sites:
 op=e[0];r=e[1] if len(e)>1 else None
 operand=v.PHYSICAL[r] if op in ('I','D') else r
 for zero in ((True,False) if op=='D' else (None,)):
  branch=(operand,zero) if op=='D' else None
  extra=0;effect=None;overflow=False
  def inc(s):return v.Decoder.increment(s),all(c=='1' for c in s)
  if op=='I':after,overflow=inc(word);effect=('inc',operand)
  elif op=='D' and not zero:after,overflow=inc(word);effect=('dec',operand);extra=1
  elif op=='D':after,overflow=inc(v.Decoder.strip(word,'0',1))
  elif op=='B':after,overflow=inc(v.Decoder.strip(word,'0',operand))
  elif op=='C':after=v.Decoder.strip(word,'1',operand)
  else:after=''
  gap=40+extra+int(overflow)-len(after)
  target=f.A.canon([('b',1)],[('b',int(c))for c in after]+[('r',0,1,gap),('b',1),('box',('plain',effect))])
  f.CASES.append((word,'C'+op,r,zero,branch,target))
f.ROOT=Path(__file__).parent
f.main()
