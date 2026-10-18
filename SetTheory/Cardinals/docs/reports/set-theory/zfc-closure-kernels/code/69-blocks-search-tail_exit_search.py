"""Screen a three-row candidate family on complete finite instruction frames."""
from pathlib import Path
import sys,itertools,json,time
BASE=Path(__file__).resolve().parents[1]/'reference/context246'
sys.path.insert(0,str(BASE/'code'))
import check_literal_instructions as lit
T=lit.read_table(BASE/'machine/zfc_prefix246_old.tm')
for b in (0,1):del T[255,b]
T[75,0]=(0,1,63);T[48,0]=(1,-1,131)
states=sorted(set(q for q,b in T))
sites=lit.program_sites(BASE/'sources/Prog254.v')
oldexpected=lit.expected
def expected(pc,kind,r,regs,spares,head,span):
 result=oldexpected(pc,kind,r,regs,spares,head,span)
 if kind=='CI':
  h,one,pc,d,regs,sp=result
  sp[-1]=0
  return h,lit.paint(pc,d,regs,sp,h),pc,d,regs,sp
 return result
lit.expected=expected
chosen=[]
for op in ['CI','CD','CB','CC','CH']:
 regs=range(9) if op in ('CI','CD') else [None]
 for r in regs:
  a=next(s for s in sites if s[1]==op and (r is None or r==s[2]))
  chosen.append(a)
cases=[]
for pc,op,r in chosen:
 for positive in ((False,True) if op=='CD' else [None]):
  vs=[i%3 for i in range(9)]
  if op=='CD':vs[lit.PHYSICAL[r]]=int(positive)
  cases.append((pc,op,r,vs,[0,1],0,40))
began=time.monotonic();afterfirst=0;survive=[];n=0
for key in [(131,0),(131,1),(112,0),(112,1),(63,0),(63,1),(48,1)]:
 orig=T[key]
 for action in itertools.product((0,1),(-1,1),states):
  n+=1;T[key]=action
  try:
   for j,c in enumerate(cases):
    lit.run_case(T,*c,fuel=3000)
    if j==0:afterfirst+=1
   survive.append((key,action));print('PASS',key,action,flush=True)
  except (AssertionError,KeyError):pass
 T[key]=orig
 print('DONE ROW',key,'attempts',n,'afterfirst',afterfirst,'survivors',survive,flush=True)
result=dict(candidates=n,case_count=len(cases),after_first=afterfirst,survivors=survive,seconds=time.monotonic()-began,scope='Finite screening; every retained candidate would need universal proof.')
(Path(__file__).resolve().parents[1]/'results/exit-search.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
