from pathlib import Path
import importlib.util,json
B=Path('research_sub246/source/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code')
spec=importlib.util.spec_from_file_location('lit',B/'63-context246-code-check_literal_instructions.py');lit=importlib.util.module_from_spec(spec);spec.loader.exec_module(lit)
P=Path('research_sub246/source/Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm'); T=lit.read_table(P)
prog=Path('research_sub246/source/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v')
pc,kind,r=next(x for x in lit.program_sites(prog) if x[0]=='0111')
regs=[0]*9;spares=[1];head=0;ones=lit.paint(pc,40,regs,spares,head);state=96
print(pc,kind,r)
for step in range(2000):
 if state in (96,95,112,131,48,63,7,10,30,57,75,255) and (head<=len(pc)+5 or state in (96,95,75,255)):
  print(step,state,head,''.join(str(int(i in ones)) for i in range(-1,45)))
 if step and state==96 and ones==lit.expected(pc,kind,r,regs,spares,0,40)[1]:break
 w,d,state=T[state,int(head in ones)]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=d
