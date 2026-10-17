#!/usr/bin/env python3
"""Independent finite audit of attributed 254/253 machines.
No Coq or Lean compiler is invoked; this is not a proof of consistency calibration.
"""
from pathlib import Path
import hashlib,importlib.util,json,re,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
from analyze_table import parse_table,audit
def loadmodule(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def run(rows,start,steps):
    tape=set();h=0;q=start
    for t in range(steps):
        a=rows.get((q,int(h in tape)))
        if a is None:raise AssertionError(('early halt',t,q))
        w,d,q=a
        if w:tape.add(h)
        else:tape.discard(h)
        h+=1 if d=='R' else -1
    return q,h,tape
def frame(h,gap,regs):
    ones={h-1,h+gap};i=h+gap+1
    for v in regs:
        i+=1
        ones.update(range(i,i+v+1));i+=v+1
    return ones
p254=HERE/'upstream/ZF/m254/machine/zfc_254.tm'
p253=HERE/'upstream253/ZF/m253/machine/zfc_253.tm'
reports=[]
for p,sha,count,steps,endq,endh,gap,regs in [
    (p254,'d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',254,264982,96,-8,62,[0]*6+[2]+[0]*2+[0]*136),
    (p253,'84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95',253,312975,33,-17,40,[0,2,0,0,0,0,5,0,0]+[0,0,1,0,0,0,0,0,1]+[0]*149)]:
    rows,start,working,terminal,digest=parse_table(p)
    assert digest==sha and working==list(range(count))and terminal==[count]and start==0
    q,h,tape=run(rows,start,steps);expected=frame(endh,gap,regs)
    assert(q,h,tape)==(endq,endh,expected)
    report=audit(p);report['path']=str(p.relative_to(HERE))
    report['full_boot']={'steps':steps,'state':q,'head':h,'gap':gap,'register_values':regs,
       'ones':sorted(tape),'entire_tape_matches':True,'all_other_integer_cells_are_zero':True}
    reports.append(report)
original_checker=loadmodule('checker254',HERE/'upstream/ZF/m254/check.py')
assert original_checker.check_table() is None
generator=loadmodule('gen253',HERE/'upstream253/ZF/m253/tools/generate_candidate.py')
assert generator.generate_candidate(p254)==p253.read_bytes()
# An independently retained Lean table agrees in each working transition.
text=(HERE/'proveit/Table253.lean').read_text()
body=text.split('def rawTable253',1)[1].split('\n]',1)[0]
pat=r'\(\((true|false), \.(left|right), (\d+)\), \((true|false), \.(left|right), (\d+)\)\)'
raw=re.findall(pat,body);assert len(raw)==253
rows=parse_table(p253)[0]
for q,(w0,d0,t0,w1,d1,t1) in enumerate(raw):
    for b,(w,d,t) in enumerate([(w0,d0,t0),(w1,d1,t1)]):
        assert rows[q,b]==(int(w=='true'),'L' if d=='left' else 'R',int(t))
out={'machines':reports,'table254_matches_Coq_literal':True,'table253_four_edit_reconstruction':True,
    'table253_matches_Lean_literal':True,'local_proof_compilers_run':False,
    'scope':'Exact finite input/table/bootstrap checks; no consistency or internalization theorem.'}
(HERE/'baseline_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='machines'},indent=2))
print('Both complete blank-tape endpoints checked, including every spare register block and blank exterior.')
