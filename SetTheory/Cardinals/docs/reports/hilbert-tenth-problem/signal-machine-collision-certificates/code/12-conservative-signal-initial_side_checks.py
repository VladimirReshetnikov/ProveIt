from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util,json
p=Path(__file__).resolve().parent/'conservative_signal.py'
s=importlib.util.spec_from_file_location('updated_cs',p);cs=importlib.util.module_from_spec(s);s.loader.exec_module(cs)
res={'initial_sides':{},'cases':0,'event_batches':0}
for side in ('L','R'):
  for L in product((1,2),repeat=2):
    for R in product((1,2),repeat=2):
      # Original tape head is0, with independent support on both sides.
      tape={-2:L[1],-1:L[0],0:R[0],1:R[1]}
      write={('start',a):('m1',3-a) for a in (1,2)}
      write.update({('second',a):('m2',a) for a in (1,2)})
      moves={'m1':('second','L'),'m2':('halt','R')}
      speed,rules=cs.compile_tm(write,moves,'start',{'halt'},initial_side=side)
      def half(head,d,inc=False):
        start=head if inc else head+d
        support=[i for i,v in tape.items() if v!=1 and (i-start)*d>=0]
        if not support:return F(1,2)
        end=max(support) if d==1 else min(support)
        return cs.blank_stack([tape.get(i,1) for i in range(start,end+d,d)],2)
      sl=half(0,-1,side=='L');sr=half(0,1,side=='R')
      conf=[(F(-4+i),'L:mark'+str(i)) for i in range(3)]
      conf += [(F(4-i),'R:mark'+str(i)) for i in range(3)]
      conf += [(F(-4)+sl,'L:mem'),(F(4)-sr,'R:mem'),(F(0),'q:start'),(F(-1 if side=='L' else 1),side+':gl')]
      conf.sort();q='start';head=0;count=0
      for k in range(1000):
        out=cs.event(conf,speed,rules)
        if out is None:break
        new,dt,rec=out
        oldq=[a[2:] for x,a in conf if x==0 and a.startswith('q:')]
        newq=[a[2:] for x,a in new if x==0 and a.startswith('q:')]
        if oldq and oldq!=newq and oldq[0] in ('start','second','halt'):
          assert oldq==[q]
          mem={a:x for x,a in conf};a=tape.get(head,1)
          assert mem['L:mem']+4==half(head,-1)
          assert 4-mem['R:mem']==half(head,1)
          assert any(label.endswith(':vr'+str(a)) for x,label in conf)
          if q=='halt':assert any(a==f'h:halt:{tape.get(head,1)}' for x,a in new)
          else:
            r,b=write[q,a];nextq,d=moves[r];tape[head]=b;head+=1 if d=='R' else -1;q=nextq
        conf=new;count+=1
      else:raise AssertionError('run limit')
      assert q=='halt'
      res['cases']+=1;res['event_batches']+=count
      res['initial_sides'][side]=res['initial_sides'].get(side,0)+1
print(json.dumps(res,indent=2))
(Path(__file__).resolve().parent.parent/'receipts'/'INITIAL_SIDE_RESULTS.json').write_text(json.dumps(res,indent=2)+'\n')
