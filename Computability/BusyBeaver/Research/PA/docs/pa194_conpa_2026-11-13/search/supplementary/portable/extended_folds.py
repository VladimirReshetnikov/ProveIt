from pathlib import Path
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]/'construction'
OUT=HERE.parent/'generated'
OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT))
import compiler as c
from support import apply,localvalid
c.MACROS[(('leaf','inc',1),('leaf','inc',1))]=99
c.MACROS[((('leaf','inc',1),('leaf','inc',1)),(('leaf','inc',1),('leaf','inc',1)))]=190
rows,ix,shape=c.build(c.read_grammar(ROOT/'inputs/parent195S.grammar.json'))
folds=json.loads((ROOT/'inputs/parent195S.folds.json').read_text())
base,alias=apply(rows,folds)
inc={q:set() for q in shape}
for (q,v),(w,d,n) in rows.items():
 if n in inc:
  assert w==v and d
  inc[n].add(v)
used={q for a,b,acts in folds for q in(a,b)}
left=[q for q in shape if inc[q]=={0} and q not in used]
right=[q for q in shape if inc[q]=={1} and q not in used]

def trial(a,b,bit,act,ctx,oldq,bound=80):
    w,d,n=rows[oldq,bit]; n=alias.get(n,n);n=b if n==a else n
    target=(n,1 if d else -1,(-1,ctx,0,w))
    tape={-1:ctx,0:bit}; pos=0;now=b
    for step in range(bound):
        if step and now==n and pos==(1 if d else -1) and tape=={-1:ctx,0:w}:return step
        if pos not in tape:return None
        if step and now==b:return None
        if step==0: w2,d2,n2=act
        else:
          if (now,tape[pos]) not in base:return None
          w2,d2,n2=base[now,tape[pos]]
        if n2==a:n2=b
        tape[pos]=w2;pos+=1 if d2 else -1;now=n2
    return None

found=[]
for a,b in itertools.product(left,right):
    opts=[]
    for bit in (0,1):
        good=[]
        for w,d,h in itertools.product((0,1),(False,True),{q for q,_ in base}-{a,b}):
            act=(w,d,h)
            lens=[trial(a,b,bit,act,ctx,oq) for ctx,oq in ((0,a),(1,b))]
            if all(l is not None for l in lens):good.append((act,lens))
        opts.append(good)
    if all(opts):
        print('Opportunity',a,b,opts,flush=True)
        for x,y in itertools.product(*opts):
            new=folds+[[a,b,[x[0],y[0]]]]
            out,al=apply(rows,new)
            if localvalid(rows,out,al,new):
                print('VALID!',new,flush=True);found.append(new)
print('complete',len(left),len(right),len(found),flush=True)
(OUT/'extended_folds_receipt.json').write_text(json.dumps({'left':left,'right':right,'found':found},indent=2))
