from pathlib import Path
import sys,json,time
BASE=Path(__file__).resolve().parent/'inputs'
sys.path.insert(0,str(BASE))
import support as s
pair=(s.INC,s.INC);s.c.MACROS[pair]=99;s.c.MACROS[(pair,pair)]=190
s.c.MACROS.update({'node37':28,'node64':106})
raw=s.c.raw_nodes;s.c.raw_nodes=lambda:{**raw(),'node163':('node6','node147')}
files=list((BASE/'ties').glob('*.grammar.json'))+[BASE/'diagonal.grammar.json',BASE/'separate.grammar.json']
start=time.time();best={};counts={};seen=set()
for path in files:
 for negate in (False,True):
  t=s.c.read_grammar(path)
  if negate:t=s.repl(t,('node49',(s.INC,'node65')),('node37',(s.INC,'node64')))
  if (t,negate) in seen:continue
  seen.add((t,negate))
  rows,idx,shape=s.c.build(t);rows[164,1]=(1,True,130)
  ops=s.c.opportunities_fast(rows,shape);lower=len(rows)//2-len(s.c.max_matching(ops))
  if lower>best.get(negate,999):continue
  ch=s.bestcompatible_all(rows,shape);rr,ali=s.apply(rows,ch);n=len(rr)//2
  if n<best.get(negate,999):
   best[negate]=n;print('BEST',negate,n,str(path),flush=True)
  counts[str((negate,n))]=counts.get(str((negate,n)),0)+1
  remaining={q:v for q,v in shape.items()if q not in ali}
  ch2=s.bestcompatible_all(rr,remaining)
  if ch2:
   rr,ali2=s.apply(rr,ch2);n=len(rr)//2;print('SECOND_FOLDS',negate,len(ch2),n,str(path),flush=True)
  if n<196:
   sites,ins,cs=s.c.source(t);check=s.c.validate(rr,cs);print('CANDIDATE',n,check,flush=True)
   if check['ok']:
    out=BASE.parent/'unexpected_success';out.mkdir(exist_ok=True)
    (out/'source.json').write_text(json.dumps(s.encode(t),indent=2))
    (out/'folds.json').write_text(json.dumps([ch,ch2],indent=2))
    (out/'machine.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {z}\n' for(q,b),(w,d,z)in sorted(rr.items())))
    (out/'sites.json').write_text(json.dumps([[list(p),op,a]for p,op,a in sites]))
    raise SystemExit('SUCCESS')
print('FINISHED',best,counts,'elapsed',time.time()-start)
