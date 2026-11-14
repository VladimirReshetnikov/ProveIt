from pathlib import Path
import sys,json,itertools,os
HERE=Path(__file__).resolve().parent
REPO=Path(os.environ['PROVEIT_REPO']).resolve()
BASE=REPO/'Computability/BusyBeaver/Research/PA/docs/pa194nq_research_2026-11-13/construction'
sys.path.insert(0,str(BASE))
import compiler as c,symbolic_runtime as s,baseline_tools as b
c.ROOT=s.ROOT=REPO/'Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196'
INC=('leaf','inc',1); INY=('leaf','inc',7)
c.MACROS.update({'node37':28,'node64':106,INY:82,(INC,INC):99,((INC,INC),(INC,INC)):190})
def encode(t):
 d={};ix={}
 def rec(t):
  if not c.isnode(t):return t
  if t in ix:return ix[t]
  a=rec(t[0]);z=rec(t[1]);n='g'+str(len(d));ix[t]=n;d[n]=[a,z];return n
 r=rec(t);return {'root':r,'rules':d}
results=[];best=999
for gfile in [BASE/'inputs/pa194.grammar.json',BASE/'inputs/q.grammar.json']:
 t=b.expanded(c.read_grammar(gfile));word=b.word(t)
 positions=[i for i in range(len(word)-2) if word[i:i+3]==['node49',INC,'node65']]
 print(gfile.name,len(word),positions,flush=True)
 for mask in range(1<<len(positions)):
  nw=word.copy()
  for j,p in enumerate(positions):
   if mask>>j&1:nw[p:p+3]=[INY,INY,'node64']
  it=iter(nw)
  def repl(t):return (repl(t[0]),repl(t[1])) if c.isnode(t) else next(it)
  nt=repl(t); rows,_,shape=c.build(nt);ops=c.opportunities_fast(rows,shape);m=c.max_matching(ops);score=len(shape)-len(m)
  results.append({'grammar':gfile.name,'mask':mask,'nodes':len(shape),'fold_bound':len(m),'score':score})
  if score<best:
   best=score;print('BEST',results[-1],flush=True)
  if score<=61:
   (HERE/f'neg18_{gfile.stem}_{mask}.grammar.json').write_text(json.dumps(encode(nt)))
(HERE/'neg18_screen.json').write_text(json.dumps(results,indent=2))
