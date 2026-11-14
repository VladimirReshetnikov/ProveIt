from support import *
p=(INC,INC);c.MACROS[p]=99;c.MACROS[(p,p)]=190

def partition(rows):
 qs=sorted({q for q,b in rows});cl={q:0 for q in qs};cl[254]=-1
 while True:
  ids={};cc={254:-1}
  for q in qs:
   key=tuple((rows[q,b][0],rows[q,b][1],cl[rows[q,b][2]]) for b in(0,1))
   if key not in ids:ids[key]=len(ids)
   cc[q]=ids[key]
  if all(cc[q]==cl[q] for q in qs):return cc
  cl=cc

if __name__=='__main__':
 import sys
 files=sys.argv[1:] or sorted(str(p)for p in Path('ties').glob('alltie_*.grammar.json'))+['scanner_6.grammar.json']
 for f in files:
  t=c.read_grammar(f);r,i,s=c.build(t);ch=bestcompatible_all(r,s);rr,al=apply(r,ch);part=partition(rr);groups={}
  for q,k in part.items():groups.setdefault(k,[]).append(q)
  multi=[v for v in groups.values()if len(v)>1]
  if multi:
   print('FOUND',f,multi,flush=True);Path('bisim_candidate.grammar.json').write_text(Path(f).read_text());Path('bisim_candidate.groups.json').write_text(json.dumps(multi));raise SystemExit()
 print('FINISHED',len(files),'no nontrivial bisimulation classes')
