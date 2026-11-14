from pathlib import Path
import json,time,hashlib
import build_composites as bc
from support import bestcompatible_all,apply,encode,localvalid
c=bc.c
(bc.ROOT/'search/results').mkdir(parents=True,exist_ok=True)
paths=sorted((bc.AX/'search/ties').glob('*.grammar.json'))+[bc.AX/'diagonal196/grammar.json',bc.AX/'separate196/grammar.json',bc.AX/'search/scanner_best196.grammar.json']
seen=set();records=[];start=time.time()
for p in paths:
 t=c.read_grammar(p)
 if t in seen:continue
 seen.add(t);rows,idx,sh=c.build(t);ops=c.opportunities_fast(rows,sh);lb=len(rows)//2-len(c.max_matching(ops))
 chosen=bestcompatible_all(rows,sh);folded,alias=apply(rows,chosen);n=len(folded)//2
 rec={'path':str(p.relative_to(bc.ROOT)),'nodes':len(sh),'individual_pairs':len(ops),'lower':lb,'states':n,'folds':len(chosen)};records.append(rec)
 print(p.name,len(sh),len(chosen),n,flush=True)
 if n<196:
  sites,ins,cs=c.source(t);val=c.validate(folded,cs);st=bc.startup(folded,sites[25][0]);rec.update(validation=val,startup=st)
  out=bc.ROOT/'search/results'/('candidate'+str(n)+'_'+str(len(records)));out.mkdir(parents=True,exist_ok=True)
  (out/'machine.native.tm').write_text(bc.table_text(folded));(out/'grammar.json').write_text(json.dumps(encode(t),indent=2));(out/'folds.json').write_text(json.dumps(chosen,indent=2));(out/'sites.json').write_text(json.dumps([[''.join(map(str,p)),op,a]for p,op,a in sites]));(out/'receipt.json').write_text(json.dumps(rec,indent=2));print('CANDIDATE',rec,flush=True)
(bc.ROOT/'search/results/grammar_screen.json').write_text(json.dumps({'records':records,'seconds':time.time()-start},indent=2)+'\n')
