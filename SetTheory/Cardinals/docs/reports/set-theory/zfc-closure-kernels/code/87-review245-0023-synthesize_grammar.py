"""Self-authored deterministic data-only routed-machine synthesizer.
Usage: python3 synthesize_grammar.py grammar.json output-prefix
Does not import or execute repository code. A syntactic table is NOT a correctness certificate.
"""
from pathlib import Path
import json,sys,hashlib,os
PACKAGE=Path(__file__).resolve().parent.parent
ROOT=PACKAGE/'results'
INPUTS=Path(os.environ.get('B245_INPUTS',PACKAGE/'inputs'))
SOURCE=INPUTS/'candidate-routing245/zfc_routing245_old.tm'
if not __debug__: raise RuntimeError('Assertions must remain enabled')
def synthesize(grammar_path,prefix):
 g=json.loads(Path(grammar_path).read_text());rules={w:(a,b)for w,a,b in g['rules']};assert len(rules)==len(g['rules'])
 oldalloc=json.loads((INPUTS/'certificate__allocation.json').read_text());inv={v:k for k,v in oldalloc.items()};term=json.loads((ROOT/'terminal_states.json').read_text())
 for w,(a,b)in rules.items():
  assert w==a+b and len(w)>1
  for child in[a,b]:assert child in rules or len(child)==1 and child in term
 t={}
 for line in SOURCE.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,n=line.split();t[int(q),int(b)]=(int(w),d,int(n))
 alloc={w:oldalloc[w]for w in rules if w in oldalloc};available=sorted(set(oldalloc.values())-set(alloc.values()))
 for w in sorted(set(rules)-set(alloc)):
  assert available,'Grammar exceeds available labels';alloc[w]=available.pop(0)
 routes={(x['source'],x['read']):x['word']for x in g['routes']};assert len(routes)==len(g['routes'])
 out={}
 for k,(w,d,n)in t.items():
  if k[0]in inv:continue
  target=routes.get(k,inv.get(n))
  if target is not None:
   assert target in alloc,(k,target,'missing required root');n=alloc[target]
  out[k]=(w,d,n)
 for word,(a,b)in rules.items():
  for bit,child in enumerate((a,b)):out[alloc[word],bit]=(bit,'R',term[child]if len(child)==1 else alloc[child])
 states={q for q,b in out};assert{n for w,d,n in out.values()}-states=={254};assert len(out)==2*len(states)
 order=[95]+sorted(states-{95});mapping={q:i for i,q in enumerate(order)}|{254:len(order)}
 def emit(rows,start):return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
 prefix=Path(prefix);prefix.parent.mkdir(parents=True,exist_ok=True)
 old=prefix.with_suffix('.old.tm');canonical=prefix.with_suffix('.tm');old.write_text(emit(out,95));canonical.write_text(emit({(mapping[q],b):(w,d,mapping[n])for(q,b),(w,d,n)in out.items()},0))
 info={'working_states':len(states),'grammar_states':len(rules),'framework_states':len(states)-len(rules),'allocation':alloc,'old_to_canonical':mapping,'canonical_to_old':order,'canonical_sha256':hashlib.sha256(canonical.read_bytes()).hexdigest(),'old_label_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'scope':'Syntactic construction only; routes, source bisimulation, runtime and blank startup need independent validation'}
 prefix.with_suffix('.json').write_text(json.dumps(info,indent=2)+'\n');return info
if __name__=='__main__':
 result=synthesize(*sys.argv[1:]);print({k:v for k,v in result.items()if k not in ['allocation','old_to_canonical','canonical_to_old']})
