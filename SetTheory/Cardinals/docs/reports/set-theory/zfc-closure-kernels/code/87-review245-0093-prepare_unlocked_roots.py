"""Derive exactly the retained entry roots from the literal 245 framework table."""
import json
import search_grammar as s
allocation=json.loads((s.BASE/'certificate__allocation.json').read_text())
inverse={q:w for w,q in allocation.items()};grammar_states=set(inverse);required=set()
for line in (s.BASE/'candidate-routing245/zfc_routing245_old.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,write,direction,t=line.split();q,b,t=map(int,(q,b,t))
 if q not in grammar_states and t in grammar_states and(q,b)not in s.ROUTES:required.add(inverse[t])
assert len(required)==14
text=(s.OUT/'joint-input.txt').read_text().splitlines();n=int(text[0]);words=[l.split()[0]for l in text[1:n+1]];ids={w:i for i,w in enumerate(words)}
i=n+1;n=int(text[i]);i+=n+1;n=int(text[i]);i+=n+1
text[i]=str(len(required))+' '+ ' '.join(str(ids[w])for w in sorted(required))
(s.OUT/'joint-unlocked-roots-input.txt').write_text('\n'.join(text)+'\n')
(s.OUT/'true_framework_roots.json').write_text(json.dumps(sorted(required),indent=2)+'\n')
print('Retained14 unchanged-framework entry roots; released18 bootstrap-only root requirements')
