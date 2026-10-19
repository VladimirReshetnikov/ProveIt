#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib,random
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;A=OUT.parent/'architectures';sys.path.insert(0,str(A));import reverse_path_copy as R
T,start,ret,ids=R.compile_copy();assert ret==19 and len(T)==38
literal={}
for line in(A/'reverse_path_copy_19.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();literal[int(q),int(b)]=int(w),d,int(n)
assert T==literal
reads={q:set()for q in range(19)};count=0;maxsteps=0
cases=[bits for n in range(8)for bits in itertools.product(range(2),repeat=n)]
rng=random.Random(191902)
cases += [tuple(rng.randrange(2)for _ in range(rng.randrange(45)))for _ in range(100)]
for bits in cases:
 for extra,c,mask in((2,0,0),(2,-13,63),(9,27,21)):
  g=len(bits)+extra;anchor=c+g+1;tape={c}|set(range(anchor,anchor+5));p=anchor+6;marker=anchor+4
  for b in bits:tape.update(range(p,p+b+3));marker=p+b+2;p+=b+4
  tape.discard(marker)
  for j in range(3):
   if mask>>j&1:tape.add(c-j-1)
   if mask>>(j+3)&1:tape.add(p+j)
  expected=tape|{marker,c+len(bits)}
  for j,b in enumerate(reversed(bits)):
   if b:expected.add(c+j)
   else:expected.discard(c+j)
  q=start;h=marker;steps=0
  while q!=ret:
   assert c<=h<=marker+1;bit=int(h in tape);reads[q].add(bit);w,d,q=T[q,bit]
   if w:tape.add(h)
   else:tape.discard(h)
   h+=1 if d=='R'else-1;steps+=1;assert steps<1000000
  assert tape==expected and h==c+len(bits)-1
  count+=1;maxsteps=max(maxsteps,steps)
ones=[ids[x]for x in('payload1','payload2',('mark_previous',0),('mark_previous',1))];zeros=[ids[x]for x in('restore','append')]
assert all(reads[q]=={1}for q in ones)and all(reads[q]=={0}for q in zeros)
result={'status':'PASS','working_states':19,'operational_states':18,'rows':38,'whole_tape_cases':count,'max_steps':maxsteps,'forced_one':ones,'forced_zero':zeros,'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[A/'reverse_path_copy.py',A/'reverse_path_copy_19.tm']}}
(OUT/'reverse_path_copy_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
proof={str(ids['payload1']):'Restored branch/sentinel has at least three ones; this is its second-last one.',str(ids['payload2']):'Restored branch/sentinel has at least three ones; this is its third-last one.',str(ids['mark_previous',0]):'For a decoded branch0, preceding field or five-one sentinel exists and its last one has not been changed.',str(ids['mark_previous',1]):'For a decoded branch1, preceding field or five-one sentinel exists and its last one has not been changed.',str(ids['restore']):'Entry is the erased final one; later forward scans return to that same moving erased-one marker.',str(ids['append']):'Copied count k<n and gap>=n+2 leave the cell after current frontier zero.'}
guards={'table':'architectures/reverse_path_copy_19.tm','table_sha256':result['hashes']['reverse_path_copy_19.tm'],'start':start,'return':ret,'reject':ids['reject'],'working_states':19,'forced_one':ones,'forced_zero':zeros,'allowed_reads':{str(q):[1]if q in ones else[0]if q in zeros else[0,1]for q in range(19)},'proof_reasons':proof,'status':'Conservative ordinary-proof guards; full induction in reverse_path_copy_review.md, not inferred solely from finite coverage.','entry_precondition':'Frontier1, gap>=n+2 zeros, sentinel111110, n branch fields1^(b+3)0 with b=0/1; erase last one of last branch or sentinel for n=0; enter restore at erased cell.','composition_note':'Copier preserves arbitrary left exterior. Pairing mirrored oracle leaf emitters as forced0 additionally requires three zero cells immediately left of the original frontier before oracle call.'}
(OUT/'reverse_path_copy_19_guards_reviewed.json').write_text(json.dumps(guards,indent=2)+'\n')
