#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;A=OUT.parent/'architectures';sys.path.insert(0,str(A));import retained_template_query as Q
T,start,ret,o=Q.compile_query();assert ret==133
literal={}
for line in(A/'retained_template_query_133.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();literal[int(q),int(b)]=int(w),d,int(n)
assert T==literal and len(T)==266
reads={q:set()for q in range(133)};count=0;maxsteps=0
def leaves(tree,path=(),bits=()):
 if tree[0]in('z','p'):yield path,bits,0 if tree[0]=='z'else tree[1]+1
 else:
  for b in(0,1):yield from leaves(tree[1+b],path+(b,),bits+((tree[0]>>b)&1,))
for rule,tree in o['syntax'].items():
 for path,expected,leaf in leaves(tree):
  source=tuple(map(int,format(rule,'04b')))+path;n=len(source)
  for extra,c in itertools.product((2,7,19),(-17,0,23)):
   anchor=c+n+extra+1;tape={c}|set(range(anchor,anchor+5));p=anchor+6;marker=anchor+4
   for b in source:tape.update(range(p,p+b+3));marker=p+b+2;p+=b+4
   tape.discard(marker);tape|={c-4,c-8,p,p+3};want=tape|{marker,c+n}
   for j,b in enumerate(reversed(source)):
    if b:want.add(c+j)
    else:want.discard(c+j)
   output=expected+tuple(map(int,format(leaf,'03b')))
   for j,b in enumerate(output):
    pos=c+len(path)-1-j
    if b:want.add(pos)
    else:want.discard(pos)
   q=start;h=marker;steps=0
   while q!=ret:
    bit=int(h in tape);reads[q].add(bit);w,d,q=T[q,bit]
    if w:tape.add(h)
    else:tape.discard(h)
    h+=1 if d=='R'else-1;steps+=1;assert steps<1000000
   assert tape==want and h==c-4
   count+=1;maxsteps=max(maxsteps,steps)
forced1=[1,2,5,9,124,128];forced0=[0,13,*range(110,121),123]
assert all(reads[q]=={1}for q in forced1)and all(reads[q]=={0}for q in forced0)
result={'status':'PASS','working_states':133,'rows':266,'whole_tape_cases':count,'max_steps':maxsteps,'forced_one':forced1,'forced_zero':forced0,'table_sha256':hashlib.sha256((A/'retained_template_query_133.tm').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((A/'retained_template_query.py').read_bytes()).hexdigest()}
(OUT/'retained_template_query_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
reasons={'1':'reverse payload1: preceding source/sentinel one','2':'reverse payload2: preceding source/sentinel one','5':'reverse mark_previous0: existing previous field/sentinel last one','9':'reverse mark_previous1: existing previous field/sentinel last one','124':'selector prefix00: only permitted template rule3 has prefix00, whose next bit is1','128':'selector prefix001: only permitted template rule3 has prefix001, whose final bit is1','0':'reverse erased source marker','13':'reverse append into remaining zero gap','123':'selector prefix1: permitted template rules8..11 all start10'}
reasons.update({str(q):'Oracle leaf emitter reads a fresh original-frontier-left padding zero, one of the three reserved zero cells.'for q in range(110,121)})
guard={'table':'architectures/retained_template_query_133.tm','table_sha256':result['table_sha256'],'working_states':133,'start':start,'return':ret,'reject':18,'forced_one':forced1,'forced_zero':forced0,'allowed_reads':{str(q):[1]if q in forced1 else[0]if q in forced0 else[0,1]for q in range(133)},'proof_reasons':reasons,'entry_precondition':'Reverse-copy prepared frame with source bits four-bit rule3..11 followed by a genuine complete leaf path for that rule; gap>=total bit count+2; three cells immediately left of original frontier zero. Initial marker as reverse-copy contract.','status':'Ordinary-proof guards from reverse copy, finite selector cases, and mirrored oracle induction; regression support is not the proof.','proof_files':['reverse_path_copy_review.md','pattern_oracle_review.md','retained_template_query_review.md'],'scope_note':'Template query only. Do not use selector guards for calls with rules0,1,2 or malformed rule encodings. Prefix000 state127 and reject18 conservatively retain both reads.'}
(OUT/'retained_template_query_133_guards_reviewed.json').write_text(json.dumps(guard,indent=2)+'\n')
