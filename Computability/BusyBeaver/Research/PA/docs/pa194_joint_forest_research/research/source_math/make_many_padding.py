from make_dup_seeds import *
import hashlib
DOCS=corpus_docs()
basewords={tuple(word(s)) for s in shapes}
allsh={str(s):s for s in shapes};orig={str(s):str(PRIMARY) for s in shapes}
for p in DOCS.rglob('*grammar.json'):
 try:
  d=json.loads(p.read_text())
  if not isinstance(d,dict)or not isinstance(d.get('rules'),dict)or 'root' not in d:continue
  t=read(p);w=word(t)
  if len(w)!=190:continue
  if isinstance(w[-1],tuple)and w[-1][0]=='leaf':
   w[-1]='node49';t=adapt(t,w)
  if tuple(w)not in basewords:continue
  st=str(t)
  if st not in allsh:allsh[st]=t;orig[st]=str(p)
 except (ValueError,KeyError,TypeError,RecursionError,AssertionError):pass
print('Unique original shapes',len(allsh),flush=True)

def ins(t,p,b,pad):
 n=len(word(t));out=[]
 if p==b:out.append((pad,t))
 if p+n==b:out.append((t,pad))
 if isnode(t):
  m=p+len(word(t[0]))
  if p<=b<=m:out += [(u,t[1]) for u in ins(t[0],p,b,pad)]
  if m<=b<=p+n:out += [(t[0],u) for u in ins(t[1],m,b,pad)]
 return out
seeds=[];info=[];seen=set()
for s in allsh.values():
 for b in bounds+[189,190]:
  for pid,pad in enumerate(['node49',('node49','node49')]):
   for t in ins(s,0,b,pad):
    st=str(t)
    if st in seen:continue
    seen.add(st);seeds.append(t);info.append(dict(original=orig[str(s)],position=b,pad=pid+1))
print('Padding shape seeds',len(seeds),flush=True)
tokens=(PRIMARY/'research/joint_grammar/joint_ax11/seeds_h.txt').read_text().splitlines();nb=int(tokens[0]);text=tokens[:1+nb]+[str(len(seeds))]
for tid,t in enumerate(seeds):
 ns,root=tarray(t);text.append(f'{tid} {len(ns)} {root}')
 text.extend(' '.join(map(str,row))for row in ns)
(HERE/'many_padding.templates.txt').write_text('\n'.join(text)+'\n');(HERE/'many_padding.seeds.json').write_text(json.dumps(info,indent=2)+'\n')
