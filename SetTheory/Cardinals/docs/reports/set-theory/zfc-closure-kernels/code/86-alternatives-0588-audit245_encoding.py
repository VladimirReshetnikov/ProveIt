#!/usr/bin/env python3
"""Independent literal allocation, closed-association and local-route audit.
No producer code is imported and no heuristic search is run.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
from functools import lru_cache
import re,json,hashlib
OUT=Path(__file__).resolve().parent
P=OUT.parent/'audit245/extracted/zfc245-proof-20261018'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R');t[q,b]=w,d,n
 return t
B=read(P/'reference/tables/zfc_prefix246_old.tm');M=read(P/'machine/zfc245_old.tm');C=read(P/'machine/zfc245.tm')
pinned=OUT.parent/'source/Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm'
assert B==read(pinned)==read(P/'reference/context246/machine/zfc_prefix246_old.tm')
S=json.loads((P/'inputs/closed-sequence-grammar-next22.json').read_text());G=json.loads((P/'grammar.json').read_text());SYM=json.loads((P/'inputs/semantic-symbols.json').read_text());enc={v:k for k,v in SYM.items()}
seq=set(S['sequence_states']);states={q for q,b in B};words={int(q):''.join(enc[x]for x in w)for q,w in S['flattened_semantic_words'].items()};rules={w:(l,r)for w,l,r in G['rules']};routes={(x['source'],x['read']):x['word']for x in G['routes']};erased={74,177}
assert len(seq)==len(words)==127 and len(states)==246 and len(rules)==128
assert G['erase177']and G['retarget']==-2 and not G.get('root_word_overrides')and 'modified_AX_word'not in G
# Independently reconstruct allocation exactly, then every old-label row.
alloc={w:q for q,w in words.items()if w in rules};available=sorted((seq|erased)-set(alloc.values()))
for w in sorted(set(rules)-set(alloc)):alloc[w]=available.pop(0)
assert alloc==json.loads((P/'certificate/allocation.json').read_text())
assert len(set(alloc.values()))==128
atomstate={ch:S['atoms'][name]['state']for ch,name in SYM.items()}
def target(w):return alloc[w]if len(w)>1 else atomstate[w]
expected={}
for(q,b),(w,d,t)in B.items():
 if q in seq|erased:continue
 if(q,b)==(58,0):expected[q,b]=0,'L',84
 elif(q,b)in routes:expected[q,b]=w,d,alloc[routes[q,b]]
 elif t in seq:expected[q,b]=w,d,alloc[words[t]]
 else:assert t not in erased;expected[q,b]=w,d,t
for w,(l,r)in rules.items():
 assert w==l+r and l and r
 for b,child in enumerate((l,r)):
  assert child in rules or child in SYM
  expected[alloc[w],b]=b,'R',target(child)
assert expected==M
newstates={q for q,b in M};assert len(newstates)==245 and len(M)==490
assert states-newstates=={247} and not newstates-states
assert set(t for w,d,t in M.values())-newstates=={254}
order=[95]+sorted(newstates-{95});ren={q:i for i,q in enumerate(order)}|{254:245}
assert {(ren[q],b):(w,d,ren[t])for(q,b),(w,d,t)in M.items()}==C
for f in ('machine/renumbering.json','certificate/renumbering.json'):
 obj=json.loads((P/f).read_text());assert{int(k):v for k,v in obj['old_to_canonical'].items()}==ren and obj['canonical_to_old']==order
assert ren[95]==0 and ren[96]==88 and ren[254]==245
assert set(q for q,b in C)==set(range(245))and len(C)==490 and not any(q==245 for q,b in C)
# Fresh parse of full original Prog254.v; compare the exact original AST.
assert (P/'reference/source/Prog254.v').read_bytes()==(OUT.parent/'source/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_bytes()
assert sha(P/'reference/source/Prog254.v')==S['source_sha256']
text=(P/'reference/source/Prog254.v').read_text();body=text.split('Definition p254_tab :')[1].split(':= [',1)[1].split('].',1)[0]
pairs=re.findall(r'\((C[INDCBH]\w*(?:\s+\d+)?),\s*(C[INDCBH]\w*(?:\s+\d+)?)\)',body)
# Explicit instruction alphabet avoids accepting omitted/unrecognized pairs.
def edge(e):
 bits=e.split();op=bits[0];assert op in('CN','CI','CD','CB','CC','CH')
 return(op,int(bits[1]))if len(bits)==2 else(op,)
ptable=[tuple(edge(x)for x in p)for p in pairs];assert len(ptable)==6459
ops={'CI':'inc','CD':'dec','CB':'brk','CC':'cont','CH':'halt'}
@lru_cache(None)
def pn(i):return('N',*(pn(e[1])if e[0]=='CN'else('L',(ops[e[0]],)+e[1:])for e in ptable[i]))
@lru_cache(None)
def ast(i):
 row=S['ast_dag'][i]
 return('L',tuple(row[1]))if row[0]=='L'else('N',ast(row[1]),ast(row[2]))
original=ast(S['original_ast']);assert original==pn(0)
@lru_cache(None)
def bounds(t):
 if t[0]=='L':
  op,*a=t[1];return(1 if op=='dec'else a[0]if op=='brk'else 0,a[0]if op=='cont'else 0)
 lb,lc=bounds(t[1]);rb,rc=bounds(t[2]);return(max(lb-1,rb,0),max(lc,rc-1,0))
for name,info in S['atoms'].items():assert bounds(ast(info['ast']))==(0,0)==tuple(info['bounds'])
for q,i in S['sequence_ast_roots'].items():
 t=ast(i);assert t[0]=='N'and bounds(t[1])==bounds(t[2])==(0,0)
# Validate original physical sequence edges and all incoming-edge lists.
for q in seq:
 assert [B[q,b]for b in(0,1)]==[(b,'R',S['rules'][str(q)][b])for b in(0,1)]
 assert sorted([p,b]for(p,b),(_,_,t)in B.items()if t==q)==sorted(S['incoming'][str(q)])
# Each sequence state's original AST is exactly its symbol-word AST, with
# literal original binary association and correct atom-variant spelling.
source_lines=(P/'inputs/semantic.txt').read_text().splitlines();ns,nroots,natoms=map(int,source_lines[0].split());assert(ns,nroots,natoms)==(127,24,44)
oldrules={w:(w[:int(k)],w[int(k):])for k,w,q in map(str.split,source_lines[1:128])}
allowed={c:int(m)for c,m in map(str.split,source_lines[1+127+24:])}
derived_allowed={c:0 for c in SYM}
for q,word in words.items():
 for bit,child in enumerate(oldrules[word]):
  original_target=next(v for v,w in words.items()if w==child)if len(child)>1 else atomstate[child]
  assert B[q,bit]==(bit,'R',original_target)
  if len(child)==1:derived_allowed[child]|=1<<bit
assert derived_allowed==allowed
for info in S['atoms'].values():assert [B[info['state'],bit]for bit in(0,1)]==[tuple(row)for row in info['rows']]
@lru_cache(None)
def old_expand(w):
 if len(w)==1:return ast(S['atoms'][SYM[w]]['ast'])
 return('N',*(old_expand(c)for c in oldrules[w]))
for q,i in S['sequence_ast_roots'].items():assert old_expand(words[int(q)])==ast(i)
byast={i:words[int(q)]for q,i in S['sequence_ast_roots'].items()}
@lru_cache(None)
def changed(i):
 if i in byast and byast[i]in rules:return expand(byast[i])
 row=S['ast_dag'][i];return('L',tuple(row[1]))if row[0]=='L'else('N',changed(row[1]),changed(row[2]))
@lru_cache(None)
def expand(w):
 if len(w)==1:return changed(S['atoms'][SYM[w]]['ast'])
 return('N',*(expand(c)for c in rules[w]))
new=changed(S['original_ast'])
@lru_cache(None)
def normal(t):
 if t[0]=='L':return t
 a,b=normal(t[1]),normal(t[2])
 if bounds(t[1])==bounds(t[2])==(0,0):
  return('S',*(a[1:]if a[0]=='S'else(a,)),*(b[1:]if b[0]=='S'else(b,)))
 return('N',a,b)
assert normal(original)==normal(new),'Not merely closed-atom reassociation'
def leaves(t,p=''):
 if t[0]=='L':return[(p,t[1])]
 return leaves(t[1],p+'0')+leaves(t[2],p+'1')
a,b=leaves(original),leaves(new);assert len(a)==len(b)==6460 and[x for p,x in a]==[x for p,x in b]
metrics={'leading_zeros':len(b[0][0]),'max_zero_run':max(len(z)for p,x in b for z in p.split('1')),'max_depth':max(len(p)for p,x in b)}
assert metrics=={'leading_zeros':3,'max_zero_run':6,'max_depth':51}
orientation_checks=0
for w,children in rules.items():
 for bit,c in enumerate(children):
  if len(c)==1:assert allowed[c]&(1<<bit);orientation_checks+=1
# All22 special-entry equations, checked against BOTH literal tables. Every
# inspected cell is either previous=-1 or the just-written cell0.
def projection(word,bits):
 for bit in bits:assert word in rules;word=rules[word][int(bit)]
 return word
local=[]
for x in S['left_entry_projection_constraints']:
 why=x['reason'];q,read,previous=why['source'],why['read'],why['previous'];bits=(str(previous)if why.get('via')==177 else'')+x['prefix'];assert bits==(str(previous)+str(why['write']))[:len(bits)]
 assert 1<=len(bits)<=2 and(q,read)in routes
 wanted=''.join(enc[z]for z in x['word']);assert projection(routes[q,read],bits)==wanted
 oldstate=B[q,read][2];newstate=M[q,read][2];assert B[q,read][:2]==M[q,read][:2]==(why['write'],'L')
 for bit in bits:
  bit=int(bit);ow,od,oldstate=B[oldstate,bit];nw,nd,newstate=M[newstate,bit];assert(ow,od)==(nw,nd)==(bit,'R')
 assert newstate==target(wanted)
 assert oldstate==(S['atoms'][SYM[wanted]]['state']if len(wanted)==1 else next(k for k,v in words.items()if v==wanted))
 local.append({'source':q,'read':read,'previous':previous,'bits':bits,'old_entry':B[q,read][2],'new_entry':M[q,read][2],'old_endpoint':oldstate,'new_endpoint':newstate,'semantic_word':wanted,'steps':1+len(bits),'head_offset':len(bits)-1})
assert len(local)==22 and set((x['source'],x['read'])for x in local)==set(routes)
all_left_entries={(q,b)for(q,b),(w,d,t)in B.items()if q not in seq|erased and t in seq|{177}and d=='L'}
assert all_left_entries==set(routes)
assert all({x['previous']for x in local if(x['source'],x['read'])==entry}=={0,1}for entry in routes)
assert {(q,b)for(q,b),(w,d,t)in B.items()if t==177}=={(153,1),(159,0)}
# Exhaustive unchanged outside callers and released roots.
released=[]
for q in S['required_entry_roots']:
 outside=[tuple(x)for x in S['incoming'][str(q)]if x[0]not in seq]
 if outside and all(x in routes or x[0]in erased for x in outside):released.append(q)
 else:assert words[q]in rules
for(q,b),(w,d,t)in B.items():
 if q in seq|erased or(q,b)in routes or(q,b)==(58,0):continue
 assert t not in erased
 if t in seq:assert words[t]in rules
#54 exact row equations ensure inherited bootstrap decoding is preserved.
ls=(P/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines();assert int(ls[0])==len(ls)-1==54
for row in ls[1:]:
 w,b,t=row.split();assert oldrules[w][int(b)]==t and projection(w,b)==t and M[alloc[w],int(b)]==(int(b),'R',target(t))
reachable=set()
def visit(w):
 if len(w)==1 or w in reachable:return
 reachable.add(w)
 for c in rules[w]:visit(c)
for w in {words[q]for q in S['required_entry_roots']if q not in released}|set(routes.values()):visit(w)
assert reachable==set(rules)
report={'status':'PASS_ENCODING_AND_ROUTING','canonical_sha256':sha(P/'machine/zfc245.tm'),'old_sha256':sha(P/'machine/zfc245_old.tm'),'grammar_sha256':sha(P/'grammar.json'),'baseline_matches_pinned':True,'source_Coq_nodes':len(ptable),'source_leaves':len(leaves(new)),'closed_atoms':44,'closed_normal_forms_equal':True,'source_metrics':metrics,'orientation_checks':orientation_checks,'orientation_masks_rederived_from_original_literal_edges':True,'left_entry_groups_exhaustive':len(all_left_entries),'all_local_routes':local,'bootstrap_equations':54,'state_ledger':{'baseline_framework':119,'baseline_grammar':127,'eliminated_framework_roles':[74,177],'final_framework':117,'final_grammar':128,'working_states':245,'rows':490,'separate_halt':245},'old_labels_removed':sorted(states-newstates),'old_labels_added':sorted(newstates-states),'grammar_words_removed':len(set(words.values())-set(rules)),'grammar_words_added':len(set(rules)-set(words.values())),'reused_numeric_labels':{str(q):next(w for w,v in alloc.items()if v==q)for q in(74,177,208)},'released_entry_roots':released,'all_grammar_rules_reachable':True,'changed_baseline_rows':sum(B.get(k)!=v for k,v in M.items()),'scope':'Allocation, exact table reconstruction, canonical renumbering, closed-association normal form, local routing and bootstrap equations. Scanner safety and complete runtime/logical calibration are separate audits.'}
(OUT/'audit245_encoding.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in('all_local_routes','reused_numeric_labels')},indent=2))
