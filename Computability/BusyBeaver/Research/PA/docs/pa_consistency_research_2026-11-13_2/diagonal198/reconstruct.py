#!/usr/bin/env python3
"""Reconstruct the 203-state allocation and five folds from pinned PA196 data."""
if not __debug__:
    raise RuntimeError('Verification requires Python without -O or -OO.')
from pathlib import Path
import ast,json,re,hashlib
HERE=Path(__file__).resolve().parent
TABLE_SHA256='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
MACROS={'node65':90,'node55':98,'node58':12,'node70':166,'node49':19,'node72':69,'node75':213,'node142':194,'node150':221,('leaf','inc',1):61,'node60':99,'node61':190}
PROTECTED={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
BREAK=('leaf','breakTo',1)

def table(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();key=int(q),int(b);assert key not in rows
  rows[key]=(int(w),d,int(n))
 return rows

def reconstruct():
 reference=HERE/'reference'
 assert hashlib.sha256((reference/'pa196.tm').read_bytes()).hexdigest()==TABLE_SHA256
 source=(reference/'Conjugacy.lean').read_text()
 labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',source)[1])
 assert len(labels)==197 and len(set(labels))==197 and labels[0]==74 and labels[-1]==254
 old={(labels[q],b):(w,d,labels[n])for(q,b),(w,d,n)in table(reference/'pa196.tm').items()}
 raw_nodes={}
 for line in(reference/'Program.lean').read_text().splitlines():
  m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
  if not m:continue
  fields=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
  children=[name if name else('leaf',op,int(arg)if arg else None)for op,arg,name in fields]
  assert len(children)==2;raw_nodes[m[1]]=tuple(children)
 assert len(raw_nodes)==159
 grammar=json.loads((HERE/'ax.grammar.json').read_text())
 def decode(t):
  if isinstance(t,list):return tuple(t)
  if t in grammar['rules']:return tuple(decode(c)for c in grammar['rules'][t])
  return t
 ax=decode(grammar['root'])
 def expand(t):
  if t=='x67':return expand(ax)
  if isinstance(t,str):return expand(raw_nodes[t])
  if t[0]=='leaf':return[t[1],t[2]or 0]
  return list(map(expand,t))
 assert expand('node172')==json.loads((HERE/'source.tree.json').read_text())
 raw={(q,b):act for(q,b),act in old.items()if q<1300};index={}
 def state(t):
  if t in MACROS:return MACROS[t]
  if t in index:return index[t]
  assert isinstance(t,tuple)and len(t)==2
  q=2000+len(index);index[t]=q
  for b,child in enumerate(t):raw[q,b]=(0,'L',302)if child==BREAK else(b,'R',state(child))
  return q
 root=state(ax);raw[101,1]=(1,'R',root)
 assert len(index)==69 and len(raw)==406
 receipt=json.loads((HERE/'receipt.json').read_text());folds=receipt['folds'];assert len(folds)==5
 alias={a:b for a,b,_ in folds};actions={b:[(w,'R'if right else'L',n)for w,right,n in acts]for a,b,acts in folds}
 assert len(alias)==len(actions)==5 and not(set(alias)&set(actions))
 folded={}
 for(q,b),act in raw.items():
  if q in alias:continue
  w,d,n=actions[q][b]if q in actions else act
  folded[q,b]=(w,d,alias.get(n,n))
 assert len(folded)==396 and folded==table(HERE/'machine.native.tm')
 for q in PROTECTED:
  for b in(0,1):assert folded[q,b]==old[q,b]
 return {'raw_working_states':203,'new_ax_readers':69,'compatible_context_folds':5,'working_states':198,'exact_native_table_reconstructed':True,'exact_source_tree_reconstructed':True,'protected_engine_rows_directly_equal_to_pa196':46}
if __name__=='__main__':print(json.dumps(reconstruct(),indent=2))
