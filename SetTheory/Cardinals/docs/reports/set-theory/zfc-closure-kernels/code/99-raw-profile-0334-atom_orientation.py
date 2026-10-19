"""Parameterized runtime probes for closed atomic entries in both orientations.

Each virtual grammar prefix is concrete. Register values and extra header gap
remain symbolic, using the unmodified inherited affine proof rules. These are
proofs of stated synthetic contexts, not a theorem for all source grammars.
"""
from pathlib import Path
from functools import lru_cache
import sys,json,time,itertools,os

BASE=Path(os.environ.get('ZFC245_BASELINE',str(Path(__file__).resolve().parents[2]/'baseline/zfc245-proof-20261018')))
sys.path.insert(0,str(BASE/'code'))
import parametric_prefix_affine as affine
source=json.loads((BASE/'inputs/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((BASE/'inputs/semantic-symbols.json').read_text())
encode={v:k for k,v in symbols.items()}
gram=json.loads((BASE/'grammar.json').read_text())
rules={w:(a,b)for w,a,b in gram['rules']}
words={int(q):''.join(encode[x]for x in w)for q,w in source['flattened_semantic_words'].items()}
by_ast={int(i):words[int(q)]for q,i in source['sequence_ast_roots'].items()}

@lru_cache(None)
def changed(i):
 if i in by_ast and by_ast[i]in rules:return expand(by_ast[i])
 row=source['ast_dag'][i]
 return ('L',tuple(row[1]))if row[0]=='L' else ('N',changed(row[1]),changed(row[2]))

@lru_cache(None)
def expand(word):
 if len(word)==1:return changed(source['atoms'][symbols[word]]['ast'])
 a,b=rules[word];return ('N',expand(a),expand(b))

def paths(ast,p=''):
 if ast[0]=='L':yield p,ast[1]
 else:
  yield from paths(ast[1],p+'0');yield from paths(ast[2],p+'1')

def inc(p):
 b=list(p);i=len(b)-1
 while i>=0 and b[i]=='1':b[i]='0';i-=1
 if i<0:return '',True
 b[i]='1';return ''.join(b),False

def strip(p,b,k):
 i=len(p)
 while k and i:
  i-=1
  if p[i]==b:k-=1
 return p[:i]

physical=(6,2,0,4,3,7,8,5,1)
table={}
for line in(BASE/'machine/zfc245_old.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,t=line.split();table[q,int(b)]=(int(w),d,t)

def virtual(prefix,q):
 t=table.copy()
 for i,b in enumerate(prefix):
  cur='96'if i==0 else str(10000+i)
  nxt=str(q)if i==len(prefix)-1 else str(10001+i)
  t[cur,int(b)]=(int(b),'R',nxt)
  t[cur,1-int(b)]=(1-int(b),'R','9999')
 t['9999',0]=(0,'R','9999');t['9999',1]=(1,'R','9999')
 return t

def check_case(t,p,op):
 kind,*arg=op;r=arg[0]if arg else None
 if kind in ('inc','dec'):r=physical[r]
 for zero in ((True,False)if kind=='dec'else(None,)):
  extra=0;effect=None;overflow=False
  if kind=='inc':successor,overflow=inc(p);effect=('inc',r)
  elif kind=='dec'and not zero:successor,overflow=inc(p);effect=('dec',r);extra=1
  elif kind=='dec':successor,overflow=inc(strip(p,'0',1))
  elif kind=='brk':successor,overflow=inc(strip(p,'0',r))
  elif kind=='cont':successor=strip(p,'1',r)
  else:assert kind=='halt';successor=''
  right=[('b',int(b))for b in successor]+[('r',0,1,affine.PADDING+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
  yield zero,affine.run(t,p,(r,zero)if kind=='dec'else None,affine.canon([('b',1)],right),halt=(kind=='halt'),fuel=1800)

def main():
 ambiguous={int(q)for q in source.get('ambiguous_atomic_states',[])}
 # Derive ambiguity directly too, because source metadata is not assumed complete.
 counts={}
 for info in source['atoms'].values():counts[info['state']]=counts.get(info['state'],0)+1
 ambiguous|={q for q,n in counts.items()if n>1}
 short='--short' in sys.argv
 selected={int(x)for x in sys.argv[1:] if not x.startswith('--')}
 output=Path(__file__).with_name('atom-orientation-short-results.jsonl'if short else'atom-orientation-results.jsonl')
 with output.open('w')as f:
  for name,info in source['atoms'].items():
   q=info['state']
   if q in ambiguous or(selected and q not in selected)or(short and not selected and q==150):continue
   leaves=list(paths(changed(info['ast'])))
   for bit in (0,1):
    began=time.monotonic();done=0;skipped=0;maxrules=0;failure=None
    prefixes=[''.join(p)+str(bit)for n in range(7)for p in itertools.product('01',repeat=n)] if short else (str(bit),'101'+str(bit),'01011'+str(bit))
    prefixes=[p for p in prefixes if '0000000'not in p]
    for prefix in prefixes:
     t=virtual(prefix,q);affine.PADDING=max(64,max(len(prefix+s)for s,op in leaves)+10)
     for s,op in leaves:
      p=prefix+s
      if '0000000'in p:skipped+=1;continue
      try:
       for zero,(used,lit)in check_case(t,p,op):done+=1;maxrules=max(maxrules,sum(used.values()))
      except Exception as exc:
       failure={'prefix':prefix,'pc':p,'op':op,'error':str(exc)};break
     if failure:break
    result={'state':q,'symbol':encode[name],'name':name,'incoming_bit':bit,'observed_bits':info['observed_final_incoming_bits'],'status':'FAIL'if failure else'PASS_SYNTHETIC_CONTEXTS','primitive_cases_passed':done,'source_leaves':len(leaves),'prefix_count':len(prefixes),'skipped_zero_run7':skipped,'max_rules':maxrules,'seconds':time.monotonic()-began,'failure':failure,'register_values':'universally quantified through inherited register-box induction contracts','header_extra':'universally quantified n>=0','scope':('all binary virtual outer prefixes of lengths1..7 without seven zeros'if short else'three concrete virtual outer prefixes')+'; unchanged affine inference rules; not all grammar contexts'}
    f.write(json.dumps(result)+'\n');f.flush();print(json.dumps({k:result[k]for k in('state','symbol','incoming_bit','status','primitive_cases_passed','failure')}),flush=True)
if __name__=='__main__':main()
