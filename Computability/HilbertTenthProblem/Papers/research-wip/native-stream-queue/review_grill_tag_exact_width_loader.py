#!/usr/bin/env python3
"""Independent bounded source/semantics audit of the exact-width Grill loader."""
import argparse,hashlib,json,random,sys,types
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
AUTHOR_PINS={'py':'685a5744c180439ca67cdfcb6eace118379365e3575c302cb19ce404aa29d2f4','json':'48f409c2eb7965ae26a4bef8b58a36ae366dfae3df4b3ca077d463581969fb75','md':'9076fcfd9d78c144ccb757dddb34bc5300f0d443336532e45dda621c73187da6'}
PINS={'grill_tag_native_composed205.py':'4084a58d5cf30694a8717c26d0abdf2aecc2fa6a7099d9815f35521005afab94','native_binary_input_dilation130.json':'175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182','native_binary_input_dilation130.py':'7e7ccb297083ffb799775d729b81ec0e403981f287af62513338c5d366fb9ac2','gpcp_fixed_program_input_bridge.py':'0d5023b52a5ffe87f5c9e26b436048571e75ccbebfd18c62f9820729b10b74f0','grill_tag_halt_bridge.py':'3984312d5a5d9c8ebfde557e683e32bcba7fc69dbf65cfe1a9037803eebdb892','grill_tag_native_word_closure.py':'80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7'}
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def normal(x):return json.loads(json.dumps(x))
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path):
 m=types.ModuleType('_independent_exact_width_native');m.__file__=str(path);exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__);return m

def counts(rows):
 c=Counter(r[1] for r in rows);return dict(total=len(rows),M=c['*'],A=c['+']+c['-'])
def run(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def value(e,v):return e[v] if type(v)is str else v

def block(N,y):
 a=28*(N+1);g=lambda r:'0'+'10'*r
 return '0'*(14*y+7)+g(a-3)+g(7)+g(a-4)+'0'*(3*a-14*y-10)
def literal_constants(N):
 a=28*(N+1);b=7*a;A=int(block(N,0)[::-1],2);K=1<<b;D=1<<14
 need(len(block(N,0))==b and len(block(N,1))==b and int(block(N,1)[::-1],2)==A*D,'Literal corrected blocks and shift')
 need(block(N,0).endswith('00') and block(N,1).endswith('00'),'Actual two trailing zeros')
 return dict(N=N,a=a,width=b,K=K,D=D,A=A,M=K-1,C=A*(K-1)*(D-1))
def binary_chain(width):
 exponent=1;last='q';source=[]
 for bit in bin(width)[3:]:
  exponent*=2;n='Q' if exponent==width else 'width_power'+str(exponent);source.append([n,'*',last,last]);last=n
  if bit=='1':
   exponent+=1;n='Q' if exponent==width else 'width_power'+str(exponent);source.append([n,'*',last,'q']);last=n
 need(exponent==width and last=='Q','Exact full power')
 return source

def independent_loader(old,N,width_port):
 c=literal_constants(N);chain=binary_chain(c['width'])
 need(old['source'][:3]==[['q2','*','q','q'],['Q','*','q2','q2'],['B','*',8,'Q']],'Exact two private power rows')
 need({n for n,o,a,b in old['source'] if 'q2' in (a,b)}=={'Q'},'Old q2 privacy')
 f=lambda v:('input_u' if v=='x' else 'spread_R' if v=='z' else 'rec__'+v) if type(v)is str else v
 source=[['input_u','+','x',1]]+[[f(n),op,f(a),f(b)] for n,op,a,b in chain+[['B','*',1<<(c['width']-1),'Q']]+old['source'][3:]]
 source += [['canonical_left','+','rec__input_slack','canonical_beta'],['canonical_right','+','input_u',1],['encoded_scaled','*',c['M'],'encoded_X'],['encoded_power','*',c['A'],'rec__Q'],['encoded_spread','*',c['C'],'spread_R'],['encoded_sum','+','encoded_power','encoded_spread'],['encoded_right','-','encoded_sum',c['A']]]
 pairs=[[f(a),f(b)] for a,b in old['comparisons']]+[['canonical_left','canonical_right'],['encoded_scaled','encoded_right'],[width_port,'rec__Q']]
 aux=[f(n) for n in old['auxiliaries']]+['spread_R','canonical_beta']
 return source,pairs,aux,c

def program():
 # Independent literal application of the corrected construction, N3, halt2,
 # source widths all1, nonhalt productions all00 at both source phases.
 a=112;out=[0]*1568;occupied=set()
 def put(i,v):
  need(i not in occupied and i%2==1 and 0<=i<len(out),'Distinct odd run row');occupied.add(i);out[i]=v
 for half in (0,784):
  for y in range(3):
   for i,v in [(28*y+17,a-3),(28*y+19,7),(28*y+21,a-4),(28*y+a+13,a-3),(28*y+a+15,7),(28*y+a+17,a-4)]:put(half+i,v)
   if y!=2:
    for offset,v in zip(range(3,16,2),(7,3,3*a-10,0,7,3,3*a-10)):put(half+14*y+2*a+offset,v)
 need(sum(x>0 for x in out)==60,'Literal60 positive phases')
 return tuple(out)

def finalizer(source,pairs,unit):
 rows=[r[:] for r in source];last=None
 for i,(a,b) in enumerate(pairs):
  r='final_res'+str(i);s='final_sq'+str(i);rows.extend([[r,'-',a,b],[s,'*',r,r]])
  if last is None:last=s
  else:n='final_sum'+str(i);rows.append([n,'+',last,s]);last=n
 rows.extend([['final_positive','+',last,1],['final_product','*',unit,'final_positive'],['final_output','-','final_product',1]])
 return rows

def audit(rows,free,output):
 ready=set(free);degree={n:1 for n in free};nodes={};counts0=counts(rows)
 for row in rows:
  need(type(row)is list and len(row)==4,'Literal list gate');n,op,a,b=row
  need(type(n)is str and n not in ready and type(op)is str and op in ['+','-','*'],'Valid fresh operation')
  need(all(type(v)is int or type(v)is str and v in ready for v in (a,b)),'Exact integer literal or prior input')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0
  degree[n]=da+db if op=='*' else max(da,db);ready.add(n);nodes[n]=(a,b)
 live=set();stack=[output]
 while stack:
  n=stack.pop()
  if type(n)is not str or n in live:continue
  live.add(n)
  if n in nodes:stack.extend(nodes[n])
 need(live==set(nodes)|set(free),'Every gate and coordinate used by complete output')
 return dict(**counts0,degree_upper=degree[output],witnesses=len(free)-1,all_live=True)

def final_polynomial(rows,output,cut_names):
 # Sparse polynomial in abstract U and literal residual-square atoms.
 zero=(0,)*len(cut_names);env={n:{tuple(int(j==i) for j in range(len(cut_names))):1} for i,n in enumerate(cut_names)}
 def add(a,b,s):
  r=dict(a)
  for m,c in b.items():r[m]=r.get(m,0)+s*c
  return {m:c for m,c in r.items() if c}
 def mul(a,b):
  r={}
  for m,c in a.items():
   for n,d in b.items():
    k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+c*d
  return {m:c for m,c in r.items() if c}
 for n,op,a,b in rows:
  if n in env:continue
  if any(type(v)is str and v not in env for v in (a,b)):continue
  av=env[a] if type(a)is str else {zero:a};bv=env[b] if type(b)is str else {zero:b}
  env[n]=mul(av,bv) if op=='*' else add(av,bv,1 if op=='+' else -1)
 need(output in env,'Finalizer source reconstructed from literal cut atoms');return env[output]

def verify(root,author):
 root=Path(root).resolve();author=Path(author);counts0=Counter()
 for ext,pin in AUTHOR_PINS.items():need(sha(author.with_suffix('.'+ext).read_bytes())==pin,'Frozen author '+ext)
 for n,pin in PINS.items():need(sha((root/n).read_bytes())==pin,'Pinned dependency '+n)
 receipt=json.loads(author.with_suffix('.json').read_text());p=receipt['complete'];old=json.loads((root/'native_binary_input_dilation130.json').read_text())['certificate']
 need(receipt['source_sha256']==AUTHOR_PINS['py'],'Receipt matches executed author source')
 table=program();need(list(table)==receipt['recipe']['program'] and len(table)==receipt['recipe']['grill_phase_count'],'Exact actual1568-phase source table')
 C=load(root/'grill_tag_native_composed205.py');limit=sys.getrecursionlimit()
 try:sys.setrecursionlimit(max(limit,32*len(table)+4096));native=normal(C.build(table,unit_product=True,root=root))
 finally:sys.setrecursionlimit(limit)
 need(sys.getrecursionlimit()==limit,'Restore interpreter recursion setting')
 f=lambda v:'encoded_X' if v=='x' else 'hist__'+v if type(v)is str else v
 H=[[f(n),o,f(a),f(b)] for n,o,a,b in native['source']];HP=[[f(a),f(b)] for a,b in native['comparisons']];unit=f(native['unit_register'])
 need(HP[-1]==[unit,1],'Native anchor interface')
 L,LP,LA,co=independent_loader(old,3,f(native['interfaces']['P0']))
 src=L+H;pairs=HP[:-1]+LP;rows=finalizer(src,pairs,unit);aux=['encoded_X']+[f(n) for n in native['auxiliaries']]+LA
 need(exact(src,p['source']) and exact(rows,p['polynomial_source']),'Complete independently reconstructed literal source')
 need(exact(pairs+[[unit,1]],p['comparisons']) and exact(aux,p['auxiliaries']),'Every comparison and positive coordinate preserved')
 need(exact(L,p['loader']['source']) and exact(LP,p['loader']['comparisons']) and exact(co,p['loader']['constants']),'Full independent loader source and literal E constants')
 ledger=audit(rows,['x']+aux,'final_output')
 need(ledger==dict(total=16291,M=4996,A=11295,degree_upper=283247,witnesses=3217,all_live=True),'Actual whole-program ledger and conservative degree')
 need(counts(native['polynomial_source'])==dict(total=16033,M=4880,A=11153),'Actual1568-phase native parent count')
 need(len(native['auxiliaries'])==3165 and len(HP)==11 and len(LP)==37 and len(LA)==51 and len(p['comparisons'])==48,'All witness/comparison increments')
 need(counts(L)==dict(total=147,M=79,A=68),'Loader prefix cost')
 need({k:counts(rows)[k]-counts(native['polynomial_source'])[k] for k in ('total','M','A')}==dict(total=258,M=116,A=142),'Entire111-gate new finalization paid')
 counts0['complete_literal_native_rows_preserved']=len(H);counts0['complete_literal_source_gates']=len(rows);counts0['current_positive_coordinates']=len(aux)
 # Literal finalizer polynomial in the same native U and47 explicit residual squares.
 sq=['final_sq'+str(i) for i in range(len(pairs))];abstract=final_polynomial(rows,'final_output',[unit]+sq);zero=(0,)*(1+len(sq));expected={zero:-1,tuple([1]+[0]*len(sq)):1}
 for i in range(len(sq)):
  key=[0]*(1+len(sq));key[0]=key[i+1]=1;expected[tuple(key)]=1
 need(abstract==expected,'Whole integer-unit finalizer exactly U*(1+all47squares)-1');counts0['symbolic_complete_finalizer_identity']=1
 for i,(a,b) in enumerate(pairs):
  need(['final_res'+str(i),'-',a,b] in rows and ['final_sq'+str(i),'*','final_res'+str(i),'final_res'+str(i)] in rows,'Every literal residual square');counts0['literal_residual_squares']=counts0.get('literal_residual_squares',0)+1
 # Exhaustively recover canonical n for a bounded census, including both boundary edges.
 for u in range(1,1025):
  actual=[n for n in range(2,13) if (1<<n)-u>0 and 2*u+1-(1<<n)>0]
  need(actual==([] if u==1 else [u.bit_length()]),'Natural canonical duration including excluded u1');counts0['canonical_input_census']=counts0.get('canonical_input_census',0)+1
 for bits in [2,3,7,16,31,64,127]:
  for u in [(1<<(bits-1)),(1<<(bits-1))+1,(1<<bits)-1]:
   q=1<<u.bit_length();s=q-u;beta=2*u+1-q
   need(s>0 and beta>0 and s+beta==u+1 and (u&(u-1)!=0 or beta==1),'All-length boundary identities');counts0['large_input_length_boundaries']+=1
 # Native Pell coordinates remain intentionally unmaterialized. These are genuine outer rows and AND ports.
 rng=random.Random(78431217);fixture_hashes=[]
 for N in (3,4,7):
  co=literal_constants(N);ls,lp,la,_=independent_loader(old,N,'initial_width')
  for x in list(range(1,25))+[31,32,63,64,127,128,255,256]:
   u=x+1;n=u.bit_length();q=1<<n;Q=1<<(n*co['width']);B=(1<<(co['width']-1))*Q;P=pow(B,n);J=(P-1)//(B-1);K=(q*P-1)//(2*B-1)
   R=sum(((u>>i)&1)<<(co['width']*i) for i in range(n));word=''.join(block(N,(u>>i)&1) for i in range(n));X=int(word[::-1],2);A=(u*J)&K
   need(len(word)==n*co['width'] and X==co['A']*((Q-1)//co['M']+(co['D']-1)*R),'Exact LSBF concatenation for every source bit')
   need(0<3*X<Q and (A-R)%(Q-1)==0,'Strict native cone and honest recoder remainder')
   v={name:1 for name in ['x','encoded_X','initial_width']+la};v.update(x=x,encoded_X=X,initial_width=Q,spread_R=R,canonical_beta=2*u+1-q,rec__q=q,rec__P=P,rec__J=J,rec__K=K,rec__Ahat=A+1,rec__quotient_hat=(A-R)//(Q-1)+1,rec__input_slack=q-u,rec__output_slack=Q-R)
   e=run(ls,v);rr=[value(e,a)-value(e,b) for a,b in lp]
   need(rr[:5]==[0]*5 and rr[-3:]==[0]*3 and J.bit_count()==n and J>B,'Genuine actual outer/canonical/binding rows')
   need(e['rec__copies']&K==A,'Genuine intended native AND inputs')
   for scale in (2,64):
    altered=dict(v,initial_width=scale*Q);ee=run(ls,altered);need(value(ee,lp[-1][0])-value(ee,lp[-1][1])==(scale-1)*Q,'False added terminal width rejected');counts0['padding_rejections']+=1
   counts0['genuine_loader_outer_interfaces']+=1
   fixture_hashes.append(dict(N=N,x=x,n=n,word_sha256=sha(word.encode()),X_bytes_sha256=sha(X.to_bytes((X.bit_length()+7)//8,'big'))))
  for i in range(24):
   J,Q,R=[rng.randrange(-9,10) for _ in range(3)];X=co['A']*(J+(co['D']-1)*R)
   need(co['M']*X-co['A']*Q-co['C']*R+co['A']==co['A']*(co['M']*J-Q+1),'Independent all-integer affine graph identity');counts0['signed_loader_graph_identities']+=1
 # Full literal parent/new output corrections beyond author fixtures. Small J=0 keeps this bounded.
 oldrows=[[f(n),o,f(a),f(b)] for n,o,a,b in native['polynomial_source']]
 for i in range(16):
  v={n:rng.randrange(-2,4) if i>=8 else rng.randrange(1,4) for n in ['x']+aux}
  for name in native['auxiliaries']:
   if name.startswith('Shat'):v[f(name)]=1
  e=run(rows,v);oe=run(oldrows,{n:v[n] for n in ['encoded_X']+[f(n) for n in native['auxiliaries']]})
  SL=sum((value(e,a)-value(e,b))**2 for a,b in LP)
  need(e['final_output']==oe[f(native['output'])]+e[unit]*SL,'Complete signed correction against actual native parent')
  counts0['full_parent_output_corrections']+=1;counts0['signed_full_parent_output_corrections']+=i>=8
 return dict(status='PASS_INDEPENDENT_EXACT_WIDTH_LOADER',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,dependency_pins=PINS,counts=dict(counts0),ledger=ledger,fixture_hashes=fixture_hashes,
   reused='Authenticated native205 builder and its transitive reviewed theorem/source guards; no author loader/composition/test function reused.',
   scope='One actual1568-phase reject-all source. Exact LSBF binary(x+1) loading and fixed-width halting composition under valid corrected source halt protocol; no numerical universal recognizer. Full positive native existence inherited, outer tests not full Pell witnesses. Internal author routines are not supported hostile-packet APIs.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author',type=Path,default=Path(__file__).with_name('grill_tag_exact_width_loader.py'));ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.author);raw=json.dumps(r,indent=2,sort_keys=True)+'\n'
 if a.output:a.output.write_text(raw)
 if a.expect:need(exact(json.loads(raw),json.loads(a.expect.read_text())),'Fresh exact independent receipt')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledger':r['ledger']},sort_keys=True))
if __name__=='__main__':main()
