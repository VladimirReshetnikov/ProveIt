"""Independent exact six-cut and complete-array audit; all predecessor files inert."""
import argparse,hashlib,json,random
from pathlib import Path
from collections import Counter
AUTHOR={
 'residue_affine_sparse_shared471.py':'8940d9c5b008bbe9d6ea210d938634afec1e59a76362b2c3a4aa25c53d460246',
 'residue_affine_sparse_shared471.json':'4732844a06fb9285d9fc57aa8dcd220e3664f965ec850393c830d2a453832ced',
 'residue_affine_sparse_shared471.md':'12c4725b79fe4e9173bef944100e41612b20e213f13b8f470d34802d6c5839c4'}
PINS={
 'residue_affine_sparse_shared477.py':'21463ce43e33aea904401277940f83990e033018ab624d8367b11c7eee9c2b0f',
 'residue_affine_sparse_shared477.json':'3472269ef557bfbcb6dd2697f9a780990bb394d7e370cadb282f7b03a4cd3716',
 'residue_affine_sparse_shared477.md':'95c37d45ea3ca2d7e7d653173f22e9821ee85036abe3a345ec0c563348b8f2b9',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
 'native_binary_norm_units.py':'1f088e43e60f068f2ca7c78a607f4cc5cd4ec34b7d2d5259c9ce545f74fdfee9'}
EDIT={
 'prime_selector_99':['+','edge_16','control_codes__target_class_35'],
 'prime_selector_101':['+','prime_selector_99','control_codes__duplicate_state_3'],
 'prime_selector_105':['+','prime_selector_103','control_codes__duplicate_state_2'],
 'prime_selector_107':['+','prime_selector_105','control_codes__duplicate_state_5'],
 'prime_selector_109':['+','prime_selector_107','control_codes__duplicate_state_8'],
 'control_codes__current_positive_19':['+','u21_grouped_J_0','prime_selector_95']}
GONE={'prime_selector_98','prime_selector_100','prime_selector_104','prime_selector_106','prime_selector_108','control_codes__current_multiple_9'}
OUT='norm_output'
def need(v,msg):
 if not v:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def pairs(v):
 out={}
 for k,x in v:need(k not in out,'duplicate JSON key');out[k]=x
 return out
def invalid(v):raise ValueError('noninteger/nonfinite '+v)
def read(p):return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=invalid,parse_constant=invalid)
def pins(root,p):
 for n,h in p.items():need(sha((root/n).read_bytes())==h,'pin '+n)
def table(rows):
 d={}
 for r in rows:
  need(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  need(type(n)is str and n not in d and o in ('+','-','*'),'SSA/op')
  need(all(type(x)in(int,str)for x in(a,b)),'operand types');d[n]=r
 return d
def free(rows):
 names=set(table(rows));return sorted({x for r in rows for x in r[2:] if type(x)is str and x not in names})
def audit(rows):
 d=table(rows);ports=free(rows);seen=set(ports)
 for n,o,a,b in rows:
  need(n not in seen and all(type(x)is int or x in seen for x in (a,b)),'topology '+n);seen.add(n)
 live=set();todo=[OUT]
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n)
  if n in d:todo.extend(d[n][2:])
 need(live==seen,'row/port liveness')
 c=Counter(r[1]for r in rows)
 return {'operations':len(rows),'multiplications':c['*'],'additions_subtractions':c['+']+c['-']}

def add(a,b,s=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+s*v
 return {m:v for m,v in c.items()if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n));c[k]=c.get(k,0)+v*w
 return {m:v for m,v in c.items()if v}
def expand(rows,target,boundaries):
 d=table(rows);memo={n:{(n,):1}for n in boundaries};cone=set()
 def at(n):
  if type(n)is int:return {():n}if n else{}
  if n not in memo:
   need(n in d,'unknown local leaf '+n);_,o,a,b=d[n];aa,bb=at(a),at(b);cone.add(n)
   memo[n]=mul(aa,bb)if o=='*'else add(aa,bb,1 if o=='+'else-1)
   need(len(memo[n])<1000,'bounded sparse expansion')
  return memo[n]
 return at(target),sorted(cone)
def plist(p):return [[list(m),v]for m,v in sorted(p.items())]

def exact(old,new):
 hats={f'edge{i}_hat'for i in range(36)};proof={}
 for n in EDIT:
  a,ca=expand(old,n,hats);b,cb=expand(new,n,hats);need(a==b,'six-cut polynomial '+n)
  need(all(len(m)<=1 for m in a),'affine cut')
  proof[n]={'raw_hat_polynomial':plist(a),'parent_cone':ca,'child_cone':cb}
 pool={}
 def intern(k):
  if k not in pool:pool[k]=len(pool)
  return pool[k]
 ports=free(old);envs=[]
 for rows in (old,new):
  env={n:intern(('supplied',n))for n in ports}
  for n,o,a,b in rows:
   def value(x):return intern(('integer',x))if type(x)is int else env[x]
   node=intern((o,value(a),value(b)))
   if n in EDIT:
    p,_=expand(rows,n,hats)
    # Exact polynomial is interpreted at actual supplied-hat expressions.
    actual=tuple(sorted((coef,tuple(env[x]for x in mon))for mon,coef in p.items()))
    if envs:need(all(env[h]==envs[0][h]for h in hats),'actual raw hat binding')
    node=intern(('integer_polynomial_at_actual_hats',actual))
   env[n]=node
  envs.append(env)
 need(all(envs[0][n]==envs[1][n]for n in table(new)),'complete471 value identity')
 return {'six_exact_raw_hat_cuts':proof,'same_value_registers':len(new),'intern_node_count':len(pool),'equality_method':'Exact tuple-intern IDs; no digest-based expression comparison; each polynomial is bound to actual equal supplied hat values'}

def degree(rows):
 ports=free(rows);raw={n:1 for n in ports}
 for n,o,a,b in rows:
  a=0 if type(a)is int else raw[a];b=0 if type(b)is int else raw[b];raw[n]=a+b if o=='*'else max(a,b)
 bd={'native__wn2','native__R12','native__R10a','native__gam'};p,cone=expand(rows,'native__R15',bd)
 X='native__wn2';a='native__R12';c='native__R10a';G='native__gam'
 want={tuple(sorted(m)):v for m,v in [((X,X),1),((a,c,X),2),((X,G),2),((a,c,G),2),((G,G),1),((a,c,c),-4),((c,c),-3)]}
 need(p==want,'seven-term norm expansion')
 weights={n:raw[n]for n in bd};need(weights=={X:308,a:374,c:67,G:375},'computed boundary weights')
 bound=max(sum(weights[x]for x in mon)for mon in p);need(bound==816,'norm degree')
 d={n:1 for n in ports}
 for n,o,a,b in rows:
  a=0 if type(a)is int else d[a];b=0 if type(b)is int else d[b];d[n]=a+b if o=='*'else max(a,b)
  if n=='native__R15':d[n]=bound
 factors=['native__R15','native__P17','native__first_unit','native__bs_q','native__f_square_minus_one','native__index_unit','native__linear_unit','sparse_repunit_unit']
 fv=[d[n]for n in factors];need(fv==[816,1900,442,65,1018,375,375,2],'factor degrees')
 need(raw[OUT]==5157 and d[OUT]==5091 and d['sparse_all_units']==4993 and d['norm_sum5']==98,'full bound')
 return {'raw_bound':5157,'actual_norm_cone':[table(rows)[n]for n in cone],'norm_expansion':plist(p),'computed_boundary_degrees':weights,'factor_bounds':fv,'native_product_bound':4993,'outer_SOS_bound':98,'degree_upper_bound':5091,'exact_degree_claimed':False}

def eval_rows(rows,values,p):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b
  e[n]=(a*b if o=='*'else a+b if o=='+'else a-b)%p
 return e

def build(root,author):
 pins(root,PINS);pins(author,AUTHOR)
 pa=read(root/'residue_affine_sparse_shared477.json');ch=read(author/'residue_affine_sparse_shared471.json')
 need(ch['dependencies']==PINS,'dependency record');need(ch['source_sha256']==AUTHOR['residue_affine_sparse_shared471.py'],'helper binding')
 old=pa['packet']['source'];new=ch['packet']['source'];od=table(old);nd=table(new)
 need(pa['packet']['source_sha256']==sha(canonical(old))and ch['packet']['source_sha256']==sha(canonical(new)),'array bindings')
 expected={n:list(r)for n,r in od.items()if n not in GONE}
 for n,r in EDIT.items():expected[n]=[n]+r
 need(nd==expected,'independent full471 definitions')
 need(set(od)-set(nd)==GONE and not(set(nd)-set(od)),'six deletions/no new producers')
 users={n:[r[0]for r in old if n in r[2:]]for n in sorted(GONE)}
 need(all(len(v)==1 and v[0]in EDIT for v in users.values()),'six old private consumers')
 before=audit(old);after=audit(new)
 need(before=={'operations':477,'multiplications':176,'additions_subtractions':301},'parent ledger')
 need(after=={'operations':471,'multiplications':175,'additions_subtractions':296},'child ledger')
 ports=free(old);need(ports==free(new)and len(ports)==69,'interface')
 unchanged={k:v for k,v in pa['packet'].items()if k not in {'source','source_sha256','ledger','certificate_ledger'}}
 need(all(ch['packet'][k]==v for k,v in unchanged.items()),'all other packet/interface metadata literal')
 need(ch['packet']['witnesses']==sorted(set(ports)-{'program','input'})and len(ch['packet']['witnesses'])==67,'67 witnesses')
 native=[r for r in old if r[0].startswith('native__')];need(len(native)==72 and all(nd[r[0]]==r for r in native),'native72 literal')
 need(new[-20:]==old[-20:],'final20 literal and contiguous')
 final_count=Counter(r[1]for r in old[-20:]);need(final_count==Counter({'*':7,'+':6,'-':7}),'finalizer count')
 cert=dict(operations=len(new)-20,multiplications=after['multiplications']-7,additions_subtractions=after['additions_subtractions']-13,equations=7,witnesses=67)
 need(cert==ch['packet']['certificate_ledger'],'451 certificate')
 need(dict(after,witnesses=67)==ch['packet']['ledger'],'471 receipt ledger')
 need(all(nd[r[0]]==od[r[0]]==r for r in ch['packet']['literal_height_radix_rows']),'literal height/radix')
 contract=exact(old,new);deg=degree(new);need(degree(old)==deg,'same source-derived degree proof')
 rng=random.Random(447171);samples=0
 for p in (1000000007,1000000009):
  for _ in range(12):
   values={n:rng.randrange(-40,41)for n in ports};a,b=eval_rows(old,values,p),eval_rows(new,values,p)
   need(all(a[n]==b[n]for n in nd),'all471 signed modular values');samples+=1
 return {'status':'PASS_INDEPENDENT_SHARED471','checker_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'parent_pins':PINS,'parent_ledger':before,'new_ledger':dict(after,witnesses=67),'certificate_ledger':cert,'all_rows_reconstructed':471,'private_deleted_consumers':users,'exact_contract':contract,'degree_audit':deg,'unchanged_ports':ports,'literal_native_rows':72,'literal_finalizer_rows':20,'signed_modular_source_pairs':samples,'scope':'Exact whole polynomial and positive zero-set identity to477; inherited valid E=3^e and ordinary positive input, no new native history or exact degree claim'}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-dir',type=Path,required=True)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root,a.author_dir)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:need(canonical(read(a.expect))==canonical(r),'exact typed receipt')
 print(r['status'],r['new_ledger'])
if __name__=='__main__':main()
