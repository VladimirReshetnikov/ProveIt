#!/usr/bin/env python3
"""Independent inert-array reconstruction and terminal-carry polynomial audit."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path
AUTH={'py':'b6bd9bd02f5aa14e73f46804706c8ca155186be4610e10f5b5e1b518e6d9c7d3','json':'6afa10fee956f9e26167345300d886116374dafc6695e91bf5dd3d28679915f2','md':'a576e578d8dc80b174a60ca9bce28b1aa8dbd848a61c8c870ced4d9ab366fbd4'}
PARENT='67ec3453bb211f3129f27d4194084007c0e1e74410745a11c4181c79ae707002'
MAP='d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'
C=2**93

def require(x,s):
 if not x:raise ValueError(s)
def digest(b):return hashlib.sha256(b).hexdigest()
def canonical(o):return json.dumps(o,sort_keys=True,separators=(',',':')).encode()
def load(p):
 def obj(pairs):
  d={}
  for k,v in pairs:
   require(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=obj,parse_constant=bad)
def same(a,b):
 if type(a)!=type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

# Sparse integer polynomials in formal string atoms, independent of author arithmetic.
def const(n):return {():n} if n else {}
def var(n):return {(n,):1}
def plus(a,b,sign=1):
 r=a.copy()
 for m,c in b.items():
  r[m]=r.get(m,0)+sign*c
  if not r[m]:del r[m]
 return r
def times(a,b):
 r={}
 for x,c in a.items():
  for y,d in b.items():
   k=tuple(sorted(x+y));r[k]=r.get(k,0)+c*d
 return {k:v for k,v in r.items() if v}
def op(o,a,b):return times(a,b) if o=='*' else plus(a,b,1 if o=='+' else -1)

def final(p):
 by={r[0]:r for r in p['source']};out=by[p['output']]
 require(out[1]=='-' and out[3]==1,'output minus one')
 prod=by[out[2]];require(prod[1]=='*','native times outer')
 native=prod[2];one=by[prod[3]];require(one[1]=='+' and one[3]==1,'one plus squares')
 names={out[0],prod[0],one[0]};leaves=[]
 def visit(n):
  r=by[n];names.add(n)
  if r[1]=='*':
   require(r[2]==r[3] and type(r[2])is str,'square leaf')
   names.add(r[2]);leaves.append((r[2],n));return
  require(r[1]=='+' and type(r[2])is str and type(r[3])is str,'addition tree')
  visit(r[2]);visit(r[3])
 visit(one[2]);res=[r for r,_ in leaves]
 require(len(set(res))==len(res) and res==p['retained_residual_wires'],'residual inventory')
 require(len(names)==3*len(res)+2,'private complete finalizer size')
 require(all(not any(v in names for v in r[2:]) for r in p['source'] if r[0] not in names),'finalizer has no outward consumer')
 return names,leaves,native

def graph(p):
 known=set(p['free']);require(len(known)==len(p['free']),'unique ports')
 require(set(p['free'])==set(p['fixed_numerals'])|set(p['witnesses'])|{'x'},'exact interface')
 ct=Counter();by={}
 for r in p['source']:
  require(len(r)==4,'row arity');n,o,a,b=r
  require(type(n)is str and n not in known and o in ['+','-','*'],'unique producer')
  require(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'topological operands')
  known.add(n);by[n]=r;ct[o]+=1
 reached=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in reached:
   reached.add(v)
   if v in by:todo+=by[v][2:]
 require(known==reached,'every row and port live')
 return {'total':len(by),'M':ct['*'],'A':ct['+']+ct['-'],'witnesses':len(p['witnesses']),'free':len(p['free'])}

def univariates(rows,Q):
 env={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q:continue
  if any(type(v)is str and v not in env for v in [a,b]):continue
  aa=env[a] if type(a)is str else ({0:a} if a else {});bb=env[b] if type(b)is str else ({0:b} if b else {})
  r={}
  if o=='*':
   for i,c in aa.items():
    for j,d in bb.items():r[i+j]=r.get(i+j,0)+c*d
  else:
   r=aa.copy()
   for i,c in bb.items():r[i]=r.get(i,0)+(c if o=='+' else -c)
  env[n]={i:c for i,c in r.items() if c}
 return env

def degree_upper(p,Q,u):
 d={n:0 if n in p['fixed_numerals'] else 1 for n in p['free']}
 for n,o,a,b in p['source']:
  da=d[a] if type(a)is str else 0;db=d[b] if type(b)is str else 0
  d[n]=da+db if o=='*' else max(da,db)
  if n in u and n!=Q:d[n]=max(u[n],default=0)*d[Q]
 return d

def run_packet(old,new,m,index):
 def wire(n):return m.get(n,n)
 before=graph(old);after=graph(new);ob={r[0]:r for r in old['source']};nb={r[0]:r for r in new['source']}
 ofinal,oleaves,N=final(old);nfinal,nleaves,NN=final(new);require(N==NN,'same native anchor')
 consumers={}
 for n,o,a,b in old['source']:
  for v in set([a,b]):
   if type(v)is str:consumers.setdefault(v,[]).append(n)
 found=[];removed=set();deleted_bounds=set();aliases={};rename={};gone_slacks=set();middle_names=set()
 # Discover source locations by actual private consumers; no author recipe rows used.
 for stem in ['X_dot0','X_dot1','Y_dot0','Y_dot1']:
  ph=stem+'_positive';hh=stem+'_high_hat';sl=stem+'_slack'
  bc=consumers[sl];require(len(bc)==1,'one slack consumer');bound=ob[bc[0]];require(bound[1:]==['+',ph,sl],'bound producer')
  pcons=[n for n in consumers[ph] if n!=bound[0]];require(len(pcons)==1,'one centered dot producer');dot=ob[pcons[0]]
  require(dot[1]=='-' and dot[2]==ph,'dot definition');half=dot[3]
  hcons=consumers[hh];require(len(hcons)==1,'one high consumer');high=ob[hcons[0]];require(high[1]=='-' and high[2]==hh,'high definition')
  hpcons=consumers[high[0]];require(len(hpcons)==1,'one high product');hp=ob[hpcons[0]];require(hp[1]=='*' and hp[3]==high[0],'high product');Q=hp[2]
  mids=consumers[hp[0]];require(len(mids)==1,'one middle');middle=ob[mids[0]];require(middle[1:]==['+',dot[0],hp[0]],'middle source')
  brcons=consumers[bound[0]];require(len(brcons)==1,'one bound residual');br=ob[brcons[0]];require(br[1:]==['-',bound[0],Q],'bound residual')
  raw=stem+'_raw_positive';negative=stem+'_negative_high'
  removed|={dot[0],high[0],bound[0]};deleted_bounds.add(br[0]);gone_slacks.add(sl)
  aliases[dot[0]]=raw;aliases[high[0]]=negative;rename[ph]=raw;rename[hh]=negative;middle_names.add(middle[0])
  found.append({'stem':stem,'ph':ph,'hh':hh,'sl':sl,'dot':dot[0],'high':high[0],'bound':bound[0],'bound_residual':br[0],'middle':middle[0],'half':half,'Q':Q,'half_low':high[3],'raw':raw,'negative':negative})
 require(len({r['Q'] for r in found})==len({r['half'] for r in found})==1,'common Q and half')
 Q=found[0]['Q'];half=found[0]['half'];P=ob[Q][3];B=wire('r3')
 require(ob[Q]==[Q,'*',C,P] and ob[half]==[half,'*',C//2,P],'actual Q relation')
 require(new['free']==[rename.get(n,n) for n in old['free'] if n not in gone_slacks],'exact free ports')
 require(new['witnesses']==[rename.get(n,n) for n in old['witnesses'] if n not in gone_slacks],'exact positive witnesses')
 require(new['fixed_numerals']==old['fixed_numerals'],'fixed coefficient ports')
 def edit(r):
  n,o,a,b=r;return [n,'-' if n in middle_names else o,aliases.get(a,a),aliases.get(b,b)]
 wanted={n:edit(r) for n,r in ob.items() if n not in removed and n not in ofinal}
 require({n:r for n,r in nb.items() if n not in nfinal}==wanted,'complete prefinal edit and no other change')
 oldleaf=dict(oleaves);newleaf=dict(nleaves)
 require(set(newleaf)==set(oldleaf)-deleted_bounds,'exact retained residual inventory')
 for n,square in nleaves:
  require(nb[n]==edit(ob[n]),'retained residual definition')
  require(square==oldleaf[n] and nb[square]==ob[square],'retained square literal')
 require((after['total'],after['M'],after['A'],after['witnesses'])==(before['total']-24,before['M']-4,before['A']-20,before['witnesses']-4),'complete paid delta')
 for k in ['total','M','A']:require(after[k]==new['ledger'][k],'ledger '+k)
 require(after['witnesses']==new['ledger']['positive_witnesses'],'witness ledger')
 comp=new['coefficient_component'];require(comp==old['coefficient_component'] and len(comp)==553,'same whole coefficient component')
 require(all(nb[r[0]]==r for r in comp),'literal coefficient rows')
 require(Counter(r[1] for r in comp)['*']==305,'component multiplication count')
 # Reexpand all coefficient polynomials directly in Z[Q].
 ou=univariates(old['source'],Q);nu=univariates(new['source'],Q)
 certs=[]
 for c in old['coefficient_certificates']:
  w=c['wire'];expected={i:v for i,v in enumerate(c['ascending_coefficients']) if v}
  require(ou[w]==nu[w]==expected,'entire coefficient word')
  certs.append({'wire':w,'entries':len(c['ascending_coefficients']),'degree':max(expected),'sha256':digest(canonical(sorted(expected.items())))})
 require(len(new['coefficient_certificates'])==4,'four new coefficient certificates')
 for c in new['coefficient_certificates']:
  require(nu[c['wire']]=={i:v for i,v in enumerate(c['ascending_coefficients']) if v},'new coefficient metadata exact')
 require(len(new['chart_records'])==4,'four chart records')
 for discovered,saved in zip(found,new['chart_records']):
  require(saved['stem']==discovered['stem'] and saved['raw_port']==discovered['raw'] and saved['high_port']==discovered['negative'] and saved['removed_residual']==discovered['bound_residual'] and saved['dot_row']==ob[discovered['dot']] and saved['high_row']==ob[discovered['high']] and saved['bound_row']==ob[discovered['bound']],'chart metadata agrees with independent consumer discovery')
 # Every common untouched producer is a shared atom; all changed cones and finalizers expand.
 zQ=times(const(C),var(P));zHalf=times(const(C//2),var(P));carry=var('formal:carry')
 oi={n:var('input:'+n) for n in old['free']};ni={n:oi[n] for n in new['free'] if n in oi}
 for r in found:
  ni[r['raw']]=plus(plus(oi[r['ph']],zHalf,-1),times(carry,zQ))
  ni[r['negative']]=plus(plus(carry,oi[r['hh']],-1),var(r['half_low']))
 for n in ['F_even','F_odd']:ni[n]=plus(oi[n],times(times(const(C),var(B)),carry))
 os={x for r in found for x in [r['ph'],r['hh'],r['sl']]}|{'F_even','F_odd'}
 ns={x for r in found for x in [r['raw'],r['negative']]}|{'F_even','F_odd'}
 def expand(p,inp,changed,finalnames):
  vals=inp.copy();dirty=set(changed)
  for n,o,a,b in p['source']:
   if n==Q:vals[n]=zQ;continue
   if n==half:vals[n]=zHalf;continue
   if a in dirty or b in dirty:dirty.add(n)
   if n in dirty or n in finalnames:
    aa=vals[a] if type(a)is str else const(a);bb=vals[b] if type(b)is str else const(b)
    vals[n]=op(o,aa,bb)
   else:vals[n]=var(n)
  return vals,dirty
 oe,od=expand(old,oi,os,ofinal);ne,nd=expand(new,ni,ns,nfinal)
 for n in newleaf:require(oe[n]==ne[n],'exact retained polynomial residual')
 require(oe[N]==ne[N],'exact native factor cut')
 loss={}
 for n in deleted_bounds:loss=plus(loss,times(oe[n],oe[n]))
 require(not plus(plus(ne[new['output']],oe[old['output']],-1),times(oe[N],loss)),'full integer ring contract')
 # Derive Y selector pack rather than treating its formal leader as trusted metadata.
 prodnames=[]
 for c in certs:
  matches=[r for r in new['source'] if r[1]=='*' and r[2]==c['wire']]
  require(len(matches)==1,'coefficient product consumer');prodnames.append(matches[0][0])
 yp=nb[prodnames[2]];center=nb[yp[3]];require(center[1]=='-','centered selected block')
 shift=nb[center[3]];require(shift[1]=='*','paid c0 selector product');c0,Spack=shift[2:]
 require(c0==wire('r2') and nb[c0]==[c0,'-',wire('r1'),1],'actual c0 producer')
 edgecuts={wire('edge_hat'+str(i)):var('e'+str(i)) for i in range(99)}
 cache={Q:var('q'),**edgecuts}
 def recursive(n):
  if type(n)is int:return const(n)
  if n in cache:return cache[n]
  require(n in nb,'selector dependency closes at Q and edge hats')
  _,o,a,b=nb[n];cache[n]=op(o,recursive(a),recursive(b));return cache[n]
 selector=recursive(Spack);desired={}
 for g,e in enumerate(list(range(2,98))+[0]):
  for power in [2*g,2*g+1]:
   qp={('q',)*power:1};desired=plus(desired,times(plus(var('e'+str(e)),const(1),-1),qp))
 require(selector==desired,'entire Y selector polynomial, last coefficient E_LOAD')
 require(nb[center[2]]==[center[2],'-','Y_block_hat',1],'Zblock has degree one')
 d=degree_upper(new,Q,nu);s=d[Q];e=d[wire('edge_hat0')]
 require((s,e)==[(2,1),(3,1),(3,2),(4,2)][index],'Q and load degrees')
 lead=386*s+1+e
 require([nu[c['wire']][193] for c in certs[2:]]==[-490,271],'uniform nonzero Y coefficients')
 require(d[prodnames[2]]==d[prodnames[3]]==lead,'product upper degree agrees with proved leader')
 require(max(d[n] for n in newleaf)==lead,'all residual upper bounds')
 # Extraction residuals are found from product consumers, not receipt chart_records.
 extraction=[]
 for prodname in prodnames:
  rs=[r for r in new['source'] if r[0] in newleaf and r[1]=='-' and r[2]==prodname]
  require(len(rs)==1,'extraction residual');r=rs[0];l=144 if len(extraction)<2 else 194
  require(d[r[3]]<=l*s+1,'negative-high RHS bound');extraction.append({'lhs':d[prodname],'rhs_upper':d[r[3]]})
 native_degree=16986*s+67;full=native_degree+2*lead
 require(full==new['ledger']['exact_degree'],'full exact degree from inherited native polynomial')
 native_names=[wire(r[0]) for r in ORIGINAL_NATIVE]
 require(len(native_names)==63 and all(nb[n]==ob[n] for n in native_names),'all 63 native definitions literal')
 require(all(n not in od and n not in nd for n in native_names),'native cone independent of every changed port')
 return {'variant':new['variant'],'ledger':after,'residuals':len(newleaf),'finalizer_rows':len(nfinal),'old_finalizer_rows':len(ofinal),'all_source_edits_exact':True,'all_live':True,'ring_contract_zero_terms':True,'expanded_parent_terms':len(oe[old['output']]),'expanded_child_terms':len(ne[new['output']]),'coefficient_words':certs,'Y_selector_full_polynomial_equal':True,'Q_degree':s,'LOAD_degree':e,'largest_residual_degree':lead,'native_degree_inherited_unchanged':native_degree,'exact_degree':full,'extraction_degree_bounds':extraction,'source_sha256':digest(canonical(new['source']))}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,default=Path('/tmp'));g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args()
 for ext,h in AUTH.items():require(digest((a.author_root/('matrix193_terminal_carry_chart.'+ext)).read_bytes())==h,'frozen author '+ext)
 receipt=load(a.author_root/'matrix193_terminal_carry_chart.json');require(receipt['source_sha256']==AUTH['py'],'author source binding')
 for n,h in receipt['pins'].items():require(digest((a.root/n).read_bytes())==h,'dependency '+n)
 require(digest((a.root/'matrix193_grouped_power_composition.json').read_bytes())==PARENT,'parent pin')
 require(digest((a.root/'matrix193_entry_controller_charts.json').read_bytes())==MAP,'map pin')
 old=load(a.root/'matrix193_grouped_power_composition.json');maps=load(a.root/'matrix193_entry_controller_charts.json')
 base=old['packets'][0]['source'];labels=[r[0] for r in base]
 global ORIGINAL_NATIVE
 ORIGINAL_NATIVE=base[labels.index('selection__bs_even'):labels.index('eight_units')+1]
 results=[run_packet(p,n,{} if i==0 else maps['packets'][i-1]['map'],i) for i,(p,n) in enumerate(zip(old['packets'],receipt['packets']))]
 require(len(results)==4,'four complete arrays')
 answer={'review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTH,'dependency_pins':receipt['pins'],'packets':results,'complete_rows':sum(r['ledger']['total'] for r in results),'coefficient_entries':sum(sum(c['entries'] for c in r['coefficient_words']) for r in results),'scope':{'predecessor_or_author_execution':False,'full_source_reconstruction':True,'exact_symbolic_contracts':True,'native_degree_inherited_from_unchanged_source':True,'no_giant_tuple':True}}
 if a.output:a.output.write_text(json.dumps(answer,sort_keys=True,indent=2)+'\n')
 else:require(same(answer,load(a.expect)),'exact independent receipt')
 print('PASS independent terminal carry:6164 rows;16 coefficient words;4 full ring contracts;Y selectors;all degrees')
if __name__=='__main__':main()
