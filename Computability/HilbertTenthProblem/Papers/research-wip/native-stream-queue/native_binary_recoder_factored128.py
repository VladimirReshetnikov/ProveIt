#!/usr/bin/env python3
"""Two exact native coefficient factorizations in full pinned recoder sources."""
if not __debug__:raise RuntimeError('Run without -O')
import argparse,copy,hashlib,json,random,subprocess,sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
PINS={
 'native_binary_input_dilation130.py':'7e7ccb297083ffb799775d729b81ec0e403981f287af62513338c5d366fb9ac2',
 'native_binary_input_dilation130.json':'175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182',
 'gpcp_fixed_program_input_bridge.py':'0d5023b52a5ffe87f5c9e26b436048571e75ccbebfd18c62f9820729b10b74f0',
 'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'grill_tag_exact_width_loader.py':'685a5744c180439ca67cdfcb6eace118379365e3575c302cb19ce404aa29d2f4',
 'grill_tag_exact_width_loader.json':'48f409c2eb7965ae26a4bef8b58a36ae366dfae3df4b3ca077d463581969fb75',
 'grill_tag_exact_width_loader.md':'9076fcfd9d78c144ccb757dddb34bc5300f0d443336532e45dda621c73187da6'}
VARIANTS=('inline4','generic32','generic784','exact_width_grill')
def need(x,s):
 if not x:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def _read(root,exact_root=None):
 root=Path(root);exact_root=root if exact_root is None else Path(exact_root);blobs={}
 for name,digest in PINS.items():
  p=(exact_root if name.startswith('grill_tag_exact_width_loader.') else root)/name
  b=p.read_bytes();need(sha(b)==digest,'Pinned source/receipt '+name);blobs[name]=b
 return blobs

def _sos(source,pairs):
 rows=copy.deepcopy(source);out=None
 for i,(a,b) in enumerate(pairs):
  r='sos_res'+str(i);q='sos_sq'+str(i);rows.extend([[r,'-',a,b],[q,'*',r,r]])
  if out is None:out=q
  else:n='sos_sum'+str(i);rows.append([n,'+',out,q]);out=n
 return rows,out

def _ledger(rows,ports,terminals):
 need(type(rows)is list and type(ports)is list and all(type(n)is str for n in ports),'Exact source and coordinate lists')
 known=set(ports);need(len(known)==len(ports),'Distinct coordinate names');degree={n:1 for n in ports};defs={};counts=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'Exact four-item source row');n,o,a,b=row
  need(type(n)is str and n not in known and type(o)is str and o in ('+','-','*'),'Typed fresh gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Exact closed operands')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0
  degree[n]=da+db if o=='*' else max(da,db);defs[n]=(a,b);known.add(n);counts['M' if o=='*' else 'A']+=1
 live=set();free=set();todo=list(terminals)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n in ports:free.add(n);continue
  if n in live:continue
  need(n in defs,'Defined terminal');live.add(n);todo.extend(defs[n])
 need(live==set(defs) and free==set(ports),'All paid gates and declared coordinates live')
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],degree_upper=max(degree[n] if type(n)is str else 0 for n in terminals))

def _chain(width):
 n=1;last='q';rows=[]
 for bit in bin(width)[3:]:
  n*=2;dest='Q' if n==width else 'width_power'+str(n);rows.append([dest,'*',last,last]);last=dest
  if bit=='1':
   n+=1;dest='Q' if n==width else 'width_power'+str(n);rows.append([dest,'*',last,'q']);last=dest
 need(n==width and len(rows)==width.bit_length()+width.bit_count()-2,'Literal paid power chain');return rows

def canonical_parent(root,variant='inline4',*,exact_root=None):
 need(type(variant)is str and variant in VARIANTS,'Selected exact variant');b=_read(root,exact_root)
 if variant=='exact_width_grill':
  receipt=json.loads(b['grill_tag_exact_width_loader.json']);old=receipt['complete']
  source=old['source'];pairs=old['comparisons'];full=old['polynomial_source'];output=old['output'];parameters=old['parameters'];aux=old['auxiliaries']
  prefixes=['rec__geo__','rec__and__'];degree=dict(upper=old['degree_upper'],exact=None);width=old['loader']['constants']['width']
  origin=dict(recipe=receipt['recipe'],scope=old['scope'],native_polynomial=old['native_polynomial'],unit_register=old['unit_register'],
              note='Existing current full16148-gate certificate and16291-gate polynomial; loader/native scopes inherited, not a universal table.')
 else:
  base=json.loads(b['native_binary_input_dilation130.json'])['certificate'];source=base['source'];pairs=base['comparisons'];parameters=base['parameters'];aux=base['auxiliaries']
  width={'inline4':4,'generic32':32,'generic784':784}[variant]
  need(source[:3]==[['q2','*','q','q'],['Q','*','q2','q2'],['B','*',8,'Q']],'Inline130 prefix')
  if variant!='inline4':source=_chain(width)+[['B','*',1<<(width-1),'Q']]+source[3:]
  full,output=_sos(source,pairs);prefixes=['geo__','and__'];degree=dict(upper=2*max(20,width+1),exact=2*max(20,width+1))
  origin=dict(scope='Complete positive ordinary input u and supplied output R=spread_width(u), some n>=2; no canonical width assertion in this standalone recoder.',
              recipe='Frozen inline130 with literal paid generic-width chain; both complete native kernels retained.')
 ports=parameters+aux;c=_ledger(source,ports,[v for pair in pairs for v in pair]);p=_ledger(full,ports,[output]);need(p['degree_upper']==degree['upper'],'Complete parent degree bound')
 need(full[:len(source)]==source,'Parent source prefix')
 return copy.deepcopy(dict(variant=variant,width=width,source=source,comparisons=pairs,polynomial_source=full,output=output,parameters=parameters,auxiliaries=aux,
               prefixes=prefixes,certificate=c,polynomial=p,degree=degree,domains=dict(parameters='strictly positive integers',auxiliaries='strictly positive integers'),
               parent_semantics=origin,parent_semantics_role='Authenticated unchanged parent relation and historical native counts; no active child registers declared here.'))

def _rewrite(parent):
 p=copy.deepcopy(parent);d={n:(o,a,b) for n,o,a,b in p['source']};removed=set();replace={};changes=[]
 for prefix in p['prefixes']:
  n=lambda v:prefix+v
  need(d[n('UM')]==('*',n('wn2'),n('sn2')) and d[n('ksn2')]==('*',n('k'),n('sn2')),'Actual E=XY and supplied kY')
  need(n('k') in p['auxiliaries'] and n('k') not in d,'Positive supplied k, never substituted via ratio equality')
  expected={'UM2':('*',n('UM'),n('UM')),'scaled_norm_coefficient':('+',n('UM2'),n('wn2')),'ratio_product2':('*',n('ksn2'),n('ksn2')),'L9':('*',n('scaled_norm_coefficient'),n('ratio_product2'))}
  need(all(d[n(key)]==value for key,value in expected.items()),'Exact four-gate coefficient cone')
  for a,b in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
   private=n(a);need({name for name,o,u,v in p['source'] if private in (u,v)}=={n(b)},'Private sole source consumer')
   need(not any(private in pair for pair in p['comparisons']),'Removed register is not compared')
   need(not any(private in row[2:] for row in p['polynomial_source'][len(p['source']):]),'No hidden finalizer consumer')
   removed.add(private)
  base=n('factored_first_base');nxt=n('factored_first_next');need(base not in d and nxt not in d,'Fresh factor registers')
  replace[n('L9')]=[[base,'*',n('UM'),n('ksn2')],[nxt,'+',base,n('k')],[n('L9'),'*',base,nxt]]
  changes.append(dict(prefix=prefix,actual_k=n('k'),output=n('L9'),removed=[n(t) for t in ('UM2','scaled_norm_coefficient','ratio_product2')]))
 if p['variant']=='exact_width_grill':
  need(all('hist__and__'+name not in d for name in ('UM2','scaled_norm_coefficient','ratio_product2','L9')),'Do not count a nonexistent history cone')
  need('hist__and__first_unit' in d,'Actual translated native history first unit remains')
 new=[]
 for row in p['source']:
  if row[0] in replace:new.extend(replace[row[0]])
  elif row[0] not in removed:new.append(row)
 p['source']=new;p['polynomial_source']=new+copy.deepcopy(parent['polynomial_source'][len(parent['source']):])
 ports=p['parameters']+p['auxiliaries'];p['certificate']=_ledger(new,ports,[v for pair in p['comparisons'] for v in pair]);p['polynomial']=_ledger(p['polynomial_source'],ports,[p['output']])
 for key in ('certificate','polynomial'):
  need(p[key]['operations']==parent[key]['operations']-2 and p[key]['M']==parent[key]['M']-2 and p[key]['A']==parent[key]['A'],'Exactly two complete multiplications saved')
  need(p[key]['degree_upper']==parent[key]['degree_upper'],'Same formal degree bound')
 p['transfer']=dict(complete_same_polynomial=True,coordinate_map='identity',factorizations=changes,saved=dict(M=2,A=0,total=2),
                   history_cone_saving=0,finalizer='Entire parent tail kept literally; integer unit anchor unchanged in complete Grill form.')
 return p

def build(root,variant='inline4',*,exact_root=None):return _rewrite(canonical_parent(root,variant,exact_root=exact_root))
def rewrite(root,variant,supplied,*,exact_root=None):
 old=canonical_parent(root,variant,exact_root=exact_root);need(exact(supplied,old),'Entire canonical parent required');return _rewrite(old)
def checked(root,p,*,exact_root=None):
 need(type(p)is dict,'Exact whole packet');q=build(root,p.get('variant'),exact_root=exact_root);need(exact(p,q),'Entire canonical child required');return q

def _execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def evaluate(root,p,values,*,signed=False,exact_root=None):
 need(type(signed)is bool,'Exact signed flag');p=checked(root,p,exact_root=exact_root)
 need(type(values)is dict and all(type(k)is str for k in values) and values.keys()==set(p['parameters']+p['auxiliaries']),'Exact full coordinate map')
 need(all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integers or explicit signed integer mode')
 return _execute(p['polynomial_source'],values)[p['output']]

def identity(old,new):
 # Actual local polynomial coefficients in X,Y,k; two cuts kept distinct.
 zero=(0,0,0)
 def add(a,b,s=1):
  c=a.copy()
  for k,v in b.items():c[k]=c.get(k,0)+s*v
  return {k:v for k,v in c.items() if v}
 def mul(a,b):
  c={}
  for p,v in a.items():
   for q,w in b.items():k=tuple(x+y for x,y in zip(p,q));c[k]=c.get(k,0)+v*w
  return {k:v for k,v in c.items() if v}
 cuts=set()
 for pref in old['prefixes']:
  vals=[]
  for source in (old['source'],new['source']):
   e={pref+'wn2':{(1,0,0):1},pref+'sn2':{(0,1,0):1},pref+'k':{(0,0,1):1}}
   for n,o,a,b in source:
    if n in e:continue
    if (type(a)is int or a in e) and (type(b)is int or b in e):
     aa={zero:a} if type(a)is int else e[a];bb={zero:b} if type(b)is int else e[b];e[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else-1)
   vals.append(e[pref+'L9'])
  need(vals[0]==vals[1]=={(2,4,2):1,(1,2,2):1},'Exact actual coefficient expansion');cuts.add(pref+'L9')
 intern={}
 def token(x):
  if x not in intern:intern[x]=len(intern)
  return intern[x]
 def graph(p):
  e={n:token(('free',n)) for n in p['parameters']+p['auxiliaries']}
  def at(v):return e[v] if type(v)is str else token(('integer',v))
  for n,o,a,b in p['polynomial_source']:e[n]=token(('proved_local_identity',n)) if n in cuts else token((o,at(a),at(b)))
  return e,at
 a,aa=graph(old);b,bb=graph(new)
 for n in set(a)&set(b):need(a[n]==b[n],'Every common register identical')
 for x,y in old['comparisons']:need(aa(x)==bb(x) and aa(y)==bb(y),'Every complete residual identical')
 need(a[old['output']]==b[new['output']],'Exact complete final polynomial')
 need(old['comparisons']==new['comparisons'] and old['parameters']==new['parameters'] and old['auxiliaries']==new['auxiliaries'],'Unchanged entire interface')
 return dict(local_coefficient_identities=len(cuts),common_register_identities=len(set(a)&set(b)),residual_identities=len(old['comparisons']),complete_polynomial_identities=1)

def verify(root,exact_root):
 counts=Counter();forms=[];rng=random.Random(12816289)
 for variant in VARIANTS:
  old=canonical_parent(root,variant,exact_root=exact_root);p=build(root,variant,exact_root=exact_root);counts.update(identity(old,p));ports=p['parameters']+p['auxiliaries']
  for i in range(16):
   v={n:rng.randrange(1,4) if i<4 else rng.randrange(-2,4) for n in ports}
   if variant=='exact_width_grill':
    for n in ports:
     if n.startswith('hist__Shat'):v[n]=1
   if i>=12:v={n:Fraction(z,3) if not n.startswith('hist__Shat') else z for n,z in v.items()};counts['rational_complete_cases']+=1
   a=_execute(old['polynomial_source'],v);b=_execute(p['polynomial_source'],v)
   need(a[old['output']]==b[p['output']],'Complete all-value evaluation');counts['whole_numeric_cases']+=1
   if i<8:need(evaluate(root,p,v,signed=i>=4,exact_root=exact_root)==b[p['output']],'Public canonical evaluator');counts['public_integer_evaluations']+=1
  for pref in p['prefixes']:
   v={n:1 for n in ports};v[pref+'k']=3;e=_execute(p['source'],v)
   need(e[pref+'R10b']==2 and e[pref+'L9']!=e[pref+'factored_first_base']*(e[pref+'factored_first_base']+e[pref+'R10b']),'Independent supplied-k boundary');counts['wrong_k_counterexamples']+=1
  def reject(fn):
   try:fn()
   except ValueError:counts['malformed_rejections']+=1
   else:raise ValueError('Malformed caller accepted')
  for isparent,q in ((True,old),(False,p)):
   for key in ('source','comparisons','parameters','auxiliaries'):
    bad=copy.deepcopy(q);bad[key]=tuple(bad[key]);reject(lambda bad=bad,isparent=isparent:rewrite(root,variant,bad,exact_root=exact_root) if isparent else checked(root,bad,exact_root=exact_root))
   bad=copy.deepcopy(q);bad['certificate']['M']=float(bad['certificate']['M']);reject(lambda bad=bad,isparent=isparent:rewrite(root,variant,bad,exact_root=exact_root) if isparent else checked(root,bad,exact_root=exact_root))
  for prefix in p['prefixes']:
   bad=copy.deepcopy(p);row=next(row for row in bad['source'] if row[0]==prefix+'factored_first_next');row[3]=prefix+'R10b';reject(lambda bad=bad:checked(root,bad,exact_root=exact_root))
  for value in (True,1.0,Fraction(1),0):
   v={n:1 for n in ports};v[ports[0]]=value;reject(lambda v=v:evaluate(root,p,v,exact_root=exact_root))
  q=build(root,variant,exact_root=exact_root);q['source'][0][0]='poison';need(build(root,variant,exact_root=exact_root)['source'][0][0]!='poison','Independent returned source');counts['copy_checks']+=1
  forms.append(dict(variant=variant,parent_certificate=old['certificate'],parent_polynomial=old['polynomial'],packet=p))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,forms=forms,counts=dict(counts),
             scope='Four complete pinned sources: two supplied-k recoder coefficient identities, unchanged same-coordinate entire polynomials. Generic chain claim for all fixed widths>=4; literal receipts for4,32,784 and one exact-width Grill composition. No saving in the already translated native history norm; no universal operation claim.')
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--exact-root',type=Path);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.exact_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'Exact full saved receipt')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers={x['variant']:x['packet']['polynomial'] for x in r['forms']}),sort_keys=True))
if __name__=='__main__':main()
