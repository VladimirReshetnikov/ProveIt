#!/usr/bin/env python3
"""Fresh independent signed cap, guard, projection, translation and SOS audit.
The unchanged Horn factorization is checked by the separately reviewed inherited auditor.
"""
import json,sys,copy
from collections import Counter
from pathlib import Path
from check_natural import P,add,scale,mul,v,c,sub,remap,eq,expansion

def require(ok,msg):
 if not ok:raise AssertionError(msg)
def equivalent(a,b):return a==b or a==scale(b,-1)
def semantic(s,g,cert):
 names={x['name']:i for i,x in enumerate(s['variables'])};rows={r['label']:P(r['terms']) for r in s['residuals']};cv=cert['cap_variables'];seeds=cert['seed_data'];A=names['shared.A'];W=names['shared.W'];h=P(cert['anchor_index']);U,C=cv['U'],cv['Y'];H,J,S,R,D=[cv[n] for n in ['H','J','S','R','B']]
 require(len(seeds)==(14 if cert.get('strict_budget') else 15) and seeds[-1]['pair']==[U,C],'exact reused anchor pair');eq(h,P(seeds[-1]['exponent']),'exact anchor index');require(cert['squared_anchor'] and cert['signed_center'] and cert['odd_auxiliary'],'intended flags')
 for seed in seeds:
  for j in seed['calls']:eq(P(seed['exponent']),P(cert['square_budget']['power_calls'][j]['exponent']),'seed requested index')
  x,y=seed['pair'];prefix=s['variables'][x]['name'].rsplit('.',1)[0];rr=rows[prefix+'.norm1'];rest=add(rr,c(1),scale(mul(v(x),v(x)),-1),scale(mul(v(y),v(y)),-1))
  require(len(rest)==1,'principal norm shape');((mon,co),)=rest.items();require(co==-1 and len(mon)==2 and mon[0]==mon[1],'principal product square');ay=mon[0]
  require(any(equivalent(P(r['terms']),add(v(ay),scale(mul(v(A),v(y)),-1))) for r in s['residuals']),'principal A Y gate')
 expected=add(v(W),c(-2))
 for atom in cert['square_budget']['atoms']:
  q=P(atom['affine']);expected=add(expected,scale(mul(q,q),-1))
 eq(rows['shared.frame_definition'],expected,'literal square frame')
 groups=cert.get('pooled_groups')
 if cert.get('sparse'):
  for j,seed in enumerate(seeds):
   x,y=seed['pair']
   for kind,delta in [('index',add(v(y),scale(P(seed['exponent']),-1))),('sign',add(v(x),c(-1)))]:
    qq=names['cap.'+('residue_' if kind=='index' else 'sign_residue_')+str(j)]
    expected=add(delta,scale(mul(add(v(A),c(-1)),v(qq)),-1));eq(rows['cap.'+kind+'_residue_'+str(j)],expected,'exact individual residue')
 elif groups:
  coverage={'x':[], 'y':[]}
  for z,group in enumerate(groups):
   kind=group['kind'];require(kind in ['x','y','both'],'pool group kind');pool={}
   for coord in (['x','y'] if kind=='both' else [kind]):
    coverage[coord]+=group['indices']
    for j in group['indices']:
     seed=seeds[j];x,y=seed['pair'];delta=add(v(x),c(-1)) if coord=='x' else add(v(y),scale(P(seed['exponent']),-1));pool=add(pool,mul(delta,delta))
   eq(pool,P(group['polynomial']),'grouped error polynomial')
   label='cap.pooled_index_residue' if len(groups)==1 else 'cap.pooled_index_residue_'+str(z)
   expected=add(pool,scale(mul(add(v(A),c(-1)),v(group['quotient'])),-1));eq(rows[label],expected,'exact grouped residue')
  for kind in coverage:eq(sorted(coverage[kind]),list(range(len(seeds))),'complete pooled sign coverage')
 else:
  pool={}
  for seed in seeds:
   x,y=seed['pair'];d=add(v(y),scale(P(seed['exponent']),-1));pool=add(pool,mul(d,d))
   if not cert['ys_only']:d=add(v(x),c(-1));pool=add(pool,mul(d,d))
  pool=add(pool,scale(mul(add(v(A),c(-1)),v(cert['pooled_quotient'])),-1));eq(rows['cap.pooled_index_residue'],pool,'signed exact pooled residue')
 y2=cert['cap_square_variable'];eq(rows['cap.Y2'],add(v(y2),scale(mul(v(C),v(C)),-1)),'anchor square gate')
 eq(rows['cap.common_multiple'],add(v(J),scale(mul(v(y2),add(scale(v(cv['e']),2),c(1))),-1)),'odd auxiliary multiplier')
 eq(rows['cap.comparison_constructor'],add(v(D),c(-1),scale(mul(v(J),add(scale(v(cv['d']),2),c(1))),-4)),'odd comparison constructor')
 for label,left,right in [('comparison_modulus',v(D),add(v(A),mul(v(H),v(cv['f'])))),('abscissa_residue',v(S),add(v(U),mul(v(H),v(cv['g'])))),('index_residue',v(R),add(h,scale(mul(v(C),v(cv['h'])),4)))]:
  eq(rows['cap.'+label],add(left,scale(right,-1)),'signed anchor progression')
 for label,x,y,base,prodname in [('common_norm',H,J,A,'cap.common_Ay'),('comparison_norm',S,R,D,'cap.BR')]:
  prod=names[prodname];eq(rows['cap.'+label],add(mul(v(x),v(x)),mul(v(y),v(y)),scale(mul(v(prod),v(prod)),-1),c(-1)),'anchor norm')
  require(any(equivalent(P(r['terms']),add(v(prod),scale(mul(v(base),v(y)),-1))) for r in s['residuals']),'anchor product gate')
 expectedrows=[P(r['terms']) for r in s['residuals']];expectedvars=copy.deepcopy(s['variables']);front=set();sawcap=0
 for i,guard in enumerate(cert['guards']):
  expr=P(guard['expression']);kind=guard['kind']
  if kind=='shared_square_cap':
   want=add(mul(v(C),v(C)),scale(mul(h,h),-1),c(-1),*[scale(mul(v(q['pair'][1]),v(q['pair'][1])),-1) for q in seeds[:-1]]);eq(expr,want,'squared cap exact orientation');sawcap+=1
  elif kind=='front_nonnegative':eq(expr,v(guard['coordinate']),'front sign guard');front.add(guard['coordinate'])
  elif kind=='postsemantic_interval':eq(expr,mul(*[v(j) for j in guard['pair']]),'interval product guard')
  else:raise AssertionError('Unexpected guard '+kind)
  aux=guard['auxiliary'];eq(aux,list(range(len(expectedvars),len(expectedvars)+3)),'fresh guard auxiliaries');aa,bb,cc=aux
  expectedrows.append(add(expr,scale(mul(v(aa),v(aa)),-1),scale(mul(v(bb),v(bb)),-1),scale(mul(v(cc),v(cc)),-1),scale(v(cc),-1)))
  expectedvars += [{'name':f'guard{i}.{z}','kind':'integer_guard'} for z in ['a','b','c']]
 eq(expectedrows,[P(r['terms']) for r in g['residuals']],'all literal guard rows');eq(expectedvars,g['variables'],'guard variables');require(sawcap==1,'one exact cap')
 known=front|{W};proof=cert['sign_inference']
 for st in proof['proof_steps']:
  i,co=st['variable'],st['coefficient'];rhs=P(st['rhs']);require(co>0 and equivalent(P(s['residuals'][st['row']]['terms']),add(scale(v(i),co),scale(rhs,-1))),'raw sign identity')
  if st['kind']=='positive_monomials':
   deps={j for mon in rhs for j,power in Counter(mon).items() if power%2};require(all(co>=0 for co in rhs.values()) and deps<=known,'raw sign dependency')
  else:
   q=P(st['square_root']);require(all(len(mon)<=1 for mon in q),'affine square');eq(mul(q,q),rhs,'sign square identity')
  known.add(i)
 for key in ['fact0.remainder','fact0.slack','choose0.oslack','t0']:require(names[key] in known,'missing initial sign '+key)
 if cert['orientation_first']:
  require(not cert['ys_only'],'orientation-first requires both coordinates');require(names['x'] not in front and not any(s['variables'][i]['name'].startswith('crt.encoded') for i in front),'unintended retained guards')
 else:
  for key in ['x']+[x['name'] for x in s['variables'] if x['name'].startswith('crt.encoded')]:require(names[key] in known,'missing conservative sign '+key)
 return {'pairs':len(seeds),'guards':len(cert['guards']),'front_guards':len(front),'sign_identities':len(proof['proof_steps']),'orientation_first':cert['orientation_first'],'all_source_power_calls':len(cert['square_budget']['power_calls'])}

def project(source,target,cert):
 rows=[P(r['terms']) for r in source['residuals']];deleted=set();gone=set()
 for st in cert['steps']:
  i,r,p=st['variable'],st['row_id'],P(st['restoration']);require(i not in gone and r not in deleted,'repeated deletion');require(equivalent(rows[r],add(v(i),scale(p,-1))),'integral monic inverse');require(not any(i in m or set(m)&gone for m in p),'cyclic restoration')
  deleted.add(r);gone.add(i)
  for j in range(len(rows)):
   if j not in deleted:rows[j]=sub(rows[j],{i:p});require(all(len(m)<=2 for m in rows[j]),'row degree')
 ids=cert['retained_original_rows'];kept=cert['retained_original_variables'];mp=dict(zip(kept,range(len(kept))));eq(set(ids),set(range(len(rows)))-deleted,'retained row census')
 eq([source['variables'][i] for i in kept],target['variables'],'projected variable order');eq([remap(rows[i],mp) for i in ids],[P(r['terms']) for r in target['residuals']],'full projection')
 unused=set(cert['unconstrained_removed']);require(not unused&{j for i in ids for m in rows[i] for j in m},'used coordinate discarded');eq(set(range(len(source['variables']))),set(kept)|gone|unused,'coordinate partition')
 return len(gone)
def translate(source,target,cert):
 require(cert['convention']=='old=new+shift','translation orientation');sh=dict(cert['shifts']);eq(len(sh),len(cert['shifts']),'unique shifts');require(all(type(i)==int and type(a)==int for i,a in sh.items()),'integral shifts');mp={i:add(v(i),c(a)) for i,a in sh.items()}
 eq([sub(P(r['terms']),mp) for r in source['residuals']],[P(r['terms']) for r in target['residuals']],'exact coordinate translation');return len(sh)
def strict_delta(path,source,cert,raw_override=None):
 raw=json.loads((path/'input_raw.json').read_text());original=json.loads((path/'input_equation.json').read_text());basepath=path.parent/'portable_input'
 baseline=json.loads((basepath/'raw_audit_input.json').read_text());eq(original,json.loads((basepath/'equation.json').read_text()),'strict original source binding')
 if raw_override is not None:raw=raw_override
 expected=copy.deepcopy(baseline);fresh=len(expected['variables']);expected['variables'].append({'name':'self_radix.BH','kind':'gate'});expected['powers'][2]['base']=['v',fresh]
 oldk=expected['powers'][1]['exponent'];oldx=expected['powers'][14]['exponent'];rx=['v',next(i for i,d in enumerate(expected['variables']) if d['name']=='x')]
 for j in [1,2,14]:expected['powers'][j]['exponent']=rx
 for field in ['seeds','indices']:
  expected[field]=[d for d in expected[field] if d['exponent']!=oldk]
  for d in expected[field]:
   if d['exponent']==oldx:d['exponent']=rx
 expected['amplification']['K']=rx;expected['amplification']['budget']='x';expected['amplification']['derived_label_radix_budget']='ell*(t+1)<2F<x=K';expected['radix']['K']=rx
 changes=0
 for d in expected['ranges']:
  if d[3] in ['crt.range.u','crt.range.vq']:d[1]=rx;changes+=1
 require(changes==2,'strict range edit census');eq(expected,raw,'exact strict raw semantics delta')
 ns={d['name']:i for i,d in enumerate(original['variables'])};old=[ns['index1.X'],ns['index1.Y']];new=[ns['index12.X'],ns['index12.Y']]
 def ay(prefix,pair):
  rr=next(P(r['terms']) for r in original['residuals'] if r['label']==prefix+'.norm1');rest=add(rr,c(1),scale(mul(v(pair[0]),v(pair[0])),-1),scale(mul(v(pair[1]),v(pair[1])),-1));require(len(rest)==1,'norm AY shape');return next(iter(rest))[0]
 olday,neway=ay('index1',old),ay('index12',new);mp=dict(zip(old+[olday],[v(i) for i in new+[neway]]));removed=[];aliased=0
 for d in cert['architecture_changes']:
  if d['kind']=='strict_delete':removed.append(d['old'])
  elif d['kind']=='strict_alias':
   eq(sub(P(d['old']['terms']),mp),P(d['new']['terms']),'exact strict coordinate alias');eq(d['old']['label'],d['new']['label'],'strict alias label');aliased+=1
 require(len(removed)==2,'duplicate norm/gate deletion census')
 require(any(r['label']=='index1.norm1' for r in removed),'duplicate principal norm deletion')
 require(any(equivalent(P(r['terms']),add(v(olday),scale(mul(v(ns['shared.A']),v(old[1])),-1))) for r in removed),'duplicate AY gate deletion')
 require(not {i for r in source['residuals'] for m in P(r['terms']) for i in m}&set(old+[olday]),'old pair remains live')
 sx=ns['x'];calls=cert['square_budget']['power_calls']
 for j in [1,2,14]:eq(P(calls[j]['exponent']),v(sx),'strict exact power index')
 merged=[d for d in cert['seed_data'] if d['pair']==new];require(len(merged)==1,'unique merged principal pair');eq(merged[0]['calls'],[1,2,14],'merged request inventory');eq(P(merged[0]['exponent']),v(sx),'merged exact index')
 return {'range_edits':changes,'deleted_duplicate_rows':len(removed),'alias_edits':aliased,'independent_pairs':len(cert['seed_data']),'power_calls':len(calls)}

def run(path,end):
 path,end=Path(path),Path(end);read=lambda n:json.loads((path/(n+'.json')).read_text());er=lambda n:json.loads((end/(n+'.json')).read_text())
 source,guarded,cert=read('source'),read('guarded'),read('transform_certificate');projected=read('projected');equation=er('equation');ex=er('expanded_polynomial');tc=er('translation_certificate')
 strict=strict_delta(path,source,cert) if cert.get('strict_budget') else None
 result={'strict_delta':strict,'path':str(path),'endpoint':str(end),'semantic':semantic(source,guarded,cert),'monic_inverses':project(read('factored_source'),projected,read('projection_certificate')),'translation':translate(projected,equation,tc),'quartic':expansion(equation,ex)}
 rejected=[]
 def trial(name,fun):
  try:fun()
  except (AssertionError,KeyError,IndexError,ValueError):rejected.append(name);return
  raise AssertionError('Mutation accepted: '+name)
 z=copy.deepcopy(cert);next(q for q in z['guards'] if q['kind']=='shared_square_cap')['expression'][0][0]+=1;trial('squared-cap sign',lambda:semantic(source,guarded,z))
 z=copy.deepcopy(source);next(r for r in z['residuals'] if r['label'].startswith('cap.pooled_index_residue') or r['label']=='cap.index_residue_0')['terms'][0][0]+=1;trial('pooled index row',lambda:semantic(z,guarded,cert))
 z=copy.deepcopy(source);next(r for r in z['residuals'] if r['label']=='cap.common_multiple')['terms'][0][0]+=1;trial('odd auxiliary multiplier',lambda:semantic(z,guarded,cert))
 z=copy.deepcopy(cert);z['sign_inference']['proof_steps'][0]['rhs'][0][0]+=1;trial('raw-sign identity',lambda:semantic(source,guarded,z))
 z=read('projection_certificate');z['steps'][0]['restoration'][0][0]+=1;trial('monic restoration',lambda:project(read('factored_source'),projected,z))
 z=copy.deepcopy(tc);z['shifts'][0][1]+=1;trial('translation',lambda:translate(projected,equation,z))
 z=copy.deepcopy(ex);z['terms'][0][0]+=1;trial('quartic coefficient',lambda:expansion(equation,z))
 if cert.get('strict_budget'):
  z=copy.deepcopy(cert);next(d for d in z['architecture_changes'] if d['kind']=='strict_alias')['new']['terms'][0][0]+=1;trial('strict pair alias',lambda:strict_delta(path,source,z))
  z=copy.deepcopy(cert);z['architecture_changes'].remove(next(d for d in z['architecture_changes'] if d['kind']=='strict_delete'));trial('missing duplicate norm deletion',lambda:strict_delta(path,source,z))
  z=json.loads((path/'input_raw.json').read_text());next(d for d in z['ranges'] if d[3]=='crt.range.u')[1]=['c',1];trial('strict beta range lower index',lambda:strict_delta(path,source,cert,z))
  z=copy.deepcopy(cert);next(d for d in z['seed_data'] if d['calls']==[1,2,14])['calls']=[1,2];trial('incomplete merged request ledger',lambda:strict_delta(path,source,z))
 result['rejected_mutations']=rejected
 return result
if __name__=='__main__':print(json.dumps(run(sys.argv[1],sys.argv[2]),indent=2))
