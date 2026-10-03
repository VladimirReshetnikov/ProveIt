#!/usr/bin/env python3
"""Independent finite search census, all-gate recount, and four-winner audit."""
import argparse,hashlib,itertools,json,types
from collections import Counter
from pathlib import Path
SOURCE='ad761700350ea15ba048248ede5553f09eb407e9fc9d7bc0078b8c8c61bca625'
RECEIPT='dda2113548c9811336b9a601841b0dfeb6050d53554ae0e6f157a91a138551fd'
PINS={
 'three_mass_projected_endpoint_penalties.py':'f5fec893112b011564620834e0b76095c1ea53b9545d4fb76ccabb3230bdaaf6',
 'three_mass_selector_projection.py':'8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8',
 'three_mass_endpoint_penalties.py':'7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c',
 'review_three_mass_projected_endpoint_penalties.py':'a348f9ffa8e411892cd892986b304bec291adbeb500b167e267632b0327d6be9',
 'review_three_mass_selector_projection.py':'c519ac0693e4928b64a1fead9ab30212570d50eb63331cf3706d335f20906321',
 'three_mass_arithmetic.py':'d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'}
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(root,name):
 p=Path(root)/name;b=p.read_bytes();need(sha(b)==PINS[name],'Independent dependency pin')
 m=types.ModuleType('_mixed_search_review_'+name[:-3]);m.__file__=str(p.resolve());exec(compile(b,m.__file__,'exec'),m.__dict__);return m

def recount(p):
 available=set(p['variables']);need(len(available)==len(p['variables']),'Unique coordinates');deps={};ops=Counter()
 for row in p['source']:
  need(type(row)is list and len(row)==4,'Paid binary operation')
  n,op,a,b=row;need(type(n)is str and n not in available and op in ('+','-','*'),'Fresh valid operation')
  for atom in (a,b):need(type(atom)is int or type(atom)is str and atom in available,'Exact closed source atom')
  deps[n]=[x for x in (a,b) if type(x)is str and x in deps];available.add(n);ops[op]+=1
 live=set()
 def walk(n):
  if n in deps and n not in live:
   live.add(n)
   for v in deps[n]:walk(v)
 walk(p['output']);need(live==set(deps),'All charged source operations live')
 return {'M':ops['*'],'A':ops['+']+ops['-'],'total':len(deps)}

def run(source,receipt,root,repo):
 need(sha(Path(source).read_bytes())==SOURCE,'Search source pin')
 b=Path(receipt).read_bytes();need(sha(b)==RECEIPT,'Author receipt pin');saved=json.loads(b)
 Q=load(root,'three_mass_projected_endpoint_penalties.py');R=load(root,'three_mass_selector_projection.py');E=load(root,'three_mass_endpoint_penalties.py')
 I=load(root,'review_three_mass_projected_endpoint_penalties.py');A=load(root,'review_three_mass_selector_projection.py');P=load(root,'three_mass_arithmetic.py')
 need(A.exact(saved['dependency_pins'],PINS),'All six dependencies agree')
 data,archives=P.source_bytes(repo);counts=Counter();records=[]
 fixtures=[('incdec',2,False),('incdec',2,True),('incchain3',3,False),('incchain3',3,True)]
 need(len(saved['cases'])==len(fixtures),'Four exact source fixtures')
 with P.subjects(data) as(C,CT):
  for case,(name,h,clean) in zip(saved['cases'],fixtures):
   cert=A.fixture(C,CT,name,h,clean);need(A.exact(cert,case['certificate']),'Actual source export identity')
   B=len(cert.get('forward_certificate',cert)['branches']);expected=[];packets={}
   for indices in itertools.product(range(B),repeat=h):
    counts['complete_layouts']+=1
    for mode in ('direct','factored','horner'):
     for end in ('none','initial','terminal','both'):
      p=Q.emit(P,R,E,cert,mode,list(indices),end);ledger=recount(p);need(A.exact(ledger,p['ledger']),'Independent gate counts')
      row={'indices':list(indices),'mode':mode,'endpoints':end,'ledger':ledger,'degree':3};expected.append(row)
      key=(indices,mode,end);need(key not in packets,'No repeated schedule key');packets[key]=p
      counts['literal_schedule_recounts']+=1;counts['live_paid_gates']+=ledger['total']
   need(len(expected)==12*B**h and A.exact(expected,case['all_ledgers']),'Complete ordered grid, with multiplicity and every ledger')
   score=lambda row:(row['ledger']['total'],row['ledger']['M'])
   winner=min(expected,key=score);uniform=[r for r in expected if len(set(r['indices']))==1];uniform_winner=min(uniform,key=score)
   need(len(uniform)==12*B,'Every uniform index represented with identical endpoint modes')
   need(A.exact(winner,case['best']) and A.exact(uniform_winner,case['uniform_best']),'Exact optimum of stated finite family and tie order')
   p=packets[(tuple(winner['indices']),winner['mode'],winner['endpoints'])]
   need(A.exact(p,case['complete_best']),'Entire winning circuit saved exactly')
   info,(poly,parent,correction,restoration)=I.check(A,cert,p);need(A.exact(info['ledger'],winner['ledger']) and info['degree']==3,'Complete winner polynomial correction, degree and ledger')
   need(case['natural_witnesses']==p['natural_witnesses']==(2*B-1)*h,'Complete witness count')
   counts['entire_winner_polynomial_identities']+=1
   for lift in case['natural_lifts']:
    x=lift['input'];old=CT.make_clean_witness(cert,{'x':x}) if clean else C.make_witness(cert,{'x':x})
    mass=P.push(cert,old);projected={k:v for k,v in mass.items() if k not in restoration}
    need(A.exact(projected,lift['projected']),'Saved full natural tuple')
    actual=projected|{k:A.ev(q,projected) for k,q in restoration.items()}
    need(actual==mass and A.ev(poly,projected)==A.ev(parent,projected)==0,'Exact whole natural lift and full polynomial zero')
    need(P.pull(cert,actual)==old,'Original offset restoration');counts['complete_winner_natural_lifts']+=1
   records.append({'fixture':name,'horizon':h,'clean':clean,'branches':B,'candidate_count':len(expected),'uniform_candidate_count':len(uniform),'best':winner,'uniform_best':uniform_winner,'natural_witnesses':p['natural_witnesses']})
 need(counts['complete_layouts']==62 and counts['literal_schedule_recounts']==744,'Exhaustive stated census total')
 return {'search_source_sha256':SOURCE,'author_receipt_sha256':RECEIPT,'dependency_pins':PINS,'archive_pins':archives,'counts':dict(counts),'cases':records,'scope':'Independent complete finite-grid census and fresh gate recount; four winning full polynomials checked by the already independent pinned engine; no new emitter, no unrestricted optimum'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--receipt',required=True);ap.add_argument('--root',required=True);ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();r=run(a.source,a.receipt,a.root,a.repo)
 if a.expect:
  A=load(a.root,'review_three_mass_selector_projection.py');need(A.exact(r,json.loads(Path(a.expect).read_text())),'Typed saved review receipt')
 Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps(r['counts'],sort_keys=True))
