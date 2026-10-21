#!/usr/bin/env python3
"""Rebuild exact native tables from pinned K219 deltas; audit source replacement recipes."""
import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE_TABLE_SHA='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
BASE_SITES_SHA='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
D5=('CD',5);D6=('CD',6);C1=('CC',1);C2=('CC',2);B1=('CB',1)
P=(D6,C2);U=(P,B1);A=(D5,U);L=(A,D6);Z=(D5,C1);E=(L,(Z,U))
WEAK=(L,B1)
UZ=(P,D6);ZERO=(((D5,UZ),D6),(Z,UZ))

def sha(raw):return hashlib.sha256(raw).hexdigest()
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode('ascii')
def leaf(x):return isinstance(x[0],str)
def sites(t,p=''):
 return[[p,*t]]if leaf(t)else sites(t[0],p+'0')+sites(t[1],p+'1')
def tree(rows):
 d={}
 for p,op,arg in rows:
  v=d
  for bit in p:v=v.setdefault(bit,{})
  assert not v;v['leaf']=(op,arg)
 def go(v):return v['leaf']if'leaf'in v else(go(v['0']),go(v['1']))
 t=go(d);assert sites(t)==rows;return t

def replace(t,new):
 if t==E:return new,1
 if leaf(t):return t,0
 a,n=replace(t[0],new);b,m=replace(t[1],new);return(a,b),n+m

def table(raw):
 t={}
 for line in raw.decode('ascii').splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();assert(int(q),int(b))not in t;t[int(q),int(b)]=(int(w),d,int(z))
 return t

def table_bytes(t):
 return('#! start 0\n'+''.join(f'{q} {bit} {w} {d} {z}\n'for(q,bit),(w,d,z)in sorted(t.items()))).encode('ascii')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline219',type=Path,required=True);a=ap.parse_args();br=(a.baseline219/'machine/k219.native.tm').read_bytes();bs=(a.baseline219/'machine/sites219.json').read_bytes();assert sha(br)==BASE_TABLE_SHA and sha(bs)==BASE_SITES_SHA
 original=table(br);source=tree(json.loads(bs));answers=[]
 for name in ['weak218_rejected','zero_guard219','counter_salt223_interface']:
  D=HERE/name;delta=json.loads((D/'delta_from_k219.json').read_text());manifest=json.loads((D/'manifest.json').read_text());assert delta['baseline_table_sha256']==BASE_TABLE_SHA
  t={k:v for k,v in original.items()if k[0]not in delta['delete_states']}
  for q,b,w,d,z in delta['set_rows']:t[q,b]=(w,d,z)
  raw=table_bytes(t);assert raw==(D/'machine.native.tm').read_bytes() and sha(raw)==manifest['table_sha256']
  st={q for q,b in t};assert len(st)==manifest['working_states'] and len(t)==2*len(st);assert all((q,b)in t for q in st for b in[0,1]);assert{z for w,d,z in t.values()}-st=={254}
  sr=(D/'sites.json').read_bytes();assert sha(sr)==manifest['sites_sha256'];tree(json.loads(sr))
  recipe='external counter-salt source construction; supplied source hash verified'
  if name in ['weak218_rejected','zero_guard219']:
   new,n=replace(source,WEAK if name=='weak218_rejected'else ZERO);assert n==4 and compact(sites(new))==sr;recipe='exact four-occurrence equality-macro replacement verified'
  answers.append({'name':name,'working_states':len(st),'table_sha256':sha(raw),'source_sha256':sha(sr),'source_recipe':recipe,'scope':'Exact syntax/census only; mathematical boundaries remain those in manifest and report.'})
 print(json.dumps(answers,indent=2))
if __name__=='__main__':main()
