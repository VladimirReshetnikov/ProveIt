from search_clones import *
def simplify(tt):
 history=[]
 while True:
  facts,_=v.bit_invariant(tt,0,10);states=sorted({q for q,b in tt});done=False
  for drop in reversed(states):
   if drop==0:continue
   used=[]if facts[drop]is None else [facts[drop][0]]if 0 in facts[drop]else[0,1]
   for keep in states:
    if keep==drop:continue
    phi=lambda q:keep if q==drop else q
    if any((tt[drop,b][0],tt[drop,b][1],phi(tt[drop,b][2]))!=(tt[keep,b][0],tt[keep,b][1],phi(tt[keep,b][2]))for b in used):continue
    nn={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in tt.items()if q!=drop}
    proof=v.prove(tt,nn,0,0,keep,drop,0,None,10,65,20000)
    if proof['status'].startswith('PASS'):
     history.append(dict(keep=keep,drop=drop,used=used,invariant=facts[drop],status=proof['status']));tt=nn;done=True;break
   if done:break
  if not done:return tt,history

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);a=ap.parse_args();p=a.directory
 tt,_=v.parse_table((p/'candidate225.klabels.tm').read_bytes());nn,history=simplify(tt);print('states',len(nn)//2,'history',history)
 (p/'simplified.tm').write_bytes(encode(nn));c.dump(p/'simplification.json',history)
