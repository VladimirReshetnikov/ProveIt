from pathlib import Path
import sys,json,time,argparse,tempfile
R=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser(description='Optional relay source screen and literal probe; not an accepted machine.')
ap.add_argument('--output',type=Path)
a=ap.parse_args()
O=a.output or Path(tempfile.mkdtemp(prefix='relay193-replay-'))
O.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(R/'reference/haz/vendor'))
import compiler as c
rows={}
for ln in (R/'inputs/runtime193.native.tm').read_text().splitlines():
 q,b,w,d,t=ln.split();rows[int(q),int(b)]=int(w),d=='R',int(t)
rows[36,0]=(1,True,16);rows[16,1]=(1,False,56)
for q in [42,47,57,126,139,141]: rows[q,1]=(0,False,122)
(O/'relay193.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {t}\n' for(q,b),(w,d,t)in sorted(rows.items())))
sites,ins,contracts=c.source(c.read_grammar(R/'reference/haz/inputs/pa194.grammar.json'))
fails=[];counts=0
for ct in contracts:
 k=c.run(rows,ct,fuel=1500)
 if k is None:fails.append({'site':ct[0],'branch':ct[1],'instruction':ins[ct[0]],'path':''.join(map(str,sites[ct[0]][0]))})
 else:counts+=1
print('runtime conditional checks',counts,'passed',len(fails),'failed',flush=True)
(O/'relay_runtime_screen.json').write_text(json.dumps({'scope':'Screen with inherited arithmetic oracles; altered marker requires ZFC local lemma transport. Not a proof.', 'passed':counts,'failed':fails},indent=2)+'\n')
# Literal blank run with full-frame detector for all source sites.
words={sum(b<<i for i,b in enumerate(p)):j for j,(p,op,arg)in enumerate(sites)}
q,h,ones=74,0,set();frames=[];seen=set();start=time.monotonic();executed=0
for step in range(2_000_001):
 if q==254:print('HALT',step,flush=True);break
 if q==84 and len(ones)>=13 and min(ones)==h-1:
  word=sum(1<<i for i in range(48) if h+i in ones)
  if word in words:
   j=words[word];ps=sorted(x for x in ones if x>=h+48)
   if ps:
    gap=ps[0]-h-48;header=ps[0];v=[];i=1;pos=header;ok=True
    while i<len(ps):
     if ps[i]!=pos+2:ok=False;break
     length=1;pos=ps[i];i+=1
     while i<len(ps) and ps[i]==pos+1:length+=1;pos=ps[i];i+=1
     v.append(length-1)
    if ok and len(v)>=10:
     logical=[v[k] for k in c.PHYSICAL];f={'step':step,'site':j,'head':h,'padding':48+gap,'registers':logical,'spares':v[9:],'one_cells':sorted(ones)}
     key=(j,tuple(logical),h)
     if key not in seen:
      seen.add(key);frames.append(f)
      if len(frames)<=15:print('frame', {k:x for k,x in f.items() if k not in ['spares','one_cells']},flush=True)
      if j in range(25,45) and logical[1]==logical[2]==logical[5]==0:
       print('POTENTIAL SOUND SEED',f,flush=True);break
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1;executed+=1
else:step=2_000_000
(O/'relay_blank_frames.json').write_text(json.dumps({'requested_bound_in_legacy_script':2000000,'executed_transitions':executed,'legacy_reported_steps':step,'final_state':q,'final_head':h,'frames':frames,'seconds':time.monotonic()-start},indent=2)+'\n')
print('finished',step,'frames',len(frames),'lastsites',[f['site'] for f in frames[-10:]],flush=True)
