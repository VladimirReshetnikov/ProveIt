from pathlib import Path
exec(Path('rotate_effective.py').read_text().split('best=cost(initial)')[0])
from collections import deque
queue=deque([initial]);seen={initial};tested={initial:62};start=time.time();best=62
while queue and len(seen)<100000:
    t=queue.popleft()
    for node in stats(t)[2]:
        for rr in rotations(node):
            nt=replace(t,node,rr)
            if nt in tested:continue
            cc=cost(nt);tested[nt]=cc[0]
            if cc[0]<=62:
                seen.add(nt);queue.append(nt)
                if cc[0]<best:
                    best=cc[0];print('BEST',cc[:3],'tested',len(tested),'secs',time.time()-start,flush=True)
                    Path(f'effective_{best}.json').write_text(json.dumps(encode(nt),indent=2));raise SystemExit()
    if len(seen)%100==0 or not queue:print('seen',len(seen),'queue',len(queue),'tested',len(tested),'secs',time.time()-start,flush=True)
