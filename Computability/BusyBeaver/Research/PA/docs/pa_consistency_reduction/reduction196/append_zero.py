from pathlib import Path
import sys,collections,time,json
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def inspect(tape,h):
    if {x for x in tape if x<h}!={h-1} or h not in tape:return
    aft=sorted(x-h for x in tape if x>h)
    if not aft or aft[0]<40:return
    gap=aft[0];pos=h+gap+1;vs=[]
    while pos not in tape and pos+1 in tape:
        pos+=1;n=0
        while pos in tape:n+=1;pos+=1
        vs.append(n-1)
    return gap,vs

def simulate(m,start,limit=2000000):
    tape=set();q=start;h=0;lastroots=[]
    for t in range(limit):
        if q==S.ROOT:
            c=inspect(tape,h)
            if c:
                print('FRAME',start,t,h,c,flush=True)
                if len(c[1])>=10 and c[1][:9]==[0,0,0,0,0,0,2,0,0]:return t,c,sorted(tape),h
            if len(lastroots)<10:lastroots.append((t,h,len(tape)))
        b=int(h in tape)
        if (q,b)not in m:print('HALT',start,t,flush=True);return
        w,d,q=m[q,b]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d
    print('FINISH',start,t,q,h,len(tape),'roots',lastroots,flush=True)

if __name__=='__main__':
    m=S.load_machine();m[62,0]=(1,-1,51)
    for q in(0,1,5,16,35,62,85):
        ans=simulate(m,q)
        if ans:Path(__file__).with_name('appendzero_startup.json').write_text(json.dumps({'start':q,'result':ans}))
