from pathlib import Path
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def replace(t,a,b):
    if t==a:return b
    if t[0]=='leaf':return t
    return replace(t[0],a,b),replace(t[1],a,b)

def setup(short=False):
    t,n=S.source_tree()
    old=n['node164'];(a,b),(c,d)=old;new=(a,((b,c),d))
    t=replace(t,old,new);(a,b),(c,d)=t;t=(a,((b,c),d))
    ns=S.flatten(t);S.all_sites=lambda:ns
    m=S.load_machine()
    for q,b,v in [(75,0,63),(132,0,50),(50,0,64),(50,1,127),(88,0,126),(115,0,117),(117,0,28),(117,1,70)]:m[q,b]=(b,1,v)
    if short:m[23,0]=(0,-1,69)
    return m,t

if __name__=='__main__':
    m,t=setup(False);cs=S.contracts()
    fail=[(i,branch)for i,branch,br,s,z in cs if S.execute(m,br,s,z)is None]
    print('fails',fail,flush=True)
    affected=[c for c in cs if c[0]in(11,20)]
    successes=[]
    for w,d,nn in itertools.product((0,1),(-1,1),range(196)):
        mm=m.copy();mm[64,0]=(w,d,nn)
        if all(S.execute(mm,br,s,z)for i,branch,br,s,z in affected):
            print('prelimsuccess',mm[64,0],flush=True)
            if all(S.execute(mm,br,s,z)for i,branch,br,s,z in cs):
                print('ALLSUCCESS',mm[64,0],flush=True);successes.append(mm[64,0])
                Path(__file__).with_name('rotated_success.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for(q,b),(w,d,t)in sorted(mm.items())))
    print('successes',successes)
