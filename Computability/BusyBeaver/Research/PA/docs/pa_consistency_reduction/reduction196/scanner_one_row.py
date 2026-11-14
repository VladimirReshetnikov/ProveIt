from compact_scanner import *

if __name__=='__main__':
    begin=time.time();m,tree=setup();cs=S.contracts();snaps=[]
    for i,b,br,s,t in cs:
        tr=[];S.execute(m,br,s,t,record=tr)
        here=next((z for k,z,row in tr if z[0]==2000),None)
        if here:snaps.append((i,b,br,here,t))
    base=m.copy();del base[2001,0];del base[2001,1]
    qs=sorted({q for q,b in base})
    found=[]
    for w,d,r in itertools.product((0,1),(-1,1),qs):
        n=base.copy();n[2000,0]=(w,d,r)
        if all(S.execute(n,br,s,t)for i,b,br,s,t in snaps):
            found.append((w,d,r));print('SUCCESS',w,d,r,flush=True)
            Path(__file__).with_name('scanner_one_success.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'for(q,b),(w,d,t)in sorted(n.items())))
    print('found',found,'time',time.time()-begin)
