"""Independently test the proposed return-scanner shortening."""
import sys,json,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'support/work/optimize196'))
import core
rows,labels=core.machine()
def clean():
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    expected={-3,-2,46};i=47
    for v in physical:
        i+=1;expected.update(range(i,i+v+1));i+=v+1
    return 84,-2,expected
def startup(m,fuel=2000000):
    q=74;h=0;t=set();c=clean()
    changed=0
    for n in range(fuel):
        if (q,h,t)==c:return {'ok':True,'steps':n,'one_cells':len(t),'changes':changed}
        if (q,int(h in t)) not in m:return {'ok':False,'halt':q,'steps':n}
        a=m[q,int(h in t)];changed += a !=rows.get((q,int(h in t)))
        w,d,q=a
        if w:t.add(h)
        else:t.discard(h)
        h+=1 if d else -1
    return {'ok':False,'steps':fuel,'q':q,'head':h,'one_cells':len(t),'changes':changed}
def main():
    out={}
    cs=core.contracts()
    for remove,retain in [([34],23),([23,34],15),([15,23,34],9)]:
        m={k:v for k,v in rows.items() if k[0] not in remove}
        m[retain,0]=rows[34,0]
        name='drop_'+('_'.join(map(str,remove)))
        out[name]={'startup':startup(m),'symbolic':core.validate(m,cs)}
        print(name,out[name],flush=True)
    (ROOT/'scanner_results.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
