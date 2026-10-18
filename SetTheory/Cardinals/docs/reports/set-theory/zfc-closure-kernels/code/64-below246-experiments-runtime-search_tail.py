from pathlib import Path
import os,sys,json,hashlib
HERE=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC246_BASE',str(HERE.parents[1]/'context246/zfc-context246')))
sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import read_table
from check_local_contracts import blocks,marked,paint
BASE_TABLE=BASE/'machine/zfc_prefix246_old.tm'
BASE_SHA256='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
assert hashlib.sha256(BASE_TABLE.read_bytes()).hexdigest()==BASE_SHA256
T=read_table(BASE_TABLE)

def sim(T,mode,values,r,left=[1,0,1],fuel=2000):
    initial=paint(marked(values,r),left,0)
    one=set(initial);q=73 if mode=='i' else 95;h=0
    expected=values.copy()
    if mode=='i':expected[r]+=1
    elif expected[r]:expected[r]-=1
    if mode=='z':
        target=(112,-1,paint(blocks(values),left,0))
    elif mode=='p':
        target=(48,0,paint(blocks(expected),[1]+left,1))
    else:
        main=blocks(expected)
        target=(48,-1,paint(main,left,0))
    seen=set()
    for step in range(fuel):
        if mode=='i' and q==48 and h==-1:
            maxone=max(one,default=-1)
            if any(((i in one)!=(i in target[2])) for i in range(-len(left),len(main))):return None
            tail=[int(i in one) for i in range(len(main),maxone+1)]
            extras=[];j=0
            while j<len(tail):
                if tail[j]!=0:return None
                j+=1;k=0
                while j<len(tail) and tail[j]==1:k+=1;j+=1
                if k<1:return None
                extras.append(k-1)
            return step,extras
        if mode!='i' and (q,h,one)==target:return step,[]
        # All candidate macro excursions must remain within their prescribed
        # left interface rather than running the global proof program.
        if h < -1:return None
        key=(q,h,tuple(sorted(one)))
        if key in seen:return None
        seen.add(key)
        try:w,d,q=T[q,int(h in one)]
        except KeyError:return None
        if w:one.add(h)
        else:one.discard(h)
        h+=d
    return None

def main():
    qs=sorted({q for q,b in T}-{255})
    cases=[('z',[0,0],0),('i',[0,0],0),('z',[3,0,2],1),('i',[3,2,0],1),('i',[2,0,3,1],2)]
    out=[]
    for w in (0,1):
        for d in (-1,1):
            for q in qs:
                U=T.copy();U[75,0]=(w,d,q)
                outcomes=[]
                for mode,values,r in cases:
                    ans=sim(U,mode,values,r)
                    if ans is None:break
                    outcomes.append(ans)
                else:out.append({'edit':[75,0,w,d,q],'outcomes':outcomes})
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
