from pathlib import Path
import json,sys
base=Path('upstream/U208_ConPA_2026-10-29/U208_ConPA_2026-10-29')
sys.path.insert(0,str(base/'code'))
import independent_runtime as ir
T=ir.table(base/'machine/u208.native.tm')
sites=json.loads((base/'machine/sites.json').read_text())
def frame(site, vals,header=56,spares=(0,)):
    pc,op,arg=site
    ones={-1,header}|{i for i,b in enumerate(pc) if b=='1'}
    phys=[0]*9
    for i,j in enumerate(ir.PHY):phys[j]=vals[i]
    p=header+1
    for v in phys+list(spares):
        ones.update(range(p+1,p+v+2));p+=v+2
    return ones

def run(table,site,vals,maxsteps=10000,header=56,log=False):
    ones=frame(site,vals,header=header);q=84;h=0;trace=[]
    for i in range(maxsteps):
        b=int(h in ones);w,d,z=table[q,b]
        if log and (q in [1,2,3,5,9,15,23,34,75,84] or i<30):
            trace.append((i,q,h,b,w,d,z,[(j,int(j in ones)) for j in range(h-8,h+9)]))
        ones.add(h) if w else ones.discard(h)
        h+=d;q=z
        if q in (84,254):return {'steps':i+1,'q':q,'h':h,'ones':sorted(ones),'trace':trace}
    return {'steps':maxsteps,'q':q,'h':h,'ones':sorted(ones),'trace':trace,'fail':True}

if __name__=='__main__':
 U=T.copy();U[23,0]=(0,-1,75);U.pop((34,0));U.pop((34,1))
 for pos in [0,1]:
    vals=[0]*9;vals[8]=pos
    a=run(T,sites[0],vals,log=True);b=run(U,sites[0],vals,log=True)
    print('POS',pos,'BASE', {k:v for k,v in a.items() if k!='trace'},'NEW', {k:v for k,v in b.items() if k!='trace'})
    Path(f'analysis/runtime_redesign/trace_{pos}.json').write_text(json.dumps({'base':a,'short':b},indent=2))
    print('BASE ORIGIN TRACE')
    for row in a['trace']:
      if row[1] in [1,2,3,5,9,15,23,34,75,84]:print(row[:7],''.join(str(bit) for j,bit in row[7]))
    print('NEW ORIGIN TRACE')
    for row in b['trace']:
      if row[1] in [1,2,3,5,9,15,23,34,75,84]:print(row[:7],''.join(str(bit) for j,bit in row[7]))
