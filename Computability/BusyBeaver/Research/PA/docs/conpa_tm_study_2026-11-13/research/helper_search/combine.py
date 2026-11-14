from pathlib import Path
import json, subprocess, time
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic as S
from site_contexts import contexts

OUT=Path(__file__).parent
root,nodes=S.source_tree()
def change(t,h_only,mp):
    if mp and t==nodes['node163']:
        return nodes['node6'], nodes['node147']
    if h_only and t==nodes['node170']:
        return ((change(nodes['node36'],False,mp),(change(nodes['node167'],False,mp),nodes['node145'])),nodes['node57'])
    if t[0]=='leaf':return t
    return change(t[0],h_only,mp),change(t[1],h_only,mp)

def main():
    records=[]
    for h,mp in [(False,True),(True,False),(True,True)]:
        name='mp_h' if not h else ('h_only_mp_h' if mp else 'h_only')
        tree=change(root,h,mp);sites=S.flatten(tree)
        machine=S.load_machine()
        if mp:machine[115,1]=(1,1,108)
        if h:
            for key,row in { (37,0):(0,1,11),(37,1):(1,1,101),(127,0):(0,1,133),(127,1):(1,1,20),(133,0):(0,1,120)}.items():machine[key]=row
        S.all_sites=lambda:sites
        try:
            start=time.time();totals,_=S.verify(machine)
        except Exception as e:
            record={'variant':name,'status':'FAIL','error':str(e)};records.append(record);print(record,flush=True);continue
        rec={'variant':name,'status':'PASS','source_sites':len(sites),'seconds':time.time()-start,**totals}
        path=OUT/(name+'.tm')
        path.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n) in sorted(machine.items())))
        (OUT/(name+'_sites.json')).write_text(json.dumps(sites)+'\n')
        ctx=contexts(4,True,machine)
        protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}
        cp=OUT/(name+'_contexts.txt')
        cp.write_text(''.join(f'{q} {int(q not in protected and bool(v))} {len(v)} '+ ' '.join(map(str,sorted(v)))+'\n' for q,v in ctx.items()))
        (OUT/(name+'_contexts.json')).write_text(json.dumps({q:sorted(v) for q,v in ctx.items()})+'\n')
        result=subprocess.run([str(OUT/'helper'),str(path),str(cp),str(OUT/(name+'_candidates.txt'))],capture_output=True,text=True,check=True)
        rec['synthesis']=result.stderr.strip();records.append(rec);print(rec,flush=True)
    (OUT/'combination_results.json').write_text(json.dumps(records,indent=2)+'\n')
if __name__=='__main__':main()
