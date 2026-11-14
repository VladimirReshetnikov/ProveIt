#!/usr/bin/env python3
"""Exact finite source-prefix audit of the context-sensitive CI1 repair.

This checker binds a literal three-row redirect and one fresh state to all
3,891 supplied source prefixes. It does not replace whole-tape primitive
simulation, which is supplied separately for the final table.
"""
from pathlib import Path
import argparse, collections, hashlib, json

def must(ok,why):
    if not ok:raise ValueError(why)

def parse(path):
    T={};start=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):start.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            must((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'bad row')
            T[q,b]=(w,1 if d=='R'else -1,z)
    must(start==[0],'bad start');return T

def prefix(T,pc):
    tape={-1:1,**{i:int(b)for i,b in enumerate(pc)}};q=84;h=0;trace=[];last=None;visits=[]
    for tick in range(10000):
        if h not in tape or(q,tape[h])not in T:return(q,h,tape),visits,trace
        b=tape[h]
        if q==150 and b==1:visits.append({'predecessor':list(last),'position':h,'leaf_position':len(pc)-1,'preceding_bit':tape[h-1]})
        w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);last=(q,b);tape[h]=w;q=z;h+=d
    raise ValueError('prefix proof construction limit reached')

def check(old_path,new_path,source_path):
    old=parse(old_path);new=parse(new_path);sites=json.loads(source_path.read_text())
    must(507 not in{q for q,b in old},'fresh state already exists')
    expected=dict(old)
    for q in(18,134,188):
        must(old[q,0]==(0,1,150),'retarget premise differs')
        expected[q,0]=(0,1,507)
    expected[507,0]=(0,1,90);expected[507,1]=(1,1,61)
    must(new==expected,'repair is not the exact prescribed split')
    must(old[150,0]==expected[507,0],'zero branch differs')
    must(old[150,1]==(1,-1,173)and old[173,1]==(1,1,182)and old[182,1]==(1,1,61),'canonical CI1 bounce differs')
    must(old[152,1]==(1,-1,170)and old[170,0]==(0,1,99)and old[99,1]==(1,1,61),'independent canonical CI1 bounce differs')
    affected=[];context_counts=collections.Counter();unchanged=0;route_rows=collections.Counter()
    for i,(pc,op,arg)in enumerate(sites):
        a,visits,trace=prefix(old,pc);b,_,newtrace=prefix(new,pc)
        for v in visits:
            context_counts[(tuple(v['predecessor']),v['position']==v['leaf_position'],v['preceding_bit'])]+=1
        for q,h,r,w,d,z in newtrace:
            if q==507:route_rows[r]+=1
        if a==b:unchanged+=1;continue
        must((op,arg)==('CI',1),'changed prefix is not CI1')
        must(a[0]==90 and b[0]==61 and a[1]==b[1]==len(pc)and a[2]==b[2],'prefix changed beyond the intended CI1 entry')
        v=[v for v in visits if v['position']==len(pc)-1]
        must(len(v)==1 and v[0]['preceding_bit']==0 and tuple(v[0]['predecessor'])in{(18,0),(134,0),(188,0)},'incorrect context repair')
        must(a[2]=={-1:1,**{j:int(bit)for j,bit in enumerate(pc)}},'prefix tape not restored')
        affected.append({'site_index':i,'site':[pc,op,arg],'old_entry':90,'new_entry':61,'predecessor':v[0]['predecessor'],'head':len(pc),'tape_restored':True})
    must([x['site_index']for x in affected]==[3004,3232,3305,3435],'unexpected affected source occurrences')
    # Crucial distinction: (195,0)->150 deliberately continues a decoder.
    internal=sum(count for (pred,isleaf,bit),count in context_counts.items()if not isleaf)
    must(all(pred==(195,0)and bit==0 for(pred,isleaf,bit),count in context_counts.items()if not isleaf),'other internal context changed')
    return {'status':'EXACT_CONTEXT_SPLIT_AND_ALL_SOURCE_PREFIXES_PASS',
            'old_sha256':hashlib.sha256(old_path.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(new_path.read_bytes()).hexdigest(),
            'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
            'old_working_states':len(old)//2,'new_working_states':len(new)//2,
            'changed_retained_rows':[[q,0,*old[q,0],*new[q,0]]for q in(18,134,188)],
            'added_rows':[[507,b,*new[507,b]]for b in(0,1)],'source_occurrences_checked':len(sites),
            'unchanged_prefix_results':unchanged,'changed_prefix_results':affected,
            'retained_internal_decoder_occurrences':internal,
            'new_state_row_visits':{str(k):v for k,v in sorted(route_rows.items())},
            'all_150_read1_contexts':[{'predecessor':list(pred),'at_source_leaf':leaf,'preceding_bit':bit,'occurrences':count}for(pred,leaf,bit),count in sorted(context_counts.items())],
            'scope':'Exact finite code-prefix and routing-repair audit. Whole-tape correctness for arbitrary registers, gaps, and spares is a separate symbolic obligation; calibration of the new numerical axiom schema is separate.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('source',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    r=check(a.old,a.new,a.source);s=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')
if __name__=='__main__':main()
