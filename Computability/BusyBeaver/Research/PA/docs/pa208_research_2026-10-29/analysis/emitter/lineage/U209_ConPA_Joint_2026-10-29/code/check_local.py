#!/usr/bin/env python3
"""Independent opaque-exterior proof of prefold212 -> literal209.
No builder, source compiler, or symbolic-induction engine is imported.
All verification conditions remain active under python -O.
"""
from pathlib import Path
import argparse,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
def need(ok,msg):
    if not ok:raise ValueError(msg)
def read(path,count):
    table={};start=[]
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):start.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in table and b in(0,1)and w in(0,1)and d in('L','R'),'Bad row')
        table[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in table}
    need(start==[0]and 0 in states and 254 not in states,'Start/halt')
    need(len(states)==count and set(table)=={(q,b)for q in states for b in(0,1)},'Census')
    need({z for w,d,z in table.values()}-states=={254},'Closure');return table
def execute(table,q,cells,n):
    tape=dict(cells);head=0;trace=[]
    for _ in range(n):
        need(q!=254 and head in tape,'Halt or opaque exterior read')
        b=tape[head];w,d,z=table[q,b];trace.append([q,head,b,w,d,z])
        tape[head]=w;head+=d;q=z
    return(q,head,tape),trace
def incoming(table,q):return sorted([p,b,w,d]for(p,b),(w,d,z)in table.items()if z==q)
def certify(old,new):
    rho=lambda q:{180:163,181:220,218:157}.get(q,q)
    special={163,180,220,181,218}
    need(set(old)-set(new)=={(q,b)for q in(180,181,218)for b in(0,1)}and not set(new)-set(old),'Deleted rows')
    inventory={163:[[217,0,0,1]],180:[[132,1,1,1],[199,1,1,1]],
      220:[[216,0,0,1]],181:[[185,1,1,1]],
      218:[[158,0,0,1],[211,0,0,1],[215,0,0,1],[220,0,0,1]]}
    for q,rows in inventory.items():need(incoming(old,q)==rows,'Incoming census '+str(q))
    ordinary=0
    for(q,b),(w,d,z)in old.items():
        if q not in special:
            need(new[rho(q),b]==(w,d,rho(z)),'Ordinary quotient row');ordinary+=1
    cases=[]
    for q,tag,t0,t1 in[(163,0,5,1),(180,1,3,1),(220,0,3,1),(181,1,3,1),(218,0,3,3)]:
        for bit,steps in[(0,t0),(1,t1)]:
            cells={-1:tag,0:bit};old_end,pa=execute(old,q,cells,1);new_end,pb=execute(new,rho(q),cells,steps)
            need(new_end==(rho(old_end[0]),old_end[1],old_end[2]),'Special endpoint')
            need(old_end[2]==cells,'Unexpected tape alteration')
            cases.append({'old_state':q,'new_state':rho(q),'left_tag':tag,'scanned':bit,
              'old_steps':1,'new_steps':steps,'old_trace':pa,'new_trace':pb,'exterior_unread':True})
    need(ordinary==414 and len(cases)==10,'Certificate census')
    return{'status':'DIRECT_LOCAL_SIMULATION_PASS','old_states':212,'new_states':209,
      'ordinary_rows':ordinary,'incoming_inventories':inventory,'cases':cases,
      'minimum_block_steps':1,'maximum_block_steps':5,
      'scope':'All common initial tapes from state0; prefold212 -> U209 only. Positive finite blocks with identical tape/head at endpoints.'}
def check(machine,output):
    machine=Path(machine);old=read(machine/'prefold212.native.tm',212);new=read(machine/'u209.native.tm',209)
    result=certify(old,new);parent=read(ROOT/'baseline/u212.native.tm',212)
    repair=[]
    for left in(0,1):
        cells={-1:left,0:0};n=2+left
        a,pa=execute(parent,171,cells,n);b,pb=execute(old,171,cells,n)
        need(a==b and a[2]==cells,'Engine repair identity')
        repair.append({'left_bit':left,'steps':n,'old_trace':pa,'new_trace':pb})
    result['engine_repair_cases']=repair
    tests=[('wrong_163_tag','old',(217,0),(1,1,163)),
      ('wrong_180_tag','old',(199,1),(0,1,180)),('wrong_220_direction','old',(216,0),(0,-1,220)),
      ('wrong_181_tag','old',(185,1),(0,1,181)),('wrong_218_tag','old',(215,0),(1,1,218)),
      ('wrong_selector163','new',(163,0),(0,1,211)),('wrong_selector220','new',(220,0),(0,1,129)),
      ('wrong_helper211','new',(211,0),(0,1,184)),('wrong_helper129','new',(129,1),(1,1,158)),
      ('wrong_helper67','new',(67,0),(0,1,90)),('wrong_common_branch','new',(163,1),(0,1,211)),
      ('wrong_ordinary_row','new',(0,0),(1,1,66))]
    rejected=[]
    for name,side,key,action in tests:
        a,b=dict(old),dict(new);(a if side=='old'else b)[key]=action
        try:certify(a,b)
        except(ValueError,KeyError):rejected.append(name)
        else:raise ValueError('Corruption accepted: '+name)
    broken=dict(old);broken[171,0]=(0,-1,7)
    try:
        for bit in(0,1):
            cells={-1:bit,0:0};need(execute(parent,171,cells,2+bit)[0]==execute(broken,171,cells,2+bit)[0],'Missing repair')
    except(ValueError,KeyError):rejected.append('missing_engine_repair')
    else:raise ValueError('Missing repair accepted')
    result['negative_controls_rejected']=rejected
    result['native_sha256']=hashlib.sha256((machine/'u209.native.tm').read_bytes()).hexdigest()
    Path(output).write_text(json.dumps(result,indent=2)+'\n');return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,default=ROOT/'machine');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=check(a.machine,a.output);print(json.dumps({k:v for k,v in r.items()if k not in('cases','engine_repair_cases')},indent=2))
