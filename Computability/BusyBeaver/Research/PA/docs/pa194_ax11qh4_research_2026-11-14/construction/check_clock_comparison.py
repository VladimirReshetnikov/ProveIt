#!/usr/bin/env python3
"""Check exact source/resource correspondence and factor-two clock transport.

Uses the pinned parent's supplied, hash-bound symbolic certificate and the
fresh variant certificates. It does not rerun the parent universal interpreter.
It does freshly replay all three finite startups directly from dense tables.
Run the independent literal verifier separately to regenerate universal traces.
This finite checker is not a Lean kernel proof or a PA-consistency calibration.
"""
import argparse,collections,hashlib,json,pathlib

PINS={
 'parent':('19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50',
           '8335110bd89bcd5dfc1dbc4410f7d46aa4e94f8423c29e1d64cb5f5536498f13',57922),
 'left':('c825ec97fdaa36868d1830b601863d255853ebe061af8b22f432d55233763659',
         'af6d4bc9ab3df0fc9c1787f72cce1038d664f47af27947e09e4dd03d94074cf4',58088),
 'right':('9ea0169880ecaea748d11217c829420aa8694948d2578b8fc28adcc3bcf76815',
          '0d4a0dadf398e2557c47e9305b945bc610f7ea9753794f21f95d9dacc76bf37f',58088)}
PHY=(6,2,0,4,3,7,8,5,1)

def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def read_json(p):return json.loads(p.read_text())
def path_string(p):return ''.join(map(str,p)) if isinstance(p,list) else p

def load(folder,role):
    pin,contracts_pin,startup=PINS[role]
    raw=(folder/'machine.tm').read_bytes();require(sha(raw)==pin,role+' table hash')
    cbytes=(folder/'independent/contracts.json').read_bytes();require(sha(cbytes)==contracts_pin,role+' contract hash')
    receipt=read_json(folder/'independent/receipt.json')
    require(receipt['status']=='PASS' and receipt['dense_sha256']==pin and receipt['contracts_sha256']==contracts_pin,role+' receipt binding')
    labels=read_json(folder/'labels.json');require(len(labels)==len(set(labels))==195 and labels[0]==74 and labels[-1]==254,role+' label map')
    rows={}
    for line in raw.decode().splitlines():
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        require((q,b)not in rows and q in range(194) and b in(0,1) and w in(0,1) and d in('L','R') and t in range(195),role+' malformed table')
        rows[q,b]=(w,1 if d=='R'else-1,t)
    require(len(rows)==388,role+' incomplete table')
    sites=read_json(folder/'sites.json');instructions=read_json(folder/'instructions.json');contracts=json.loads(cbytes)
    require(len(sites)==len(instructions)==3671,role+' site count')
    expected=[(i,pos)for i,s in enumerate(sites)for pos in ([False,True]if s[1]=='dec'else[False])]
    require([(x['site'],x['positive'])for x in contracts]==expected and len(expected)==4778,role+' outcome coverage/order')
    for x in contracts:
        require(len(x['duration'])==len(x['motion'])==13,role+' affine dimension')
        require(x['duration'][0]>=3 and all(isinstance(v,int)and v>=0 for v in x['duration']),role+' affine duration sign')
    # Finite startup is replayed from the authoritative dense table itself.
    q=h=0;ones=set()
    for _ in range(startup):
        require(q!=194,role+' premature initialization halt')
        w,d,q=rows[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    require(labels[q]==84 and h==-2,role+' initial frame control/head')
    physical=[0]*9
    for i,j in enumerate(PHY):physical[j]=2 if i==0 else 0
    pc=path_string(sites[25][0]);require(len(pc)<=48 and set(pc)<=set('01'),role+' frame path')
    frame=[1]+list(map(int,pc))+[0]*(48-len(pc))+[1]
    for value in physical+[1]*26:frame+=[0]+[1]*(value+1)
    expected_ones={h-1+i for i,b in enumerate(frame)if b}
    require(ones==expected_ones,role+' whole initial frame tape')
    return {'folder':str(folder),'table_sha256':pin,'contracts_sha256':contracts_pin,
            'startup':startup,'sites':sites,'instructions':instructions,'contracts':contracts,
            'startup_frame':{'native_control':84,'head':h,'site':25,'gap':0,'logical_registers':[2]+[0]*8,'first_spare':1,'tail_width':75}}

def check(parent,left,right):
    data={k:load(p,k)for k,p in [('parent',parent),('left',left),('right',right)]}
    p,l,r=(data[k]for k in ('parent','left','right'))
    for v in(l,r):
        require(v['instructions']==p['instructions'],'Resolved source CFG mismatch')
        require([s[1:]for s in v['sites']]==[s[1:]for s in p['sites']],'Source opcode/register/argument mismatch')
        require(v['startup_frame']==p['startup_frame'],'Initial source resources differ')
    require(p['startup']<=l['startup']<=2*p['startup'],'Left startup comparison')
    require(p['startup']<=2*r['startup']and r['startup']<=2*p['startup'],'Right startup comparison')
    pairs=[];deltas={'left':collections.Counter(),'right':collections.Counter()};halt_sites=[]
    for a,b,c in zip(p['contracts'],l['contracts'],r['contracts']):
        key=(a['site'],a['positive']);require(key==(b['site'],b['positive'])==(c['site'],c['positive']),'Outcome alignment')
        require(a['motion']==b['motion']==c['motion'],'Frame motion/overflow differs')
        require(a['duration'][1:]==b['duration'][1:]==c['duration'][1:],'Nonconstant clock coefficient differs')
        require(all(x<=y<=2*x for x,y in zip(a['duration'],b['duration'])),'Left factor-two inequality')
        require(all(x<=2*y and y<=2*x for x,y in zip(a['duration'],c['duration'])),'Right factor-two inequality')
        op,arg=p['sites'][a['site']][1:]
        if op=='halt':
            halt_sites.append(a['site']);require(a['duration']==b['duration']==c['duration']==[3]+[0]*12,'Terminal clock')
            require(a['motion']==[3]+[0]*12,'Terminal motion')
        else:require(a['motion']==[0]*13,'Unexpected nonterminal root overflow')
        dl=b['duration'][0]-a['duration'][0];dr=c['duration'][0]-a['duration'][0]
        deltas['left'][dl]+=1;deltas['right'][dr]+=1
        pairs.append({'site':a['site'],'positive':a['positive'],'opcode':op,'argument':arg,
                      'parent_address':path_string(p['sites'][a['site']][0]),
                      'left_address':path_string(l['sites'][a['site']][0]),
                      'right_address':path_string(r['sites'][a['site']][0]),
                      'parent_duration':a['duration'],'left_constant_delta':dl,'right_constant_delta':dr,
                      'common_motion':a['motion']})
    require(halt_sites==[10],'Terminal site correspondence')
    return {'status':'PASS','scope':__doc__,'inputs':{k:{x:v[x]for x in('table_sha256','contracts_sha256','startup','startup_frame')}for k,v in data.items()},
            'paired_outcomes':len(pairs),'resolved_source_instructions':3671,'opcodes_and_register_fields_identical':True,
            'positive_decrement_parameters_identical':True,'all_motion_vectors_identical':True,'nonterminal_zero_overflow_outcomes':4777,
            'unique_terminal_site':10,'terminal_duration':3,'terminal_motion':3,'all_nonconstant_duration_coefficients_identical':True,
            'constant_difference_histograms':{k:dict(sorted(v.items()))for k,v in deltas.items()},
            'coefficientwise_bounds':['parent <= left <= 2*parent','parent <= 2*right and right <= 2*parent'],
            'halting_witness_bounds':['HaltBy(parent,t) -> HaltBy(left,2*t)','HaltBy(left,t) -> HaltBy(parent,t)',
                                     'HaltBy(parent,t) -> HaltBy(right,2*t)','HaltBy(right,t) -> HaltBy(parent,2*t)'],
            'theorem_boundary':'The witness implications follow using the written source-frame/list induction soundness and bounded inverse-clock proof; they are not a kernel theorem and do not establish absolute Con(PA) calibration.',
            'pairs':pairs}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    for n in('parent','left','right'):ap.add_argument('--'+n,type=pathlib.Path,required=True)
    ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
    result=check(args.parent,args.left,args.right);args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='pairs'},indent=2))
