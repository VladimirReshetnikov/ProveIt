#!/usr/bin/env python3
"""Independent free-algebra audit of the new seven-head AX search inputs.

No compiler module, C++ score, numeric sample, or saved verification receipt is
trusted. This checks the emitted arithmetic expression trees and stack effects.
It does not prove physical runtime contracts or the PA interpretation itself.
"""
from pathlib import Path
import argparse,collections,hashlib,itertools,json

def require(v,msg):
    if not v:raise ValueError(msg)
ZERO=('zero',);ONE=('succ',ZERO)
def atom(s):return ('atom',s)
def S(x):return ('succ',x)
def I(x,y):return ('im',x,y)
def U(x,y):return S(S(I(y,x)))
def M(x,y):return S(I(x,y))
def E(x,y,flip=False):return S(S(S(I(y,x) if flip else I(x,y))))
def N(x):return I(x,ONE)
def AND(x,y):return N(I(x,N(y)))
def EX(x,y):return N(U(x,N(y)))
def ADD(x,y):return ('add',x,y)
ATOMS={s:atom(s)for s in ('t','a','d','h','y','x')}
SYMBOLS=['node58','node55','node65',['leaf','inc',1],'node72','node75','node70','node49','node142','node150',['leaf','breakTo',1]]
NAMES=['copyH','copyD','cons','incT','readH','readDCons','copyA','push','copyGuard','compareGuard','close']
PREFIX=[0,1,2,3,3,4,0,1,2,5,1,0,2,6,0,2,2,2]
SUFFIX=[8,9,10]

def execute(word,initial=None):
    if initial is None:
        t=ATOMS['t'];a=ATOMS['a'];d=ATOMS['d'];h=ATOMS['h'];stack=[];fields=[ATOMS['y'],ATOMS['x']]
    else:
        t,a,d,h,stack,fields=initial
        stack=list(stack);fields=list(fields)
    for token in word:
        require(isinstance(token,int)and 0<=token<8,'unexpected operation before cleanup')
        if token==0:stack.append(t);t=h
        elif token==1:stack.append(t);t=d
        elif token==2:
            require(stack,'stack underflow');t=I(stack.pop(),t)
        elif token==3:t=S(t)
        elif token==4:
            require(fields,'missing H field');h=ADD(h,fields.pop(0))
        elif token==5:
            require(fields,'missing D field');d=ADD(d,fields.pop(0));t=I(t,d)
        elif token==6:stack.append(t);t=a
        elif token==7:stack.append(t);t=ZERO
    return (t,a,d,h,stack,fields)

def heads(a,d,h,flip=False):
    return [
        I(EX(d,U(d,h)),h),
        I(U(d,U(a,h)),U(a,U(d,h))),
        I(M(h,d),I(E(h,a,flip),M(a,d))),
        I(E(h,d,flip),I(M(a,h),M(a,d))),
        EX(d,E(h,d,flip)),
        I(U(d,a),I(U(d,I(a,h)),U(d,h))),
        I(a,U(a,a))
    ]

def swap_antecedents(t):
    require(t[0]=='im'and t[2][0]=='im','exchange shape')
    return I(t[2][1],I(t[1],t[2][2]))

def prefix_state():
    a=ATOMS['a'];d=ADD(ATOMS['d'],ATOMS['x']);h=ADD(ATOMS['h'],ATOMS['y'])
    rho=I(I(I(h,ATOMS['d']),d),I(I(d,h),I(a,h)))
    expected=(rho,a,d,h,[ATOMS['t'],U(ATOMS['d'],ATOMS['h'])],[])
    require(execute(PREFIX)==expected,'fixed read/propositional prefix')
    return expected

def interpret_variant(word,head,flip):
    # Test this standalone formula program with a free accumulator and older stack.
    a,d,h=atom('A'),atom('D'),atom('H')
    old=atom('current');older=atom('older')
    result=execute(word,(old,a,d,h,[older],[]))
    require(result[1:4]==(a,d,h)and result[4]==[older,old]and result[5]==[], 'head changes scalar registers or older stack')
    formula=result[0]
    if head==6:
        for label,value in [('A',a),('D',d),('H',h)]:
            if formula==I(value,U(value,value)):
                return {'gamma_parameter':label,'antecedents_exchanged':False}
        raise ValueError('gamma is not a renamed diagonal head')
    for perm in itertools.permutations([('A',a),('D',d),('H',h)]):
        aa,dd,hh=[v for _,v in perm]
        target=heads(aa,dd,hh,flip)[head]
        for exchanged in ([False,True]if head in(2,3,5)else[False]):
            want=swap_antecedents(target)if exchanged else target
            if formula==want:
                return {'role_map':dict(zip(['A','D','H'],[k for k,v in perm])),'antecedents_exchanged':exchanged}
    raise ValueError(('head variant outside declared family',head,flip,formula))

def gate_value(a,d,h,variant):
    require(variant in range(4),'gate variant range')
    commute=bool(variant//2);swap=bool(variant%2)
    v=I(M(h,d),U(a,M(h,d)));point=I(a,M(a,d))
    left=I(a,I(M(h,d),M(a,d)))if commute else I(M(h,d),I(a,M(a,d)))
    right=I(M(a,d),a)
    matrix=AND(right,left)if swap else AND(left,right)
    sep=U(d,matrix);gate=U(a,I(sep,N(point)))
    return N(I(v,gate))

def check_gate_boolean():
    count=0
    imp=lambda x,y:(not x)or y
    for x,a,y in itertools.product((False,True),repeat=3):
        original=imp(x,imp(a,y))and imp(y,a)
        for mode in range(4):
            left=imp(a,imp(x,y))if mode//2 else imp(x,imp(a,y))
            right=imp(y,a)
            new=(right and left)if mode%2 else(left and right)
            require(original==new,'gate matrix Boolean identity')
            count+=1
    return count

def check_inputs(cfg):
    require(cfg['symbols']==SYMBOLS,'terminal-to-operation identities')
    require(cfg['prefix']==PREFIX and cfg['suffix']==SUFFIX,'fixed prefix/cleanup suffix')
    require(cfg['NG']in(1,4) and len(cfg['heads'])==2 and len(cfg['gate'])==2,'mode counts')
    check_gate_boolean()
    results=[]
    for flip in range(2):
        require([len(x)for x in cfg['heads'][flip]]==[6,6,12,12,6,12,3],'variant counts')
        for head,variants in enumerate(cfg['heads'][flip]):
            meanings=[interpret_variant(word,head,flip)for word in variants]
            results.append({'flip':flip,'head':head,'variants':meanings})
    ps=prefix_state();rho,a,d,h,oldstack,fields=ps
    current=atom('head');older=[atom('stack')]
    for flip in range(2):
        require(len(cfg['gate'][flip])==cfg['NG'],'declared gate count')
        for mode,gword in enumerate(cfg['gate'][flip]):
            st=execute(gword,(current,a,d,h,older,[]))
            require(st==(gate_value(a,d,h,mode),a,d,h,older+[current],[]),'independent separated-diagonal gate identity')
    return results

def expand_rules(rules,root):
    words=[]
    for i,pair in enumerate(rules):
        require(isinstance(pair,list)and len(pair)==2,'binary grammar rule')
        w=[]
        for j in pair:
            require(isinstance(j,int),'integer grammar label')
            if j<0:
                k=-1-j;require(0<=k<len(SYMBOLS),'terminal range');w.append(k)
            else:
                require(j<i,'grammar is not acyclic/topological');w+=words[j]
        require(len(w)<=2000,'unexpected grammar expansion')
        words.append(w)
    require(isinstance(root,int)and 0<=root<len(rules),'root range')
    return words[root]

def check_word_witness(cfg,witness,actual):
    require(witness['gate']in range(cfg['NG']) and witness['flip']in(0,1),'witness mode')
    order=witness['order'];roles=witness['roles'];flip=witness['flip']
    require(sorted(order)==list(range(7)),'order is not a seven-head permutation')
    require(len(roles)==7,'role count')
    chosen=[];meanings=[]
    for j in range(7):
        require(isinstance(roles[j],int)and 0<=roles[j]<len(cfg['heads'][flip][j]),'role selector')
        word=cfg['heads'][flip][j][roles[j]]
        chosen.append(word);meanings.append(interpret_variant(word,j,flip))
    want=PREFIX+sum((chosen[j]for j in order),[])+cfg['gate'][flip][witness['gate']]+SUFFIX
    require(actual==want,'grammar does not emit its declared head variants/order')
    require(len(actual)==190,'expected190 macro tokens')
    ps=prefix_state();rho,a,d,h,stack,fields=ps
    expected_head_values=[]
    for j in order:
        st=execute(chosen[j],(rho,a,d,h,[],[]));expected_head_values.append(st[0])
    top=gate_value(a,d,h,witness['gate'])
    require(execute(actual[:-3])==(top,a,d,h,stack+[rho]+expected_head_values,[]),'complete independent free-algebra/stack contract')
    return {'gate_variant':witness['gate'],'macro_tokens':190,'head_order_zero_based':order,'equality_arguments_reversed':bool(flip),'head_variants':meanings,
     'complete_expression_and_stack_exact':True,'parameter_reads_unchanged':True,'guard_suffix_unchanged':True,
     'input_word_sha256':hashlib.sha256(json.dumps(actual,separators=(',',':')).encode()).hexdigest(),
     'scope':'Exact expression/stack identity, schema role renaming, equality-code reversal, antecedent exchange and head reordering. No new logical schema is introduced; physical validation and PA proof transport are separate.'}

def check_witness(cfg,witness):
    return check_word_witness(cfg,witness,expand_rules(witness['rules'],witness['root']))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,required=True);ap.add_argument('--witness',type=Path);ap.add_argument('--out',type=Path)
    args=ap.parse_args();cfg=json.loads(args.inputs.read_text());variants=check_inputs(cfg)
    baseline={'rules':cfg['initial_rules'],'root':cfg['initial_root'],'flip':0,'gate':0,'roles':[0]*7,'order':list(range(7))}
    result={'input_sha256':hashlib.sha256(args.inputs.read_bytes()).hexdigest(),'all_input_variants_audited':sum(len(x['variants'])for x in variants),'gate_variants_audited':cfg['NG'],'gate_boolean_cases':check_gate_boolean(),'baseline':check_witness(cfg,baseline),'variant_meanings':variants}
    bad=dict(baseline);bad['order']=[1,0,2,3,4,5,6]
    try:check_witness(cfg,bad)
    except ValueError:result['wrong_metadata_negative_control_rejected']=True
    else:raise ValueError('negative control accepted')
    if args.witness:
        witness=json.loads(args.witness.read_text());result['witness_sha256']=hashlib.sha256(args.witness.read_bytes()).hexdigest();result['witness']=check_witness(cfg,witness)
    if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='variant_meanings'},indent=2))
if __name__=='__main__':main()
