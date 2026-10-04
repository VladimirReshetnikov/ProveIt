#!/usr/bin/env python3
"""Own-code arithmetic DAG schema. Never imports or executes frozen/upstream code.
Default prints a count; --emit prints each arithmetic gate as a JSON line.
Only fixed-numeral DAGs are streamed; the enormous strict constant prefix has a
separate exact finite grammar and ledger in PROOF.md and strict_cost().
"""
if not __debug__: raise RuntimeError("Optimized mode unsupported: checks require assertions")
import argparse, hashlib, json
U=481238074400
V=576000

def chain(n):
    if n<0: raise ValueError('Negative exponent')
    return 0 if n<2 else n.bit_length()-1+n.bit_count()-1

class DAG:
    def __init__(self, emit=False):
        self.counts={'M':0,'A':0}; self.equations=0; self.witnesses=[]
        self.digest=hashlib.sha256(); self.emit=emit; self.nodes=0
        self.inputs={'W','Wp','Q','InitialHead','InitialMemoryPlus','RawLeft','RawRight'}
    def witness(self,name):
        assert name not in self.inputs
        self.witnesses.append(name); self.inputs.add(name); return name
    def gate(self,op,a,b):
        if op not in {"+","-","*"}: raise ValueError("Unsupported arithmetic opcode")
        for val in (a,b):
            assert (type(val) is int and 0 <= val < self.nodes) or (type(val) is str and (val in self.inputs or val.startswith('C:')))
        row=[self.nodes,op,a,b]; payload=json.dumps(row,separators=(',',':'))
        self.digest.update((payload+'\n').encode())
        if self.emit: print(payload)
        out=self.nodes; self.nodes+=1; self.counts['M' if op=='*' else 'A']+=1
        return out
    def add(self,a,b):return self.gate('+',a,b)
    def sub(self,a,b):return self.gate('-',a,b)
    def mul(self,a,b):return self.gate('*',a,b)
    def eq(self,a,b):
        for val in (a,b):
            assert (type(val) is int and 0 <= val < self.nodes) or (type(val) is str and (val in self.inputs or val.startswith("C:")))
        self.equations+=1
        payload=json.dumps(['eq',a,b],separators=(',',':'))
        self.digest.update((payload+'\n').encode())
        if self.emit:print(payload)
    def power(self,a,n):
        if n==0:return 'C:1'
        result=a
        for bit in bin(n)[3:]:
            result=self.mul(result,result)
            if bit=='1':result=self.mul(result,a)
        return result
    def horner(self,base,coeffs):
        it=iter(coeffs);out=next(it)
        for coeff in it:out=self.add(self.mul(out,base),coeff)
        return out
    def receipt(self):
        return dict(self.counts, total=self.nodes, equations=self.equations,
                    positive_witnesses=len(self.witnesses),dag_sha256=self.digest.hexdigest())

def build(left_length,right_length,period_y=V,emit=False,dag=None):
    """period_y is overridable only for DAG-structure regression, not geometry."""
    if any(type(k) is not int or k<0 for k in [left_length,right_length]):raise ValueError('Lengths must be nonnegative integers')
    if type(period_y) is not int or period_y<1:raise ValueError('Period must be a positive integer')
    d=DAG(emit) if dag is None else dag;n=left_length+right_length;m=n+1
    X=d.witness('HorizontalExtra');H=d.witness('HalfRowsPower')
    K=d.witness('HalfPeriodRepunit');P=d.witness('PaddingPower')
    hx=d.add(X,'C:1')
    d.eq(d.sub('Wp','C:1'),d.mul('C:Cx',hx))
    G=d.power('W',period_y)
    gm1=d.sub(G,'C:1');hm1=d.sub(H,'C:1')
    d.eq(hm1,d.mul(gm1,K));d.eq('Q',d.mul(H,H))
    hy=d.mul(K,d.add(H,'C:1'))
    Gn=d.power(G,n);Gm=d.power(G,m);GR=d.power(G,right_length)
    d.eq(H,d.mul(P,Gm));d.eq('InitialHead',d.mul('C:Cu',H))
    bits=[]
    for side,size in [('L',left_length),('R',right_length)]:
        row=[]
        for i in range(size):
            b=d.sub(d.witness(f'{side}{i}Plus'),'C:1')
            d.eq(d.mul(b,d.sub(b,'C:1')),'C:0');row.append(b)
        raw='C:1'
        for b in row:raw=d.add(d.mul('C:2',raw),b)
        d.eq('RawLeft' if side=='L' else 'RawRight',raw)
        bits.append(row)
    tape=d.horner(G,list(reversed(bits[0]))+['C:0']+bits[1])
    tile=d.horner('W',(f'C:tile:{j}' for j in range(period_y-1,-1,-1)))
    first=d.horner('W',(f'C:first:{j}' for j in range(period_y-1,-1,-1)))
    anchor=d.horner('W',(f'C:anchor:{j}' for j in range(583,-1,-1)))
    bg=d.mul(hy,d.add(d.mul(hx,tile),d.mul('Wp',first)))
    powers={e:d.power('W',e) for e in [V-550,23945,263945,264000,24000]}
    anch=d.mul(d.mul(powers[V-550],Gn),anchor)
    middle=d.add(d.mul(powers[24000],tape),GR)
    tail=d.mul(d.mul(powers[263945],d.add(powers[264000],'C:1')),middle)
    marker_tail=d.add(powers[23945],tail)
    removed=d.mul(d.mul('C:C198',d.add('W','C:1')),marker_tail)
    delta=d.mul(d.mul('C:Cbase',P),d.sub(anch,removed))
    memory=d.add(bg,delta)
    d.eq('InitialMemoryPlus',d.add(memory,'C:1'))
    return d.receipt()

def build_uniform_wrapper(period_y=V,emit=False,dag=None):
    """Fixed wrapper only: A=G^(L+R), B=G^R and T already certified elsewhere.
    T is a possibly-zero expression port, not a new positive variable here.
    No raw-code, exponent synchronization, or dilation theorem is asserted.
    """
    if type(period_y) is not int or period_y<1:raise ValueError('Invalid period')
    d=DAG(emit) if dag is None else dag
    d.inputs.update({'DilationA','DilationB','DilationT'})
    X=d.witness('HorizontalExtra');H=d.witness('HalfRowsPower')
    K=d.witness('HalfPeriodRepunit');P=d.witness('PaddingPower')
    hx=d.add(X,'C:1')
    d.eq(d.sub('Wp','C:1'),d.mul('C:Cx',hx))
    G=d.power('W',period_y)
    d.eq(d.sub(H,'C:1'),d.mul(d.sub(G,'C:1'),K))
    d.eq('Q',d.mul(H,H))
    hy=d.mul(K,d.add(H,'C:1'))
    gm=d.mul('DilationA',G)
    d.eq(H,d.mul(P,gm));d.eq('InitialHead',d.mul('C:Cu',H))
    tile=d.horner('W',(f'C:tile:{j}' for j in range(period_y-1,-1,-1)))
    first=d.horner('W',(f'C:first:{j}' for j in range(period_y-1,-1,-1)))
    anchor=d.horner('W',(f'C:anchor:{j}' for j in range(583,-1,-1)))
    bg=d.mul(hy,d.add(d.mul(hx,tile),d.mul('Wp',first)))
    powers={e:d.power('W',e) for e in [V-550,23945,263945,264000,24000]}
    anch=d.mul(d.mul(powers[V-550],'DilationA'),anchor)
    middle=d.add(d.mul(powers[24000],'DilationT'),'DilationB')
    tail=d.mul(d.mul(powers[263945],d.add(powers[264000],'C:1')),middle)
    marker_tail=d.add(powers[23945],tail)
    removed=d.mul(d.mul('C:C198',d.add('W','C:1')),marker_tail)
    delta=d.mul(d.mul('C:Cbase',P),d.sub(anch,removed))
    d.eq('InitialMemoryPlus',d.add(d.add(bg,delta),'C:1'))
    receipt=d.receipt();receipt['radix_expression_node']=G
    return receipt

def uniform_wrapper_cost(v=V):
    base=closed_cost(0,0,v)
    return dict(M=base['M']+1,A=base['A'],total=base['total']+1,equations=6,positive_witnesses=4)

def closed_cost(L,R,v=V):
    n=L+R
    powcost=chain(v)+chain(n)+chain(n+1)+chain(R)+sum(chain(e) for e in [V-550,23945,263945,264000,24000])
    # Count independent rows of the displayed source, with the 584-term anchor.
    M=2*(v-1)+583+3*n+powcost+18
    A=2*(v-1)+583+4*n+13
    return {'M':M,'A':A,'total':M+A,'equations':n+8,'positive_witnesses':n+4}

def strict_cost(u=U,v=V):
    # Three basic constants: 0=1-1, -1=0-1, 2=1+1.
    # Tile coeffs: v ternary Horner strings of u bits; anchor coeffs:
    # 584 signed ternary Horner strings of 221 coefficients each.
    M=v*(u-1)+584*220+chain(u)+chain(u-219)+chain(198)
    A=v*(u-1)+584*220+4 # basic constants plus Cx=Cu-1
    return {'M':M,'A':A,'total':M+A}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--left-length',type=int,default=0);p.add_argument('--right-length',type=int,default=0);p.add_argument('--emit',action='store_true');p.add_argument('--full-stream',action='store_true');args=p.parse_args()
    cost=closed_cost(args.left_length,args.right_length)
    if args.emit or args.full_stream:
        measured=build(args.left_length,args.right_length,emit=args.emit)
        assert all(measured[k]==v for k,v in cost.items()),(measured,cost)
        cost=measured
    cost['strict_constant_prefix']=strict_cost()
    print(json.dumps(cost,indent=2))
