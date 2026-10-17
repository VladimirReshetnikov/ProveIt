"""Complete structured primitive-register version of the pattern certificate test.

Every generated operation is Wade/RMDag inc/decnz/break/continue/halt. The fast
interpreter optionally contracts explicitly listed arithmetic helper macros;
it never delegates certificate parsing/verification to the Python reference.
"""
from term_register import Program,REGISTERS,seq
from functools import cache

GLOBALS=('valid','full_cursor','nodes','node_bound','arena_i','proof_count','proofs_i',
 'rows_begin','row_tag','arg0','arg1','arg2','arg3','premise0','premise1','formula',
 'minor','major','query','scan_todo','scan_tag','scan_formula','scan_field',
 'path0','path1','active','gate_a','gate_b','gate_tag','gate_left','gate_right',
 'path_bit','path_loop','saved_cursor','dispatch','temp0','temp1','main_loop')
ARITY=(0,1,1,2,3,3,3,3,2,3,4,3)

class FullProgram(Program):
 def __init__(self,backend,templates):
  super().__init__(backend);self.templates=templates;self.macros={}
  for n in GLOBALS:self.r[n]=self.b.reg(n)
  self.names=tuple(self.b.registers)
 def mark(self,kind,args,body):
  root=self.b.add_sequence(body)
  if isinstance(root,int):self.macros[root]=(kind,args)
  return root
 @cache
 def clear(self,n):return self.mark('clear',(n,),super().clear(n))
 @cache
 def move(self,out,src):return self.mark('move',(out,src),super().move(out,src))
 @cache
 def copy(self,out,src):return self.mark('copy',(out,src),super().copy(out,src))
 @cache
 def pop(self):return self.mark('pop',(),super().pop())
 @cache
 def unary(self,out):return self.mark('unary',(out,),super().unary(out))
 @cache
 def fixed2(self,out):return self.mark('fixed2',(out,),super().fixed2(out))
 @cache
 def lt(self,a,b):return self.mark('lt',(a,b),super().lt(a,b))
 @cache
 def read_node(self):return super().read_node()
 def G(self,body):return self.branch('valid',body)
 def fail(self):return self.clear('valid')
 def sync(self):return self.branch('ok',(),self.fail())
 def req0(self,n):return self.G(self.branch(n,self.fail()))
 def reqpositive(self,n):return self.G(self.branch(n,(),self.fail()))
 @cache
 def eq(self,a,b):
  body=seq(self.clear('less'),self.inc('less'),self.copy('cmp_a',a),self.copy('cmp_b',b),
   self.b.while_decnz(self.r['cmp_a'],self.branch('cmp_b',self.dec('cmp_b'),seq(self.clear('less'),self.clear('cmp_a')))),
   self.branch('cmp_b',self.clear('less')),self.clear('cmp_b'))
  return self.mark('eq',(a,b),body)
 def require_eq(self,a,b):return self.G(seq(self.eq(a,b),self.branch('less',(),self.fail())))
 def require_ne(self,a,b):return self.G(seq(self.eq(a,b),self.branch('less',self.fail())))
 def require_bound(self,a,b):return self.G(seq(self.lt(a,b),self.branch('less',(),self.fail())))
 def constant(self,n,k):
  return self.G(seq(self.copy('temp0',n),*(self.branch('temp0',self.dec('temp0'),self.fail()) for _ in range(k)),self.req0('temp0')))
 @cache
 def reset_ok(self):return seq(self.clear('ok'),self.inc('ok'))
 @cache
 def field(self,out):
  return self.G(seq(self.copy('cursor','full_cursor'),self.reset_ok(),self.unary(out),self.sync(),self.copy('full_cursor','cursor')))
 @cache
 def fixed(self,out,width,full=True):
  # Horner accumulation is primitive, with one temporary copy per input bit.
  body=[self.clear(out)]
  for _ in range(width):
   body += [self.copy('temp1',out),self.move(out,'temp1'),self.pop(),self.guarded(self.branch('bit',self.inc(out)))]
  if full:return self.G(seq(self.copy('cursor','full_cursor'),self.reset_ok(),seq(*body),self.sync(),self.copy('full_cursor','cursor')))
  return seq(*body)
 def switch(self,n,cases,default=None):
  def chain(k):
   if k==len(cases):return self.fail() if default is None else default
   return self.branch('dispatch',seq(self.dec('dispatch'),chain(k+1)),cases[k])
  return seq(self.copy('dispatch',n),chain(0))
 @cache
 def skip_path(self,full=True,out=None):
  # Consume exactly the terminating0 or fail on truncation.
  body=seq(self.pop(),self.guarded(self.branch('bit',seq(self.pop(),self.guarded(self.inc('path_loop'))))))
  parse=seq(self.clear('path_loop'),self.inc('path_loop'),self.b.while_decnz(self.r['path_loop'],body))
  if not full:return parse
  return self.G(seq(self.copy('cursor','full_cursor'),self.reset_ok(),self.copy(out,'cursor') if out else (),parse,self.sync(),self.copy('full_cursor','cursor')))
 @cache
 def parse_row(self):
  cases=[]
  for tag,arity in enumerate(ARITY):
   body=[]
   for n in ('arg0','arg1','arg2','arg3','premise0','premise1'):body.append(self.clear(n))
   for i in range(arity):body.extend([self.field('arg'+str(i)),self.require_bound('arg'+str(i),'node_bound')])
   for i in range(2 if tag==1 else 1 if tag==2 else 0):body.extend([self.field('premise'+str(i)),self.require_bound('premise'+str(i),'proofs_i')])
   body.extend([self.field('formula'),self.require_bound('formula','node_bound')])
   if tag==11:body.extend([self.skip_path(out='path0'),self.skip_path(out='path1')])
   cases.append(seq(*body))
  return self.G(seq(self.fixed('row_tag',4),self.G(self.switch('row_tag',cases))))
 @cache
 def syntax(self):
  # Physical remaining-bit count prechecks are unnecessary for this constant-
  # space scanner: successful full parsing itself entails those inequalities.
  node=seq(self.inc('arena_i'),self.fixed('tag',2),self.field('left'),self.field('right'),
   self.require_bound('left','arena_i'),self.require_bound('right','arena_i'),
   self.G(self.branch('tag',(),self.branch('left',(),self.branch('right',(),self.fail())))))
  return seq(self.clear('valid'),self.inc('valid'),self.copy('full_cursor','candidate'),self.field('nodes'),
   self.copy('node_bound','nodes'),self.inc('node_bound'),self.clear('arena_i'),self.copy('scan_todo','nodes'),
   self.b.while_decnz(self.r['scan_todo'],self.G(node)),self.field('proof_count'),self.copy('rows_begin','full_cursor'),
   self.clear('proofs_i'),self.copy('scan_todo','proof_count'),
   self.b.while_decnz(self.r['scan_todo'],seq(self.parse_row(),self.inc('proofs_i'))),self.req0('full_cursor'))
 @cache
 def node(self,source):
  # read_node touches only the original18 helper registers, not GLOBALS.
  return self.G(seq(self.copy('index',source),self.read_node(),self.sync()))
 @cache
 def scan_row(self):
  # Earlier rows have passed the complete syntax scan. No row data is retained
  # except this formula; current outer parameters/formula/cursor are preserved.
  cases=[]
  for tag,arity in enumerate(ARITY):
   body=[self.unary('scan_field') for _ in range(arity+(2 if tag==1 else 1 if tag==2 else 0))]
   body.append(self.unary('scan_formula'))
   if tag==11:body.extend([self.skip_path(full=False),self.skip_path(full=False)])
   cases.append(seq(*body))
  return seq(self.fixed('scan_tag',4,full=False),self.switch('scan_tag',cases))
 @cache
 def get_formula(self,premise,out):
  return self.G(seq(self.copy('cursor','rows_begin'),self.reset_ok(),self.copy('scan_todo',premise),self.scan_row(),
   self.b.while_decnz(self.r['scan_todo'],self.scan_row()),self.sync(),self.copy(out,'scan_formula')))
 @cache
 def follow(self,bit):return self.G(self.branch('active',seq(self.node('active'),self.G(self.copy('active','right' if bit else 'left')))))
 @cache
 def matcher(self,pattern):
  checks=[]
  def visit(slot,path):
   prefix=[self.copy('active','formula')]+[self.follow(bit) for bit in path]
   if slot<pattern.arity:tail=self.require_eq('active','arg'+str(slot))
   elif slot==pattern.arity:tail=self.req0('active')
   else:
    tag,left,right=pattern.steps[slot-pattern.arity-1]
    tail=self.branch('active',seq(self.node('active'),self.constant('tag',tag)),() if tag==0 else self.fail())
   checks.append(self.G(seq(*prefix,tail)))
   if slot>pattern.arity:
    _,left,right=pattern.steps[slot-pattern.arity-1];visit(left,path+(0,));visit(right,path+(1,))
  visit(pattern.root,());return seq(*checks)
 @cache
 def gate(self,other,path):
  # Continue tokens consume one childbit; endtoken checks actual root mismatch.
  first=seq(self.node('gate_a'),self.G(seq(self.copy('gate_tag','tag'),self.copy('gate_left','left'),self.copy('gate_right','right'))))
  descend=seq(self.pop(),self.sync(),self.copy('path_bit','bit'),self.copy('saved_cursor','cursor'),
   self.reqpositive('gate_a'),self.reqpositive('gate_b'),first,self.node('gate_b'),self.require_eq('tag','gate_tag'),
   self.G(self.branch('path_bit',seq(self.copy('gate_a','gate_right'),self.copy('gate_b','right')),
       seq(self.copy('gate_a','gate_left'),self.copy('gate_b','left')))),
   self.G(seq(self.copy('cursor','saved_cursor'),self.inc('path_loop'))))
  terminal=self.branch('gate_a',self.branch('gate_b',seq(first,self.node('gate_b'),self.require_ne('tag','gate_tag'))),self.branch('gate_b',(),self.fail()))
  body=self.G(seq(self.pop(),self.sync(),self.G(self.branch('bit',descend,terminal))))
  return self.G(seq(self.copy('gate_a','arg2'),self.copy('gate_b',other),self.copy('cursor',path),self.reset_ok(),
   self.clear('path_loop'),self.inc('path_loop'),self.b.while_decnz(self.r['path_loop'],body)))
 @cache
 def semantic_row(self):
  mp=seq(self.require_eq('formula','arg0'),self.get_formula('premise0','minor'),self.get_formula('premise1','major'),
   self.G(self.branch('major',seq(self.node('major'),self.constant('tag',0),self.require_eq('left','minor'),self.require_eq('right','formula')),
      seq(self.req0('minor'),self.req0('formula')))))
  gen=seq(self.get_formula('premise0','minor'),self.reqpositive('formula'),self.node('formula'),
   self.constant('tag',2),self.require_eq('left','arg0'),self.require_eq('right','minor'))
  cases=[self.req0('formula'),mp,gen]
  for tag in range(3,12):
   body=self.matcher(self.templates[tag])
   if tag==11:body=seq(self.gate('arg0','path0'),self.gate('arg1','path1'),body)
   cases.append(body)
  return self.G(self.switch('row_tag',cases))
 @cache
 def verify(self,control_goal=None):
  # A trusted compile-time goal exists solely for positive finite controls.
  cases=seq(self.parse_row(),self.semantic_row(),self.inc('proofs_i'))
  endpoint=seq(self.reqpositive('formula'),self.node('formula'),self.constant('tag',1),self.req0('left'),self.req0('right'))
  if control_goal is not None:endpoint=self.constant('formula',control_goal)
  return seq(self.syntax(),self.reqpositive('proof_count'),self.copy('full_cursor','rows_begin'),self.clear('proofs_i'),
   self.copy('main_loop','proof_count'),self.b.while_decnz(self.r['main_loop'],cases),self.G(endpoint))
 def search(self,initial=0,control_goal=None):
  body=seq(self.verify(control_goal),self.G('halt'),self.inc('candidate'),'continue_forever')
  forever=self.b.label('forever',seq(self.inc('main_loop'),seq(body)))
  # Outer loop must not reuse main_loop, which verify consumes. Continue exits
  # are resolved structurally; the left guard is a register increment, not test.
  root=self.b.add_sequence(seq(*(self.clear(n) for n in self.names),*(self.inc('candidate') for _ in range(initial)),forever))
  self.b.sequences[root].name='main().0';return root


def execute_fast(P,root,values,fuel=20_000_000,contract_macros=True):
 """Use exact local loop contracts, not a reference certificate verifier."""
 remaining=fuel;calls=literal=accelerated=0;index={n:i for i,n in enumerate(P.names)}
 def get(n):return values[index[n]]
 def put(n,x):values[index[n]]=x
 def pop():
  put('bit',0);put('quotient',0)
  if get('ok'):
   n=get('cursor')
   if n:put('cursor',(n-1)//2);put('bit',(n-1)%2)
   else:put('ok',0)
 def contract(kind,args):
  if kind=='clear':put(args[0],0)
  elif kind=='move':a,b=args;put(a,get(a)+get(b));put(b,0)
  elif kind=='copy':a,b=args;put(a,get(b));put('copy_scratch',0)
  elif kind=='pop':pop()
  elif kind=='unary':
   out=args[0];put(out,0);put('unary_loop',0)
   while get('ok'):
    pop()
    if not get('ok') or not get('bit'):break
    put(out,get(out)+1)
  elif kind=='fixed2':
   out=args[0];put(out,0);pop()
   if get('ok'):put(out,2*get('bit'))
   pop()
   if get('ok'):put(out,get(out)+get('bit'))
  elif kind in ('lt','eq'):
   a,b=args;put('less',int(get(a)<get(b)) if kind=='lt' else int(get(a)==get(b)))
   for n in ('cmp_a','cmp_b','copy_scratch'):put(n,0)
  else:raise AssertionError(kind)
 def run(e):
  nonlocal remaining,calls,literal,accelerated
  remaining-=1;calls+=1
  if remaining<0:raise RuntimeError('fast register fuel exhausted')
  if isinstance(e,(tuple,list)):e=P.b.add_sequence(e)
  if isinstance(e,int):
   if contract_macros and e in P.macros:accelerated+=1;contract(*P.macros[e]);return 'normal',
   while True:
    left,right=P.b.sequences[e].seq;x=run(left)
    if x[0]=='break':return ('normal',) if x[1]==1 else ('break',x[1]-1)
    if x[0]!='normal':return x
    x=run(right)
    if x[0]=='continue':
     if x[1]==1:continue
     return 'continue',x[1]-1
    return x
  if e.startswith('_break.'):
   k=int(e.split('.')[1]);return ('normal',) if k==0 else ('break',k)
  if e.startswith('_continue.'):return 'continue',int(e.split('.')[1])
  if e=='halt':return 'halt',
  _,n,k=e.split('.');literal+=1
  if k=='inc':put(n,get(n)+1);return 'normal',
  assert k=='decnz'
  if get(n):put(n,get(n)-1);return 'normal',
  return 'break',1
 result=run(root)
 return {'control':result,'structured_calls':calls,'literal_register_operations':literal,'contracted_macro_calls':accelerated}
