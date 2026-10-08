"""Optional regular-language multiplicity domains, with exact integer cardinality.

The implementation masks all ports outside the accepted language, runs the full-
word solver, and subtracts the homology of the known uncoupled complementary base.
No signed saturation is used: this subtraction is performed on exact integers.
"""
from __future__ import annotations
from dataclasses import dataclass
from .automata import Register
from .complexes import PortComplex,TemplateBlock,analyze
from . import gf2


@dataclass(frozen=True)
class Language:
    widths: tuple[int,...]
    transitions: tuple[tuple[tuple[int,...],tuple[int,...]],...]
    initial: int
    accepting: tuple[int,...]

    def __post_init__(self):
        if not self.widths or any(type(b) is not int or b<1 for b in self.widths):
            raise ValueError('language widths must be positive integers')
        if type(self.initial) is not int or not 0<=self.initial<self.widths[0]:
            raise ValueError('invalid language initial state')
        if len(self.transitions)!=len(self.widths)-1:
            raise ValueError('invalid language transition count')
        for j,pair in enumerate(self.transitions):
            if len(pair)!=2:raise ValueError('binary language needs two transitions')
            for delta in pair:
                if len(delta)!=self.widths[j] or any(type(s) is not int or not 0<=s<self.widths[j+1] for s in delta):
                    raise ValueError('invalid deterministic language transition')
        if len(set(self.accepting))!=len(self.accepting) or any(type(s) is not int or not 0<=s<self.widths[-1] for s in self.accepting):
            raise ValueError('invalid accepting states')

    @property
    def length(self):return len(self.transitions)

    def count(self) -> int:
        counts=[0]*self.widths[0];counts[self.initial]=1
        for j,pair in enumerate(self.transitions):
            new=[0]*self.widths[j+1]
            for delta in pair:
                for state,value in enumerate(counts):new[delta[state]]+=value
            counts=new
        return sum(counts[s] for s in self.accepting)

    def accepts(self,word) -> bool:
        if len(word)!=self.length or any(type(x) is not int or x not in (0,1) for x in word):
            raise ValueError('invalid language word')
        state=self.initial
        for x,pair in zip(word,self.transitions):state=pair[x][state]
        return state in self.accepting

    def to_dict(self):
        return {'widths':list(self.widths),'transitions':[[list(a),list(b)] for a,b in self.transitions],
                'initial':self.initial,'accepting':list(self.accepting)}

    @classmethod
    def from_dict(cls,obj):
        if not isinstance(obj,dict):raise ValueError('language JSON object required')
        return cls(tuple(obj['widths']),tuple((tuple(a),tuple(b)) for a,b in obj['transitions']),
                   obj['initial'],tuple(obj['accepting']))


def fixed_weight(length: int,weight: int) -> Language:
    if type(length) is not int or type(weight) is not int or not 0<=weight<=length:
        raise ValueError('fixed weight requires 0 <= weight <= length')
    width=weight+2;dead=weight+1
    zero=tuple(range(width));one=tuple(min(i+1,dead) for i in range(width))
    return Language((width,)*(length+1),((zero,one),)*length,0,(weight,))


def mask_register(reg: Register,language: Language) -> Register:
    if reg.length!=language.length:raise ValueError('language/register length mismatch')
    widths=tuple(a*b for a,b in zip(reg.widths,language.widths))
    initial=sum(1 << (i*language.widths[0]+language.initial) for i in gf2.bits(reg.initial))
    transitions=[]
    for j,(pair,deltas) in enumerate(zip(reg.transitions,language.transitions)):
        newpair=[]
        for matrix,delta in zip(pair,deltas):
            rows=[]
            for i,row in enumerate(matrix):
                for state in range(language.widths[j]):
                    rows.append(sum(1 << (k*language.widths[j+1]+delta[state]) for k in gf2.bits(row)))
            newpair.append(tuple(rows))
        transitions.append(tuple(newpair))
    outputs=tuple(row if state in language.accepting else 0
                  for row in reg.outputs for state in range(language.widths[-1]))
    return Register(widths,tuple(transitions),initial,outputs,reg.output_count)


def analyze_restricted(c: PortComplex,languages: tuple[Language|None,...]) -> dict:
    if len(languages)!=len(c.blocks):raise ValueError('one language required per block')
    blocks=[];counts=[]
    for b,language in zip(c.blocks,languages):
        reg=b.register if language is None else mask_register(b.register,language)
        blocks.append(TemplateBlock(b.differential,b.degrees,reg))
        counts.append((1 << reg.length) if language is None else language.count())
    masked=PortComplex(tuple(blocks),c.port_degrees)
    result=analyze(masked)
    removed_dimension=removed_rank=0
    for b,count,summary in zip(c.blocks,counts,result['register_summaries']):
        removed=(1 << b.register.length)-count
        removed_dimension+=b.size*removed
        removed_rank+=summary['template_rank']*removed
    removed_beta=removed_dimension-2*removed_rank
    for key in ('base_differential_rank','differential_rank'):result[key]-=removed_rank
    for key in ('base_homology_dimension','homology_dimension'):result[key]-=removed_beta
    result['dimension']-=removed_dimension
    result['rank_two']=result['homology_dimension']==2
    result['rank_two_obstruction_from_budget']=result['base_homology_dimension']>2*c.ports+2
    result['base_dimension_safe_cap']=min(result['base_homology_dimension'],2*c.ports+3)
    result.update({'format':'portkh-restricted-certificate-1','accepted_word_counts':counts,
                   'removed_uncoupled_dimension':removed_dimension,
                   'removed_uncoupled_homology_dimension':removed_beta,
                   'scope':'Exact language-restricted binary chain rank; no knot provenance inferred.'})
    beta=result['homology_dimension'];n=result['dimension'];rank=result['differential_rank']
    if n-2*rank != beta or not 0<=beta<=n or rank<0:
        raise ArithmeticError('inconsistent restricted homology dimension')
    return result
