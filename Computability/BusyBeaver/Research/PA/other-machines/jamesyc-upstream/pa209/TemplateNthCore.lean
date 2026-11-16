module
public import MappingTemplateCore
public import SeqTemplateCore
public import PrimitiveData
@[expose] public section
namespace PalomarPA.ConstructedNth
/-- Every parameter of the generic HFS templates is instantiated by explicit
arithmetic syntax. No semantic predicate or opaque axiom is introduced. -/
def mapping : Formula Empty 1 := mappingTemplate PrimitiveData.domain PrimitiveData.member PrimitiveData.edge
def seq : Formula Empty 1 := seqTemplate mapping PrimitiveData.domain PrimitiveData.under
def length : Formula Empty 2 := seqLengthTemplate seq PrimitiveData.domain PrimitiveData.under
/-- PR edge arguments are (index,sequence,value), unlike memRel's
(sequence,index,value). The swap is explicit. -/
def edge : Formula Empty 3 := prSub3 PrimitiveData.edge (.bvar (boundIndex 1)) (.bvar (boundIndex 0)) (.bvar (boundIndex 2))
def succ : Formula Empty 3 := fixSuccTemplate PrimitiveData.member PrimitiveData.core PrimitiveData.core
def cseq : Formula Empty 1 := prCSeqTemplate fixZeroTemplate seq succ edge length
def result : Formula Empty 2 := prResultTemplate cseq edge
def graph : Formula Empty 1 := fixPointTemplate PrimitiveData.member result
def formula : Formula Empty 3 := nthTemplate PrimitiveData.pair3 graph
end PalomarPA.ConstructedNth
