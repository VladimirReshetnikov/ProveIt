module
public import PRTemplateCore
@[expose] public section
namespace PalomarPA
/-- Explicit bounded sequence predicate, parameterized by its lower-level graphs. -/
def seqTemplate (mapping : Formula Empty 1) (domain under : Formula Empty 2) : Formula Empty 1 :=
 .and (prSub1 mapping (.bvar (boundIndex 0)))
 (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) .one))
  (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
   (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (prSub2 under (.bvar (boundIndex 0)) (.bvar (boundIndex 1))))))))
/-- Explicit length graph; invalid sequence inputs return zero. -/
def seqLengthTemplate (seq : Formula Empty 1) (domain under : Formula Empty 2) : Formula Empty 2 :=
 let valid := prSub1 seq (.bvar (boundIndex 1))
 .and (.or valid.neg
  (.ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 2))) .one))
   (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 2))) (prSub2 under (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))))
  (.or valid.neg.neg (.eq (.bvar (boundIndex 0)) .zero))
end PalomarPA
