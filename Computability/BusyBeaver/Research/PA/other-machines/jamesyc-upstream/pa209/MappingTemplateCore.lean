module
public import PRTemplateCore
@[expose] public section
namespace PalomarPA
/-- HFS mapping schema. Edge arguments are (relation,input,output). -/
def mappingTemplate (domain member : Formula Empty 2) (edge : Formula Empty 3) : Formula Empty 1 :=
 let unique : Formula Empty 4 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 4)))
  (.or (prSub3 edge (.bvar (boundIndex 4)) (.bvar (boundIndex 2)) (.bvar (boundIndex 0))).neg (.eq (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))))
 let value : Formula Empty 3 := .ex (.and (.lt (.bvar (boundIndex 0)) (.bvar (boundIndex 3)))
  (.and (prSub3 edge (.bvar (boundIndex 3)) (.bvar (boundIndex 1)) (.bvar (boundIndex 0))) unique))
 let total : Formula Empty 2 := .all (.or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 1)))
  (.or (prSub2 member (.bvar (boundIndex 0)) (.bvar (boundIndex 1))).neg value))
 .ex (.and (.lt (.bvar (boundIndex 0)) (.add (.mul (.add .one .one) (.bvar (boundIndex 1))) .one))
  (.and (prSub2 domain (.bvar (boundIndex 0)) (.bvar (boundIndex 1))) total))
end PalomarPA
