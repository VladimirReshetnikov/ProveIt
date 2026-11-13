module
public import ExactCore
@[expose] public section
namespace PalomarPA.PA196
set_option maxRecDepth 100000
/-- Exact four-sequence-witness, six-register-step halting sentence schema. -/
def traceFormula (step : Formula Empty 6) : Sentence :=
  let body : Formula Empty 11 :=
    .and (nthAt (.bvar (boundIndex 5)) (.bvar (boundIndex 9)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 4)) (.bvar (boundIndex 8)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 3)) (.bvar (boundIndex 7)) (.bvar (boundIndex 6))) <|
    .and (nthAt (.bvar (boundIndex 2)) (.bvar (boundIndex 9)) (.add (.bvar (boundIndex 6)) .one)) <|
    .and (nthAt (.bvar (boundIndex 1)) (.bvar (boundIndex 8)) (.add (.bvar (boundIndex 6)) .one)) <|
    .and (nthAt (.bvar (boundIndex 0)) (.bvar (boundIndex 7)) (.add (.bvar (boundIndex 6)) .one)) <|
    step.rewrite (fun j => .bvar (boundIndex (5-j.val))) Empty.elim
  let timeBody : Formula Empty 5 :=
    .or (.nlt (.bvar (boundIndex 0)) (.bvar (boundIndex 4))) (.ex (.ex (.ex (.ex (.ex (.ex body))))))
  let startBody : Formula Empty 4 :=
    .and (nthAt .zero (.bvar (boundIndex 2)) .zero) <|
    .and (nthAt .zero (.bvar (boundIndex 1)) .zero) <|
    .and (nthAt .zero (.bvar (boundIndex 0)) .zero) <|
    .and (nthAt (.numeral 196) (.bvar (boundIndex 2)) (.bvar (boundIndex 3))) (.all timeBody)
  .ex (.ex (.ex (.ex startBody)))
abbrev RowSpec := Nat × Nat × Nat × Nat × Bool
/-- The 392 supplied transitions, with working states 0..195 and halt state 196. -/
def pa196Rows : List RowSpec := [
(0,0,1,1,true),(0,1,1,61,true),(1,0,1,82,true),(1,1,1,1,true),
(2,0,0,2,false),(2,1,1,3,false),(3,0,0,4,false),(3,1,1,3,false),
(4,0,0,6,false),(4,1,1,3,false),(5,0,1,7,true),(5,1,0,5,false),
(6,0,0,9,false),(6,1,1,3,false),(7,0,0,7,true),(7,1,0,10,true),
(8,0,0,14,true),(8,1,1,13,true),(9,0,0,15,false),(9,1,1,3,false),
(10,0,0,16,false),(10,1,0,10,true),(11,0,0,26,false),(11,1,1,18,true),
(12,0,0,19,true),(12,1,1,20,true),(13,0,0,79,false),(13,1,1,31,false),
(14,0,0,11,false),(14,1,0,22,true),(15,0,0,23,false),(15,1,1,3,false),
(16,0,1,2,false),(16,1,0,2,false),(17,0,0,24,true),(17,1,0,32,true),
(18,0,0,84,true),(18,1,0,95,false),(19,0,0,28,true),(19,1,1,29,true),
(20,0,0,30,true),(20,1,1,31,true),(21,0,0,24,true),(21,1,0,57,true),
(22,0,0,33,true),(22,1,1,22,true),(23,0,0,34,false),(23,1,1,3,false),
(24,0,0,35,false),(24,1,0,1,true),(25,0,0,36,true),(25,1,1,25,true),
(26,0,0,122,true),(26,1,1,41,true),(27,0,0,38,true),(27,1,0,39,false),
(28,0,0,40,true),(28,1,1,41,true),(29,0,0,42,true),(29,1,1,43,true),
(30,0,0,44,true),(30,1,1,45,true),(31,0,0,21,true),(31,1,1,46,true),
(32,0,0,47,true),(32,1,1,32,true),(33,0,0,32,true),(33,1,1,33,true),
(34,0,0,69,false),(34,1,1,3,false),(35,0,1,35,true),(35,1,1,2,false),
(36,0,0,49,true),(36,1,1,36,true),(37,0,0,28,true),(37,1,1,20,true),
(38,0,0,11,false),(38,1,0,36,true),(39,0,0,5,false),(39,1,1,51,false),
(40,0,0,24,true),(40,1,0,25,true),(41,0,0,13,true),(41,1,0,16,false),
(42,0,0,53,true),(42,1,1,54,true),(43,0,0,55,true),(43,1,1,56,true),
(44,0,0,24,true),(44,1,0,52,true),(45,0,0,58,true),(45,1,1,59,true),
(46,0,0,60,true),(46,1,0,16,false),(47,0,0,25,true),(47,1,1,47,true),
(48,0,0,35,false),(48,1,0,61,true),(49,0,0,16,true),(49,1,1,49,true),
(50,0,0,63,true),(50,1,1,64,true),(51,0,0,39,false),(51,1,1,51,false),
(52,0,0,22,true),(52,1,1,52,true),(53,0,0,11,false),(53,1,0,49,true),
(54,0,0,58,true),(54,1,0,16,false),(55,0,0,65,true),(55,1,1,66,true),
(56,0,0,59,true),(56,1,1,67,true),(57,0,0,52,true),(57,1,1,57,true),
(58,0,0,48,true),(58,1,0,25,true),(59,0,0,28,false),(59,1,1,68,false),
(60,0,0,102,false),(60,1,1,30,false),(61,0,0,0,true),(61,1,1,61,true),
(62,0,1,125,true),(62,1,1,51,false),(63,0,0,70,true),(63,1,1,196,true),
(64,0,0,126,false),(64,1,1,31,true),(65,0,0,40,true),(65,1,1,60,true),
(66,0,0,79,false),(66,1,1,71,true),(67,0,0,53,true),(67,1,1,72,false),
(68,0,0,73,true),(68,1,1,74,true),(69,0,0,69,true),(69,1,1,75,true),
(70,0,0,76,true),(70,1,1,77,true),(71,0,0,79,true),(71,1,1,110,false),
(72,0,0,98,false),(72,1,1,54,true),(73,0,0,48,true),(73,1,0,33,true),
(74,0,0,81,true),(74,1,0,41,false),(75,0,0,50,true),(75,1,1,132,true),
(76,0,0,130,true),(76,1,1,21,true),(77,0,0,101,true),(77,1,1,90,true),
(78,0,0,92,true),(78,1,1,93,true),(79,0,0,73,true),(79,1,1,72,true),
(80,0,0,91,true),(80,1,1,119,true),(81,0,0,95,true),(81,1,1,96,true),
(82,0,0,62,true),(82,1,0,1,true),(83,0,0,27,true),(83,1,1,97,true),
(84,0,0,89,true),(84,1,1,88,true),(85,0,1,99,false),(85,1,1,85,false),
(86,0,0,19,true),(86,1,1,100,true),(87,0,0,58,true),(87,1,1,58,true),
(88,0,0,117,true),(88,1,1,115,true),(89,0,0,26,false),(89,1,1,195,true),
(90,0,0,95,true),(90,1,0,131,false),(91,0,0,102,true),(91,1,1,103,true),
(92,0,0,67,true),(92,1,1,56,true),(93,0,0,55,true),(93,1,1,104,true),
(94,0,0,21,true),(94,1,1,105,true),(95,0,0,21,true),(95,1,0,10,false),
(96,0,0,59,true),(96,1,1,41,true),(97,0,0,106,true),(97,1,1,8,true),
(98,0,0,91,true),(98,1,1,107,true),(99,0,0,131,false),(99,1,0,85,false),
(100,0,0,108,true),(100,1,1,94,true),(101,0,0,109,false),(101,1,0,2,false),
(102,0,0,38,true),(102,1,1,68,true),(103,0,0,59,true),(103,1,1,110,true),
(104,0,0,59,true),(104,1,1,111,true),(105,0,0,66,true),(105,1,0,16,false),
(106,0,0,14,true),(106,1,1,110,true),(107,0,0,21,true),(107,1,1,112,true),
(108,0,0,113,true),(108,1,1,20,false),(109,0,0,30,true),(109,1,1,65,true),
(110,0,0,38,true),(110,1,1,108,false),(111,0,0,121,true),(111,1,0,16,false),
(112,0,0,114,true),(112,1,0,16,false),(113,0,0,24,true),(113,1,0,47,true),
(114,0,0,48,true),(114,1,0,32,true),(115,0,0,70,true),(115,1,1,86,true),
(116,0,0,19,true),(116,1,1,118,true),(117,0,0,126,true),(117,1,1,28,true),
(118,0,0,122,true),(118,1,1,107,true),(119,0,0,94,true),(119,1,1,86,true),
(120,0,0,83,true),(120,1,1,98,true),(121,0,0,87,true),(121,1,1,87,true),
(122,0,0,17,true),(122,1,1,109,false),(123,0,0,70,true),(123,1,1,101,true),
(124,0,0,96,true),(124,1,1,108,true),(125,0,1,39,false),(125,1,1,99,false),
(126,0,0,80,true),(126,1,1,78,true),(127,0,0,120,true),(127,1,1,133,true),
(128,0,0,124,true),(128,1,1,123,true),(129,0,0,123,true),(129,1,1,128,true),
(130,0,0,44,true),(130,1,1,90,true),(131,0,0,5,false),(131,1,0,131,false),
(132,0,0,127,true),(132,1,1,59,true),(133,0,0,11,true),(133,1,1,37,true),
(134,0,0,78,true),(134,1,1,58,true),(135,0,0,134,true),(135,1,1,58,true),
(136,0,0,86,true),(136,1,1,135,true),(137,0,0,12,true),(137,1,1,136,true),
(138,0,0,168,false),(138,1,1,140,true),(139,0,0,116,true),(139,1,1,140,true),
(140,0,0,158,false),(140,1,1,78,true),(141,0,0,140,true),(141,1,1,137,true),
(142,0,0,139,true),(142,1,1,141,true),(143,0,0,138,true),(143,1,1,142,true),
(144,0,0,19,true),(144,1,1,160,true),(145,0,0,144,true),(145,1,1,136,true),
(146,0,0,145,true),(146,1,1,144,true),(147,0,0,143,true),(147,1,1,138,true),
(148,0,0,126,true),(148,1,1,147,true),(149,0,0,116,true),(149,1,1,135,true),
(150,0,0,12,true),(150,1,1,149,true),(151,0,0,136,true),(151,1,1,137,true),
(152,0,0,149,true),(152,1,1,78,true),(153,0,0,86,true),(153,1,1,134,true),
(154,0,0,152,true),(154,1,1,183,true),(155,0,0,150,true),(155,1,1,174,true),
(156,0,0,148,true),(156,1,1,155,true),(157,0,0,78,true),(157,1,1,156,true),
(158,0,0,157,true),(158,1,1,150,true),(159,0,0,116,true),(159,1,1,153,true),
(160,0,0,58,true),(160,1,1,185,false),(161,0,0,141,true),(161,1,1,58,true),
(162,0,0,160,true),(162,1,1,161,true),(163,0,0,139,true),(163,1,1,162,true),
(164,0,0,162,true),(164,1,1,163,true),(165,0,0,158,true),(165,1,1,164,true),
(166,0,0,86,true),(166,1,1,165,true),(167,0,0,146,true),(167,1,1,159,true),
(168,0,0,166,true),(168,1,1,167,true),(169,0,0,12,true),(169,1,1,168,true),
(170,0,0,58,true),(170,1,1,139,true),(171,0,0,151,true),(171,1,1,161,true),
(172,0,0,170,true),(172,1,1,171,true),(173,0,0,172,true),(173,1,1,137,true),
(174,0,0,172,false),(174,1,1,154,true),(175,0,0,174,true),(175,1,1,183,true),
(176,0,0,173,true),(176,1,1,175,true),(177,0,0,176,true),(177,1,1,154,true),
(178,0,0,169,true),(178,1,1,177,true),(179,0,0,142,false),(179,1,1,159,true),
(180,0,0,179,true),(180,1,1,179,true),(181,0,0,178,true),(181,1,1,180,true),
(182,0,0,64,true),(182,1,1,181,true),(183,0,0,158,false),(183,1,1,167,false),
(184,0,0,183,true),(184,1,1,78,true),(185,0,0,179,true),(185,1,1,184,true),
(186,0,0,145,true),(186,1,1,185,true),(187,0,0,184,true),(187,1,1,186,true),
(188,0,0,116,true),(188,1,1,187,true),(189,0,0,183,true),(189,1,1,122,true),
(190,0,0,152,true),(190,1,1,189,true),(191,0,0,188,true),(191,1,1,190,true),
(192,0,0,182,true),(192,1,1,191,true),(193,0,0,129,true),(193,1,0,131,false),
(194,0,0,192,true),(194,1,1,193,true),(195,0,0,137,true),(195,1,1,194,true)]
def rowOfSpec (r : RowSpec) : Formula Empty 6 := rowFormula r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
def disjoinRows : List RowSpec → Formula Empty 6
  | [] => .bot | r::rs => .or (rowOfSpec r) (disjoinRows rs)

def pa196Step : Formula Empty 6 := disjoinRows pa196Rows
def pa196Halting : Sentence := traceFormula pa196Step
def pa196Nonhalting : Sentence := pa196Halting.neg
theorem pa196Rows_count : pa196Rows.length=392 := by decide
end PalomarPA.PA196
