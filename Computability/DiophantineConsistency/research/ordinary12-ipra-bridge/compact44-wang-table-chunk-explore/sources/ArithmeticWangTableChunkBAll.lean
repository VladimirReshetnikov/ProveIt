import DiophantineConsistency.ArithmeticWangTableChunkCover
import DiophantineConsistency.ArithmeticWangTableChunkB00
import DiophantineConsistency.ArithmeticWangTableChunkB01
import DiophantineConsistency.ArithmeticWangTableChunkB02
import DiophantineConsistency.ArithmeticWangTableChunkB03
import DiophantineConsistency.ArithmeticWangTableChunkB04
import DiophantineConsistency.ArithmeticWangTableChunkB05
import DiophantineConsistency.ArithmeticWangTableChunkB06
import DiophantineConsistency.ArithmeticWangTableChunkB07
import DiophantineConsistency.ArithmeticWangTableChunkB08
import DiophantineConsistency.ArithmeticWangTableChunkB09
import DiophantineConsistency.ArithmeticWangTableChunkB10
import DiophantineConsistency.ArithmeticWangTableChunkB11
import DiophantineConsistency.ArithmeticWangTableChunkB12
import DiophantineConsistency.ArithmeticWangTableChunkB13
import DiophantineConsistency.ArithmeticWangTableChunkB14
import DiophantineConsistency.ArithmeticWangTableChunkB15
import DiophantineConsistency.ArithmeticWangTableChunkB16
import DiophantineConsistency.ArithmeticWangTableChunkB17
import DiophantineConsistency.ArithmeticWangTableChunkB18
import DiophantineConsistency.ArithmeticWangTableChunkB19
import DiophantineConsistency.ArithmeticWangTableChunkB20
import DiophantineConsistency.ArithmeticWangTableChunkB21
import DiophantineConsistency.ArithmeticWangTableChunkB22
import DiophantineConsistency.ArithmeticWangTableChunkB23
import DiophantineConsistency.ArithmeticWangTableChunkB24
import DiophantineConsistency.ArithmeticWangTableChunkB25
import DiophantineConsistency.ArithmeticWangTableChunkB26
import DiophantineConsistency.ArithmeticWangTableChunkB27
import DiophantineConsistency.ArithmeticWangTableChunkB28
import DiophantineConsistency.ArithmeticWangTableChunkB29
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodB : ∀ row ∈ orderedRows, GoodB row.2 := by
  have h29 : ∀ row ∈ orderedRows.drop 928, GoodB row.2 := rows_goodB_chunk29
  have h28 : ∀ row ∈ orderedRows.drop 896, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 896) 32
    · exact rows_goodB_chunk28
    · simpa only [List.drop_drop] using h29
  have h27 : ∀ row ∈ orderedRows.drop 864, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 864) 32
    · exact rows_goodB_chunk27
    · simpa only [List.drop_drop] using h28
  have h26 : ∀ row ∈ orderedRows.drop 832, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 832) 32
    · exact rows_goodB_chunk26
    · simpa only [List.drop_drop] using h27
  have h25 : ∀ row ∈ orderedRows.drop 800, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 800) 32
    · exact rows_goodB_chunk25
    · simpa only [List.drop_drop] using h26
  have h24 : ∀ row ∈ orderedRows.drop 768, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 768) 32
    · exact rows_goodB_chunk24
    · simpa only [List.drop_drop] using h25
  have h23 : ∀ row ∈ orderedRows.drop 736, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 736) 32
    · exact rows_goodB_chunk23
    · simpa only [List.drop_drop] using h24
  have h22 : ∀ row ∈ orderedRows.drop 704, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 704) 32
    · exact rows_goodB_chunk22
    · simpa only [List.drop_drop] using h23
  have h21 : ∀ row ∈ orderedRows.drop 672, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 672) 32
    · exact rows_goodB_chunk21
    · simpa only [List.drop_drop] using h22
  have h20 : ∀ row ∈ orderedRows.drop 640, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 640) 32
    · exact rows_goodB_chunk20
    · simpa only [List.drop_drop] using h21
  have h19 : ∀ row ∈ orderedRows.drop 608, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 608) 32
    · exact rows_goodB_chunk19
    · simpa only [List.drop_drop] using h20
  have h18 : ∀ row ∈ orderedRows.drop 576, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 576) 32
    · exact rows_goodB_chunk18
    · simpa only [List.drop_drop] using h19
  have h17 : ∀ row ∈ orderedRows.drop 544, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 544) 32
    · exact rows_goodB_chunk17
    · simpa only [List.drop_drop] using h18
  have h16 : ∀ row ∈ orderedRows.drop 512, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 512) 32
    · exact rows_goodB_chunk16
    · simpa only [List.drop_drop] using h17
  have h15 : ∀ row ∈ orderedRows.drop 480, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 480) 32
    · exact rows_goodB_chunk15
    · simpa only [List.drop_drop] using h16
  have h14 : ∀ row ∈ orderedRows.drop 448, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 448) 32
    · exact rows_goodB_chunk14
    · simpa only [List.drop_drop] using h15
  have h13 : ∀ row ∈ orderedRows.drop 416, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 416) 32
    · exact rows_goodB_chunk13
    · simpa only [List.drop_drop] using h14
  have h12 : ∀ row ∈ orderedRows.drop 384, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 384) 32
    · exact rows_goodB_chunk12
    · simpa only [List.drop_drop] using h13
  have h11 : ∀ row ∈ orderedRows.drop 352, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 352) 32
    · exact rows_goodB_chunk11
    · simpa only [List.drop_drop] using h12
  have h10 : ∀ row ∈ orderedRows.drop 320, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 320) 32
    · exact rows_goodB_chunk10
    · simpa only [List.drop_drop] using h11
  have h9 : ∀ row ∈ orderedRows.drop 288, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 288) 32
    · exact rows_goodB_chunk09
    · simpa only [List.drop_drop] using h10
  have h8 : ∀ row ∈ orderedRows.drop 256, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 256) 32
    · exact rows_goodB_chunk08
    · simpa only [List.drop_drop] using h9
  have h7 : ∀ row ∈ orderedRows.drop 224, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 224) 32
    · exact rows_goodB_chunk07
    · simpa only [List.drop_drop] using h8
  have h6 : ∀ row ∈ orderedRows.drop 192, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 192) 32
    · exact rows_goodB_chunk06
    · simpa only [List.drop_drop] using h7
  have h5 : ∀ row ∈ orderedRows.drop 160, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 160) 32
    · exact rows_goodB_chunk05
    · simpa only [List.drop_drop] using h6
  have h4 : ∀ row ∈ orderedRows.drop 128, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 128) 32
    · exact rows_goodB_chunk04
    · simpa only [List.drop_drop] using h5
  have h3 : ∀ row ∈ orderedRows.drop 96, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 96) 32
    · exact rows_goodB_chunk03
    · simpa only [List.drop_drop] using h4
  have h2 : ∀ row ∈ orderedRows.drop 64, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 64) 32
    · exact rows_goodB_chunk02
    · simpa only [List.drop_drop] using h3
  have h1 : ∀ row ∈ orderedRows.drop 32, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 32) 32
    · exact rows_goodB_chunk01
    · simpa only [List.drop_drop] using h2
  have h0 : ∀ row ∈ orderedRows.drop 0, GoodB row.2 := by
    apply chunk_cover (fun row => GoodB row.2) (orderedRows.drop 0) 32
    · exact rows_goodB_chunk00
    · simpa only [List.drop_drop] using h1
  simpa only [List.drop_zero] using h0
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodB
end DiophantineConsistency.ArithmeticWangTable
