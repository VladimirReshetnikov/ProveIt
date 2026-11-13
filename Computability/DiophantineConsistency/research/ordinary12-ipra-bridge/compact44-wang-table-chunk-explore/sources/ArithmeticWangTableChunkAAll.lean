import DiophantineConsistency.ArithmeticWangTableChunkCover
import DiophantineConsistency.ArithmeticWangTableChunkA00
import DiophantineConsistency.ArithmeticWangTableChunkA01
import DiophantineConsistency.ArithmeticWangTableChunkA02
import DiophantineConsistency.ArithmeticWangTableChunkA03
import DiophantineConsistency.ArithmeticWangTableChunkA04
import DiophantineConsistency.ArithmeticWangTableChunkA05
import DiophantineConsistency.ArithmeticWangTableChunkA06
import DiophantineConsistency.ArithmeticWangTableChunkA07
import DiophantineConsistency.ArithmeticWangTableChunkA08
import DiophantineConsistency.ArithmeticWangTableChunkA09
import DiophantineConsistency.ArithmeticWangTableChunkA10
import DiophantineConsistency.ArithmeticWangTableChunkA11
import DiophantineConsistency.ArithmeticWangTableChunkA12
import DiophantineConsistency.ArithmeticWangTableChunkA13
import DiophantineConsistency.ArithmeticWangTableChunkA14
import DiophantineConsistency.ArithmeticWangTableChunkA15
import DiophantineConsistency.ArithmeticWangTableChunkA16
import DiophantineConsistency.ArithmeticWangTableChunkA17
import DiophantineConsistency.ArithmeticWangTableChunkA18
import DiophantineConsistency.ArithmeticWangTableChunkA19
import DiophantineConsistency.ArithmeticWangTableChunkA20
import DiophantineConsistency.ArithmeticWangTableChunkA21
import DiophantineConsistency.ArithmeticWangTableChunkA22
import DiophantineConsistency.ArithmeticWangTableChunkA23
import DiophantineConsistency.ArithmeticWangTableChunkA24
import DiophantineConsistency.ArithmeticWangTableChunkA25
import DiophantineConsistency.ArithmeticWangTableChunkA26
import DiophantineConsistency.ArithmeticWangTableChunkA27
import DiophantineConsistency.ArithmeticWangTableChunkA28
import DiophantineConsistency.ArithmeticWangTableChunkA29
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodA : ∀ row ∈ orderedRows, GoodA row.2 := by
  have h29 : ∀ row ∈ orderedRows.drop 928, GoodA row.2 := rows_goodA_chunk29
  have h28 : ∀ row ∈ orderedRows.drop 896, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 896) 32
    · exact rows_goodA_chunk28
    · simpa only [List.drop_drop] using h29
  have h27 : ∀ row ∈ orderedRows.drop 864, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 864) 32
    · exact rows_goodA_chunk27
    · simpa only [List.drop_drop] using h28
  have h26 : ∀ row ∈ orderedRows.drop 832, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 832) 32
    · exact rows_goodA_chunk26
    · simpa only [List.drop_drop] using h27
  have h25 : ∀ row ∈ orderedRows.drop 800, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 800) 32
    · exact rows_goodA_chunk25
    · simpa only [List.drop_drop] using h26
  have h24 : ∀ row ∈ orderedRows.drop 768, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 768) 32
    · exact rows_goodA_chunk24
    · simpa only [List.drop_drop] using h25
  have h23 : ∀ row ∈ orderedRows.drop 736, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 736) 32
    · exact rows_goodA_chunk23
    · simpa only [List.drop_drop] using h24
  have h22 : ∀ row ∈ orderedRows.drop 704, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 704) 32
    · exact rows_goodA_chunk22
    · simpa only [List.drop_drop] using h23
  have h21 : ∀ row ∈ orderedRows.drop 672, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 672) 32
    · exact rows_goodA_chunk21
    · simpa only [List.drop_drop] using h22
  have h20 : ∀ row ∈ orderedRows.drop 640, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 640) 32
    · exact rows_goodA_chunk20
    · simpa only [List.drop_drop] using h21
  have h19 : ∀ row ∈ orderedRows.drop 608, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 608) 32
    · exact rows_goodA_chunk19
    · simpa only [List.drop_drop] using h20
  have h18 : ∀ row ∈ orderedRows.drop 576, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 576) 32
    · exact rows_goodA_chunk18
    · simpa only [List.drop_drop] using h19
  have h17 : ∀ row ∈ orderedRows.drop 544, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 544) 32
    · exact rows_goodA_chunk17
    · simpa only [List.drop_drop] using h18
  have h16 : ∀ row ∈ orderedRows.drop 512, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 512) 32
    · exact rows_goodA_chunk16
    · simpa only [List.drop_drop] using h17
  have h15 : ∀ row ∈ orderedRows.drop 480, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 480) 32
    · exact rows_goodA_chunk15
    · simpa only [List.drop_drop] using h16
  have h14 : ∀ row ∈ orderedRows.drop 448, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 448) 32
    · exact rows_goodA_chunk14
    · simpa only [List.drop_drop] using h15
  have h13 : ∀ row ∈ orderedRows.drop 416, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 416) 32
    · exact rows_goodA_chunk13
    · simpa only [List.drop_drop] using h14
  have h12 : ∀ row ∈ orderedRows.drop 384, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 384) 32
    · exact rows_goodA_chunk12
    · simpa only [List.drop_drop] using h13
  have h11 : ∀ row ∈ orderedRows.drop 352, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 352) 32
    · exact rows_goodA_chunk11
    · simpa only [List.drop_drop] using h12
  have h10 : ∀ row ∈ orderedRows.drop 320, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 320) 32
    · exact rows_goodA_chunk10
    · simpa only [List.drop_drop] using h11
  have h9 : ∀ row ∈ orderedRows.drop 288, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 288) 32
    · exact rows_goodA_chunk09
    · simpa only [List.drop_drop] using h10
  have h8 : ∀ row ∈ orderedRows.drop 256, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 256) 32
    · exact rows_goodA_chunk08
    · simpa only [List.drop_drop] using h9
  have h7 : ∀ row ∈ orderedRows.drop 224, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 224) 32
    · exact rows_goodA_chunk07
    · simpa only [List.drop_drop] using h8
  have h6 : ∀ row ∈ orderedRows.drop 192, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 192) 32
    · exact rows_goodA_chunk06
    · simpa only [List.drop_drop] using h7
  have h5 : ∀ row ∈ orderedRows.drop 160, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 160) 32
    · exact rows_goodA_chunk05
    · simpa only [List.drop_drop] using h6
  have h4 : ∀ row ∈ orderedRows.drop 128, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 128) 32
    · exact rows_goodA_chunk04
    · simpa only [List.drop_drop] using h5
  have h3 : ∀ row ∈ orderedRows.drop 96, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 96) 32
    · exact rows_goodA_chunk03
    · simpa only [List.drop_drop] using h4
  have h2 : ∀ row ∈ orderedRows.drop 64, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 64) 32
    · exact rows_goodA_chunk02
    · simpa only [List.drop_drop] using h3
  have h1 : ∀ row ∈ orderedRows.drop 32, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 32) 32
    · exact rows_goodA_chunk01
    · simpa only [List.drop_drop] using h2
  have h0 : ∀ row ∈ orderedRows.drop 0, GoodA row.2 := by
    apply chunk_cover (fun row => GoodA row.2) (orderedRows.drop 0) 32
    · exact rows_goodA_chunk00
    · simpa only [List.drop_drop] using h1
  simpa only [List.drop_zero] using h0
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodA
end DiophantineConsistency.ArithmeticWangTable
