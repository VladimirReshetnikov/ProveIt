import DiophantineConsistency.ArithmeticWangTableChunkCover
import DiophantineConsistency.ArithmeticWangTableChunkC00
import DiophantineConsistency.ArithmeticWangTableChunkC01
import DiophantineConsistency.ArithmeticWangTableChunkC02
import DiophantineConsistency.ArithmeticWangTableChunkC03
import DiophantineConsistency.ArithmeticWangTableChunkC04
import DiophantineConsistency.ArithmeticWangTableChunkC05
import DiophantineConsistency.ArithmeticWangTableChunkC06
import DiophantineConsistency.ArithmeticWangTableChunkC07
import DiophantineConsistency.ArithmeticWangTableChunkC08
import DiophantineConsistency.ArithmeticWangTableChunkC09
import DiophantineConsistency.ArithmeticWangTableChunkC10
import DiophantineConsistency.ArithmeticWangTableChunkC11
import DiophantineConsistency.ArithmeticWangTableChunkC12
import DiophantineConsistency.ArithmeticWangTableChunkC13
import DiophantineConsistency.ArithmeticWangTableChunkC14
import DiophantineConsistency.ArithmeticWangTableChunkC15
import DiophantineConsistency.ArithmeticWangTableChunkC16
import DiophantineConsistency.ArithmeticWangTableChunkC17
import DiophantineConsistency.ArithmeticWangTableChunkC18
import DiophantineConsistency.ArithmeticWangTableChunkC19
import DiophantineConsistency.ArithmeticWangTableChunkC20
import DiophantineConsistency.ArithmeticWangTableChunkC21
import DiophantineConsistency.ArithmeticWangTableChunkC22
import DiophantineConsistency.ArithmeticWangTableChunkC23
import DiophantineConsistency.ArithmeticWangTableChunkC24
import DiophantineConsistency.ArithmeticWangTableChunkC25
import DiophantineConsistency.ArithmeticWangTableChunkC26
import DiophantineConsistency.ArithmeticWangTableChunkC27
import DiophantineConsistency.ArithmeticWangTableChunkC28
import DiophantineConsistency.ArithmeticWangTableChunkC29
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodC : ∀ row ∈ orderedRows, GoodC row.2 := by
  have h29 : ∀ row ∈ orderedRows.drop 928, GoodC row.2 := rows_goodC_chunk29
  have h28 : ∀ row ∈ orderedRows.drop 896, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 896) 32
    · exact rows_goodC_chunk28
    · simpa only [List.drop_drop] using h29
  have h27 : ∀ row ∈ orderedRows.drop 864, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 864) 32
    · exact rows_goodC_chunk27
    · simpa only [List.drop_drop] using h28
  have h26 : ∀ row ∈ orderedRows.drop 832, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 832) 32
    · exact rows_goodC_chunk26
    · simpa only [List.drop_drop] using h27
  have h25 : ∀ row ∈ orderedRows.drop 800, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 800) 32
    · exact rows_goodC_chunk25
    · simpa only [List.drop_drop] using h26
  have h24 : ∀ row ∈ orderedRows.drop 768, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 768) 32
    · exact rows_goodC_chunk24
    · simpa only [List.drop_drop] using h25
  have h23 : ∀ row ∈ orderedRows.drop 736, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 736) 32
    · exact rows_goodC_chunk23
    · simpa only [List.drop_drop] using h24
  have h22 : ∀ row ∈ orderedRows.drop 704, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 704) 32
    · exact rows_goodC_chunk22
    · simpa only [List.drop_drop] using h23
  have h21 : ∀ row ∈ orderedRows.drop 672, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 672) 32
    · exact rows_goodC_chunk21
    · simpa only [List.drop_drop] using h22
  have h20 : ∀ row ∈ orderedRows.drop 640, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 640) 32
    · exact rows_goodC_chunk20
    · simpa only [List.drop_drop] using h21
  have h19 : ∀ row ∈ orderedRows.drop 608, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 608) 32
    · exact rows_goodC_chunk19
    · simpa only [List.drop_drop] using h20
  have h18 : ∀ row ∈ orderedRows.drop 576, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 576) 32
    · exact rows_goodC_chunk18
    · simpa only [List.drop_drop] using h19
  have h17 : ∀ row ∈ orderedRows.drop 544, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 544) 32
    · exact rows_goodC_chunk17
    · simpa only [List.drop_drop] using h18
  have h16 : ∀ row ∈ orderedRows.drop 512, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 512) 32
    · exact rows_goodC_chunk16
    · simpa only [List.drop_drop] using h17
  have h15 : ∀ row ∈ orderedRows.drop 480, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 480) 32
    · exact rows_goodC_chunk15
    · simpa only [List.drop_drop] using h16
  have h14 : ∀ row ∈ orderedRows.drop 448, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 448) 32
    · exact rows_goodC_chunk14
    · simpa only [List.drop_drop] using h15
  have h13 : ∀ row ∈ orderedRows.drop 416, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 416) 32
    · exact rows_goodC_chunk13
    · simpa only [List.drop_drop] using h14
  have h12 : ∀ row ∈ orderedRows.drop 384, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 384) 32
    · exact rows_goodC_chunk12
    · simpa only [List.drop_drop] using h13
  have h11 : ∀ row ∈ orderedRows.drop 352, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 352) 32
    · exact rows_goodC_chunk11
    · simpa only [List.drop_drop] using h12
  have h10 : ∀ row ∈ orderedRows.drop 320, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 320) 32
    · exact rows_goodC_chunk10
    · simpa only [List.drop_drop] using h11
  have h9 : ∀ row ∈ orderedRows.drop 288, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 288) 32
    · exact rows_goodC_chunk09
    · simpa only [List.drop_drop] using h10
  have h8 : ∀ row ∈ orderedRows.drop 256, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 256) 32
    · exact rows_goodC_chunk08
    · simpa only [List.drop_drop] using h9
  have h7 : ∀ row ∈ orderedRows.drop 224, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 224) 32
    · exact rows_goodC_chunk07
    · simpa only [List.drop_drop] using h8
  have h6 : ∀ row ∈ orderedRows.drop 192, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 192) 32
    · exact rows_goodC_chunk06
    · simpa only [List.drop_drop] using h7
  have h5 : ∀ row ∈ orderedRows.drop 160, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 160) 32
    · exact rows_goodC_chunk05
    · simpa only [List.drop_drop] using h6
  have h4 : ∀ row ∈ orderedRows.drop 128, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 128) 32
    · exact rows_goodC_chunk04
    · simpa only [List.drop_drop] using h5
  have h3 : ∀ row ∈ orderedRows.drop 96, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 96) 32
    · exact rows_goodC_chunk03
    · simpa only [List.drop_drop] using h4
  have h2 : ∀ row ∈ orderedRows.drop 64, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 64) 32
    · exact rows_goodC_chunk02
    · simpa only [List.drop_drop] using h3
  have h1 : ∀ row ∈ orderedRows.drop 32, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 32) 32
    · exact rows_goodC_chunk01
    · simpa only [List.drop_drop] using h2
  have h0 : ∀ row ∈ orderedRows.drop 0, GoodC row.2 := by
    apply chunk_cover (fun row => GoodC row.2) (orderedRows.drop 0) 32
    · exact rows_goodC_chunk00
    · simpa only [List.drop_drop] using h1
  simpa only [List.drop_zero] using h0
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodC
end DiophantineConsistency.ArithmeticWangTable
