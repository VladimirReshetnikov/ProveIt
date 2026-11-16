import PA194AX11HSource
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194AX11HCompareRows
theorem s3642 : PA194AX11HSource.program[3642]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 5 (some 3646) (some 3643)) := by decide +kernel
theorem s3643 : PA194AX11HSource.program[3643]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 3645) (some 3644)) := by decide +kernel
theorem s3644 : PA194AX11HSource.program[3644]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3642)) := by decide +kernel
theorem s3645 : PA194AX11HSource.program[3645]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3647)) := by decide +kernel
theorem s3646 : PA194AX11HSource.program[3646]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 3652) (some 3647)) := by decide +kernel
theorem s3647 : PA194AX11HSource.program[3647]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 5 (some 3649) (some 3648)) := by decide +kernel
theorem s3648 : PA194AX11HSource.program[3648]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3647)) := by decide +kernel
theorem s3649 : PA194AX11HSource.program[3649]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 3651) (some 3650)) := by decide +kernel
theorem s3650 : PA194AX11HSource.program[3650]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3647)) := by decide +kernel
theorem s3651 : PA194AX11HSource.program[3651]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3659)) := by decide +kernel
theorem s3652 : PA194AX11HSource.program[3652]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 4 (some 3656) (some 3653)) := by decide +kernel
theorem s3653 : PA194AX11HSource.program[3653]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 1 (some 3654)) := by decide +kernel
theorem s3654 : PA194AX11HSource.program[3654]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 6 (some 3655)) := by decide +kernel
theorem s3655 : PA194AX11HSource.program[3655]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3652)) := by decide +kernel
theorem s3656 : PA194AX11HSource.program[3656]'(by rw [PA194AX11HSource.program_length]; decide) = some (.dec 6 (some 3659) (some 3657)) := by decide +kernel
theorem s3657 : PA194AX11HSource.program[3657]'(by rw [PA194AX11HSource.program_length]; decide) = some (.inc 4 (some 3658)) := by decide +kernel
theorem s3658 : PA194AX11HSource.program[3658]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 3656)) := by decide +kernel
theorem s3659 : PA194AX11HSource.program[3659]'(by rw [PA194AX11HSource.program_length]; decide) = some (.jump (some 25)) := by decide +kernel
#print axioms s3642
#print axioms s3659
end PA194AX11HCompareRows
