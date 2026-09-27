import ConnectionEnergy.Basic
-- Two vertices, scalar blocks D = diag(1, 0), unitary edge: the self-commutator energy is
-- 8·|D₁ − D₂|² = 8, not 4·|D₁ − D₂|². The factor in (1) is 1/8, not 1/4.
example : (8 : ℝ) * (1 - 0) ^ 2 = 4 * (1 - 0) ^ 2 := by norm_num
