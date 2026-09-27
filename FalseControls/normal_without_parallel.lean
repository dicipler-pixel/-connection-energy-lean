import ConnectionEnergy.Basic
-- A non-parallel field (D₁ = 1, D₂ = 0 on a unitary edge) is not normal: equation (2) fails.
example : (1 : ℂ) = 1 * 0 * 1 := by norm_num
