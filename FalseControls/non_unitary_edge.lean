import ConnectionEnergy.Basic
-- Without unitarity the edge term is not a transport: with Aᵢⱼ = 2, scalar Dᵢ = 1, Dⱼ = 0,
-- the block [D, A]ᵢⱼ = 2, while Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ* = 1.
example : ((1 : ℝ) * 2 - 2 * 0) = 1 - 2 * 0 * 2 := by norm_num
