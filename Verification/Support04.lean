import Mathlib
import Verification.Core02

noncomputable section
open scoped NNReal
namespace Verification.Core02

def object13 (φ : type01 → ℝ) (c S : ℝ) (ξ : type01) : ℝ := φ ((c * S)⁻¹ • ξ)
def object14 (φ : type01 → ℝ) (c C S : ℝ) (ξ : type01) : ℝ :=
  φ ((2 / (C * S)) • ξ) - object13 φ c S ξ
def object15 (φ : type01 → ℝ) (C S : ℝ) (ξ : type01) : ℝ :=
  1 - φ ((2 / (C * S)) • ξ)

theorem result64 (φ : type01 → ℝ)
    (hφ : ∀ ξ, φ ξ ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ ξ, ‖ξ‖ ≤ 1 → φ ξ = 1)
    (hzero : ∀ ξ, 2 ≤ ‖ξ‖ → φ ξ = 0)
    {c C S : ℝ} (hc : 0 < c) (hC : 0 < C) (hS : 0 < S)
    (hsep : 4 * c ≤ C) (ξ : type01) : object14 φ c C S ξ ∈ Set.Icc (0 : ℝ) 1 := by
  have hcS := mul_pos hc hS
  have hCS := mul_pos hC hS
  by_cases hξ : ‖ξ‖ ≤ 2 * c * S
  · have hupper : ‖(2 / (C * S)) • ξ‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hCS)]
      rw [div_mul_eq_mul_div]
      apply (div_le_one hCS).2
      nlinarith [mul_le_mul_of_nonneg_right hsep hS.le]
    rw [object14, hone _ hupper]
    have hlow := hφ ((c * S)⁻¹ • ξ)
    unfold object13
    exact ⟨by linarith [hlow.2], by linarith [hlow.1]⟩
  · have hlower : 2 ≤ ‖(c * S)⁻¹ • ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcS)]
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hcS).2
      linarith
    simp only [object14, object13, hzero _ hlower, sub_zero]
    exact hφ _

theorem result65 (φ : type01 → ℝ)
    (hφ : ∀ ξ, φ ξ ∈ Set.Icc (0 : ℝ) 1) (c C S : ℝ) (ξ : type01) :
    object13 φ c S ξ ∈ Set.Icc (0 : ℝ) 1 ∧
      object15 φ C S ξ ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hφ _, ?_⟩
  have hu := hφ ((2 / (C * S)) • ξ)
  exact ⟨by dsimp [object15]; linarith [hu.2],
    by dsimp [object15]; linarith [hu.1]⟩

#print axioms Verification.Core02.result64
#print axioms Verification.Core02.result65
#print axioms Verification.Core02.object13
#print axioms Verification.Core02.object14
#print axioms Verification.Core02.object15

end Verification.Core02
