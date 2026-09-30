import Mathlib

namespace Verification.Support01


theorem result01
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (w e : ι → ℝ)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hpoint : ∀ i ∈ s, w i * e i ≤ A)
    (hsq : ∑ i ∈ s, (e i) ^ 2 ≤ B) :
    ∑ i ∈ s, w i * (e i) ^ 3 ≤ A * B := by
  calc
    ∑ i ∈ s, w i * (e i) ^ 3
        = ∑ i ∈ s, (w i * e i) * (e i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ ≤ ∑ i ∈ s, A * (e i) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hpoint i hi) (sq_nonneg (e i))
    _ = A * ∑ i ∈ s, (e i) ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ A * B := mul_le_mul_of_nonneg_left hsq hA


theorem result02
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (w e : ι → ℝ)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hsup : ∀ i ∈ s, w i * e i ≤ A)
    (hsquare : ∑ i ∈ s, (e i) ^ 2 ≤ B) :
    ∑ i ∈ s, w i * (e i) ^ 3 ≤ A * B :=
  result01 s w e A B hA hsup hsquare


theorem result03 :
    (1 : ℕ) + 3 + 3 + 1 = 8 := by
  norm_num


theorem result04 :
    Nat.choose 3 1 = 3 ∧ Nat.choose 3 2 = 3 := by
  norm_num [Nat.choose]

#print axioms Verification.Support01.result01
#print axioms Verification.Support01.result02
#print axioms Verification.Support01.result03
#print axioms Verification.Support01.result04

end Verification.Support01
