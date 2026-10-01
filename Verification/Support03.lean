import Mathlib
import Verification.Core02
import Verification.Support02

noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Verification.Core02

def object05 (p : type01 →ᵇ ℂ) : type02 →L[ℂ] type02 :=
  fourierInvCLM ℂ type02 ∘L object04 p ∘L fourierCLM ℂ type02

theorem result16 (χ : type01 →ᵇ ℂ) (b : ℂ) {s : ℝ}
    (hχ : ∀ x, ‖χ x - b‖ ≤ s) (f : type02) :
    ‖object04 χ f - b • f‖ ≤ s * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (object04 χ f) (b • f), result09 χ f,
    Lp.coeFn_smul b f] with x hsub hm hb
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hb
  rw [hsub, hm, hb, ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _)

theorem result17 (χ : type01 →ᵇ ℂ) (b : ℂ) {s : ℝ}
    (hs : 0 ≤ s) (hχ : ∀ x, ‖χ x - b‖ ≤ s) :
    ‖object04 χ - b • 1‖ ≤ s := by
  apply ContinuousLinearMap.opNorm_le_bound _ hs
  intro f
  simpa using result16 χ b hχ f

theorem result18 (p : type01 →ᵇ ℂ) (a : ℂ) {r : ℝ}
    (hp : ∀ ξ, ‖p ξ - a‖ ≤ r) (f : type02) :
    ‖object05 p f - a • f‖ ≤ r * ‖f‖ := by
  rw [← Lp.norm_fourier_eq (object05 p f - a • f)]
  have heq : 𝓕 (object05 p f - a • f) = object04 p (𝓕 f) - a • 𝓕 f := by
    simp [object05, sub_eq_add_neg, fourier_fourierInv_eq]
  rw [heq]
  simpa using result16 p a hp (𝓕 f)

theorem result19 (p : type01 →ᵇ ℂ) (a : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hp : ∀ ξ, ‖p ξ - a‖ ≤ r) :
    ‖object05 p - a • 1‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro f
  simpa using result18 p a hp f

theorem result20 (p χ : type01 →ᵇ ℂ) (a b : ℂ) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ ξ, ‖p ξ - a‖ ≤ r) (hχ : ∀ x, ‖χ x - b‖ ≤ s) :
    ‖Support02.object01 (object05 p) (object04 χ)‖ ≤ 2 * r * s :=
  Support02.result03 _ _ a b hr hs
    (result19 p a hr hp) (result17 χ b hs hχ)

def object06 (p : type01 →ᵇ ℝ) : type01 →ᵇ ℂ :=
  BoundedContinuousFunction.comp Complex.ofReal Complex.isometry_ofReal.lipschitzWith p

@[simp] theorem result21 (p : type01 →ᵇ ℝ) (x : type01) :
    object06 p x = (p x : ℂ) := rfl

theorem result22 (p : type01 →ᵇ ℝ) {lo hi : ℝ}
    (hp : ∀ ξ, lo ≤ p ξ ∧ p ξ ≤ hi) (ξ : type01) :
    ‖object06 p ξ - (((lo + hi) / 2 : ℝ) : ℂ)‖ ≤ (hi - lo) / 2 := by
  rw [result21, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨hl, hu⟩ := hp ξ
  rw [abs_le]
  constructor <;> linarith

theorem result23 (p χ : type01 →ᵇ ℝ) {lo hi u v : ℝ}
    (hp : ∀ ξ, lo ≤ p ξ ∧ p ξ ≤ hi) (hχ : ∀ x, u ≤ χ x ∧ χ x ≤ v) :
    ‖Support02.object01 (object05 (object06 p))
      (object04 (object06 χ))‖ ≤ (hi - lo) * (v - u) / 2 := by
  have hp_order : lo ≤ hi := (hp 0).1.trans (hp 0).2
  have hχ_order : u ≤ v := (hχ 0).1.trans (hχ 0).2
  have h := result20 (object06 p) (object06 χ)
    (((lo + hi) / 2 : ℝ) : ℂ) (((u + v) / 2 : ℝ) : ℂ)
    (r := (hi - lo) / 2) (s := (v - u) / 2)
    (by positivity) (by positivity)
    (result22 p hp) (result22 χ hχ)
  nlinarith

theorem result24 (p χ : type01 →ᵇ ℝ) {lo hi : ℝ}
    (hp : ∀ ξ, lo ≤ p ξ ∧ p ξ ≤ hi) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ‖Support02.object01 (object05 (object06 p))
      (object04 (object06 χ))‖ ≤ (hi - lo) / 2 := by
  simpa using result23 p χ hp hχ

theorem result25 (p χ : type01 →ᵇ ℝ)
    (hp : ∀ ξ, 0 ≤ p ξ ∧ p ξ ≤ 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ‖Support02.object01 (object05 (object06 p))
      (object04 (object06 χ))‖ ≤ (1 / 2 : ℝ) := by
  simpa using result24 p χ hp hχ

theorem result26 (p : type01 →ᵇ ℂ) (χ : type01 →ᵇ ℝ)
    (hp : ∀ ξ, ‖p ξ‖ ≤ 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ‖Support02.object01 (object05 p) (object04 (object06 χ))‖ ≤ 1 := by
  have h := result20 p (object06 χ) 0 (1 / 2 : ℂ)
    (r := 1) (s := 1 / 2) (by norm_num) (by norm_num)
    (by simpa using hp) (by simpa using result22 χ hχ)
  norm_num at h ⊢
  exact h

theorem result27 (p χ : type01 →ᵇ ℝ)
    {lo hi : ℝ} (hp : ∀ ξ, lo ≤ p ξ ∧ p ξ ≤ hi)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (f : type02) :
    ‖object05 (object06 p) (object04 (object06 χ) f) -
      object04 (object06 χ) (object05 (object06 p) f)‖ ≤
      (hi - lo) / 2 * ‖f‖ := by
  have h := (Support02.object01
    (object05 (object06 p)) (object04 (object06 χ))).le_opNorm f
  exact h.trans (mul_le_mul_of_nonneg_right
    (result24 p χ hp hχ) (norm_nonneg f))

#print axioms Verification.Core02.result16
#print axioms Verification.Core02.result17
#print axioms Verification.Core02.result18
#print axioms Verification.Core02.result19
#print axioms Verification.Core02.result20
#print axioms Verification.Core02.result21
#print axioms Verification.Core02.result22
#print axioms Verification.Core02.result23
#print axioms Verification.Core02.result24
#print axioms Verification.Core02.result25
#print axioms Verification.Core02.result26
#print axioms Verification.Core02.result27
#print axioms Verification.Core02.object05
#print axioms Verification.Core02.object06

end Verification.Core02
