import Mathlib

noncomputable section

open scoped NNReal

namespace Verification.Support02

section Scope01

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def object01 (P M : E →L[𝕜] E) : E →L[𝕜] E := P * M - M * P

theorem result01 (P M : E →L[𝕜] E) (a b : 𝕜) :
    object01 (P - a • 1) (M - b • 1) = object01 P M := by
  simp only [object01, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_sub, smul_smul]
  rw [mul_comm a b]
  abel

theorem result02 (P M : E →L[𝕜] E) :
    ‖object01 P M‖ ≤ 2 * ‖P‖ * ‖M‖ := by
  calc
    ‖object01 P M‖ ≤ ‖P * M‖ + ‖M * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖M‖ + ‖M‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖M‖ := by ring

theorem result03 (P M : E →L[𝕜] E) (a b : 𝕜)
    {r s : ℝ} (hr : 0 ≤ r) (_hs : 0 ≤ s)
    (hP : ‖P - a • 1‖ ≤ r) (hM : ‖M - b • 1‖ ≤ s) :
    ‖object01 P M‖ ≤ 2 * r * s := by
  rw [← result01 P M a b]
  calc
    _ ≤ 2 * ‖P - a • 1‖ * ‖M - b • 1‖ := result02 _ _
    _ ≤ 2 * r * s := by gcongr

theorem result04 (P M : E →L[𝕜] E)
    (hP : ‖P‖ ≤ 1) (hM : ‖M - (1 / 2 : 𝕜) • 1‖ ≤ (1 / 2 : ℝ)) :
    ‖object01 P M‖ ≤ 1 := by
  have h := result03 P M 0 (1 / 2 : 𝕜)
    (r := 1) (s := 1 / 2) (by norm_num) (by norm_num) (by simpa using hP) hM
  norm_num at h ⊢
  exact h

theorem result05 (P M : E →L[𝕜] E)
    (hP : ‖P - (1 / 2 : 𝕜) • 1‖ ≤ (1 / 2 : ℝ))
    (hM : ‖M - (1 / 2 : 𝕜) • 1‖ ≤ (1 / 2 : ℝ)) :
    ‖object01 P M‖ ≤ (1 / 2 : ℝ) := by
  have h := result03 P M (1 / 2 : 𝕜) (1 / 2 : 𝕜)
    (r := 1 / 2) (s := 1 / 2) (by norm_num) (by norm_num) hP hM
  norm_num at h ⊢
  exact h

theorem result06 (P M : E →L[𝕜] E) (a : 𝕜)
    {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ‖P - a • 1‖ ≤ ω / 2)
    (hM : ‖M - (1 / 2 : 𝕜) • 1‖ ≤ (1 / 2 : ℝ)) :
    ‖object01 P M‖ ≤ ω / 2 := by
  have h := result03 P M a (1 / 2 : 𝕜)
    (r := ω / 2) (s := 1 / 2) (by positivity) (by norm_num) hP hM
  nlinarith

theorem result07 (P M : E →L[𝕜] E) (a : 𝕜)
    {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ‖P - a • 1‖ ≤ ω / 2)
    (hM : ‖M - (1 / 2 : 𝕜) • 1‖ ≤ (1 / 2 : ℝ)) (f : E) :
    ‖object01 P M f‖ ≤ ω / 2 * ‖f‖ :=
  (object01 P M).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right
      (result06 P M a hω hP hM) (norm_nonneg f))

end Scope01

section Scope02

open MeasureTheory

variable {V F : Type*} [NormedAddCommGroup V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def object02 (K χ : V → ℂ) (f : V → F) (x z : V) : F :=
  K z • ((χ (x - z) - χ x) • f (x - z))

theorem result08 (K χ : V → ℂ) (f : V → F) (x z : V)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) :
    ‖object02 K χ f x z‖ ≤
      (L : ℝ) * (‖z‖ * ‖K z‖ * ‖f (x - z)‖) := by
  have hdiff : ‖χ (x - z) - χ x‖ ≤ (L : ℝ) * ‖z‖ := by
    simpa [dist_eq_norm, sub_sub_cancel_left] using hχ.dist_le_mul (x - z) x
  calc
    ‖object02 K χ f x z‖ =
        ‖K z‖ * (‖χ (x - z) - χ x‖ * ‖f (x - z)‖) := by
      simp only [object02, norm_smul]
    _ ≤ ‖K z‖ * (((L : ℝ) * ‖z‖) * ‖f (x - z)‖) := by gcongr
    _ = (L : ℝ) * (‖z‖ * ‖K z‖ * ‖f (x - z)‖) := by ring

variable [MeasurableSpace V]

theorem result09 (μ : Measure V)
    (K χ : V → ℂ) (f : V → F) (x : V) {L : ℝ≥0}
    (hχ : LipschitzWith L χ)
    (hint : Integrable (fun z ↦ ‖z‖ * ‖K z‖ * ‖f (x - z)‖) μ) :
    ‖∫ z, object02 K χ f x z ∂μ‖ ≤
      (L : ℝ) * ∫ z, ‖z‖ * ‖K z‖ * ‖f (x - z)‖ ∂μ := by
  calc
    _ ≤ ∫ z, (L : ℝ) * (‖z‖ * ‖K z‖ * ‖f (x - z)‖) ∂μ :=
      norm_integral_le_of_norm_le (hint.const_mul L)
        (Filter.Eventually.of_forall (result08 K χ f x · hχ))
    _ = _ := integral_const_mul _ _

theorem result10 (μ : Measure V)
    (K χ : V → ℂ) (f : V → F) (x : V)
    (hbase : Integrable (fun z ↦ K z • f (x - z)) μ)
    (hweighted : Integrable (fun z ↦ K z • (χ (x - z) • f (x - z))) μ) :
    (∫ z, object02 K χ f x z ∂μ) =
      (∫ z, K z • (χ (x - z) • f (x - z)) ∂μ) -
        χ x • (∫ z, K z • f (x - z) ∂μ) := by
  have heq : (fun z ↦ object02 K χ f x z) =
      (fun z ↦ K z • (χ (x - z) • f (x - z)) - χ x • (K z • f (x - z))) := by
    funext z
    simp [object02, sub_smul, smul_sub, smul_smul, mul_comm]
  have hconst : Integrable (fun z ↦ χ x • (K z • f (x - z))) μ :=
    hbase.fun_smul (χ x)
  rw [heq, integral_sub hweighted hconst, integral_smul]

theorem result11 (μ : Measure V)
    (K χ : V → ℂ) (f : V → F) (x : V) {L : ℝ≥0}
    (hχ : LipschitzWith L χ)
    (hbase : Integrable (fun z ↦ K z • f (x - z)) μ)
    (hweighted : Integrable (fun z ↦ K z • (χ (x - z) • f (x - z))) μ)
    (hmoment : Integrable (fun z ↦ ‖z‖ * ‖K z‖ * ‖f (x - z)‖) μ) :
    ‖(∫ z, K z • (χ (x - z) • f (x - z)) ∂μ) -
        χ x • (∫ z, K z • f (x - z) ∂μ)‖ ≤
      (L : ℝ) * ∫ z, ‖z‖ * ‖K z‖ * ‖f (x - z)‖ ∂μ := by
  rw [← result10 μ K χ f x hbase hweighted]
  exact result09 μ K χ f x hχ hmoment

end Scope02

section Scope03

def object03 (c : ℝ) : ℝ := 1 / c
def object04 (c C : ℝ) : ℝ := 1 / c + 2 / C
def object05 (C : ℝ) : ℝ := 2 / C

theorem result12 (A L c S R : ℝ) (hc : c ≠ 0) (hS : S ≠ 0)
    (hR : R ≠ 0) :
    (L * S / R) * (A / (c * S)) = A * L * object03 c / R := by
  unfold object03
  field_simp

theorem result13 (A L C S R : ℝ) (hC : C ≠ 0) (hS : S ≠ 0)
    (hR : R ≠ 0) :
    (L * S / R) * (2 * A / (C * S)) = A * L * object05 C / R := by
  unfold object05
  field_simp

theorem result14 (A L c C S R : ℝ)
    (hc : c ≠ 0) (hC : C ≠ 0) (hS : S ≠ 0) (hR : R ≠ 0) :
    (L * S / R) * (A / (c * S) + 2 * A / (C * S)) =
      A * L * object04 c C / R := by
  unfold object04
  field_simp

theorem result15 {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    0 < object03 c ∧ 0 < object05 C ∧
      object03 c ≤ object04 c C ∧ object05 C ≤ object04 c C := by
  unfold object03 object05 object04
  have hlow : 0 < 1 / c := by positivity
  have hhigh : 0 < 2 / C := by positivity
  exact ⟨hlow, hhigh, by linarith, by linarith⟩

theorem result16 {A L γ R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    A * L * γ / R ≤ ε ↔ A * L * γ / ε ≤ R := by
  rw [div_le_iff₀ hR, div_le_iff₀ hε]
  constructor <;> intro h <;> nlinarith

theorem result17 {A c C R : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hC : 0 < C) (hR : 0 < R)
    (hthreshold : A * object04 c C / c ≤ R) :
    A * object03 c / R ≤ c ∧
      A * object04 c C / R ≤ c ∧ A * object05 C / R ≤ c := by
  have hmid : A * object04 c C / R ≤ c := by
    apply (div_le_iff₀ hR).2
    have h := (div_le_iff₀ hc).1 hthreshold
    nlinarith
  obtain ⟨_, _, hlow, hhigh⟩ := result15 hc hC
  exact ⟨(div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlow hA) hR.le).trans hmid, hmid,
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhigh hA) hR.le).trans hmid⟩

end Scope03

#print axioms Verification.Support02.result01
#print axioms Verification.Support02.result02
#print axioms Verification.Support02.result03
#print axioms Verification.Support02.result04
#print axioms Verification.Support02.result05
#print axioms Verification.Support02.result06
#print axioms Verification.Support02.result07
#print axioms Verification.Support02.result08
#print axioms Verification.Support02.result09
#print axioms Verification.Support02.result10
#print axioms Verification.Support02.result11
#print axioms Verification.Support02.result12
#print axioms Verification.Support02.result13
#print axioms Verification.Support02.result14
#print axioms Verification.Support02.result15
#print axioms Verification.Support02.result16
#print axioms Verification.Support02.result17
#print axioms Verification.Support02.object01
#print axioms Verification.Support02.object02
#print axioms Verification.Support02.object03
#print axioms Verification.Support02.object04
#print axioms Verification.Support02.object05

end Verification.Support02
