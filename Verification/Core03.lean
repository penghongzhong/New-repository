import Mathlib
import Verification.Bridge03

noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal NNReal SchwartzMap BoundedContinuousFunction

namespace Verification.Core02

def object09 (f : type01 → ℂ) (ξ : type01) : ℂ :=
  ∫ x, Complex.exp ((↑(-inner ℝ x ξ) : ℂ) * Complex.I) * f x

def object10 (g : type01 → ℂ) (x : type01) : ℂ :=
  ((2 * Real.pi) ^ 3)⁻¹ •
    ∫ ξ, Complex.exp ((↑(inner ℝ ξ x) : ℂ) * Complex.I) * g ξ

theorem result46 (f : type01 → ℂ) (ξ : type01) :
    object09 f ξ = 𝓕 f ((2 * Real.pi)⁻¹ • ξ) := by
  rw [object09, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [inner_smul_right, smul_eq_mul]
  congr 3
  field_simp

theorem result47 (g : type01 → ℂ) (x : type01) :
    object10 g x =
      ((2 * Real.pi) ^ 3)⁻¹ • 𝓕⁻ g ((2 * Real.pi)⁻¹ • x) := by
  rw [object10, Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [inner_smul_right, smul_eq_mul]
  congr 3
  field_simp

theorem result48 (g : type01 → ℂ) :
    object10 g = object07 (2 * Real.pi)⁻¹ (𝓕⁻ g) := by
  funext x
  rw [result47]
  simp only [object07, inv_pow]

theorem result49 (g : type01 → ℂ) :
    (∫ z, ‖z‖ * ‖object10 g z‖) =
      (2 * Real.pi) * (∫ z, ‖z‖ * ‖𝓕⁻ g z‖) := by
  rw [result48,
    result32 (by positivity : 0 < (2 * Real.pi)⁻¹)]
  simp only [div_inv_eq_mul, mul_comm]

theorem result50 (g : type01 → ℂ) (x : type01) :
    object10 g x = 𝓕⁻ (fun ξ => g ((2 * Real.pi) • ξ)) x := by
  let F : type01 → ℂ := fun ξ =>
    Complex.exp ((↑(inner ℝ ξ x) : ℂ) * Complex.I) * g ξ
  have heq : (fun ξ => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) *
      g ((2 * Real.pi) • ξ)) = fun ξ => F ((2 * Real.pi) • ξ) := by
    funext ξ
    simp only [F, inner_smul_left, starRingEnd_apply, star_trivial]
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul]
  rw [heq]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure type01) F (2 * Real.pi)
    (hR := by positivity)
  simp only [type01, finrank_euclideanSpace, Fintype.card_fin] at h
  exact h.symm

theorem result51 (p f : type01 → ℂ) (x : type01) :
    object10 (fun ξ => p ξ * object09 f ξ) x =
      𝓕⁻ (fun ξ => p ((2 * Real.pi) • ξ) * 𝓕 f ξ) x := by
  rw [result50]
  have heq : (fun ξ => p ((2 * Real.pi) • ξ) * object09 f ((2 * Real.pi) • ξ)) =
      fun ξ => p ((2 * Real.pi) • ξ) * 𝓕 f ξ := by
    funext ξ
    rw [result46]
    simp only [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
      one_smul]
  rw [heq]

def object11 (p : type01 →ᵇ ℂ) : type01 →ᵇ ℂ :=
  object08 p (2 * Real.pi) 0

@[simp] theorem result52 (p : type01 →ᵇ ℂ) (ξ : type01) :
    object11 p ξ = p ((2 * Real.pi) • ξ) := by
  simp [object11, object08]

def object12 (p : type01 →ᵇ ℂ) : type02 →L[ℂ] type02 :=
  object05 (object11 p)

theorem result53 (p : type01 →ᵇ ℂ) (a : ℝ) :
    object11 (object08 p a 0) = object08 p (a * (2 * Real.pi)) 0 := by
  ext ξ
  simp [object11, object08, smul_smul]

theorem result54 (φ : 𝓢(type01, ℂ)) : Integrable (object10 φ) := by
  rw [result48, ← SchwartzMap.fourierInv_coe]
  exact result30 (by positivity) (𝓕⁻ φ : 𝓢(type01, ℂ)).integrable

theorem result55 (φ : 𝓢(type01, ℂ)) :
    Integrable (fun z => ‖z‖ * ‖object10 φ z‖) := by
  simp only [result48, ← SchwartzMap.fourierInv_coe]
  exact result31 (by positivity)
    (result33 (𝓕⁻ φ : 𝓢(type01, ℂ))).2

theorem result56 (φ : 𝓢(type01, ℂ))
    {a : ℝ} (ha : 0 < a) (f : type02) :
    object02 (object07 a (object10 φ)) f =
      object12 (object08 φ.toBoundedContinuousFunction a⁻¹ 0) f := by
  apply result38
    (result30 ha (result54 φ))
  intro ξ
  rw [result37 ha, result48,
    result37 (by positivity : 0 < (2 * Real.pi)⁻¹),
    ← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe, fourier_fourierInv_eq]
  simp [object11, object08, smul_smul, mul_comm]

theorem result57 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {c S R : ℝ}
    (hc : 0 < c) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    ‖object12 (object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0)
        (object04 (object08 χ (S / R) y) f) -
      object04 (object08 χ (S / R) y)
        (object12 (object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖object10 φ z‖) / (c * R)) * ‖f‖ := by
  have h := result40 φ χ hχ
    (c := c / (2 * Real.pi)) (by positivity) hS hR y f
  have ha : (c * S)⁻¹ * (2 * Real.pi) = ((c / (2 * Real.pi)) * S)⁻¹ := by
    field_simp
  simp only [object12, result53, ha]
  rw [result49]
  have hm : (∫ z, ‖z‖ * ‖𝓕⁻ (φ : type01 → ℂ) z‖) =
      ∫ z, ‖z‖ * ‖(𝓕⁻ φ : 𝓢(type01, ℂ)) z‖ := by
    simp only [SchwartzMap.fourierInv_coe]
  rw [hm]
  convert h using 1
  field_simp

theorem result58 (p q : type01 →ᵇ ℂ) (f : type02) :
    object12 (p - q) f =
      object12 p f - object12 q f := by
  have hpq : object11 (p - q) = object11 p - object11 q := by
    ext ξ
    simp
  simp only [object12, hpq, result42]

theorem result59 (f : type02) : object12 1 f = f := by
  have h1 : object11 1 = 1 := by
    ext ξ
    simp
  simp only [object12, h1, result43]

theorem result60 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {c C S R : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
    let pl := object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0
    let M := object04 (object08 χ (S / R) y)
    ‖object12 (pu - pl) (M f) - M (object12 (pu - pl) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖object10 φ z‖) * (1 / c + 2 / C) / R) * ‖f‖ := by
  dsimp only
  let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
  let pl := object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0
  let M := object04 (object08 χ (S / R) y)
  have hu := result57 φ χ hχ (c := C / 2)
    (by positivity) hS hR y f
  have hl := result57 φ χ hχ hc hS hR y f
  have heq : object12 (pu - pl) (M f) - M (object12 (pu - pl) f) =
      (object12 pu (M f) - M (object12 pu f)) -
        (object12 pl (M f) - M (object12 pl f)) := by
    rw [result58, result58, map_sub]
    abel
  change ‖object12 (pu - pl) (M f) - M (object12 (pu - pl) f)‖ ≤ _
  rw [heq]
  refine (norm_sub_le _ _).trans ((add_le_add hu hl).trans_eq ?_)
  field_simp
  ring

theorem result61 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {C S R : ℝ}
    (hC : 0 < C) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
    let M := object04 (object08 χ (S / R) y)
    ‖object12 (1 - pu) (M f) - M (object12 (1 - pu) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖object10 φ z‖) * (2 / C) / R) * ‖f‖ := by
  dsimp only
  let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
  let M := object04 (object08 χ (S / R) y)
  have hu := result57 φ χ hχ (c := C / 2)
    (by positivity) hS hR y f
  have heq : object12 (1 - pu) (M f) - M (object12 (1 - pu) f) =
      -(object12 pu (M f) - M (object12 pu f)) := by
    rw [result58, result58,
      result59, result59, map_sub]
    abel
  change ‖object12 (1 - pu) (M f) - M (object12 (1 - pu) f)‖ ≤ _
  rw [heq, norm_neg]
  refine hu.trans_eq ?_
  field_simp

theorem result62 (p χ : type01 →ᵇ ℂ) (a b : ℂ) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hp : ∀ ξ, ‖p ξ - a‖ ≤ r) (hχ : ∀ x, ‖χ x - b‖ ≤ s) :
    ‖Support02.object01 (object12 p) (object04 χ)‖ ≤ 2 * r * s := by
  apply result20 (object11 p) χ a b hr hs
  · intro ξ
    simpa only [result52] using hp ((2 * Real.pi) • ξ)
  · exact hχ

theorem result63 (p χ : type01 →ᵇ ℂ)
    (hp : ∀ ξ, ‖p ξ - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ))
    (hχ : ∀ x, ‖χ x - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ)) :
    ‖Support02.object01 (object12 p) (object04 χ)‖ ≤ (1 / 2 : ℝ) := by
  have h := result62 p χ (1 / 2) (1 / 2)
    (r := 1 / 2) (s := 1 / 2) (by norm_num) (by norm_num) hp hχ
  norm_num at h ⊢
  exact h

#print axioms Verification.Core02.result46
#print axioms Verification.Core02.result47
#print axioms Verification.Core02.result48
#print axioms Verification.Core02.result49
#print axioms Verification.Core02.result50
#print axioms Verification.Core02.result51
#print axioms Verification.Core02.result52
#print axioms Verification.Core02.result53
#print axioms Verification.Core02.result54
#print axioms Verification.Core02.result55
#print axioms Verification.Core02.result56
#print axioms Verification.Core02.result57
#print axioms Verification.Core02.result58
#print axioms Verification.Core02.result59
#print axioms Verification.Core02.result60
#print axioms Verification.Core02.result61
#print axioms Verification.Core02.result62
#print axioms Verification.Core02.result63
#print axioms Verification.Core02.object09
#print axioms Verification.Core02.object10
#print axioms Verification.Core02.object11
#print axioms Verification.Core02.object12

end Verification.Core02
