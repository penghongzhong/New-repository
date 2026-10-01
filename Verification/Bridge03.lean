import Mathlib
import Verification.Core02
import Verification.Bridge02
import Verification.Support03

noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal NNReal SchwartzMap BoundedContinuousFunction

namespace Verification.Core02

def object07 (a : ℝ) (K : type01 → ℂ) (z : type01) : ℂ := a ^ 3 • K (a • z)

theorem result28 {a : ℝ} (ha : 0 < a) (K : type01 → ℂ) (z : type01) :
    ‖object07 a K z‖ = a ^ 3 * ‖K (a • z)‖ := by
  simp [object07, Real.norm_eq_abs, abs_of_pos ha]

theorem result29 {a : ℝ} (ha : 0 < a) (K : type01 → ℂ) (z : type01) :
    ‖z‖ * ‖object07 a K z‖ = a ^ 2 * (‖a • z‖ * ‖K (a • z)‖) := by
  rw [result28 ha, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  ring

theorem result30 {a : ℝ} (ha : 0 < a) {K : type01 → ℂ}
    (hK : Integrable K) : Integrable (object07 a K) :=
  (hK.comp_smul ha.ne').fun_smul (a ^ 3)

theorem result31 {a : ℝ} (ha : 0 < a) {K : type01 → ℂ}
    (hKm : Integrable (fun z => ‖z‖ * ‖K z‖)) :
    Integrable (fun z => ‖z‖ * ‖object07 a K z‖) := by
  simp_rw [result29 ha]
  exact (hKm.comp_smul ha.ne').const_mul (a ^ 2)

theorem result32 {a : ℝ} (ha : 0 < a) (K : type01 → ℂ) :
    (∫ z, ‖z‖ * ‖object07 a K z‖) = (∫ z, ‖z‖ * ‖K z‖) / a := by
  simp_rw [result29 ha]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure type01)
    (fun z => ‖z‖ * ‖K z‖) a (hR := ha.le)
  simp only [type01, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  rw [h]
  field_simp

theorem result33 (K : 𝓢(type01, ℂ)) :
    Integrable K ∧ Integrable (fun z => ‖z‖ * ‖K z‖) := by
  exact ⟨K.integrable, by simpa using K.integrable_pow_mul volume 1⟩

theorem result34 (K : 𝓢(type01, ℂ)) {a : ℝ} (ha : 0 < a)
    (χ : type01 →ᵇ ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ) (f : type02) :
    ‖object02 (object07 a K) (object04 χ f) -
        object04 χ (object02 (object07 a K) f)‖ ≤
      (L : ℝ) * ((∫ z, ‖z‖ * ‖K z‖) / a) * ‖f‖ := by
  have h := result15 (object07 a K)
    (result30 ha K.integrable) χ hχ
    (result31 ha (result33 K).2) f
  rwa [result32 ha] at h

def object08 (χ : type01 →ᵇ ℂ) (a : ℝ) (y : type01) : type01 →ᵇ ℂ :=
  χ.compContinuous ⟨fun x => a • (x - y), by fun_prop⟩

theorem result35 (χ : type01 →ᵇ ℂ) {L : ℝ≥0}
    (hχ : LipschitzWith L χ) (a : ℝ) (y : type01) :
    LipschitzWith (L * ‖a‖₊) (object08 χ a y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  calc
    dist (object08 χ a y x) (object08 χ a y z) ≤
        (L : ℝ) * dist (a • (x - y)) (a • (z - y)) := hχ.dist_le_mul _ _
    _ = ((L * ‖a‖₊ : ℝ≥0) : ℝ) * dist x z := by
      simp only [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        NNReal.coe_mul, coe_nnnorm]
      ring

theorem result36 (K : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {c S R : ℝ}
    (hc : 0 < c) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    ‖object02 (object07 (c * S) K) (object04 (object08 χ (S / R) y) f) -
        object04 (object08 χ (S / R) y) (object02 (object07 (c * S) K) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖K z‖) / (c * R)) * ‖f‖ := by
  have h := result34 K (mul_pos hc hS)
    (object08 χ (S / R) y) (result35 χ hχ (S / R) y) f
  have heq : ((L * ‖S / R‖₊ : ℝ≥0) : ℝ) * ((∫ z, ‖z‖ * ‖K z‖) / (c * S)) =
      (L : ℝ) * (∫ z, ‖z‖ * ‖K z‖) / (c * R) := by
    rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (div_pos hS hR)]
    field_simp
  rwa [heq] at h

theorem result37 {a : ℝ} (ha : 0 < a) (K : type01 → ℂ) (ξ : type01) :
    𝓕 (object07 a K) ξ = 𝓕 K (a⁻¹ • ξ) := by
  let F : type01 → ℂ := fun x => Real.fourierChar (-inner ℝ x (a⁻¹ • ξ)) • K x
  have heq : (fun x => Real.fourierChar (-inner ℝ x ξ) • object07 a K x) =
      fun x => a ^ 3 • F (a • x) := by
    funext x
    have hi : inner ℝ (a • x) (a⁻¹ • ξ) = inner ℝ x ξ := by
      simp [inner_smul_left, inner_smul_right, ha.ne']
    dsimp only [F, object07]
    rw [hi]
    exact smul_comm _ _ _
  change (∫ x, Real.fourierChar (-inner ℝ x ξ) • object07 a K x) = _
  rw [heq, integral_smul]
  have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure type01) F a (hR := ha.le)
  simp only [type01, finrank_euclideanSpace, Fintype.card_fin] at hscale
  rw [hscale, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 ha.ne'), one_smul]
  rfl

theorem result38 {K : type01 → ℂ} (hK : Integrable K)
    (p : type01 →ᵇ ℂ) (hp : ∀ ξ, p ξ = 𝓕 K ξ) (f : type02) :
    object02 K f = object05 p f := by
  rw [Bridge02.result16 hK]
  have hs : Bridge02.object03 hK = (p.memLp_top (μ := volume)).toLp p := by
    apply Lp.ext
    filter_upwards [(Bridge02.result04 hK).coeFn_toLp,
      (p.memLp_top (μ := volume)).coeFn_toLp] with ξ hKξ hpξ
    exact hKξ.trans ((hp ξ).symm.trans hpξ.symm)
  rw [hs]
  rfl

theorem result39 (φ : 𝓢(type01, ℂ)) {a : ℝ} (ha : 0 < a) (f : type02) :
    object02 (object07 a (𝓕⁻ φ : 𝓢(type01, ℂ))) f =
      object05 (object08 φ.toBoundedContinuousFunction a⁻¹ 0) f := by
  apply result38 (result30 ha (𝓕⁻ φ : 𝓢(type01, ℂ)).integrable)
  intro ξ
  rw [result37 ha]
  change φ (a⁻¹ • (ξ - 0)) = (𝓕 (𝓕⁻ φ : 𝓢(type01, ℂ))) (a⁻¹ • ξ)
  simp only [sub_zero, fourier_fourierInv_eq]

theorem result40 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {c S R : ℝ}
    (hc : 0 < c) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    ‖object05 (object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0)
        (object04 (object08 χ (S / R) y) f) -
      object04 (object08 χ (S / R) y)
        (object05 (object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖(𝓕⁻ φ : 𝓢(type01, ℂ)) z‖) / (c * R)) * ‖f‖ := by
  have h := result36 (𝓕⁻ φ : 𝓢(type01, ℂ)) χ hχ hc hS hR y f
  simpa only [result39 φ (mul_pos hc hS)] using h

theorem result41 (p q : type01 →ᵇ ℂ) (f : type02) :
    object04 (p - q) f = object04 p f - object04 q f := by
  apply Lp.ext
  filter_upwards [result09 (p - q) f, result09 p f, result09 q f,
    Lp.coeFn_sub (object04 p f) (object04 q f)] with x hpq hp hq hsub
  simp only [Pi.sub_apply] at hsub
  rw [hpq, hsub, hp, hq]
  change (p x - q x) * f x = _
  ring

theorem result42 (p q : type01 →ᵇ ℂ) (f : type02) :
    object05 (p - q) f = object05 p f - object05 q f := by
  change 𝓕⁻ (object04 (p - q) (𝓕 f)) = _
  rw [result41]
  simp [object05, sub_eq_add_neg]

theorem result43 (f : type02) : object05 1 f = f := by
  have hm : object04 (1 : type01 →ᵇ ℂ) (𝓕 f) = 𝓕 f := by
    apply Lp.ext
    filter_upwards [result09 (1 : type01 →ᵇ ℂ) (𝓕 f)] with x hx
    simpa using hx
  change 𝓕⁻ (object04 1 (𝓕 f)) = f
  rw [hm, fourierInv_fourier_eq]

theorem result44 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {c C S R : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
    let pl := object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0
    let M := object04 (object08 χ (S / R) y)
    ‖object05 (pu - pl) (M f) - M (object05 (pu - pl) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖(𝓕⁻ φ : 𝓢(type01, ℂ)) z‖) * (1 / c + 2 / C) / R) * ‖f‖ := by
  dsimp only
  let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
  let pl := object08 φ.toBoundedContinuousFunction (c * S)⁻¹ 0
  let M := object04 (object08 χ (S / R) y)
  have hu := result40 φ χ hχ (c := C / 2) (by positivity) hS hR y f
  have hl := result40 φ χ hχ hc hS hR y f
  have heq : object05 (pu - pl) (M f) - M (object05 (pu - pl) f) =
      (object05 pu (M f) - M (object05 pu f)) -
        (object05 pl (M f) - M (object05 pl f)) := by
    rw [result42, result42, map_sub]
    abel
  change ‖object05 (pu - pl) (M f) - M (object05 (pu - pl) f)‖ ≤ _
  rw [heq]
  refine (norm_sub_le _ _).trans ((add_le_add hu hl).trans_eq ?_)
  field_simp
  ring

theorem result45 (φ : 𝓢(type01, ℂ)) (χ : type01 →ᵇ ℂ)
    {L : ℝ≥0} (hχ : LipschitzWith L χ) {C S R : ℝ}
    (hC : 0 < C) (hS : 0 < S) (hR : 0 < R) (y : type01) (f : type02) :
    let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
    let M := object04 (object08 χ (S / R) y)
    ‖object05 (1 - pu) (M f) - M (object05 (1 - pu) f)‖ ≤
      ((L : ℝ) * (∫ z, ‖z‖ * ‖(𝓕⁻ φ : 𝓢(type01, ℂ)) z‖) * (2 / C) / R) * ‖f‖ := by
  dsimp only
  let pu := object08 φ.toBoundedContinuousFunction ((C / 2) * S)⁻¹ 0
  let M := object04 (object08 χ (S / R) y)
  have hu := result40 φ χ hχ (c := C / 2) (by positivity) hS hR y f
  have heq : object05 (1 - pu) (M f) - M (object05 (1 - pu) f) =
      -(object05 pu (M f) - M (object05 pu f)) := by
    rw [result42, result42,
      result43, result43, map_sub]
    abel
  change ‖object05 (1 - pu) (M f) - M (object05 (1 - pu) f)‖ ≤ _
  rw [heq, norm_neg]
  refine hu.trans_eq ?_
  field_simp

#print axioms Verification.Core02.result28
#print axioms Verification.Core02.result29
#print axioms Verification.Core02.result30
#print axioms Verification.Core02.result31
#print axioms Verification.Core02.result32
#print axioms Verification.Core02.result33
#print axioms Verification.Core02.result34
#print axioms Verification.Core02.result35
#print axioms Verification.Core02.result36
#print axioms Verification.Core02.result37
#print axioms Verification.Core02.result38
#print axioms Verification.Core02.result39
#print axioms Verification.Core02.result40
#print axioms Verification.Core02.result41
#print axioms Verification.Core02.result42
#print axioms Verification.Core02.result43
#print axioms Verification.Core02.result44
#print axioms Verification.Core02.result45
#print axioms Verification.Core02.object07
#print axioms Verification.Core02.object08

end Verification.Core02
