import Mathlib

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Verification.Core02
abbrev type01 := EuclideanSpace ℝ (Fin 3)
abbrev type02 := Lp ℂ 2 (volume : Measure type01)
local instance inst01 : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def object01 (z : type01) (f : type02) : type02 := DomAddAct.mk (-z) +ᵥ f

@[simp] theorem result01 (z : type01) (f : type02) : ‖object01 z f‖ = ‖f‖ := by
  simp [object01]

theorem result02 (z : type01) (f : type02) : object01 z f =ᵐ[volume] fun x => f (x - z) := by
  simpa [object01, sub_eq_add_neg, add_comm] using DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-z)) f

theorem result03 (f : type02) : Continuous fun z : type01 => object01 z f := by
  unfold object01
  exact (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

theorem result04 (z : type01) (f g : type02) : object01 z (f + g) = object01 z f + object01 z g := by
  simp [object01]

theorem result05 (z : type01) (c : ℂ) (f : type02) : object01 z (c • f) = c • object01 z f := by
  change (Lp.compMeasurePreservingₗ ℂ (fun x : type01 => -z + x)
    (measurePreserving_add_left volume (-z))) (c • f) = _
  exact map_smul _ _ _

def object02 (K : type01 → ℂ) (f : type02) : type02 := ∫ z, K z • object01 z f

theorem result06 {K : type01 → ℂ} (hK : Integrable K) (f : type02) :
    Integrable (fun z => K z • object01 z f) := by
  apply (hK.norm.mul_const ‖f‖).mono'
    (hK.aestronglyMeasurable.smul (result03 f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by simp [norm_smul]

theorem result07 {K : type01 → ℂ} (_hK : Integrable K) (f : type02) :
    ‖object02 K f‖ ≤ (∫ z, ‖K z‖) * ‖f‖ := by
  calc
    ‖object02 K f‖ ≤ ∫ z, ‖K z • object01 z f‖ := norm_integral_le_integral_norm _
    _ = (∫ z, ‖K z‖) * ‖f‖ := by simp [norm_smul, integral_mul_const]

def object03 (K : type01 → ℂ) (hK : Integrable K) : type02 →L[ℂ] type02 :=
  LinearMap.mkContinuous
    { toFun := object02 K
      map_add' := fun f g => by
        simp only [object02, result04, smul_add]
        exact integral_add (result06 hK f) (result06 hK g)
      map_smul' := fun c f => by
        simp only [object02, result05, RingHom.id_apply]
        simp_rw [smul_comm (K _) c]
        exact integral_smul c _ }
    (∫ z, ‖K z‖) (result07 hK)

theorem result08 {K : type01 → ℂ} (hK : Integrable K) :
    ‖object03 K hK‖ ≤ ∫ z, ‖K z‖ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ => norm_nonneg _) _

def object04 (χ : type01 →ᵇ ℂ) : type02 →L[ℂ] type02 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 ((χ.memLp_top).toLp χ)

theorem result09 (χ : type01 →ᵇ ℂ) (f : type02) :
    object04 χ f =ᵐ[volume] fun x => χ x * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((χ.memLp_top (μ := volume)).toLp χ) f
  have hc := (χ.memLp_top (μ := volume)).coeFn_toLp
  filter_upwards [hm, hc] with x hx hcx
  simpa [object04, ContinuousLinearMap.holderL_apply_apply, hcx] using hx

theorem result10 (χ : type01 →ᵇ ℂ) (f : type02) {C : ℝ}
    (hχ : ∀ x, ‖χ x‖ ≤ C) : ‖object04 χ f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [result09 χ f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _)

theorem result11 (χ : type01 →ᵇ ℂ) (z : type01) (f : type02) :
    (object01 z (object04 χ f) - object04 χ (object01 z f) : type02) =ᵐ[volume]
      fun x => (χ (x - z) - χ x) * f (x - z) := by
  have hc := (measurePreserving_sub_right (volume : Measure type01) z).quasiMeasurePreserving.ae_eq_comp
    (result09 χ f)
  filter_upwards [Lp.coeFn_sub (object01 z (object04 χ f)) (object04 χ (object01 z f)),
    result02 z (object04 χ f), result09 χ (object01 z f), result02 z f, hc]
    with x hsub hleft hright hf hcx
  simp only [Function.comp_apply] at hcx
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hleft, hright, hf, hcx]
  ring

theorem result12 (χ : type01 →ᵇ ℂ) {L : ℝ≥0}
    (hχ : LipschitzWith L χ) (z : type01) (f : type02) :
    ‖object01 z (object04 χ f) - object04 χ (object01 z f)‖ ≤
      ((L : ℝ) * ‖z‖) * ‖f‖ := by
  rw [← result01 z f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [result11 χ z f, result02 z f] with x hx hf
  rw [hx, hf, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa [dist_eq_norm, sub_sub_cancel_left] using hχ.dist_le_mul (x - z) x

theorem result13 (K : type01 → ℂ) (hK : Integrable K) (f g : type02) :
    inner ℂ g (object02 K f) = ∫ z, K z * inner ℂ g (object01 z f) := by
  rw [object02, ← integral_inner (result06 hK f)]
  simp only [inner_smul_right]

theorem result14 (K : type01 → ℂ) (hK : Integrable K)
    (χ : type01 →ᵇ ℂ) (f : type02) :
    object02 K (object04 χ f) - object04 χ (object02 K f) =
      ∫ z, K z • (object01 z (object04 χ f) - object04 χ (object01 z f)) := by
  have hi := result06 hK f
  rw [object02, object02, ← (object04 χ).integral_comp_comm hi]
  simp_rw [map_smul]
  have him : Integrable (fun z => K z • object04 χ (object01 z f)) := by
    simpa only [map_smul] using (object04 χ).integrable_comp hi
  rw [← integral_sub (result06 hK (object04 χ f)) him]
  apply integral_congr_ae
  filter_upwards with z
  simp [smul_sub]

theorem result15 (K : type01 → ℂ) (hK : Integrable K)
    (χ : type01 →ᵇ ℂ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hKm : Integrable (fun z => ‖z‖ * ‖K z‖)) (f : type02) :
    ‖object02 K (object04 χ f) - object04 χ (object02 K f)‖ ≤
      (L : ℝ) * (∫ z, ‖z‖ * ‖K z‖) * ‖f‖ := by
  rw [result14 K hK χ f]
  calc
    _ ≤ ∫ z, (L : ℝ) * (‖z‖ * ‖K z‖) * ‖f‖ := by
      apply norm_integral_le_of_norm_le ((hKm.const_mul L).mul_const ‖f‖)
      filter_upwards with z
      rw [norm_smul]
      calc
        _ ≤ ‖K z‖ * (((L : ℝ) * ‖z‖) * ‖f‖) :=
          mul_le_mul_of_nonneg_left (result12 χ hχ z f) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_mul_const, integral_const_mul]

#print axioms Verification.Core02.result01
#print axioms Verification.Core02.result02
#print axioms Verification.Core02.result03
#print axioms Verification.Core02.result04
#print axioms Verification.Core02.result05
#print axioms Verification.Core02.result06
#print axioms Verification.Core02.result07
#print axioms Verification.Core02.result08
#print axioms Verification.Core02.result09
#print axioms Verification.Core02.result10
#print axioms Verification.Core02.result11
#print axioms Verification.Core02.result12
#print axioms Verification.Core02.result13
#print axioms Verification.Core02.result14
#print axioms Verification.Core02.result15
#print axioms Verification.Core02.object01
#print axioms Verification.Core02.object02
#print axioms Verification.Core02.object03
#print axioms Verification.Core02.object04
#print axioms Verification.Core02.type01
#print axioms Verification.Core02.type02
#print axioms Verification.Core02.inst01

end Verification.Core02
