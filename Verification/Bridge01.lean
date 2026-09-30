import Mathlib

namespace Verification.Bridge01


theorem result01
    {delta a b c : ℝ}
    (hdelta : delta = a - b)
    (hc : c = a - delta) :
    c = b := by
  rw [hc, hdelta]
  ring


theorem result02
    {x y q : ℝ}
    (hxy : x = y - q) :
    q = y - x := by
  linarith


theorem result03
    {X : Type*}
    (F : (X → ℝ) → ℝ)
    (p q : X → ℝ)
    (delta c : ℝ)
    (hdelta : delta = F p - F q)
    (hc : c = F p - delta) :
    c = F q := by
  exact result01 hdelta hc


theorem result04
    {q f j B total : ℝ}
    (hf : 0 ≤ f)
    (hj : 0 ≤ j)
    (hB : j ≤ B)
    (hq : |q| ≤ 4 * f * j)
    (htotal : f ≤ total) :
    |q| ≤ 4 * B * total := by
  have hB0 : 0 ≤ B := hj.trans hB
  calc
    |q| ≤ 4 * f * j := hq
    _ ≤ 4 * f * B := by
      gcongr
    _ ≤ 4 * total * B := by
      gcongr
    _ = 4 * B * total := by ring

#print axioms Verification.Bridge01.result01
#print axioms Verification.Bridge01.result02
#print axioms Verification.Bridge01.result03
#print axioms Verification.Bridge01.result04

end Verification.Bridge01
