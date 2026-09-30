import Mathlib

example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
