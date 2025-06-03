import Mathlib.Tactic

open Real
#help tactic apply

/-
# apply
-/
#check lt_of_le_of_lt --a ≤ b → b < c → a < c
#check lt_trans
example {a b c d e : ℝ} (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

#check le_min
#check add_le_add_right
#check min_le_left
example (a b c : ℝ) : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right


/-
# rw
-/

#check add_neg_cancel_right
example {a b c : ℝ} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

#check pow_two
#check mul_sub
#check mul_comm
#check sub_add
#check sub_sub
#check two_mul
#check mul_assoc
example {a b : ℝ} : (a - b) ^ 2 = a * a - 2 * a * b + b * b := by
  rw [pow_two, mul_sub, sub_mul, sub_mul, mul_comm b a, ← sub_add, mul_assoc, two_mul, sub_sub]

/-
# have
-/

#check pow_two_nonneg
example (a b : ℝ) : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : a ^ 2 + b ^ 2 - a * b * 2 = (a - b) ^  2 := by ring
  have : 0 ≤ a ^ 2 + b ^ 2 - a * b * 2 := by
    rw [h]
    exact pow_two_nonneg (a - b)
  apply le_of_sub_nonneg
  exact this
/-
# ring
-/

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

example (x y : ℝ) (h : (x + y) * (x - y) = 0) : x ^ 2 - y ^ 2 = 0 := by
  ring_nf at h
  exact h

example (a b : ℝ) : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    have h' : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    rw [h']
    exact sq_nonneg (a - b)
  linarith

theorem Cauchy_Schwarz_Ineq (a b c d : ℝ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 := by
    have h' : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    rw [h']
    exact pow_two_nonneg (a * d - b * c)
  apply le_of_sub_nonneg
  exact h

/-
# linarith
-/
example (x y : ℝ) (h : y > x ^ 2) : y > 0 := by
  linarith [pow_two_nonneg x]

example (x y : ℝ) (h : x ^ 2 + y ^ 2 = 0) : x ^ 2 = 0 := by
  linarith [pow_two_nonneg x, pow_two_nonneg y]

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  have : exp (a + d) ≤ exp (a + e) := by
    apply exp_le_exp.2
    linarith
  linarith

example (a b : ℝ) : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    have h' : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    rw [h']
    exact sq_nonneg (a - b)
  linarith

theorem Cauchy_Schwarz_Ineq' (a b c d : ℝ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 := by
    have h' : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    rw [h']
    exact pow_two_nonneg (a * d - b * c)
  linarith
