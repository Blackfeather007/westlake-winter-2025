import Mathlib.Tactic

/-
# 第一部分
-/

/-
1. 陈述并证明1 + 1 = 2
2. 陈述并证明实数x ≤ y, y ≤ z 则x ≤ z
3. 陈述并证明实数a，b的最小值小于等于a
4. 在实数集上陈述并证明完全平方公式
5. 在实数集上陈述并证明平方差公式
-/
/-
# 第二部分
-/

open Nat Real
variable {a b c d e : ℝ}
variable {x y z w : ℤ}

/-
# apply/exact
-/
example (a b c : ℕ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (a b : ℝ) (h : a ≤ b ∧ -a ≤ b) : |a| ≤ b := by
  apply abs_le'.2 h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (x y z : ℤ) : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example (x y z w : ℤ) (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

example (a b : ℝ) : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    apply min_le_left
  · apply le_min
    · apply min_le_right
    apply min_le_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right

/-
# rw
-/

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℕ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

example {a b : ℝ} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

/-
# ring
-/
example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  ring_nf at h
  rw [← add_zero (2 * x * y), ← h]
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

/-
# have
-/

example {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  apply pow_eq_zero h'

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    have h' : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    rw [h']
    exact sq_nonneg (a - b)
  linarith

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
  calc
    a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff h]
    apply fact1
  rw [le_div_iff h]
  apply fact2

/-
# simp
-/
example {α : Type} {x : α} {s t : Set α} (h1 : x ∈ s) (h2 : x ∈ t) : x ∈ s ∩ t := by
  simp only [Set.mem_inter_iff]
  constructor
  · exact h1
  · exact h2

example {α : Type} {x : α} {s t : Set α} (h1 : x ∈ {a | a ∈ s}) (h2 : x ∈ {a | a ∈ t}) : x ∈ s ∩ t := by
  simp only [Set.mem_inter_iff]
  simp at h1 h2
  constructor
  · exact h1
  · exact h2
