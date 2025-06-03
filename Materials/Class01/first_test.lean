import Mathlib.Tactic

/-
# 第一部分
-/

/-
你可能会用到的定理
-/
#check one_add_one_eq_two
#check le_trans
#check mul_add
#check add_mul
#check two_mul
#check add_assoc
#check add_comm
#check add_sub_right_comm

/-
1. 陈述并证明1 + 1 = 2
2. 陈述并证明实数x ≤ y, y ≤ z 则x ≤ z
3. 陈述并证明实数a，b的最小值小于等于a
4. 在实数集上陈述并证明完全平方公式
5. 在实数集上陈述并证明平方差公式
-/

/-
# 第二部分
需要用到的定理已经全部#check在例子前，如果没有#check，请在前文中寻找，或者根据已有的定理猜测命名
-/

open Nat Real
variable {a b c d e : ℝ}
variable {x y z w : ℤ}

/-
# apply/exact
-/

#check mul_assoc
example (a b c : ℕ) : a * b * c = a * (b * c) := by sorry

#check abs_le
example (a b : ℝ) (h : a ≤ b ∧ -a ≤ b) : |a| ≤ b := by sorry

#check add_lt_add_of_lt_of_le
#check exp_lt_exp
#check le_refl
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by sorry

#check dvd_mul_of_dvd_left
#check dvd_mul_left
example (x y z : ℤ) : x ∣ y * x * z := by sorry

#check dvd_add
#check pow_two
example (x y z w : ℤ) (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by sorry

#check le_antisymm
#check le_min
#check min_le_right
example (a b : ℝ) : min a b = min b a := by sorry

example : min (min a b) c = min a (min b c) := by sorry
/-
# rw
-/

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by sorry

example (a b c : ℕ) : a * b * c = b * (a * c) := by sorry

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by sorry

#check sub_self
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by sorry

#check neg_add_cancel_left
example {a b : ℝ} (h : a + b = 0) : -a = b := by sorry

/-
# ring
-/
example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by sorry

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by sorry


/-
# have
-/

#check pow_eq_zero
#check pow_two_nonneg
example {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by sorry

theorem aux : min a b + c ≤ min (a + c) (b + c) := by sorry

--你可以尝试使用aux来完成这一证明
#check le_antisymm
#check add_le_add_right
#check sub_eq_add_neg
example : min a b + c = min (a + c) (b + c) := by sorry

#check pow_two_nonneg
theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by sorry

theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by sorry

--你可以尝试使用fact1，fact2来完成这一证明
#check abs_le
#check le_div_iff
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by sorry

/-
# simp
-/
example {α : Type} {x : α} {s t : Set α} (h1 : x ∈ s) (h2 : x ∈ t) : x ∈ s ∩ t := by
  simp only [Set.mem_inter_iff]
  sorry

example {α : Type} {x : α} {s t : Set α} (h1 : x ∈ {a | a ∈ s}) (h2 : x ∈ {a | a ∈ t}) : x ∈ s ∩ t := by sorry
