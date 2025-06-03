import Mathlib.Tactic
import Mathlib.Data.Real.Irrational

/-
# 更多的类型论
-/

/-
# Term, Type和universe
-/
#check 1
#check (1 : ℝ)
#check √2
#check 2 + 2
#check 2 + 2 = 4
#check mul_comm

#check ℕ    -- ℕ : Type
#check ℝ    -- ℝ : Type
#check Prop -- Prop : Type

#check Type

section a
#check 1
variable (p : Prop)

example (h : p) : p := by
  exact h

#check ℕ

example {α : Type} (a : Set ℕ) (x : ℕ) : x ∈ a ∨ x ∉ a := by sorry

end a



#check mul_assoc
#check Nat.mul_assoc
#check Int.mul_assoc
/-
# 定理的陈述以及函数类型简介
-/


/-
1. ∀ α β 是任意的类型, 都可以构造α → β， 任意有限多的类型也一样
2. 如果有类型 α → β, 有 f : α → β ,a : α， 那么 f a : β
如果有 f : α → β → γ， a : α, 那么 f a : β → γ
-/

example (f : ℤ → ℤ) (h : ∀ x, f x = x) : f 1 = 1 := by sorry

theorem function_type {p q : Prop} (hp : p) (hq : q) : p ∧ q := by sorry

theorem function_type' {p q : Prop} : p → (q → (p ∧ q)) := by sorry

theorem function_type'' : ∀ {p q : Prop}, p → (q → (p ∧ q)) := by sorry

#check Set.mem_union
#check add_le_add

/-
# Term proof
1. 证明一个定理等价于给出一个要求的term
2. 使用term proof有时可以使得代码更为简洁
3. 在需要证明的定理非常复杂时，term proof则会比较难用
-/

example (a b : ℝ) : a + b = b + a := add_comm a b

example (a b c d e f : ℝ) (h₁ : b * d = f * e) (h₂ : f * c = 1) : a * b * c * d = a * e :=
    (mul_assoc (a * b) c d).symm ▸ (mul_comm d c) ▸ (mul_assoc (a * b) d c) ▸ (mul_assoc a b d).symm ▸ h₁.symm ▸ (mul_comm e f) ▸ (mul_assoc a e f) ▸ (mul_assoc (a * e) f c).symm ▸ h₂.symm ▸ (mul_one (a * e))

example (a b c d e f : ℝ) (h₁ : b * d = f * e) (h₂ : f * c = 1) : a * b * c * d = a * e := by
  have h1 : a * b * c * d = a * c * (b * d) := by ring
  have h2 : a * c * (f * e) = a * e * (f * c) := by ring
  rw [h1, h₁, h2, h₂, mul_one]

namespace westlake

theorem one_eight (a : ℝ) : a = a := by sorry



/-
# suffices, assumption 和 refine
1. suffices可以替代have使用
2. assumption会自动搜索匹配目标的假设
3. refine可以替代apply使用
-/
example (P Q R : Prop) (h₁ : P → R) (h₂ : Q) (h₃ : Q → P) : R := by
  suffices h : Q from by
    apply h₁
    apply h₃
    exact h
  exact h₂

example (P Q R : Prop) (h₁ : P → R) (h₂ : Q) (h₃ : Q → P) : R := by
  have h : Q := by
    exact h₂
  exact h₁ (h₃ h)

example (a b : ℝ) (h : a = b) : a = b := by
  assumption

#check add_assoc
example (a b c : ℝ) : a + b + c = a + (b + c) := by
  apply add_assoc

example (P Q R : Prop) (h1 : P) (h2 : Q) (h3 : P → R) : Q ∧ R := by
  constructor
  · exact h2
  · apply h3 h1

example (P Q R : Prop) (h1 : P) (h2 : Q) (h3 : P → R) : Q ∧ R := by
  refine ⟨h2, h3 h1⟩

example (p q r t : Prop) (h1 : p → q) (h2 : q → r) (h3 : p) (h4 : t) : r ∧ t := by
  refine ⟨?_, h4⟩
  exact h2 (h1 h3)

/-
# calc
1. calc可以将复杂的运算分步进行
2. calc可以处理等式与不等式问题
-/
open Real
#check exp_log
example (x y : ℝ) (h1 : 0 < x) (h2 : 0 < y) (h : log x = log y) : x = y := by
  calc
    _ = exp (log x) := by
      rw [exp_log h1]
    _ = exp (log y) := by
      rw [h]
    _ = _ := by
      rw [exp_log h2]

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have : a ^ 2 + b ^ 2 - 2 * a * b ≥ 0 := by
    calc
      _ = (a - b) ^ 2 := by ring
      _ ≥ 0 := by linarith [pow_two_nonneg (a - b)]
  linarith
