import Mathlib.Tactic

/-
# 一点点类型论
1. 任何东西都有类型！
-/

#check 1         --1 : ℕ
#check (1 : ℝ)   -- 1 : ℝ
#check √2        -- √2 : ℝ
#check 2 + 2     -- 2 + 2 : ℕ
#check 2 + 2 = 4 -- 2 + 2 = 4 : Prop
#check mul_comm  -- mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a

/-
# 第一个例子
-/
theorem The_frist_example {G : Type*} [Group G] {a b c d e f : G} (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  exact mul_assoc c d f

theorem /-name-/The_frist_example' /-parameters-/{G : Type*} [Group G] (a b c d e f : G) (h : a * b = c * d) (h' : e = f) : /-goal-/a * (b * e) = c * (d * f) := by/-proof-/
  rw [h']
  rw [← mul_assoc]
  rw [h]
  exact mul_assoc c d f

/-
# 隐式参数与显式参数
1. 花括号表示隐式参数，圆括号表示显式参数
2. 函数需要填入参数才能返回结论
3. 隐式参数不需要填入，显式参数需要填入
-/
theorem my_lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans
  apply h1
  apply h2

--#check (my_lt_trans : ∀ {a b c : ℕ}, a < b → b < c → a < c)

theorem one_lt_two' : 1 < 2 := by sorry
theorem two_lt_three' : 2 < 3 := by sorry

#check lt_trans one_lt_two' two_lt_three' --lt_trans one_lt_two' two_lt_three' : 1 < 3
--example : 1 < 3 := lt_trans one_lt_two' two_lt_three'

/-
# 定义的陈述
1. 格式类似于定理的陈述
-/
def div_two {a : ℤ} (h : Even a) : ℤ := a / 2

/-
# structure 和 class
1. 两者都实现了信息的打包
2. 方括号表示使用了一个class的信息
3. instance可以对class的内容进行举例，可以使用#synth来检查
-/

structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

class PreOrder' (α : Type*) where
  le : α → α → Prop
  le_refl : ∀ a : α, le a a
  le_trans : ∀ a b c : α, le a b → le b c → le a c

instance : PreOrder' ℕ  where
  le := sorry
  le_refl := sorry
  le_trans := sorry

#synth PreOrder' ℕ

/-
# 定理的证明
-/

/-
# exact 和 rfl
1. exact通过使用定理，来证明和定理结论完全一致的目标
2. rfl能够证明两侧相等的等式
-/

#check mul_assoc
example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (x y : ℝ) : x + 37 * y = x + 37 * y := by rfl


/-
# apply， rw 和 have
1. apply可以使用一个定理
2. rw可以通过等式来改写当前目标
3. have可以先证明一个引理
-/
#check lt_trans
theorem my_lt_trans' {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans h1 h2

#check lt_trans
-- 强行填入隐式参数
theorem my_lt_trans1 {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans (b := b)
  apply h1
  apply h2

-- 不填入的参数，如果无法自动推断，则成为新的目标
theorem my_lt_trans2 {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans
  apply h1
  apply h2

-- 填入参数需要按照顺序，可以使用占位符来跳过，跳过的部分会变成新的目标
theorem my_lt_trans3 {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans ?_ h2
  apply h1

example {a b c d : ℝ} (h1 : a = c) (h2 : b = d) : a * b = c * d := by
  rw [h1]
  rw [h2]

#check mul_add
example (a : ℝ) : a * 0 + a * 0 = a * 0 := by
  rw [← mul_add, add_zero]

#check mul_comm
example (a b c : ℝ) : a * (b * c) = b * c * a := by
  rw [mul_comm]

example (a b c : ℝ) : a * (b * c) = a * (c * b) := by
  rw [mul_comm b c]

section a

variable (a b c d e f : ℝ)

#check add_mul
example (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

#check add_left_cancel
example : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

end a

/-
# 与逻辑相关的tactic
-/

/-
# 逻辑学命题出现在目标中
1. 且命题使用constructor拆开
2. 或命题使用left/right来选择
3. 全称量词使用intro来引入
4. 存在量词使用use
5. 否定命题使用push_neg
-/
variable {x y : ℝ}

example (h₀ : x ≤ y) (h₁ : x ≠ y) : x ≤ y ∧ x ≠ y := by
  constructor
  · apply h₀
  · apply h₁

example (h : (y > 0) ∧ (y < 8)) : y > 0 ∨ y < -1 := by
  left
  apply h.left

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := by
  intro a b hab
  apply h
  apply hab

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 3
  constructor
  · norm_num
  · norm_num

example (h : x < 0) : ¬ 0 ≤ x := by
  push_neg
  apply h

/-
# 逻辑命题出现在条件中
1. 且命题使用.left/.right（.1/.2）来获得两个条件
2. 且命题，或命题都可以使用rcases来拆分
-/
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  apply lt_of_le_of_ne
  apply h.left
  apply h.right

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : x < y := by
  rcases h with ⟨h1, h2⟩
  apply lt_of_le_of_ne
  apply h1
  apply h2

example {x : ℝ} (h : x = 3 ∨ x = 5) : x = 3 ∨ x = 5 := by
  rcases h with h | h
  · left
    apply h
  · right
    apply h

example {x : ℝ} (h : ¬ 0 ≤ x) : x < 0 := by
  push_neg at h
  exact h

variable (a b c d : ℝ)

/-
# 自动化证明工具
1. ring解决环的计算问题
2. linarith解决不等式问题
3. simp解决所有问题
-/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring

example : c * b * a = b * (a * c) := by
  ring

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

example {n : ℕ} (h : Nat.Prime n → 2 < n → ¬Even n) : n ∈ {n | Nat.Prime n} ∩ {n | n > 2} → n ∈ {n | ¬Even n} := by
  simp
  exact h

example {α : Type} {s t : Set α} {x : α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  simp only [Set.mem_union]
