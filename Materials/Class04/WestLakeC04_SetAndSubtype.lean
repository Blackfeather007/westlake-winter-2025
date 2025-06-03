import Mathlib.Tactic

/-
# 1 **Lean**中的集合
-/

/-
## 1.1 集合的定义
-/

/-
引入: 集合论中的集合并不完美, 比如陈老师第一节课举过的例子, 集合下界有两种定义方式, 对于一个集合`X`的幂集`𝒫(X)`, 如果把空集分别视作其子集和元素, 得到的结论并不相同.

在**Lean**中, 类型并不是集合论中所述的集合, 比如`0 ∈ ℕ`在集合论中被视作一个命题, 因此我们也有`(1, 3) ∈ ℕ`, 尽管这是一个假命题. 但在类型论中, `0 : ℕ`可以被理解成类似的意思, 但`(1, 3) : ℕ`的这个写法是从根本上没有意义的, 无关对错. 换句话说, 类型更像是一种本质属性, 而非判断或者说陈述.

我们也想在**Lean**中定义集合, 一个观点或许能比较好地做到这一点. 假设现在已经有了一个集合`s`, 考虑表达式`a ∈ s`, 这应当仍然是一个命题, 即`a ∈ s : Prop`. 现在我们对所有可以谈论与集合`s`之间属于关系的元素考虑一个函数, `fun x => x ∈ s`, 这是我们前文提到过的依赖函数. 但注意, 在**Lean**中, 一个函数的自变量应来自同一类型`α`, 因此我们只能对某个类型上的元素来谈论它是否属于某个集合`s`. 换句话说, 一个集合的定义应当依赖于某个类型.
-/
section definition_of_set
variable (α : Type)
#check Set α      -- Set α : Type
#print Set        -- def Set.{u} : Type u → Type u := fun α => α → Prop

example : (Set α) = (α → Prop) := by rfl

variable (s : Set α)

#check s          -- s : Set α

/- **Question** 如何定义一个包含这个类型全部元素的集合? -/
def SET' : Set α := sorry
end definition_of_set

/-
## 1.2 集合的相关属性
-/
section properties_of_set
/-
### 1.2.1 属于关系
-/
variable (α : Type) (a : α) (s : Set α)

#check a ∈ s      -- a ∈ s : Prop

example : (a ∈ s) = (s a) := by rfl

#check a ∉ s      -- a ∉ s : Prop

example : (a ∉ s) = ¬(a ∈ s) := by rfl

/-
### 1.2.2 子集关系
-/

variable (t : Set α)

#check s ⊆ t      -- s ⊆ t : Prop

example : (s ⊆ t) = (∀ ⦃x : α⦄, x ∈ s → x ∈ t) := by rfl
/-
Strict-implicit binder, like `⦃x y : A⦄` or `⦃x y⦄`. In contrast to `{ ... }` implicit binders, strict-implicit binders do not automatically insert a `_` placeholder until at least one subsequent explicit parameter is specified. Do not use strict-implicit binders unless there is a subsequent explicit parameter. Assuming this rule is followed, for fully applied expressions implicit and strict-implicit binders have the same behavior.

Example: If `h : ∀ ⦃x : A⦄, x ∈ s → p x` and `hs : y ∈ s`, then `h` by itself elaborates to itself without inserting `_` for the `x : A` parameter, and `h hs` has type `p y`. In contrast, if `h' : ∀ {x : A}, x ∈ s → p x`, then `h` by itself elaborates to have type `?m ∈ s → p ?m` with `?m` a fresh metavariable.
-/

example (h₁ : s ⊆ t) (x : α) (h₂ : x ∈ s) : x ∈ t := by
  exact h₁ h₂

/-
### 1.2.3 交集
-/

#check s ∩ t      -- s ∩ t : Set α

example : (s ∩ t) = (fun x => x ∈ s ∧ x ∈ t) := by rfl
-- example : (s ∩ t) = (fun x => x ∈ t ∧ x ∈ s) :=
--   by rfl
  /-
  tactic 'rfl' failed, the left-hand side
    s ∩ t
  is not definitionally equal to the right-hand side
    fun x => x ∈ t ∧ x ∈ s
  -/

example : (a ∈ s ∩ t) = (a ∈ s ∧ a ∈ t) := by rfl

example (h : a ∈ s ∩ t) : a ∈ s := by
  rcases h with ⟨mem_s, mem_t⟩
  exact mem_s
example (h : a ∈ s ∩ t) : a ∈ s := by
  exact h.left
example (h₁ : a ∈ s) (h₂ : a ∈ t) : a ∈ s ∩ t := by
  constructor
  · exact h₁
  · exact h₂
/-
### 1.2.4 并集
-/

#check s ∪ t      -- s ∪ t : Set α

example : (s ∪ t) = (fun x => x ∈ s ∨ x ∈ t) := by rfl

example : (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) := by rfl

example (r : Set α) (h : a ∈ s ∪ t) (h₁ : s ⊆ r) (h₂ : t ⊆ r) : a ∈ r := by
  rcases h with mem_s | mem_t
  · exact h₁ mem_s
  · exact h₂ mem_t

example (h : a ∈ s) : a ∈ s ∨ a ∈ t := by
  left
  exact h
/-
### 1.2.5 差集
-/

#check s \ t      -- s \ t : Set α

example : (s \ t) = (fun x => x ∈ s ∧ x ∉ t) := by rfl

example : (a ∈ s \ t) = (a ∈ s ∧ a ∉ t) := by rfl

example (h : a ∈ s \ t) : a ∉ t := by
  exact h.right

example (h₁ : a ∈ s) (h₂ : a ∉ t) : a ∈ s \ t := by
  exact ⟨h₁, h₂⟩

/-
### 1.2.6 补集
-/

#check sᶜ         -- sᶜ : Set α

example : sᶜ = (fun x => x ∉ s) := by rfl

example : (a ∈ sᶜ) = (a ∉ s) := by rfl

example (h₁ : a ∈ s) (h₂ : a ∈ sᶜ) : 1 = 2 := by
  exfalso
  exact h₂ h₁
example (h : a ∉ t) (h₂ : s ⊆ t) : a ∈ sᶜ := by
  intro mem_s
  apply h
  exact h₂ mem_s
end properties_of_set


/-
## 1.3 全集与空集
-/
section univ_and_empty
axiom α : Type

def SET'' : Set α := fun x => True
def SET : Set α := fun _ => True

example : ∀ x : α, x ∈ SET := by
  intro x
  exact trivial

#check Set.univ     -- Set.univ.{u} {α : Type u} : Set α
example : ∀ x : α, x ∈ Set.univ := by
  intro x
  exact trivial


def EMPTY' : Set α := fun x => False
def EMPTY : Set α := fun _ => False

example : ∀ x : α, x ∉ EMPTY := by
  intro x mem_empty
  exact mem_empty

#check ∅              -- ∅ : ?m.3167
#check (∅ : Set α)    -- ∅ : Set α
example : ∀ x : α, x ∉ (∅ : Set α) := by
  intro x mem_empty
  exact mem_empty
end univ_and_empty


/-
## 1.4 集合构建符号
-/
section set_builder
variable (α : Type) (p : α → Prop)

#check {x : α | p x}          -- {x | p x} : Set α

#check {x | ∃ n, 2 * n = x}   -- {x | ∃ n, 2 * n = x} : Set ℕ
#check {2 * n | n}            -- {x | ∃ n, 2 * n = x} : Set ℕ
end set_builder


/-
## 1.5 函数与集合
-/
section function
variable (α β : Type) (s : Set α) (f : α → β)

#check f '' s     -- f '' s : Set β

example (b : β) : (b ∈ f '' s) = (∃ a ∈ s, f a = b) := by rfl

variable (t : Set β)

#check f ⁻¹' t    -- f ⁻¹' t : Set α

example (a : α) : (a ∈ f ⁻¹' t) = (f a ∈ t) := by rfl
end function


/-
## 1.6 全称命题和存在命题相关的语法糖
-/
section sugar
example (p : ℕ → Prop) : (∀ x > 0, p x) = (∀ x, x > 0 → p x) := by rfl
example (p : ℕ → Prop) : (∃ x > 0, p x) = (∃ x, x > 0 ∧ p x) := by rfl
end sugar

/-
# 2 子类型
-/
section subtype
/-
## 2.1 引入和基本定义
-/
variable (α : Type) (s : Set α)

variable (a : s)    -- 竟然没有报错!!

#check a            -- a : ↑s

variable (p : α → Prop) (a : {x : α // p x})

#check a.val        -- ↑a : α
#check a.property   -- a.property : p ↑a
#check a.1          -- ↑a : α
#check a.2          -- a.property : p ↑a

#check Subtype.val          -- Subtype.val.{u} {α : Sort u} {p : α → Prop} (self : Subtype p) : α
#check Subtype.property     -- Subtype.property.{u} {α : Sort u} {p : α → Prop} (self : Subtype p) : p ↑self


/-
## 2.2 多层子类型嵌套定义
-/
#check ℝ                    -- ℝ : Type
#check {x : ℝ // x ≥ 0}     -- { x // x ≥ 0 } : Type

variable (y : {x : ℝ // x ≥ 0})

#check y.val                -- ↑y : ℝ
#check y.property           -- y.property : ↑y ≥ 0

#check {x : {x : ℝ // x ≥ 0} // x.val > 0}  -- { x // ↑x > 0 } : Type
variable (z : {x : {x : ℝ // x ≥ 0} // x.val > 0})

#check z.val                -- ↑z : { x // x ≥ 0 }
#check z.property           -- z.property : ↑↑z > 0

#check z.val.val            -- ↑↑z : ℝ
#check z.val.property       -- (↑z).property : ↑↑z ≥ 0


variable (t : Set s) (x : t)

#check x.val            -- ↑x : ↑s
#check x.property       -- x.property : ↑x ∈ t
#check x.val.val        -- ↑↑x : α
#check x.val.property   -- (↑x).property : ↑↑x ∈ s
end subtype

/-
# 3 类型转换
-/
section coercion
def f : ℝ → ℝ := fun x => x + 1

#check f (1 : ℕ)    -- f ↑1 : ℝ

/-
(1) `↑`. `↑x` represents a coercion, which converts `x` of type `α` to type `β`, using typeclasses to resolve a suitable conversion function. You can often leave the `↑` off entirely, since coercion is triggered implicitly whenever there is a type error, but in ambiguous cases it can be useful to use `↑` to disambiguate between e.g. `↑x + ↑y` and `↑(x + y)`.
(2) `↥`. `↥ t` coerces `t` to a type.
(3) `⇑`. `⇑ t` coerces `t` to a function.
-/

#check 1
#check (1 : ℚ)
#check (1 : ℝ)
end coercion



/-
# 4 Tactic 及练习
-/
section tactics
/-
## 4.1 `ext`
-/
variable (α : Type) (s t : Set α)

example (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  /-
  α : Type
  s t : Set α
  h : ∀ (x : α), x ∈ s ↔ x ∈ t
  ⊢ s = t
  -/
  ext x
  /-
  α : Type
  s t : Set α
  h : ∀ (x : α), x ∈ s ↔ x ∈ t
  x : α
  ⊢ x ∈ s ↔ x ∈ t
  -/
  exact h x

#check Set.ext    -- Set.ext.{u} {α : Type u} {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b

example (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  apply Set.ext
  intro x
  exact h x
/-
# 4.2 `linarith` & `nlinarith`
-/
example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  linarith

example {a b c d : ℝ} (h1 : a < b) (h2 : b ≤ c) (h3 : c = d) : a + a < d + b := by
  linarith -- linarith can solve this obvious inequality

example {n : ℕ} (h : n = 5) : ¬n = 1 := by
  linarith

example (x y z : ℚ) (h1 : 2 * x < 3 * y) (h2 : - 4 * x + 2 * z < 0)
    (h3 : 12 * y - 4 * z < 0) : False := by
  linarith

example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  linarith

example {x y : ℝ} (h1 : x = 5) (h2 : 1 ≤ y) : x * y + x ≥ 10 := by
  rw [h1] -- 如果删掉这行, `linarith`就会失败, 因为它只能处理线性计算, 而乘法不是线性计算. (注意区分数乘和乘法).
  linarith

example {α: Type*} [LinearOrderedCommRing α] (x : α) (h: x < x) : False := by
  linarith

example {x : ℝ} (h : x ≤ -3) : x ^ 2 ≥ 9 := by
  nlinarith

/-
## 4.3 `norm_num`
-/
example : (1 : ℝ) + 1 = 2 := by
  norm_num

example : (1 : ℚ) + 1 ≤ 3 := by
  norm_num

example : (1 : ℤ) + 1 < 4 := by
  norm_num

example : (1 : ℂ) + 1 ≠ 5 := by
  norm_num

example : (1 : ℕ) + 1 ≠ 6 := by
  norm_num

example : ¬ (5 : ℤ) ∣ 12 := by
  norm_num

example : (3.141 : ℝ) + 2.718 = 5.859 := by
  norm_num

example : 3.141 + 2.718 = 5.859 := by
  norm_num    -- `norm_num`不能处理浮点数.
  sorry

example : |(3 : ℝ) - 7| = 4 := by
  norm_num    -- `norm_num`也可以处理绝对值.

example {x : Nat} : x + 0 = x := by
  norm_num    -- `norm_num`有时会调用`simp`, 比如这个目标并不是纯数值表达式, 但`norm_num`仍然可以处理.

/-
## 4.4 `positivity`
-/
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by
  positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3 : ℤ) + a| := by
  positivity

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a * a * b * c - a * b * d = 0) : a * c = d := by
  -- positivity
  sorry

example : 0 < 5 - (-3) := by
  -- positivity
  sorry

example : ¬ (5 : ℤ) ∣ 12 := by
  -- positivity
  sorry

example (x : ℝ) (hx : 0 < x) : 0 < 5 - (-x) := by
  -- norm_num
  -- positivity -- `positivity` 失败了!
  sorry

/-
## 4.5 `ring`/`ring_nf`/`noncomm_ring` & `group`/`abel`
-/
example {x y : ℤ} : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (x y : ℝ) (f : ℝ → ℝ) : f (x + y) + f (y + x) = 2 * f (x + y) := by
  ring_nf

example (x y : ℤ) (h : (x - y) ^ 2 = 0) : x ^ 2 + y ^ 2 = 2 * x * y := by
  rw [← add_zero (2 * x * y), ← h]
  ring

example (x y : ℕ) : x * 2 + id y = y + 2 * id x := by
  rw [id, id]
  ring

example {R : Type} [Ring R] (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + a * b + b * a := by
  noncomm_ring

/-
## 4.6 `field_simp`
-/
example (x : ℝ) (h : x > 0) : 1 / x + 1 = (x + 1) / x := by
  field_simp
  ring

example (x: ℝ) (h1: x > 0) : (1 - x) / √x = 1 / √x - √x  := by
  field_simp

example {a b : ℝ} (h : b ≠ 1) : a = (a * b - a) / (b - 1) := by
  field_simp [sub_ne_zero_of_ne h]
  ring

/-
## 4.7 `norm_cast` & `push_cast`
-/
example (a b : ℤ) (h : (a : ℚ) + b < 10) : a + b < 10 := by
  norm_cast at h

example (a b : Nat)
    (h1 : ((a + b : Nat) : Int) = 10)
    (h2 : ((a + b + 0 : Nat) : Int) = 10) :
    ((a + b : Nat) : Int) = 10 := by
  /-
  h1 : ↑(a + b) = 10
  h2 : ↑(a + b + 0) = 10
  ⊢ ↑(a + b) = 10
  -/
  push_cast
  /- Now
  ⊢ ↑a + ↑b = 10
  -/
  push_cast at h1
  push_cast [Int.add_zero] at h2
  /- Now
  h1 h2 : ↑a + ↑b = 10
  -/
  exact h1

/-
## 4.8 `omega`
-/
example : x ≥ 1 → x + 1 ≤ 2 * x := by omega

example : x ≥ 2 → x / 2 ≤ x - 1 := by omega

example : 5 % 2 = 1 := by omega

example (x : ℕ) (h : Odd x) : x % 2 ≠ 0 := by
  rw [Odd] at h
  omega

example (x : Nat) : x * (x + 1) % 2 = 0 := by
  have h : Even (x * (x + 1)) := by
    exact Nat.even_mul_succ_self x
  rw [Even] at h
  omega
end tactics



section examples
variable (α : Type) (s t u : Set α)
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x mem_inter
  rcases mem_inter with ⟨mem_s, mem_u⟩
  constructor
  · exact h mem_s
  · exact mem_u

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨mem_s, mem_u⟩
  exact ⟨h mem_s, mem_u⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨mem_s, mem_u⟩ => ⟨h mem_s, mem_u⟩
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨mem_s, mem_u⟩ => ⟨h mem_s, mem_u⟩
end examples



section exercise₁
variable (α : Type) (s t u : Set α)
/- 请尽量少使用 tactic 且不使用`constrcutor`完成以下四个题目. -/
example : s ∩ (s ∪ t) = s := sorry
example : s ∪ s ∩ t = s := sorry
example : s \ t ∪ t = s ∪ t := sorry
example (h : s ⊆ t) : s \ u ⊆ t \ u := sorry


/- 以下四个题目允许使用 tactic 或搜索定理来完成证明, 但仍请做到结构尽量精简. -/
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  sorry

variable (f : α → β) (v : Set β)
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
end exercise₁



section exercise₂
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x ^ 2 + d / x ^ 3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  sorry

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example {n m : ℕ} : (n + m) ^ 3 = n ^ 3 + m ^ 3 + 3 * m ^ 2 * n + 3 * m * n ^ 2 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  set x := (b - a + c) / 2 with hx_def
  set y := (a - b + c) / 2 with hy_def
  set z := (a + b - c) / 2 with hz_def
  sorry

example (x : ℕ) (h : (x : ℚ) = 1) : x = 1 := by
  sorry

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by
  sorry

example (x : ℕ) : x ≥ 2 → x / 2 ≥ 1 := by
  sorry
end exercise₂
