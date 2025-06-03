import Mathlib


/-
结构

**结构**是对一组数据形式的约定，可能还包含数据需要满足的约束条件。结构的**实例**是一组满足这些约束条件的特定数据。
-/

noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

/-
@[ext] 告诉 Lean 自动生成一些定理，这些定理可用于证明当两个结构实例的每部分信息分别相等时，这两个实例相等，这一性质称为**外延性**。
-/
#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  exact hx
  exact hy
  exact hz

/-
定义 `Point` 结构的特定实例
-/

def myPoint1 : Point where -- := + 下划线
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4 -- .mk 构造函数

def myPoint4 : Point := by
  constructor
  exact 2
  exact -1
  exact 4

/-
构造函数的重命名
-/
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

/-
定义结构上的函数
-/

#check Point.x
#check Point.y
#check Point.z

#check myPoint1
#check Point.x myPoint1
#check myPoint1.x

/-
通常，我们会将与 `Point` 这样的结构相关的定义和定理放在同名的命名空间中, 和 `Point.mk`, `Point.x` 具有相同的格式.
-/
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/-
证明性质
-/
namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add] -- 展开定义
  ext <;> dsimp -- 将两个元素之间的等式简化为组件之间的等式。
  apply add_comm
  apply add_comm
  apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

/-
使用模式匹配在结构上定义函数
-/
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  sorry

end Point

/-
结构不仅可以指定数据类型，还可以指定数据必须满足的约束条件.
-/

/-
这个集合是三维空间中顶点为 (1, 0, 0)、(0, 1, 0) 和 (0, 0, 1) 的等边三角形及其内部。
-/
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def swapXY (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  sorry

end

end StandardTwoSimplex

open BigOperators
/-
类型的定义可以包含参数
-/
structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex

/-
将属性捆绑在一起而不包含数据
-/
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

/-
结构并不是将数据捆绑在一起的唯一方式. `product` `and` `subtype`
-/
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

/-
子类型
-/
structure PReal' where
  val : ℝ
  property : 0 < val

#check Subtype

def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

end

/-
**代数结构**
-/

/- Try LeanSearch-/
/-
1. 一个偏序集由一个集合 P 和一个在 P 上的二元关系 ≤ 组成，该关系是传递的和自反的。一个群由一个集合 G
和一个结合的二元运算、一个单位元 e 以及一个为每个 G 中元素 x 返回逆元的函数组成。如果该运算是交换
的，则该群是阿贝尔群或交换群。
2. 一个格是一个带有交和并的偏序集。
3. 一个环由一个（加法写作的）阿贝尔群 R 连同结合的乘法运算和单位元 1 组成，使得乘法对加法分配。如果乘
法是交换的，则该环是交换环。
4. 一个有序环 R 由一个环连同其元素上的偏序组成，使得对于 R 中的每个 a、b 和 c，a ≤ b 意味着 a + c ≤ b + c，
并且 0 ≤ a 和 0 ≤ b 意味着 0 ≤ ab。
5. 一个度量空间由一个集合 X 和一个函数 d : X × X → R 组成，满足以下条件：
(a) 对于 X 中的每个 x 和 y，d(x, y) ≥ 0。
(b) d(x, y) = 0 当且仅当 x = y。
(c) 对于 X 中的每个 x 和 y，d(x, y) = d(y, x)。
(d) 对于 X 中的每个 x、y 和 z，d(x, z) ≤ d(x, y) + d(y, z)。
6. 一个拓扑空间由一个集合 X 和一个 X 的子集集合 τ 组成，称为 X 的开子集，满足以下条件：
(a) 空集和 X 是开的。
(b) 两个开集的交是开的。
(c) 任意开集的并是开的。
-/

#check Preorder

/-
共同点: 在这些例子中，结构的元素属于一个集合，即载体集，有时它代表整个结构。例如，当我们说“设 \( G \) 是一个群”然后说“设 \( x \in G \)”时，我们使用 \( G \) 来代表结构和它的载体。
-/

/-
群结构 和mathlib定义数学上相同
-/
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

/-
构造一个群: 置换群
-/
section
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β

-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

/-
Coercion from `Equiv α β` to `α → β`
-/
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

/-
置换群
-/
example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

/-
Mathlib中的实现
-/
section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

/-
之所以可以直接应用群的定理,是因为:
1. **逻辑**。一个应该在任何群中解释的定义将群的类型和群结构作为参数。类似地，关于任意群元素的定理以对群的类型和群结构的全称量词开始。
2. **隐式参数**。类型和结构的参数通常被隐式化，因此我们不必编写它们或在 Lean 信息窗口中看到它们。Lean 会默默地为我们填充这些信息。
3. **类型类 (type-class) 推断**。也称为类推断，这是一种简单但强大的机制，使我们能够注册信息供 Lean 以后使用。当 Lean 被要求填充定义、定理或符号的隐式参数时，它可以使用已注册的信息。
-/

-- structure
class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

-- def
instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check Group₂.mul -- 隐式参数

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

/-
默认值的类型类
-/
#check Inhabited

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

/-
取第一个元素,空列表返回默认值
-/
example : ([] : List Point).headI = default :=
  rfl

/- 符号类 -/
instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
