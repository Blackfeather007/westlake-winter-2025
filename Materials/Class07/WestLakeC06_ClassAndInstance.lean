import Mathlib.Tactic
import Mathlib.Deprecated.Subgroup

/-!
# `structure` 复习

我们复习一下昨天讲的 `structure` 关键词。本质上，使用 `structure` 依然是在定义一个归纳类型，
但该归纳类型只有一个constructor `.mk`，同时Lean能够自动派生出许多辅助函数。

`structure` 十分重要，在定义数学对象、性质时都有着广泛应用。你至少你应当需要掌握以下内容：

- 如何使用 `structure` 关键词定义一个类型
- 如何创建一个使用 `structure` 关键词定义的类型的对象
- 如何使用 `extends` 进行继承
-/

-- 声明 `Point` 类型为具有 `x` `y` 两个属性的结构，其中 `x` `y` 均为 `Nat`
@[ext]
structure Point where
  x : Nat
  y : Nat

#check Point.mk
#check Point.x
#check Point.y
#check Point.ext

#print Point


def p₁ : Point := ⟨1, 2⟩

def p₂ : Point := {
  x := 2
  y := 3
}

def p₃ : Point where
  x := 3
  y := 4

def p₄ : Point := Point.mk 5 6

#eval p₁
#eval p₂

-- 声明 `Point3D` 为 `Point` 的子类，额外多出一个 `z` 属性
structure Point3D extends Point where
  z : Nat

#check Point3D.mk
#check Point3D.z

def p₁' : Point3D := ⟨⟨1,2⟩,3⟩
def p₂' : Point3D where
  toPoint := ⟨2, 3⟩
  z := 4

#print Point3D

#print Subtype

def f : {n // n > 2} → {n // n > 1} := fun n => ⟨n, by linarith [n.property]⟩

#eval f ⟨3, by decide⟩

/-
考虑到有时类型的继承中会出现如下的情形：
    A
  /   \
B       C
  \   /
    D
如若我们不使用 `extends`，而是手动在结构定义中使用 `toB` 和 `toC`，构造时分别提供 `B` 和 `C` 的具体对象，
那么就存在这两个同样继承于 `A` 的对象的 `A` 的字段数据不同的问题。
-/

structure A where
  x : Nat

structure B where
  toA : A
  y   : Nat

structure C where
  toA : A
  z   : Nat

structure D where
  toB : B
  toC : C

#check D.mk

def b : B := ⟨⟨1⟩, 2⟩
def c : C := ⟨⟨2⟩, 3⟩
def d : D := ⟨b, c⟩

#eval d.toB.toA
#eval d.toC.toA

-- `extends` 用一些魔法帮助我们避免了这一问题。

structure B' extends A where
  y : Nat

structure C' extends A where
  z : Nat

structure D' extends B, C

example : ∀ d : D', d.toA = d.toC.toA := by
  intro d
  rfl

/-!
# 类型层级与实例搜索

下面我们介绍 `class` 与 `instance` 关键词，其中大部分概念都雷同于上文所述的 `structure`，
但其使用情境有较大差异。具体而言，可以将 `structure` 声明的类型视为结构体，
在实际使用中会声明多个该类型的不同实例，而用 `class` 声明的类型视为特征，一般都为依赖类型，
其实例表示为某个具体类型实现指定的特征，比如为自然数实现加法和乘法，
就表现为为自然数实现 `Add` 和 `Mul` 这两个 `class` 的实例。

我们先看一下如果直接将一些应当使用 `structure` 声明的承载数据的结构改为用 `class` 声明会发生什么：
-/

class Point' where
  x : Nat
  y : Nat

#check Point'.mk

class Point3D' extends Point' where
  z : Nat

#check Point3D'.mk
#check Point3D'.toPoint'
#check Point3D'.z

instance (priority := 100) : Point3D' where
  x := 1
  y := 1
  z := 1

instance (priority := 50) : Point3D' where
  x := 2
  y := 2
  z := 2

#eval Point3D'.z

/-
可以看到，使用 `class` 进行类继承会导致其构造函数中的父类实例参数变为实例隐式参数，当你使用 `Point3D'.z` 时，
Lean会自动按序搜索 `Point3D'` 实例并填入，导致后续调用 `Point3D.z` 时都会固定搜索到一个实例的值，如果有着需要
使用该类型多个不同实例的情境，那么使用 `class` 定义就并不合适。

随之而来的问题是，我们为何需要 `class`？实际上，在数学证明中会存在许多“约定俗成”的前提条件，比如我们用同一个符号
` * `时，对于不同的参数类型我们指代的实际上是不同的乘法，如果每次都需要我们手动提供，那么会显得非常繁琐。同时，
一个定理的条件可能有数十个，其中大部分都是命题，无法用隐式参数让Lean自动推断。我们希望Lean能够自动搜索相关结论，
而不是人工提供。
-/

instance : Mul Point where
  mul p₁ p₂ := ⟨p₁.x * p₂.x, p₁.y * p₂.y⟩

#eval p₁ * p₂

instance : Add Point where
  add p₁ p₂ := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

#eval p₁ + p₂

-- 证明 `Point` 是一个交换的幺半群
instance : CommMonoid Point where
  mul_assoc := by
    intro a b c
    ext <;> apply mul_assoc
  one := ⟨1, 1⟩
  one_mul
  | ⟨x, y⟩ => by ext <;> apply one_mul
  mul_one := fun ⟨x, y⟩ => by ext <;> apply mul_one
  mul_comm := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => by ext <;> apply mul_comm

/-
构造出以上实例后，Mathlib中所有条件中要求幺半群的定理都可以对 `Point` 使用。

由于Mathlib中的定理多为最general的情形，部分定理并不需要幺半群这么强的条件，但只要实现了
`CommMonoid` 的实例，就相当于实现了其所有父类的实例，Lean能够在调用定理时自动进行搜索转换。
你可以使用 `#synth` 命令查看Lean是否能搜索到某个实例，以及搜索到的是哪个。
-/
#check mul_comm
#check one_mul
#check mul_one

#synth CommMagma Point
#synth CommSemigroup Point
#synth MulOneClass Point
#synth Monoid Point

example (p₁ p₂ : Point) : p₁ * p₂ = p₂ * p₁ := mul_comm p₁ p₂


#check inferInstanceAs (Monoid Point)

instance inst1 : CommSemigroup Point := inferInstance
instance inst2 : CommSemigroup Point := by infer_instance

example : inst1 = inst2 := rfl


section Diamond
/-
以下是一个模拟实际情况中经常出现的Diamond问题实例，当你声明两个看似无交的实例条件时，可能两者存在相同的数据字段，
这一般隐藏于错综复杂的继承关系中。此时Lean在证明中搜索到的对应字段所来源的实例是难以预测的，从而导致一些问题。
-/

#print MulZeroClass
#print AddZeroClass

class AddZeroHaveTwoClass (α : Type*) extends AddZeroClass α where
  two : α

class MulZeroHaveOneClass (α : Type*) extends MulZeroClass α where
  one : α

variable {α : Type*} [MulZeroHaveOneClass α] [AddZeroHaveTwoClass α]

#synth Zero α

example (a : α) : a + 0 = a := by
  -- apply add_zero
  sorry

end Diamond
/-！
下面我们讲解Lean中的 **Coercion**，即**强制类型转换**。一般而言，考虑到Lean的可靠性很大程度上依赖于其类型检查功能，如果
Lean中的对象可以随意转换类型，那显然是无法接受的。但是，如果你无法把一个类型转为另一个类型，或是每次都需要自己
显式地应用一个函数来进行转换，那么又会变得太过繁琐。

在自然语言的语境中，我们在计算时实际上进行了约定俗成的类型转换，比如两个自然数相除变成分数（有理数），或者有理数加
实数变成实数，表现在字面上都是同一套数字，但在Lean中，所有字面量都有着固定的类型，不同类型间进行运算时，如果找不到
类型签名正确的函数，那么Lean就会尝试进行**强制类型转换**。
-/

#check 1 / 2
#check (1 : ℚ) / 2
#check (2 : ℚ) + (3 : ℝ)

#print Coe

-- #check p₁ * p₁'

instance : Coe Point3D Point where
  coe := fun p => ⟨p.1.1, p.1.2⟩

#check p₁ * p₂'
#eval p₁ * p₁'


-- Example for outparam
class Plus (α : Type*) (β : Type*) (γ : Type*) where
  plus : α → β → γ

instance : Plus Nat Rat Rat where
  plus := fun n q => n + q

#check Plus.plus (1 : ℕ) (2 : ℚ)

class Plus' (α : Type*) (β : Type*) (γ : outParam Type*) where
  plus : α → β → γ

instance : Plus' Nat Rat Rat where
  plus := fun n q => n + q

#check Plus'.plus (1 : ℕ) (2 : ℚ)

infixl:50 " ⋄ " => Plus'.plus

#check (1 : ℕ) ⋄ (2 : ℚ)


#check (1 : ℕ) ⋄ ((1 : ℕ) ⋄ (2 : ℚ))

-- infixr:50 " ⋄ " => Plus'.plus

-- #check (1 : ℕ) ⋄ (1 : ℕ) ⋄ (2 : ℚ)

#print CoeDep


structure NonemptyList (α : Type*) where
  head : α
  tail : List α

instance {α : Type*} {x : α} {xs : List α} : CoeDep (List α) (x :: xs) (NonemptyList α) where
  coe := ⟨x, xs⟩

#check ([1] : NonemptyList Nat)
-- #check ([] : NonemptyList Nat)


#print CoeFun

structure SpecialFun where
  f : Nat → Nat
  p : ∀ n, f n < 10

instance : CoeFun SpecialFun (fun _ => Nat → Nat) where
  coe := SpecialFun.f

def specialfun : SpecialFun where
  f := fun n => 1
  p := by
    intro n
    dsimp
    decide

#eval specialfun 10


#print Subgroup
#print IsSubgroup
